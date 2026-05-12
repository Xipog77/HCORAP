"""
Python port of the HCORAP encoding from C++ (HCORAPEncoding.cpp + smtformula.cpp).

Exposes the API expected by maxsat_solver.py:
  - HCORAPInstance(filepath)
  - HCORAPEncoding(instance)  with .hard_clauses, .soft_clauses, .vm
  - verify_solution(inst, enc, model)

All clauses use plain integers (positive = true, negative = negated),
compatible with PySAT's WCNF format.

NOTE vs original C++:
  - The C++ code uses Literal/Clause objects with operator overloading.
    Here we use plain ints: var_id for positive, -var_id for negated.
  - AMO uses quadratic encoding (same default as C++ AMO_QUAD).
  - Sorting network is the Batcher odd-even mergesort from smtformula.cpp.
  - Service coverage (constraint 1.2) is a hard clause (strat=False mode),
    matching the non-stratified C++ behaviour used in the standard pipeline.
"""

from collections import Counter


# ---------------------------------------------------------------------------
# Instance parser  (matches C++ parser::parseHCORAP)
# ---------------------------------------------------------------------------
class HCORAPInstance:

    def __init__(self, filepath):
        self.filepath = filepath
        self._parse(filepath)

    def _parse(self, filepath):
        with open(filepath, 'r') as f:
            lines = f.read().splitlines()

        idx = 0

        def skip_to(tag):
            nonlocal idx
            while idx < len(lines) and lines[idx].strip() != tag:
                idx += 1
            idx += 1

        def read_int():
            nonlocal idx
            val = int(lines[idx].strip())
            idx += 1
            return val

        skip_to('#U');  self.U = read_int()
        skip_to('#S');  self.S = read_int()
        skip_to('#A');  self.A = read_int()
        skip_to('#TS'); self.TS = read_int()

        skip_to('#SU')
        self.SU = []
        while idx < len(lines) and lines[idx].strip() != '#SEQ':
            line = lines[idx].strip()
            if line:
                self.SU.append([int(x) for x in line.split()])
            idx += 1

        idx += 1  # skip '#SEQ'
        self.SEQ = []
        while idx < len(lines) and lines[idx].strip() != '#TSA(i)':
            line = lines[idx].strip()
            if line:
                self.SEQ.append([int(x) for x in line.split()])
            idx += 1

        idx += 1
        self.TSA = []
        for a in range(self.A):
            row = []
            while len(row) < self.TS:
                row.extend([int(x) for x in lines[idx].split()])
                idx += 1
            self.TSA.append(row[:self.TS])

        skip_to('#TSS(i)')
        self.TSS = []
        for s in range(self.S):
            row = []
            while len(row) < self.TS:
                row.extend([int(x) for x in lines[idx].split()])
                idx += 1
            self.TSS.append(row[:self.TS])

        skip_to('#r(i,j)')
        self.r = []
        for a in range(self.A):
            self.r.append([int(x) for x in lines[idx].split()])
            idx += 1

        skip_to('#P');  self.P = read_int()

        skip_to('#HN(i)')
        self.HN = [read_int() for _ in range(self.A)]

        skip_to('#HE(i)')
        self.HE = [read_int() for _ in range(self.A)]

    def __repr__(self):
        return (f"HCORAP(U={self.U}, S={self.S}, A={self.A}, TS={self.TS}, "
                f"|SEQ|={len(self.SEQ)}, P={self.P})")


# ---------------------------------------------------------------------------
# Variable manager
# ---------------------------------------------------------------------------
class VarManager:
    def __init__(self):
        self._next = 1

    def new_var(self):
        v = self._next
        self._next += 1
        return v

    @property
    def num_vars(self):
        return self._next - 1


# ---------------------------------------------------------------------------
# Encoding  (faithful port of HCORAPEncoding::encode from C++)
# ---------------------------------------------------------------------------
class HCORAPEncoding:
    """
    Builds the MaxSAT encoding of an HCORAP instance.

    After construction the following attributes are available:
      hard_clauses : list[list[int]]       – hard CNF clauses
      soft_clauses : list[tuple[list[int]|int, int]] – (lits, weight)
      vm           : VarManager
      x, y, su, s  : dict  – variable maps for solution verification
      total_soft, konstant_revenue – bookkeeping from C++
    """

    def __init__(self, instance: HCORAPInstance, strat: bool = False):
        self.inst = instance
        self.strat = strat
        self.vm = VarManager()

        self.hard_clauses: list[list[int]] = []
        self.soft_clauses: list[tuple] = []

        # Variable maps (key→var_id).  0 means "false variable".
        self.x = {}   # (a, s, t) -> var
        self.y = {}   # (a, s)    -> var
        self.su = {}  # (s, t)    -> var
        self.s = {}   # (a, q)    -> var

        self.total_soft = 0
        self.konstant_revenue = 0
        self.total_soft_strat = 0

        # false variable (unit clause forcing it false)
        self._false_id = self.vm.new_var()
        self.hard_clauses.append([-self._false_id])

        self._encode()

    # -- helpers --------------------------------------------------------
    def _new(self):
        return self.vm.new_var()

    def _add_hard(self, clause):
        self.hard_clauses.append(clause)

    def _add_soft(self, lits, weight):
        if isinstance(lits, int):
            lits = [lits]
        self.soft_clauses.append((lits, weight))

    def _is_false(self, v):
        return v == self._false_id

    # -- AMO (quadratic, same as C++ default AMO_QUAD) ------------------
    def _add_amo(self, lits):
        n = len(lits)
        if n <= 1:
            return
        for i in range(n - 1):
            for j in range(i + 1, n):
                self._add_hard([-lits[i], -lits[j]])

    # -- Sorting network (Batcher odd-even mergesort from smtformula.cpp)
    def _two_comp(self, x1, x2):
        """Two-comparator: returns (y_max, y_min)."""
        y1 = self._new()
        y2 = self._new()
        # leq clauses
        self._add_hard([-x1, y1])
        self._add_hard([-x2, y1])
        self._add_hard([-x1, -x2, y2])
        # geq clauses
        self._add_hard([x1, -y2])
        self._add_hard([x2, -y2])
        self._add_hard([x1, x2, -y1])
        return y1, y2

    def _sorting(self, x):
        n = len(x)
        if n == 0:
            return []
        if n == 1:
            return list(x)
        if n == 2:
            y1, y2 = self._two_comp(x[0], x[1])
            return [y1, y2]
        mid = n // 2
        z1 = self._sorting(x[:mid])
        z2 = self._sorting(x[mid:])
        return self._merge(z1, z2)

    def _merge(self, x1, x2):
        a, b = len(x1), len(x2)
        if a == 0:
            return list(x2)
        if b == 0:
            return list(x1)
        if a == 1 and b == 1:
            y1, y2 = self._two_comp(x1[0], x2[0])
            return [y1, y2]

        x1e, x1o = x1[0::2], x1[1::2]
        x2e, x2o = x2[0::2], x2[1::2]
        ze = self._merge(x1e, x2e)
        zo = self._merge(x1o, x2o)

        y = [None] * (a + b)
        z = [None] * (a + b)

        if a % 2 == 0:
            if b % 2 == 0:
                for i in range((a + b) // 2):
                    z[2 * i] = ze[i]
                    z[2 * i + 1] = zo[i]
                y[0] = z[0]
                y[a + b - 1] = z[a + b - 1]
                for i in range(1, a + b - 2, 2):
                    y[i], y[i + 1] = self._two_comp(z[i], z[i + 1])
            else:
                for i in range((a + b) // 2 + 1):
                    z[2 * i] = ze[i]
                for i in range((a + b) // 2):
                    z[2 * i + 1] = zo[i]
                y[0] = z[0]
                for i in range(1, a + b - 1, 2):
                    y[i], y[i + 1] = self._two_comp(z[i], z[i + 1])
        else:
            if b % 2 == 0:
                return self._merge(x2, x1)
            else:
                for i in range((a + 1) // 2):
                    z[2 * i] = ze[i]
                for i in range((b + 1) // 2):
                    z[a + 2 * i] = ze[(a + 1) // 2 + i]
                for i in range(a // 2):
                    z[2 * i + 1] = zo[i]
                for i in range(b // 2):
                    z[a + 2 * i + 1] = zo[a // 2 + i]
                y[0] = z[0]
                y[a + b - 1] = z[a + b - 1]
                for i in range(1, a + b - 2, 2):
                    y[i], y[i + 1] = self._two_comp(z[i], z[i + 1])
        return y

    # -- main encoding --------------------------------------------------
    def _encode(self):
        inst = self.inst
        F = self._false_id
        self.total_soft = 0
        self.konstant_revenue = 0

        # --- [BƯỚC 1]: Khởi tạo variables (Giữ nguyên phần này) ---
        for a in range(inst.A):
            for s in range(inst.S):
                if inst.r[a][s] == 0: continue
                for t in range(inst.TS):
                    if inst.TSA[a][t] and inst.TSS[s][t]:
                        self.x[(a, s, t)] = self._new()

        for a in range(inst.A):
            for s in range(inst.S):
                if inst.r[a][s] != 0:
                    self.y[(a, s)] = self._new()

        for s in range(inst.S):
            for t in range(inst.TS):
                if inst.TSS[s][t]:
                    self.su[(s, t)] = self._new()

        for a in range(inst.A):
            for q in range(len(inst.SEQ)):
                if len(inst.SEQ[q]) == 1:
                    s0 = inst.SEQ[q][0]
                    if (a, s0) in self.y: self.s[(a, q)] = self.y[(a, s0)]
                else:
                    self.s[(a, q)] = self._new()

        # --- 5) Reification: y[a,s] <==> OR_t x[a,s,t] ---
        for a in range(inst.A):
            for s in range(inst.S):
                if (a, s) not in self.y: continue
                yv = self.y[(a, s)]
                xvars = [self.x[(a, s, t)] for t in range(inst.TS) if (a, s, t) in self.x]
                if not xvars:
                    self._add_hard([-yv])
                    continue
                for xv in xvars:
                    self._add_hard([-xv, yv])
                self._add_hard([-yv] + xvars)

        # --- 5b) Reification: su[s,t] <==> OR_a x[a,s,t] ---
        for s in range(inst.S):
            for t in range(inst.TS):
                if (s, t) not in self.su: continue
                zv = self.su[(s, t)]
                xvars = [self.x[(a, s, t)] for a in range(inst.A) if (a, s, t) in self.x]
                if not xvars:
                    self._add_hard([-zv])
                    continue
                for xv in xvars:
                    self._add_hard([-xv, zv])
                self._add_hard([-zv] + xvars)

        # --- 1) AMO: each service at most one (agent, timeslot) ---
        for s in range(inst.S):
            xvars = [self.x[(a, s, t)] for a in range(inst.A)
                     for t in range(inst.TS) if (a, s, t) in self.x]
            self._add_commander_amo(xvars) 

        # --- [THAY THẾ 2]: AMO cho từng nhân viên/khung giờ ---
        for a in range(inst.A):
            for t in range(inst.TS):
                xvars = [self.x[(a, s, t)] for s in range(inst.S)
                         if (a, s, t) in self.x]
                # Thay đổi sang Commander Encoding
                self._add_commander_amo(xvars) 

        # --- [THAY THẾ 3]: AMO cho từng user-group ---
        for su_group in inst.SU:
            for t in range(inst.TS):
                zvars = [self.su[(s, t)] for s in su_group
                         if (s, t) in self.su]
                # Thay đổi sang Commander Encoding
                self._add_commander_amo(zvars) 

        # --- 6) Reification of sequences (size > 1) ---
        #     s[a,q] <==> OR_{j in SEQ[q]} y[a,j]
        for a in range(inst.A):
            for q in range(len(inst.SEQ)):
                if len(inst.SEQ[q]) == 1: continue
                if (a, q) not in self.s: continue
                wv = self.s[(a, q)]
                yvars = [self.y[(a, j)] for j in inst.SEQ[q] if (a, j) in self.y]
                if not yvars:
                    self._add_hard([-wv])
                    continue
                for yv in yvars:
                    self._add_hard([-yv, wv])
                self._add_hard([-wv] + yvars)

        # --- [THÊM MỚI]: Gọi Symmetry Breaking sau khi có đủ biến y ---
        self._add_symmetry_breaking() 

        # --- 7) Objective O2: Stability (Sequence consistency) ---
        for q in range(len(inst.SEQ)):
            if len(inst.SEQ[q]) == 1: continue
            wvars = [self.s[(a, q)] for a in range(inst.A) if (a, q) in self.s]
            if not wvars: continue
            
            vout = self._totalizer(wvars) 
            p = min(inst.A, len(inst.SEQ[q]))
            for i in range(p):
                # REWARD when vout[i] is False (means we have fewer than i+1 agents)
                # This effectively MINIMIZES the number of agents per sequence.
                self._add_soft(-vout[i], 1)
                self.total_soft += 1
            self.konstant_revenue += len(inst.SEQ[q]) - p

        # --- 8) Objective O1: Similarity (Expertise reward) ---
        for a in range(inst.A):
            for s in range(inst.S):
                if (a, s) in self.y:
                    weight = inst.r[a][s]
                    if weight > 0:
                        # REWARD similarity
                        self._add_soft(self.y[(a, s)], weight)
                        self.total_soft += weight

        # --- 9) Objective O3: Working hours ---
        for a in range(inst.A):
            yvars = [self.y[(a, s)] for s in range(inst.S) if (a, s) in self.y]
            if not yvars: continue
            
            max_hours = inst.HN[a] + inst.HE[a]
            vout = self._totalizer(yvars) 
            
            if len(yvars) > max_hours:
                self._add_hard([-vout[max_hours]])
            
            abs_P = abs(inst.P)
            limit = min(max_hours, len(vout))
            for k in range(inst.HN[a], limit):
                # PENALTY for extra hours (REWARD when vout[k] is False)
                self._add_soft(-vout[k], abs_P)
                self.total_soft += abs_P
            self.konstant_revenue += (limit - inst.HN[a]) * inst.P

        # --- 10) Service coverage ---
        for s in range(inst.S):
            yvars = [self.y[(a, s)] for a in range(inst.A) if (a, s) in self.y]
            self._add_hard(yvars)

        print(f"c {self.total_soft} {self.konstant_revenue}")

# ---------------------------------------------------------------------------
# new
# ---------------------------------------------------------------------------

# Thay thế hàm _sorting bằng _totalizer
    def _totalizer(self, lits):
        n = len(lits)
        if n == 0: return []
        if n == 1: return [lits[0]]
        
        mid = n // 2
        left = self._totalizer(lits[:mid])
        right = self._totalizer(lits[mid:])
        return self._merge_totalizer(left, right)

    def _merge_totalizer(self, left, right):
        n_l, n_r = len(left), len(right)
        res = [self._new() for _ in range(n_l + n_r)]
        
        # Ràng buộc cơ bản của Totalizer:
        # Nếu left có i bit True và right có j bit True, thì res có ít nhất i+j bit True
        for i in range(n_l + 1):
            for j in range(n_r + 1):
                if i == 0 and j == 0: continue
                
                clause = []
                if i > 0: clause.append(-left[i-1])
                if j > 0: clause.append(-right[j-1])
                
                if i + j <= n_l + n_r:
                    clause.append(res[i + j - 1])
                    self._add_hard(clause)
        return res

        
    def _add_commander_amo(self, lits, k=3):
        """Standard Commander Encoding for At Most One."""
        n = len(lits)
        if n <= 1: return
        if n <= k:
            self._add_amo_quadratic(lits)
            return

        groups = [lits[i:i + k] for i in range(0, n, k)]
        commanders = []

        for group in groups:
            cmd = self._new()
            commanders.append(cmd)
            
            # 1. At most one in each group
            self._add_amo_quadratic(group)
            
            # 2. If any lit is True, commander must be True
            for lit in group:
                self._add_hard([-lit, cmd])
                
            # 3. IMPORTANT for AMO: We do NOT add (cmd -> OR group)
            # because the commander can be False if the whole group is False.
            # But if a lit is True, the commander IS True.
            # Combined with AMO(commanders), this ensures at most one group is active.

        self._add_commander_amo(commanders, k)

    def _add_amo_quadratic(self, lits):
        n = len(lits)
        for i in range(n):
            for j in range(i + 1, n):
                self._add_hard([-lits[i], -lits[j]])

    def _add_symmetry_breaking(self):
        inst = self.inst
        # Tìm các nhóm agent có profile giống hệt nhau
        groups = {}
        for a in range(inst.A):
            # Đặc trưng của Agent: r(a,s) và TSA(a)
            profile = (tuple(inst.r[a]), tuple(inst.TSA[a]))
            if profile not in groups: groups[profile] = []
            groups[profile].append(a)

        for profile, agents in groups.items():
            if len(agents) < 2: continue
            
            # Với mỗi cặp agent liên tiếp trong nhóm đối xứng
            for i in range(len(agents) - 1):
                a1, a2 = agents[i], agents[i+1]
                # Ép thứ tự: Số dịch vụ agent i làm phải >= agent i+1
                # (Hoặc ép thứ tự từ điển trên vector y[a, s])
                self._add_lex_order(a1, a2)

    def _add_lex_order(self, a1, a2):
        # Ràng buộc đơn giản: Count(y[a1, s]) >= Count(y[a2, s])
        # Sử dụng các bit đầu ra từ Totalizer của mỗi agent
        y1 = [self.y[(a1, s)] for s in range(self.inst.S) if (a1, s) in self.y]
        y2 = [self.y[(a2, s)] for s in range(self.inst.S) if (a2, s) in self.y]
        
        if not y1 or not y2: return
        
        out1 = self._totalizer(y1)
        out2 = self._totalizer(y2)
        
        # Nếu agent 2 làm k việc, agent 1 cũng phải làm ít nhất k việc
        for k in range(min(len(out1), len(out2))):
            self._add_hard([-out2[k], out1[k]])


# ---------------------------------------------------------------------------
# Solution verification  (port of checkSolution from C++)
# ---------------------------------------------------------------------------
def evaluate_cop_objective(inst: HCORAPInstance, assignments):
    """COP objective: similarity + stability - cost."""
    abs_p = abs(inst.P)

    similarity = sum(inst.r[a][s] for a, s, t in assignments)

    stability = 0
    for seq in inst.SEQ:
        agents_in_seq = {a for a, s, t in assignments if s in seq}
        k = len(agents_in_seq)
        stability += max(0, len(seq) - k)

    agent_hours = Counter(a for a, s, t in assignments)
    cost = 0
    for a in range(inst.A):
        h = agent_hours.get(a, 0)
        cost += abs_p * max(0, h - inst.HN[a])

    return similarity, stability, cost, similarity + stability - cost


def verify_solution(inst: HCORAPInstance, enc: HCORAPEncoding, model):
    """Verify a SAT model against the HCORAP constraints (mirrors C++ output)."""
    model_set = set(model)
    ok = True

    assignments = [(a, s, t) for (a, s, t), v in enc.x.items()
                   if v in model_set]

    # C1: each service at most once
    svc_cnt = Counter(s for a, s, t in assignments)
    for s, c in svc_cnt.items():
        if c > 1:
            print(f"  [FAIL] C1: service {s} assigned {c} times"); ok = False

    # C2: agent at most one service per timeslot
    at_cnt = Counter((a, t) for a, s, t in assignments)
    for (a, t), c in at_cnt.items():
        if c > 1:
            print(f"  [FAIL] C2: agent {a}, slot {t} = {c}"); ok = False

    # C3: allowed assignments
    for a, s, t in assignments:
        if inst.r[a][s] == 0:
            print(f"  [FAIL] C3: r({a},{s})=0"); ok = False
        if not inst.TSA[a][t]:
            print(f"  [FAIL] C3: TSA({a},{t})=0"); ok = False
        if not inst.TSS[s][t]:
            print(f"  [FAIL] C3: TSS({s},{t})=0"); ok = False

    # C4: user-group at most one service per timeslot
    for su_group in inst.SU:
        su_set = set(su_group)
        ts_cnt = Counter(t for a, s, t in assignments if s in su_set)
        for t, c in ts_cnt.items():
            if c > 1:
                print(f"  [FAIL] C4: user-group, slot {t} = {c}"); ok = False

    covered = set(s for a, s, t in assignments)
    uncovered = set(range(inst.S)) - covered

    # C6: max working hours
    agent_hours = Counter(a for a, s, t in assignments)
    for a in range(inst.A):
        h = agent_hours.get(a, 0)
        if h > inst.HN[a] + inst.HE[a]:
            print(f"  [FAIL] C6: agent {a} works {h} > "
                  f"{inst.HN[a]}+{inst.HE[a]}"); ok = False

    similarity, stability, cost, objective = evaluate_cop_objective(
        inst, assignments)

    print(f"\n  === Solution Verification ===")
    print(f"  Hard constraints:  {'OK' if ok else 'FAILED'}")
    print(f"  Assigned:          {len(assignments)}/{inst.S}")
    print(f"  Uncovered:         {len(uncovered)}")
    print(f"  ---")
    print(f"  O1 Similarity:     +{similarity}")
    print(f"  O2 Stability:      +{stability}")
    print(f"  O3 Cost:           −{cost}")
    print(f"  ---")
    print(f"  Objective (sim+stab−cost): {objective}")
    return ok
