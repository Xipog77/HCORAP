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
    

    # Chuyển thành commander
    # case AMO_COMMANDER:
	# 	{
	# 		if(n<6)
	# 			addAMO(x,AMO_QUAD);
	# 		else{
	# 			int nsplits = n/3;
	# 			if(n%3!=0) nsplits++;

	# 			std::vector<literal> cmd_vars(nsplits);

	# 			if(nsplits==2){
	# 				cmd_vars[0] = newBoolVar();
	# 				cmd_vars[1] = !cmd_vars[0];
	# 			}
	# 			else{
	# 				for(int i= 0; i < nsplits; i++)
	# 					cmd_vars[i] = newBoolVar();
	# 				addEO(cmd_vars,AMO_COMMANDER);
	# 			}

	# 			for(int i = 0; i < nsplits; i++){
	# 				std::vector<literal> v;
	# 				for(int j = 3*i; j < 3*(i+1) && j < n; j++){
	# 					v.push_back(x[j]);
	# 					addClause(v[i] | !x[j]);
	# 				}
	# 				addAMO(v,AMO_QUAD);
	# 			}
	# 		}
	# 	}
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

        # --- Create variables ---
        # x[a,s,t]
        for a in range(inst.A):
            for s in range(inst.S):
                if inst.r[a][s] == 0:
                    continue
                for t in range(inst.TS):
                    if inst.TSA[a][t] and inst.TSS[s][t]:
                        self.x[(a, s, t)] = self._new()

        # y[a,s]
        for a in range(inst.A):
            for s in range(inst.S):
                if inst.r[a][s] != 0:
                    self.y[(a, s)] = self._new()

        # su[s,t]
        for s in range(inst.S):
            for t in range(inst.TS):
                if inst.TSS[s][t]:
                    self.su[(s, t)] = self._new()

        # s[a,q]  (reification variable for sequences)
        for a in range(inst.A):
            for q in range(len(inst.SEQ)):
                if len(inst.SEQ[q]) == 1:
                    s0 = inst.SEQ[q][0]
                    if (a, s0) in self.y:
                        self.s[(a, q)] = self.y[(a, s0)]
                    # NOTE: if (a,s0) not in y, agent can't do this seq
                else:
                    self.s[(a, q)] = self._new()

        # --- 5) Reification: y[a,s] <==> OR_t x[a,s,t] ---
        for a in range(inst.A):
            for s in range(inst.S):
                if (a, s) not in self.y:
                    continue
                yv = self.y[(a, s)]
                xvars = [self.x[(a, s, t)] for t in range(inst.TS)
                         if (a, s, t) in self.x]
                if not xvars:
                    self._add_hard([-yv])
                    continue
                for xv in xvars:
                    self._add_hard([-xv, yv])
                self._add_hard([-yv] + xvars)

        # --- 5b) Reification: su[s,t] <==> OR_a x[a,s,t] ---
        for s in range(inst.S):
            for t in range(inst.TS):
                if (s, t) not in self.su:
                    continue
                zv = self.su[(s, t)]
                xvars = [self.x[(a, s, t)] for a in range(inst.A)
                         if (a, s, t) in self.x]
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
            self._add_amo(xvars)

        # --- 2) AMO: each agent at most one service per timeslot ---
        for a in range(inst.A):
            for t in range(inst.TS):
                xvars = [self.x[(a, s, t)] for s in range(inst.S)
                         if (a, s, t) in self.x]
                self._add_amo(xvars)

        # --- 4) AMO: each user-group at most one service per timeslot ---
        for su_group in inst.SU:
            for t in range(inst.TS):
                zvars = [self.su[(s, t)] for s in su_group
                         if (s, t) in self.su]
                self._add_amo(zvars)

        # --- 6) Reification of sequences (size > 1) ---
        #     s[a,q] <==> OR_{j in SEQ[q]} y[a,j]
        for a in range(inst.A):
            for q in range(len(inst.SEQ)):
                if len(inst.SEQ[q]) == 1:
                    continue
                if (a, q) not in self.s:
                    continue
                wv = self.s[(a, q)]
                yvars = [self.y[(a, j)] for j in inst.SEQ[q]
                         if (a, j) in self.y]
                if not yvars:
                    self._add_hard([-wv])
                    continue
                for yv in yvars:
                    self._add_hard([-yv, wv])
                self._add_hard([-wv] + yvars)

        # --- [THÊM MỚI]: Gọi Symmetry Breaking sau khi có đủ biến y ---
        # Bỏ comment dòng dưới để bật Linear Lex-Leader Symmetry Breaking
        self._add_symmetry_breaking()

        # --- 7) Sequence consistency (sorting network + soft) ---
        for q in range(len(inst.SEQ)):
            if len(inst.SEQ[q]) == 1:
                continue
            wvars = [self.s[(a, q)] for a in range(inst.A)
                     if (a, q) in self.s]
            if not wvars:
                continue
            vout = self._sorting(wvars)
            p = min(inst.A, len(inst.SEQ[q]))
            for i in range(p):
                self._add_soft(-vout[i], 1)
                self.total_soft += 1
            self.konstant_revenue += len(inst.SEQ[q]) - p

        # --- 8) Revenue (expertise reward) ---
        for a in range(inst.A):
            for s in range(inst.S):
                if inst.r[a][s] != 0 and (a, s) in self.y:
                    self._add_soft(self.y[(a, s)], inst.r[a][s])
                    self.total_soft += inst.r[a][s]

        # --- 9) Working hours (sorting network + soft penalty + hard cap) ---
        for a in range(inst.A):
            yvars = [self.y[(a, s)] for s in range(inst.S)
                     if (a, s) in self.y]
            if len(yvars) <= inst.HN[a]:
                continue
            max_hours = inst.HN[a] + inst.HE[a]
            vout = self._sorting(yvars)
            if len(yvars) > max_hours:
                self._add_hard([-vout[max_hours]])
            p = min(max_hours, len(vout))
            # NOTE: In C++ weight is -P (negative), but MaxSAT weights must
            # be positive. The C++ code uses negative soft weights as a
            # penalty trick inside its own objective calculation.
            # For PySAT/RC2 we use abs(P) as the weight (penalise extra hrs).
            abs_P = abs(inst.P)
            for k in range(inst.HN[a], p):
                self._add_soft(-vout[k], abs_P)
                self.total_soft += -inst.P  # keep C++ bookkeeping sign
            self.konstant_revenue += (p - inst.HN[a]) * inst.P

        # --- 1.2) Service coverage ---
        self.total_soft_strat = 0
        for s in range(inst.S):
            zvars = [self.su[(s, t)] for t in range(inst.TS)
                     if (s, t) in self.su]
            if not zvars:
                continue
            if self.strat:
                weight = self.total_soft + 1
                self._add_soft(zvars, weight)
                self.total_soft_strat += weight
            else:
                self._add_hard(zvars)

        print(f"c {self.total_soft} {self.konstant_revenue}")

    # =========================================================================
    # SYMMETRY BREAKING (Được cấy từ hcorap_encoding_new.py)
    # =========================================================================
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
                # Ép thứ tự từ điển nghiêm ngặt (y1 >=lex y2)
                self._add_lex_order(a1, a2)

    def _add_lex_order(self, a1, a2):
        # Linear Lex-Leader Symmetry Breaking (Độ phức tạp O(S))
        y1 = [self.y[(a1, s)] for s in range(self.inst.S) if (a1, s) in self.y]
        y2 = [self.y[(a2, s)] for s in range(self.inst.S) if (a2, s) in self.y]
        
        if not y1 or not y2: return
        
        n = len(y1)
        e = [self._new() for _ in range(n)]
        self._add_hard([e[0]]) # e[0] luôn là True ở đầu chuỗi
        
        for j in range(1, n):
            # e[j] -> e[j-1]
            self._add_hard([-e[j], e[j-1]])
            # e[j] -> (y1[j-1] == y2[j-1])
            self._add_hard([-e[j], -y1[j-1], y2[j-1]])
            self._add_hard([-e[j], -y2[j-1], y1[j-1]])
            # (e[j-1] and y1[j-1] == y2[j-1]) -> e[j]
            self._add_hard([-e[j-1], -y1[j-1], -y2[j-1], e[j]])
            self._add_hard([-e[j-1], y1[j-1], y2[j-1], e[j]])
            
        # Ràng buộc Lex chính: e[j] -> (y1[j] >= y2[j])
        for j in range(n):
            self._add_hard([-e[j], -y2[j], y1[j]])



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
