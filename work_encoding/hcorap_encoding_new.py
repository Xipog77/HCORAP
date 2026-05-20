"""
Python port of the HCORAP encoding from C++ (HCORAPEncoding.cpp + smtformula.cpp).

Exposes the API expected by maxsat_solver.py:
  - HCORAPInstance(filepath)
  - HCORAPEncoding(instance)  with .hard_clauses, .soft_clauses, .vm
  - verify_solution(inst, enc, model)

Optimized with PySAT (CardEnc, ITotalizer) and Lex-Leader Symmetry Breaking.
"""

from collections import Counter
from pysat.card import CardEnc, EncType, ITotalizer


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
# Encoding
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

        # Variable maps (key→var_id).
        self.x = {}   # (a, s, t) -> var
        self.y = {}   # (a, s)    -> var
        self.su = {}  # (s, t)    -> var
        self.s = {}   # (a, q)    -> var

        self.total_soft = 0
        self.konstant_revenue = 0

        # false variable (unit clause forcing it false)
        self._false_id = self.vm.new_var()
        self.hard_clauses.append([-self._false_id])

        self._encode()

    # =========================================================================
    # CORE HELPERS
    # =========================================================================
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

    # =========================================================================
    # CARDINALITY & AMO (Using PySAT)
    # =========================================================================
    def _totalizer(self, lits):
        """Wrapper for PySAT's ITotalizer to get output bits (rhs)."""
        if not lits: return []
        if len(lits) == 1: return [lits[0]]
        
        tot = ITotalizer(lits=lits, ubound=len(lits), top_id=self.vm.num_vars)
        for clause in tot.cnf.clauses:
            self._add_hard(clause)
            
        if tot.cnf.nv > self.vm.num_vars:
            self.vm._next = tot.cnf.nv + 1
            
        return tot.rhs

    def _add_sequential_counter_amo(self, lits):
        """
        At Most One encoding with Hybrid threshold.
        Uses Quadratic AMO for small groups (n <= 10) to speed up UNSAT proofs.
        Uses PySAT's Sequential Counter for large groups to prevent clause explosion.
        """
        n = len(lits)
        if n <= 1:
            return
            
        if n <= 10:
            for i in range(n):
                for j in range(i + 1, n):
                    self._add_hard([-lits[i], -lits[j]])
            return
            
        cnf = CardEnc.atmost(lits, bound=1, top_id=self.vm.num_vars, encoding=EncType.seqcounter)
        for clause in cnf.clauses:
            self._add_hard(clause)
            
        if cnf.nv > self.vm.num_vars:
            self.vm._next = cnf.nv + 1

    # =========================================================================
    # SYMMETRY BREAKING
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
        """Linear Lex-Leader Symmetry Breaking (Độ phức tạp O(S))."""
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

    # =========================================================================
    # MAIN ENCODING FLOW
    # =========================================================================
    def _encode(self):
        inst = self.inst
        self.total_soft = 0
        self.konstant_revenue = 0

        # --- 1. Create variables ---
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

        # --- 2. Reification: y[a,s] <==> OR_t x[a,s,t] ---
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

        # --- 3. Reification: su[s,t] <==> OR_a x[a,s,t] ---
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

        # --- 4. AMO Constraints ---
        # 4.1: Each service at most one (agent, timeslot)
        for s in range(inst.S):
            xvars = [self.x[(a, s, t)] for a in range(inst.A)
                     for t in range(inst.TS) if (a, s, t) in self.x]
            self._add_sequential_counter_amo(xvars)

        # 4.2: AMO cho từng nhân viên/khung giờ
        for a in range(inst.A):
            for t in range(inst.TS):
                xvars = [self.x[(a, s, t)] for s in range(inst.S)
                         if (a, s, t) in self.x]
                self._add_sequential_counter_amo(xvars)

        # 4.3: AMO cho từng user-group
        for su_group in inst.SU:
            for t in range(inst.TS):
                zvars = [self.su[(s, t)] for s in su_group
                         if (s, t) in self.su]
                self._add_sequential_counter_amo(zvars) 

        # --- 5. Reification of sequences (size > 1) ---
        # s[a,q] <==> OR_{j in SEQ[q]} y[a,j]
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

        # --- 6. Symmetry Breaking ---
        self._add_symmetry_breaking() 

        # --- 7. Objectives Encoding ---
        self._encode_soft()

        # --- 8. Service coverage ---
        for s in range(inst.S):
            yvars = [self.y[(a, s)] for a in range(inst.A) if (a, s) in self.y]
            self._add_hard(yvars)

        print(f"c {self.total_soft} {self.konstant_revenue}")

    def _encode_soft(self):
        inst = self.inst
        # --- Objective O2: Stability (Sequence consistency) ---
        for q in range(len(inst.SEQ)):
            if len(inst.SEQ[q]) == 1: continue
            wvars = [self.s[(a, q)] for a in range(inst.A) if (a, q) in self.s]
            if not wvars: continue
            
            vout = self._totalizer(wvars) 
            p = min(inst.A, len(inst.SEQ[q]))
            for i in range(p):
                self._add_soft(-vout[i], 1)
                self.total_soft += 1
            self.konstant_revenue += len(inst.SEQ[q]) - p

        # --- Objective O1: Similarity (Expertise reward) ---
        for a in range(inst.A):
            for s in range(inst.S):
                if (a, s) in self.y:
                    weight = inst.r[a][s]
                    if weight > 0:
                        self._add_soft(self.y[(a, s)], weight)
                        self.total_soft += weight

        # --- Objective O3: Working hours ---
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
                self._add_soft(-vout[k], abs_P)
                self.total_soft += abs_P
            self.konstant_revenue += (limit - inst.HN[a]) * inst.P


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
