from collections import Counter

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

class VarManager:

    def __init__(self):
        self._next_var = 1

    def new_var(self):
        v = self._next_var
        self._next_var += 1
        return v

    @property
    def num_vars(self):
        return self._next_var - 1

class HCORAPEncoding:

    def __init__(self, instance: HCORAPInstance):
        self.inst = instance
        self.vm = VarManager()

        self.x = {}       
        self.y = {}       
        self.z = {}       
        self.w = {}       

        self.hard_clauses = []
        self.soft_clauses = []

        self._create_variables()
        self._encode_hard()
        self._encode_soft()

    def _add_hard(self, clause):
        self.hard_clauses.append(clause)

    def _add_soft(self, lits, weight):
        if isinstance(lits, int):
            lits = [lits]
        self.soft_clauses.append((lits, weight))

    def _create_variables(self):
        inst = self.inst

        for a in range(inst.A):
            for s in range(inst.S):
                if inst.r[a][s] == 0:
                    continue  
                self.y[(a, s)] = self.vm.new_var()
                for t in range(inst.TS):
                    if inst.TSA[a][t] and inst.TSS[s][t]:
                        self.x[(a, s, t)] = self.vm.new_var()

        for s in range(inst.S):
            for t in range(inst.TS):
                if inst.TSS[s][t]:
                    self.z[(s, t)] = self.vm.new_var()

        for a in range(inst.A):
            for q in range(len(inst.SEQ)):
                if len(inst.SEQ[q]) == 1:
                    s0 = inst.SEQ[q][0]
                    if (a, s0) in self.y:
                        self.w[(a, q)] = self.y[(a, s0)]
                else:
                    self.w[(a, q)] = self.vm.new_var()

    def _equivalent_agent_pairs(self):
        """Agents with identical availability, similarity row, and hour limits."""
        inst = self.inst
        pairs = []
        for a in range(inst.A):
            sig = (tuple(inst.TSA[a]), tuple(inst.r[a]),
                   inst.HN[a], inst.HE[a])
            for b in range(a + 1, inst.A):
                sig_b = (tuple(inst.TSA[b]), tuple(inst.r[b]),
                         inst.HN[b], inst.HE[b])
                if sig == sig_b:
                    pairs.append((a, b))
        return pairs

    def _add_amo(self, lits):
        if len(lits) <= 1:
            return
        from pysat.card import CardEnc, EncType
        if len(lits) <= 10:
            enc = EncType.pairwise
        else:
            enc = EncType.bitwise
        cnf = CardEnc.atmost(lits, bound=1, top_id=self.vm.num_vars,
                             encoding=enc)
        if cnf.nv > self.vm.num_vars:
            while self.vm.num_vars < cnf.nv:
                self.vm.new_var()
        self.hard_clauses.extend(cnf.clauses)

    def _add_card_atmost(self, lits, k):
        """Cardinality ∑ lits ≤ k."""
        if len(lits) <= 1 or k < 0:
            return
        if k >= len(lits):
            return
        if k == 0:
            for v in lits:
                self._add_hard([-v])
            return
        from pysat.card import CardEnc, EncType
        # `bitwise` is mainly for AMO; for general at-most-k it may raise
        # UnsupportedBound on larger k. Use a general-purpose encoding here.
        enc = EncType.seqcounter
        cnf = CardEnc.atmost(lits, bound=k, top_id=self.vm.num_vars,
                             encoding=enc)
        if cnf.nv > self.vm.num_vars:
            while self.vm.num_vars < cnf.nv:
                self.vm.new_var()
        self.hard_clauses.extend(cnf.clauses)

    def _encode_hard(self):
        inst = self.inst

        for a in range(inst.A):
            for s in range(inst.S):
                if (a, s) not in self.y:
                    continue
                y_var = self.y[(a, s)]
                x_vars = [self.x[(a, s, t)] for t in range(inst.TS)
                          if (a, s, t) in self.x]
                if not x_vars:
                    self._add_hard([-y_var])
                    continue
                for xv in x_vars:
                    self._add_hard([-xv, y_var])
                self._add_hard([-y_var] + x_vars)

        for s in range(inst.S):
            for t in range(inst.TS):
                if (s, t) not in self.z:
                    continue
                z_var = self.z[(s, t)]
                x_vars = [self.x[(a, s, t)] for a in range(inst.A)
                          if (a, s, t) in self.x]
                if not x_vars:
                    self._add_hard([-z_var])
                    continue
                for xv in x_vars:
                    self._add_hard([-xv, z_var])
                self._add_hard([-z_var] + x_vars)

        for a in range(inst.A):
            for q in range(len(inst.SEQ)):
                if len(inst.SEQ[q]) == 1:
                    continue
                if (a, q) not in self.w:
                    continue
                w_var = self.w[(a, q)]
                y_vars = [self.y[(a, s)] for s in inst.SEQ[q]
                          if (a, s) in self.y]
                if not y_vars:
                    self._add_hard([-w_var])
                    continue
                for yv in y_vars:
                    self._add_hard([-yv, w_var])
                self._add_hard([-w_var] + y_vars)

        for s in range(inst.S):
            x_vars = [self.x[(a, s, t)] for a in range(inst.A)
                      for t in range(inst.TS) if (a, s, t) in self.x]
            self._add_amo(x_vars)

        for a in range(inst.A):
            for t in range(inst.TS):
                x_vars = [self.x[(a, s, t)] for s in range(inst.S)
                          if (a, s, t) in self.x]
                self._add_amo(x_vars)

        for su_group in inst.SU:
            for t in range(inst.TS):
                z_vars = [self.z[(s, t)] for s in su_group
                          if (s, t) in self.z]
                self._add_amo(z_vars)

        # --- Symmetry breaking: y[b,s] ⇒ y[a,s] for equivalent agents a < b ---
        for a, b in self._equivalent_agent_pairs():
            for s in range(inst.S):
                if (a, s) in self.y and (b, s) in self.y:
                    self._add_hard([-self.y[(b, s)], self.y[(a, s)]])

        # --- C5: Service coverage (eq:cov-hard) ---
        for s in range(inst.S):
            z_vars = [self.z[(s, t)] for t in range(inst.TS)
                      if (s, t) in self.z]
            if z_vars:
                self._add_hard(z_vars)

        for a in range(inst.A):
            max_hours = inst.HN[a] + inst.HE[a]
            y_vars = [self.y[(a, s)] for s in range(inst.S)
                      if (a, s) in self.y]
            if len(y_vars) > max_hours:
                self._add_card_atmost(y_vars, max_hours)

    def _build_sorting_network(self, lits):
        n = len(lits)
        if n == 0:
            return []
        if n == 1:
            return [lits[0]]

        prev = [0] * n
        prev[0] = lits[0]
        for j in range(1, n):
            v = self.vm.new_var()
            self._add_hard([-v])
            prev[j] = v

        for i in range(1, n):
            curr = [0] * n
            for j in range(min(i + 1, n)):
                v = self.vm.new_var()
                curr[j] = v
                if j == 0:
                    self._add_hard([-prev[0], v])
                    self._add_hard([-lits[i], v])
                    self._add_hard([prev[0], lits[i], -v])
                else:
                    self._add_hard([-prev[j], v])
                    self._add_hard([-prev[j - 1], -lits[i], v])
                    self._add_hard([-v, prev[j], prev[j - 1]])
                    self._add_hard([-v, prev[j], lits[i]])
            for j in range(i + 1, n):
                v = self.vm.new_var()
                self._add_hard([-v])
                curr[j] = v
            prev = curr
        return prev

    def _encode_soft(self):

        inst = self.inst

        # --- O1: Similarity — ⟨y_{a,s}, r(a,s)⟩  (eq:soft-reward) ---
        for a in range(inst.A):
            for s in range(inst.S):
                if inst.r[a][s] > 0 and (a, s) in self.y:
                    self._add_soft(self.y[(a, s)], inst.r[a][s])

        # --- O2: Stability — ⟨¬c_{q,i}, 1⟩  (eq:soft-cont) ---
        for q in range(len(inst.SEQ)):
            w_vars = [self.w[(a, q)] for a in range(inst.A)
                      if (a, q) in self.w]
            if not w_vars:
                continue
            c_outputs = self._build_sorting_network(w_vars)
            p = min(len(inst.SEQ[q]), len(c_outputs))
            for i in range(p):
                self._add_soft(-c_outputs[i], 1)

        # --- O3: Extra-hour cost — ⟨¬ŵ_{a,i}, |P|⟩  (eq:soft-extra) ---
        abs_P = -inst.P
        for a in range(inst.A):
            y_vars = [self.y[(a, s)] for s in range(inst.S)
                      if (a, s) in self.y]
            if len(y_vars) <= inst.HN[a]:
                continue
            w_hat_outputs = self._build_sorting_network(y_vars)
            upper = min(inst.HN[a] + inst.HE[a], len(w_hat_outputs))
            for k in range(inst.HN[a], upper):
                self._add_soft(-w_hat_outputs[k], abs_P)


def evaluate_cop_objective(inst: HCORAPInstance, assignments):
    """
    COP objective from doc/main.tex Eq. (sat-obj)–(cost), same as prompt §4:
      objective = similarity + stability - cost
    """
    abs_p = abs(inst.P)

    similarity = sum(inst.r[a][s] for a, s, t in assignments)

    stability = 0
    for seq in inst.SEQ:
        agents_in_seq = {a for a, s, t in assignments if s in seq}
        k = len(agents_in_seq)
        L = len(seq)
        # sum_{i=1..L} (1 - c_{q,i}) with c_{q,i} <=> (k >= i)  =>  max(0, L - k)
        stability += max(0, L - k)

    agent_hours = Counter(a for a, s, t in assignments)
    cost = 0
    for a in range(inst.A):
        h = agent_hours.get(a, 0)
        cost += abs_p * max(0, h - inst.HN[a])

    return similarity, stability, cost, similarity + stability - cost


def verify_solution(inst: HCORAPInstance, enc: HCORAPEncoding, model):
    model_set = set(model)
    ok = True

    assignments = [(a, s, t) for (a, s, t), v in enc.x.items()
                   if v in model_set]

    svc_cnt = Counter(s for a, s, t in assignments)
    for s, c in svc_cnt.items():
        if c > 1:
            print(f"  [FAIL] C1: service {s} assigned {c} times"); ok = False

    at_cnt = Counter((a, t) for a, s, t in assignments)
    for (a, t), c in at_cnt.items():
        if c > 1:
            print(f"  [FAIL] C2: agent {a}, slot {t} = {c}"); ok = False

    for a, s, t in assignments:
        if inst.r[a][s] == 0:
            print(f"  [FAIL] C3: r({a},{s})=0"); ok = False
        if not inst.TSA[a][t]:
            print(f"  [FAIL] C3: TSA({a},{t})=0"); ok = False
        if not inst.TSS[s][t]:
            print(f"  [FAIL] C3: TSS({s},{t})=0"); ok = False

    for su_group in inst.SU:
        su_set = set(su_group)
        ts_cnt = Counter(t for a, s, t in assignments if s in su_set)
        for t, c in ts_cnt.items():
            if c > 1:
                print(f"  [FAIL] C4: user-group, slot {t} = {c}"); ok = False

    covered = set(s for a, s, t in assignments)
    uncovered = set(range(inst.S)) - covered

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
