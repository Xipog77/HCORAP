import sys
from collections import Counter
from hermax.model import Model, sum_expr, Clause

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


class HCORAPEncodingHermax:
    def __init__(self, instance: HCORAPInstance, strat: bool = False):
        self.inst = instance
        self.strat = strat
        self.m = Model()
        
        self.x = {}   # (a, s, t) -> bool var
        self.y = {}   # (a, s)    -> bool var
        self.su = {}  # (s, t)    -> bool var
        self.s = {}   # (a, q)    -> bool var

        self.total_soft = 0
        self.konstant_revenue = 0

        self._encode()

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
                        self.x[(a, s, t)] = self.m.bool(f"x_{a}_{s}_{t}")

        for a in range(inst.A):
            for s in range(inst.S):
                if inst.r[a][s] != 0:
                    self.y[(a, s)] = self.m.bool(f"y_{a}_{s}")

        for s in range(inst.S):
            for t in range(inst.TS):
                if inst.TSS[s][t]:
                    self.su[(s, t)] = self.m.bool(f"su_{s}_{t}")

        for a in range(inst.A):
            for q in range(len(inst.SEQ)):
                if len(inst.SEQ[q]) == 1:
                    s0 = inst.SEQ[q][0]
                    if (a, s0) in self.y: 
                        self.s[(a, q)] = self.y[(a, s0)]
                else:
                    self.s[(a, q)] = self.m.bool(f"s_{a}_{q}")

        # --- 2. Reification: y[a,s] <==> OR_t x[a,s,t] ---
        for a in range(inst.A):
            for s in range(inst.S):
                if (a, s) not in self.y: continue
                yv = self.y[(a, s)]
                xvars = [self.x[(a, s, t)] for t in range(inst.TS) if (a, s, t) in self.x]
                if not xvars:
                    self.m &= ~yv
                    continue
                # yv <==> OR(xvars)
                for xv in xvars:
                    self.m &= (~xv | yv)
                # ~yv | xvars[0] | xvars[1] | ...
                self.m &= Clause.from_iterable([~yv] + xvars)

        # --- 3. Reification: su[s,t] <==> OR_a x[a,s,t] ---
        for s in range(inst.S):
            for t in range(inst.TS):
                if (s, t) not in self.su: continue
                zv = self.su[(s, t)]
                xvars = [self.x[(a, s, t)] for a in range(inst.A) if (a, s, t) in self.x]
                if not xvars:
                    self.m &= ~zv
                    continue
                for xv in xvars:
                    self.m &= (~xv | zv)
                self.m &= Clause.from_iterable([~zv] + xvars)

        # --- 4. AMO Constraints ---
        # 4.1: Each service at most one (agent, timeslot)
        for s in range(inst.S):
            xvars = [self.x[(a, s, t)] for a in range(inst.A)
                     for t in range(inst.TS) if (a, s, t) in self.x]
            if len(xvars) > 1:
                self.m &= (sum_expr(xvars) <= 1)

        # 4.2: AMO cho từng nhân viên/khung giờ
        for a in range(inst.A):
            for t in range(inst.TS):
                xvars = [self.x[(a, s, t)] for s in range(inst.S)
                         if (a, s, t) in self.x]
                if len(xvars) > 1:
                    self.m &= (sum_expr(xvars) <= 1)

        # 4.3: AMO cho từng user-group
        for su_group in inst.SU:
            for t in range(inst.TS):
                zvars = [self.su[(s, t)] for s in su_group
                         if (s, t) in self.su]
                if len(zvars) > 1:
                    self.m &= (sum_expr(zvars) <= 1)

        # --- 5. Reification of sequences (size > 1) ---
        # s[a,q] <==> OR_{j in SEQ[q]} y[a,j]
        for a in range(inst.A):
            for q in range(len(inst.SEQ)):
                if len(inst.SEQ[q]) == 1: continue
                if (a, q) not in self.s: continue
                wv = self.s[(a, q)]
                yvars = [self.y[(a, j)] for j in inst.SEQ[q] if (a, j) in self.y]
                if not yvars:
                    self.m &= ~wv
                    continue
                for yv in yvars:
                    self.m &= (~yv | wv)
                self.m &= Clause.from_iterable([~wv] + yvars)

        # =====================================================================
        # IMPLIED CONSTRAINTS (Pruning Search Space)
        # =====================================================================
        # IC3: Singleton Feasibility Pruning
        for s in range(inst.S):
            feasible_agents = [a for a in range(inst.A) if (a, s) in self.y]
            if len(feasible_agents) == 1:
                self.m &= self.y[(feasible_agents[0], s)]

        # IC1: Agent Service Count Consistency
        for a in range(inst.A):
            valid_services = [s for s in range(inst.S) if (a, s) in self.y]
            if not valid_services: continue
            avail_slots = sum(1 for t in range(inst.TS) if inst.TSA[a][t])
            tight_bound = min(inst.HN[a] + inst.HE[a], avail_slots)
            if len(valid_services) > tight_bound:
                y_vars = [self.y[(a, s)] for s in valid_services]
                self.m &= (sum_expr(y_vars) <= tight_bound)

        # IC2: Time Slot Capacity Bound
        for t in range(inst.TS):
            avail_agents = sum(1 for a in range(inst.A) if inst.TSA[a][t])
            su_vars = [self.su[(s, t)] for s in range(inst.S) if (s, t) in self.su]
            if len(su_vars) > avail_agents:
                self.m &= (sum_expr(su_vars) <= avail_agents)

        # IC6: Agent-Service Incompatibility Propagation
        for a in range(inst.A):
            services_a = [s for s in range(inst.S) if (a, s) in self.y]
            for i, s1 in enumerate(services_a):
                slots_s1 = {t for t in range(inst.TS) if (a, s1, t) in self.x}
                for s2 in services_a[i+1:]:
                    slots_s2 = {t for t in range(inst.TS) if (a, s2, t) in self.x}
                    if len(slots_s1 | slots_s2) < 2:
                        self.m &= (~self.y[(a, s1)] | ~self.y[(a, s2)])

        # --- 6. Symmetry Breaking ---
        self._add_symmetry_breaking() 

        # --- 7. Objectives Encoding ---
        self._encode_soft()

        # --- 8. Service coverage ---
        for s in range(inst.S):
            yvars = [self.y[(a, s)] for a in range(inst.A) if (a, s) in self.y]
            if yvars:
                self.m &= (sum_expr(yvars) >= 1)

    def _encode_soft(self):
        inst = self.inst
        # --- Objective O1: Similarity (Expertise reward) ---
        for a in range(inst.A):
            for s in range(inst.S):
                if (a, s) in self.y:
                    weight = inst.r[a][s]
                    if weight > 0:
                        self.m.obj[weight] += self.y[(a, s)]
                        self.total_soft += weight

        # --- Objective O2: Stability (Sequence consistency) ---
        # Stability is maximized by rewarding fewer agents participating in the sequence.
        # We want to reward sum_w <= i for i in [0..p-1] where p = min(A, len(SEQ[q]))
        for q in range(len(inst.SEQ)):
            if len(inst.SEQ[q]) == 1: continue
            wvars = [self.s[(a, q)] for a in range(inst.A) if (a, q) in self.s]
            if not wvars: continue
            
            p = min(inst.A, len(inst.SEQ[q]))
            sum_w = sum_expr(wvars)
            
            for i in range(p):
                ind = self.m.bool()
                self.m &= ind.implies(sum_w <= i)
                self.m.obj[1] += ind
                self.total_soft += 1
            self.konstant_revenue += len(inst.SEQ[q]) - p

        # --- Objective O3: Working hours ---
        # Cost is abs_P * sum_{a} max(0, h_a - HN[a]). Minimize cost -> Maximize -cost.
        # Equivalent: reward sum_h <= k for k in [HN[a], max_hours-1] with weight abs_P
        for a in range(inst.A):
            yvars = [self.y[(a, s)] for s in range(inst.S) if (a, s) in self.y]
            if not yvars: continue
            
            max_hours = inst.HN[a] + inst.HE[a]
            sum_h = sum_expr(yvars)
            
            # Hard limit max hours
            if len(yvars) > max_hours:
                self.m &= (sum_h <= max_hours)
            
            abs_P = abs(inst.P)
            limit = min(max_hours, len(yvars))
            for k in range(inst.HN[a], limit):
                ind = self.m.bool()
                self.m &= ind.implies(sum_h <= k)
                self.m.obj[abs_P] += ind
                self.total_soft += abs_P
            
            self.konstant_revenue += (limit - inst.HN[a]) * inst.P

    def _add_symmetry_breaking(self):
        inst = self.inst
        groups = {}
        for a in range(inst.A):
            profile = (tuple(inst.r[a]), tuple(inst.TSA[a]))
            if profile not in groups: groups[profile] = []
            groups[profile].append(a)

        for profile, agents in groups.items():
            if len(agents) < 2: continue
            for i in range(len(agents) - 1):
                a1, a2 = agents[i], agents[i+1]
                self._add_lex_order(a1, a2)

    def _add_lex_order(self, a1, a2):
        y1 = [self.y[(a1, s)] for s in range(self.inst.S) if (a1, s) in self.y]
        y2 = [self.y[(a2, s)] for s in range(self.inst.S) if (a2, s) in self.y]
        
        if not y1 or not y2: return
        
        n = len(y1)
        e = [self.m.bool() for _ in range(n)]
        self.m &= e[0]
        
        for j in range(1, n):
            self.m &= (~e[j] | e[j-1])
            self.m &= (~e[j] | ~y1[j-1] | y2[j-1])
            self.m &= (~e[j] | ~y2[j-1] | y1[j-1])
            self.m &= Clause.from_iterable([~e[j-1], ~y1[j-1], ~y2[j-1], e[j]])
            self.m &= Clause.from_iterable([~e[j-1], y1[j-1], y2[j-1], e[j]])
            
        for j in range(n):
            self.m &= (~e[j] | ~y2[j] | y1[j])

def evaluate_cop_objective(inst: HCORAPInstance, assignments):
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

def verify_solution(inst: HCORAPInstance, enc: HCORAPEncodingHermax, model_result):
    ok = True
    # extract true variables from model_result
    # In hermax, r.model is a dict-like or we can index r.model[var] -> bool
    assignments = []
    for (a, s, t), var in enc.x.items():
        if model_result.model[var]:
            assignments.append((a, s, t))

    # Check hard constraints
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
    print(f"  O3 Cost:           -{cost}")
    print(f"  ---")
    print(f"  Objective (sim+stab-cost): {objective}")
    return ok

if __name__ == '__main__':
    import argparse
    import time
    import subprocess
    
    parser = argparse.ArgumentParser(description='Hermax Solver for HCORAP')
    parser.add_argument('instance', help='Path to instance file')
    parser.add_argument('--solver', help='Path to external MaxSAT solver (e.g. ./solver/EvalMaxSAT_bin)', default=None)
    args = parser.parse_args()
    
    print(f"\n[INFO] Parsing: {args.instance}")
    t0 = time.time()
    inst = HCORAPInstance(args.instance)
    print(f"[INFO] Parsed in {time.time()-t0:.3f}s: {inst}")
    
    print("\n[INFO] Encoding with Hermax...")
    t0 = time.time()
    enc = HCORAPEncodingHermax(inst)
    print(f"[INFO] Encoded in {time.time()-t0:.3f}s")
    
    if args.solver:
        print(f"\n[INFO] Solving with external solver: {args.solver}...")
        t0 = time.time()
        wcnf_path = "temp_hermax.wcnf"
        # Export to WCNF
        enc.m.to_wcnf().to_file(wcnf_path)
        
        # Run external solver
        process = subprocess.run([args.solver, wcnf_path], capture_output=True, text=True)
        out = process.stdout + process.stderr
        print(f"[INFO] Solved in {time.time()-t0:.3f}s")
        
        cost = None
        model_list = []
        for line in out.splitlines():
            if line.startswith('o '):
                cost = int(line.split()[1])
            elif line.startswith('v '):
                for x in line.split()[1:]:
                    if x.strip() == '0' or not x.strip(): continue
                    if len(x) > 10 and all(c in '01' for c in x):
                        for i, c in enumerate(x):
                            if c == '1': model_list.append(i + 1)
                            elif c == '0': model_list.append(-(i + 1))
                    else:
                        model_list.append(int(x))
                
        if cost is not None:
            print(f"\n[INFO] Optimum found by {args.solver}! (Falsified penalty: {cost})")
            if model_list:
                class DummyModelResult:
                    def __init__(self, lits):
                        self.s = set(lits)
                    @property
                    def model(self):
                        class ModelDict:
                            def __init__(self, s):
                                self.s = s
                            def __getitem__(self, var):
                                if hasattr(var, 'id'): return var.id in self.s
                                return var in self.s
                        return ModelDict(self.s)
                verify_solution(inst, enc, DummyModelResult(model_list))
        else:
            print("\n[INFO] Could not parse output or UNSAT.")
            print(out[-500:])
    else:
        print("\n[INFO] Solving with Hermax built-in RC2 (Python)...")
        t0 = time.time()
        res = enc.m.solve()
        print(f"[INFO] Solved in {time.time()-t0:.3f}s")
        
        if res.ok:
            print(f"\n[INFO] Optimum found! (Falsified penalty: {res.cost})")
            verify_solution(inst, enc, res)
        else:
            print("\n[INFO] UNSATISFIABLE or solver error")
