"""
Incremental weighted MaxSAT: SAT + PB bound (PyPBLib sorting networks).

Avoids weight expansion (no ``[lit] * w``). Uses ``PBEnc.atmost`` with
``EncType.sortnetwrk``. Install: ``pip install pypblib``.

Each iteration adds PB clauses under a fresh activation literal and calls
``solve(assumptions=[act])`` so the solver base stays the hard CNF + soft
reifications; only the current bound is forced active.
"""
import time
import argparse

from pysat.solvers import Solver

from hcorap_encoding import (
    HCORAPInstance,
    HCORAPEncoding,
    verify_solution,
    evaluate_cop_objective,
)


def _pb_weighted_atmost_clauses(enc, neg_lits, weights, bound):
    try:
        from pysat.pb import PBEnc, EncType
    except Exception as e:
        raise ImportError(
            "incremental_sat needs PyPBLib. Run: pip install pypblib"
        ) from e
    cnf = PBEnc.atmost(
        lits=neg_lits,
        weights=weights,
        bound=bound,
        top_id=enc.vm.num_vars,
        encoding=EncType.sortnetwrk,
    )
    if cnf.nv > enc.vm.num_vars:
        while enc.vm.num_vars < cnf.nv:
            enc.vm.new_var()
    return cnf.clauses


def solve_incremental(enc: HCORAPEncoding, solver_name="glucose4", search_mode="binary"):
    solver = Solver(name=solver_name)
    for cl in enc.hard_clauses:
        solver.add_clause(cl)

    print(f"[INFO] Solver: {solver_name}, {enc.vm.num_vars} vars, "
          f"{len(enc.hard_clauses)} hard, {len(enc.soft_clauses)} soft")

    obj_pairs = []
    for lits, w in enc.soft_clauses:
        if isinstance(lits, int):
            obj_pairs.append((lits, w))
        elif len(lits) == 1:
            obj_pairs.append((lits[0], w))
        else:
            aux = enc.vm.new_var()
            for lit in lits:
                solver.add_clause([-lit, aux])
            solver.add_clause([-aux] + lits)
            obj_pairs.append((aux, w))

    total_W = sum(w for _, w in obj_pairs)
    print(f"[INFO] Weighted obj: {len(obj_pairs)} lits, W={total_W} "
          f"(PBEnc.sortnetwrk, no literal duplication)")

    t_start = time.time()
    n_calls = 0

    n_calls += 1
    if not solver.solve():
        print("[INFO] UNSATISFIABLE")
        solver.delete()
        return None

    model = solver.get_model()
    model_set = set(model)
    best_obj = sum(w for lit, w in obj_pairs if lit in model_set)
    best_model = model
    print(f"  [{n_calls:2d}] Initial: maxsat_soft_sum={best_obj}")

    neg_lits = [-lit for lit, _ in obj_pairs]
    weights = [w for _, w in obj_pairs]

    if search_mode == "linear":
        while best_obj < total_W:
            target = best_obj + 1
            falsified_bound = total_W - target
            if falsified_bound < 0:
                break

            act = enc.vm.new_var()
            pb_clauses = _pb_weighted_atmost_clauses(
                enc, neg_lits, weights, falsified_bound)
            for cl in pb_clauses:
                solver.add_clause([-act] + cl)

            n_calls += 1
            t0 = time.time()
            sat = solver.solve(assumptions=[act])
            t_call = time.time() - t0

            if sat:
                model = solver.get_model()
                model_set = set(model)
                obj = sum(w for lit, w in obj_pairs if lit in model_set)
                print(f"  [{n_calls:2d}] target>={target:4d}  SAT   "
                      f"maxsat_soft_sum={obj:4d}  ({t_call:.3f}s)")
                best_obj = obj
                best_model = model
            else:
                print(f"  [{n_calls:2d}] target>={target:4d}  UNSAT "
                      f"             ({t_call:.3f}s)")
                break
    else:
        # Binary search cuts SAT calls from O(W) to O(log W).
        lo, hi = best_obj + 1, total_W
        while lo <= hi:
            target = (lo + hi) // 2
            falsified_bound = total_W - target

            act = enc.vm.new_var()
            pb_clauses = _pb_weighted_atmost_clauses(
                enc, neg_lits, weights, falsified_bound)
            for cl in pb_clauses:
                solver.add_clause([-act] + cl)

            n_calls += 1
            t0 = time.time()
            sat = solver.solve(assumptions=[act])
            t_call = time.time() - t0

            if sat:
                model = solver.get_model()
                model_set = set(model)
                obj = sum(w for lit, w in obj_pairs if lit in model_set)
                print(f"  [{n_calls:2d}] target>={target:4d}  SAT   "
                      f"maxsat_soft_sum={obj:4d}  ({t_call:.3f}s)")
                if obj > best_obj:
                    best_obj = obj
                    best_model = model
                lo = target + 1
            else:
                print(f"  [{n_calls:2d}] target>={target:4d}  UNSAT "
                      f"             ({t_call:.3f}s)")
                hi = target - 1

    t_total = time.time() - t_start
    print(f"[INFO] Done: {n_calls} calls, {t_total:.2f}s, "
          f"maxsat_soft_sum={best_obj}")

    solver.delete()
    return (best_obj, best_model)


def main():
    parser = argparse.ArgumentParser(
        description="Incremental SAT for HCORAP (PBEnc sortnetwrk + assumptions)")
    parser.add_argument("instance", help="Path to instance file")
    parser.add_argument("--solver", default="glucose4",
                        choices=["glucose4", "cadical153", "minisat22"],
                        help="SAT backend (default: glucose4)")
    parser.add_argument(
        "--search-mode",
        default="binary",
        choices=["binary", "linear"],
        help="Search strategy for objective bound (default: binary)",
    )
    args = parser.parse_args()

    print("=" * 60)
    print("  HCORAP Incremental SAT (PB + assumptions)")
    print("=" * 60)

    print(f"\n[INFO] Parsing: {args.instance}")
    t0 = time.time()
    inst = HCORAPInstance(args.instance)
    print(f"[INFO] {inst}  ({time.time()-t0:.3f}s)")

    print(f"\n[INFO] Encoding...")
    t0 = time.time()
    enc = HCORAPEncoding(inst)
    t_enc = time.time() - t0
    print(f"[INFO] Encoded in {t_enc:.2f}s: "
          f"{enc.vm.num_vars} vars, {len(enc.hard_clauses)} hard, "
          f"{len(enc.soft_clauses)} soft")

    print(f"\n[INFO] Solving (incremental)...")
    t0 = time.time()
    try:
        result = solve_incremental(
            enc, solver_name=args.solver, search_mode=args.search_mode
        )
    except ImportError as e:
        print(f"[FATAL] {e}")
        return
    t_solve = time.time() - t0

    if result is not None:
        obj, model = result
        print(f"\n[INFO] Total solve time: {t_solve:.2f}s")
        ms = set(model)
        assigns = [(a, s, t) for (a, s, t), v in enc.x.items() if v in ms]
        sim, stab, cost, cop = evaluate_cop_objective(inst, assigns)
        print(f"[INFO] COP (sim + stab − cost): {cop} "
              f"(sim={sim}, stab={stab}, cost={cost}; "
              f"maxsat_soft_sum={obj})")
        verify_solution(inst, enc, model)
    else:
        print(f"\n[INFO] UNSATISFIABLE ({t_solve:.2f}s)")

    print()


if __name__ == "__main__":
    main()
