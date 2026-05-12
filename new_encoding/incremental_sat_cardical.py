"""
Incremental weighted MaxSAT: SAT + Cardinality bound (via literal expansion).

Uses ``CardEnc.atmost`` with ``EncType.totalizer``. This "unrolls" weights
(e.g. weight 5 becomes 5 copies of the literal). This can be faster for small
weights but potentially very large for large weights.
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


def _card_atmost_clauses(enc, neg_lits, weights, bound):
    from pysat.card import CardEnc, EncType
    # Expand literals by their weights to use cardinality encoding
    expanded_lits = []
    for lit, w in zip(neg_lits, weights):
        expanded_lits.extend([lit] * w)

    cnf = CardEnc.atmost(
        lits=expanded_lits,
        bound=bound,
        top_id=enc.vm.num_vars,
        encoding=EncType.totalizer,
    )
    if cnf.nv > enc.vm.num_vars:
        while enc.vm.num_vars < cnf.nv:
            enc.vm.new_var()
    return cnf.clauses


def solve_incremental(enc: HCORAPEncoding, solver_name="cadical153", search_mode="linear"):
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
    print(f"[INFO] Cardinality obj (unrolled): {len(obj_pairs)} lits, "
          f"expanded to {total_W} terms (CardEnc.totalizer)")

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
            # Use cardinality encoding with expanded literals
            card_clauses = _card_atmost_clauses(
                enc, neg_lits, weights, falsified_bound)
            for cl in card_clauses:
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
            card_clauses = _card_atmost_clauses(
                enc, neg_lits, weights, falsified_bound)
            for cl in card_clauses:
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
        description="Incremental SAT for HCORAP (CardEnc totalizer + assumptions)")
    parser.add_argument("instance", help="Path to instance file")
    parser.add_argument("--solver", default="cadical153",
                        choices=["glucose4", "cadical153", "minisat22"],
                        help="SAT backend (default: glucose4)")
    parser.add_argument(
        "--search-mode",
        default="linear",
        choices=["binary", "linear"],
        help="Search strategy for objective bound (default: linear)",
    )
    args = parser.parse_args()

    print("=" * 60)
    print("  HCORAP Incremental SAT (Cardinality + assumptions)")
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
