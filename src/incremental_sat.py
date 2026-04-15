import time
import argparse
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

from hcorap_encoding import HCORAPInstance, HCORAPEncoding, verify_solution


def solve_incremental(enc: HCORAPEncoding, solver_name='glucose4'):
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
            for l in lits:
                solver.add_clause([-l, aux])
            solver.add_clause([-aux] + lits)
            obj_pairs.append((aux, w))

    total_W = sum(w for _, w in obj_pairs)
    print(f"[INFO] Weighted obj: {len(obj_pairs)} lits, W={total_W}")

    t_start = time.time()
    n_calls = 0

    n_calls += 1
    if not solver.solve():
        print("[INFO] UNSATISFIABLE")
        solver.delete()
        return None

    model = solver.get_model()
    model_set = set(model)
    best_obj = sum(w for l, w in obj_pairs if l in model_set)
    best_model = model
    print(f"  [{n_calls:2d}] Initial: obj={best_obj}")

    while best_obj < total_W:
        target = best_obj + 1

        neg_lits = [-l for l, w in obj_pairs]
        weights = [w for l, w in obj_pairs]
        bound = total_W - target

        if bound < 0:
            break

        expanded = []
        for nl, wt in zip(neg_lits, weights):
            expanded.extend([nl] * wt)

        cnf = CardEnc.atmost(expanded, bound=bound,
                             top_id=enc.vm.num_vars,
                             encoding=EncType.totalizer)
        if cnf.nv > enc.vm.num_vars:
            while enc.vm.num_vars < cnf.nv:
                enc.vm.new_var()

        for cl in cnf.clauses:
            solver.add_clause(cl)

        n_calls += 1
        t0 = time.time()
        sat = solver.solve()
        t_call = time.time() - t0

        if sat:
            model = solver.get_model()
            model_set = set(model)
            obj = sum(w for l, w in obj_pairs if l in model_set)
            print(f"  [{n_calls:2d}] target>={target:4d}  SAT   "
                  f"obj={obj:4d}  ({t_call:.3f}s)")
            best_obj = obj
            best_model = model
        else:
            print(f"  [{n_calls:2d}] target>={target:4d}  UNSAT "
                  f"             ({t_call:.3f}s)")
            break

    t_total = time.time() - t_start
    print(f"[INFO] Done: {n_calls} calls, {t_total:.2f}s, optimal={best_obj}")

    solver.delete()
    return (best_obj, best_model)


def main():
    parser = argparse.ArgumentParser(
        description='Incremental SAT solver for HCORAP')
    parser.add_argument('instance', help='Path to instance file')
    parser.add_argument('--solver', default='glucose4',
                        choices=['glucose4', 'cadical153', 'minisat22'],
                        help='SAT solver backend (default: glucose4)')
    args = parser.parse_args()

    print("=" * 60)
    print("  HCORAP Incremental SAT Solver")
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

    print(f"\n[INFO] Solving (incremental top-down)...")
    t0 = time.time()
    result = solve_incremental(enc, solver_name=args.solver)
    t_solve = time.time() - t0

    if result is not None:
        obj, model = result
        print(f"\n[INFO] Total solve time: {t_solve:.2f}s")
        verify_solution(inst, enc, model)
    else:
        print(f"\n[INFO] UNSATISFIABLE ({t_solve:.2f}s)")

    print()


if __name__ == '__main__':
    main()
