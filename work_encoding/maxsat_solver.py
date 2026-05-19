import time
import argparse
import subprocess
from pathlib import Path

from pysat.formula import WCNF
from pysat.examples.rc2 import RC2

from hcorap_encoding import HCORAPInstance, HCORAPEncoding, verify_solution
# from hcorap_encoding_new import HCORAPInstance, HCORAPEncoding, verify_solution
# from hcorap_encoding_binary import HCORAPInstance, HCORAPEncoding, verify_solution
from hcorap_wcnf import (
    load_hcorap2sat_wcnf,
    parse_wmaxcdcl_stats,
    parse_generic_maxsat_cost,
    parse_maxsat_status,
    parse_maxsat_model,
    resolve_solver_exe,
    run_external_solver,
    sum_soft_weights,
)


def solve_maxsat(enc: HCORAPEncoding):
    """
    Solve using PySAT's RC2 (core-guided MaxSAT solver).

    Creates a WCNF formula with:
      - Hard clauses: all constraints (weight = ∞)
      - Soft clauses: objective components with finite weights
    RC2 maximises total weight of satisfied soft clauses.
    """
    wcnf = WCNF()

    for cl in enc.hard_clauses:
        wcnf.append(cl)

    for lits, w in enc.soft_clauses:
        if isinstance(lits, int):
            wcnf.append([lits], weight=w)
        elif isinstance(lits, list):
            wcnf.append(lits, weight=w)

    total_W = sum(w for _, w in enc.soft_clauses)
    print(f"[INFO] WCNF: {wcnf.nv} vars, "
          f"{len(wcnf.hard)} hard, {len(wcnf.soft)} soft, W={total_W}")

    t0 = time.time()
    with RC2(wcnf) as rc2:
        model = rc2.compute()
        cost = rc2.cost
    t_solve = time.time() - t0

    if model is None:
        print(f"[INFO] UNSATISFIABLE ({t_solve:.2f}s)")
        return False, None

    # RC2: rc2.cost = total weight of *falsified* soft clauses (standard MaxSAT cost).
    # EvalMaxSAT / many solvers print successive `o` lines as this cost (lower is better).
    # Satisfied soft weight = total_W - cost (what RC2 effectively maximizes).
    satisfied_w = total_W - cost
    print(f"[INFO] RC2: falsified_soft_weight(cost)={cost}, "
          f"satisfied_soft_weight={satisfied_w}, total_soft_W={total_W} "
          f"({t_solve:.2f}s)")
    print(f"[INFO] Compare external `o` / optimum cost to falsified_soft_weight "
          f"({cost}), not to satisfied_soft_weight ({satisfied_w}); "
          f"note: cost + satisfied = total_soft_W.")
    return (satisfied_w, model)


def solve_external(enc: HCORAPEncoding, solver_exe: str, instance_name: str):
    """
    Solve using an external MaxSAT solver.
    1. Dumps the encoding to a temporary WCNF file.
    2. Runs the solver.
    3. Parses the output (cost and model).
    """
    wcnf = WCNF()
    for cl in enc.hard_clauses:
        wcnf.append(cl)
    for lits, w in enc.soft_clauses:
        if isinstance(lits, int):
            wcnf.append([lits], weight=w)
        elif isinstance(lits, list):
            wcnf.append(lits, weight=w)

    temp_wcnf = Path(f"temp_{instance_name}.wcnf")
    wcnf.to_file(temp_wcnf)
    print(f"[INFO] Encoding dumped to {temp_wcnf}")

    print(f"[INFO] Running external solver: {solver_exe}...")
    t0 = time.time()
    code, out = run_external_solver(temp_wcnf, solver_exe)
    t_solve = time.time() - t0

    # Try to clean up
    try:
        temp_wcnf.unlink()
    except:
        pass

    # Parse
    status = parse_maxsat_status(out)
    cost = parse_generic_maxsat_cost(out)
    model = parse_maxsat_model(out)

    if status == "UNSATISFIABLE" or code == 20:
        print(f"[INFO] UNSATISFIABLE ({t_solve:.2f}s)")
        return False, None

    if cost is not None:
        total_soft_W = sum(w for _, w in enc.soft_clauses)
        satisfied_w = total_soft_W - cost
        print(f"[INFO] External Solver: falsified_soft_weight(cost)={cost}, "
              f"satisfied_soft_weight={satisfied_w}, total_soft_W={total_soft_W} "
              f"({t_solve:.2f}s)")
        return satisfied_w, model
    else:
        # Try WMaxCDCL format
        stats = parse_wmaxcdcl_stats(out)
        if stats:
            opt, msat, _ = stats
            print(f"[INFO] External Solver (WMaxCDCL): optimal={opt}, maxsat={msat} ({t_solve:.2f}s)")
            return None, model # satisfied_w is hard to guess for WMaxCDCL without more info

    if status == "OPTIMUM FOUND" or status == "SATISFIABLE":
        # We had status but no cost/model? That's weird but possible
        print(f"[INFO] External Solver: status={status} ({t_solve:.2f}s)")
        return None, model

    print(f"[ERROR] External solver failed or output could not be parsed (code {code}).")
    return None, None


def main():
    parser = argparse.ArgumentParser(
        description='MaxSAT (RC2) solver for HCORAP')
    parser.add_argument('instance', help='Path to instance file')
    parser.add_argument(
        '--dump-wcnf', metavar='PATH',
        help='Write the Python encoding as standard WCNF (for EvalMaxSAT etc.)')
    parser.add_argument(
        '--solver', '--wmaxcdcl-exe', metavar='EXE', default=None,
        help='Path to external MaxSAT solver to run on sidecar .wcnf (e.g. EvalMaxSAT_bin)')
    args = parser.parse_args()

    print("=" * 60)
    print("  HCORAP MaxSAT Solver (RC2)")
    print("=" * 60)

    # Parse
    print(f"\n[INFO] Parsing: {args.instance}")
    t0 = time.time()
    inst = HCORAPInstance(args.instance)
    print(f"[INFO] {inst}  ({time.time()-t0:.3f}s)")

    # Encode
    print(f"\n[INFO] Encoding...")
    t0 = time.time()
    enc = HCORAPEncoding(inst)
    t_enc = time.time() - t0
    print(f"[INFO] Encoded in {t_enc:.2f}s: "
          f"{enc.vm.num_vars} vars, {len(enc.hard_clauses)} hard, "
          f"{len(enc.soft_clauses)} soft")
    print("[INFO] EvalMaxSAT/WMaxCDCL `o` is usually *falsified* soft weight "
          "(minimize). Compare that to falsified_soft_weight from RC2, not to "
          "satisfied_soft_weight. hcorap2sat WCNF differs from this encoder—use "
          "--dump-wcnf to export this CNF for external solvers.")

    if args.dump_wcnf:
        wcnf = WCNF()
        for cl in enc.hard_clauses:
            wcnf.append(cl)
        for lits, w in enc.soft_clauses:
            if isinstance(lits, int):
                wcnf.append([lits], weight=w)
            elif isinstance(lits, list):
                wcnf.append(lits, weight=w)
        wcnf.to_file(args.dump_wcnf)
        print(f"[INFO] WCNF written to {args.dump_wcnf}")

    # External solver on Python encoding
    result = None
    if args.solver:
        sexe = resolve_solver_exe(args.solver)
        if sexe:
            print(f"\n[INFO] Solving with external solver...")
            result = solve_external(enc, sexe, Path(args.instance).stem)
        else:
            print(f"[ERROR] Solver executable not found: {args.solver}")
            return
    else:
        # Solve with RC2
        print(f"\n[INFO] Solving (MaxSAT RC2)...")
        result = solve_maxsat(enc)

    if result is not None:
        obj, model = result
        if obj is False:
            print(f"\n[INFO] UNSATISFIABLE")
        elif model:
            verify_solution(inst, enc, model)
        elif obj is not None:
            print(f"[INFO] Optimum found: {obj} (but no model parsed for verification)")
    else:
        print(f"\n[INFO] Could not find a solution (solver error).")

    print()


if __name__ == '__main__':
    main()
