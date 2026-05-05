#!/usr/bin/env python3
"""
MaxSAT solver for the HCORAP problem.

Uses PySAT's RC2 (core-guided MaxSAT solver) to solve the
partial weighted MaxSAT encoding in a single invocation.

Corresponds to Section 6.3 in doc/main.tex.

Usage:
    python3 maxsat_solver.py <instance>
    python3 maxsat_solver.py instance1.txt   # uses instance1.wcnf if present

  If ``INSTANCE.wcnf`` exists (e.g. from hcorap2sat), runs WMaxCDCL when the
  binary is found (``./solver/wmaxcdcl_static`` or ``HCORAP_WMAXCDCL``), then
  RC2 on that WCNF for EvalMaxSAT-comparable ``optimal`` / cost.
"""

import time
import argparse
import subprocess
from pathlib import Path

from pysat.formula import WCNF
from pysat.examples.rc2 import RC2

from hcorap_encoding import HCORAPInstance, HCORAPEncoding, verify_solution
from hcorap_wcnf import (
    load_hcorap2sat_wcnf,
    parse_wmaxcdcl_stats,
    resolve_wmaxcdcl_exe,
    run_wmaxcdcl,
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
        return None

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


def report_sidecar_hcorap_wcnf(instance_path: str, wmaxcdcl_exe: str | None):
    """
    If INSTANCE.wcnf exists (hcorap2sat), report stats comparable to WMaxCDCL /
    EvalMaxSAT. When the WMaxCDCL binary is available, print its optimal/maxsat/
    hardConflicts line; otherwise fall back to RC2 on that WCNF.
    """
    sidecar = Path(instance_path).with_suffix(".wcnf")
    if not sidecar.is_file():
        return

    print(f"\n[INFO] Sidecar hcorap2sat WCNF: {sidecar.name}")

    if wmaxcdcl_exe:
        try:
            code, out = run_wmaxcdcl(sidecar, wmaxcdcl_exe)
            stats = parse_wmaxcdcl_stats(out)
            if stats:
                opt, msat, hcf = stats
                print(f"[INFO] WMaxCDCL: optimal: {opt}, maxsat: {msat}, "
                      f"hardConflicts: {hcf}")
                return
            print(f"[INFO] WMaxCDCL exit {code}: could not parse "
                  f"optimal/maxsat/hardConflicts; falling back to RC2 on sidecar.")
        except FileNotFoundError:
            print(f"[INFO] WMaxCDCL executable not found: {wmaxcdcl_exe}")
        except subprocess.TimeoutExpired:
            print("[INFO] WMaxCDCL timed out; falling back to RC2 on sidecar.")
        except Exception as e:
            print(f"[INFO] WMaxCDCL run failed ({e}); falling back to RC2 on sidecar.")

    wcnf, top_decl = load_hcorap2sat_wcnf(sidecar)
    total_w = sum_soft_weights(wcnf)
    t0 = time.time()
    with RC2(wcnf) as rc2:
        _ = rc2.compute()
        cost = rc2.cost
    t_rc2 = time.time() - t0
    sat_w = total_w - cost
    print(f"[INFO] RC2 on sidecar WCNF: optimal (falsified cost): {cost}, "
          f"satisfied_soft_weight: {sat_w}, total_soft_W: {total_w} "
          f"(declared top {top_decl}, {t_rc2:.2f}s)")
    print("[INFO] EvalMaxSAT `o` matches optimal (falsified). "
          "WMaxCDCL 'maxsat' may differ from satisfied_soft_weight after its "
          "preprocessing.")


def main():
    parser = argparse.ArgumentParser(
        description='MaxSAT (RC2) solver for HCORAP')
    parser.add_argument('instance', help='Path to instance file')
    parser.add_argument(
        '--dump-wcnf', metavar='PATH',
        help='Write the Python encoding as standard WCNF (for EvalMaxSAT etc.)')
    parser.add_argument(
        '--no-wmaxcdcl', action='store_true',
        help='Do not run WMaxCDCL on INSTANCE.wcnf (still run RC2 on it if present)')
    parser.add_argument(
        '--wmaxcdcl-exe', metavar='EXE', default=None,
        help='Path to wmaxcdcl_static (default: auto-detect or HCORAP_WMAXCDCL)')
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

    wexe = None
    if not args.no_wmaxcdcl:
        wexe = resolve_wmaxcdcl_exe(args.wmaxcdcl_exe)
    report_sidecar_hcorap_wcnf(args.instance, wexe)

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

    # Solve
    print(f"\n[INFO] Solving (MaxSAT RC2)...")
    t0 = time.time()
    result = solve_maxsat(enc)
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
