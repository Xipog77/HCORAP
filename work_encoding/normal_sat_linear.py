"""
normal_sat: warm-up on hard constraints + binary search on MaxSAT soft weight.

Phase 1: SAT with hard clauses only, multiple runs with ``set_phases`` jitter;
take UB = max COP (Similarity + Stability − Cost) over models.

Phase 2: binary search for the largest Mid such that hard ∧ (∑ w_i·ℓ_i ≥ Mid)
is SAT, using ``PBEnc.atleast`` (sorting-network encoding) under assumptions.

Requires: pip install pypblib
"""
from __future__ import annotations

import argparse
import random
import time

from pysat.solvers import Solver

from hcorap_encoding import (
    HCORAPInstance,
    HCORAPEncoding,
    evaluate_cop_objective,
    verify_solution,
)


def attach_soft_reification(enc: HCORAPEncoding) -> list[tuple[int, int]]:
    """
    Append CNF for multi-literal soft clauses to enc.hard_clauses once.
    Returns (positive_lit, weight) pairs for the objective.
    """
    pairs = []
    for lits, w in enc.soft_clauses:
        if isinstance(lits, int):
            pairs.append((lits, w))
        elif len(lits) == 1:
            pairs.append((lits[0], w))
        else:
            aux = enc.vm.new_var()
            for lit in lits:
                enc.hard_clauses.append([-lit, aux])
            enc.hard_clauses.append([-aux] + lits)
            pairs.append((aux, w))
    return pairs


def _pb_atleast_clauses(enc, lits, weights, bound):
    from pysat.pb import PBEnc, EncType
    cnf = PBEnc.atleast(
        lits=lits,
        weights=weights,
        bound=bound,
        top_id=enc.vm.num_vars,
        encoding=EncType.sortnetwrk,
    )
    if cnf.nv > enc.vm.num_vars:
        while enc.vm.num_vars < cnf.nv:
            enc.vm.new_var()
    return cnf.clauses


def phase1_warmup(
        enc: HCORAPEncoding,
        obj_pairs: list[tuple[int, int]],
        solver_name: str,
        runs: int = 10,
):
    """Feasible models from hard CNF only; return best COP and max soft-sum."""
    rng = random.Random(42)
    best_cop = None
    best_soft = -1
    best_model = None

    for _ in range(runs):
        solver = Solver(name=solver_name)
        for cl in enc.hard_clauses:
            solver.add_clause(cl)

        phases = []
        for v in range(1, enc.vm.num_vars + 1):
            phases.append(v if rng.random() < 0.5 else -v)
        solver.set_phases(phases)

        ok = solver.solve()
        if ok:
            m = solver.get_model()
            ms = set(m)
            soft = sum(w for lit, w in obj_pairs if lit in ms)
            assigns = [(a, s, t) for (a, s, t), v in enc.x.items() if v in ms]
            _, _, _, cop = evaluate_cop_objective(enc.inst, assigns)
            if best_cop is None or cop > best_cop:
                best_cop = cop
                best_soft = soft
                best_model = m
        solver.delete()

    return best_cop, best_soft, best_model


def phase2_linear_search(
        enc: HCORAPEncoding,
        solver_name: str,
        obj_pairs: list[tuple[int, int]],
        total_W: int,
        start_soft: int = -1,
        start_model: list[int] = None
):
    """Linear search bottom-up for Max soft weight."""
    lits = [lit for lit, _ in obj_pairs]
    weights = [w for _, w in obj_pairs]

    best_soft = start_soft
    best_model = start_model

    curr_bound = best_soft + 1

    while curr_bound <= total_W:
        solver = Solver(name=solver_name)
        for cl in enc.hard_clauses:
            solver.add_clause(cl)

        act = enc.vm.new_var()
        pb_clauses = _pb_atleast_clauses(enc, lits, weights, curr_bound)
        for cl in pb_clauses:
            solver.add_clause([-act] + cl)

        if solver.solve(assumptions=[act]):
            m = solver.get_model()
            ms = set(m)
            # Calculate actual weight of this model
            actual_soft = sum(w for lit, w in obj_pairs if lit in ms)
            best_soft = actual_soft
            best_model = m
            print(f"  [SAT] Bound {curr_bound} -> soft_weight={best_soft}")
            curr_bound = best_soft + 1
        else:
            print(f"  [UNSAT] Bound {curr_bound}")
            break
        solver.delete()

    return best_soft, best_model


def main():
    ap = argparse.ArgumentParser(description="HCORAP normal_sat (warm-up + linear search bottom-up)")
    ap.add_argument("instance")
    ap.add_argument("--solver", default="glucose4")
    ap.add_argument("--warm-runs", type=int, default=10)
    ap.add_argument("--strat", action="store_true", help="Enable stratified coverage")
    args = ap.parse_args()

    try:
        from pysat.pb import PBEnc  # noqa: F401
    except Exception as e:
        print("Requires pypblib: pip install pypblib\n", e)
        return

    print("=" * 60)
    print("  HCORAP normal_sat")
    print("=" * 60)

    inst = HCORAPInstance(args.instance)
    print(f"[INFO] {inst}")

    t0 = time.time()
    enc = HCORAPEncoding(inst, strat=args.strat)
    obj_pairs = attach_soft_reification(enc)
    total_W = sum(w for _, w in obj_pairs)
    print(f"[INFO] Encoded: {enc.vm.num_vars} vars, "
          f"{len(enc.hard_clauses)} hard, {len(enc.soft_clauses)} soft, "
          f"total_soft_W={total_W} ({time.time()-t0:.2f}s)")

    print(f"\n[INFO] Phase 1: {args.warm_runs} SAT calls (hard only)...")
    t0 = time.time()
    best_soft, best_soft_weight, warm_model = phase1_warmup(
        enc, obj_pairs, args.solver, runs=args.warm_runs)
    print(f"[INFO] Warm-up done ({time.time()-t0:.2f}s): "
          f"best COP={best_soft}, best soft-sum={best_soft_weight}")

    print(f"\n[INFO] Phase 2: linear search bottom-up on soft weight "
          f"[{best_soft_weight if best_soft_weight >= 0 else 0}, {total_W}]...")
    t0 = time.time()
    opt_soft_weight, opt_model = phase2_linear_search(
        enc, args.solver, obj_pairs, total_W,
        start_soft=best_soft_weight, start_model=warm_model)
    print(f"[INFO] Phase 2 done ({time.time()-t0:.2f}s): "
          f"optimal soft_sum={opt_soft_weight}")

    if opt_model is not None:
        final_cop = opt_soft_weight + enc.konstant_revenue
        print(f"[RESULT] Optimal COP Objective: {final_cop}")
        verify_solution(inst, enc, opt_model)
    elif warm_model is not None:
        final_cop = best_soft_weight + enc.konstant_revenue
        print(f"[RESULT] Best warm-up COP Objective: {final_cop}")
        print("[INFO] Falling back to warm-up model for verification.")
        verify_solution(inst, enc, warm_model)
    print()


if __name__ == "__main__":
    main()
