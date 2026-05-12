"""
Load weighted CNF produced by hcorap2sat (-f=dimacs).

Format (non-standard DIMACS):
  - Comment line "c <top> 0" declares total soft weight (optional).
  - "h <lits> 0" hard clauses.
  - "<weight> <lits> 0" soft weighted clauses.
"""

from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path

from pysat.formula import WCNF


def load_hcorap2sat_wcnf(path: str | os.PathLike) -> tuple[WCNF, int]:
    """
    Parse hcorap2sat dimacs output into PySAT WCNF.

    Returns (wcnf, top_hint) where top_hint is the integer from the first
    "c <int> 0" line if present, else 0.
    """
    wcnf = WCNF()
    top_hint = 0
    p = Path(path)

    with p.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith("c "):
                rest = line[2:].strip().split()
                if len(rest) >= 1 and rest[0].lstrip("-").isdigit():
                    top_hint = int(rest[0])
                continue
            if line.startswith("h "):
                cl = [int(x) for x in line[2:].split()]
                assert cl[-1] == 0
                wcnf.append(cl[:-1])
                continue
            parts = line.split()
            w = int(parts[0])
            cl = [int(x) for x in parts[1:]]
            assert cl[-1] == 0
            wcnf.append(cl[:-1], weight=w)

    return wcnf, top_hint


def sum_soft_weights(wcnf: WCNF) -> int:
    return sum(wcnf.wght)


_WMAXCDCL_STATS = re.compile(
    r"optimal:\s*(\d+),\s*maxsat:\s*(\d+),\s*hardConflicts:\s*(\d+)",
    re.IGNORECASE,
)


def parse_wmaxcdcl_stats(output: str) -> tuple[int, int, int] | None:
    m = _WMAXCDCL_STATS.search(output)
    if not m:
        return None
    return int(m.group(1)), int(m.group(2)), int(m.group(3))


def parse_generic_maxsat_cost(output: str) -> int | None:
    """
    Parse standard MaxSAT output for the last 'o <cost>' line.
    """
    costs = re.findall(r"^o\s+(\d+)", output, re.MULTILINE)
    if costs:
        return int(costs[-1])
    return None


def parse_maxsat_model(output: str) -> list[int] | None:
    """
    Parse standard MaxSAT output for the 'v' line.
    Supports both:
    1. Space-separated integers (DIMACS): v 1 -2 3 0
    2. Bitstring (EvalMaxSAT): v 00101...
    Returns a list of literals (positive/negative integers).
    """
    model = []
    found = False
    for line in output.splitlines():
        if line.startswith("v "):
            found = True
            content = line[2:].strip()
            
            # Check if it's a bitstring (contains only 0, 1 and no spaces except at ends)
            if all(c in '01' for c in content) and ' ' not in content:
                # Bitstring format: index i means var i+1. '1' is True, '0' is False.
                for i, bit in enumerate(content):
                    var_id = i + 1
                    model.append(var_id if bit == '1' else -var_id)
            else:
                # Standard DIMACS format
                parts = content.split()
                for p in parts:
                    try:
                        val = int(p)
                        if val != 0:
                            model.append(val)
                    except ValueError:
                        continue
    return model if found else None


def resolve_solver_exe(cli_path: str | None) -> str | None:
    if cli_path:
        if os.path.isfile(cli_path):
            return cli_path
        return None
    
    env = os.environ.get("HCORAP_SOLVER") or os.environ.get("HCORAP_WMAXCDCL")
    if env and os.path.isfile(env):
        return env
    
    return None


def run_external_solver(wcnf_path: str | os.PathLike, exe: str, timeout: float = 600.0):
    """Run an external MaxSAT solver on WCNF; return (returncode, combined_stdout_stderr)."""
    p = Path(wcnf_path)
    try:
        proc = subprocess.run(
            [exe, str(p)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return proc.returncode, proc.stdout + proc.stderr
    except Exception as e:
        return -1, str(e)
