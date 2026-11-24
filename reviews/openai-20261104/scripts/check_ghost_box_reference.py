#!/usr/bin/env python3
"""Cross-check the conventional four-leg ghost-box formula in the draft.

Requires NumPy. This does not evaluate a submitted Lean graph or prove an
error bound for the quadrature. Run without arguments for JSON on stdout,
or use --output PATH to save a new record explicitly.
"""

import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
from itertools import combinations
import json
import math
from pathlib import Path
import platform

import numpy as np
from numpy.polynomial.legendre import leggauss


def check():
    # D_j = u + j*v + j^2*w, u=k^2, v=2*k.p, w=p^2.
    # First use D_0 - 2 D_1 + D_2 = 2w, then reduce each triple.
    pairs = list(combinations(range(4), 2))
    coeff = {pair: F(0) for pair in pairs}
    for drop_first, outer in [(0, F(1, 2)), (1, F(-1)), (2, F(1, 2))]:
        triple = [j for j in range(4) if j != drop_first]
        for drop in triple:
            remain = tuple(j for j in triple if j != drop)
            coeff[remain] += outer / F(math.prod(drop - j for j in remain))

    # Exact polynomial verification of
    # w^2 = sum_{j<k} c_jk * product_{m not in {j,k}} D_m.
    polynomial = {(i, j): F(0) for i in range(3) for j in range(i, 3)}
    for pair, value in coeff.items():
        a, b = [j for j in range(4) if j not in pair]
        pa, pb = [1, a, a*a], [1, b, b*b]
        for i in range(3):
            for j in range(3):
                polynomial[tuple(sorted((i, j)))] += value * pa[i] * pb[j]
    assert polynomial == {(i, j): F(int((i, j) == (2, 2)))
                          for i in range(3) for j in range(i, 3)}

    by_gap = {d: sum(v for (j, k), v in coeff.items() if k-j == d)
              for d in [1, 2, 3]}
    assert by_gap == {1: F(5, 12), 2: F(-2, 3), 3: F(1, 4)}
    assert sum(v*d**4 for d, v in by_gap.items()) == 10
    c_box = 46/15 + (32/15)*math.log(2) - (81/20)*math.log(3)

    # Independent simplex quadrature. The substitution has Jacobian
    # (1-u)^2*(1-v): x0=u, x1=(1-u)v, x2=(1-u)(1-v)z,
    # x3=(1-u)(1-v)(1-z), and V=sum j^2*xj-(sum j*xj)^2.
    rows = []
    for n in [16, 32, 64, 96, 144]:
        nodes, weights = leggauss(n)
        nodes, weights = (nodes+1)/2, weights/2
        v, z = nodes[:, None], nodes[None, :]
        weight_vz = weights[:, None]*weights[None, :]
        integral = 0.0
        for u, weight_u in zip(nodes, weights):
            x1 = (1-u)*v
            x2 = (1-u)*(1-v)*z
            x3 = (1-u)*(1-v)*(1-z)
            variance = x1+4*x2+9*x3-(x1+2*x2+3*x3)**2
            assert np.all(variance > 0)
            integral += weight_u*np.sum(
                weight_vz*(1-u)**2*(1-v)*np.log(variance))
        value = -6*integral
        rows.append({"nodes_per_axis": n, "c_box": float(value),
                     "error_vs_analytic": float(value-c_box)})
    assert abs(rows[-1]["error_vs_analytic"]) < 1e-8

    # Floating-point sanity check, in addition to the exact identity above.
    rng = np.random.default_rng(20261116)
    worst = 0.0
    p = np.array([1., 0., 0., 0.])
    for _ in range(100):
        k = rng.normal(size=4)
        denominators = [np.dot(k+j*p, k+j*p) for j in range(4)]
        lhs = 1/math.prod(denominators)
        rhs = sum(float(value)/(denominators[j]*denominators[m])
                  for (j, m), value in coeff.items())
        worst = max(worst, abs(lhs-rhs)/max(abs(lhs), 1e-16))
    assert worst < 1e-9

    return {
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Independent conventional ghost-box reference only. No submitted-graph or lattice comparison; no Lean run; no certified quadrature error bound.",
        "python": platform.python_version(), "numpy": np.__version__,
        "exact_denominator_polynomial_identity": True,
        "pair_coefficients": {f"{j},{k}": str(v) for (j, k), v in coeff.items()},
        "bubble_weights": {str(k): str(v) for k, v in by_gap.items()},
        "c_box_exact": "46/15 + (32/15) log(2) - (81/20) log(3)",
        "c_box": c_box, "quadrature": rows,
        "max_rational_identity_relative_error": worst,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    record = json.dumps(check(), indent=2) + "\n"
    if args.output:
        args.output.write_text(record)
    print(record, end="")
