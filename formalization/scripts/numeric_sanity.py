#!/usr/bin/env python3
"""Deterministic floating-point sanity checks for the formalized identities.

This is not a proof and is not a substitute for Lean kernel checking.  It is
useful for catching transcription mistakes in the displayed constants and
endpoint substitutions.
"""

from __future__ import annotations

import math
import random
import sys

SEED = 20260815
TRIALS = 2000
RTOL = 2e-10
ATOL = 2e-12


def close(x: float, y: float) -> bool:
    return math.isclose(x, y, rel_tol=RTOL, abs_tol=ATOL)


def require(name: str, x: float, y: float) -> None:
    if not close(x, y):
        raise AssertionError(f"{name}: {x!r} != {y!r}")


def require_le(name: str, x: float, y: float) -> None:
    if x > y and not close(x, y):
        raise AssertionError(f"{name}: {x!r} > {y!r}")


def positive(rng: random.Random, lo: float = 0.05, hi: float = 20.0) -> float:
    return math.exp(rng.uniform(math.log(lo), math.log(hi)))


def main() -> int:
    rng = random.Random(SEED)
    for _ in range(TRIALS):
        H = positive(rng)
        L = positive(rng)
        m = positive(rng)
        b = positive(rng, 0.001, 0.5)
        c0 = positive(rng, 0.001, 0.5)
        C = positive(rng)
        d = positive(rng, 1.0, 50.0)
        p = positive(rng, 0.1, 50.0)
        t = positive(rng)
        c = positive(rng)
        a = positive(rng)
        bscale = positive(rng)

        require(
            "min/max square",
            max(min(H, a) ** 2, min(H, bscale) ** 2),
            min(H, max(a, bscale)) ** 2,
        )

        tau = (b / L) / math.sqrt(p * (d + p))
        theta = min(1.0, H / tau)
        require("endpoint theta", theta * tau, min(H, tau))
        require("endpoint theta square", theta**2 * tau**2, min(H, tau) ** 2)

        gamma = t / (2.0 * H)
        safe_phi_sq = m * t * math.log(2.0) / (2.0**26)
        ladder_phi_sq = m * t * p / (2.0**29)
        require(
            "safe reciprocal",
            1.0 / (gamma * safe_phi_sq),
            (2.0**27) * H / (m * t**2 * math.log(2.0)),
        )
        require(
            "ladder reciprocal",
            1.0 / (gamma * ladder_phi_sq),
            (2.0**30) * H / (m * t**2 * p),
        )
        require(
            "safe one-component value",
            1.0 / (2.0 * (1.0 / (gamma * safe_phi_sq))),
            m * t**2 * math.log(2.0) / ((2.0**28) * H),
        )

        require(
            "ladder coefficient",
            m * theta**2 * b**2 / (2.0 * C * H * L**2 * p * (d + p)),
            (1.0 / (2.0 * C)) * (m / H) * min(H, tau) ** 2,
        )

        M = max(1.0 / math.sqrt(p * (d + p)), 1.0 / d)
        kappa = L / m
        certified = (b / L) * M

        H_adapted = c * M / L
        master_adapted = c0 * (m / H_adapted) * min(H_adapted, certified) ** 2
        adapted_rhs = (c0 / kappa) * min(c, b) ** 2 / c * M
        require("adapted endpoint", master_adapted, adapted_rhs)

        H_sqrt = c / (L * math.sqrt(d))
        master_sqrt = c0 * (m / H_sqrt) * min(H_sqrt, certified) ** 2
        sqrt_rhs = (
            c0 * math.sqrt(d) / (c * kappa)
            * min(c / math.sqrt(d), b * M) ** 2
        )
        require("sqrt-d endpoint", master_sqrt, sqrt_rhs)

        corollary_general = (
            c0
            / (kappa * math.sqrt(d))
            * min(
                c,
                (b**2 / c)
                * max(d / (p * (d + p)), 1.0 / d),
            )
        )
        require("current corollary factorization", sqrt_rhs, corollary_general)

        inverse_scale = min(p * (d + p) / d, d)
        require_le("assumption-free inverse-scale bound", inverse_scale, 2.0 * p)
        corollary_simplified = (
            c0
            / (kappa * math.sqrt(d))
            * min(c, b**2 / (2.0 * c * p))
        )
        require_le(
            "assumption-free corollary simplification",
            corollary_simplified,
            corollary_general,
        )

        psmall = rng.uniform(0.05, d)
        lhs_small = (
            c0 * math.sqrt(d) / (c * kappa)
            * min(c / math.sqrt(d), b / math.sqrt(2.0 * psmall * d)) ** 2
        )
        rhs_small = (
            c0 / (kappa * math.sqrt(d))
            * (min(c, b / math.sqrt(2.0 * psmall)) ** 2 / c)
        )
        require("small-moment factorization", lhs_small, rhs_small)

    print("NUMERIC SANITY PASSED")
    print(f"Seed: {SEED}")
    print(f"Random trials: {TRIALS}")
    print("Checked: min/max gluing, theta identities, reciprocal constants,")
    print("safe/ladder coefficients, both endpoint substitutions, and")
    print("the current assumption-free Corollary 2.2 simplification.")
    print("NOTE: this is not a proof and not a Lean kernel check.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"NUMERIC SANITY FAILED: {exc}", file=sys.stderr)
        raise SystemExit(1)
