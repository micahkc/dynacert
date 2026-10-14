"""Sample-size and confidence calculations for Monte Carlo validation.

The two statements dynacert reports are proved in Lean (`Dynacert/Prob/Scenario.lean`) for
`N` i.i.d. samples from a distribution `μ` over scenarios and a measurable performance `g`:

* `scenario_bound`: P^N[ μ{g > max_i g(ωᵢ)} > ε ] ≤ (1 - ε)^N;
* `zero_failure_bound`: if μ{g > b} ≥ ε, then P^N[ all g(ωᵢ) ≤ b ] ≤ (1 - ε)^N.

So with confidence `1 - β`, `β = (1 - ε)^N`, the sample maximum is a `(1 - ε)`-quantile of `g`,
and a run with no sample above `b` shows `μ{g > b} < ε`. Confidence levels are computed here in
exact rational arithmetic; `ε` is rounded up, never down.

`wilks_confidence` (discarding the `k` largest samples), `clopper_pearson` and `dkw` are standard
results that are *not* proved in Lean; reports label them as such.
"""

from __future__ import annotations

import math
from fractions import Fraction


def _frac(x) -> Fraction:
    return x if isinstance(x, Fraction) else Fraction(str(x))


def confidence_failure(n: int, eps) -> Fraction:
    """`β = (1 - ε)^N`: the probability that the scenario statement fails (exact)."""
    eps = _frac(eps)
    if not 0 <= eps <= 1:
        raise ValueError("eps must be in [0, 1]")
    return (1 - eps) ** n


def samples_for(eps, beta) -> int:
    """Smallest `N` with `(1 - ε)^N ≤ β` (checked exactly)."""
    eps, beta = _frac(eps), _frac(beta)
    if not (0 < eps < 1 and 0 < beta < 1):
        raise ValueError("need 0 < eps < 1 and 0 < beta < 1")
    n = max(0, math.ceil(math.log(float(beta)) / math.log1p(-float(eps))) - 1)
    while confidence_failure(n, eps) > beta:
        n += 1
    return n


def eps_for(n: int, beta, digits: int = 4) -> Fraction:
    """A small `ε` with `(1 - ε)^N ≤ β`, rounded *up* to `digits` significant digits."""
    beta = _frac(beta)
    if n <= 0:
        return Fraction(1)
    e = -math.expm1(math.log(float(beta)) / n)
    scale = 10 ** (digits - 1 - math.floor(math.log10(e))) if e > 0 else 10 ** digits
    eps = Fraction(math.ceil(e * scale), scale)
    while confidence_failure(n, eps) > beta:  # float rounding: nudge up until exact check holds
        eps += Fraction(1, scale)
    return min(eps, Fraction(1))


def wilks_confidence_failure(n: int, k: int, eps) -> Fraction:
    """P[Binomial(N, ε) ≤ k]: the probability that the (k+1)-th largest sample is *not* a
    `(1 - ε)`-quantile bound (Wilks; exact). `k = 0` is `confidence_failure`. Not proved in
    Lean for `k > 0`."""
    eps = _frac(eps)
    return sum(Fraction(math.comb(n, j)) * eps ** j * (1 - eps) ** (n - j) for j in range(k + 1))


def clopper_pearson(k: int, n: int, beta: float = 1e-3) -> tuple[float, float]:
    """Exact two-sided `1 - β` binomial interval for a probability from `k` hits in `n`
    trials (not proved in Lean)."""
    from scipy.stats import beta as B

    lo = 0.0 if k == 0 else float(B.ppf(beta / 2, k, n - k + 1))
    hi = 1.0 if k == n else float(B.ppf(1 - beta / 2, k + 1, n - k))
    return lo, hi


def dkw(n: int, beta: float = 1e-3) -> float:
    """Dvoretzky–Kiefer–Wolfowitz: with probability ≥ 1 - β the empirical CDF is within this
    distance of the true CDF, uniformly (Massart's constant; not proved in Lean)."""
    return math.sqrt(math.log(2 / beta) / (2 * n))
