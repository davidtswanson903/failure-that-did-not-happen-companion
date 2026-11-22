"""The sieve as a survival model: capacities held, unheld or cut, in closed form.

The rules (the exact statement; the companion's entry Model S proves what this checks)
  R1. Each capacity is in one of three states: held (someone holds its lapse), unheld, or cut.
      Cut is absorbing: a capacity once cut stays cut.
  R2. Each year is tight with chance P, independently of every other year. In a tight year a held
      capacity is cut with chance V and an unheld one with chance U. A calm year cuts nothing.
      The closed forms give the chances for one capacity. Capacities of one city meet the same
      tight years, so one city's shares scatter around them from run to run (one_city_run).
  R3. A held capacity that survives the year loses its holder with chance Q, and is unheld from
      then on. Nothing makes an unheld capacity held again.
  R4. (Survivors' worth only.) Each capacity has a worth w, uniform on [0, 1], and the budget office
      registers a signal s, also uniform on [0, 1], that moves with w: w and s are the normal
      quantiles of a pair of standard normals with correlation RHO. In a tight year an unheld
      capacity is cut with chance U * 2 * (1 - s), which averages U and falls as s rises. Worth
      enters nowhere else.

Reference values. P = 0.4 is the book's sieve's "four years in ten" and Q = 0.02 its holders moving on
at 2 per cent a year. U and V are not given there; they are set here so the chain
reproduces the two 30-year endpoints the book prints from compute_sieve.py, TARGET_UNHELD and
TARGET_HELD. compute_sieve.py draws a different cut chance for each capacity, so its full curves
differ from these; this chain is the closed form, not that script.

 Every result is checked by assertion: the closed forms
against the chain's recursion in exact rational arithmetic, and against a Monte Carlo run of rules
R1 to R4 with a fixed seed. The functions are importable; the notebook in ../notebook uses them.

Run it with `python compute_sieve_chain.py`. It writes sieve_chain.json beside itself.
"""
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np

P, Q = 0.4, 0.02
TARGET_UNHELD, TARGET_HELD, TARGET_YEAR = 0.17, 0.58, 30
SEED = 7
DRAWS = 200_000
HORIZON = 40
RHOS = [0.0, 0.25, 0.5, 0.75]


# ---------------------------------------------------------------- the chain and its closed forms
def rates(p=P, q=Q, u=None, v=None):
    """Yearly quantities of the chain: hazards h0, h1, the stay-held factor a, the unheld factor b
    and the yearly chance c of passing from held to unheld."""
    h0, h1 = p * u, p * v
    return dict(h0=h0, h1=h1, a=(1 - h1) * (1 - q), b=1 - h0, c=(1 - h1) * q)


def survival(t, r):
    """S.1. Shares still kept after t years, for capacities unheld and held at the start."""
    a, b, c = r["a"], r["b"], r["c"]
    s_u = b ** t
    s_h = a ** t + (c / (a - b)) * (a ** t - b ** t) if a != b else a ** t + c * t * a ** (t - 1)
    return s_u, s_h


def lifespan(r):
    """S.2. Expected number of years kept: the sum of S.1 over t >= 1."""
    a, b, c = r["a"], r["b"], r["c"]
    return b / (1 - b), a / (1 - a) + c / ((1 - a) * (1 - b))


def hazard_held(t, r):
    """S.3. Yearly hazard in year t of the capacities held at the start."""
    s0, s1 = survival(t, r)[1], survival(t + 1, r)[1]
    return 1 - s1 / s0


def half_life(r, which):
    """The year, as a real number, at which S.1 falls to one half."""
    f = (lambda t: survival(t, r)[0]) if which == "unheld" else (lambda t: survival(t, r)[1])
    lo, hi = 0.0, 1.0
    while f(hi) > 0.5:
        hi *= 2
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if f(mid) > 0.5 else (lo, mid)
    return (lo + hi) / 2


def calibrate(p=P, q=Q, year=TARGET_YEAR, unheld=TARGET_UNHELD, held=TARGET_HELD):
    """U from the unheld endpoint exactly; V by bisection on the held endpoint."""
    u = (1 - unheld ** (1 / year)) / p
    lo, hi = 0.0, u
    for _ in range(200):
        mid = (lo + hi) / 2
        s_h = survival(year, rates(p, q, u, mid))[1]
        lo, hi = (mid, hi) if s_h > held else (lo, mid)
    return u, (lo + hi) / 2


# ---------------------------------------------------------------- survivors' worth (S.4)
def _phi(z):
    return math.exp(-z * z / 2) / math.sqrt(2 * math.pi)


def _Phi(z):
    return 0.5 * (1 + math.erf(z / math.sqrt(2)))


def survivors_worth(rho, t, p=P, u=None, grid=4001, span=8.0):
    """S.4. Mean worth of unheld capacities still kept after t years (rule R4), and the Price
    form Cov(w, S(t|s)) / E[S(t|s)] + E[w], both by quadrature over the signal's normal score."""
    z = np.linspace(-span, span, grid)
    dz = z[1] - z[0]
    weight = np.array([_phi(x) for x in z]) * dz
    s = np.array([_Phi(x) for x in z])
    cond_w = np.array([_Phi(rho * x / math.sqrt(2 - rho * rho)) for x in z])   # E[w | s]
    surv = (1 - p * u * 2 * (1 - s)) ** t                                    # S(t | s)
    e_s, e_w = (weight * surv).sum(), (weight * cond_w).sum()
    direct = (weight * cond_w * surv).sum() / e_s
    price = e_w + ((weight * cond_w * surv).sum() - e_w * e_s) / e_s
    return direct, price, e_w


# ---------------------------------------------------------------- exact and simulated checks
def recursion_exact(t_max, p, q, u, v):
    """The chain stepped in exact rational arithmetic from held and from unheld."""
    p, q, u, v = (Fraction(x) for x in (p, q, u, v))
    h0, h1 = p * u, p * v
    out = []
    for start in ("held", "unheld"):
        held, unheld = (Fraction(1), Fraction(0)) if start == "held" else (Fraction(0), Fraction(1))
        series = [held + unheld]
        for _ in range(t_max):
            held, unheld = held * (1 - h1) * (1 - q), held * (1 - h1) * q + unheld * (1 - h0)
            series.append(held + unheld)
        out.append(series)
    return out[0], out[1]


def closed_exact(t, p, q, u, v):
    p, q, u, v = (Fraction(x) for x in (p, q, u, v))
    h0, h1 = p * u, p * v
    a, b, c = (1 - h1) * (1 - q), 1 - h0, (1 - h1) * q
    return a ** t + c / (a - b) * (a ** t - b ** t), b ** t


def one_city_run(p, q, u, v, years, draws, seed):
    """Rules R1 to R3 for one city, whose capacities all meet the same tight years: the shares
    kept along one run, from held and from unheld. The closed forms are the expectation over runs."""
    rng = np.random.default_rng(seed)
    result = {}
    for start in ("held", "unheld"):
        state = np.full(draws, 0 if start == "held" else 1)       # 0 held, 1 unheld, 2 cut
        kept = [1.0]
        for _ in range(years):
            tight = rng.random() < p                                # one year for all capacities
            if tight:
                cut_chance = np.where(state == 0, v, u)
                state = np.where((state < 2) & (rng.random(draws) < cut_chance), 2, state)
            leave = (state == 0) & (rng.random(draws) < q)
            state = np.where(leave, 1, state)
            kept.append(float((state < 2).mean()))
        result[start] = kept
    return result


def monte_carlo_independent_years(p, q, u, v, years, draws, seed):
    """As monte_carlo, but each capacity meets its own tight years, so draws are independent."""
    rng = np.random.default_rng(seed)
    result = {}
    for start in ("held", "unheld"):
        state = np.full(draws, 0 if start == "held" else 1)
        kept = [1.0]
        for _ in range(years):
            tight = rng.random(draws) < p
            cut_chance = np.where(state == 0, v, u)
            state = np.where((state < 2) & tight & (rng.random(draws) < cut_chance), 2, state)
            leave = (state == 0) & (rng.random(draws) < q)
            state = np.where(leave, 1, state)
            kept.append(float((state < 2).mean()))
        result[start] = kept
    return result


def worth_monte_carlo(rho, t, p, u, draws, seed):
    rng = np.random.default_rng(seed)
    z1 = rng.standard_normal(draws)
    z2 = rho * z1 + math.sqrt(1 - rho * rho) * rng.standard_normal(draws)
    w = np.array([_Phi(x) for x in z1])
    s = np.array([_Phi(x) for x in z2])
    alive = np.ones(draws, bool)
    for _ in range(t):
        tight = rng.random(draws) < p
        alive &= ~(tight & (rng.random(draws) < u * 2 * (1 - s)))
    return float(w[alive].mean()), float(w.mean())


def lump_classes(departure):
    """Kemeny-Snell lumpability. A richer generator keeps each holder's years served (capped at
    len(departure) - 1) and lets the chance of leaving depend on them. Starting from the
    partition the book reads (held, unheld, cut), split blocks until every state of a block
    sends the same total chance into every block. Returns the number of blocks left."""
    p, u, v = Fraction(P), Fraction(1, 7), Fraction(1, 41)
    k_max = len(departure) - 1
    states = [("H", k) for k in range(k_max + 1)] + [("U", 0), ("C", 0)]
    def step(x):
        kind, k = x
        if kind == "C":
            return {("C", 0): Fraction(1)}
        if kind == "U":
            return {("U", 0): 1 - p * u, ("C", 0): p * u}
        q_k = Fraction(departure[k])
        stay = (1 - p * v)
        return {("H", min(k + 1, k_max)): stay * (1 - q_k), ("U", 0): stay * q_k, ("C", 0): p * v}
    block_of = {x: x[0] for x in states}
    while True:
        def signature(x):
            totals = {}
            for y, pr in step(x).items():
                totals[block_of[y]] = totals.get(block_of[y], 0) + pr
            return (block_of[x], tuple(sorted(totals.items())))
        new = {x: signature(x) for x in states}
        if len(set(new.values())) == len(set(block_of.values())):
            return len(set(block_of.values()))
        block_of = new


# ---------------------------------------------------------------- run, check, write
def main():
    here = Path(__file__).parent
    u, v = calibrate()
    r = rates(P, Q, u, v)
    s_u30, s_h30 = survival(TARGET_YEAR, r)
    assert abs(s_u30 - TARGET_UNHELD) < 1e-12 and abs(s_h30 - TARGET_HELD) < 1e-12

    # S.1 against the recursion, exactly, for every t <= 100
    held_rec, unheld_rec = recursion_exact(100, P, Q, u, v)
    for t in range(101):
        h_cl, u_cl = closed_exact(t, P, Q, u, v)
        assert h_cl == held_rec[t] and u_cl == unheld_rec[t], t

    # S.1 against simulation, with each capacity meeting its own tight years
    sim = monte_carlo_independent_years(P, Q, u, v, HORIZON, DRAWS, SEED)
    gaps = {}
    for start, idx in (("held", 1), ("unheld", 0)):
        gap = max(abs(sim[start][t] - survival(t, r)[idx]) for t in range(HORIZON + 1))
        se = max(math.sqrt(survival(t, r)[idx] * (1 - survival(t, r)[idx]) / DRAWS)
                 for t in range(HORIZON + 1))
        assert gap < 5 * se, (start, gap, se)
        gaps[start] = gap

    # S.2, S.3, limits and the dimensionless form
    life_u, life_h = lifespan(r)
    assert abs(life_u - sum(survival(t, r)[0] for t in range(1, 3000))) < 1e-9
    assert abs(life_h - sum(survival(t, r)[1] for t in range(1, 3000))) < 1e-9
    limit = 1 - max(r["a"], r["b"])
    assert abs(hazard_held(2000, r) - limit) < 1e-9
    q0 = rates(P, 0.0, u, v)
    assert all(abs(survival(t, q0)[1] - (1 - q0["h1"]) ** t) < 1e-12 for t in range(60))
    same = rates(P, Q, u, u)
    assert all(abs(survival(t, same)[1] - survival(t, same)[0]) < 1e-12 for t in range(60))
    kappa, epsilon = Q / r["h0"], r["h1"] / r["h0"]

    # S.4: Price form equals the direct mean; independent signal leaves worth where it was
    worth = {}
    for rho in RHOS:
        direct, price, base = survivors_worth(rho, TARGET_YEAR, P, u)
        assert abs(direct - price) < 1e-12
        worth[f"{rho:.2f}"] = round(direct, 4)
    assert abs(worth["0.00"] - 0.5) < 1e-9
    mc_w, mc_base = worth_monte_carlo(0.5, TARGET_YEAR, P, u, DRAWS, SEED + 1)
    assert abs(mc_w - worth["0.50"]) < 0.01, (mc_w, worth["0.50"])

    # Lumping: memoryless departures lump to the three states; departures by years served do not
    memoryless = lump_classes([Fraction(1, 50)] * 4)
    by_tenure = lump_classes([Fraction(1, 10), Fraction(1, 20), Fraction(1, 40), Fraction(1, 80)])
    assert memoryless == 3 and by_tenure > 3

    numbers = {
        "rules": dict(P=P, Q=Q, target_year=TARGET_YEAR, target_unheld=TARGET_UNHELD,
                      target_held=TARGET_HELD, seed=SEED, draws=DRAWS),
        "calibrated": dict(U=round(u, 6), V=round(v, 6)),
        "hazard": dict(unheld=round(r["h0"], 6), held=round(r["h1"], 6)),
        "survival": {"unheld": [round(survival(t, r)[0], 6) for t in range(HORIZON + 1)],
                     "held": [round(survival(t, r)[1], 6) for t in range(HORIZON + 1)]},
        "half_life": dict(unheld=round(half_life(r, "unheld"), 2), held=round(half_life(r, "held"), 2)),
        "lifespan": dict(unheld=round(life_u, 2), held=round(life_h, 2), ratio=round(life_h / life_u, 2),
                         shortcut=round(1 / Q + 1 / r["h0"], 1)),
        "hazard_held_start": dict(start=round(hazard_held(0, r), 4), year_thirty=round(hazard_held(30, r), 4),
                                  limit=round(limit, 4)),
        "jump": round(u / v, 2),
        "dimensionless": dict(kappa=round(kappa, 3), epsilon=round(epsilon, 3),
                              ratio_continuous=round((1 + kappa) / (kappa + epsilon), 2)),
        "worth_after_thirty": worth,
        "lumping": dict(memoryless=memoryless, by_tenure=by_tenure),
        "checks": dict(exact_recursion_years=100, simulation_gap_held=round(gaps["held"], 4),
                       simulation_gap_unheld=round(gaps["unheld"], 4)),
    }
    (here / "sieve_chain.json").write_text(json.dumps(numbers, indent=2) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
