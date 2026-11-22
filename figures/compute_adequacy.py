"""Adequacy for a purpose: the share of the states that occur at which a register's reading
settles what an arrangement is for, its seven properties, and its course over time.

The rules (the exact statement; the companion's entry Model A proves what this checks)
  R1. A world is a finite set of states S. The states that occur are a subset X of S, each with a
      weight (one each unless stated). A register is a map c on S, and two states it maps alike are
      ones it cannot tell apart. A purpose is a map q on S: what an arrangement is for.
  R2. The class of x is the set of states of X that c cannot tell from x.
  R3. The adequacy region R(c, q; X) is the set of states of X whose class q takes one value across.
  R4. Adequacy alpha(c, q; X) is the weight of R over the weight of X, a number from 0 to 1.
  R5. A confusion is a pair of states of X that c cannot tell apart and q can.
  R6. An arrangement's register is its parties' registers read together, the joint register.
  R7. (Over time; presentation, chosen for curves that can be read.) While a correction that keeps
      the register adequate is kept, adequacy stays at 1. In each year after it is cut, the world
      moves and adequacy is multiplied by D = 1 - M. The correction is a capacity like any other:
      held, unheld or cut as in compute_sieve_chain.py, with its reference rates.

Checks, all by assertion: properties A1 to A7 on INSTANCES random instances on up to six states;
the price of adequacy (A.7) against every refinement of the register; the book's bridge;
age and corrosion on a narrow and a wide world; the closed forms of R7 against their sums and
against a Monte Carlo run with a fixed seed.  The functions
are importable; the notebook in ../notebook uses them.

Run it with `python compute_adequacy.py`. It writes adequacy.json beside itself.
"""
import itertools
import json
import math
import random
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
import compute_sieve_chain as sieve  # noqa: E402

M = 0.02
YEARS = 40
INSTANCES = 4000
SEED = 11
DRAWS = 200_000


# ---------------------------------------------------------------- the definitions, R2 to R6
def classes(c, X):
    out = {}
    for x in X:
        out.setdefault(c(x), []).append(x)
    return out


def region(c, q, X):
    """R3. The states of X whose class settles the purpose."""
    R = set()
    for members in classes(c, X).values():
        if len({q(x) for x in members}) == 1:
            R.update(members)
    return R


def adequacy(c, q, X, weight=None):
    """R4. The weight of the region over the weight of X."""
    w = weight or (lambda x: 1)
    total = sum(w(x) for x in X)
    return sum(w(x) for x in region(c, q, X)) / total if total else 1.0


def confusions(c, q, X):
    """R5. Pairs of X the register cannot tell apart and the purpose can."""
    X = list(X)
    return [(x, y) for x, y in itertools.combinations(X, 2) if c(x) == c(y) and q(x) != q(y)]


def joint(*registers):
    """R6. Registers read together."""
    return lambda x: tuple(r(x) for r in registers)


def between(registers, X):
    """Pairs of X that no register in the arrangement tells apart."""
    j = joint(*registers)
    return [(x, y) for x, y in itertools.combinations(list(X), 2) if j(x) == j(y)]


def price(c, finer, pairs_of):
    """Pairs among pairs_of that the finer register tells apart and c did not."""
    return sum(1 for x, y in pairs_of if c(x) == c(y) and finer(x) != finer(y))


# ---------------------------------------------------------------- over time (R7)
def expected_adequacy(t, m=M, start="held", r=None):
    """Closed forms: E0 with no correction, EU for a correction unheld at the start, EH held."""
    d = 1 - m
    if start == "none":
        return d ** t
    a, b, c = r["a"], r["b"], r["c"]
    s_u, s_h = sieve.survival(t, r)
    if start == "unheld":
        return s_u + (1 - b) * d / (d - b) * (d ** t - b ** t)
    k = c / (a - b)
    return (s_h + (1 + k) * (1 - a) * d / (d - a) * (d ** t - a ** t)
            - k * (1 - b) * d / (d - b) * (d ** t - b ** t))


def expected_adequacy_sum(t, m, start, r):
    """The defining sum: survival, plus decay after each year the correction could be cut."""
    d = 1 - m
    S = lambda s: sieve.survival(s, r)[0 if start == "unheld" else 1]
    return S(t) + sum((S(s - 1) - S(s)) * d ** (t - s + 1) for s in range(1, t + 1))


def adequacy_monte_carlo(m, years, r, draws, seed):
    """Correction cut by the chain's yearly chances; adequacy multiplied by 1 - m each year after."""
    rng = np.random.default_rng(seed)
    out = {}
    for start in ("held", "unheld"):
        state = np.full(draws, 0 if start == "held" else 1)
        lapsed_for = np.zeros(draws)
        for _ in range(years):
            cut_chance = np.where(state == 0, r["h1"], r["h0"])
            state = np.where((state < 2) & (rng.random(draws) < cut_chance), 2, state)
            state = np.where((state == 0) & (rng.random(draws) < r["c"] / (1 - r["h1"])), 1, state)
            lapsed_for = np.where(state == 2, lapsed_for + 1, lapsed_for)
        out[start] = float(((1 - m) ** lapsed_for).mean())
    return out


# ---------------------------------------------------------------- random instances
def random_instance(rng):
    n = rng.randint(2, 6)
    S = list(range(n))
    X = [s for s in S if rng.random() < 0.8] or [0]
    labels = lambda k: {s: rng.randrange(k) for s in S}
    c_map, q_map, c2_map = labels(rng.randint(1, n)), labels(rng.randint(1, 3)), labels(rng.randint(1, n))
    return S, X, c_map.__getitem__, q_map.__getitem__, c2_map.__getitem__


def partitions(items):
    """Every partition of a list, as a dict from item to block number."""
    if not items:
        yield {}
        return
    first, rest = items[0], items[1:]
    for p in partitions(rest):
        blocks = sorted(set(p.values()))
        for b in blocks:
            yield {**p, first: b}
        yield {**p, first: (max(blocks) + 1 if blocks else 0)}


def check_properties(instances, seed):
    rng = random.Random(seed)
    counts = dict.fromkeys(["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A6_share_can_rise"], 0)
    for _ in range(instances):
        S, X, c, q, c2 = random_instance(rng)
        R = region(c, q, X)
        # A1: adequate exactly when c carries q across X
        carries = all(q(x) == q(y) for x in X for y in X if c(x) == c(y))
        assert (adequacy(c, q, X) == 1) == carries
        counts["A1"] += 1
        # A2: a coarser purpose has a region at least as large
        coarse = lambda x: q(x) % 2
        assert R <= region(c, coarse, X)
        counts["A2"] += 1
        # A3: a state adequate across X stays adequate across any smaller set holding it
        Y = [x for x in X if rng.random() < 0.6]
        assert {x for x in R if x in Y} <= region(c, q, Y)
        counts["A3"] += 1
        # A4: a description built from c has a region inside c's
        built = lambda x: c(x) % 2
        assert region(built, q, X) <= R and adequacy(built, q, X) <= adequacy(c, q, X)
        counts["A4"] += 1
        # A5: the joint register's region holds every party's; outside it, a between pair q separates
        J = joint(c, c2)
        RJ = region(J, q, X)
        assert R <= RJ and region(c2, q, X) <= RJ
        btw = between([c, c2], X)
        for x in X:
            outside = x not in RJ
            witnessed = any(x in pair and q(pair[0]) != q(pair[1]) for pair in btw)
            assert outside == witnessed
        counts["A5"] += 1
        # A6: with c fixed, more states can only take states of X out of the region
        X_wide = sorted(set(X) | {s for s in S if rng.random() < 0.5})
        assert region(c, q, X_wide) & set(X) <= R
        if adequacy(c, q, X_wide) > adequacy(c, q, X):
            counts["A6_share_can_rise"] += 1
        counts["A6"] += 1
        # A7: the cheapest refinement adequate on X costs exactly the confusions within X
        pairs_X = list(itertools.combinations(X, 2))
        need = len(confusions(c, q, X))
        best = None
        for part in partitions(list(S)):
            finer = lambda x, part=part: (c(x), part[x])
            if adequacy(finer, q, X) == 1:
                cost = price(c, finer, pairs_X)
                best = cost if best is None else min(best, cost)
        reads_q = lambda x: (c(x), q(x))
        assert best == need == price(c, reads_q, pairs_X)
        counts["A7"] += 1
    return counts


# ---------------------------------------------------------------- the bridge and the cables
def bridge():
    """The book's bridge: crack, funding, corrosion. The purpose: sound, no crack and no corrosion."""
    S = list(itertools.product((0, 1), repeat=3))
    sound = lambda x: int(x[0] == 0 and x[2] == 0)
    registers = {
        "inspection": lambda x: x[0],
        "budget": lambda x: x[1],
        "both_offices": lambda x: (x[0], x[1]),
        "ultrasound": lambda x: (x[0], x[2]),
    }
    table = {name: dict(adequacy=adequacy(c, sound, S), region=len(region(c, sound, S)),
                        confusions=len(confusions(c, sound, S)))
             for name, c in registers.items()}
    all_pairs = list(itertools.combinations(S, 2))
    inspection = registers["inspection"]
    paid_ultrasound = price(inspection, registers["ultrasound"], all_pairs)
    paid_adequacy = price(inspection, lambda x: (x[0], sound(x)), all_pairs)
    return S, sound, registers, table, paid_ultrasound, paid_adequacy


def cables():
    """Age and corrosion. Narrow world: new cables sound, old ones corroded. Wide: all four."""
    age, corroded = (lambda x: x[0]), (lambda x: x[1])
    narrow = [(0, 0), (1, 1)]
    wide = list(itertools.product((0, 1), repeat=2))
    return adequacy(age, corroded, narrow), adequacy(age, corroded, wide)


# ---------------------------------------------------------------- run, check, write
def main():
    here = Path(__file__).parent
    counts = check_properties(INSTANCES, SEED)
    assert all(counts[k] == INSTANCES for k in ["A1", "A2", "A3", "A4", "A5", "A6", "A7"])

    S, sound, registers, table, paid_ultrasound, paid_adequacy = bridge()
    assert [table[k]["region"] for k in ("inspection", "budget", "both_offices", "ultrasound")] == [4, 0, 4, 8]
    assert paid_ultrasound == 8 and paid_adequacy == 4 == table["inspection"]["confusions"]

    narrow, wide = cables()
    assert narrow == 1.0 and wide == 0.0

    u, v = sieve.calibrate()
    r = sieve.rates(sieve.P, sieve.Q, u, v)
    for start in ("unheld", "held"):
        for t in range(61):
            assert abs(expected_adequacy(t, M, start, r) - expected_adequacy_sum(t, M, start, r)) < 1e-12
    year = {start: expected_adequacy(YEARS, M, start, r) for start in ("none", "unheld", "held")}
    mc = adequacy_monte_carlo(M, YEARS, r, DRAWS, SEED)
    for start in ("unheld", "held"):
        assert abs(mc[start] - year[start]) < 0.005, (start, mc[start], year[start])

    numbers = {
        "rules": dict(M=M, years=YEARS, instances=INSTANCES, seed=SEED, draws=DRAWS),
        "bridge": {k: dict(adequacy=round(v_["adequacy"], 4), region=v_["region"],
                           confusions=v_["confusions"]) for k, v_ in table.items()},
        "price": dict(ultrasound=paid_ultrasound, adequacy=paid_adequacy),
        "cables": dict(narrow=narrow, wide=wide),
        "properties": {k: counts[k] for k in ["A1", "A2", "A3", "A4", "A5", "A6", "A7"]},
        "share_rose_when_world_widened": counts["A6_share_can_rise"],
        "year_forty": {k: round(v_, 4) for k, v_ in year.items()},
        "year_forty_simulated": {k: round(v_, 4) for k, v_ in mc.items()},
        "curves": {start: [round(expected_adequacy(t, M, start, r), 6) for t in range(YEARS + 1)]
                   for start in ("none", "unheld", "held")},
    }
    (here / "adequacy.json").write_text(json.dumps(numbers, indent=2) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
