"""Kept facts lapse at no cost, and facts are added only when paid for: what lies between parties grows unless something pays against it,
and shrinks by no more than is paid.

The rules
  R1. FACTS yes-or-no facts give 2^FACTS states. A party keeps some facts, and tells two states apart exactly when they differ in one.
  R2. What lies between parties is the set of pairs none of them tells apart.
  R3. The parties begin keeping the facts in START, which between them leave one fact unkept.
  R4. Each year each fact a party keeps lapses with chance LAPSE, at no cost.
  R5. A party comes to keep a new fact only when a fund covers its price, the pairs it comes to tell apart. Each year a budget, counted in
      pairs, goes into the fund, and what is not spent stays there.
  R6. Each year the fund is offered one fact no party keeps, at the party that keeps most, for whom it is cheapest.
  R7. Within a year, lapses come first and the refinement follows.
  R8. Random changes: CHANGES times, three parties are drawn, each keeping each fact with chance KEEP, and one party's keeping of one fact
      is turned over. Every pair that left what lies between must be in the price, and every pair that joined it in what was let go.

Run it with `python compute_drift.py`. It writes drift.json, and drift as PDF and PNG, beside itself. To change a number, edit the block
below and run it again.
"""
import json
from itertools import combinations
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from figure_style import fonts, finish
import numpy as np

# Parameters: every number the model uses
SEED = 1
FACTS = 6  # how many yes-or-no facts
PARTIES = 3  # how many parties
START = ((0, 1, 2), (2, 3), (3, 4))  # which facts each party keeps at the start
LAPSE = 0.05  # the chance a year that a fact a party keeps lapses
BUDGETS = (0, 20, 60)  # the budgets compared, in pairs a year
YEARS = 50  # how long each run lasts
RUNS = 300  # how many runs for each budget
CHANGES = 3000  # how many random changes
KEEP = 0.35  # in the random changes, the chance a party keeps a fact

parameters = {name.lower(): value for name, value in globals().items() if name.isupper()}
HERE = Path(__file__).resolve().parent
BLUE, ORANGE, RED, GREY, INK = "#2a78d6", "#eb6834", "#e34948", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})
rng = np.random.default_rng(SEED)

# R1, R2: a party's facts are the bits of a number. Two states differ in the bits of their exclusive or
STATES = 2**FACTS
PAIRS = np.array(list(combinations(range(STATES), 2)))
DIFFER = PAIRS[:, 0] ^ PAIRS[:, 1]
EVERY_PAIR = len(PAIRS)


def bits(facts):
    return sum(1 << fact for fact in facts)


def untold(kept):
    """R1: the pairs a party keeping these facts leaves untold."""
    return (DIFFER & kept) == 0


def between(kept_by_each):
    """R2: the pairs no party tells apart."""
    found = np.ones(EVERY_PAIR, dtype=bool)
    for kept in kept_by_each:
        found &= untold(kept)
    return found


BETWEEN_GIVEN_UNION = [int(untold(union).sum()) for union in range(STATES)]
start = [bits(facts) for facts in START]
start_between = int(between(start).sum())


def price(kept):
    """R5: the pairs a party keeping these facts comes to tell apart by keeping one more. It is the same for every fact it does not keep."""
    return 2 ** (2 * FACTS - 2 - bin(kept).count("1"))


def drift(budget):
    """R3 to R7: what lies between, at the end of each year, for each run."""
    out = np.empty((RUNS, YEARS + 1))
    for run in range(RUNS):
        kept, fund = list(start), 0.0
        out[run, 0] = start_between
        for year in range(1, YEARS + 1):
            for party in range(PARTIES):  # R4
                for fact in range(FACTS):
                    if kept[party] >> fact & 1 and rng.random() < LAPSE:
                        kept[party] ^= 1 << fact
            fund += budget  # R5
            union = kept[0] | kept[1] | kept[2]
            unkept = [fact for fact in range(FACTS) if not union >> fact & 1]
            if unkept:  # R6
                buyer = int(np.argmax([bin(k).count("1") for k in kept]))
                if fund >= price(kept[buyer]):
                    fund -= price(kept[buyer])
                    kept[buyer] |= 1 << int(rng.choice(unkept))
            out[run, year] = BETWEEN_GIVEN_UNION[kept[0] | kept[1] | kept[2]]
    return out


runs = {budget: drift(budget) for budget in BUDGETS}

# R8: both inclusions of balance on every random change, and how much of what refinements paid another party already told apart
balance_on_every_change = True
refinements = paid_total = already_total = 0
points = []
for _ in range(CHANGES):
    kept = (rng.random((PARTIES, FACTS)) < KEEP).astype(int).dot(1 << np.arange(FACTS))
    party, fact = int(rng.integers(PARTIES)), int(rng.integers(FACTS))
    before = between(kept)
    old = int(kept[party])
    kept[party] = old ^ (1 << fact)
    after = between(kept)
    paid = untold(old) & ~untold(int(kept[party]))
    released = untold(int(kept[party])) & ~untold(old)
    balance_on_every_change &= not (before & ~after & ~paid).any() and not (after & ~before & ~released).any()
    if paid.any():
        refinements += 1
        paid_total += int(paid.sum())
        already_total += int((paid & ~before).sum())
        points.append((int(paid.sum()), int((before & ~after).sum())))

results = {
    "states": STATES, "pairs": EVERY_PAIR, "start_between": start_between, "kept_facts": bin(start[0] | start[1] | start[2]).count("1"),
    "between_after_0": runs[0][:, -1].mean(), "between_after_20": runs[20][:, -1].mean(), "between_after_60": runs[60][:, -1].mean(),
    "refinements": refinements, "already_made": 100 * already_total / paid_total,
    "budget_low": BUDGETS[1], "budget_high": BUDGETS[2],
}
curves = {str(budget): runs[budget].mean(axis=0).tolist() for budget in BUDGETS}
shapes = {
    "unpaid_never_shrinks": not (np.diff(runs[0], axis=1) < 0).any(),
    "grows_when_nothing_is_paid": results["between_after_0"] > start_between,
    "more_paid_less_between": results["between_after_0"] > results["between_after_20"] > results["between_after_60"],
    "balance_on_every_change": balance_on_every_change,
    "shrinks_by_no_more_than_the_price": all(shrank <= paid for paid, shrank in points),
}
output = {**parameters, **results, **shapes, "curves": curves}
(HERE / "drift.json").write_text(json.dumps(output, indent=1, sort_keys=True, default=lambda number: number.item()) + "\n", encoding="utf-8", newline="\n")

# The figure: on the left, what lies between by what is paid; on the right, no refinement shrinks it by more than its price
fig, (left, right) = plt.subplots(1, 2, figsize=(6.27, 3.4))
years = np.arange(YEARS + 1)
for budget, colour, words in ((0, RED, "nothing paid"), (20, ORANGE, "20 pairs a year"), (60, BLUE, "60 pairs a year")):
    left.plot(years, curves[str(budget)], color=colour, linewidth=2)
    left.text(YEARS + 1, max(curves[str(budget)][-1], 120), f"{words}:\n{curves[str(budget)][-1]:,.0f}", va="center")
left.set_xlabel("year")
left.set_ylabel("pairs between the parties")
left.set_xlim(0, YEARS + 26)  # room for the labels at the lines' ends
left.spines["bottom"].set_bounds(0, YEARS)
left.set_xticks([0, 10, 20, 30, 40, 50])
left.set_ylim(0, EVERY_PAIR)
counts = {}
for paid, shrank in points:
    counts[paid, shrank] = counts.get((paid, shrank), 0) + 1
top = max(paid for paid, _ in points)
low = min(paid for paid, _ in points)
right.plot([low, top], [low, top], color=GREY, linewidth=1, linestyle="--")
right.text(top * 0.6, top * 1.15, "shrinks by the whole price", color=GREY, ha="right")
right.scatter([paid for paid, _ in counts], [max(shrank, 1) for _, shrank in counts], s=[12 + count**0.75 * 3 for count in counts.values()],
              color=BLUE, edgecolor="white", linewidth=0.8, zorder=2)
right.text(top * 1.1, 4, "no refinement lies above the line", ha="right")
right.set_xscale("log", base=2)
right.set_yscale("log", base=2)
right.set_xticks([32, 64, 128, 256, 512, 1024], ["32", "64", "128", "256", "512", "1,024"])
right.set_yticks([1, 32, 64, 128, 256, 512, 1024], ["0", "32", "64", "128", "256", "512", "1,024"])
right.minorticks_off()
right.set_xlabel("what a refinement paid, in pairs")
right.set_ylabel("pairs that left what lies between")
finish(fig, HERE / "drift")

# The checks: exact facts, then the shape the figure's caption states
assert (STATES, EVERY_PAIR) == (2**FACTS, STATES * (STATES - 1) // 2)
for kept in range(STATES):  # R5: the price counted one by one is the formula
    for fact in range(FACTS):
        if not kept >> fact & 1:
            assert int((untold(kept) & ~untold(kept | 1 << fact)).sum()) == price(kept)
for name, holds in shapes.items():
    assert holds, name
