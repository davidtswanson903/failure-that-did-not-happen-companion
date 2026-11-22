"""Every pair of registers on five states, every rule built on them, and every refinement that carries what lies between them.

Everything here is exact. There is no draw and nothing to tune.

The rules
  R1. A register is a way of dividing the states into groups: it tells two states apart exactly when they fall in different groups.
  R2. An arrangement is an ordered pair of registers, one for each of two parties, over the same states.
  R3. What lies between them is the set of pairs of states neither tells apart.
  R4. A rule built on the two registers gives a yes or a no for each combination of their groups that some state has.
  R5. A refinement divides a party's groups further. Its cost is the pairs that party comes to tell apart, summed over the parties.
  R6. A refinement carries what lies between when nothing lies between the refined registers. The cheapest is the one of least cost.

Run it with `python compute_exact.py`. It writes exact.json, and exact as PDF and PNG, beside itself.
"""
import json
from collections import Counter
from itertools import combinations, product
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from figure_style import fonts, finish

STATES = 5  # how many states the two parties register

HERE = Path(__file__).resolve().parent
BLUE, RED, GREY, INK = "#2a78d6", "#e34948", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})


def registers(items):
    """R1: every way of dividing these states into groups."""
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for groups in registers(rest):
        yield [[first]] + groups
        for i in range(len(groups)):
            yield groups[:i] + [[first] + groups[i]] + groups[i + 1:]


def untold(register):
    """R1: the pairs of states a register leaves untold: those in one group."""
    return frozenset(pair for group in register for pair in combinations(sorted(group), 2))


def group_of(register, state):
    return next(i for i, group in enumerate(register) if state in group)


REGISTERS = list(registers(list(range(STATES))))
UNTOLD = [untold(register) for register in REGISTERS]
FINER = [[j for j, other in enumerate(UNTOLD) if other <= mine] for mine in UNTOLD]  # R5: each register's refinements

rules = 0
between_is_what_no_rule_separates = True
with_something_between = at_price = 0
points = Counter()  # (pairs carried, cheapest cost): how many arrangements
excess_is_what_the_other_told = True
remedy_never_cheaper = True

for a, b in product(range(len(REGISTERS)), repeat=2):  # R2
    between = UNTOLD[a] & UNTOLD[b]  # R3

    # R4: every rule on the combinations of groups that occur, and the pairs no rule separates
    combination = {s: (group_of(REGISTERS[a], s), group_of(REGISTERS[b], s)) for s in range(STATES)}
    occurring = sorted(set(combination.values()))
    never_separated = set(combinations(range(STATES), 2))
    for answers in product((False, True), repeat=len(occurring)):
        rules += 1
        rule = dict(zip(occurring, answers))
        never_separated = {(s, t) for s, t in never_separated if rule[combination[s]] == rule[combination[t]]}
    between_is_what_no_rule_separates &= never_separated == set(between)

    if not between:
        continue
    with_something_between += 1

    # R5, R6: the cheapest refinement that leaves nothing between
    cheapest, cheapest_excess = None, None
    for x, y in product(FINER[a], FINER[b]):
        if UNTOLD[x] & UNTOLD[y]:
            continue
        paid_a, paid_b = UNTOLD[a] - UNTOLD[x], UNTOLD[b] - UNTOLD[y]
        cost = len(paid_a) + len(paid_b)
        if cheapest is None or cost < cheapest:
            cheapest = cost
            cheapest_excess = len(paid_a - UNTOLD[b]) + len(paid_b - UNTOLD[a]) + len(paid_a & paid_b)
    carried = len(between)
    points[carried, cheapest] += 1
    at_price += cheapest == carried
    remedy_never_cheaper &= cheapest >= carried
    excess_is_what_the_other_told &= cheapest - carried == cheapest_excess

results = {
    "states": STATES, "registers": len(REGISTERS), "arrangements": len(REGISTERS) ** 2, "rules": rules,
    "between_is_what_no_rule_separates": between_is_what_no_rule_separates,
    "with_something_between": with_something_between, "exactly_at_price": at_price,
    "exactly_at_price_share": 100 * at_price / with_something_between,
    "remedy_never_cheaper": remedy_never_cheaper,
    "largest_excess": max(cost - carried for carried, cost in points),
    "excess_is_what_the_other_told": excess_is_what_the_other_told,
    "points": sorted([carried, cost, count] for (carried, cost), count in points.items()),
}
(HERE / "exact.json").write_text(json.dumps(results, indent=1, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

# The figure: the cheapest remedy against what it carries, with no arrangement below the line
fig, ax = plt.subplots(figsize=(6.27, 4.2))
top = max(carried for carried, _ in points) + 1
ax.plot([0, top], [0, top], color=GREY, linewidth=1, linestyle="--", zorder=1)
for (carried, cost), count in sorted(points.items()):
    colour = BLUE if cost == carried else RED
    size = 30 + 1.1 * count
    ax.scatter(carried, cost, s=size, color=colour, edgecolor="white", linewidth=1, zorder=2)
    reach = size**0.5 / 2 + 3  # the number sits just outside its dot: below and right on the line, above it off the line
    offset = (reach, -reach * 0.8) if cost == carried else (-reach * 0.6, reach * 0.8)
    ax.annotate(f"{count:,}", (carried, cost), textcoords="offset points", xytext=offset, ha="left" if cost == carried else "right",
                va="top" if cost == carried else "bottom")
ax.text(4.8, 3.2, f"On the line: {at_price:,} of the {with_something_between:,}\nwith something between cost\nexactly what they carry", va="top")
ax.text(0.3, 6.6, f"Above it: the rest cost more,\nby at most {results['largest_excess']} pairs", va="center")
ax.text(4.8, 1.0, "None lies below the line", va="top")
ax.set_xlabel("pairs that lie between: what the remedy carries")
ax.set_ylabel("pairs the cheapest remedy costs")
ax.set_xlim(0, top)
ax.set_ylim(0, top + 0.3)
finish(fig, HERE / "exact")

# The checks: all exact
assert results["registers"] == 52 and results["arrangements"] == 2704
assert results["rules"] == 58158
assert results["with_something_between"] == 1551 and results["exactly_at_price"] == 1171
assert results["largest_excess"] == 2
assert between_is_what_no_rule_separates, "the pairs no rule separates are exactly the pairs between"
assert remedy_never_cheaper, "no remedy costs fewer pairs than it carries"
assert excess_is_what_the_other_told, "what a remedy costs beyond what it carries is what the other party already told apart"
