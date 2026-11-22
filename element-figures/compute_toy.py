"""Registers as sets of kept facts, counted exactly on 8 and 16 states: the chain, the between and the price.

Everything here is exact. There is no draw and nothing to tune.

The rules
  R1. A state is one answer, yes or no, to each of a few facts, so n facts give 2^n states, and any two states make a pair.
  R2. A party registers a set of facts. It tells two states apart exactly when they differ in a fact it keeps.
  R3. What lies between parties is the set of pairs none of them tells apart.
  R4. When a party comes to keep another fact, the price is the set of pairs it comes to tell apart.
  R5. A description built from a description keeps only some of what the earlier one kept.

The two cases
  The bridge has three facts: crack, funding, corrosion. The inspection unit keeps the crack, the budget office the funding.
  Ultrasound adds corrosion to what the inspection unit keeps.
  The case records have four facts: opened, delayed, reversed, appealed. A summary keeps three, a report built from it two,
  a dashboard built from the report one, and a redesign of the dashboard the same one.

Run it with `python compute_toy.py`. It writes toy.json, and toy_chain, toy_between and toy_price as PDF and PNG, beside itself.
"""
import json
from itertools import combinations, product
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from figure_style import fonts, finish

HERE = Path(__file__).resolve().parent
BLUE, ORANGE, RED, GREY, INK = "#2a78d6", "#eb6834", "#e34948", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})


# The counts
def states(facts):
    """R1: every state of this many yes-or-no facts."""
    return list(product((0, 1), repeat=facts))


def all_pairs(facts):
    """R1: every pair of states."""
    return set(combinations(states(facts), 2))


def untold(facts, kept):
    """R2: the pairs a party keeping these facts leaves untold: those that agree on every fact it keeps."""
    return {(a, b) for a, b in all_pairs(facts) if all(a[i] == b[i] for i in kept)}


CRACK, FUNDING, CORROSION = 0, 1, 2
inspection, budget, ultrasound = untold(3, [CRACK]), untold(3, [FUNDING]), untold(3, [CRACK, CORROSION])
between_before = inspection & budget  # R3
between_after = ultrasound & budget
price = inspection - ultrasound  # R4
told_elsewhere = price - budget

CHAIN = ("record", "summary", "report", "dashboard", "redesign")
chain = [untold(4, kept) for kept in ((0, 1, 2, 3), (0, 1, 2), (0, 1), (0,), (0,))]  # R5

results = {
    "bridge_states": len(states(3)), "bridge_pairs": len(all_pairs(3)),
    "inspection_untold": len(inspection), "budget_untold": len(budget),
    "bridge_between": len(between_before), "refined_between": len(between_after),
    "refinement_price": len(price), "price_told_elsewhere": len(told_elsewhere),
    "balance_holds": (between_before - between_after) <= price and len(between_before - between_after) <= len(price),
    "records_states": len(states(4)), "records_pairs": len(all_pairs(4)),
    "summary_untold": len(chain[1]), "report_untold": len(chain[2]), "dashboard_untold": len(chain[3]), "redesign_untold": len(chain[4]),
    "chain_never_recovers": all(a <= b for a, b in zip(chain, chain[1:])),
    "chain_settles": chain[3] == chain[4],
}
(HERE / "toy.json").write_text(json.dumps(results, indent=1, sort_keys=True) + "\n", encoding="utf-8", newline="\n")


# The figures
def save(fig, name):
    finish(fig, HERE / name)


# Descriptions of descriptions: the pairs left untold climb the steps of the chain and never come back
fig, ax = plt.subplots(figsize=(6.27, 3.4))
counts = [len(step) for step in chain]
ax.axhline(len(all_pairs(4)), color=GREY, linewidth=1, linestyle="--")
ax.text(0, len(all_pairs(4)) - 3, f"all {len(all_pairs(4))} pairs of the 16 states", color=GREY, va="top")
ax.plot(range(5), counts, color=BLUE, linewidth=2, marker="o", markersize=8, drawstyle="steps-post")
ax.plot(range(5), counts, color=BLUE, linestyle="none", marker="o", markersize=8)
for x, count in enumerate(counts):
    ax.annotate(str(count), (x, count), textcoords="offset points", xytext=(0, 9), ha="center", fontweight="bold")
ax.text(0, 72, "Each step can drop more,\nand no step gets a pair back", va="top")
ax.set_xticks(range(5), [name.capitalize() for name in CHAIN])
ax.set_ylabel("pairs left untold apart")
ax.set_ylim(0, len(all_pairs(4)) * 1.08)
ax.set_xlim(-0.4, 4.4)
save(fig, "toy_chain")

def place(state):
    """Where a state is drawn: its cell by crack and funding, its side of the cell by corrosion. The tilt keeps any line from passing through a third state."""
    return 2 * state[CRACK] + (0.45 if state[CORROSION] else -0.45), 2 * state[FUNDING] + (0.14 if state[CORROSION] else -0.14)


def bridge_states(ax, lines):
    """The eight states in their four cells, and every one of the 28 pairs as a line: `lines` gives the pairs to pick out, as {color: (pairs, style)}, and the rest are thin and grey."""
    for crack, funded in product((0, 1), repeat=2):
        ax.add_patch(plt.Rectangle((2 * crack - 0.9, 2 * funded - 0.8), 1.8, 1.6, fill=False, edgecolor=GREY))
    picked = set().union(*(pairs for pairs, _ in lines.values()))
    for a, b in all_pairs(3) - picked:
        ax.plot(*zip(place(a), place(b)), color=GREY, linewidth=0.5, alpha=0.65, zorder=1)
    for color, (pairs, style) in lines.items():
        for a, b in pairs:
            ax.plot(*zip(place(a), place(b)), color=color, linewidth=2.2, linestyle=style, zorder=2)
    for state in states(3):
        x, y = place(state)
        ax.plot(x, y, marker="s" if state[CORROSION] else "o", color=INK if state[CORROSION] else BLUE, markersize=9, zorder=3)
        up = state[FUNDING] == 1  # on the side of the state away from the other row, where fewest lines run
        ax.text(x, y + (0.18 if up else -0.18), "corroded" if state[CORROSION] else "sound", ha="center", va="bottom" if up else "top", zorder=4,
                bbox={"facecolor": "white", "edgecolor": "none", "pad": 0.8})
    ax.set_xticks([0, 2], ["no crack", "crack"])
    ax.set_yticks([0, 2], ["not funded", "funded"])
    ax.set_xlabel("crack: what the inspection unit registers")
    ax.set_ylabel("funding: what the budget office registers")
    ax.set_xlim(-1.1, 3.1)
    ax.set_ylim(-1, 3.8)
    ax.tick_params(length=0)


# Two registers, and what lies between them: all eight states and all 28 pairs, the pairs neither office tells apart picked out, one in each cell
fig, ax = plt.subplots(figsize=(6.27, 4.4))
bridge_states(ax, {RED: (between_before, "-")})
ax.text(1, 3.0, f"Red: the {len(between_before)} pairs neither office tells apart, which lie between them\n"
                f"Grey: the other {len(all_pairs(3) - between_before)}, which at least one office tells apart", ha="center", va="bottom")
save(fig, "toy_between")

# Refinement, and its price: the same states and pairs; what the inspection unit newly tells apart is what lay between and as much again
fig, ax = plt.subplots(figsize=(6.27, 4.4))
bridge_states(ax, {RED: (price - told_elsewhere, "-"), ORANGE: (told_elsewhere, (0, (3, 1.5)))})
ax.text(1, 3.0, f"With ultrasound the inspection unit newly tells apart {len(price)} pairs, and {len(between_after)} now lie between:\n"
                f"Red: the {len(price - told_elsewhere)} that lay between\n"
                f"Dashed orange: {len(told_elsewhere)} the budget office already told apart", ha="center", va="bottom")
save(fig, "toy_price")


# The checks: all exact
assert results["bridge_states"] == 8 and results["bridge_pairs"] == 28
assert results["inspection_untold"] == results["budget_untold"] == 12
assert results["bridge_between"] == 4 and results["refined_between"] == 0
assert results["refinement_price"] == 8 and results["price_told_elsewhere"] == 4
assert results["records_states"] == 16 and results["records_pairs"] == 120
assert [len(step) for step in chain[1:]] == [8, 24, 56, 56]
assert results["balance_holds"], "what lies between shrinks by no more than the price"
assert results["chain_never_recovers"], "no step of the chain gets a pair back"
assert results["chain_settles"], "the redesign changes nothing the dashboard keeps"
assert price - told_elsewhere == between_before, "the pairs picked out in red are the same in both drawings"
assert not any(abs((place(b)[0] - place(a)[0]) * (place(c)[1] - place(a)[1]) - (place(b)[1] - place(a)[1]) * (place(c)[0] - place(a)[0])) < 1e-9
               for a, b in all_pairs(3) for c in states(3) if c not in (a, b)), "no state lies on the line of a pair it is not in, so each of the 28 shows"
