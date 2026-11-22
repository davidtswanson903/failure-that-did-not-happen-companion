"""Capacities are cut in tight years unless someone holds their lapse: what lasts follows being held, and follows worth only through what
the budget office registers.

The rules
  R1. A city keeps CAPACITIES capacities, each with a worth drawn at random from 0 to 1. HELD_SHARE of them begin with a holder.
  R2. Each year a holder moves on with chance MOVE_ON. Its capacity is then held by no one, and nothing gives it a new holder.
  R3. A year is tight with chance TIGHT_IN_TEN in ten.
  R4. In a tight year, a held capacity is cut with chance CUT_HELD. An unheld one is cut with a chance that depends only on what the
      budget office registers about it, r, from 0 to 1: CUT_AT_NOTHING where r is 0, falling evenly to CUT_AT_MOST where r is 1.
  R5. What is registered is r = c x worth + (1 - c) x an independent draw, where c is how closely it moves with worth. In the first run c
      is 0, so it has nothing to do with worth. The run is repeated for each c in CLOSENESS.
  R6. A capacity cut stays cut. Within a year, holders move on first and cuts follow.
  R7. The exact pair: where what is registered moves with worth exactly (c = 1), one capacity held by no one, worth PAIR_WORTHS[0], and one
      held, worth PAIR_WORTHS[1]. Their chances are computed year by year, with no draw, and the unheld one is cut first.

Run it with `python compute_sieve.py`. It writes sieve.json, and sieve as PDF and PNG, beside itself. To change a number, edit the block
below and run it again.
"""
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from figure_style import fonts, finish
import numpy as np

# Parameters: every number the model uses
SEED = 1
CAPACITIES = 2000  # how many capacities
YEARS = 30  # how long each run lasts
RUNS = 200  # how many runs
HELD_SHARE = 0.30  # the share that begin with a holder
MOVE_ON = 0.02  # the chance a year that a holder moves on
TIGHT_IN_TEN = 4  # how many years in ten are tight
CUT_HELD = 0.02  # the chance in a tight year that a held capacity is cut
CUT_AT_NOTHING = 0.30  # the chance in a tight year that an unheld capacity registered as worth nothing is cut
CUT_AT_MOST = 0.05  # the same, for one registered as worth the most
CLOSENESS = (0.0, 0.25, 0.5, 0.75, 1.0)  # how closely what is registered moves with worth, in each sweep
PAIR_WORTHS = (0.9, 0.1)  # the exact pair: the unheld capacity's worth, and the held one's

parameters = {name.lower(): value for name, value in globals().items() if name.isupper()}
HERE = Path(__file__).resolve().parent
BLUE, ORANGE, GREY, INK = "#2a78d6", "#eb6834", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})
rng = np.random.default_rng(SEED)


def cut_chance(registered):
    """R4: the chance an unheld capacity is cut in a tight year, from what is registered about it."""
    return CUT_AT_NOTHING + (CUT_AT_MOST - CUT_AT_NOTHING) * registered


def correlation(a, b):
    """How closely two quantities move together across the capacities, run by run, averaged over the runs. A run with no tight year cuts
    nothing, so nothing moves with anything, and it counts as none."""
    a, b = a - a.mean(axis=1, keepdims=True), b - b.mean(axis=1, keepdims=True)
    scale = np.sqrt((a * a).sum(axis=1) * (b * b).sum(axis=1))
    return float(((a * b).sum(axis=1) / np.where(scale > 0, scale, np.inf)).mean())


def run(closeness):
    """R1 to R6, RUNS times over."""
    shape = (RUNS, CAPACITIES)
    worth = rng.random(shape)  # R1
    held_at_start = rng.random(shape).argsort(axis=1) < round(HELD_SHARE * CAPACITIES)
    registered = closeness * worth + (1 - closeness) * rng.random(shape)  # R5
    unheld_chance = cut_chance(registered)
    held, alive = held_at_start.copy(), np.ones(shape, dtype=bool)
    curves = {"held": [], "others": []}
    for year in range(YEARS):
        held &= rng.random(shape) >= MOVE_ON  # R2
        tight = rng.random((RUNS, 1)) < TIGHT_IN_TEN / 10  # R3
        alive &= ~(tight & (rng.random(shape) < np.where(held, CUT_HELD, unheld_chance)))  # R4, R6
        curves["held"].append(100 * alive[held_at_start].mean())
        curves["others"].append(100 * alive[~held_at_start].mean())
    return {"curves": curves, "survivors_worth": float(((worth * alive).sum(axis=1) / alive.sum(axis=1)).mean()),
            "starting_worth": float(worth.mean()),
            "follows_holding": correlation(alive.astype(float), held_at_start.astype(float)),
            "follows_worth": correlation(alive.astype(float), worth)}


sweep = [run(closeness) for closeness in CLOSENESS]
first, last = sweep[0], sweep[-1]


def pair_race():
    """R7: the chance over the years that the unheld capacity of the pair is cut before the held one, and the other way, with no draw."""
    unheld, tight = float(cut_chance(PAIR_WORTHS[0])), TIGHT_IN_TEN / 10
    other_chance = {"held": CUT_HELD, "moved": float(cut_chance(PAIR_WORTHS[1]))}
    mass = {"held": 1.0, "moved": 0.0}
    unheld_first = held_first = 0.0
    for year in range(YEARS):
        mass = {"held": mass["held"] * (1 - MOVE_ON), "moved": mass["moved"] + mass["held"] * MOVE_ON}
        for status, chance in other_chance.items():
            unheld_first += mass[status] * tight * unheld * (1 - chance)
            held_first += mass[status] * tight * (1 - unheld) * chance
            mass[status] *= 1 - tight * (1 - (1 - unheld) * (1 - chance))
    return unheld_first, held_first


unheld_first, held_first = pair_race()
results = {
    "held_remaining": first["curves"]["held"][-1], "unheld_remaining": first["curves"]["others"][-1],
    "survivors_worth": first["survivors_worth"], "starting_worth": first["starting_worth"],
    "pair_unheld_first": unheld_first, "pair_held_first": held_first,
}
shapes = {
    "held_outlast_the_others": results["held_remaining"] > results["unheld_remaining"],
    "worth_has_no_part_when_unregistered": abs(first["follows_worth"]) < 0.02,
    "worth_counts_as_registered_moves_with_it": all(a["follows_worth"] < b["follows_worth"] for a, b in zip(sweep, sweep[1:])),
    "holding_followed_more_than_worth_at_exact": last["follows_holding"] > last["follows_worth"],
    "pair_unheld_cut_first": cut_chance(PAIR_WORTHS[0]) > CUT_HELD and unheld_first > held_first,
}
output = {**parameters, **results, **shapes, "curves": first["curves"],
          "follows_holding": [point["follows_holding"] for point in sweep], "follows_worth": [point["follows_worth"] for point in sweep]}
(HERE / "sieve.json").write_text(json.dumps(output, indent=1, sort_keys=True, default=lambda number: number.item()) + "\n", encoding="utf-8", newline="\n")

# The figure: on the left, what is held outlasts the rest; on the right, what survival follows as registering moves with worth
fig, (left, right) = plt.subplots(1, 2, figsize=(6.27, 3.4))
years = np.arange(1, YEARS + 1)
left.plot(years, first["curves"]["held"], color=BLUE, linewidth=2)
left.plot(years, first["curves"]["others"], color=ORANGE, linewidth=2)
left.text(YEARS + 0.5, first["curves"]["held"][-1], f"held at the\nstart: {first['curves']['held'][-1]:.0f}%", va="center")
left.text(YEARS + 0.5, first["curves"]["others"][-1], f"the others:\n{first['curves']['others'][-1]:.0f}%", va="center")
left.set_title("What is registered has nothing to do with worth", loc="left")
left.set_xlabel("year")
left.set_ylabel("per cent remaining")
left.set_ylim(0, 105)
left.set_xlim(1, YEARS + 14)  # room for the labels at the lines' ends
left.spines["bottom"].set_bounds(1, YEARS)
left.set_xticks([1, 10, 20, 30])
right.plot(CLOSENESS, [point["follows_holding"] for point in sweep], color=BLUE, linewidth=2, marker="o", markersize=8)
right.plot(CLOSENESS, [point["follows_worth"] for point in sweep], color=ORANGE, linewidth=2, marker="o", markersize=8)
right.axhline(0, color=GREY, linewidth=1)
right.text(0.5, sweep[2]["follows_holding"] - 0.035, "survival follows being held", ha="center", va="top")
right.text(0.52, sweep[2]["follows_worth"] - 0.03, "survival follows worth", ha="left", va="top")
right.set_title("As what is registered moves with worth", loc="left")
right.set_xlabel("how closely what is registered moves with worth")
right.set_ylabel("correlation with surviving")
right.set_xticks(CLOSENESS, ["none", "", "", "", "exactly"])
finish(fig, HERE / "sieve")

# The checks: the shape the figure's caption states, and the exact pair
for name, holds in shapes.items():
    assert holds, name
