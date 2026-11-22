"""Four causes open routes to cutting a programme, and a held lapse closes them: what happens when causes are taken away, and when the
programme is held instead.

The rules
  R1. Each city has its own chance of meeting each cause in any year, drawn at random from nothing up to CAP.
  R2. In a year when any cause arises, one route opens: someone proposes the cut.
  R3. A proposal ends in a cut with chance CUT_UNHELD where no one holds the lapse, and CUT_HELD where someone does.
  R4. A programme no one holds can also be folded away with no cause at all, with chance FOLD a year.
  R5. A programme cut stays cut.
  R6. The four scenarios, over YEARS: every cause and no holder; each city's likeliest cause gone and no holder; every cause gone and
      no holder; every cause and a holder for every programme.
  R7. How often causes arise is varied by multiplying every chance by each factor in SWEEP, with no holder.

Run it with `python compute_causes.py`. It writes causes.json, and causes as PDF and PNG, beside itself. To change a number, edit the
block below and run it again.
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
CITIES = 4000  # how many model cities
CAUSES = 4  # how many causes each city can meet
YEARS = 20  # how long each runs
CAP = 0.30  # each chance of a cause is drawn from 0 up to this, a year
CUT_UNHELD = 0.60  # the chance a proposal ends in a cut where no one holds the lapse
CUT_HELD = 0.03  # the same where someone holds it
FOLD = 0.03  # the chance a year that a programme no one holds is folded away with no cause
SWEEP = (0.5, 1.0, 2.0)  # how often causes arise: every chance is multiplied by each of these

parameters = {name.lower(): value for name, value in globals().items() if name.isupper()}
HERE = Path(__file__).resolve().parent
BLUE, ORANGE, AQUA, RED, GREY, INK = "#2a78d6", "#eb6834", "#1baf7a", "#e34948", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})
rng = np.random.default_rng(SEED)


def cut_years(chances, held):
    """R2 to R5: the year each city's programme is cut, or 0 if it lasts."""
    cut = np.zeros(CITIES, dtype=int)
    for year in range(1, YEARS + 1):
        route = (rng.random((CITIES, CAUSES)) < chances).any(axis=1)  # R2
        cut_now = route & (rng.random(CITIES) < (CUT_HELD if held else CUT_UNHELD))  # R3
        if not held:
            cut_now |= rng.random(CITIES) < FOLD  # R4
        cut[(cut == 0) & cut_now] = year  # R5
    return cut


chances = rng.random((CITIES, CAUSES)) * CAP  # R1
without_likeliest = chances.copy()
without_likeliest[np.arange(CITIES), chances.argmax(axis=1)] = 0.0

scenarios = {  # R6
    "all": cut_years(chances, held=False),
    "likeliest_removed": cut_years(without_likeliest, held=False),
    "all_removed": cut_years(np.zeros_like(chances), held=False),
    "held": cut_years(chances, held=True),
}
sweep = [100 * (cut_years(chances * factor, held=False) > 0).mean() for factor in SWEEP]  # R7


def by_year(cut):
    return [100 * ((cut > 0) & (cut <= year)).mean() for year in range(1, YEARS + 1)]


curves = {name: by_year(cut) for name, cut in scenarios.items()}
results = {f"share_{name}": curve[-1] for name, curve in curves.items()}
results["median_delay"] = float(np.median(scenarios["likeliest_removed"][scenarios["likeliest_removed"] > 0])
                                - np.median(scenarios["all"][scenarios["all"] > 0]))
results.update(sweep_low=min(sweep), sweep_high=max(sweep))
shapes = {
    "taking_causes_away_moves_it_less_than_holding": results["share_all"] - results["share_likeliest_removed"]
    < results["share_all"] - results["share_held"],
    "folding_cuts_with_no_cause": results["share_all_removed"] > 0,
    "the_scenarios_fall_in_order": results["share_all"] >= results["share_likeliest_removed"] > results["share_all_removed"],
    "holding_cuts_least_with_every_cause_in_place": results["share_held"] < results["share_likeliest_removed"],
}
output = {**parameters, **results, **shapes, "curves": curves, "sweep": sweep}
(HERE / "causes.json").write_text(json.dumps(output, indent=1, sort_keys=True, default=lambda number: number.item()) + "\n", encoding="utf-8", newline="\n")

# The figure: taking causes away hardly moves the line, and holding moves it most
fig, ax = plt.subplots(figsize=(6.27, 3.8))
years = np.arange(1, YEARS + 1)
lines = (("all", "every cause, no holder", RED, 3), ("likeliest_removed", "likeliest cause taken away", ORANGE, -5),
         ("all_removed", "every cause taken away", AQUA, 0), ("held", "every cause, and held", BLUE, 0))
for name, words, colour, nudge in lines:
    ax.plot(years, curves[name], color=colour, linewidth=2)
    ax.text(YEARS + 0.3, curves[name][-1] + nudge, f"{words}: {curves[name][-1]:.0f}%", va="center", color=INK)
ax.set_xlabel("year")
ax.set_ylabel("per cent of programmes cut")
ax.set_xlim(1, YEARS + 12)  # room for the labels at the lines' ends
ax.spines["bottom"].set_bounds(1, YEARS)
ax.set_xticks([1, 5, 10, 15, 20])
ax.set_ylim(0, 105)
finish(fig, HERE / "causes")

# The checks: the shape the figure's caption states
for name, holds in shapes.items():
    assert holds, name
