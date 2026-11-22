"""Damage the register drops, and a correction that lasts while held: whether a city's register still finds its weakest bridges as the
world changes in what it does not see.

The rules
  R1. A city has BRIDGES bridges, of ages drawn from 0 to OLDEST years. Each wears at its own rate, from 0 to 1 a year, and its wear is its
      rate times its age.
  R2. Three kinds of damage begin in years ONSETS: corrosion, fatigue and scour. Each grows at each bridge at its own rate, from 0 to
      DAMAGE_RATE a year.
  R3. A bridge's weakness is its wear and all its damage together.
  R4. The register sees wear, read with an error of READING_ERROR times the spread of wear across the bridges.
  R5. A correcting capacity, where one is in place, comes to register each new kind of damage LAG years after it begins, and adds what
      has grown from then on to what the register shows.
  R6. Each kind's registering is a correction of its own. One no one holds has chance UNHELD_END each year of ending. What it recorded
      stays on the register, no longer growing. One that is held does not end.
  R7. Inspections are completed on schedule in every year, under every arrangement.
  R8. What the bridges are for is measured each year as the share of the WEAKEST truly weakest bridges that the register also ranks among
      its WEAKEST weakest.

Run it with `python compute_purpose.py`. It writes purpose.json, and purpose as PDF and PNG, beside itself. To change a number, edit the
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
BRIDGES = 400  # how many bridges
YEARS = 40  # how long each run lasts
RUNS = 300  # how many runs
ONSETS = (8, 18, 28)  # the years corrosion, fatigue and scour begin
LAG = 3  # years from a kind of damage beginning to a correcting capacity registering it
UNHELD_END = 0.15  # the chance a year that a correction no one holds ends
WEAKEST = 40  # how many of the weakest bridges the measure looks at
OLDEST = 50  # bridges are drawn from new to this many years old
DAMAGE_RATE = 2.0  # each kind of damage grows at up to this a year; wear grows at up to 1
READING_ERROR = 0.05  # how far the register misreads wear, as a share of the spread of wear
BEFORE_YEAR = 7  # the year the first figure is read, before any damage begins

parameters = {name.lower(): value for name, value in globals().items() if name.isupper()}
HERE = Path(__file__).resolve().parent
BLUE, ORANGE, RED, GREY, INK = "#2a78d6", "#eb6834", "#e34948", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})
rng = np.random.default_rng(SEED)

ages = rng.random((RUNS, BRIDGES)) * OLDEST  # R1
wear_rate = rng.random((RUNS, BRIDGES))
damage_rate = rng.random((RUNS, len(ONSETS), BRIDGES)) * DAMAGE_RATE  # R2
reading = rng.standard_normal((RUNS, BRIDGES))  # R4
onsets = np.array(ONSETS)
starts = onsets + LAG  # R5: the year each kind comes to be registered

# R6: the last year each kind's correction runs, where no one holds it
years_it_runs = rng.geometric(UNHELD_END, (RUNS, len(ONSETS)))
ends = {"none": np.zeros((RUNS, len(ONSETS)), dtype=int), "unheld": starts - 1 + years_it_runs, "held": np.full((RUNS, len(ONSETS)), YEARS)}


def share_found(true, seen):
    """R8: the share of the truly weakest that the register also ranks among its weakest, over all the runs."""
    truly = np.argsort(-true, axis=1)[:, :WEAKEST]
    ranked = np.argsort(-seen, axis=1)[:, :WEAKEST]
    on_register = np.zeros(seen.shape, dtype=bool)
    np.put_along_axis(on_register, ranked, True, axis=1)
    return 100 * np.take_along_axis(on_register, truly, axis=1).mean()


curves = {regime: [] for regime in ends}
for year in range(1, YEARS + 1):
    wear = wear_rate * (ages + year)  # R1
    damage = damage_rate * np.clip(year - onsets + 1, 0, None)[None, :, None]  # R2
    true = wear + damage.sum(axis=1)  # R3
    read_wear = wear + READING_ERROR * wear.std(axis=1, keepdims=True) * reading  # R4
    for regime, last_year in ends.items():
        recorded_years = np.clip(np.minimum(year, last_year) - starts + 1, 0, None)  # R5, R6
        curves[regime].append(share_found(true, read_wear + (damage_rate * recorded_years[:, :, None]).sum(axis=1)))

results = {"found_before": curves["none"][BEFORE_YEAR - 1], "found_none": curves["none"][-1],
           "found_unheld": curves["unheld"][-1], "found_held": curves["held"][-1],
           "onset_corrosion": ONSETS[0], "onset_fatigue": ONSETS[1], "onset_scour": ONSETS[2]}
shapes = {
    "the_register_drifts_with_no_correction": results["found_none"] < results["found_before"],
    "a_correction_no_one_holds_does_little": results["found_none"] <= results["found_unheld"]
    < (results["found_none"] + results["found_held"]) / 2,
    "held_keeps_most": results["found_held"] > results["found_unheld"],
    "inspections_on_schedule": True,  # R7: nothing in the model moves them
}
output = {**parameters, **results, **shapes, "curves": curves}
(HERE / "purpose.json").write_text(json.dumps(output, indent=1, sort_keys=True, default=lambda number: number.item()) + "\n", encoding="utf-8", newline="\n")

# The figure: the measure holds still, and the register finds the weakest only where its correction is held
fig, ax = plt.subplots(figsize=(6.27, 3.8))
years = np.arange(1, YEARS + 1)
ax.plot([1, YEARS], [100, 100], color=GREY, linewidth=1, linestyle="--")
ax.text(YEARS + 0.5, 101, "inspections on schedule: every year", color=GREY, va="center")
for onset, kind in zip(ONSETS, ("corrosion", "fatigue", "scour")):
    ax.plot([onset, onset], [0, 97], color=GREY, linewidth=0.7, linestyle=":")
    ax.text(onset + 0.3, 3, f"{kind}\nbegins", color=GREY, va="bottom")
for regime, words, colour, nudge in (("held", "correction held", BLUE, -3), ("unheld", "correction no one holds", ORANGE, 0), ("none", "no correction", RED, 0)):
    ax.plot(years, curves[regime], color=colour, linewidth=2)
    ax.text(YEARS + 0.5, curves[regime][-1] + nudge, f"{words}: {curves[regime][-1]:.0f}%", va="center")
ax.set_xlabel("year")
ax.set_ylabel("per cent of weakest bridges found")
ax.set_xlim(1, YEARS + 21)  # room for the labels at the lines' ends
ax.spines["bottom"].set_bounds(1, YEARS)
ax.set_xticks([1, 10, 20, 30, 40])
ax.set_ylim(0, 108)
finish(fig, HERE / "purpose")

# The checks: the shape the figure's caption states
for name, holds in shapes.items():
    assert holds, name
