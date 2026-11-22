"""Reforms after failures, cut as attention fades, and what counts changing in year 40: reforms with a holder outlast the rest, and the
change shows only as held reforms accumulate.

The rules
  R1. Each arrangement fails with chance FAIL_BARE a year with no protective capacity in place, and FAIL_PROTECTED with one.
  R2. A failure brings attention, at full strength. Attention loses FADE of itself each year.
  R3. A failure where no capacity is in place brings a reform with chance USUALLY, which puts a capacity in place.
  R4. A reform comes with a holder with chance HOLDER_BEFORE, and HOLDER_AFTER from counted year CHANGE_YEAR, when what counts changes.
  R5. A reform with no holder is protected while attention stands at ATTENTION_LASTS or more. After that, each tight year (chance TIGHT) it
      is cut with chance CUT_IN_TIGHT_YEAR.
  R6. A reform with a holder lapses only when its holder does, with chance MOVE_ON a year.
  R7. Within a year: attention fades, holders move on and tight years cut, then failures come, with their attention and reforms.
  R8. Each run is a start of START_YEARS, then COUNTED_YEARS counted. A reform's life is watched for WATCH years, among reforms made in the
      counted years with that long left to watch.
  R9. Failures before the change are read over the counted years before it, and after it over the last LAST_YEARS.

Run it with `python compute_orders.py`. It writes orders.json, and orders as PDF and PNG, beside itself. To change a number, edit the block
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
ARRANGEMENTS = 600  # how many arrangements
RUNS = 40  # how many runs
START_YEARS = 30  # years run before counting begins
COUNTED_YEARS = 80  # years counted
CHANGE_YEAR = 40  # the counted year from which what counts has changed
FAIL_BARE = 0.06  # the chance a year of failing with no protective capacity
FAIL_PROTECTED = 0.015  # the same with one
FADE = 0.30  # the share of itself attention loses each year
MOVE_ON = 0.02  # the chance a year that a holder moves on
HOLDER_BEFORE = 0.10  # the share of reforms with a holder, before the change
HOLDER_AFTER = 0.50  # the same, from the change
USUALLY = 0.90  # the chance a failure brings a reform
ATTENTION_LASTS = 0.30  # attention protects an unheld reform while it stands at this or more
TIGHT = 0.40  # the chance a year is tight
CUT_IN_TIGHT_YEAR = 0.35  # the chance in a tight year that an unheld reform with no attention left is cut
WATCH = 20  # years a reform's life is watched
LAST_YEARS = 10  # the last years, over which failures after the change are read

parameters = {name.lower(): value for name, value in globals().items() if name.isupper()}
HERE = Path(__file__).resolve().parent
BLUE, RED, ORANGE, GREY, INK = "#2a78d6", "#e34948", "#eb6834", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})
rng = np.random.default_rng(SEED)

shape = (RUNS, ARRANGEMENTS)
in_place, held = np.zeros(shape, dtype=bool), np.zeros(shape, dtype=bool)
made, attention = np.zeros(shape, dtype=int), np.zeros(shape)
failures = np.zeros(COUNTED_YEARS)
lives = {True: [], False: []}  # for reforms with a holder and with none: the year made, and the years lasted


def close(which, year):
    """Record how long each reform in `which` lasted."""
    for kind in (True, False):
        chosen = which & (held == kind)
        lives[kind].append(np.stack([made[chosen], year - made[chosen]], axis=1))


for year in range(1, START_YEARS + COUNTED_YEARS + 1):  # R8
    counted = year - START_YEARS
    attention *= 1 - FADE  # R2
    tight = rng.random((RUNS, 1)) < TIGHT
    cut = in_place & ~held & (attention < ATTENTION_LASTS) & tight & (rng.random(shape) < CUT_IN_TIGHT_YEAR)  # R5
    lapsed = in_place & held & (rng.random(shape) < MOVE_ON)  # R6
    close(cut | lapsed, year)
    in_place &= ~(cut | lapsed)
    fails = rng.random(shape) < np.where(in_place, FAIL_PROTECTED, FAIL_BARE)  # R1
    if counted >= 1:
        failures[counted - 1] = 100 * fails.mean()
    attention[fails] = 1.0  # R2
    reform = fails & ~in_place & (rng.random(shape) < USUALLY)  # R3
    holder_share = HOLDER_AFTER if counted >= CHANGE_YEAR else HOLDER_BEFORE  # R4
    held = np.where(reform, rng.random(shape) < holder_share, held)
    made = np.where(reform, year, made)
    in_place |= reform
close(in_place, START_YEARS + COUNTED_YEARS + 1)


def watched(kind):
    """R8: how long each watched reform lasted."""
    record = np.concatenate(lives[kind])
    return record[(record[:, 0] > START_YEARS) & (record[:, 0] <= START_YEARS + COUNTED_YEARS - WATCH), 1]


survival = {name: [100 * float((watched(kind) > age).mean()) for age in range(WATCH + 1)] for name, kind in (("held", True), ("unheld", False))}
results = {
    "unheld_half_gone": next((age for age, share in enumerate(survival["unheld"]) if share <= 50), None),
    "unheld_remaining": survival["unheld"][-1], "held_remaining": survival["held"][-1],
    "failures_before": failures[:CHANGE_YEAR].mean(), "failures_after": failures[-LAST_YEARS:].mean(),  # R9
}
shapes = {
    "held_outlast_unheld": results["held_remaining"] > results["unheld_remaining"],
    "failures_fall_after_the_change": results["failures_after"] < results["failures_before"],
}
output = {**parameters, **results, **shapes, "survival": survival, "failures": failures.tolist()}
(HERE / "orders.json").write_text(json.dumps(output, indent=1, sort_keys=True, default=lambda number: number.item()) + "\n", encoding="utf-8", newline="\n")

# The figure: on the left, what lasts; on the right, failures come down only slowly once what counts has changed
fig, (left, right) = plt.subplots(1, 2, figsize=(6.27, 3.4))
ages = np.arange(WATCH + 1)
left.plot(ages, survival["held"], color=BLUE, linewidth=2)
left.plot(ages, survival["unheld"], color=RED, linewidth=2)
left.text(WATCH + 0.3, survival["held"][-1], f"with a holder:\n{survival['held'][-1]:.0f}%", va="center")
left.text(WATCH + 0.3, survival["unheld"][-1], f"with none:\n{survival['unheld'][-1]:.0f}%", va="center")
left.set_xlabel("years since the reform was made")
left.set_ylabel("per cent still in place")
left.set_xlim(0, WATCH + 8)  # room for the labels at the lines' ends
left.spines["bottom"].set_bounds(0, WATCH)
left.set_xticks([0, 5, 10, 15, 20])
left.set_ylim(0, 105)
years = np.arange(1, COUNTED_YEARS + 1)
smooth = np.convolve(failures, np.ones(5) / 5, mode="valid")
right.plot(years[2:-2], smooth, color=ORANGE, linewidth=2)
right.axvline(CHANGE_YEAR, color=GREY, linewidth=1, linestyle=":")
right.text(CHANGE_YEAR + 1, max(smooth) * 1.18, "what counts\nchanges", color=GREY, va="top")
right.plot([1, CHANGE_YEAR], [results["failures_before"]] * 2, color=INK, linewidth=1, linestyle="--")
right.plot([COUNTED_YEARS - LAST_YEARS + 1, COUNTED_YEARS], [results["failures_after"]] * 2, color=INK, linewidth=1, linestyle="--")
right.text(3, results["failures_before"] * 0.87, f"{results['failures_before']:.1f}")
right.text(COUNTED_YEARS, results["failures_after"] * 0.85, f"{results['failures_after']:.1f}", ha="right")
right.set_xlabel("year")
right.set_ylabel("failures per 100 arrangements a year\n(five-year average)")
right.set_xlim(1, COUNTED_YEARS)
right.set_ylim(0, max(smooth) * 1.2)
finish(fig, HERE / "orders")

# The checks: the shape the figure's caption states
for name, holds in shapes.items():
    assert holds, name
