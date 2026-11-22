"""Arrangements keeping a practice in step with a world that moves, each acting by a price on being wrong: the heavier being wrong weighs, the
more often it is out of step, further still when it learns how often it errs only from its own acts, and holding not finding out brings it
back.

The rules
  R1. Each year, with chance CHANGE, what an arrangement's practice should be changes, and it is out of step until it next acts. It begins
      out of step with chance START_OUT.
  R2. An arrangement finds out only by acting. In a year it acts, it corrects any mismatch, and the act goes wrong with chance GOES_WRONG, an
      error recorded against it. Not acting is recorded nowhere.
  R3. Each year it acts with chance value / (value + weight * supposed): weight is what being wrong weighs against what acting is for, and
      supposed is how often it supposes its acts go wrong.
  R4. Learning from its own acts: supposed is (errors + 1) / (acts + 2), over its acts of the last MEMORY years, so one half before it has
      acts to go on. Told: supposed is GOES_WRONG.
  R5. The value of acting is ACTING_IS_FOR. Holding not finding out as well adds GROWS for each year since it last acted, this one counted.
  R6. Within a year: the world moves, it acts or does not, and being out of step is then read.
  R7. Each case is ARRANGEMENTS arrangements over YEARS years, at each of WEIGHTS, drawn in turn. Years acted and being out of step are read
      over the whole span; not acting at all, over the last LAST_YEARS.

Run it with `python compute_anxious.py`. It writes anxious.json, and anxious as PDF and PNG, beside itself. To change a number, edit the block
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
SEED = 23
ARRANGEMENTS = 1000  # how many arrangements in each case
YEARS = 100  # years run
CHANGE = 0.2  # the chance a year that what the practice should be changes
GOES_WRONG = 0.1  # the chance an act goes wrong
MEMORY = 5  # the years of its own acts an arrangement goes on
START_OUT = 0.5  # the chance it begins out of step
ACTING_IS_FOR = 1.0  # what acting is for, against which being wrong is weighed
GROWS = 1.0  # what not finding out adds for each year since it last acted
LAST_YEARS = 10  # the last years, over which not acting at all is read
WEIGHT_LIGHT = 10  # the weight the text reads first
WEIGHT_HEAVY = 30  # the weight it reads second
WEIGHTS = (1, 2, 3, 5, 7, 10, 15, 20, 30, 40, 50)  # the weights of being wrong

parameters = {name.lower(): value for name, value in globals().items() if name.isupper()}
HERE = Path(__file__).resolve().parent
BLUE, RED, ORANGE, GREY, INK = "#2a78d6", "#e34948", "#eb6834", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})
rng = np.random.default_rng(SEED)
LEARNS, TOLD, BOTH = "learns", "told", "both"


def run(weight, case):
    """One case at one weight: the years acted, the per cent of the time out of step, and the per cent not acting in the last years."""
    out = rng.random(ARRANGEMENTS) < START_OUT  # R1
    acts, errors = np.zeros((ARRANGEMENTS, MEMORY), dtype=bool), np.zeros((ARRANGEMENTS, MEMORY), dtype=bool)
    since, acted, out_years, late = np.ones(ARRANGEMENTS), np.zeros(ARRANGEMENTS), np.zeros(ARRANGEMENTS), np.zeros(ARRANGEMENTS)
    for year in range(YEARS):
        out |= rng.random(ARRANGEMENTS) < CHANGE  # R1
        supposed = np.full(ARRANGEMENTS, GOES_WRONG) if case == TOLD else (errors.sum(axis=1) + 1) / (acts.sum(axis=1) + 2)  # R4
        value = ACTING_IS_FOR + (GROWS * since if case == BOTH else 0)  # R5
        act = rng.random(ARRANGEMENTS) < value / (value + weight * supposed)  # R3
        wrong = act & (rng.random(ARRANGEMENTS) < GOES_WRONG)  # R2
        out &= ~act
        acts[:, year % MEMORY], errors[:, year % MEMORY] = act, wrong
        since = np.where(act, 1, since + 1)
        acted += act
        out_years += out  # R6
        if year >= YEARS - LAST_YEARS:
            late += act
    return float(acted.mean()), float(100 * out_years.mean() / YEARS), float(100 * (late == 0).mean())


cases = {case: {weight: run(weight, case) for weight in WEIGHTS} for case in (LEARNS, TOLD, BOTH)}  # R7
out_of_step = {case: [cases[case][weight][1] for weight in WEIGHTS] for case in cases}
results = {
    "acts_light": cases[LEARNS][WEIGHT_LIGHT][0], "out_light": cases[LEARNS][WEIGHT_LIGHT][1],
    "told_acts_light": cases[TOLD][WEIGHT_LIGHT][0], "told_out_light": cases[TOLD][WEIGHT_LIGHT][1],
    "silent_heavy": cases[LEARNS][WEIGHT_HEAVY][2],
    "both_acts_light": cases[BOTH][WEIGHT_LIGHT][0], "both_out_light": cases[BOTH][WEIGHT_LIGHT][1],
    "both_silent_heavy": cases[BOTH][WEIGHT_HEAVY][2],
}
shapes = {
    "heavier_is_further_out": all(np.all(np.diff(out_of_step[case]) > 0) for case in cases),
    "learning_from_acts_is_further_out_than_told": all(a > b for a, b in zip(out_of_step[LEARNS], out_of_step[TOLD])),
    "holding_not_finding_out_brings_it_back": all(a > b for a, b in zip(out_of_step[LEARNS], out_of_step[BOTH])),
}
output = {**parameters, **results, **shapes, "out_of_step": out_of_step}
(HERE / "anxious.json").write_text(json.dumps(output, indent=1, sort_keys=True, default=lambda number: number.item()) + "\n", encoding="utf-8", newline="\n")

# The figure: how often out of step, against how heavily being wrong weighs, for each of the three
fig, ax = plt.subplots(figsize=(6.27, 3.4))
for case, color, label, place in ((LEARNS, RED, "learning only from\nits own acts", "center"), (TOLD, BLUE, "told how often its\nacts go wrong", "bottom"), (BOTH, ORANGE, "also holding\nnot finding out", "top")):
    ax.plot(WEIGHTS, out_of_step[case], color=color, linewidth=2)
    ax.text(WEIGHTS[-1] + 1, out_of_step[case][-1], label, va=place, color=color)
ax.set_xlabel("what being wrong weighs, against what acting is for")
ax.set_ylabel("per cent of the time out of step")
ax.set_xlim(0, WEIGHTS[-1] + 15)  # room for the labels at the lines' ends
ax.spines["bottom"].set_bounds(0, WEIGHTS[-1])
ax.set_xticks([1, 10, 20, 30, 40, 50])
ax.set_ylim(0, 100)
finish(fig, HERE / "anxious")

# The checks: the shape the figure's caption states
for name, holds in shapes.items():
    assert holds, name
