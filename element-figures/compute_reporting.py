"""Offices divide their effort by the losses held on it: the same rule gives noise, an effective report and a gamed one, according to what
someone holds a loss on.

The rules
  R1. Each office divides its effort, a whole each year, among four uses: the work, filing the report, raising the figure by other
      means, and its other duties.
  R2. Each use's share of the effort is in proportion to the square of the loss held on it. This is the best division when what each use
      returns grows with the square root of the effort put in.
  R3. The work returns the root of its effort. The figure the report shows rises with the work, and with raising it by other means.
  R4. Each office holds a loss on the work, drawn from WORK_LOSS_LOW to WORK_LOSS_HIGH, and OTHER_LOSS on its other duties. No one holds a
      loss on the report or on raising the figure unless a group below puts one there.
  R5. Noise: the report is held, and only at audit, which comes one year in AUDIT_EVERY, when the loss on it is AUDIT_LOSS.
  R6. Effective: someone holds THING_LOSS on the thing reported, which adds to the loss on the work.
  R7. Gamed: someone holds FIGURE_LOSS on the figure itself, which adds to the loss on the work. The other means cost COST_SHARE as much as
      the work, so the same effort raises the figure 1/COST_SHARE times as much, and the loss on them is that many times FIGURE_LOSS.
  R8. Each is compared with no requirement at all, over OFFICES offices and YEARS years.

Run it with `python compute_reporting.py`. It writes reporting.json, and reporting as PDF and PNG, beside itself. To change a number, edit
the block below and run it again.
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
OFFICES = 1000  # how many offices
USES = 4  # the work, the report, raising the figure, other duties
YEARS = 8  # how long each runs
AUDIT_EVERY = 4  # the audit comes one year in this many
COST_SHARE = 1 / 3  # what raising the figure by other means costs, against doing the work better
WORK_LOSS_LOW = 0.4  # the loss an office holds on its work is drawn from this ...
WORK_LOSS_HIGH = 0.7  # ... to this
OTHER_LOSS = 1.0  # the loss an office holds on its other duties
AUDIT_LOSS = 1.0  # the loss held on the report in an audit year
THING_LOSS = 1.0  # the loss someone holds on the thing reported, where the report is effective
FIGURE_LOSS = 1.0  # the loss someone holds on the figure, where the report is gamed

parameters = {name.lower(): value for name, value in globals().items() if name.isupper()}
HERE = Path(__file__).resolve().parent
BLUE, ORANGE, RED, GREY, LIGHT, INK = "#2a78d6", "#eb6834", "#e34948", "#8a8984", "#d5d4cf", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})
rng = np.random.default_rng(SEED)

WORK, REPORT, RAISING, OTHER = range(USES)
GROUPS = ("none", "noise", "effective", "gamed")
work_loss = rng.uniform(WORK_LOSS_LOW, WORK_LOSS_HIGH, OFFICES)  # R4
audit_year = (np.arange(1, YEARS + 1) % AUDIT_EVERY == 0)  # R5
worth_of_other_means = 1 / COST_SHARE


def run(group):
    """Each use's loss, and from it each office's effort, work and figure, year by year."""
    losses = np.zeros((OFFICES, YEARS, USES))
    losses[:, :, WORK] = work_loss[:, None]
    losses[:, :, OTHER] = OTHER_LOSS
    if group == "noise":
        losses[:, audit_year, REPORT] = AUDIT_LOSS  # R5
    if group == "effective":
        losses[:, :, WORK] += THING_LOSS  # R6
    if group == "gamed":
        losses[:, :, WORK] += FIGURE_LOSS  # R7
        losses[:, :, RAISING] = FIGURE_LOSS * worth_of_other_means
    effort = losses**2 / (losses**2).sum(axis=2, keepdims=True)  # R2
    work = np.sqrt(effort[:, :, WORK])  # R3
    figure = work + worth_of_other_means * np.sqrt(effort[:, :, RAISING])
    return {"effort": effort.mean(axis=(0, 1)), "work": work.sum(), "figure": figure.sum()}


found = {group: run(group) for group in GROUPS}  # R8
work_level = {group: found[group]["work"] / found["none"]["work"] for group in GROUPS}
figure_level = {group: found[group]["figure"] / found["none"]["figure"] for group in GROUPS}
results = {
    "work_fall_audit": 100 * (1 - work_level["noise"]),
    "work_gain_thing": 100 * (work_level["effective"] - 1),
    "figure_ratio": figure_level["gamed"],
    "work_fall_figure": 100 * (1 - work_level["gamed"]),
    "report_share_audit": 100 * found["noise"]["effort"][REPORT],
    "raising_share_gamed": 100 * found["gamed"]["effort"][RAISING],
}
shapes = {
    "noise_takes_a_little_from_the_work": 0 < results["work_fall_audit"] < results["work_gain_thing"],
    "effective_raises_the_work": work_level["effective"] > 1,
    "gamed_raises_the_figure_and_lowers_the_work": figure_level["gamed"] > 1 > work_level["gamed"],
}
shapes["three_groups_sort"] = all(shapes.values())
output = {**parameters, **results, **shapes,
          "work_level": work_level, "figure_level": figure_level,
          "effort": {group: (100 * found[group]["effort"]).tolist() for group in GROUPS}}
(HERE / "reporting.json").write_text(json.dumps(output, indent=1, sort_keys=True, default=lambda number: number.item()) + "\n", encoding="utf-8", newline="\n")

# The figure: where the effort goes in each group, and what happens to the work and the figure
fig, (effort, levels) = plt.subplots(2, 1, figsize=(6.27, 5.8))
names = ("no\nrequirement", "noise:\nreport held\nat audit", "effective:\nthing\nreported held", "gamed:\nfigure held")
uses = ((BLUE, WORK), (ORANGE, REPORT), (RED, RAISING), (LIGHT, OTHER))
for x, group in enumerate(GROUPS):
    bottom = 0.0
    for colour, use in uses:
        share = 100 * found[group]["effort"][use]
        effort.bar(x, share, bottom=bottom, color=colour, edgecolor="white", linewidth=1.5, width=0.75)
        if share >= 7:
            words = f"report {share:.0f}" if use == REPORT else f"{share:.0f}"
            effort.text(x, bottom + share / 2, words, ha="center", va="center", color=INK if colour == LIGHT else "white")
        bottom += share
effort.text(3.5, 100 * found["gamed"]["effort"][WORK] / 2, "the work", va="center", color=INK)
effort.text(3.5, 100 * (found["gamed"]["effort"][WORK] + found["gamed"]["effort"][RAISING] / 2), "raising\nthe figure", va="center", color=INK)
effort.text(3.5, 100 - 100 * found["gamed"]["effort"][OTHER] / 2, "other duties", va="center", color=INK)
effort.set_xticks(range(4), names)
effort.set_xlim(-0.5, 4.5)
effort.set_ylim(0, 100)
effort.set_ylabel("per cent of effort")
effort.tick_params(axis="x", length=0)

for x, group in enumerate(GROUPS[1:]):
    levels.bar(x - 0.2, work_level[group], width=0.38, color=BLUE)
    levels.bar(x + 0.2, figure_level[group], width=0.38, color=RED)
    levels.text(x - 0.2, work_level[group] + 0.1, f"{work_level[group]:.2f}", ha="center")
    levels.text(x + 0.2, figure_level[group] + 0.1, f"{figure_level[group]:.2f}", ha="center")
levels.axhline(1, color=GREY, linewidth=1, linestyle="--")
levels.text(1.92, figure_level["gamed"] * 0.93, "the figure", ha="right", va="center")
levels.text(1.7, work_level["gamed"] + 0.55, "the work", ha="center")
levels.set_xticks(range(3), names[1:])
levels.set_ylabel("times its level with no requirement")
levels.tick_params(axis="x", length=0)
finish(fig, HERE / "reporting")

# The checks: the three groups sort as the claim says, and the rule is the best division
for name, holds in shapes.items():
    assert holds, name
losses = np.array([0.7, 0.2, 0.5, 1.0])
best = losses**2 / (losses**2).sum()
for other in rng.dirichlet(np.ones(USES), 200):
    assert (losses * np.sqrt(other)).sum() <= (losses * np.sqrt(best)).sum() + 1e-12, "R2 is the best division under root returns"
