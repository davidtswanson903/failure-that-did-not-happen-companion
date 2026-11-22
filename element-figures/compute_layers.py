"""Reviews added one at a time: each forbids a little more, and the homes forbidden grow fastest.

The rules
  R1. Each review registers one concern. No review registers the number of homes.
  R2. PROPOSALS proposals, of sizes spread around MEDIAN_HOMES on a logarithmic scale, from SMALLEST to LARGEST homes.
  R3. A proposal raises each concern on its own, with a chance that rises with its size: RAISE_AT_SMALLEST at the smallest, and
      RAISE_PER_TENFOLD more for each tenfold rise in homes.
  R4. Each review vetoes a share VETO of the proposals that raise its concern, on its own. A proposal passes only if every review approves.
  R5. Reviews are added one at a time, up to MOST_REVIEWS, and the stack of the first k is counted for each k.
  R6. Approval at a size is the rule's own chance at that size, with no draw.

Run it with `python compute_layers.py`. It writes layers.json, and layers as PDF and PNG, beside itself. To change a number, edit the block
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
SEED = 2
MOST_REVIEWS = 12  # reviews are added up to this many
PROPOSALS = 20000  # how many proposals
VETO = 0.30  # the share of proposals raising its concern that a review vetoes
MEDIAN_HOMES = 16  # half of proposals are smaller than this
SIZE_SPREAD = 1.5  # how widely sizes spread around the median, on a logarithmic scale
SMALLEST = 4  # no proposal is smaller
LARGEST = 400  # no proposal is larger
RAISE_AT_SMALLEST = 0.06  # the chance the smallest proposal raises a given concern
RAISE_PER_TENFOLD = 0.30  # how much more likely, for each tenfold rise in homes

parameters = {name.lower(): value for name, value in globals().items() if name.isupper()}
HERE = Path(__file__).resolve().parent
BLUE, ORANGE, RED, GREY, INK = "#2a78d6", "#eb6834", "#e34948", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})
rng = np.random.default_rng(SEED)


def chance_raised(size):
    """R3: the chance a proposal of this size raises a given concern."""
    return RAISE_AT_SMALLEST + RAISE_PER_TENFOLD * np.log10(size / SMALLEST)


sizes = np.clip(MEDIAN_HOMES * np.exp(SIZE_SPREAD * rng.standard_normal(PROPOSALS)), SMALLEST, LARGEST)  # R2
raises = rng.random((PROPOSALS, MOST_REVIEWS)) < chance_raised(sizes)[:, None]  # R3
approves = ~(raises & (rng.random((PROPOSALS, MOST_REVIEWS)) < VETO))  # R4
passes = np.logical_and.accumulate(approves, axis=1)  # R5

reviews = np.arange(1, MOST_REVIEWS + 1)
curves = {
    "proposals": (100 * passes.mean(axis=0)).tolist(),
    "homes": (100 * (sizes[:, None] * passes).sum(axis=0) / sizes.sum()).tolist(),
    "largest": [100 * float(1 - VETO * chance_raised(LARGEST)) ** k for k in reviews],  # R6
}
results = {"proposals": PROPOSALS}
for k, word in ((1, "one"), (8, "eight"), (MOST_REVIEWS, "twelve")):
    results[f"{word}_proposals"], results[f"{word}_homes"] = curves["proposals"][k - 1], curves["homes"][k - 1]
results["largest_one"], results["largest_twelve"] = curves["largest"][0], curves["largest"][-1]
shapes = {
    "each_review_forbids_no_less": bool((passes[:, 1:] <= passes[:, :-1]).all()),
    "every_review_lowers_the_share": all(a > b for a, b in zip(curves["proposals"], curves["proposals"][1:])),
    "homes_fall_fastest": curves["homes"][-1] / curves["homes"][0] < curves["proposals"][-1] / curves["proposals"][0],
}
output = {**parameters, **results, **shapes, "curves": curves}
(HERE / "layers.json").write_text(json.dumps(output, indent=1, sort_keys=True, default=lambda number: number.item()) + "\n", encoding="utf-8", newline="\n")

# The figure: what passes as reviews are added, with the homes below the proposals
fig, ax = plt.subplots(figsize=(6.27, 3.8))
for key, colour, words in (("proposals", BLUE, "proposals that pass"), ("homes", ORANGE, "homes they carry"), ("largest", RED, "approval at 400 homes")):
    ax.plot(reviews, curves[key], color=colour, linewidth=2, marker="o", markersize=6)
    ax.text(MOST_REVIEWS + 0.25, curves[key][-1], f"{words}: {curves[key][-1]:.0f}%", va="center")
ax.set_xticks(reviews)
ax.set_xlim(0.7, MOST_REVIEWS + 6.5)  # room for the labels at the lines' ends
ax.spines["bottom"].set_bounds(1, MOST_REVIEWS)
ax.set_ylim(0, 105)
ax.set_xlabel("reviews in the stack")
ax.set_ylabel("per cent")
finish(fig, HERE / "layers")

# The checks: each review added forbids no less, exactly, then the shape the figure's caption states
for name, holds in shapes.items():
    assert holds, name
