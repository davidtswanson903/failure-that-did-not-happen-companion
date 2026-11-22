"""Reviews that each forbid little, jointly forbidding much: first exact on 256 projects, then a population of proposals.

The rules
  R1. Each review registers one concern. No review registers the number of homes.
  R2. Exact case: there are CONCERNS concerns, and a project raises some set of them, so there is one project for each set. It provides
      BASE_HOMES homes, plus HOMES_PER_CONCERN for each concern it raises.
  R3. Exact case: each review vetoes any project that raises its concern and approves every other. A project is built only if every review
      approves it.
  R4. Population: PROPOSALS proposals, of sizes spread around MEDIAN_HOMES on a logarithmic scale, from SMALLEST to LARGEST homes.
  R5. A proposal raises each concern on its own, with a chance that rises with its size: RAISE_AT_SMALLEST at the smallest, and
      RAISE_PER_TENFOLD more for each tenfold rise in homes.
  R6. Each review vetoes a share VETO of the proposals that raise its concern, on its own. A proposal passes only if every review approves.
  R7. Approval at a size is the rule's own chance at that size, with no draw.

Run it with `python compute_stack.py`. It writes stack.json, and stack as PDF and PNG, beside itself. To change a number, edit the block
below and run it again.
"""
import json
from itertools import product
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from figure_style import fonts, finish
import numpy as np

# Parameters: every number the model uses
SEED = 1
CONCERNS = 8  # how many concerns, and so how many reviews
BASE_HOMES = 10  # exact case: the homes a project raising no concern provides
HOMES_PER_CONCERN = 20  # exact case: the homes each further concern adds
LARGE = 100  # exact case: the size of project the joint prohibition is about
PROPOSALS = 20000  # population: how many proposals
VETO = 0.30  # population: the share of proposals raising its concern that a review vetoes
MEDIAN_HOMES = 16  # population: half of proposals are smaller than this
SIZE_SPREAD = 1.5  # population: how widely sizes spread around the median, on a logarithmic scale
SMALLEST = 4  # population: no proposal is smaller
LARGEST = 400  # population: no proposal is larger
RAISE_AT_SMALLEST = 0.06  # population: the chance the smallest proposal raises a given concern
RAISE_PER_TENFOLD = 0.30  # population: how much more likely, for each tenfold rise in homes

parameters = {name.lower(): value for name, value in globals().items() if name.isupper()}
HERE = Path(__file__).resolve().parent
BLUE, RED, GREY, INK = "#2a78d6", "#e34948", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})
rng = np.random.default_rng(SEED)

# The exact case: every project, and what each review and the stack approve
raised = np.array(list(product((False, True), repeat=CONCERNS)))  # R2
homes = BASE_HOMES + HOMES_PER_CONCERN * raised.sum(axis=1)
alone = [~raised[:, review] for review in range(CONCERNS)]  # R3
stack = np.logical_and.reduce(alone)
large = homes >= LARGE
exact = {
    "projects": len(raised), "one_review_largest": max(int(homes[approved].max()) for approved in alone), "stack_largest": int(homes[stack].max()),
    "stack_approves_one_project": int(stack.sum()) == 1,
    "joint_prohibition": all(bool((approved & large).any()) for approved in alone) and not bool((stack & large).any()),
}


# The population
def chance_raised(size):
    """R5: the chance a proposal of this size raises a given concern."""
    return RAISE_AT_SMALLEST + RAISE_PER_TENFOLD * np.log10(size / SMALLEST)


def approval(size, reviews):
    """R7: the chance a proposal of this size passes this many reviews."""
    return (1 - VETO * chance_raised(size)) ** reviews


sizes = np.clip(MEDIAN_HOMES * np.exp(SIZE_SPREAD * rng.standard_normal(PROPOSALS)), SMALLEST, LARGEST)  # R4
raises = rng.random((PROPOSALS, CONCERNS)) < chance_raised(sizes)[:, None]  # R5
approves = ~(raises & (rng.random((PROPOSALS, CONCERNS)) < VETO))  # R6
passes = approves.all(axis=1)
each_alone = 100 * approves.mean(axis=0)

results = {
    **exact, "proposals": PROPOSALS, "one_review_low": each_alone.min(), "one_review_high": each_alone.max(),
    "stack_proposals": 100 * passes.mean(), "stack_homes": 100 * sizes[passes].sum() / sizes.sum(),
    "approval_smallest": 100 * approval(SMALLEST, CONCERNS), "approval_largest": 100 * approval(LARGEST, CONCERNS),
}
# The same two numbers, under the names of what the text says of them in words
results["homes_under_a_third"] = results["stack_homes"]
results["each_over_nine_in_ten"] = results["one_review_low"]
shapes = {
    "each_alone_approves_most": results["one_review_low"] > results["stack_proposals"],
    "each_alone_rounds_to_one_figure": round(results["one_review_low"]) == round(results["one_review_high"]),
    "homes_fare_worse_than_proposals": results["stack_homes"] < results["stack_proposals"],
    "approval_falls_with_size": results["approval_smallest"] > results["approval_largest"],
}
output = {**parameters, **results, **shapes}
(HERE / "stack.json").write_text(json.dumps(output, indent=1, sort_keys=True, default=lambda number: number.item()) + "\n", encoding="utf-8", newline="\n")

# The figure: each review alone approves nearly everything, and the eight fall hardest on the largest
fig, ax = plt.subplots(figsize=(6.27, 3.8))
axis = np.geomspace(SMALLEST, LARGEST, 80)
ax.plot(axis, 100 * approval(axis, 1), color=BLUE, linewidth=2)
ax.plot(axis, 100 * approval(axis, CONCERNS), color=RED, linewidth=2)
ax.text(LARGEST * 0.92, 100 * approval(LARGEST, 1) - 7, "one review alone", ha="right")
ax.text(70, 100 * approval(70, CONCERNS) - 7, f"all {CONCERNS} together", ha="right", va="top")
ax.annotate(f"{100 * approval(SMALLEST, CONCERNS):.0f}%", (SMALLEST, 100 * approval(SMALLEST, CONCERNS)), textcoords="offset points", xytext=(6, 5))
ax.annotate(f"{100 * approval(LARGEST, CONCERNS):.0f}%", (LARGEST, 100 * approval(LARGEST, CONCERNS)), textcoords="offset points", xytext=(-6, 8), ha="right")
ax.text(LARGEST, 3, f"Of all proposals, {results['stack_proposals']:.0f}% pass, carrying {results['stack_homes']:.0f}% of the homes", ha="right", color=INK)
ax.set_xscale("log")
ax.set_xticks([4, 10, 40, 100, 400], ["4", "10", "40", "100", "400"])
ax.minorticks_off()
ax.set_xlim(SMALLEST, LARGEST)
ax.set_ylim(0, 105)
ax.set_xlabel("homes the proposal provides")
ax.set_ylabel("per cent of proposals approved")
finish(fig, HERE / "stack")

# The checks: joint prohibition exactly, with the rule's own numbers, then the shape the figure's caption states
assert exact["projects"] == 2**CONCERNS
assert exact["stack_largest"] == BASE_HOMES and exact["stack_approves_one_project"]
assert exact["one_review_largest"] == BASE_HOMES + HOMES_PER_CONCERN * (CONCERNS - 1)
assert exact["joint_prohibition"], "no review alone excludes a project of this size, and the stack never reaches one"
for name, holds in shapes.items():
    assert holds, name
