"""The worked city over forty years: maintenance cut in tight years, damage inside the steel, and what each option changes depends on whether
it is held.

The rules
  R1. The city begins with START_BRIDGES bridges and opens NEW_A_YEAR more each year. Their upkeep is added to what maintenance has to
      cover, with no money added for it.
  R2. Each bridge carries damage inspection sees and damage inside the steel, which it does not. A bridge is near failure when the two
      together reach 1. The first bridges begin with seen damage from 0 to START_DAMAGE, and a new bridge with none.
  R3. Each year a bridge's seen damage grows at its own rate, from 0 to WEAR a year, and UNMAINTAINED times that where it goes unmaintained.
      From year HIDDEN_FROM, damage inside the steel grows at its own rate, from 0 to HIDDEN a year.
  R4. Funding begins at the upkeep of the first bridges, and covers that many bridges, drawn at random each year. The rest go unmaintained.
  R5. A year is tight with chance TIGHT. In a tight year funding is cut by CUT_SHARE with chance CUT_CHANCE, and the cut stands.
  R6. Each year crews repair the REPAIRS bridges the register shows as weakest. A repair restores what the register shows.
  R7. Inspections are on schedule and the budget balances in every year of every run.
  R8. The options, each in place from the start. A register of the hidden damage adds it to what the register shows. Upkeep charged at
      approval adds a new bridge's upkeep to funding. A recorded vote before a cut, read by an auditor, multiplies CUT_CHANCE by VOTE_EFFECT.
  R9. An option no one holds ends with chance UNHELD_END a year. A held option lasts while its holder stays, a holder moving on with chance
      MOVE_ON a year.
  R10. Within a year: bridges open, options end, a tight year cuts, maintenance is assigned, damage grows, crews repair, and the bridges near
      failure are counted. Every option runs on the same draws, so two options differ only by what an option changes.

Run it with `python compute_city.py`. It writes city.json, and city as PDF and PNG, beside itself. To change a number, edit the block below
and run it again.
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
YEARS = 40  # how long each run lasts
RUNS = 200  # how many runs
START_BRIDGES = 400  # how many bridges the city begins with
NEW_A_YEAR = 4  # how many it opens each year
REPAIRS = 12  # how many bridges crews repair each year
HIDDEN_FROM = 10  # the year damage inside the steel begins
CUT_SHARE = 0.10  # how much of funding a cut takes
CUT_CHANCE = 0.75  # the chance a tight year brings a cut
TIGHT = 0.40  # the chance a year is tight
START_DAMAGE = 0.40  # the first bridges begin with seen damage up to this
WEAR = 0.025  # seen damage grows at up to this a year, on a maintained bridge
UNMAINTAINED = 2.5  # how many times faster on an unmaintained one
HIDDEN = 0.015  # damage inside the steel grows at up to this a year
VOTE_EFFECT = 0.10  # how much of the chance of a cut remains under a recorded vote
UNHELD_END = 0.15  # the chance a year that an option no one holds ends
MOVE_ON = 0.02  # the chance a year that an option's holder moves on

parameters = {name.lower(): value for name, value in globals().items() if name.isupper()}
HERE = Path(__file__).resolve().parent
BLUE, ORANGE, AQUA, YELLOW, RED, GREY, INK = "#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e34948", "#8a8984", "#333333"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})
OPTIONS = {  # each option: register, charge and vote in place, and whether it is held
    "as_it_is": (False, False, False, True),
    "register_unheld": (True, False, False, False),
    "register_held": (True, False, False, True),
    "charge_held": (False, True, False, True),
    "vote_held": (False, False, True, True),
    "all_held": (True, True, True, True),
}


def lasting(in_use, held, draws):
    """R9: whether an option is in place, run by run and year by year."""
    if not in_use:
        return np.zeros(draws.shape, dtype=bool)
    return np.cumprod(draws >= (MOVE_ON if held else UNHELD_END), axis=1).astype(bool)


def run(register, charge, vote, held):
    """R1 to R10: the bridges near failure, run by run and year by year."""
    rng = np.random.default_rng(SEED)  # R10: every option on the same draws
    all_bridges = START_BRIDGES + NEW_A_YEAR * YEARS
    opens = np.concatenate([np.zeros(START_BRIDGES, dtype=int), 1 + np.arange(NEW_A_YEAR * YEARS) // NEW_A_YEAR])  # R1
    every = (RUNS, all_bridges)
    seen, inside = np.zeros(every), np.zeros(every)
    seen[:, :START_BRIDGES] = rng.random((RUNS, START_BRIDGES)) * START_DAMAGE  # R2
    wear, hidden = rng.random(every) * WEAR, rng.random(every) * HIDDEN  # R3
    draws = rng.random((3, RUNS, YEARS))
    has_register, has_charge, has_vote = (lasting(in_use, held, draws[i]) for i, in_use in enumerate((register, charge, vote)))
    funding = np.full(RUNS, float(START_BRIDGES))  # R4
    near = np.zeros((RUNS, YEARS))
    rows = np.arange(RUNS)[:, None]
    for year in range(1, YEARS + 1):
        open_now = opens <= year
        funding += np.where(has_charge[:, year - 1], NEW_A_YEAR, 0.0)  # R8
        tight = rng.random(RUNS) < TIGHT  # R5
        chance = CUT_CHANCE * np.where(has_vote[:, year - 1], VOTE_EFFECT, 1.0)
        funding = np.where(tight & (rng.random(RUNS) < chance), funding * (1 - CUT_SHARE), funding)
        order = np.where(open_now, rng.random(every), 2.0).argsort(axis=1).argsort(axis=1)  # R4: drawn at random among the open bridges
        maintained = open_now & (order < np.floor(funding)[:, None])
        seen += np.where(open_now, wear * np.where(maintained, 1.0, UNMAINTAINED), 0.0)  # R3
        if year >= HIDDEN_FROM:
            inside += np.where(open_now, hidden, 0.0)
        registers_it = has_register[:, year - 1 : year]
        shown = seen + inside * registers_it  # R8
        weakest = np.argsort(np.where(open_now, -shown, np.inf), axis=1, kind="stable")[:, :REPAIRS]  # R6
        seen[rows, weakest] = 0.0
        inside[rows, weakest] *= ~registers_it
        near[:, year - 1] = ((seen + inside >= 1) & open_now).sum(axis=1)
    return near


near = {name: run(*choice) for name, choice in OPTIONS.items()}
curves = {name: found.mean(axis=0).tolist() for name, found in near.items()}
results = {f"near_{name}": curve[-1] for name, curve in curves.items()}
results["near_year_30"] = curves["as_it_is"][29]
gap = near["register_unheld"][:, -1] - near["as_it_is"][:, -1]
shapes = {
    "measures_hold_still": True,  # R7: nothing in the model moves them
    "quiet_for_thirty_years_then_failing": results["near_year_30"] < results["near_as_it_is"] / 10,
    "an_unheld_register_changes_little": abs(gap.mean()) < results["near_as_it_is"] / 10,
    "the_register_held_does_more_than_unheld": results["near_register_held"] < results["near_register_unheld"],
    "options_in_the_order_printed": results["near_as_it_is"] > results["near_charge_held"] > results["near_register_held"]
    > results["near_vote_held"] > results["near_all_held"],
}
output = {**parameters, **results, **shapes, "options": len(OPTIONS), "curves": curves}
(HERE / "city.json").write_text(json.dumps(output, indent=1, sort_keys=True, default=lambda number: number.item()) + "\n", encoding="utf-8", newline="\n")

# The figure: on the left, nothing the city measures moves and the bridges near failure climb late; on the right, the same late years enlarged, by option
ENLARGED_FROM = 28  # the year the right-hand panel begins: a matter of drawing, so not among the parameters
fig, (whole, late) = plt.subplots(1, 2, figsize=(6.27, 4.0), sharey=True, gridspec_kw={"width_ratios": [1, 1.75]})
years = np.arange(1, YEARS + 1)
top = max(curves["as_it_is"])
lines = (("as_it_is", "as it is", RED), ("charge_held", "upkeep charged, held", ORANGE), ("register_held", "register, held", BLUE),
         ("vote_held", "recorded vote, held", YELLOW), ("all_held", "all three, each held", AQUA))
for ax in (whole, late):
    for name, words, colour in lines:
        ax.plot(years, curves[name], color=colour, linewidth=2)
    ax.plot(years, curves["register_unheld"], color=RED, linewidth=1, linestyle="--")
for name, words, colour in lines:
    late.text(YEARS + 0.3, curves[name][-1], f"{words}: {curves[name][-1]:.0f}", va="center")
late.text(YEARS + 0.3, top * 0.9, f"register no one holds: {curves['register_unheld'][-1]:.0f}", va="center")
whole.axvspan(ENLARGED_FROM, YEARS, color=GREY, alpha=0.15, linewidth=0)
whole.plot([HIDDEN_FROM, HIDDEN_FROM], [0, top * 0.6], color=GREY, linewidth=0.7, linestyle=":")
whole.text(HIDDEN_FROM + 0.8, top * 0.6, "damage inside\nthe steel begins", color=GREY, va="top")
whole.text(2, top * 1.0, "Every year of every run:\ninspections on schedule,\nbudget balanced", color=GREY, va="top")
whole.set_title(f"all {YEARS} years", loc="left")
whole.set_xlabel("year")
whole.set_ylabel("bridges near failure")
whole.set_xlim(1, YEARS)
whole.set_xticks([1, 10, 20, 30, 40])
whole.set_ylim(0, top * 1.05)
late.set_title(f"years {ENLARGED_FROM} to {YEARS}, enlarged", loc="left")
late.set_xlabel("year")
late.set_xlim(ENLARGED_FROM, YEARS + 9)  # room for the labels at the lines' ends
late.spines["bottom"].set_bounds(ENLARGED_FROM, YEARS)
late.set_xticks([28, 30, 32, 34, 36, 38, 40])
late.tick_params(axis="y", labelleft=True)
finish(fig, HERE / "city")

# The checks: the shape the text says carries over
for name, holds in shapes.items():
    assert holds, name
