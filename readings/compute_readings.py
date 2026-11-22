"""The figure of the readings of the Element's Section 10.6, a panel for each, drawn from what each reading's own script wrote. It computes nothing of its own, and shares its finish
with the figures of the computations. It writes readings.pdf and readings.png beside itself."""

import json
import pathlib
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "element-figures"))
from figure_style import finish, fonts

BLUE, ORANGE, GREY, INK = "#2a78d6", "#ec6a33", "#8a8a85", "#2b2b2b"
plt.rcParams.update({**fonts, "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": GREY, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK})


def loaded(name):
    return json.loads((HERE / name / f"{name}.json").read_text(encoding="utf-8"))


reserve, backlog, permits = loaded("reserve"), loaded("backlog"), loaded("permits")
fig, ((kept, upkeep), (out, slow)) = plt.subplots(2, 2, figsize=(6.27, 5.6))

# The reserve's stock against the obligation, in one unit
kept.plot(reserve["years"], reserve["stock"], color=BLUE, linewidth=2)
kept.plot(reserve["years"], reserve["obligation"], color=GREY, linewidth=1.5, linestyle="--")
kept.text(1979, 760, "Stock", color=BLUE, va="bottom")
kept.text(2000, 1150, "90 days of net imports", color=GREY, ha="center", va="bottom")
kept.set_ylim(0, 1300)
kept.set_xticks([1977, 1990, 2005, 2015, 2025], ["1977", "1990", "2005", "2015", "2025"])
kept.set_title("Strategic Petroleum Reserve", loc="left")
kept.set_xlabel("Year")
kept.set_ylabel("Millions of barrels")

# The backlog, in current dollars and in the report's FY2020 dollars
upkeep.plot(backlog["years"], backlog["current"], color=BLUE, linewidth=2)
upkeep.plot(backlog["real_years"], backlog["real"], color=ORANGE, linewidth=2)
upkeep.text(2012, backlog["current"][5] - 1.2, "Current dollars", color=BLUE, va="top")
upkeep.text(2011.2, backlog["real"][0] + 0.45, "FY2020 dollars", color=ORANGE, va="bottom")
upkeep.set_ylim(0, 16)
upkeep.set_xticks([2007, 2011, 2015, 2020], ["2007", "2011", "2015", "2020"])
upkeep.set_title("National Park Service backlog", loc="left")
upkeep.set_xlabel("Fiscal year")
upkeep.set_ylabel("Billions of dollars")

# Permits: the share that end withdrawn or cancelled, and the median time to close, by homes proposed
places = range(len(permits["groups"]))
names = [group["group"] for group in permits["groups"]]
out.errorbar(places, [group["share"] for group in permits["groups"]], yerr=[group["error"] for group in permits["groups"]], color=BLUE, marker="o", markersize=5, linewidth=1.5, capsize=2)
out.set_xticks(list(places), names, rotation=45)
out.set_ylim(0, None)
out.set_title("San Francisco: withdrawn or cancelled", loc="left")
out.set_xlabel("Homes proposed")
out.set_ylabel("Per cent of records that ended")
slow.plot(places, [group["median_days"] for group in permits["groups"]], color=ORANGE, marker="o", markersize=5, linewidth=1.5)
slow.set_xticks(list(places), names, rotation=45)
slow.set_ylim(0, None)
slow.set_title("San Francisco: time to close", loc="left")
slow.set_xlabel("Homes proposed")
slow.set_ylabel("Median days")

finish(fig, HERE / "readings")
