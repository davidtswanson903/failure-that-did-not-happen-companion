"""What the permit series tells: whether a project's chance of ending withdrawn or cancelled, and the time it takes to close, rise with the homes it proposes.

The rules:
R1. A record counts if it proposes homes and was opened from 2015 to 2022. Most records opened earlier came from older systems, and many opened later have not yet ended.
R2. Its size is the homes it proposes, in the groups 1, 2 to 4, 5 to 9, 10 to 19, 20 to 49, 50 to 99, 100 to 199, and 200 or more.
R3. A record has ended unless its status says it is open, under review, on hold, submitted, accepted or pending.
R4. It is out if its status says withdrawn or cancelled. A share is of the records that have ended, with its binomial standard error. A plain "Closed" says nothing of how, and is not read as approved.
R5. Time to close is the median of days from open to close, among records that have ended, have a close date and are not out.

It fits nothing and estimates nothing. It writes permits.json beside itself."""

import csv
import datetime
import json
import math
import pathlib
import statistics

HERE = pathlib.Path(__file__).resolve().parent
FIRST, LAST = 2015, 2022
GROUPS = ((1, 1), (2, 4), (5, 9), (10, 19), (20, 49), (50, 99), (100, 199), (200, math.inf))
OUT = {"Closed - Withdrawn", "Withdrawn", "Project Withdrawn", "Closed - Cancelled", "Cancelled"}
OPEN = {"Open", "Under Review", "On Hold", "Submitted", "Accepted", "Pending Review", "Pending", "Application Intake - Pending", "Application Accepted", "Appeal Pending"}

with (HERE / "series.csv").open(encoding="utf-8", newline="") as handle:
    rows = [row for row in csv.DictReader(handle) if FIRST <= int(row["open_date"][:4]) <= LAST]


def days(row):
    return (datetime.date.fromisoformat(row["close_date"]) - datetime.date.fromisoformat(row["open_date"])).days


found = []
for low, high in GROUPS:
    chosen = [row for row in rows if low <= float(row["number_of_units_prop"]) <= high]
    ended = [row for row in chosen if row["record_status"] not in OPEN]
    out = [row for row in ended if row["record_status"] in OUT]
    times = [days(row) for row in ended if row["close_date"] and row["record_status"] not in OUT and days(row) >= 0]
    share = len(out) / len(ended)
    found.append({"group": f"{low}" if low == high else (f"{low}+" if high == math.inf else f"{low}-{high}"), "records": len(chosen), "ended": len(ended), "out": len(out),
                  "share": 100 * share, "error": 100 * math.sqrt(share * (1 - share) / len(ended)), "median_days": statistics.median(times), "timed": len(times)})
ended_all = sum(group["ended"] for group in found)
plain = sum(1 for row in rows if row["record_status"] == "Closed")
results = {
    "first": FIRST, "last": LAST, "records": len(rows), "ended": ended_all, "plain_closed": 100 * plain / ended_all,
    "share_single": found[0]["share"], "error_single": found[0]["error"], "share_largest": found[-1]["share"], "error_largest": found[-1]["error"], "ended_largest": found[-1]["ended"],
    "days_single": found[0]["median_days"], "days_largest": found[-1]["median_days"], "groups": found,
}
(HERE / "permits.json").write_text(json.dumps(results, indent=1, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

# The checks: exact facts of the rules
assert sum(group["records"] for group in found) == len(rows)
assert all(group["out"] <= group["ended"] <= group["records"] for group in found)
