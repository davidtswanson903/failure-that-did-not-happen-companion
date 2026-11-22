"""What the backlog series tells: whether the National Park Service's deferred maintenance shrinks in the years before anything was made to hold it.

The rules:
R1. The series stops at FY2020. From FY2021 the fund made for the backlog pays in, and the method of estimating changes in each of FY2021, FY2022 and FY2023.
R2. Current dollars run from FY2007. Constant dollars run from FY2011, in the FY2020 dollars the report gives, and no other deflator is used.
R3. It has not shrunk over the years as a whole if its last figure stands above its first, in both measures. A stretch of falling is a run of years in which constant dollars fall from their first year to their lowest.

It fits nothing and estimates nothing. It writes backlog.json beside itself."""

import csv
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent

with (HERE / "series.csv").open(encoding="utf-8", newline="") as handle:
    rows = list(csv.DictReader(handle))
years = [int(row["fiscal_year"]) for row in rows]
current = [float(row["current_billions"]) for row in rows]
real_years = [int(row["fiscal_year"]) for row in rows if row["constant_fy2020_billions"]]
real = [float(row["constant_fy2020_billions"]) for row in rows if row["constant_fy2020_billions"]]
lowest = min(real)
lowest_year = real_years[real.index(lowest)]

results = {
    "first_year": years[0], "last_year": years[-1], "current_first": current[0], "current_last": current[-1],
    "real_first_year": real_years[0], "real_first": real[0], "real_last": real[-1], "real_lowest": lowest, "real_lowest_year": lowest_year,
    "real_fall": 100 * (real[0] - lowest) / real[0], "real_rise": 100 * (real[-1] - real[0]) / real[0],
    "years": years, "current": current, "real_years": real_years, "real": real,
}
(HERE / "backlog.json").write_text(json.dumps(results, indent=1, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

# The checks: exact facts of the rules
assert years == list(range(2007, 2021)) and real_years == list(range(2011, 2021))
assert current[-1] == real[-1], "in FY2020 current and FY2020 dollars are one"
