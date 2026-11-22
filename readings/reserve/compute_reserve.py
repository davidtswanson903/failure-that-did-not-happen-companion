"""What the reserve's series tells: whether the Strategic Petroleum Reserve is kept while an obligation reaches it, and spent down once none does.

The rules:
R1. The stock is the reserve's at the end of each year, in millions of barrels.
R2. The obligation is 90 days of the year's net imports of crude oil and petroleum products, in the same units, and none in a year of net exports. The agreement counts the previous year's net imports, and this uses the same year's, since the shape does not turn on it.
R3. The stock clears the obligation from the first year after which it never again falls below it.
R4. The stock's peak is its highest year-end figure.

It fits nothing and estimates nothing. It writes reserve.json beside itself."""

import csv
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
DAYS = 90

with (HERE / "series.csv").open(encoding="utf-8", newline="") as handle:
    rows = list(csv.DictReader(handle))
years = [int(row["year"]) for row in rows]
stock = [int(row["stock_thousand_barrels"]) / 1000 for row in rows]
net = [int(row["net_imports_thousand_barrels_a_day"]) for row in rows]
obligation = [max(0, DAYS * rate / 1000) for rate in net]

clears = next(year for at, year in enumerate(years) if all(s >= o for s, o in zip(stock[at:], obligation[at:])))
exporter = next(year for year, rate in zip(years, net) if rate < 0)
peak = max(stock)
results = {
    "first_year": years[0], "stock_first": stock[0], "stock_peak": peak, "peak_year": years[stock.index(peak)], "stock_2016": stock[years.index(2016)],
    "last_year": years[-1], "stock_last": stock[-1], "clears_from": clears, "net_exporter_from": exporter,
    "years": years, "stock": stock, "obligation": obligation,
}
(HERE / "reserve.json").write_text(json.dumps(results, indent=1, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

# The checks: exact facts of the rules
assert all(year + 1 == later for year, later in zip(years, years[1:]))
assert all(o == 0 for year, o in zip(years, obligation) if net[years.index(year)] < 0)
