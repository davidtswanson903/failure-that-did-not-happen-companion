"""Rebuilds series.csv from San Francisco's open record of planning projects, every record that proposes homes. It needs a network. The record is updated daily, so a new fetch can
differ from the series kept here, whose retrieval date source.md gives."""

import csv
import json
import pathlib
import urllib.parse
import urllib.request

HERE = pathlib.Path(__file__).resolve().parent
FIELDS = ("record_id", "record_status", "open_date", "close_date", "number_of_units_prop")
query = urllib.parse.urlencode({"$select": ",".join(FIELDS), "$where": "number_of_units_prop > 0", "$order": "record_id", "$limit": "100000"})
request = urllib.request.Request("https://data.sf.gov/resource/qvu5-m3a2.json?" + query, headers={"User-Agent": "Mozilla/5.0"})
rows = json.load(urllib.request.urlopen(request, timeout=300))

with (HERE / "series.csv").open("w", newline="", encoding="utf-8") as handle:
    writer = csv.DictWriter(handle, FIELDS, lineterminator="\n")
    writer.writeheader()
    for row in rows:
        writer.writerow({field: row.get(field, "")[:10] if field.endswith("date") else row.get(field, "") for field in FIELDS})
