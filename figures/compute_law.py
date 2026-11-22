"""The six things law set out to secure, coded from their sources, with each account's verdict.

Nothing here is drawn or tuned: the coding is data, written below with the sources each row rests on, so the script reads no file.

The rules
  R1. A thing law set out to secure is a capacity, whose product is a prevented failure, or an outcome.
  R2. Its protections are those it was given of the four lawyers name: priority, durability, convertibility into state money, universality.
  R3. Its holder is the party whose loss follows its lapse, if any. Who bears the loss does not make a holder unless the loss reaches the
      party that keeps the capacity going.
  R4. Whether it is kept going is read from the record, row by row.
  R5. A reading sorts the capacities when its verdict agrees with whether each is kept going, on every one.
  R6. The readings tried: how much the law gave (the more protections, the more it is kept); where the beneficiaries stand (scattered
      beneficiaries go unserved); and whether some party holds the lapse.

Run it with `python compute_law.py`. It writes law.json and law_table.md beside itself.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROTECTIONS = ("priority", "durability", "convertibility", "universality")

# Each row, with what the draft's table prints in its columns (`given`, `holder`, `kept_words`) and the coding the readings use.
# `protections` counts what the entry states it was given: "at least" counts what the sources show, as the table prints.
ROWS = [
    {   # Sources: First National Bank of Bellaire v. Comptroller of the Currency 1983; International Lending Supervision Act 1983;
        # OCC 2011; Banking Act 1933
        "name": "A bank's capital buffer (United States)", "kind": "capacity", "protections": ["priority"], "scattered": True,
        "given": "at least priority", "holder": "the deposit insurer, whose fund pays when a bank fails", "held": True,
        "kept": True, "kept_words": "yes: enforced as an order since 1983",
    },
    {   # Sources: 14 C.F.R. 25.1309; FAA 2024
        "name": "An airworthiness standard (United States)", "kind": "outcome", "protections": [], "scattered": True,
        "given": "a target for an outcome", "holder": "stands apart", "held": None,
        "kept": None, "kept_words": "—",
    },
    {   # Sources: 14 C.F.R. 91.25; 49 U.S.C. 40123; FAA 2021
        "name": "An immunity for reporting error (United States)", "kind": "capacity", "protections": [], "scattered": False,
        "given": "none: a remedy taken from the state", "holder": "the reporter, whose certificate is their livelihood", "held": True,
        "kept": True, "kept_words": "yes: reports flow",
    },
    {   # Sources: Banking Act 1933; Banking Act 1935; Calomiris and White 1994
        "name": "A guarantee of deposits (United States)", "kind": "capacity", "protections": ["durability", "convertibility"], "scattered": True,
        "given": "at least durability, convertibility", "holder": "the depositor", "held": True,
        "kept": True, "kept_words": "yes: no further act needed since 1935",
    },
    {   # Sources: Charitable Uses Act 1601; Charities Act 2011, ss. 3-4; Charity Commission n.d.
        "name": "A trust for repairing sea-banks (England)", "kind": "capacity", "protections": list(PROTECTIONS), "scattered": True,
        "given": "all four", "holder": "no one: the landowner bears the loss and has no claim on the trust; the office that has the claim loses nothing",
        "held": False, "kept": False, "kept_words": "no: its protection reaches its terms, not its funds",
    },
    {   # Sources: Cal v. Attorney General of Belize 2007; Maya Leaders Alliance v. Attorney General of Belize 2015; Greater Belize Media 2025;
        # Love FM 2026
        "name": "A constitutional right to customary land (Belize)", "kind": "capacity", "protections": ["priority", "durability", "universality"], "scattered": False,
        "given": "priority, durability, universality",
        "holder": "no one whose loss reaches the state's budget: the villages bear the loss, and winning in court reached the terms of the order, not the budget",
        "held": False, "kept": False, "kept_words": "no: supervision ended; the codifying law not passed",
    },
]
COLUMNS = ("What law set out to secure", "Protections given", "Who holds its lapse", "Kept going?")
PROTECTIONS_NAMED = len(PROTECTIONS)

capacities = [row for row in ROWS if row["kind"] == "capacity"]  # R1

# R5, R6: the first two readings fail, and the third sorts every capacity
given_most_kept = max(capacities, key=lambda row: len(row["protections"]))
given_least_kept = min(capacities, key=lambda row: len(row["protections"]))
scattered_served = [row["name"] for row in capacities if row["scattered"] and row["kept"]]
concentrated_lapsed = [row["name"] for row in capacities if not row["scattered"] and not row["kept"]]
results = {
    "rows": len(ROWS), "capacities": len(capacities), "outcomes": len(ROWS) - len(capacities), "protections_named": PROTECTIONS_NAMED,
    "protections_do_not_sort": not given_most_kept["kept"] and given_least_kept["kept"],
    "beneficiaries_do_not_sort": bool(scattered_served) and bool(concentrated_lapsed),
    "holder_sorts_all_five": all(row["held"] == row["kept"] for row in capacities),
    "table": [[row["name"], row["given"], row["holder"], row["kept_words"]] for row in ROWS],
}
(HERE / "law.json").write_text(json.dumps(results, indent=1, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")

lines = ["| " + " | ".join(COLUMNS) + " |", "| --- | --- | --- | --- |"]
lines += ["| " + " | ".join(row) + " |" for row in results["table"]]
(HERE / "law_table.md").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")

# The checks: what the text says of the table
assert results["rows"] == 6 and results["capacities"] == 5 and results["outcomes"] == 1
assert results["protections_do_not_sort"], "the trust was given all four and is not kept; the immunity was given none and is"
assert results["beneficiaries_do_not_sort"], "where the beneficiaries stand does not sort the rows"
assert results["holder_sorts_all_five"], "whether some party holds the lapse sorts all five"
