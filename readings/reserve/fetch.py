"""Rebuilds series.csv from the Energy Information Administration's two annual tables, the Strategic Petroleum Reserve's stock at the end of each year and net imports of crude oil and
petroleum products. It needs a network. A later fetch adds years and can revise them."""

import csv
import pathlib
import re
import urllib.request

HERE = pathlib.Path(__file__).resolve().parent
STOCK = "https://www.eia.gov/dnav/pet/hist/LeafHandler.ashx?n=PET&s=MCSSTUS1&f=A"
NET = "https://www.eia.gov/dnav/pet/hist/LeafHandler.ashx?n=PET&s=MTTNTUS2&f=A"


def table(address):
    """The table's years and figures, read from its decade rows: a blank cell before a series begins, and after it ends, is no year."""
    request = urllib.request.Request(address, headers={"User-Agent": "Mozilla/5.0"})
    html = urllib.request.urlopen(request, timeout=120).read().decode("utf-8", "replace")
    found = {}
    for row in re.findall(r"<tr[^>]*>(.*?)</tr>", html, flags=re.S | re.I):
        cells = [re.sub(r"<[^>]+>|&nbsp;", "", cell).strip() for cell in re.findall(r"<td[^>]*>(.*?)</td>", row, flags=re.S | re.I)]
        if cells and re.fullmatch(r"\d{4}'s", cells[0]):
            for offset, cell in enumerate(cells[1:11]):
                if re.fullmatch(r"-?[\d,]+", cell):
                    found[int(cells[0][:4]) + offset] = int(cell.replace(",", ""))
    return found


stock, net = table(STOCK), table(NET)
with (HERE / "series.csv").open("w", newline="", encoding="utf-8") as handle:
    writer = csv.writer(handle, lineterminator="\n")
    writer.writerow(["year", "stock_thousand_barrels", "net_imports_thousand_barrels_a_day"])
    for year in sorted(stock):
        writer.writerow([year, stock[year], net[year]])
