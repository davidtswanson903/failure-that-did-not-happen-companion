"""Rebuilds series.csv from two editions of CRS report R43997: FY2007 to FY2010 in current dollars from the 2017 edition, and FY2011 to FY2020 in current and constant dollars from
the 2021 edition. It needs a network and pdftotext."""

import csv
import pathlib
import re
import subprocess
import tempfile
import urllib.request

HERE = pathlib.Path(__file__).resolve().parent
EDITION_2017 = "https://www.everycrsreport.com/files/20170425_R43997_2d22cc13febc61b786a03be237950dd4ed10ad0d.html"
EDITION_2021 = "https://www.everycrsreport.com/files/2021-11-30_R43997_e9e0adda228777651a9f2e18821dff68ca3677ca.pdf"


def fetched(address):
    request = urllib.request.Request(address, headers={"User-Agent": "Mozilla/5.0"})
    return urllib.request.urlopen(request, timeout=120).read()


html = re.sub(r"<[^>]+>", " ", fetched(EDITION_2017).decode("utf-8", "replace"))
early = re.search(r"Table 1\. Estimated Deferred Maintenance by Agency in Current Dollars,\s+FY2007-FY2016.*?NPS\s+((?:[\d.]+\s+){10})", html, flags=re.S).group(1).split()[:4]
with tempfile.TemporaryDirectory() as folder:
    pdf = pathlib.Path(folder) / "report.pdf"
    pdf.write_bytes(fetched(EDITION_2021))
    subprocess.run(["pdftotext", "-layout", str(pdf), str(pdf.with_suffix(".txt"))], check=True)
    text = pdf.with_suffix(".txt").read_text(encoding="utf-8", errors="replace")
rows = re.findall(r"^NPS\s+((?:[\d.]+a?\s+){10})", text, flags=re.M)
current, constant = [[cell.rstrip("a") for cell in row.split()] for row in rows[:2]]

with (HERE / "series.csv").open("w", newline="", encoding="utf-8") as handle:
    writer = csv.writer(handle, lineterminator="\n")
    writer.writerow(["fiscal_year", "current_billions", "constant_fy2020_billions"])
    for year, value in zip(range(2007, 2011), early):
        writer.writerow([year, value, ""])
    for year, now, real in zip(range(2011, 2021), current, constant):
        writer.writerow([year, now, real])
