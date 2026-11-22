# The Failure That Did Not Happen: Mathematical Companion

## What this is

The mathematics, proofs and computations behind *The Failure That Did Not Happen*. It can be read without them, and they can be checked without it.

**Read the paper:** [*The Failure That Did Not Happen: Mathematical Companion*](paper/companion.pdf) (PDF). It takes a reader from any claim of the book to the mathematics behind it. Each of the book's claims and definitions has an entry under the book's own number and title, which reads the claim's words as formal objects, states and proves what follows, and names the Lean declarations that check the proof. The two models the book glosses, Model S and Model A, have entries of their own, and a closing map lists every claim with its standing.

## What is here

- `paper/companion.pdf`: the paper, which states the mathematics claim by claim under the book's numbers.
- `lean/`: the Lean proofs of what the paper proves.
- `figures/`: the scripts that compute every figure and the two models of the book's Appendix B, with the numbers and figures they write.
- `notebook/models.ipynb`: runs the two models, Model S and Model A, from `compute_sieve_chain.py` and `compute_adequacy.py`, with their rates and registers set by the reader.
- `binder/`: what Binder needs to run the notebook in a browser.

The notebook runs in a browser with nothing installed: open it [in Colab](https://colab.research.google.com/github/davidtswanson903/failure-that-did-not-happen-companion/blob/main/notebook/models.ipynb) or [in Binder](https://mybinder.org/v2/gh/davidtswanson903/failure-that-did-not-happen-companion/main?labpath=notebook%2Fmodels.ipynb). In Colab its first cell fetches the scripts it draws from.

## How to rebuild

You need Python 3.14 with the packages in `requirements.txt` (`pip install -r requirements.txt`), [elan](https://github.com/leanprover/elan), and a TeX distribution with latexmk. Then:

```
make
```

That rebuilds the figures, then the proofs, then the paper. `make figures`, `make lean` and `make paper` each rebuild one part, and `make sieve` rebuilds one script's files, by its name.

## Which script makes which figure

| Book | Script | Files |
| --- | --- | --- |
| Figure 2.1 | [`compute_toy.py`](figures/compute_toy.py) | [`toy_chain.pdf`](figures/toy_chain.pdf), [`toy_chain.png`](figures/toy_chain.png) |
| Figure 2.2 | [`compute_toy.py`](figures/compute_toy.py) | [`toy_between.pdf`](figures/toy_between.pdf), [`toy_between.png`](figures/toy_between.png) |
| Figure 2.3 | [`compute_toy.py`](figures/compute_toy.py) | [`toy_price.pdf`](figures/toy_price.pdf), [`toy_price.png`](figures/toy_price.png) |
| Figure 3.1 | [`compute_sieve.py`](figures/compute_sieve.py) | [`sieve.pdf`](figures/sieve.pdf), [`sieve.png`](figures/sieve.png) |
| Figure 3.2 | [`compute_purpose.py`](figures/compute_purpose.py) | [`purpose.pdf`](figures/purpose.pdf), [`purpose.png`](figures/purpose.png) |
| Figure 3.3 | [`compute_drift.py`](figures/compute_drift.py) | [`drift.pdf`](figures/drift.pdf), [`drift.png`](figures/drift.png) |
| Figure 4.1 | [`compute_causes.py`](figures/compute_causes.py) | [`causes.pdf`](figures/causes.pdf), [`causes.png`](figures/causes.png) |
| Figure 5.1 | [`compute_reporting.py`](figures/compute_reporting.py) | [`reporting.pdf`](figures/reporting.pdf), [`reporting.png`](figures/reporting.png) |
| Figure 5.2 | [`compute_stack.py`](figures/compute_stack.py) | [`stack.pdf`](figures/stack.pdf), [`stack.png`](figures/stack.png) |
| Figure 5.3 | [`compute_layers.py`](figures/compute_layers.py) | [`layers.pdf`](figures/layers.pdf), [`layers.png`](figures/layers.png) |
| Figure 7.1 | [`compute_orders.py`](figures/compute_orders.py) | [`orders.pdf`](figures/orders.pdf), [`orders.png`](figures/orders.png) |
| Figure 8.1 | [`compute_exact.py`](figures/compute_exact.py) | [`exact.pdf`](figures/exact.pdf), [`exact.png`](figures/exact.png) |
| Figure 9.1 | [`compute_city.py`](figures/compute_city.py) | [`city.pdf`](figures/city.pdf), [`city.png`](figures/city.png) |
| The table of what law set out to secure | [`compute_law.py`](figures/compute_law.py) | [`law_table.md`](figures/law_table.md) |
| Figure 10.1 | [`compute_readings.py`](readings/compute_readings.py) | [`readings.pdf`](readings/readings.pdf), [`readings.png`](readings/readings.png) |
| Figure 12.1 | [`compute_anxious.py`](figures/compute_anxious.py) | [`anxious.pdf`](figures/anxious.pdf), [`anxious.png`](figures/anxious.png) |

## What each computation does

| Figure, table or model | Script | Claims | Rules | Size | Checked by assertion |
| --- | --- | --- | --- | --- | --- |
| 2.1–2.3 | [`compute_toy.py`](figures/compute_toy.py) | 3, 4, 9, 11 | registers as sets of facts kept | 8 and 16 states | balance; no recovery along the chain |
| 3.1 | [`compute_sieve.py`](figures/compute_sieve.py) | 10, 13 | capacities cut in tight years unless held; holders lapse | 2,000 capacities, 30 years, 200 runs | an unheld capacity worth nine times a held one is cut first |
| 3.2 | [`compute_purpose.py`](figures/compute_purpose.py) | 14, 15 | damage the register drops; a correction that lasts while held | 400 bridges, 40 years, 300 runs | — |
| 3.3 | [`compute_drift.py`](figures/compute_drift.py) | 11, 16 | kept facts lapse free; facts added only when paid for | 64 states, 3,000 changes, 300 runs a budget | balance on every change; no shrinking unpaid |
| 4.1 | [`compute_causes.py`](figures/compute_causes.py) | 19, 20 | four causes open routes to a cut; a held lapse closes them | 4,000 cities, 20 years, four scenarios | — |
| Table 5.1 | [`compute_law.py`](figures/compute_law.py) | 10 | the six things law set out to secure, coded from their sources | 6 rows | whether a party holds the lapse sorts all five |
| 5.1 | [`compute_reporting.py`](figures/compute_reporting.py) | 21, 24 | effort in proportion to the square of the loss held on each use | 1,000 offices, 8 years | the three groups sort as the claim says |
| 5.2 | [`compute_stack.py`](figures/compute_stack.py) | 5, 9, 25 | each review vetoes some proposals raising its concern; none registers homes | 256 projects exactly; 20,000 proposals | joint prohibition, exactly |
| 5.3 | [`compute_layers.py`](figures/compute_layers.py) | 25 | as 5.2, with reviews added one at a time, up to twelve | 20,000 proposals | each review added forbids no less |
| 7.1 | [`compute_orders.py`](figures/compute_orders.py) | 30–33 | failures bring reforms; unheld reforms cut as attention fades; what counts changes in year 40 | 600 arrangements, 80 years after a 30-year start, 40 runs | — |
| 8.1 | [`compute_exact.py`](figures/compute_exact.py) | 9, 11, 35 | every pair of registers on five states; every rule; every refinement | 2,704 arrangements | the between is exactly what no rule separates; no remedy costs less than it carries |
| 9.1 | [`compute_city.py`](figures/compute_city.py) | 14, 15, 32 | the city's parties; maintenance cut in tight years; damage inside the steel from year 10 | 400 bridges, 40 years, 200 runs, six options | — |
| 12.1 | [`compute_anxious.py`](figures/compute_anxious.py) | 39, 40 | a world that moves; acting priced at what being wrong weighs; finding out only by acting | 1,000 arrangements, 100 years, three cases at eleven weights | the heavier the weight the further out of step; learning from its own acts further out than being told; holding not finding out brings it back |
| Model S | [`compute_sieve_chain.py`](figures/compute_sieve_chain.py) | 6, 10, 13 | capacities held, unheld or cut, with constant yearly chances; worth through a registered signal | three states, 100 years exactly; 200,000 simulated capacities | the closed forms against the exact recursion and a simulation; the endpoints the book prints |
| Model A | [`compute_adequacy.py`](figures/compute_adequacy.py) | 6, 9, 11, 14, 15 | adequacy for a purpose; a correction kept, held or cut as in Model S | 4,000 random instances of up to six states; 40 years | A.1 to A.7; the bridge; the closed forms against their sums and a simulation |

Each script also writes its numbers, to the `.json` file of its name, and states its rules at its head. `figure_style.py` finishes every figure the same way: labels at 9pt with an initial capital, fonts embedded.

The readings of the book's Section 10.6, unlike the computations, read public data. They are in `readings/`, one folder to a reading, each with its series, its `source.md` and its script, and `make readings` runs them from the committed series with no network.

## Licence and citation

The scripts and the Lean are under Apache-2.0 (`LICENSE`). The paper and the figures are under CC BY 4.0 (`LICENSE-text`). To cite this deposit, use `CITATION.cff`.
