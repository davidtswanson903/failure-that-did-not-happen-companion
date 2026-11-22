# make               figures, then lean, then paper
# make figures       rebuild every figure and number file
# make readings      rebuild the readings of the Element's Section 10.6 from their committed series
# make fetch         refresh those series; needs a network, and is never part of the default build
# make sieve         rebuild one script's, by its name: toy, sieve, purpose, drift, causes, reporting, stack, layers, orders, exact, city, law, anxious, sieve_chain, adequacy
# make lean          build the proofs
# make paper         build paper/companion.pdf; an undefined citation or reference fails the build
PYTHON ?= python
SCRIPTS := toy sieve purpose drift causes reporting stack layers orders exact city law anxious sieve_chain adequacy

.PHONY: all figures readings fetch lean paper $(SCRIPTS)

all: figures readings lean paper

figures: $(SCRIPTS)

$(SCRIPTS):
	$(PYTHON) element-figures/compute_$@.py

readings:
	$(PYTHON) readings/reserve/compute_reserve.py
	$(PYTHON) readings/backlog/compute_backlog.py
	$(PYTHON) readings/permits/compute_permits.py
	$(PYTHON) readings/compute_readings.py

fetch:
	$(PYTHON) readings/reserve/fetch.py
	$(PYTHON) readings/backlog/fetch.py
	$(PYTHON) readings/permits/fetch.py

lean:
	cd lean && lake exe cache get && lake build

paper:
	$(PYTHON) paper/numbers.py
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error -quiet companion.tex
	cd paper && ! grep -E "(Citation|Reference) .* undefined|undefined references|undefined citations" companion.log
	cd paper && latexmk -c companion.tex
