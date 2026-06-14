#!/usr/bin/env python3
"""Summarize the cells (disjuncts) a lazy run discovers, from a liastar-ext
trace. Used to establish 'cell discovery is not the bottleneck on the hard
sat instance': it shows how many *distinct* cells were found and how big the
Hilbert bases are.

Produce the trace first, e.g.:
    build/bin/cvc5 -q -t liastar-ext <bench>.smt2 > trace.log 2>&1
Then:
    analyze_cells.py trace.log
"""
import re, sys
from collections import Counter

log = open(sys.argv[1], errors='replace').read()

# discovered cells (printed as "disjunct: (and ...)" or with let-bindings)
cells = [c for c in re.findall(r'^disjunct: (\(.*)$', log, flags=re.M) if '(and' in c]
print(f"rounds (disjuncts read):      {len(cells)}")
print(f"distinct cells:               {len(set(cells))}")
print(f"cell sizes (tokens) min/med/max: ", end="")
sz = sorted(len(c.split()) for c in cells)
print(f"{sz[0]}/{sz[len(sz)//2]}/{sz[-1]}" if sz else "n/a")

# Hilbert-basis sizes: count numeric rows in each "Hilbert basis:" block
sizes = []
for chunk in log.split('Hilbert basis:')[1:]:
    body = chunk.split('Module generators:')[0]
    sizes.append(sum(1 for l in body.splitlines() if re.match(r'^[\d\s-]+$', l) and l.strip()))
if sizes:
    sizes.sort()
    print(f"Hilbert basis sizes min/med/max/total: "
          f"{sizes[0]}/{sizes[len(sizes)//2]}/{sizes[-1]}/{sum(sizes)}")
