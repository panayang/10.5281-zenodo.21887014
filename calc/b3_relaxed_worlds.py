"""B3: relax "worlds are closed under the past" (D19's open option) and see what becomes possible.

Three events a, b, c; worlds {a,b}, {b,c}, {a,c} (pairwise coexistence, no triple: the hollow triangle).
Within each world the relation is a fact (M4) and must be a partial order on that pair: a<b, b<a, or a||b.
With past-closed worlds a comparable pair forces the triple to coexist (docs/law.md section 6), so every
configuration glues. Without past-closure all 27 assignments are locally admissible; count those that do not
extend to a partial order on {a, b, c}, and sort them.
Output: calc/out/b3_relaxed_worlds.txt
"""
import itertools
import os

OUT = os.path.join(os.path.dirname(__file__), "out", "b3_relaxed_worlds.txt")
E = ["a", "b", "c"]
pairs = [("a", "b"), ("b", "c"), ("a", "c")]


def rel_sets():
    for choice in itertools.product(["<", ">", "|"], repeat=3):
        R = set()
        for (x, y), c in zip(pairs, choice):
            if c == "<":
                R.add((x, y))
            elif c == ">":
                R.add((y, x))
        yield choice, R


def is_partial_order(R):
    if any((y, x) in R for (x, y) in R):
        return False
    for (x, y) in R:
        for (y2, z) in R:
            if y == y2 and x != z and (x, z) not in R:
                return False
    return True


def has_cycle(R):
    return {("a", "b"), ("b", "c"), ("c", "a")} <= R or {("b", "a"), ("c", "b"), ("a", "c")} <= R


lines = []
total = glue = cyc = gap = 0
for choice, R in rel_sets():
    total += 1
    if is_partial_order(R):
        glue += 1
    elif has_cycle(R):
        cyc += 1
    else:
        gap += 1
lines.append(f"hollow triangle, worlds not closed under the past: {total} locally admissible assignments")
lines.append(f"  extend to a global partial order: {glue}")
lines.append(f"  causal cycles (a<b<c<a or reverse): {cyc}")
lines.append(f"  transitivity gaps (x<y<z but x||z): {gap}")
lines.append("with past-closed worlds only the gluing ones can occur (a comparable pair forces the triple to coexist)")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
