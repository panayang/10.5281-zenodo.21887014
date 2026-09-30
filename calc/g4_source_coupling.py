"""G4: what fixes gamma? A linear static response h_mn = a T_mn + b eta_mn T (T = trace), read against the PPN form
   h_00 = -2 Phi, h_ij = -2 gamma Phi delta_ij   (a comparison target, not a premise).
Cases: scalar coupling to the trace (a = 0: the source is the Lorentz-invariant count of content events, the natural
causal-set source); massless gauge-invariant tensor (b = -1/(D-2)); massive Fierz-Pauli (b = -1/(D-1)).
Also: which sources see radiation, and Laue's theorem (a bound static system has integrated T_ij = 0, so every
linear coupling gives a far field proportional to its total energy).
Output: calc/out/g4_source_coupling.txt
"""
import os
import sympy as sp

OUT = os.path.join(os.path.dirname(__file__), "out", "g4_source_coupling.txt")
lines = []


def say(s=""):
    print(s)
    lines.append(s)


a, b, rho, p, eps, D = sp.symbols("a b rho p epsilon D", real=True)


def response(T00, Tii, n):
    """static diagonal source in n spatial dims: T_00, T_ij = Tii delta_ij; eta = diag(-1, 1, ...)."""
    tr = -T00 + n * Tii
    h00 = a * T00 + b * (-1) * tr
    hii = a * Tii + b * tr
    return sp.simplify(h00), sp.simplify(hii)


# dust in n = D - 1 spatial dims
h00, hii = response(rho, 0, D - 1)
gamma = sp.simplify(hii / h00)      # h_ij = gamma h_00 for pure T_00 in the PPN reading
say(f"dust: h_00 = {h00},  h_ii = {hii},  gamma = h_ii / h_00 = {gamma}")
for name, bval, aval in [("scalar (trace) coupling", b, 0), ("massless gauge-invariant tensor", -1 / (D - 2), 1),
                         ("massive Fierz-Pauli tensor", -1 / (D - 1), 1)]:
    g = sp.simplify(gamma.subs({a: aval, b: bval}) if aval == 0 else gamma.subs({b: bval, a: aval}))
    say(f"  {name:34s}: gamma = {sp.simplify(g)}   (D = 4: {sp.simplify(g.subs(D, 4))}; D = 5: {sp.simplify(g.subs(D, 5))})")
say("  light deflection relative to the observed value: (1 + gamma) / 2")

# radiation (unbound, isotropic): T_00 = eps, T_ii = eps / (D - 1), trace 0
h00r, hiir = response(eps, eps / (D - 1), D - 1)
say(f"\nisotropic radiation: h_00 = {sp.simplify(h00r)}, h_ii = {sp.simplify(hiir)}  -> the trace coupling (a = 0) gives nothing:")
say("  radiation neither gravitates nor is deflected under the Lorentz-invariant event-count source")

# Laue: bound static system, integrated T_ij = 0, integrated trace = -E
E = sp.symbols("E", positive=True)
h00b, hiib = response(E, 0, D - 1)
say(f"\nbound static system (Laue: integrated T_ij = 0): far field h_00 = {h00b}, h_ii = {hiib}")
say("  every linear coupling, including the scalar one, gives a far field proportional to the total energy E")
say("  (a box of trapped light gravitates by its energy even in scalar theory); the couplings differ only for UNBOUND massless content")
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
