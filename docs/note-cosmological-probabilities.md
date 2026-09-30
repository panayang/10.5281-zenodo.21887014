# When do two observers agree on cosmological frequencies? (standalone note, draft)

> Written for cosmologists working on the measure problem, without the vocabulary of the rest of this repository.
> Status: draft; statements marked "Proposition" have one-paragraph proofs; numerical checks are in `calc/m1_foelner_frw.py`, `calc/m2_converse.py`.

## Setting

Each observer (a timelike worldline i) has at proper time t a **past** P_i(t): all events in the causal past of its point at t.
Frequencies are defined by exhausting the past: the fraction of events of type A among the events in P_i(t), as t → ∞. No time slicing is chosen.
Two observers i and j are linked by light signals. Let **W(t)** be the radar round-trip time from i to j and back, measured by i for a signal sent at i's time t,
and **ρ(t) = W(t)/t**.

## Results

**Proposition 1 (agreement).** If the past volume of i grows regularly, V_i(t + u)/V_i(t) → 1 whenever u = o(t) (true for all power-law FRW and for de Sitter,
whose observer pasts grow only linearly in t), and ρ(t) → 0, then for the matched time s = time at which j first sees i's event at t,
|P_i(t) Δ P_j(s)| / |P_i(t)| → 0. Hence both observers obtain the same limiting frequency for every event type with bounded density.

*Proof.* Pasts are causally closed, so P_i(t) ⊂ P_j(s) ⊂ P_i(t + W(t)); the symmetric difference lies in P_i(t + W) \ P_i(t). ∎

**Proposition 2 (converse).** Let r₁ = lim s/t and r₂ be the analogous one-way ratio from j back to i, so that 1 + ρ → r₁r₂.
Counting the events on j's worldline per event on i's worldline gives 1/r₂ along i's pasts and r₁ along j's pasts.
So the two observers agree on this frequency iff r₁r₂ = 1 iff ρ → 0.

**Consequences in FRW (a ∝ t^p).** For comoving observers ρ → 0 iff p < 1 (strict deceleration). At p = 1 (coasting, flat or Milne) there is **no event horizon, yet ρ stays constant and the observers disagree**:
absence of horizons is necessary but not sufficient. For p > 1 and de Sitter, ρ = ∞ beyond the horizon. Exhaustion by pasts has no youngness paradox in any of these cases;
the youngness paradox is a property of global-time cutoffs.

## A classification of cosmological frequency questions

| Class | Question | Status |
|---|---|---|
| C1 | a count within one observer's past | always well defined |
| C2 | the limit along one observer's past | well defined iff the frequency changes only finitely often at every precision (otherwise no fact) |
| C3 | agreement between observers | for all event types iff ρ → 0 between them (Props. 1–2) |
| C4 | a fraction over all observers, across horizons | defined only if the symmetries of the theory act on the branch types with a unique invariant probability; countably many symmetric branches, or tree-like branching, admit none |

- A global-time cutoff is a choice of slicing; the disagreement between cutoffs on C4 questions is forced, not a technical defect.
- The stationary measure's good behaviour is naturally read as answering a C2 question (the long-run frequency of vacua along one worldline, an ergodic Markov chain).
- Olum's no-go theorem is the failure of axioms that presuppose a global answer to C4 questions.

## Relation to existing work

Cutoff dependence and reordering dependence (Winitzki; Guth–Vanchurin; Linde–Noorbala), local measures and the causal patch (Bousso), the local–global duality with initial ensembles,
and Olum's no-go theorem are known. What seems new here is the intrinsic criterion ρ → 0 for when the ensemble of observers does not matter, and the observation that it is
exactly the condition under which the observers' relative clock rates are fixed by the causal order alone.
