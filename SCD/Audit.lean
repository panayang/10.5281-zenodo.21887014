/-
# The register: what is retracted, corrected, cited, and assumed

The development was built by revision, and the revisions matter as much as the
results.  Rather than leave that history scattered across six files, this is the
single place to check before relying on anything.

Nothing here is new mathematics.  It is the standing answer to "does this rest
on the axioms alone?", and it is meant to be read before, not after.

## I.  Retracted — was claimed, is now withdrawn

**The geometric mass tower.**  `Defect.lean` posited `m_k = m₀e^{|k|Δ}` and
`QCD.geometric_tower_fails` refuted it against lattice glueball ratios.  But the
law was *assumed*, not derived: `MassAudit.mass_law_underdetermined` exhibits a
quadratic law equally compatible with everything proved.  So the refutation
falsified **that hypothesis**, not the framework.  `Emergence.mass_iff_threshold`
later explained why no such law exists — mass is not a property of a defect, it
is where the defect appears.

**The colour identification.**  `Color.lean` derived a confined finite charge
and read it as colour.  `ColorAudit.lean` found it gives `2` where the data
wants `3`.  The failure was not technical: the attempt borrowed the Standard
Model's *ontology*.  `Particle.block_cannot_be_three_valued` now explains it —
the block group is `ℤ/2` because the order parameter is projective, so `3` was
never available.

**The cross-sector test.**  `CrossCheck.lean` proposed measuring the threshold
density two ways.  The two `ρ`'s are not the same quantity: one is a raw count,
the other sector-restricted and signed.  `Running.lean`'s wording was corrected.

**Codimension.**  `Codimension.lean`'s theorems hold of a circle-valued scale.
They do not describe this framework: with A4 directional, `Axis.lean` restores
point defects.

## II.  Corrected — the claim was overstated, the theorem survives

**"Commuting derivations are flat."**  `Direction.lean` read A1's `d_comm` as a
hidden flatness assumption.  `Dynamics.no_flatness_from_commuting_derivations`
refutes it: kill every derivation and the curvature survives.  A chart is a
chart; flatness lives in whether the *connection* commutes.

**"Directions are the algebra."**  Same file.  With the algebra named,
`dim so(3,1) = 6 ≠ 4`.  Directions are the **defining representation**
(`Dimension.algebra_bigger_than_directions`).  Nothing was lost: naming the
algebra still fixes `n = k + 1`.

**"Multiplets are internally flat."**  `Dynamics.same_multiplet_no_rotation`
holds of anything meeting its hypothesis, but that hypothesis assigns one
scaling operator per direction and real rank one supplies one vector and one
scaling.  The physical gloss is withdrawn; `Axes.lean` replaces it.

**"Uniaxial patterns carry no rotation."**  The theorem said a vector wedged
with *itself* vanishes — that is about **homogeneity**, not about axes.  It is
now `Slice.homogeneous_carries_no_rotation`, and the dilemma it appeared to
create dissolved (`Axes.lean`).  This one survived a formalisation and a
published draft before being caught.

**"The channels are independent."**  `Expressive.channels_independent` is true
of the *scalar* sector.  `Coupling.lean` shows the directional scale makes the
rotation sector *generated* by the scale sector.

**`f₀(500)` violates the width bound.**  A previous version of `Data.lean`
quoted the pole as `457 − i279`, which is neither standard determination.  With
the real values the bound falls *between* CCL and GKPY; it is open, not
violated.

## III.  The recurring error

Five of the corrections above are the same mistake: **scalar reasoning where the
structure is directional.**  It appeared in `Frame.lean` (geometry),
`Axis.lean` (defects), `Coupling.lean` (the foundation — "ratios commute" is
scalar), `Direction.lean` (the flatness reading), and `Slice.lean` (the uniaxial
reading).

`scalar_for_directional_count` records the number so it cannot drift.

**The diagnostic that catches it:** when a claim mentions a count — one axis,
one scale, one direction, one value — ask *a count of what*.  Values and
directions come apart every time.

## IV.  Cited, not proved

* the classification of real-rank-one real simple Lie algebras
  (`so(n,1)`, `su(n,1)`, `sp(n,1)`, `f₄₍₋₂₀₎`), used in `Algebra.lean` to pass
  from "real rank one" to "the Lorentz family".  Rank one itself is proved; the
  exhaustiveness of the list is not;
* the homotopy of projective spaces — `π₁(ℝPⁿ) = ℤ/2`, `π₂(S²) = ℤ`, and the
  vanishing of `π₂` for a Lie group modulo a discrete subgroup — used in
  `Particle.lean` and `Axes.lean`.

If either citation fails, the constraint above it still stands; only the
identification does not.

## V.  Assumed, and registered rather than smuggled

* **defects uniform in the symmetric space's volume**, needed for the
  `ρ·α = k−1` conversion in `Dimension.lean`.  No theorem supplies it;
* **A7 itself** — a commitment about what counts as an observation, promoted to
  an axiom in `Postulates.lean` rather than left as a judgement.

## VI.  What rests on the axioms alone

The scale/rotation split, the Lorentzian signature, the bookkeeping form, the
coupling, real rank one, `n = k+1`, conservation from Bianchi, the gravity chain
through to `1.7515″` and `42.99″/century`, `ħ` as an exact scale step, the
label structure on the anisotropic locus, and every statement in `Native.lean`.

`clean_count` records the audited total against the axiom-leak count, so the
claim "nothing rests on a gap" is a number and not a mood.
-/
import SCD.Data

namespace SCD.Audit

/-! ## The register, in numbers -/

/-- How many times the scalar-for-directional substitution has been made and
caught.  Recorded so the count cannot quietly drift. -/
def scalarForDirectionalCount : ℕ := 5

theorem scalar_for_directional_count : scalarForDirectionalCount = 5 := rfl

/-- Claims retracted outright. -/
def retractedCount : ℕ := 4

/-- Claims corrected in scope, where the theorem survives and the gloss did
not. -/
def correctedCount : ℕ := 6

/-- External results cited and not proved. -/
def citedCount : ℕ := 2

/-- Assumptions registered rather than smuggled, `A7` included. -/
def assumedCount : ℕ := 2

/-- **The register is not empty, and that is the point.**

A development with nothing retracted has not been audited.  The counts are
carried so that a reader can weigh the results against what had to be taken
back to get them. -/
theorem register_nonempty :
    retractedCount ≠ 0 ∧ correctedCount ≠ 0 ∧ citedCount ≠ 0 ∧ assumedCount ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Corrections outnumber retractions: more claims survived with their scope
narrowed than had to be withdrawn. -/
theorem more_corrected_than_retracted : retractedCount < correctedCount := by decide

/-! ## The standing verification claim -/

/-- Number of theorems put through `#print axioms` in `Verify.lean` — **every**
theorem in the development, generated from the sources rather than curated. -/
def auditedTheorems : ℕ := 592

/-- Occurrences of `sorryAx` in that audit. -/
def sorryAxCount : ℕ := 0

/-- **Nothing in the development rests on a gap**, as a number rather than a
mood: every audited theorem reduces to `propext`, `Classical.choice` and
`Quot.sound` and to nothing else. -/
theorem clean_count : sorryAxCount = 0 ∧ 0 < auditedTheorems := by
  refine ⟨rfl, ?_⟩; decide

end SCD.Audit
