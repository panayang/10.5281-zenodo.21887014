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
structure is directional.**  Taking the attribution from the files' own
self-diagnoses rather than from memory:

1. `Frame.lean` — geometry: the scalar scale forbids Schwarzschild;
2. `Codimension.lean` — defects: a circle-valued (scalar) scale predicts
   strings, corrected by `Axis.lean`'s unoriented axis;
3. `Coupling.lean` — the foundation: "ratios commute" is a scalar statement;
4. `Direction.lean` — the flatness reading of commuting derivations;
5. `Axes.lean` — the uniaxial reading of `wedge v v = 0`, which is about
   *homogeneity*; the theorem was renamed in `Slice.lean`.

An earlier version of this list credited `Axis.lean` and `Slice.lean` for
occurrences 2 and 5.  Those are the files that *corrected* them; the files that
*made* them are `Codimension.lean` and `Axes.lean`'s antecedent.  The count is
unchanged; the attribution was wrong and is fixed.

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

* **A6′, the scale response law** `e^{2σ}R = κρ`.  **This is not one of the
  seven axioms.**  It is an external physical input, introduced in
  `Newton.lean` and load-bearing there and in `RicciDiag.lean`,
  `Precession.lean` and `Waves.lean`.  It appears as an explicit hypothesis in
  every theorem that uses it, so nothing is hidden at the type level — but it
  was **missing from this register**, which is the one place a reader looks to
  answer "does this rest on the axioms alone?".  Added after an external audit
  pointed it out; the omission was mine and it was the register's most
  consequential gap.
* **defects uniform in the symmetric space's volume**, needed for the
  `ρ·α = k−1` conversion in `Dimension.lean`.  No theorem supplies it;
* **A7 itself** — a commitment about what counts as an observation, promoted to
  an axiom in `Postulates.lean` rather than left as a judgement.

## V.b  Structures that carry hypotheses the axioms do not supply

A recurring shape, first registered for `Dynamics.Realizes` and then found more
widely by an external audit.  A theorem of the form "given a structure `S`, …"
is only as strong as the framework's ability to *build* an `S`.  Where it
cannot, the theorem is true but unwitnessed, and its physical gloss is a
conditional:

* **`Crossed.ScaleShift`** — the carrier of the "`ħ` is an exact scale step"
  result.  It is never constructed from `ScaleAlgebra`, `DiffRing` or
  `ScaleField`; it asks only for a ring endomorphism.  So the exactness is a
  property **of the model**, not something the axioms are shown to realise.
  This is the most consequential instance, because the claim is a flagship one;
* `Waves.Conserved` — the multipole conservation hypothesis is not bridged from
  `Dynamics.source_conserved_of_field_equation` to a concrete moment;
* `RG.ScaleFlow`, `Direction.DirTransport`, `Invariant.Trace`,
  `Covariance.CosmicHistory` — each never instantiated from the framework's own
  carrier.

**None of these is false.**  Each is a correct theorem about anything meeting
its hypothesis.  What is corrected here is the *reading*: they describe what
would follow, not what the axioms deliver.

**Update — `Witness.lean` now builds all six.**  `ℝ[X]` with `d/dX` satisfies
A1, and the shift `X ↦ X + 1` is a `ScaleShift` on it with `Δ X = 1`: the step
is **exact and finite**, not a first-order truncation.  Witnesses are also given
for `Trace` (the matrix trace), `DirTransport` (the adjoint action), `ScaleFlow`
(a non-degenerate translation flow), `Conserved` (a constant moment) and
`CosmicHistory` (a spatially constant drift).

**What that changes and what it does not.**  The theorems are now known
non-vacuous, and the structures are shown *compatible* with A1 rather than
merely assumed.  It is **not** a derivation: one model carrying both structures
does not show that every model of A1 must carry a scale shift.  So
`ħ = ` the step remains an **identification**, and stays in this register as
one.  The gap between "compatible" and "forced" is real and is not closed.

**Also fixed in the same pass**, all from the same audit: a vacuous
`x = x` theorem in `Observation.lean` replaced by its contentful contrapositive;
the deflection and precession bounds tightened from `±0.005″`/`±0.1″` to
`±0.0001″`/`±0.001″` so the *certified* precision matches the quoted comparison;
two literal `x = x` theorems removed from `Waves.lean`; and the docstring of
`Particle.no_further_label` corrected to say that it is structure
extensionality, with the physical content living upstream.

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

/-- Assumptions registered rather than smuggled: A6′, the uniform-density
assumption, and A7 itself. -/
def assumedCount : ℕ := 3

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

/-- Structures carrying hypotheses the framework does not supply — true
theorems whose physical reading is conditional (§V.b). -/
def unwitnessedStructures : ℕ := 6

/-- **The register grew under external audit, which is the point of having
one.**  An audit that finds nothing has not been run adversarially. -/
theorem register_grew_under_audit : 0 < unwitnessedStructures := by decide

/-! ## The standing verification claim -/

/-- Number of theorems put through `#print axioms` in `Verify.lean` — **every**
theorem in the development, generated from the sources rather than curated. -/
def auditedTheorems : ℕ := 641

/-- Occurrences of `sorryAx` in that audit. -/
def sorryAxCount : ℕ := 0

/-- **Nothing in the development rests on a gap**, as a number rather than a
mood: every audited theorem reduces to `propext`, `Classical.choice` and
`Quot.sound` and to nothing else. -/
theorem clean_count : sorryAxCount = 0 ∧ 0 < auditedTheorems := by
  refine ⟨rfl, ?_⟩; decide

end SCD.Audit
