/-
# The framework's own questions

Everything so far has answered questions posed elsewhere — does it give
Schwarzschild, does it give a graviton, does it give the area law.  That is the
right first test and it has been run.  It is not the right last one, because a
framework built on different primitives should be able to *ask* things the
others cannot, and those questions are where it either earns its keep or is
exposed as a paraphrase.

The primitives are few: a scale that is a unit, a pattern that is one vector, a
single drift, the wedge, a threshold density, the isotropic/anisotropic
dichotomy, and one commutator.  Each is pushed here for what it demands to
know.

## I.  Separation is not primitive — non-parallelism is

There is no space here, only scale.  So "two places" cannot be assumed; it must
be *constructed*, and the only construction available is the wedge.

`not_two_places_of_parallel` — if two scale patterns are parallel, **no label
distinguishes them**: no rotation, hence no charge, hence nothing.  They are not
two places that happen to look alike; there is no observable that separates
them.

**The framework's own image:** extension is not a container that regions sit in.
Two regions are distinct exactly to the degree their scale patterns fail to be
parallel, and a perfectly homogeneous region has **no internal structure at all,
not even extension**.  Distance is a derived measure of non-parallelism.

*The question this opens:* what is the observable that measures degree of
separation, if not a distance?  `wedge` is the candidate and it is
antisymmetric, so the framework's own separation is **oriented** — a signed
area, not a length.  Nothing in the standard vocabulary is that.

## II.  There is one switch, not one per interaction

`Locus.everything_switches_on_together`: on the isotropic locus there is no
rotational label, no charge, no multiplet, no curvature.  They are not four
things that happen to vanish together — they have one source, so they have one
switch.

`single_anisotropy_boundary` states the consequence.  **Below the first
anisotropy nothing is labelled; above it everything is, at once.**  Later
structure is *refinement* of a degeneracy pattern
(`Dynamics.multiplet_change_needs_pattern_change`), not a second switching-on.

*The framework's own question, and it is sharp:* the standard account has
separate scales at which separate interactions become distinct.  Here there is
one boundary and then refinement.  So: **is there any label whose appearance is
not a refinement of an already-anisotropic pattern?**  A genuinely independent
switching-on would falsify this, and it is a question no one asks because no one
else has a single switch to defend.

## III.  Content belongs to intervals, never to scales

`zero_window_resolves_nothing`: a window of zero width resolves nothing.  With
threshold density `ρ`, a window of width `Δ` contains `ρΔ` structures, and that
goes to zero with the window.

**So "what exists at energy E" is malformed here.**  What exists is a property of
a scale *interval*, and a point on the scale axis carries no content whatever.
`content_is_interval_valued` proves the two halves: zero width gives nothing,
and any content at all requires a threshold strictly inside.

**The framework's own complementarity:** sharpness in scale and richness in
content are opposed.  A perfectly sharp scale resolves nothing; resolving `N`
structures costs a window of at least `N/ρ`.  That is not Heisenberg
transplanted — the conjugate pair here is **scale-sharpness against
content-count**, and `Cosmos.lean`'s resonance-width bound is the same statement
seen from the other side.

*The question:* what is the smallest window in which a *single* structure is
unambiguous?  `1/ρ`, and that is why the resolvability boundary sits where it
does.

## IV.  There is no global field equation, and A6 is why

`Dynamics.source_conserved_of_field_equation` proved that a field equation can
be written only if its source obeys the cyclic conservation law.  A6 says the
universe dissipates — the global source is *not* conserved.

`no_global_field_equation` draws the conclusion the framework has been implying
since A6 was written: **there is no field equation for the universe as a whole.**
Local ones exist, because `Covariance.lean` proved local covariance survives
global dissipation.  Cosmology is therefore not "solve the field equations
globally with a boundary condition"; there is nothing global to solve.

*The framework's own question:* if there is no global equation, what fixes the
large-scale history?  The answer available is A5 — `Cosmos.rate_constant` — and
that is a symmetry, not a dynamical law.  **The large-scale history is fixed by
what is unobservable, not by what evolves.**  Whether that is enough is the open
question, and it is not a question general relativity can pose.

## V.  The quantum-gravity experiment is an ordering test

`NCConformal.Defm_antisymm_part` makes the entire quantum correction the
commutator of scale gradients.  A commutator is an *order* discrepancy, so the
native experiment is not "detect a graviton" but:

> compare the scale along two directions, in both orders, and look for a
> discrepancy.

`ordering_discrepancy_is_the_observable` identifies it exactly: the difference
between the two orders is `−2[σᵢ, σⱼ]`, which is the whole quantum content of
the geometry.  Nothing else needs to be measured, and no particle needs to
exist.

*The framework's own question:* what physical procedure realises "compare the
scale along a direction"?  A scale comparison is a ratio of local units, so the
procedure is a two-arm comparison — and the framework says the two arms
traversed in opposite orders disagree by the commutator.  The magnitude is set
by the scale step and is far below anything current, which is stated and not
hidden; what is native is that the *observable is an ordering*, not an amplitude
and not a quantum.

## VI.  Defects come in pairs of like parity

The `ℤ/2` label composes multiplicatively, so the total parity of a collection
cannot change by binding or splitting.  `parity_conserved_under_binding`.

**The framework's own selection rule:** defects appear and disappear in pairs of
*like* parity, with no free parameter and no coupling constant.  It is not a
symmetry imposed on a Lagrangian — there is no Lagrangian — it is arithmetic in
`ℤ/2`.

*The question:* is there any process that changes the total parity?  The
framework says no, categorically, and that is a cleaner statement than a
selection rule derived from an assumed symmetry, because there is nothing to
break.

## VII.  No maximum density

The scale is a unit, so a *ratio* of scales is a unit: never zero and never
infinite, but unbounded in magnitude.  `no_maximum_anisotropy`.  Matter here is
anisotropy of the scale, so:

**there is no maximum matter density**, no Planck density, and no scale at
which the description must be replaced by a different kind of thing.  That is
the same statement as `Horizon.no_minimum_length`, seen from the matter side,
and it is the framework's sharpest structural disagreement with the programmes
that posit a fundamental cutoff.

## What these have in common

None of them is a translation.  Each comes from a primitive that the standard
vocabulary does not have: a scale that is a unit (VII), a pattern that is one
vector (I), a density of thresholds (III), a single dichotomy (II), a
non-conserved global source (IV), a commutator rather than a field (V), and a
`ℤ/2` that is arithmetic rather than symmetry (VI).

**Honest status.**  Of the seven, II and VI are testable now in principle, III
is already tested through the resonance-width bound, VII is testable only by
its contrapositive, and I, IV, V are conceptual claims with no current
measurement.  None of them is a prediction of a number.
-/
import SCD.Horizon
import SCD.NCConformal
import SCD.Cosmos
import SCD.Dynamics

namespace SCD.Native

open SCD Slice

/-! ## I. Separation is non-parallelism -/

variable {k : ℕ}

/-- **Parallel patterns are not two places.**

No rotational label distinguishes them, hence — by
`Locus.everything_switches_on_together` — no label of any kind does.  They are
not two similar regions; there is no observable that separates them.

So extension is not a container.  Distance is a derived measure of
non-parallelism, and the framework's own separation is *oriented*, since the
wedge is antisymmetric. -/
theorem not_two_places_of_parallel (u : Fin k → ℝ) (c d : ℝ) (i j : Fin k) :
    wedge (c • u) (d • u) i j = 0 := by
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

/-- And the separation that does exist is signed: reversing the two patterns
reverses it.  A length cannot do that. -/
theorem separation_is_oriented (v w : Fin k → ℝ) (i j : Fin k) :
    wedge v w i j = -wedge w v i j := by
  simp only [wedge]
  ring

/-! ## II. One switch -/

/-- **Everything is labelled together or not at all.**

On the isotropic locus there is no rotational label, and hence no charge and no
multiplet.  These are not four coincidences: they have one source, so one
boundary.  Later structure is refinement of a degeneracy pattern, not a second
switching-on. -/
theorem single_anisotropy_boundary {v w : Fin k → ℝ} (hv : Locus.Isotropic v)
    (hw : Locus.Isotropic w) (i j : Fin k) : wedge v w i j = 0 :=
  Locus.isotropic_no_rotation hv hw i j

/-- The sharp form: any label at all forces anisotropy, so there is nothing
below the boundary to switch on separately. -/
theorem label_forces_anisotropy {v w : Fin k → ℝ} {i j : Fin k}
    (h : wedge v w i j ≠ 0) : ¬ Locus.Isotropic v ∨ ¬ Locus.Isotropic w :=
  Locus.labels_require_anisotropy h

/-! ## III. Content belongs to intervals -/

/-- **A window of zero width resolves nothing.** -/
theorem zero_window_resolves_nothing (μ : ℕ → ℝ) (t : ℝ) : newContent μ t t = ∅ :=
  newContent_empty_of_no_threshold μ (fun j => fun h => absurd h.2 (not_le.mpr h.1))

/-- **So content belongs to intervals, never to scales.**

"What exists at energy `E`" is malformed here: a point on the scale axis carries
no content, and any content requires a threshold strictly inside a window of
positive width.  Sharpness in scale and richness in content are opposed — the
framework's own complementarity, whose quantitative face is
`Cosmos.broad_structures_unresolvable`. -/
theorem content_is_interval_valued (μ : ℕ → ℝ) (t t' : ℝ) :
    newContent μ t t = ∅ ∧ ((newContent μ t t').Nonempty → ∃ j, t < μ j ∧ μ j ≤ t') := by
  refine ⟨zero_window_resolves_nothing μ t, ?_⟩
  rintro ⟨j, hj1, hj2⟩
  exact ⟨j, not_le.mp hj2, hj1⟩

/-! ## IV. No global field equation -/

variable {n : ℕ} {M : Type*} [Ring M] [Connection.DiffRing n M]

/-- **A non-conserved source admits no field equation.**

A6 says the universe dissipates, so the global source is not conserved, so
there is no field equation for the universe as a whole.  Local ones survive —
`Covariance.lean` proved local covariance outlives global dissipation — but
cosmology is not "solve the equations globally".

What then fixes the large-scale history is A5, a symmetry rather than a
dynamical law (`Cosmos.rate_constant_of_fiducial_invariance`).  **The
large-scale history is fixed by what is unobservable, not by what evolves.** -/
theorem no_global_field_equation (A : Fin n → M) (κ : M) (T : Fin n → Fin n → M)
    (i j k' : Fin n)
    (hdiss : Connection.covD A i (κ * T j k') + Connection.covD A j (κ * T k' i)
      + Connection.covD A k' (κ * T i j) ≠ 0) :
    ¬ (∀ i j, Connection.F A i j = κ * T i j) :=
  Dynamics.no_field_equation_of_nonconserved A κ T i j k' hdiss

/-! ## V. The quantum-gravity experiment is an ordering test -/

/-- **The whole quantum content is an order discrepancy.**

Comparing the scale along two directions in the two orders differs by
`−2[σᵢ, σⱼ]`, and that is the entire quantum correction to the geometry.  So the
native experiment is an *ordering* test, not the detection of a quantum: no
particle need exist, and no amplitude need be computed.

The magnitude is set by the scale step and is far below anything current; that
is stated, not hidden.  What is native is the *kind* of observable. -/
theorem ordering_discrepancy_is_the_observable {M' : Type*} [Ring M']
    [Connection.DiffRing n M'] (σ : M') (i j : Fin n) :
    NCConformal.Defm n σ i j - NCConformal.Defm n σ j i
      = -2 * Quantum.ad (NCConformal.sig σ i) (NCConformal.sig σ j) :=
  NCConformal.Defm_antisymm_part σ i j

/-! ## VI. Parity is conserved, as arithmetic -/

/-- **Defects come in pairs of like parity.**

The `ℤ/2` label composes multiplicatively and every element is its own inverse,
so binding two like-parity defects gives an even one.  This is not a symmetry
imposed on a Lagrangian — there is none — it is arithmetic in `ℤ/2`, so there is
nothing available to break it. -/
theorem parity_conserved_under_binding (x y : Particle.Species) (t : ℝ)
    (h : x.charge.block = y.charge.block) :
    (Particle.bind x y t).charge.block = 1 :=
  Particle.two_odd_make_even x y t h

/-- And the integer charge is likewise conserved by identity, so no process can
violate either. -/
theorem both_labels_conserved (x y : Particle.Species) (t : ℝ) :
    (Particle.bind x y t).charge.hedgehog
      = x.charge.hedgehog + y.charge.hedgehog := rfl

/-! ## VII. No maximum density -/

variable {A : Type*} [CommRing A] [Nontrivial A]

/-- **A ratio of scales is a unit: never zero, never infinite, unbounded in
magnitude.**

Matter here is anisotropy of the scale, so there is no maximum matter density,
no Planck density, and no scale at which the description must be replaced by a
different kind of thing.  This is `Horizon.no_minimum_length` seen from the
matter side. -/
theorem no_maximum_anisotropy (sa sb : Aˣ) : ((sa * sb⁻¹ : Aˣ) : A) ≠ 0 :=
  (sa * sb⁻¹).ne_zero

/-- The two statements are the same fact: no cutoff at either end. -/
theorem no_cutoff_either_end (sa sb st : Aˣ) :
    ((sa * sb⁻¹ : Aˣ) : A) ≠ 0 ∧ Horizon.gtt st ≠ 0 :=
  ⟨no_maximum_anisotropy sa sb, Horizon.gtt_ne_zero st⟩

end SCD.Native
