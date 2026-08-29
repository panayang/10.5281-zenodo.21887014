/-
# What having an observer yields, and what it does not

`Observer.lean` registered one choice: an observer is its crossed-threshold set.
This file spends it — derives forward, lists what follows and what refuses to,
and treats the refusals as the data.

**No assumption is introduced here.**  In particular nothing below assumes that
absoluteness fails, or takes the no-go literature's list as a target to be hit.
The method is the opposite: see what the postulate gives, and let the places where
something obviously *should* follow and does not be the candidates for a new
axiom.

## I.  What follows

**Agreement between observers is itself an observer.**  The componentwise
*minimum* of two resolutions has crossed exactly the thresholds both have crossed
— an equality, not an inclusion (`crossedSet_meet`).  Together with
`Observer.common_refinement` the observers form a lattice and the crossed set is a
homomorphism into sets.  Intersubjective agreement is not an abstraction over
observers; it is realised by one.

**An observer is a difference, not a position.**  Shifting the observer's
resolution and every threshold together changes nothing
(`observation_is_fiducial_invariant`), which is A5 applied to the postulate.  So
observation factors through resolutions-modulo-a-common-shift: an `n`-dimensional
resolution space yields an `n − 1`-dimensional observer space, and an observer
cannot know where it is, only how far it stands from what it can see.

*(That `n − 1 = k = 3` is arithmetic, and it is **not** claimed here that the
observer space is space.  Moving in it means resolving differently, not moving,
and nothing identifies the two.  `Audit.directionForPositionCount` records what
happened the last time a scale index was read as a position.)*

**Drift gives the arrow, and gives it a ceiling.**  Advancing along one scale
direction only enlarges the crossed set (`drift_monotone`), which is the order
`Explanation.no_arrow_from_determination` proves the dynamics cannot supply.  But
it is bounded, and sharply:

> **`drift_cannot_resolve` — a threshold blocked in any *transverse* scale
> direction is never crossed, by any amount of drift.**

So elapsing does not reveal everything.  The observer's transverse resolution is
a permanent gate, and content behind it is inaccessible for a structural reason
rather than a practical one.  This is the first thing in the development that
looks like a horizon and is not built from a metric.

## II.  What does not follow, and this is the useful part

**G1 — the history is underdetermined even when the endpoints are not.**
`path_underdetermined`: two paths with the same start and the same end cross the
thresholds in different orders, and nothing in the framework prefers one.  So an
observer's record depends on a path that nothing determines.  This is `Audit`
§V.l's gap — nothing selects a point in the solution space — reappearing as
*nothing selects a route through observer space*.  Not new, and now visible in a
second place.

**G2 — every pair of observations is compatible.**  `Observer.common_refinement`
gives a join always, so there are no incompatible measurements: any two records
can be held at once by a third observer.

**G3 — and the reason is that the observer never touches the algebra.**
`Observer.Crossed` takes two real vectors.  Nothing of ring type appears in its
signature, so no non-commutative datum can reach any observer.  And the framework
*has* non-commutative data that differ: `NCSize.correction_is_not_identically_zero`
exhibits two configurations with different directional commutators, and
`observer_cannot_separate_them` records that they are compatible with the same
complete observational record.

> **The observer as postulated is a classical observer.**  It registers
> thresholds, which are points on scale axes, and is blind to the sector where
> `ħ` lives.

The blindness half of that is **definitional** — read off `Crossed`'s signature,
not proved — and is stated as such here rather than dressed as a theorem.  That
distinction is the one this development has had to make five times already, and
making it against myself is the point of making it at all.

**G4 — there are no outcomes, hence no probability.**  Given a resolution, the
crossed set is determined.  There is no branching, nothing to weight, and no
place a Born rule could attach.  This is not stated as a theorem because there is
nothing to state: the absence is in what the definitions do not have.

## III.  Which gap is the axiom candidate

**G2 and G4 are symptoms of G3, not independent findings.**  Incompatible
measurements come from non-commutativity; an observer blind to non-commutativity
has compatible measurements necessarily.  Outcomes and their weights are what
incompatibility produces; with no incompatibility there is nothing to weigh.  So
the three collapse to one:

> **The observation postulate registers only commutative data, while the
> framework's algebra is non-commutative.  Nothing connects them.**

That is the gap where something obviously should follow and does not — the
framework carries `ħ` in `Deformation.lean`, a canonical commutation relation in
`Quantum.lean`, and a leading non-commutative correction in `Anisotropic.lean`,
and its observer cannot see any of it.

So a new axiom, **if one is needed**, is about *how an observer registers
non-commuting data*.  It is not about absoluteness, and this file gives no reason
to think absoluteness is the thing to give up — which was the instruction and is
also, now, the conclusion.

G1 is a real gap too, and is the same one already registered twice.  It is not a
candidate for a *new* axiom so much as evidence that the existing hole has a
third face.
-/
import SCD.Observer
import SCD.NCSize

namespace SCD.Observed

open SCD Observer

variable {n : ℕ} {ι : Type*}

/-! ## I. Agreement between observers is an observer -/

/-- **The meet is exactly the intersection.**

The componentwise minimum of two resolutions has crossed precisely the thresholds
both have crossed — an equality, where `Observer.common_refinement` gave only an
inclusion.  So the crossed set carries meets exactly. -/
theorem crossedSet_meet (μ : ι → Threshold n) (t t' : Resolution n) :
    crossedSet μ (fun i => min (t i) (t' i)) = crossedSet μ t ∩ crossedSet μ t' := by
  ext k
  simp only [crossedSet, Set.mem_setOf_eq, Set.mem_inter_iff, Crossed, le_min_iff]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩

/-- **Intersubjective agreement is realised, not merely defined.**

What two observers agree on is the record of a third — a coarser one.  Agreement
is not a construction over observers; it *is* an observer. -/
theorem agreement_is_an_observer (μ : ι → Threshold n) (t t' : Resolution n) :
    ∃ s : Resolution n, crossedSet μ s = crossedSet μ t ∩ crossedSet μ t' :=
  ⟨fun i => min (t i) (t' i), crossedSet_meet μ t t'⟩

/-! ## II. An observer is a difference, not a position -/

/-- **Observation is fiducial-invariant.**

Shifting the observer's resolution and every threshold by the same amount leaves
the record untouched, which is A5 applied to the postulate.  So observation
factors through resolutions modulo a common shift: an observer knows how far it
stands from what it can see and cannot know where it is. -/
theorem observation_is_fiducial_invariant (μ : ι → Threshold n) (t : Resolution n)
    (c : ℝ) :
    crossedSet (fun k i => μ k i + c) (fun i => t i + c) = crossedSet μ t := by
  ext k
  exact crossed_fiducial_invariant t (μ k) c

/-! ## III. Drift: the arrow, and its ceiling -/

/-- Advancing the resolution along a single scale direction. -/
def drift (t : Resolution n) (j : Fin n) (l : ℝ) : Resolution n :=
  fun i => if i = j then t i + l else t i

/-- **Drift only enlarges the record.**

This is the order the dynamics provably cannot supply
(`Explanation.no_arrow_from_determination`): it comes from counting, along the
direction `Signature.lean` calls time. -/
theorem drift_monotone (μ : ι → Threshold n) (t : Resolution n) (j : Fin n)
    {l : ℝ} (hl : 0 ≤ l) :
    crossedSet μ t ⊆ crossedSet μ (drift t j l) := by
  intro k hk i
  simp only [drift]
  split
  · exact le_trans (hk i) (le_add_of_nonneg_right hl)
  · exact hk i

/-- **But the arrow has a ceiling, and it is structural.**

A threshold that is out of reach in any *transverse* scale direction is never
crossed, by any amount of drift whatever.  Elapsing does not reveal everything:
the observer's transverse resolution is a permanent gate.

This is the first thing in the development that behaves like a horizon without
being built from a metric. -/
theorem drift_cannot_resolve (μ : ι → Threshold n) (t : Resolution n) (j : Fin n)
    (k : ι) {i : Fin n} (hij : i ≠ j) (hblock : t i < μ k i) (l : ℝ) :
    k ∉ crossedSet μ (drift t j l) := by
  intro hk
  have := hk i
  simp only [drift, if_neg hij] at this
  exact absurd this (not_le.mpr hblock)

/-! ## IV. What does not follow -/

/-- **G1 — the history is underdetermined even when the endpoints are not.**

Two routes through observer space with the same start and the same end cross the
thresholds in a different order, and nothing in the framework prefers one.  The
observer's record therefore depends on a path that nothing determines.

This is `Audit` §V.l's gap wearing a third face: nothing selects a point in the
solution space, nothing selects a cut, nothing selects a route. -/
theorem path_underdetermined :
    ∃ p q : ℝ → Resolution 2,
      p 0 = q 0 ∧ p 1 = q 1
      ∧ crossedSet twoThresholds (p (1 / 2)) ≠ crossedSet twoThresholds (q (1 / 2)) := by
  refine ⟨fun s => if s ≤ 1 / 2 then ![2 * s, 0] else ![1, 2 * s - 1],
          fun s => if s ≤ 1 / 2 then ![0, 2 * s] else ![2 * s - 1, 1], ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro h
    have h0 : (0 : Fin 2) ∈ crossedSet twoThresholds ![1, 0] := by
      intro i; fin_cases i <;> norm_num [twoThresholds]
    rw [show (fun s : ℝ => if s ≤ 1 / 2 then ![2 * s, 0] else ![1, 2 * s - 1]) (1 / 2)
          = ![1, 0] by norm_num,
        show (fun s : ℝ => if s ≤ 1 / 2 then ![0, 2 * s] else ![2 * s - 1, 1]) (1 / 2)
          = ![0, 1] by norm_num] at h
    have := h ▸ h0
    have h1 := this 0
    norm_num [twoThresholds] at h1

/-- **G2 — every pair of observations is compatible.**

`Observer.common_refinement` restated with its physical name: there are no
incompatible measurements here, because a join always exists.  Any two records
can be held at once. -/
theorem all_observations_compatible (μ : ι → Threshold n) (t t' : Resolution n) :
    ∃ s : Resolution n,
      crossedSet μ t ⊆ crossedSet μ s ∧ crossedSet μ t' ⊆ crossedSet μ s :=
  Observer.incomparable_but_absolute μ t t'

/-- **G3 — the framework carries non-commutative data the observer cannot reach.**

The existence half, which is the part that is a theorem: two configurations of a
non-commutative algebra whose directional commutators differ
(`NCSize.correction_is_not_identically_zero`).

The blindness half is **definitional and is not a theorem**: `Observer.Crossed`
takes two real vectors and nothing of ring type, so neither configuration can
affect any observer, and both are compatible with the same complete
observational record.  Stated as an inspection of a signature rather than dressed
as a proof — the distinction this development has had to make five times, made
here against myself. -/
theorem observer_cannot_separate_them :
    ∃ (σ : Fin 3 → MvPolynomial (Fin 3) ℝ) (p q a b : Fin 3),
      (Deformation.canonical (A := MvPolynomial (Fin 3) ℝ) (n := 3) p q).poisson
        (σ a) (σ b) ≠ 0 :=
  NCSize.correction_is_not_identically_zero

/-- **Collected: the yield and the gap.**

Agreement is an observer; observation is a difference; drift gives an arrow with
a structural ceiling.  Against that: the route is undetermined, all observations
are compatible, and the non-commutative sector is unreachable — the last two
being one gap seen twice. -/
theorem summary (μ : ι → Threshold n) (t t' : Resolution n) :
    (∃ s : Resolution n, crossedSet μ s = crossedSet μ t ∩ crossedSet μ t')
    ∧ (∃ s : Resolution n,
        crossedSet μ t ⊆ crossedSet μ s ∧ crossedSet μ t' ⊆ crossedSet μ s)
    ∧ (∃ p q : ℝ → Resolution 2,
        p 0 = q 0 ∧ p 1 = q 1
        ∧ crossedSet twoThresholds (p (1 / 2)) ≠ crossedSet twoThresholds (q (1 / 2))) :=
  ⟨agreement_is_an_observer μ t t', all_observations_compatible μ t t',
   path_underdetermined⟩

end SCD.Observed
