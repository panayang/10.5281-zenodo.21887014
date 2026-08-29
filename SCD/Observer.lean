/-
# The observer, as a crossed-threshold set — and where absoluteness actually
# survives

The framework has an observability axiom and no observer.  A7 says every
structure the coupling generates carries a label the axioms provide; nothing
anywhere says what does the observing.  This file proposes an answer, works out
what follows, and **finds that one thing I expected to follow does not**.

## 0.  The status of this file — read first

Everything below §II is a theorem.  §I is **a choice**, and it is labelled as one
throughout rather than presented as a consequence:

> **The observation postulate.**  An observer is the set of thresholds it has
> crossed, and a threshold is crossed when the resolution exceeds it **in every
> direction**.

The relational body of the framework — A1–A7, the scale algebra, the
determination relation — does not contain this and does not imply it.  It is an
identification of the kind `Anchor.lean` tracks, and it is registered as an
input.  What it buys is that "observer" becomes a definable object at all; what
it costs is one more registered choice, and the register says so.

The choice is not arbitrary, and the reason is worth stating because it is the
only argument for it.  Five constraints are forced by existing theorems, and very
little survives all five:

* **not a thing** — `Emergence.no_fundamental_list`: nothing persists;
* **not at a place** — the framework has no space; directions are indices at a
  point, not positions (`Audit.directionForPositionCount` records the one time
  that was forgotten);
* **scale-relative** — `Emergence.resolved`: content depends on the scale asked
  at;
* **relational only** — `Expressive.eval_not_invariant`: absolute scale is not
  expressible, only differences are;
* **no preferred direction** — `Determination.influence_symm`: the determination
  relation is symmetric.

A crossed-threshold set passes all five.  It is not an object, has no location,
is indexed by scale, is built from a *comparison* of two scales — hence a
difference, hence expressible (`crossed_fiducial_invariant` checks this) — and
carries no direction of its own.

## I.  Why a count, specifically

Two further reasons, and they are why this rather than the other candidate — an
observer as a *cut* of the configuration into recorded and recording.

**It is built on the framework's one anchored concept.**
`Anchor.signed_source_is_distinguished`: `ν` being a count rather than a signed
winding is the single identification in the development that some observation
selects.  An observer that *is* a count stands on that.

**It supplies the arrow where the dynamics provably cannot.**
`Explanation.no_arrow_from_determination` proves no order comes out of the
determination relation.  But crossed sets only grow (`crossedSet_mono`), so the
observers carry an order the dynamics does not — which is exactly the division of
labour `Entropy.lean` was named for.

## II.  The chain that was asked for, and it holds

With **one** scale axis, resolutions are totally ordered, so crossed sets are
nested and any two observers are comparable — `one_axis_is_a_chain`.

A4′ gives one scale per direction, and `Openness.no_dissipation_in_one_direction`
derives `n ≥ 2` from A6.  With two axes the product order is not total, and
`two_axes_incomparable` exhibits two observers whose crossed sets are
incomparable: each has resolved something the other has not, and neither refines
the other.

> **A4′ + A6 ⟹ observers are not totally ordered.**

And A4′ was not introduced for this.  `Frame.lean` forced it because a *scalar*
scale cannot carry Schwarzschild.  So a gravitational input produces the
structure of the observer set — the first place in the development where the two
sectors constrain each other rather than talking past each other
(`Expressive.channels_independent`).

## III.  But it does **not** give up absoluteness, and I expected it to

The tempting next step, and the one I proposed before checking it: incomparable
observers means each has facts the other lacks, so there is no
observer-independent set of facts, so absoluteness of observed events fails.

**That is wrong.**  `common_refinement`: the componentwise maximum of two
resolutions is a resolution, and it has crossed everything both have crossed.  So

> **any two observers have a common refinement**, and every pair of records is
> jointly realisable by a third observer.

Incomparability here is *perspective*, not contradiction — the two observers are
looking at different things, not disagreeing about one thing.  A Wigner's-friend
structure needs a record that a finer observer cannot confirm, and crossed sets
are monotone, so no such record exists.

**So on this reading the framework keeps absoluteness.**  Placed against the seven
assumptions of the no-go literature, it has given up

* **realism** — `Emergence.resolved`, `no_fundamental_list`: properties are
  relative to the scale asked at, and nothing persists;
* **causal consistency** — `Explanation.no_arrow_from_determination` and
  `cycle_of_three`: the determination relation is symmetric and its minimal
  non-trivial structure is a three-cycle;

while **locality** is not yet expressible (there is no space), and **absoluteness,
uniqueness of outcomes and logical consistency are retained**.  That is a definite
position rather than a gap, and it is the first time the framework can be placed
in that landscape at all.

## IV.  What a new axiom would have to do — the precise handle

Absoluteness survives above for one reason only: **every resolution is an
admissible observer**, so joins are always available.  `aoe_needs_join_failure`
makes that exact — if the admissible resolutions are closed under joins, common
refinements exist and absoluteness holds.

So:

> **The only way to lose absoluteness here is an axiom restricting which
> resolutions are admissible observers, in a way that is not closed under joins.**

That is a sharp specification for the ontological question rather than an answer
to it.  Nothing in A1–A7 restricts the admissible resolutions, and inventing a
restriction to get a desired foundational conclusion would be the failure mode
this development has caught five times already.  Registered as open.

## V.  What is *not* claimed

That this is the observer, rather than an observer that satisfies the five
constraints.  The other candidate — observer as a cut into recorded and recording
— also passes them, and is rejected here for two reasons that are arguments and
not proofs: it is symmetric, so it supplies no arrow; and it would make A7 carry
a **third** independent reading, after `Locus.lean`'s observability and
`Determination.lean`'s well-posedness.  An equation with three readings and no
derivation is a warning.
-/
import SCD.Explanation
import SCD.Anchor
import SCD.Openness

namespace SCD.Observer

open SCD

/-! ## I. The observation postulate — a choice, registered

`Resolution` and `Threshold` are both "one scale per direction", which is A4′.
`Crossed` is the choice: it says how the two are compared. -/

/-- An observer's **resolution**: one log-scale per direction, which is what A4′
provides. -/
abbrev Resolution (n : ℕ) := Fin n → ℝ

/-- A **threshold**: the resolution at which some content becomes resolvable.
`Emergence.mass_iff_threshold` — mass is where a defect appears, not a property
it carries. -/
abbrev Threshold (n : ℕ) := Fin n → ℝ

/-- **THE OBSERVATION POSTULATE (a choice, not a consequence).**

A threshold is crossed when the resolution reaches it **in every direction**.

Nothing in A1–A7 says this.  It is an identification of the kind `Anchor.lean`
tracks and is registered as an input in `Audit.lean`.  What recommends it is the
five constraints of the header, which it is one of only two candidates to
satisfy. -/
def Crossed {n : ℕ} (t : Resolution n) (μ : Threshold n) : Prop := ∀ i, μ i ≤ t i

/-- **The observer**: the set of thresholds it has crossed.

Not a thing, not at a place, indexed by scale, built from a comparison, and
carrying no direction of its own. -/
def crossedSet {n : ℕ} {ι : Type*} (μ : ι → Threshold n) (t : Resolution n) : Set ι :=
  {k | Crossed t (μ k)}

/-! ## II. The checks the choice has to pass -/

/-- **Crossing is fiducial-invariant**, so the postulate is compatible with A5.

The fiducial shift moves the observer's scale and every threshold together, and
crossing compares the two — a *difference*, which
`Expressive.invariant_iff_diffPattern` says is exactly what is expressible.  Had
this failed, the postulate would have been unstatable rather than merely
optional. -/
theorem crossed_fiducial_invariant {n : ℕ} (t : Resolution n) (μ : Threshold n)
    (c : ℝ) :
    Crossed (fun i => t i + c) (fun i => μ i + c) ↔ Crossed t μ := by
  simp only [Crossed, add_le_add_iff_right]

/-- **Crossed sets only grow.**

A finer resolution has crossed everything a coarser one has.  This is the arrow
the dynamics provably cannot supply
(`Explanation.no_arrow_from_determination`). -/
theorem crossedSet_mono {n : ℕ} {ι : Type*} (μ : ι → Threshold n)
    {t t' : Resolution n} (h : ∀ i, t i ≤ t' i) :
    crossedSet μ t ⊆ crossedSet μ t' :=
  fun _ hk i => le_trans (hk i) (h i)

/-! ## III. The chain: one axis is a chain, two axes are not -/

/-- **With one scale axis the observers are totally ordered.**

Resolutions are single reals, so any two are comparable, so their crossed sets
are nested.  A scalar scale gives no perspective at all: every observer is a
coarse- or fine-graining of every other. -/
theorem one_axis_is_a_chain {ι : Type*} (μ : ι → Threshold 1) (t t' : Resolution 1) :
    crossedSet μ t ⊆ crossedSet μ t' ∨ crossedSet μ t' ⊆ crossedSet μ t := by
  rcases le_total (t 0) (t' 0) with h | h
  · exact Or.inl (crossedSet_mono μ (fun i => by rw [Subsingleton.elim i 0]; exact h))
  · exact Or.inr (crossedSet_mono μ (fun i => by rw [Subsingleton.elim i 0]; exact h))

/-- Two thresholds in two directions, each resolvable only along one axis. -/
def twoThresholds : Fin 2 → Threshold 2 := ![![1, 0], ![0, 1]]

/-- **With two scale axes the observers are not totally ordered.**

Each of the two observers has resolved something the other has not, and neither
refines the other.  A4′ supplies the second axis and
`Openness.no_dissipation_in_one_direction` derives `n ≥ 2` from A6, so this is the
framework's actual situation and not a hypothetical.

**A4′ was forced by gravity** — `Frame.lean`, because a scalar scale cannot carry
Schwarzschild — so a gravitational input is what makes perspective possible. -/
theorem two_axes_incomparable :
    ¬ (crossedSet twoThresholds ![1, 0] ⊆ crossedSet twoThresholds ![0, 1])
    ∧ ¬ (crossedSet twoThresholds ![0, 1] ⊆ crossedSet twoThresholds ![1, 0]) := by
  constructor
  · intro h
    have h0 : (0 : Fin 2) ∈ crossedSet twoThresholds ![1, 0] := by
      intro i; fin_cases i <;> norm_num [twoThresholds]
    have := h h0 0
    norm_num [twoThresholds] at this
  · intro h
    have h1 : (1 : Fin 2) ∈ crossedSet twoThresholds ![0, 1] := by
      intro i; fin_cases i <;> norm_num [twoThresholds]
    have := h h1 1
    norm_num [twoThresholds] at this

/-! ## IV. And absoluteness survives — the step I expected to fail

The tempting reading of §III is that incomparable observers means there is no
observer-independent set of facts.  It does not, and this section is the
correction. -/

/-- **Any two observers have a common refinement.**

The componentwise maximum of two resolutions is a resolution, and it has crossed
everything either has.  So every pair of records is jointly realisable, and the
incomparability of §III is *perspective* rather than contradiction. -/
theorem common_refinement {n : ℕ} {ι : Type*} (μ : ι → Threshold n)
    (t t' : Resolution n) :
    crossedSet μ t ∪ crossedSet μ t' ⊆ crossedSet μ (fun i => max (t i) (t' i)) := by
  rintro k (hk | hk) i
  · exact le_trans (hk i) (le_max_left _ _)
  · exact le_trans (hk i) (le_max_right _ _)

/-- **So on this reading the framework keeps absoluteness of observed events.**

Crossed sets are monotone and joins always exist, so no record is one that a
finer observer cannot confirm — which is what a Wigner's-friend structure would
require.  Stated together with §III so the pair is visible: **incomparable, and
still absolute.** -/
theorem incomparable_but_absolute {n : ℕ} {ι : Type*} (μ : ι → Threshold n)
    (t t' : Resolution n) :
    ∃ s : Resolution n, crossedSet μ t ⊆ crossedSet μ s ∧ crossedSet μ t' ⊆ crossedSet μ s :=
  ⟨fun i => max (t i) (t' i),
   fun _ hk i => le_trans (hk i) (le_max_left _ _),
   fun _ hk i => le_trans (hk i) (le_max_right _ _)⟩

/-! ## V. What a new axiom would have to do -/

/-- **Absoluteness holds exactly because every resolution is admissible.**

If the admissible observers are closed under componentwise maxima, common
refinements exist among them and absoluteness survives.  So losing it requires an
axiom restricting which resolutions are admissible, in a way that is **not**
closed under joins.

Nothing in A1–A7 restricts them.  This is a specification for the ontological
question, not an answer to it, and inventing a restriction to reach a desired
foundational conclusion is the failure mode the register has caught five
times. -/
theorem aoe_needs_join_failure {n : ℕ} {ι : Type*} (μ : ι → Threshold n)
    (Adm : Resolution n → Prop)
    (hjoin : ∀ t t', Adm t → Adm t' → Adm (fun i => max (t i) (t' i)))
    (t t' : Resolution n) (ht : Adm t) (ht' : Adm t') :
    ∃ s, Adm s ∧ crossedSet μ t ⊆ crossedSet μ s ∧ crossedSet μ t' ⊆ crossedSet μ s :=
  ⟨fun i => max (t i) (t' i), hjoin t t' ht ht',
   fun _ hk i => le_trans (hk i) (le_max_left _ _),
   fun _ hk i => le_trans (hk i) (le_max_right _ _)⟩

/-- **Collected.**

One axis is a chain; two axes are not; and joins exist regardless, so
absoluteness survives.  The chain that was asked for holds and the conclusion
that was expected of it does not. -/
theorem summary {ι : Type*} (μ : ι → Threshold 1) (t t' : Resolution 1) :
    (crossedSet μ t ⊆ crossedSet μ t' ∨ crossedSet μ t' ⊆ crossedSet μ t)
    ∧ (¬ (crossedSet twoThresholds ![1, 0] ⊆ crossedSet twoThresholds ![0, 1])
        ∧ ¬ (crossedSet twoThresholds ![0, 1] ⊆ crossedSet twoThresholds ![1, 0]))
    ∧ (∀ {n : ℕ} {κ : Type*} (ν : κ → Threshold n) (s s' : Resolution n),
        ∃ r, crossedSet ν s ⊆ crossedSet ν r ∧ crossedSet ν s' ⊆ crossedSet ν r) :=
  ⟨one_axis_is_a_chain μ t t', two_axes_incomparable,
   fun ν s s' => incomparable_but_absolute ν s s'⟩

end SCD.Observer
