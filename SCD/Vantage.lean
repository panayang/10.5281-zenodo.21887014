/-
# The vantage space: there is no spacetime to relate the observer to

The question this file was opened to answer was "what is the relation between
the observer and spacetime".  The answer is that **the second term does not
refer**, and once that is said the first one becomes a definite object.

## I.  Observer and observed are one type

`Observer.Resolution n` and `Observer.Threshold n` are both `Fin n → ℝ`, and
`Observer.lean` says why: both are "one scale per direction", which is A4′.  So
`observer_and_observed_are_one_type` is `rfl` — the proof is empty and the
statement is the content.  There is no category of observer distinct from the
category of thing observed.  Both are **places in a space of scales**, and this
file calls that the *vantage space*.

`Crossed` is then the product order on it, and the order is the observing
relation:

* `every_vantage_observes_itself` — reflexivity.  Every vantage observes itself,
  and exactly at its own boundary;
* `self_observation_is_exact` — antisymmetry.  Two vantages that observe each
  other are the same vantage.

So the vantage space is a **poset whose order is observation**.  Nothing was
imported to get that; it is `Crossed` read for what it says.

## II.  And there is no space for it to sit in

`Observer.lean` states the framework's own position: *the framework has no
space; directions are indices at a point, not positions*, and
`Audit.directionForPositionCount` records the one time that was forgotten.

This file does not overturn that.  The vantage space is a space of **scales**,
one per direction — not of positions.  Calling it spacetime would repeat exactly
the error the register already counts once.  What is claimed is narrower and
more useful:

> There is no position space in this framework, so "the relation between the
> observer and spacetime" has no second term.  What exists is the vantage space,
> and an observer is a point of it together with a commitment.

## III.  The commitment, and what it costs

An internal observer is a pair: **where** it is (`σ`, a point) and **how much of
itself it commits** (`S`, a set of directions).  Content is

* **covariant** in the vantage — `record_mono_in_resolution`, new here; the
  development had `Observer.crossedSet_mono` for the detached observer and never
  the internal one;
* **contravariant** in the commitment — `Internal.record_antitone`, already
  proved: more directions is more conditions, hence a stricter filter.

`the_two_variances_commute` puts them together: content is a bifunctor on
`(ℝⁿ, ≤) × (Finset (Fin n))ᵒᵖ`.  `Content.lean` found the second variance and
fixed the vantage; nobody varied both.

And the trade is real, not formal.  `empty_commitment_records_everything`: an
observer committing **no** direction records **everything**.
`Internal.record_univ_is_the_detached_observer`: committing all of them is
detachment.  `commitment_costs_content` exhibits the strict gap.

> **Detachment is maximal commitment, and it sees the least.**

That is an uncertainty-shaped statement obtained by unfolding an intersection.
It is not the uncertainty principle and no claim is made that it is one.

## IV.  Where the algebra enters — and this part is new

Until now nothing mapped the algebra into the observer's space.  The two shared
the index type `Fin n` and nothing else: the algebra's directions carried ring
elements, the observer's carried reals, and §V.x records the resulting gap.

`place` is the map.  Given a filtration **per direction** and its threshold
function, a ring element gets one real per direction — its threshold there — and
so acquires a point of the vantage space.  `algebra_record_is_observer_record`
then says the algebraic resolved set **is** the observer's record, and
`algebra_record_mono` transports the ordering back.

So the algebra's elements do not sit in a pre-existing space; they **acquire**
places, and the place is a tuple of thresholds.

## What this costs, and it is not small

`place` needs `n` filtrations, one per direction.  §V.ac already records that a
filtration is **postulated** and that nothing in A1–A7 builds one — G3's residue.
This file does not discharge that; it **multiplies it by `n`**.  The gain is that
the postulate now does visible work in a second place, so it is one structure
paying for two things rather than one; the cost is that the unwitnessed
structure got larger, and the register says so.

And the bridge reaches `Internal.record`, not `Spectrum.gaps`.  §V.x's gap has
two halves — algebra-to-record and record-to-measurement — and only the first is
closed here.
-/
import SCD.Internal
import SCD.Layers
import SCD.Content

namespace SCD.Vantage

open SCD Observer


variable {n : ℕ} {ι : Type*}

/-! ## I. Observer and observed are one type -/

/-- **Observer and observed are the same type.**

Both are `Fin n → ℝ`, both are "one scale per direction" (A4′).  The proof is
empty; the statement is the content. -/
theorem observer_and_observed_are_one_type (n : ℕ) :
    Resolution n = Threshold n := rfl

/-- **Reflexivity**: every vantage observes itself, exactly at its own
boundary. -/
theorem every_vantage_observes_itself (σ : Resolution n) : Crossed σ σ :=
  fun _ => le_rfl

/-- **Antisymmetry**: two vantages that observe each other are one vantage.  With
the previous theorem this makes the vantage space a poset **whose order is
observation**. -/
theorem self_observation_is_exact (σ : Resolution n) (μ : Threshold n)
    (h : Crossed μ σ) (h' : Crossed σ μ) : σ = μ :=
  funext fun i => le_antisymm (h i) (h' i)

/-! ## II. Commitment costs content -/

/-- **An observer committing no direction records everything.**

Vacuous quantification over the empty commitment.  The other end is
`Internal.record_univ_is_the_detached_observer`. -/
theorem empty_commitment_records_everything (μ : ι → Threshold n) (σ : Resolution n) :
    Internal.record (∅ : Finset (Fin n)) μ σ = Set.univ := by
  ext k
  simp only [Internal.record, Internal.InternalCrossed, Set.mem_setOf_eq,
    Finset.notMem_empty, false_implies, Set.mem_univ, iff_true]
  intro i
  trivial

/-- **And the trade is strict**, not merely formal: one direction, one threshold,
and the two ends differ. -/
theorem commitment_costs_content :
    ∃ (μ : Fin 1 → Threshold 1) (σ : Resolution 1),
      Internal.record (Finset.univ : Finset (Fin 1)) μ σ
        ≠ Internal.record (∅ : Finset (Fin 1)) μ σ := by
  refine ⟨fun _ => ![1], ![0], ?_⟩
  intro h
  have hmem : (0 : Fin 1) ∈ Internal.record (∅ : Finset (Fin 1)) (fun _ => ![1]) ![0] := by
    simp only [Internal.record, Internal.InternalCrossed, Set.mem_setOf_eq,
      Finset.notMem_empty, false_implies, forall_const]
  rw [← h] at hmem
  have := hmem 0 (Finset.mem_univ 0)
  norm_num at this

/-! ## III. Content is covariant in the vantage and contravariant in the commitment -/

/-- **Content is covariant in the vantage.**

`Observer.crossedSet_mono` had this for the detached observer only; the internal
one never had it. -/
theorem record_mono_in_resolution (μ : ι → Threshold n) (S : Finset (Fin n))
    {σ σ' : Resolution n} (h : ∀ i, σ i ≤ σ' i) :
    Internal.record S μ σ ⊆ Internal.record S μ σ' :=
  fun _ hk i hi => le_trans (hk i hi) (h i)

/-- **The two variances commute**, so content is a bifunctor on
`(ℝⁿ, ≤) × (Finset (Fin n))ᵒᵖ`: covariant in where you stand, contravariant in how
much of yourself you commit. -/
theorem the_two_variances_commute (μ : ι → Threshold n) {S S' : Finset (Fin n)}
    (hS : S ⊆ S') {σ σ' : Resolution n} (h : ∀ i, σ i ≤ σ' i) :
    Internal.record S' μ σ ⊆ Internal.record S μ σ' :=
  fun _ hk i hi => le_trans (hk i (hS hi)) (h i)

/-! ## IV. The algebra lands in the vantage space -/

section Place

variable {A : Type*} [Ring A]

/-- A ring element's **place**: its threshold in each direction, one real per
direction.

This is the first map from the algebra into the observer's space.  The `+1` is
`Layers.HasThreshold`'s convention — *invisible up to `k`* versus *visible from
`k`* — and not a difference of content. -/
def place (thr : Fin n → A → ℕ) (a : A) : Threshold n :=
  fun i => ((thr i a : ℝ) + 1)

/-- **The algebraic resolved set is the observer's record.**

Per-direction filtrations give each element a place, and what a probe resolves in
the algebra is exactly what an observer at that vantage records.  This is the
algebra-to-record half of §V.x's gap; the record-to-measurement half is
untouched. -/
theorem algebra_record_is_observer_record
    (F : Fin n → Resolution.Filtration A) (thr : Fin n → A → ℕ)
    (hthr : ∀ i, Layers.HasThreshold (F i) (thr i))
    (e : ι → A) (k : Fin n → ℕ) (S : Finset (Fin n)) :
    Internal.record S (fun j => place thr (e j)) (fun i => (k i : ℝ))
      = {j | ∀ i ∈ S, (F i).Resolved (k i) (e j)} := by
  ext j
  simp only [Internal.record, Internal.InternalCrossed, place, Set.mem_setOf_eq]
  constructor
  · intro h i hi
    rw [hthr i]
    have := h i hi
    exact_mod_cast this
  · intro h i hi
    have := (hthr i _ _).mp (h i hi)
    exact_mod_cast this

/-- **And a finer resolution records more**, stated in the algebra's own terms by
transporting `record_mono_in_resolution` across the bridge. -/
theorem algebra_record_mono
    (F : Fin n → Resolution.Filtration A) (thr : Fin n → A → ℕ)
    (hthr : ∀ i, Layers.HasThreshold (F i) (thr i))
    (e : ι → A) (k k' : Fin n → ℕ) (hk : ∀ i, k i ≤ k' i) (S : Finset (Fin n)) :
    {j | ∀ i ∈ S, (F i).Resolved (k i) (e j)}
      ⊆ {j | ∀ i ∈ S, (F i).Resolved (k' i) (e j)} := by
  rw [← algebra_record_is_observer_record F thr hthr e k S,
      ← algebra_record_is_observer_record F thr hthr e k' S]
  exact record_mono_in_resolution _ S (fun i => by exact_mod_cast hk i)

end Place

end SCD.Vantage
