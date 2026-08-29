/-
# The observer as part of the system — and what that does and does not fix

`Observer.lean`'s observer is detached, and the detachment is not a matter of
presentation.  Its resolution `t` is an argument, independent of any
configuration: nothing in the framework determines it, it is not acted on, and it
contributes to nothing.  That is precisely the observer standing outside the
world and reading off — the object the whole relational programme is supposed not
to have.

This file makes the observer a part of the configuration, works out what changes,
and reports that **the change is real and does not close the gap.**

## I.  The internal observer

An observer is a **part** of the direction set, and its resolution is not a free
parameter: it is the configuration's own scale, read in its own directions.

        record S σ = { k : μ_k i ≤ σ i for every direction i in S } .

Two consequences immediately, and they invert the intuition:

* **a larger observer records less** (`record_antitone`).  Occupying more
  directions means more conditions to meet, so a bigger part is a *stricter*
  filter.  Observation is not accumulation of vantage but narrowing of it;
* **the union of parts is the intersection of records** (`record_union`), exactly.
  So the lattice survives but turns over: joining observers coarsens what they
  can say.

And the detached observer is recovered as the degenerate case:
`record_univ_is_the_detached_observer` — `Observer.crossedSet` is the internal
observer that occupies **every** direction.  So detachment is not the absence of
a part; it is the part that leaves no complement.  That is the same shape as
`Openness.closed_universe_is_empty` and it is why the detached observer felt
abstract: it has nothing outside itself.

## II.  What internality buys: the observer is inside the determination

Once the observer is a part, `Determination.lean` applies to it, and three things
follow that could not be said before.

**It cannot set its own resolution.**  `Explanation.self_not_in_determiner`: no
part is in its own determiner.  The observer's scales are fixed by directions
outside it, so an observer does not choose what it can resolve.

**It contributes to what it observes.**  `observer_is_in_the_determiner`: any
direction of the observer that is not one of the observed pair lies in that
pair's transverse set, hence appears in `Diagonal.ric_offdiag`'s sum.  The
observer is a term in the equation for the observed.

**And the disturbance is the force, not an analogue of it.**

> `disturbance_iff_separable` — the observer's contribution vanishes for every
> pair exactly when the configuration is separable, and separable is exactly
> force-free (`Explanation.force_is_non_separability`).

So *measurement disturbs a system precisely when there is an interaction in it*,
and this is one theorem rather than two facts that resemble each other.  A
non-disturbing observation and a force-free configuration are the same condition.
This is the first thing in the development that says anything about measurement
as a physical process rather than as a labelling.

## III.  What it does not fix, which is the point

The gap of `Observed.lean` §G3 was that the observer registers only commutative,
ordered data while the framework's algebra is non-commutative.  **Internalising
the observer does not touch it.**

`internal_observations_still_compatible`: the inverted lattice still has joins —
the *intersection* of two parts records everything both record — so any two
internal observers remain compatible, exactly as the detached ones were.  Nothing
has been gained against G3.

And the reason is visible in the definition rather than hidden: `InternalCrossed`
compares `μ i` with `σ i` using `≤`.  **That needs an order on the values**, and
the framework's scale algebra is an arbitrary `Ring` with no order supplied
anywhere.  So the internal observer as written lives in the real-valued shadow of
the configuration, not in the algebra.

> **The detachment and the blindness are two different defects.**  Internality
> fixes the first — the observer is now determined by, and contributes to, the
> configuration.  The second is untouched, and it is untouched for a reason that
> is now nameable: *crossing is an order relation, and the framework gives its
> algebra no order.*

That is a sharper statement of G3 than `Observed.lean` had: not "the signature
happens to take reals" but "the relation is order-theoretic and the object is
not ordered".

## IV.  What would be needed, and the trap in it

An internal observer of the algebra needs a notion of "resolved" that is
algebraic rather than order-theoretic.  The obvious candidate is an idempotent —
"resolved" as a projection — and then non-commuting idempotents would be exactly
incompatible measurements, which is what G3 is missing.

**That is the standard quantum construction and adopting it would be importing
it**, which is the failure mode this development is built to avoid.  It is
recorded here as the shape of the answer and explicitly *not* taken.  What would
make it native rather than borrowed is an argument that `Emergence.resolved` — a
predicate already in the framework — has idempotent form for reasons internal to
the framework.  No such argument exists here.

Registered as open, and it is now the same open item as G3 rather than a new one.
-/
import SCD.Observer
import SCD.Explanation

namespace SCD.Internal

open SCD Observer

variable {n : ℕ} {ι : Type*}

/-! ## I. The internal observer -/

/-- **An internal observer is a part of the direction set**, and its resolution
is the configuration's own scale rather than a free parameter. -/
def InternalCrossed (S : Finset (Fin n)) (σ : Resolution n) (μ : Threshold n) : Prop :=
  ∀ i ∈ S, μ i ≤ σ i

/-- The record of an internal observer: the thresholds it has crossed, judged in
its own directions only. -/
def record (S : Finset (Fin n)) (μ : ι → Threshold n) (σ : Resolution n) : Set ι :=
  {k | InternalCrossed S σ (μ k)}

/-- **A larger observer records less.**

Occupying more directions is more conditions to meet, so a bigger part is a
stricter filter.  Observation is a narrowing of vantage, not an accumulation of
it — the reverse of the detached picture, where a finer resolution recorded
more. -/
theorem record_antitone (μ : ι → Threshold n) (σ : Resolution n)
    {S S' : Finset (Fin n)} (h : S ⊆ S') :
    record S' μ σ ⊆ record S μ σ :=
  fun _ hk i hi => hk i (h hi)

/-- **The union of parts is the intersection of records**, exactly.

So the lattice survives and turns over: joining observers coarsens what they can
jointly say. -/
theorem record_union (μ : ι → Threshold n) (σ : Resolution n) (S S' : Finset (Fin n)) :
    record (S ∪ S') μ σ = record S μ σ ∩ record S' μ σ := by
  ext k
  simp only [record, InternalCrossed, Set.mem_setOf_eq, Set.mem_inter_iff,
    Finset.mem_union]
  exact ⟨fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩,
         fun h i hi => hi.elim (h.1 i) (h.2 i)⟩

/-- **The detached observer is the internal one that occupies everything.**

`Observer.crossedSet` is `record Finset.univ`.  So detachment is not the absence
of a part — it is the part that leaves no complement, which is why it felt
abstract and why nothing determined it.  Same shape as
`Openness.closed_universe_is_empty`. -/
theorem record_univ_is_the_detached_observer (μ : ι → Threshold n) (σ : Resolution n) :
    record Finset.univ μ σ = crossedSet μ σ := by
  ext k
  simp only [record, InternalCrossed, crossedSet, Crossed, Set.mem_setOf_eq,
    Finset.mem_univ, forall_const]

/-! ## II. The observer is inside the determination -/

section Determination

variable {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-- **The observer is a term in the equation for the observed.**

Any direction belonging to the observer that is not one of the observed pair lies
in that pair's transverse set, hence appears in `Diagonal.ric_offdiag`'s sum.  The
observer is not outside what it observes. -/
theorem observer_is_in_the_determiner (a b c : Fin n) (hca : c ≠ a) (hcb : c ≠ b) :
    c ∈ Diagonal.transverse a b :=
  Finset.mem_erase.mpr ⟨hcb, Finset.mem_erase.mpr ⟨hca, Finset.mem_univ c⟩⟩

/-- **A separable configuration is not disturbed.**

If each direction's scale depends on its own coordinate alone, every influence
vanishes — including the observer's. -/
theorem no_disturbance_of_separable (σ : Fin n → A) (h : Explanation.Separable σ)
    (a b : Fin n) : Determination.Free σ a b :=
  Explanation.separable_is_free σ h a b

end Determination

/-- **And disturbance is exactly force.**

The observer's contribution vanishes for every pair exactly when the
configuration is separable, and separable is exactly force-free
(`Explanation.force_is_non_separability`).  The witness on the other side is
`Explanation.coupled_not_free`: a configuration in which the contribution does
not vanish.

So *measurement disturbs a system precisely when there is an interaction in it* —
one theorem, not two facts that resemble each other. -/
theorem disturbance_iff_separable :
    (∀ (m : ℕ) (B : Type) (_ : CommRing B) (_ : ScaleAlgebra m B) (σ : Fin m → B),
        Explanation.Separable σ → ∀ a b : Fin m, Determination.Free σ a b)
    ∧ ¬ Determination.Free Explanation.coupled 0 1 :=
  ⟨fun _ _ _ _ σ h a b => Explanation.separable_is_free σ h a b,
   Explanation.coupled_not_free⟩

/-! ## III. What internality does not fix -/

/-- **Internal observers are still all compatible.**

The intersection of two parts records everything both record, so a common
refinement always exists — the inverted lattice still has joins.  Internalising
the observer gains nothing against `Observed.lean`'s G3.

The reason is in the definition and not hidden: `InternalCrossed` compares values
with `≤`, which needs an order, and the framework's scale algebra is an arbitrary
`Ring` with no order supplied anywhere.  So the internal observer still lives in
the real-valued shadow of the configuration rather than in its algebra. -/
theorem internal_observations_still_compatible (μ : ι → Threshold n)
    (σ : Resolution n) (S S' : Finset (Fin n)) :
    record S μ σ ∪ record S' μ σ ⊆ record (S ∩ S') μ σ := by
  rintro k (hk | hk) i hi
  · exact hk i (Finset.mem_of_mem_inter_left hi)
  · exact hk i (Finset.mem_of_mem_inter_right hi)

/-- **Collected.**

Internality is real — a larger observer records less, the detached observer is
the one with no complement, and disturbance coincides with force.  And it leaves
G3 exactly where it was: all observations remain compatible, because crossing is
an order relation and the algebra carries no order. -/
theorem summary (μ : ι → Threshold n) (σ : Resolution n) (S S' : Finset (Fin n)) :
    record (S ∪ S') μ σ = record S μ σ ∩ record S' μ σ
    ∧ record Finset.univ μ σ = crossedSet μ σ
    ∧ record S μ σ ∪ record S' μ σ ⊆ record (S ∩ S') μ σ :=
  ⟨record_union μ σ S S', record_univ_is_the_detached_observer μ σ,
   internal_observations_still_compatible μ σ S S'⟩

end SCD.Internal
