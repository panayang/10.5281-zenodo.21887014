/-
# Resolution without an order: the observer reaches the algebra

`Audit` §V.s registered G3 — the observer never touches the algebra — and §V.t
named the reason: `Observer.Crossed` compares *values*, `μ i ≤ σ i`, and the
framework's scale algebra is a `Ring` with no order supplied anywhere.  §V.t also
named the obvious repair, idempotents, and **declined it**: non-commuting
projections are the standard quantum construction and adopting them would be
importing the answer.

Two things are worth saying before anything is built.

**It is not an accident of `Observer.lean`.**  `Emergence.resolved μ t = {k | μ k ≤ t}`
compares reals too, so the whole notion of resolution in the development lives in
a real-valued shadow of the configuration.  G3 is in the framework's oldest
account of content, not only in its newest account of observers.

**And what has to change is the word "resolved", not the word "observer".**  An
observer that reaches the algebra needs *resolution* to be algebraic; everything
else follows.

## What a resolution can be, with no order

A decreasing family of two-sided ideals, given by membership: `mem k a` says `a`
is **invisible** at resolution `k`, and a finer resolution misses less.  No `≤`
on the ring appears anywhere.  `Resolved k a` is `¬ mem k a`, and
`resolved_mono` is `Emergence.resolved_mono` with the real comparison removed —
content only grows.

## The point: incompatibility is a commutator read at a resolution

    `Compatible F k a b  :=  F.mem k (ad a b)` .

Two things are jointly resolvable when their failure to commute is invisible.
**Nothing is imported.**  `Quantum.ad` was already the framework's word for the
failure to commute, `Triple.influence_asymmetry` already made the discrepancy
between two readings of one observation equal to it, and `Ordering.lean` already
found the same object obstructing a canonical lift.  What is added here is only
the resolution at which it is read.

`commutative_all_compatible`: over a commutative ring every pair is compatible at
every resolution.  The classical limit is not imposed — it is what the definition
gives when the ring commutes.

## Non-vacuity, at both ends

* `sharp` is the finest resolution, where only zero is invisible, and
  `incompatible_witness` exhibits an incompatible pair there:
  `Triple.crossedScale`'s two directional gradients, whose commutator
  `Triple.asymmetry_witness` shows is non-zero;
* `powerFiltration` has layers — what a probe of order `k` misses is what `xᵏ`
  divides — and `compatible_at_zero` says the **coarsest** probe sees no
  incompatibility at all.

So incompatibility is not a property of a pair.  It is a property of a pair **at
a resolution**, which is what putting it in a filtration was for, and it is the
first thing in the development that behaves like a measurement without being
built from a projection.

## What this does not do, and the list is not short

* **The filtration is postulated.**  Nothing in A1–A7 supplies one, so this is
  §V.b's category exactly: a structure carrying theorems the framework does not
  build.  It is registered as such and not dressed as a consequence;
* **no link to `Emergence.resolved`.**  That notion has real thresholds and this
  one has ideals, and nothing connects them — the same shape of gap as
  `Spectrum.gaps` against `Internal.record`, and the same kind of work would
  close it.  Until it is closed, this is an algebraic notion of resolution
  standing beside the framework's real-valued one rather than replacing it;
* **the layers are not exercised.**  Incompatibility is shown at the sharpest
  resolution and its absence at the coarsest; that incompatibility *appears* at
  some finite order in a concrete ring is not shown, and that is the statement
  with physical content;
* **no probability, no outcomes, no process.**  G4 is untouched.  `Compatible`
  says when two things can be jointly resolved, not what is obtained when they
  are.

**So G3 narrows and does not close.**  What is new is that "resolved" has a form
the algebra can carry, and that incompatibility arrives as the framework's own
commutator rather than as an imported lattice.  What is not new is that the
observer is still a structure the axioms do not supply.
-/
import SCD.Amendment
import SCD.Triple

namespace SCD.Resolution

open SCD ScaleAlgebra Quantum


open SCD ScaleAlgebra Quantum

variable {A : Type*} [Ring A]

/-- **What a resolution cannot see.**

A decreasing family of two-sided ideals, given by membership so that no order on
the ring is needed: `mem k a` says `a` is invisible at resolution `k`, and a
finer resolution has less it cannot see. -/
structure Filtration (A : Type*) [Ring A] where
  /-- `mem k a` : `a` is invisible at resolution `k`. -/
  mem : ℕ → A → Prop
  zero_mem : ∀ k, mem k 0
  add_mem : ∀ k a b, mem k a → mem k b → mem k (a + b)
  neg_mem : ∀ k a, mem k a → mem k (-a)
  mul_left : ∀ k a b, mem k b → mem k (a * b)
  mul_right : ∀ k a b, mem k a → mem k (a * b)
  /-- A finer resolution sees more, so what it misses is less. -/
  antitone : ∀ k l : ℕ, k ≤ l → ∀ a, mem l a → mem k a

namespace Filtration

variable (F : Filtration A)

/-- **Resolved**: visible at resolution `k`.  No `≤` on the ring appears. -/
def Resolved (k : ℕ) (a : A) : Prop := ¬ F.mem k a

/-- **Content only grows**, which is `Emergence.resolved_mono` with the real
comparison removed. -/
theorem resolved_mono {k l : ℕ} (h : k ≤ l) {a : A} (ha : F.Resolved k a) :
    F.Resolved l a := fun hl => ha (F.antitone k l h a hl)

/-- Nothing resolves the zero of the ring. -/
theorem not_resolved_zero (k : ℕ) : ¬ F.Resolved k (0 : A) := fun h => h (F.zero_mem k)

/-- **Jointly resolvable**: the failure of `a` and `b` to commute is invisible.

This is the whole of the proposal.  Incompatibility is not a lattice of
projections imported from somewhere else — it is `Quantum.ad`, the framework's
own word for the failure to commute, read at a resolution. -/
def Compatible (k : ℕ) (a b : A) : Prop := F.mem k (ad a b)

theorem compatible_symm {k : ℕ} {a b : A} (h : F.Compatible k a b) :
    F.Compatible k b a := by
  have : ad b a = -(ad a b) := by simp only [ad]; noncomm_ring
  rw [Compatible, this]
  exact F.neg_mem k _ h

/-- **A coarser resolution cannot see an incompatibility a finer one misses.** -/
theorem compatible_of_le {k l : ℕ} (h : k ≤ l) {a b : A} (hl : F.Compatible l a b) :
    F.Compatible k a b := F.antitone k l h _ hl

end Filtration

/-- **In the commutative sector everything is compatible, at every resolution.**

The classical limit is not imposed; it is what the definition gives when the ring
commutes. -/
theorem commutative_all_compatible {B : Type*} [CommRing B] (F : Filtration B)
    (k : ℕ) (a b : B) : F.Compatible k a b := by
  have : ad a b = 0 := by simp only [ad, mul_comm, sub_self]
  rw [Filtration.Compatible, this]
  exact F.zero_mem k

/-! ## Non-vacuity -/

/-- The sharpest resolution: only zero is invisible. -/
def sharp (A : Type*) [Ring A] : Filtration A where
  mem _ a := a = 0
  zero_mem _ := rfl
  add_mem _ a b ha hb := by rw [ha, hb, add_zero]
  neg_mem _ a ha := by rw [ha, neg_zero]
  mul_left _ a b hb := by rw [hb, mul_zero]
  mul_right _ a b ha := by rw [ha, zero_mul]
  antitone _ _ _ _ h := h

/-- **And there are incompatible pairs.**

`Triple.matrixScaleAlgebra`'s crossed scale has a non-zero commutator, so at the
sharpest resolution the two directional gradients are not jointly resolvable.
The notion is not empty. -/
theorem incompatible_witness :
    ¬ (sharp (Triple.Mat 2)).Compatible 0
        (d (0 : Fin 2) (Triple.crossedScale 0)) (d (1 : Fin 2) (Triple.crossedScale 0)) :=
  Triple.asymmetry_witness

/-- **A filtration with layers**: what a probe of order `k` misses is what is
divisible by `xᵏ`, for a central `x`.

`sharp` has no layers and so no notion of a *coarse* probe; this one has, and it
is the shape the framework's own tower already has — `Newton.Dual` resolves to
first order because `ε² = 0`. -/
def powerFiltration (x : A) (hx : ∀ y : A, x * y = y * x) : Filtration A where
  mem k a := ∃ b, a = x ^ k * b
  zero_mem k := ⟨0, by rw [mul_zero]⟩
  add_mem k a b := by
    rintro ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u + v, by rw [mul_add]⟩
  neg_mem k a := by
    rintro ⟨u, rfl⟩
    exact ⟨-u, by rw [mul_neg]⟩
  mul_left k a b := by
    rintro ⟨u, rfl⟩
    refine ⟨a * u, ?_⟩
    have hpow : ∀ y : A, x ^ k * y = y * x ^ k := fun y => by
      induction k with
      | zero => simp
      | succ m ih => rw [pow_succ, mul_assoc, hx, ← mul_assoc, ih, mul_assoc]
    rw [← mul_assoc, ← hpow a, mul_assoc]
  mul_right k a b := by
    rintro ⟨u, rfl⟩
    exact ⟨u * b, by rw [mul_assoc]⟩
  antitone k l hkl a := by
    rintro ⟨u, rfl⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkl
    exact ⟨x ^ m * u, by rw [pow_add, mul_assoc]⟩

/-- **The coarsest probe sees no incompatibility.**

At order zero everything is divisible by `x⁰ = 1`, so every pair is jointly
resolvable.  Incompatibility is therefore not a property of a pair — it is a
property of a pair *at a resolution*, which is what having it live in a
filtration was for. -/
theorem compatible_at_zero (x : A) (hx : ∀ y : A, x * y = y * x) (a b : A) :
    (powerFiltration x hx).Compatible 0 a b := ⟨ad a b, by rw [pow_zero, one_mul]⟩


end SCD.Resolution
