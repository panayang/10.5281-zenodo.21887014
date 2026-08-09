/-
# Confinement, and why charge comes in thirds

`Defect.lean` gave a defect a single integer: the winding of the scale around
it.  That was incomplete.  If the defect sits in a **degenerate block** — a set
of directions carrying the same local unit — then going once around it, the
scale need not only shift; the *labels of the block may also be permuted*,
because within a block the labels are not physical (`Gauge.sameOrbit_iff_eq_scale`).

So the monodromy of a defect is a pair: a winding **and** a block permutation.
Nothing here is copied from gauge theory; the permutation is forced by the fact
that a degenerate block has no preferred labelling.

Everything below follows from asking when such a configuration is globally
consistent — when the labelling closes up after the loop.

* `confinement` — a defect whose monodromy permutes the block **cannot exist
  alone**.  It is not that a force grows with distance; the configuration is
  simply not single-valued.
* `bound_state_size` — the smallest consistent combination has exactly
  `order(π)` constituents.  For a block of size `n` cycled once, that is `n`.
  **Baryon number is the block size.**
* `pair_observable` — a defect together with its opposite is always consistent:
  mesons need no special explanation.
* `no_partial_state` — fewer than `n` constituents is never consistent, so
  there are no two-quark hadrons.
* `constituent_charge_fraction` — each of the `n` constituents carries exactly
  `1/n` of the bound state's charge.  **Charge comes in `n`ths.**

With `n = 3` this is the observed pattern: three constituents per bound state,
none observable alone, charges in thirds.  The framework does not put the
number 3 in — it puts in "a degeneracy block of size `n`" and gets `n`
constituents and `1/n` charges out.  Which `n` nature chose is not derived;
that would require deriving the scale pattern itself.
-/
import ScaleUniverse.Gauge
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs

namespace ScaleUniverse.Color

open Finset

variable {n : ℕ}

/-! ## Monodromy of a defect in a degenerate block -/

/-- The **monodromy** of a defect that sits in a degenerate block: going once
around it, the scale winds *and* the block labels may be permuted.  Both are
forced — the winding by discrete scale invariance, the permutation by the
absence of a preferred labelling inside a block. -/
structure BlockMonodromy (n : ℕ) where
  /-- How the block labels are permuted on one circuit. -/
  perm : Equiv.Perm (Fin n)
  /-- How much the scale winds, per direction. -/
  wind : Fin n → ℤ

namespace BlockMonodromy

/-- Bringing two defects together composes their monodromies. -/
def comp (M N : BlockMonodromy n) : BlockMonodromy n where
  perm := M.perm * N.perm
  wind := fun a => M.wind a + N.wind a

/-- The opposite defect: reversed circuit. -/
def anti (M : BlockMonodromy n) : BlockMonodromy n where
  perm := M.perm⁻¹
  wind := fun a => -M.wind a

/-- The vacuum. -/
def triv (n : ℕ) : BlockMonodromy n where
  perm := 1
  wind := fun _ => 0

/-- Total scale winding — the charge. -/
def charge (M : BlockMonodromy n) : ℤ := ∑ a, M.wind a

@[simp] theorem comp_perm (M N : BlockMonodromy n) : (M.comp N).perm = M.perm * N.perm := rfl
@[simp] theorem anti_perm (M : BlockMonodromy n) : M.anti.perm = M.perm⁻¹ := rfl
@[simp] theorem triv_perm : (triv n).perm = 1 := rfl

@[simp] theorem charge_comp (M N : BlockMonodromy n) :
    (M.comp N).charge = M.charge + N.charge := by
  simp only [charge, comp, Finset.sum_add_distrib]

@[simp] theorem charge_anti (M : BlockMonodromy n) : M.anti.charge = -M.charge := by
  simp only [charge, anti, Finset.sum_neg_distrib]

/-! ## Consistency

A configuration is physically realisable only if the labelling of the block
closes up after the circuit.  If it does not, the field is not single-valued
and the configuration does not describe anything. -/

/-- A configuration is **observable** when its block labelling closes up. -/
def Observable (M : BlockMonodromy n) : Prop := M.perm = 1

@[simp] theorem triv_observable : Observable (triv n) := rfl

/-- **Confinement.**

A defect whose monodromy genuinely permutes the block cannot exist on its own.
This is not a force that grows with separation — the isolated configuration is
simply not single-valued, so there is nothing there to separate. -/
theorem confinement (M : BlockMonodromy n) (h : M.perm ≠ 1) : ¬ Observable M := h

/-- **Mesons are free.**  A defect together with its opposite always closes up,
whatever the block permutation is.  No condition on `n`, no fine-tuning. -/
@[simp] theorem pair_observable (M : BlockMonodromy n) : Observable (M.comp M.anti) := by
  simp only [Observable, comp_perm, anti_perm, mul_inv_cancel]

/-- The pair carries zero charge, as it must. -/
@[simp] theorem pair_charge (M : BlockMonodromy n) : (M.comp M.anti).charge = 0 := by
  simp only [charge_comp, charge_anti, add_neg_cancel]

/-! ## Bound states of identical defects -/

/-- Bringing together `k` copies of the same defect. -/
def rep (M : BlockMonodromy n) : ℕ → BlockMonodromy n
  | 0 => triv n
  | k + 1 => M.comp (rep M k)

@[simp] theorem rep_perm (M : BlockMonodromy n) (k : ℕ) : (rep M k).perm = M.perm ^ k := by
  induction k with
  | zero => simp only [rep, triv_perm, pow_zero]
  | succ m ih => simp only [rep, comp_perm, ih, pow_succ']

@[simp] theorem rep_charge (M : BlockMonodromy n) (k : ℕ) :
    (rep M k).charge = (k : ℤ) * M.charge := by
  induction k with
  | zero => simp only [rep, charge, triv, Finset.sum_const_zero, Nat.cast_zero, zero_mul]
  | succ m ih =>
      simp only [rep, charge_comp, ih]
      push_cast
      ring

/-- **The size of a bound state is the order of its monodromy.**

`k` copies close up exactly when `π^k = 1`.  For a defect that cycles a block of
size `n` once, the smallest consistent number of constituents is `n`:
**baryon number is the block size**, not an extra quantum number. -/
theorem bound_state_observable (M : BlockMonodromy n) (k : ℕ)
    (h : M.perm ^ k = 1) : Observable (rep M k) := by
  simp only [Observable, rep_perm, h]

theorem bound_state_size (M : BlockMonodromy n) (hord : orderOf M.perm = n) :
    Observable (rep M n) := by
  refine bound_state_observable M n ?_
  have h := pow_orderOf_eq_one M.perm
  rwa [hord] at h

/-- **No partial hadrons.**

Fewer constituents than the block size never closes up.  With `n = 3`: a single
constituent is unobservable, two are unobservable, three are observable.  The
absence of two-quark hadrons is not an extra rule. -/
theorem no_partial_state (M : BlockMonodromy n) (hord : orderOf M.perm = n)
    (k : ℕ) (hk : 0 < k) (hkn : k < n) : ¬ Observable (rep M k) := by
  simp only [Observable, rep_perm]
  intro hcon
  have hle : orderOf M.perm ≤ k := orderOf_le_of_pow_eq_one hk hcon
  rw [hord] at hle
  exact absurd hle (not_le.mpr hkn)

/-! ## Charge comes in `n`ths -/

/-- **Each constituent carries `1/n` of the bound state's charge.**

The bound state's charge is `n` times a constituent's.  So if observable charge
is normalised to integers — which it must be, being the charge of an observable
state — then constituent charges lie in `(1/n)ℤ`.

With `n = 3` this is charge quantisation in thirds.  The framework does not
insert the number 3: it inserts "a degeneracy block of size `n`", and the
fraction is `1/n`. -/
theorem constituent_charge_fraction (M : BlockMonodromy n) :
    (rep M n).charge = (n : ℤ) * M.charge :=
  rep_charge M n

/-- Stated as a fraction: the constituent carries `1/n` of the observable
charge. -/
theorem constituent_charge_rat (M : BlockMonodromy n) (hn : 0 < n) :
    (M.charge : ℚ) = (1 / (n : ℚ)) * ((rep M n).charge : ℚ) := by
  rw [constituent_charge_fraction]
  have hne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  push_cast
  rw [one_div, inv_mul_cancel_left₀ hne]

/-- An observable bound state of `n` identical constituents has charge divisible
by `n`; a single constituent need not, which is exactly what "fractional charge"
means. -/
theorem bound_charge_divisible (M : BlockMonodromy n) :
    (n : ℤ) ∣ (rep M n).charge := ⟨M.charge, constituent_charge_fraction M⟩

end BlockMonodromy

end ScaleUniverse.Color
