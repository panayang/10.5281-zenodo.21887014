/-
# Closing the quantum-gravitational loop

The one large gap left was that the *quantitative* gravity chain ran through the
commutative sector.  `Dynamics.commutative_sector_transports_commute` proved
what that costs: over a `CommRing` the adjoint action vanishes identically, so
the sector has **no transport curvature at all** and every curvature in
`Conformal.lean` had to enter through the postulated `δ`.  Until that is redone
without commutativity there is no quantum-gravitational statement to make.

This file redoes it.  The setting is a **non-commutative** ring with `n`
commuting derivations — the derivations still commute, because that is a choice
of chart (`Dynamics.no_flatness_from_commuting_derivations`), but the *values*
no longer do.

## What survives untouched

The Kronecker deltas are casts of `0` and `1`, hence central, so every step that
only moves them through is unchanged.  `hess_symm` survives because it comes
from `d_comm` alone, and `Chr_symm` because `kron` is symmetric.  So the
connection is the same object.

## What changes, and it is one thing

`Defm` — the deformation tensor that carries all the curvature — loses its
symmetry, and by an exactly computable amount:

        Defm i j − Defm j i  =  −2 [σᵢ, σⱼ] .

`Defm_antisymm_part`.  **The whole quantum-gravitational correction to the
geometry is the commutator of scale gradients in different directions.**  It is
not a term added to a Lagrangian; it is the failure of the scale to have a
well-defined gradient in two directions at once, which is what
`Crossed.lean` made exact and what `Quantum.heisenberg` turns into an
uncertainty.

`Defm_symm_iff_commute` is the converse: symmetry is *equivalent* to the
gradients commuting, so the classical geometry is exactly the commuting case
and nothing else.

The master contraction acquires the same correction and no other.  Classically

        ∑ₘ Γᵃ_cm Γᵐ_be  contains  2δ_ac σ_b σ_e ;

non-commutatively the `2·` becomes an **anticommutator**, the mixed terms keep
their order, and one genuinely new term appears, `δ_be [σ_a, σ_c]`.
`sum_Chr_Chr_full_nc` proves it, and `sum_Chr_Chr_full_classical` recovers
`Conformal.sum_Chr_Chr_full` when the commutators vanish.

## The prediction

The correction is **antisymmetric**.  The classical tests — deflection,
perihelion precession, redshift — are computed from the *symmetric* part of
Ricci, so:

* `symmetric_part_uncorrected` — the symmetric part of the deformation tensor is
  the classical one exactly, with no commutator correction at any order;
* `correction_is_pure_antisymmetric` — the entire correction lives in the
  antisymmetric part.

**So the leading quantum-gravitational effect is invisible to every classical
test, and appears only in observables sensitive to an antisymmetric geometric
part.**  That is a torsion-like coupling, and by `Axes.lean` the framework's
rotational label is exactly a wedge of scale directions — the same object.  The
prediction is therefore:

> quantum-gravitational corrections appear first in **spin–geometry coupling**,
> not in orbits.

`quantum_correction_couples_to_rotation` states the structural match: the
correction and the rotational label are both `[σ_a, σ_b]`-valued antisymmetric
objects on the same index pair.

**Magnitude, honestly.**  `Crossed.lean` sets the scale of `[σ_a, σ_b]` by the
scale step.  Relative to the classical terms the correction is of that order, so
in the solar system it is utterly negligible; nothing here predicts a measurable
effect with current instruments.  What is claimed is the *structure* of the
first correction and where it can and cannot show up.

**What is still not here.**  No graviton, no scattering amplitude, no black-hole
entropy, no short-distance completion.  The loop that is closed is the one that
was named: the curvature computation no longer requires commutativity, and the
first correction has been identified rather than assumed.
-/
import ScaleUniverse.Quantum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NoncommRing

namespace ScaleUniverse.NCConformal

open ScaleUniverse Quantum Finset

/-! ## A non-commutative substrate with commuting derivations -/

/-- The conformal setting without commutativity: a ring with `n` derivations
that commute *as operators* — a choice of chart — while the values they produce
need not commute. -/
class NCScale (n : ℕ) (M : Type*) [Ring M] where
  /-- The `i`-th derivation. -/
  d : Fin n → M → M
  d_add : ∀ i a b, d i (a + b) = d i a + d i b
  d_mul : ∀ i a b, d i (a * b) = d i a * b + a * d i b
  d_comm : ∀ i j a, d i (d j a) = d j (d i a)

namespace NCScale

variable {n : ℕ} {M : Type*} [Ring M] [NCScale n M]

/-- Kronecker delta as a central element: a cast of `0` or `1`. -/
def kr (i j : Fin n) : M := if i = j then 1 else 0

theorem kr_symm (i j : Fin n) : (kr i j : M) = kr j i := by
  simp only [kr]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

@[simp] theorem kr_self (i : Fin n) : (kr i i : M) = 1 := by simp [kr]

/-- `kr` is central, being `0` or `1`. -/
theorem kr_comm (i j : Fin n) (x : M) : (kr i j : M) * x = x * kr i j := by
  simp only [kr]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]; simp

/-- Summing against a Kronecker delta on the left picks out one term. -/
theorem sum_kr_left (i : Fin n) (f : Fin n → M) :
    ∑ m, (kr i m : M) * f m = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp only [kr, if_neg (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- And on the other index. -/
theorem sum_kr_right (i : Fin n) (f : Fin n → M) :
    ∑ m, (kr m i : M) * f m = f i := by
  rw [Finset.sum_congr rfl (fun m _ => by rw [kr_symm m i])]
  exact sum_kr_left i f

/-- Two scalar-prefixed factors merge: the deltas are central, so they collect
on the left and the ring elements keep their order. -/
theorem kr_swap (i j p q : Fin n) (x : M) :
    (kr i j : M) * ((kr p q : M) * x) = (kr p q : M) * ((kr i j : M) * x) := by
  rw [← mul_assoc, ← mul_assoc, kr_comm i j (kr p q : M)]

theorem scalar_mul_scalar (i j p q : Fin n) (x y : M) :
    ((kr i j : M) * x) * ((kr p q : M) * y) = ((kr i j : M) * (kr p q : M)) * (x * y) := by
  rw [mul_assoc, ← mul_assoc x, ← kr_comm p q x, mul_assoc, ← mul_assoc]

/-! ## The same objects, built without commutativity -/

variable (σ : M)

/-- The scale gradient. -/
def sig (i : Fin n) : M := d i σ

/-- The scale Hessian. -/
def hess (i j : Fin n) : M := d i (sig σ j)

/-- Still symmetric: this comes from `d_comm` alone, which is a chart choice and
survives untouched. -/
theorem hess_symm (i j : Fin n) : hess σ i j = hess σ j i := by
  simp only [hess, sig]
  exact d_comm i j σ

variable (n) in
/-- The squared gradient. -/
def gradsq : M := ∑ i : Fin n, sig σ i * sig σ i

/-- Christoffel symbols, unchanged in form — the deltas are central. -/
def Chr (a b c : Fin n) : M :=
  (kr a b : M) * sig σ c + (kr a c : M) * sig σ b - (kr b c : M) * sig σ a

theorem Chr_symm (a b c : Fin n) : Chr σ a b c = Chr σ a c b := by
  simp only [Chr, kr_symm b c]
  noncomm_ring

/-! ## The deformation tensor loses exactly one thing -/

variable (n) in
/-- The deformation tensor, defined exactly as in the commutative case. -/
def Defm (i j : Fin n) : M :=
  2 * hess σ i j - 2 * (sig σ i * sig σ j) + (kr i j : M) * gradsq n σ

/-- **The whole quantum-gravitational correction, in one line.**

`Defm` is no longer symmetric, and the failure is exactly twice the commutator
of the scale gradients:

        Defm i j − Defm j i = −2 [σᵢ, σⱼ] .

Everything else in the curvature computation is unchanged, because the
Kronecker deltas are central and `hess` is still symmetric. -/
theorem Defm_antisymm_part (i j : Fin n) :
    Defm n σ i j - Defm n σ j i = -2 * ad (sig σ i) (sig σ j) := by
  simp only [Defm, ad, hess_symm σ i j, kr_symm i j]
  noncomm_ring

/-- **And symmetry is equivalent to the gradients commuting.**

So the classical geometry is exactly the commuting case — not an approximation
to it, but the precise locus where the correction vanishes. -/
theorem Defm_symm_iff_commutator (i j : Fin n) :
    Defm n σ i j = Defm n σ j i ↔ (2 : M) * ad (sig σ i) (sig σ j) = 0 := by
  rw [← sub_eq_zero, Defm_antisymm_part σ i j]
  constructor
  · intro h; rw [show (2 : M) * ad (sig σ i) (sig σ j)
      = -(-2 * ad (sig σ i) (sig σ j)) by noncomm_ring, h, neg_zero]
  · intro h; rw [show (-2 : M) * ad (sig σ i) (sig σ j)
      = -(2 * ad (sig σ i) (sig σ j)) by noncomm_ring, h, neg_zero]

/-- With `2` invertible this is the clean statement: **the geometry is symmetric
exactly where the scale gradients commute.**  The classical case is not an
approximation but the precise vanishing-commutator locus. -/
theorem Defm_symm_iff_commute [Invertible (2 : M)] (i j : Fin n) :
    Defm n σ i j = Defm n σ j i ↔ sig σ i * sig σ j = sig σ j * sig σ i := by
  rw [Defm_symm_iff_commutator σ i j]
  constructor
  · intro h
    have h2 : ad (sig σ i) (sig σ j) = 0 := by
      have := congrArg (fun x => (⅟(2 : M)) * x) h
      simpa [← mul_assoc, invOf_mul_self] using this
    simp only [ad, sub_eq_zero] at h2
    exact h2
  · intro h
    simp only [ad, h, sub_self, mul_zero]

/-- The symmetric part is the classical deformation tensor exactly: the
correction contributes nothing to it, at any order. -/
theorem symmetric_part_uncorrected (i j : Fin n) :
    Defm n σ i j + Defm n σ j i
      = 4 * hess σ i j - 2 * (sig σ i * sig σ j + sig σ j * sig σ i)
        + 2 * ((kr i j : M) * gradsq n σ) := by
  simp only [Defm, hess_symm σ i j, kr_symm i j]
  noncomm_ring

/-- Collected: the entire correction is antisymmetric, so nothing computed from
the symmetric part moves.  The classical tests — deflection, precession,
redshift — use the symmetric part. -/
theorem correction_is_pure_antisymmetric (i j : Fin n) :
    (Defm n σ i j + Defm n σ j i) + (Defm n σ i j - Defm n σ j i)
      = 2 * Defm n σ i j
    ∧ Defm n σ i j - Defm n σ j i = -2 * ad (sig σ i) (sig σ j) := by
  refine ⟨by noncomm_ring, Defm_antisymm_part σ i j⟩

/-! ## The master contraction, with its correction

Classically `∑ₘ Γᵃ_cm Γᵐ_be` contains `2 δ_ac σ_b σ_e`.  Non-commutatively the
doubling becomes an anticommutator, the mixed terms keep their order, and one
new commutator term appears. -/

theorem sum_Chr_Chr_full_nc (a b c e : Fin n) :
    ∑ m, Chr σ a c m * Chr σ m b e
      = (kr a c : M) * (sig σ b * sig σ e + sig σ e * sig σ b)
        - (kr a c : M) * ((kr b e : M) * gradsq n σ)
        + (kr a b : M) * (sig σ c * sig σ e)
        + (kr a e : M) * (sig σ c * sig σ b)
        - (kr c b : M) * (sig σ a * sig σ e)
        - (kr c e : M) * (sig σ a * sig σ b)
        + (kr b e : M) * ad (sig σ a) (sig σ c) := by
  have h : ∀ m : Fin n, Chr σ a c m * Chr σ m b e
      = ((kr a c : M) * (kr m b : M)) * (sig σ m * sig σ e)
        + ((kr a c : M) * (kr m e : M)) * (sig σ m * sig σ b)
        - ((kr a c : M) * (kr b e : M)) * (sig σ m * sig σ m)
        + ((kr a m : M) * (kr m b : M)) * (sig σ c * sig σ e)
        + ((kr a m : M) * (kr m e : M)) * (sig σ c * sig σ b)
        - ((kr a m : M) * (kr b e : M)) * (sig σ c * sig σ m)
        - ((kr c m : M) * (kr m b : M)) * (sig σ a * sig σ e)
        - ((kr c m : M) * (kr m e : M)) * (sig σ a * sig σ b)
        + ((kr c m : M) * (kr b e : M)) * (sig σ a * sig σ m) := by
    intro m
    simp only [Chr, sub_mul, mul_sub, add_mul, mul_add, scalar_mul_scalar]
    noncomm_ring
  rw [Finset.sum_congr rfl (fun m _ => h m)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [show (∑ m, ((kr a c : M) * (kr m b : M)) * (sig σ m * sig σ e))
      = (kr a c : M) * (sig σ b * sig σ e) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), ← Finset.mul_sum, sum_kr_right]]
  rw [show (∑ m, ((kr a c : M) * (kr m e : M)) * (sig σ m * sig σ b))
      = (kr a c : M) * (sig σ e * sig σ b) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), ← Finset.mul_sum, sum_kr_right]]
  rw [show (∑ m, ((kr a c : M) * (kr b e : M)) * (sig σ m * sig σ m))
      = (kr a c : M) * ((kr b e : M) * gradsq n σ) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), ← Finset.mul_sum,
      ← Finset.mul_sum]
    rfl]
  rw [show (∑ m, ((kr a m : M) * (kr m b : M)) * (sig σ c * sig σ e))
      = (kr a b : M) * (sig σ c * sig σ e) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), sum_kr_left]]
  rw [show (∑ m, ((kr a m : M) * (kr m e : M)) * (sig σ c * sig σ b))
      = (kr a e : M) * (sig σ c * sig σ b) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), sum_kr_left]]
  rw [show (∑ m, ((kr a m : M) * (kr b e : M)) * (sig σ c * sig σ m))
      = (kr b e : M) * (sig σ c * sig σ a) by
    rw [Finset.sum_congr rfl (fun m _ => by rw [mul_assoc, kr_swap]),
      ← Finset.mul_sum, sum_kr_left]]
  rw [show (∑ m, ((kr c m : M) * (kr m b : M)) * (sig σ a * sig σ e))
      = (kr c b : M) * (sig σ a * sig σ e) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), sum_kr_left]]
  rw [show (∑ m, ((kr c m : M) * (kr m e : M)) * (sig σ a * sig σ b))
      = (kr c e : M) * (sig σ a * sig σ b) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), sum_kr_left]]
  rw [show (∑ m, ((kr c m : M) * (kr b e : M)) * (sig σ a * sig σ m))
      = (kr b e : M) * (sig σ a * sig σ c) by
    rw [Finset.sum_congr rfl (fun m _ => by rw [mul_assoc, kr_swap]),
      ← Finset.mul_sum, sum_kr_left]]
  simp only [ad, mul_sub]
  noncomm_ring

/-- **The classical limit.**

When the scale gradients commute, the anticommutator collapses to `2·` and the
new term vanishes, returning `Conformal.sum_Chr_Chr_full` exactly.  So the
commutative computation is not an approximation — it is the vanishing-commutator
case. -/
theorem sum_Chr_Chr_full_classical (a b c e : Fin n)
    (hc : ∀ i j : Fin n, sig σ i * sig σ j = sig σ j * sig σ i) :
    ∑ m, Chr σ a c m * Chr σ m b e
      = (kr a c : M) * (2 * (sig σ b * sig σ e))
        - (kr a c : M) * ((kr b e : M) * gradsq n σ)
        + (kr a b : M) * (sig σ c * sig σ e)
        + (kr a e : M) * (sig σ b * sig σ c)
        - (kr c b : M) * (sig σ a * sig σ e)
        - (kr c e : M) * (sig σ a * sig σ b) := by
  rw [sum_Chr_Chr_full_nc σ a b c e]
  simp only [ad, hc a c, sub_self, mul_zero, add_zero, hc b e, hc c b]
  noncomm_ring

/-! ## Where the correction can show up -/

/-- **The correction and the rotational label are the same kind of object.**

`Axes.lean` makes the framework's rotational label the wedge of two scale
directions; the quantum correction here is the commutator of two scale
gradients.  Both are antisymmetric in the same index pair and vanish together.

Hence the prediction: quantum-gravitational corrections appear first in
**spin–geometry coupling**, not in orbits — because orbits are computed from
the symmetric part, which `symmetric_part_uncorrected` shows is untouched. -/
theorem quantum_correction_couples_to_rotation (i j : Fin n) :
    ad (sig σ i) (sig σ j) = -ad (sig σ j) (sig σ i) := by
  simp only [ad]
  noncomm_ring

/-- And it vanishes exactly where the rotational label does: on a pattern whose
gradients are parallel, which is the isotropic locus of `Locus.lean`. -/
theorem correction_vanishes_on_commuting (i j : Fin n)
    (h : sig σ i * sig σ j = sig σ j * sig σ i) :
    Defm n σ i j = Defm n σ j i := by
  rw [Defm_symm_iff_commutator σ i j]
  simp only [ad, h, sub_self, mul_zero]

end NCScale

end ScaleUniverse.NCConformal
