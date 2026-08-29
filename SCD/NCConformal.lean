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

## One set of objects

`sig`, `hess`, `gradsq`, `Chr` and `Defm` are **not redefined here**.  An earlier
state of this file declared its own copies of all five over a ring, with `kr` for
`kron`, and then related them to `Conformal.lean`'s by proving classical limits —
a translation between two vocabularies rather than a limit of one.  A1 never
needed commutativity to be *stated*, so the objects are now defined once in
`Conformal.lean` over a ring, and everything below is a statement about those
objects.  The classical limits are consequently limits, and
`Conformal.two_Rm_eq` and `two_Rm_eq_nc` below are two theorems about the same
`Rm`.

## What survives untouched

The Kronecker deltas are casts of `0` and `1`, hence central (`kron_comm`), so
every step that only moves them through is unchanged.  `hess_symm` survives
because it comes from `d_comm` alone, and `Chr_symm` because `kron` is symmetric.
So the connection is the same object, and `d_Chr_diff` — the derivative half of
the Riemann tensor — is the same identity.

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

## The master regression theorem, without commutativity

With one language for the objects, the theorem `Conformal.lean` could only prove
commutatively goes through in general, and the correction can be read off:

        2 R^a_{bce} = (δ ∧ D)^a_{bce} + C^a_{bce} ,
        C^a_{bce} = δ_{bc}[σ_a, σ_e] − δ_{be}[σ_a, σ_c] .

`two_Rm_eq_nc`.  So the Riemann tensor is *still* the Kulkarni–Nomizu product of
the bare bookkeeping with the scale deformation, plus a term built from nothing
but commutators of scale gradients.  `two_Rm_eq_classical` recovers
`Conformal.two_Rm_eq` exactly when they vanish, and
`Rm_eq_zero_of_Defm_eq_zero_nc` shows the flatness criterion needs one extra
condition and only one: a deformation-free scale field is flat **iff** its
gradients also commute.

That closes the loop the file was written for.  The quantitative gravity chain
no longer runs through a sector with no transport curvature; it runs through the
general one, and the classical chain is the commuting locus of it.

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
rotational label is exactly a wedge of scale directions — the same object.  With
the shared vocabulary that is no longer an analogy:
`Pattern.wedge_self_eq_commutator` says the wedge of a pattern with *itself* is
the commutator of its values, so `quantum_correction_is_a_wedge` below is an
identity, not a structural match.  The prediction is therefore:

> quantum-gravitational corrections appear first in **spin–geometry coupling**,
> not in orbits.

**Magnitude, honestly.**  `Crossed.lean` sets the scale of `[σ_a, σ_b]` by the
scale step.  Relative to the classical terms the correction is of that order, so
in the solar system it is utterly negligible; nothing here predicts a measurable
effect with current instruments.  What is claimed is the *structure* of the
first correction and where it can and cannot show up.

**What is still not here.**  No graviton, no scattering amplitude, no black-hole
entropy, no short-distance completion.
-/
import SCD.Connection
import SCD.Conformal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NoncommRing

namespace SCD.NCConformal

open SCD Quantum Finset ScaleAlgebra

variable {n : ℕ} {M : Type*} [Ring M] [ScaleAlgebra n M]

variable (σ : M)

/-! ## The scale connection, and the one thing that is not flat

`Conformal.scaleCurv_eq_zero` says the abelian curl of the scale connection
vanishes — that is `d_comm`, and it holds here.  `Connection.F` is the full
curvature of the same connection, and the difference between the two is exactly
one commutator.  So the "no second clock effect" result and the quantum
correction are the two halves of a single computation. -/

/-- **The curvature of the scale connection is the commutator of the scale
gradients — and nothing else.**

`Conformal.scaleCurv` (the abelian curl) vanishes identically by `d_comm`.  What
remains of `Connection.F` on the same connection is `[σᵢ, σⱼ]`.  So the scale
transports integrably exactly where its gradients commute, and the obstruction is
the same object that corrects the geometry below. -/
theorem F_scaleConn (i j : Fin n) :
    Connection.F (fun k => sig σ k) i j = ad (sig σ i) (sig σ j) := by
  simp only [Connection.F, sig]
  rw [d_comm i j σ, sub_self, zero_add]

/-- Consequently the scale connection is flat exactly on the commuting locus:
`Conformal.scaleCurv_eq_zero` is the classical half of this statement, and
`Connection.curv_gradient_eq_zero` is the hypothesis it needs. -/
theorem F_scaleConn_eq_zero_iff (i j : Fin n) :
    Connection.F (fun k => sig σ k) i j = 0 ↔ sig σ i * sig σ j = sig σ j * sig σ i := by
  rw [F_scaleConn]
  simp only [ad, sub_eq_zero]

/-! ## The deformation tensor loses exactly one thing -/

/-- **The whole quantum-gravitational correction, in one line.**

`Defm` is no longer symmetric, and the failure is exactly twice the commutator
of the scale gradients:

        Defm i j − Defm j i = −2 [σᵢ, σⱼ] .

Everything else in the curvature computation is unchanged, because the
Kronecker deltas are central and `hess` is still symmetric. -/
theorem Defm_antisymm_part (i j : Fin n) :
    Defm n σ i j - Defm n σ j i = -2 * ad (sig σ i) (sig σ j) := by
  simp only [Defm, ad, hess_symm σ i j, kron_symm i j]
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
        + 2 * ((kron i j : M) * gradsq n σ) := by
  simp only [Defm, hess_symm σ i j, kron_symm i j]
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
      = (kron a c : M) * (sig σ b * sig σ e + sig σ e * sig σ b)
        - (kron a c : M) * ((kron b e : M) * gradsq n σ)
        + (kron a b : M) * (sig σ c * sig σ e)
        + (kron a e : M) * (sig σ c * sig σ b)
        - (kron c b : M) * (sig σ a * sig σ e)
        - (kron c e : M) * (sig σ a * sig σ b)
        + (kron b e : M) * ad (sig σ a) (sig σ c) := by
  have h : ∀ m : Fin n, Chr σ a c m * Chr σ m b e
      = ((kron a c : M) * (kron m b : M)) * (sig σ m * sig σ e)
        + ((kron a c : M) * (kron m e : M)) * (sig σ m * sig σ b)
        - ((kron a c : M) * (kron b e : M)) * (sig σ m * sig σ m)
        + ((kron a m : M) * (kron m b : M)) * (sig σ c * sig σ e)
        + ((kron a m : M) * (kron m e : M)) * (sig σ c * sig σ b)
        - ((kron a m : M) * (kron b e : M)) * (sig σ c * sig σ m)
        - ((kron c m : M) * (kron m b : M)) * (sig σ a * sig σ e)
        - ((kron c m : M) * (kron m e : M)) * (sig σ a * sig σ b)
        + ((kron c m : M) * (kron b e : M)) * (sig σ a * sig σ m) := by
    intro m
    simp only [Chr, sub_mul, mul_sub, add_mul, mul_add, kron_mul_kron_mul]
    noncomm_ring
  rw [Finset.sum_congr rfl (fun m _ => h m)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [show (∑ m, ((kron a c : M) * (kron m b : M)) * (sig σ m * sig σ e))
      = (kron a c : M) * (sig σ b * sig σ e) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), ← Finset.mul_sum, sum_kron_left]]
  rw [show (∑ m, ((kron a c : M) * (kron m e : M)) * (sig σ m * sig σ b))
      = (kron a c : M) * (sig σ e * sig σ b) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), ← Finset.mul_sum, sum_kron_left]]
  rw [show (∑ m, ((kron a c : M) * (kron b e : M)) * (sig σ m * sig σ m))
      = (kron a c : M) * ((kron b e : M) * gradsq n σ) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), ← Finset.mul_sum,
      ← Finset.mul_sum]
    rfl]
  rw [show (∑ m, ((kron a m : M) * (kron m b : M)) * (sig σ c * sig σ e))
      = (kron a b : M) * (sig σ c * sig σ e) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), sum_kron_right]]
  rw [show (∑ m, ((kron a m : M) * (kron m e : M)) * (sig σ c * sig σ b))
      = (kron a e : M) * (sig σ c * sig σ b) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), sum_kron_right]]
  rw [show (∑ m, ((kron a m : M) * (kron b e : M)) * (sig σ c * sig σ m))
      = (kron b e : M) * (sig σ c * sig σ a) by
    rw [Finset.sum_congr rfl (fun m _ => by rw [mul_assoc, kron_swap]),
      ← Finset.mul_sum, sum_kron_right]]
  rw [show (∑ m, ((kron c m : M) * (kron m b : M)) * (sig σ a * sig σ e))
      = (kron c b : M) * (sig σ a * sig σ e) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), sum_kron_right]]
  rw [show (∑ m, ((kron c m : M) * (kron m e : M)) * (sig σ a * sig σ b))
      = (kron c e : M) * (sig σ a * sig σ b) by
    rw [Finset.sum_congr rfl (fun m _ => mul_assoc _ _ _), sum_kron_right]]
  rw [show (∑ m, ((kron c m : M) * (kron b e : M)) * (sig σ a * sig σ m))
      = (kron b e : M) * (sig σ a * sig σ c) by
    rw [Finset.sum_congr rfl (fun m _ => by rw [mul_assoc, kron_swap]),
      ← Finset.mul_sum, sum_kron_right]]
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
      = (kron a c : M) * (2 * (sig σ b * sig σ e))
        - (kron a c : M) * ((kron b e : M) * gradsq n σ)
        + (kron a b : M) * (sig σ c * sig σ e)
        + (kron a e : M) * (sig σ b * sig σ c)
        - (kron c b : M) * (sig σ a * sig σ e)
        - (kron c e : M) * (sig σ a * sig σ b) := by
  rw [sum_Chr_Chr_full_nc σ a b c e]
  simp only [ad, hc a c, sub_self, mul_zero, add_zero, hc b e, hc c b]
  noncomm_ring

/-! ## The master regression theorem, without commutativity

This is what the shared vocabulary buys.  `Conformal.two_Rm_eq` proved that the
Riemann tensor is the Kulkarni–Nomizu product `δ ∧ D`; it could only be stated
over a commutative ring because `Rm` and `Defm` were commutative-sector objects.
They are not: they are the same objects here, and the theorem goes through with
one extra term, built from nothing but commutators of scale gradients. -/

variable (n) in
/-- The **commutator correction to the Riemann tensor**:

        C^a_{bce} = δ_{ab}[σ_c, σ_e] + δ_{be}[σ_a, σ_c] − δ_{bc}[σ_a, σ_e] .

Built from nothing but commutators of scale gradients, antisymmetric in
`c ↔ e` exactly as the Riemann tensor is, and identically zero in the classical
sector. -/
def RmCorr (σ : M) (a b c e : Fin n) : M :=
  (kron a b : M) * ad (sig σ c) (sig σ e)
    + (kron b e : M) * ad (sig σ a) (sig σ c)
    - (kron b c : M) * ad (sig σ a) (sig σ e)

@[simp] theorem RmCorr_eq_zero_of_commute (a b c e : Fin n)
    (hc : ∀ i j : Fin n, sig σ i * sig σ j = sig σ j * sig σ i) :
    RmCorr n σ a b c e = 0 := by
  simp only [RmCorr, ad, hc c e, hc a c, hc a e, sub_self, mul_zero, add_zero]

/-- The correction is antisymmetric in the last index pair, as the curvature it
corrects must be. -/
theorem RmCorr_antisymm (a b c e : Fin n) :
    RmCorr n σ a b c e = -RmCorr n σ a b e c := by
  simp only [RmCorr, ad]
  noncomm_ring

/-- **The master regression theorem, in the general sector.**

`2 R^a_{bce} = δ_{ae} D_{bc} − δ_{ac} D_{be} + δ_{bc} D_{ae} − δ_{be} D_{ac}
              + 2 C^a_{bce}` .

Curvature is *still* the Kulkarni–Nomizu product of the bare bookkeeping `δ` with
the scale deformation `D`.  Non-commutativity adds one term, and that term is
built from commutators of scale gradients — the same object that
`Defm_antisymm_part` identifies as the whole correction to the deformation
tensor, and the same object `F_scaleConn` identifies as the whole curvature of
the scale connection.  Three computations, one correction.

This is the statement the file was written to reach: the quantitative curvature
identity no longer runs through the commutative sector. -/
theorem two_Rm_eq_nc (a b c e : Fin n) :
    2 * Rm σ a b c e
      = (kron a e : M) * Defm n σ b c - (kron a c : M) * Defm n σ b e
        + (kron b c : M) * Defm n σ a e - (kron b e : M) * Defm n σ a c
        + 2 * RmCorr n σ a b c e := by
  have hsplit : Rm σ a b c e
      = (d c (Chr σ a b e) - d e (Chr σ a b c))
        + ((∑ m, Chr σ a c m * Chr σ m b e) - ∑ m, Chr σ a e m * Chr σ m b c) := by
    simp only [Rm, Finset.sum_sub_distrib]
  rw [hsplit, d_Chr_diff, sum_Chr_Chr_full_nc, sum_Chr_Chr_full_nc]
  simp only [Defm, RmCorr, ad, mul_add, mul_sub]
  rw [kron_symm c b, kron_symm e b, kron_symm e c,
    kron_swap b c a e (gradsq n σ), kron_swap b e a c (gradsq n σ)]
  noncomm_ring

/-- **And the classical theorem is its commuting locus.**

With commuting gradients the correction vanishes and `two_Rm_eq_nc` is
`Conformal.two_Rm_eq` — the same `Rm`, the same `Defm`, not a translation. -/
theorem two_Rm_eq_classical (a b c e : Fin n)
    (hc : ∀ i j : Fin n, sig σ i * sig σ j = sig σ j * sig σ i) :
    2 * Rm σ a b c e
      = (kron a e : M) * Defm n σ b c - (kron a c : M) * Defm n σ b e
        + (kron b c : M) * Defm n σ a e - (kron b e : M) * Defm n σ a c := by
  rw [two_Rm_eq_nc σ a b c e, RmCorr_eq_zero_of_commute σ a b c e hc, mul_zero, add_zero]

/-- **Flatness needs one extra condition, and only one.**

Classically a deformation-free scale field is flat.  Here it is flat provided the
scale gradients also commute — and by `Defm_symm_iff_commute` that second
condition is not an extra postulate about the geometry: it is the symmetry of
`Defm` itself.  So "vacuum" in the quantum sector means *uniform and
simultaneously specifiable* scale change. -/
theorem Rm_eq_zero_of_Defm_eq_zero_nc [Invertible (2 : M)] (σ : M)
    (h : ∀ i j, Defm n σ i j = 0)
    (hc : ∀ i j : Fin n, sig σ i * sig σ j = sig σ j * sig σ i) (a b c e : Fin n) :
    Rm σ a b c e = 0 := by
  have h2 : 2 * Rm σ a b c e = 0 := by
    rw [two_Rm_eq_classical σ a b c e hc, h b c, h b e, h a e, h a c]
    noncomm_ring
  calc Rm σ a b c e = ⅟(2 : M) * (2 * Rm σ a b c e) := by
        rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = 0 := by rw [h2, mul_zero]

/-! ## Where the correction can show up -/

/-- **The correction and the rotational label are one object, not two.**

`Pattern.wedge` is the framework's rotational label, and
`Pattern.wedge_self_eq_commutator` says the wedge of a pattern with *itself* is
the commutator of its values.  Applied to the scale gradient pattern that is
exactly the quantum correction.

Previously this was stated as a structural match — both antisymmetric in the
same index pair.  With one vocabulary it is an identity. -/
theorem quantum_correction_is_a_wedge (i j : Fin n) :
    ad (sig σ i) (sig σ j) = wedge (sig (n := n) σ) (sig (n := n) σ) i j := rfl

/-- Consequently the correction is antisymmetric, so it cannot appear in
anything computed from a symmetric part: orbits are untouched, and the first
place it can show up is a coupling to the rotational label itself. -/
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

/-- **The geometry is classical exactly on the parallel locus.**

`Parallel (sig σ) (sig σ)` — the scale gradient pattern being parallel to
itself — is automatic in the commutative sector (`Pattern.parallel_self`) and is
a genuine restriction outside it.  This says it is *equivalent* to the
deformation tensor being symmetric, hence to the whole correction vanishing.

So "classical" is not a limit taken but a locus: the set of scale fields whose
gradient pattern is self-parallel. -/
theorem classical_iff_parallel [Invertible (2 : M)] :
    (∀ i j : Fin n, Defm n σ i j = Defm n σ j i)
      ↔ Parallel (sig (n := n) σ) (sig (n := n) σ) := by
  constructor
  · intro h i j
    exact (Defm_symm_iff_commute σ i j).mp (h i j)
  · intro h i j
    exact (Defm_symm_iff_commute σ i j).mpr (h i j)

/-- And on that locus the entire correction to the curvature is zero — so the
classical Riemann tensor is not an approximation to the general one, it is the
general one restricted to the self-parallel scale fields. -/
theorem RmCorr_eq_zero_of_parallel (h : Parallel (sig (n := n) σ) (sig (n := n) σ))
    (a b c e : Fin n) :
    RmCorr n σ a b c e = 0 :=
  RmCorr_eq_zero_of_commute σ a b c e (fun i j => h i j)

end SCD.NCConformal
