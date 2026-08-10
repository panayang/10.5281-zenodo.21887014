/-
# The Newtonian limit: Poisson's equation from the scale response

Given the master identity of `Conformal.lean`, gravity needs only one further
statement — a **scale response law** saying what sources the scale:

    A6′  (Scale response)   `e^{2σ} R = κ ρ`,

the scalar curvature of the measured metric is proportional to the local
dimensionless energy density.  For `n = 3` this is exactly the Hamiltonian
constraint on a conformally flat slice.

We show that in the first-order regime this *is* Poisson's equation, with the
log-scale identified as minus the Newtonian potential,

    σ = −Φ ,

so that the scale is *larger* deep inside a gravitational well: rulers stretch
and, by A3, local energies redshift on the way out.  Both signs come out right
without being put in.

The first-order regime is not an approximation we wave away.  It is realised
exactly, as an identity, in the dual-number extension `A[ε]/(ε²)` of the
substrate — see `gradsq_inr` at the end of the file.
-/
import SCD.Axioms
import Mathlib.Algebra.DualNumber

namespace SCD

open Finset ScaleAlgebra

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-! ## The Newtonian potential -/

/-- The Newtonian potential is minus the log-scale.  Deep in a well the scale
is enlarged (`σ > 0`), so `Φ < 0` as it must be. -/
def newtPot (σ : A) : A := -σ

@[simp] theorem lap_newtPot (σ : A) : lap n (newtPot σ) = -lap n σ := by
  simp only [newtPot, lap_neg]

/-! ## The regime of first-order scale variation

`gradsq σ = 0` says that the scale gradient is too small for its square to
register: exactly the weak-field condition. -/

/-- In the first-order regime the scalar curvature is *linear* in the scale:
the `|∇σ|²` term drops out identically. -/
theorem RscBare_linear (σ : A) (hlin : gradsq n σ = 0) :
    RscBare n σ = -2 * ((n : A) - 1) * lap n σ := by
  rw [RscBare_eq, hlin]
  ring

/-- **Poisson's equation.**

From the scale response law `e^{2σ}R = κρ` in the first-order regime,

    `2(n−1) ΔΦ = κ ρ` ,   `Φ = −σ` .

For `n = 3` and `κ = 16πG` this is `ΔΦ = 4πGρ` exactly.  Newtonian gravity is
therefore not an input: it is the linearisation of the statement that energy
sets the local scale. -/
theorem poisson (σ ρ κ : A) (hlin : gradsq n σ = 0) (hfield : RscBare n σ = κ * ρ) :
    2 * ((n : A) - 1) * lap n (newtPot σ) = κ * ρ := by
  rw [lap_newtPot, ← hfield, RscBare_linear σ hlin]
  ring

/-- The physical case `n = 3`: `4 ΔΦ = κρ`, i.e. `ΔΦ = 4πGρ` for `κ = 16πG`. -/
theorem poisson_three {B : Type*} [CommRing B] [ScaleAlgebra 3 B] (σ ρ κ : B)
    (hlin : gradsq 3 σ = 0) (hfield : RscBare 3 σ = κ * ρ) :
    4 * lap 3 (newtPot σ) = κ * ρ := by
  have h := poisson σ ρ κ hlin hfield
  rw [lap_newtPot] at h ⊢
  norm_num at h
  linear_combination h

/-! ## The first-order regime is exactly realised

`gradsq σ = 0` is not a hypothesis we hope is harmless.  Extend the substrate
by a square-zero infinitesimal, `A[ε]/(ε²)`, and let the scale be
*infinitesimal*, `σ = εφ`.  Then `|∇σ|² = ε²|∇φ|² = 0` identically, and the
results above hold with no approximation whatsoever: `RscBare` is exactly
linear and Poisson's equation is exact.

First-order perturbation theory is thereby given a home inside the axiom
system rather than being imposed from outside. -/

namespace Dual

open TrivSqZeroExt

/-- The derivations extend componentwise to the dual numbers `A[ε]/(ε²)`. -/
instance instScaleAlgebra : ScaleAlgebra n (DualNumber A) where
  d i x := (d i x.fst, d i x.snd)
  d_add i a b := by
    ext
    · exact d_add i a.fst b.fst
    · exact d_add i a.snd b.snd
  d_mul i a b := by
    ext
    · show d i (a.fst * b.fst) = d i a.fst * b.fst + a.fst * d i b.fst
      exact d_mul i a.fst b.fst
    · show d i (a.fst * b.snd + a.snd * b.fst)
          = d i a.fst * b.snd + d i a.snd * b.fst
            + (a.fst * d i b.snd + a.snd * d i b.fst)
      rw [d_add, d_mul, d_mul]
      ring
  d_comm i j a := by
    ext
    · exact d_comm i j a.fst
    · exact d_comm i j a.snd



/-- An infinitesimal scale field `σ = εφ` has purely infinitesimal gradient. -/
theorem sig_inr (φ : A) (i : Fin n) :
    sig (inr φ : DualNumber A) i = inr (d i φ) := by
  ext
  · show d i (0 : A) = 0
    exact d_zero i
  · rfl

/-- **The linearised regime is exact.**  For an infinitesimal scale field the
quadratic invariant vanishes identically — no term is discarded. -/
@[simp] theorem gradsq_inr (φ : A) : gradsq n (inr φ : DualNumber A) = 0 := by
  simp only [gradsq, sig_inr]
  exact Finset.sum_eq_zero (fun i _ => TrivSqZeroExt.inr_mul_inr A (d i φ) (d i φ))

/-- Consequently Poisson's equation holds *exactly* for an infinitesimal scale
field: no linearisation error, because there is nothing to linearise. -/
theorem poisson_exact (φ : A) (κ α : DualNumber A)
    (hfield : RscBare n (inr φ : DualNumber A) = κ * α) :
    2 * ((n : DualNumber A) - 1) * lap n (newtPot (inr φ : DualNumber A)) = κ * α :=
  poisson _ _ _ (gradsq_inr φ) hfield

end Dual

end SCD
