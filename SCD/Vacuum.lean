/-
# Reciprocity, and where its constant comes from

`PPN.lean` showed that the reciprocal condition `s_t · s_r = 1` forces the PPN
coefficient `γ = 1` and so supplies the half of the light deflection that a
scalar scale cannot.  That left reciprocity itself as a property of the
configuration being *described* rather than one *derived*.

This file closes the second half of that gap — the part that can be closed
without the component-wise curvature computation.

The vacuum condition, in the standard static spherically symmetric
computation, does not directly give `s_t s_r = 1`.  It gives something weaker:
the sum of the temporal and radial log-scales has **vanishing derivative**, so
`s_t s_r` is *constant*.  Getting from "constant" to "one" is a separate step,
and it is the step that has physical content: it is **asymptotic flatness** —
far from the source there is nothing, so the local unit must agree with the
fiducial.

* `const_of_deriv_zero_and_vanishing` — a function with zero derivative that
  vanishes somewhere vanishes everywhere;
* `reciprocity_of_asymptotic_flatness` — hence `σ_t + σ_r = 0`, i.e.
  `s_t · s_r = 1`, once the scale sum is required to vanish far away;
* `scale_product_eq_one` — the same statement multiplicatively.

**What is and is not established.**  Derived here: given the vacuum
consequence that the scale sum is constant, reciprocity follows from
asymptotic flatness alone, with no further choice.  *Not* derived here: that
the vacuum field equation implies the sum is constant.  That is the standard
Ricci combination `R_tt/A + R_rr/B = 0` and it is taken as input; formalizing
it needs the diagonal-ansatz curvature computation, which remains the one
outstanding piece of the gravity sector.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

namespace SCD.Vacuum

open Real

/-! ## From constant to one -/

/-- A function with vanishing derivative that vanishes at one point vanishes
everywhere.  Elementary, and it is the whole of the normalisation step. -/
theorem const_of_deriv_zero_and_vanishing (f : ℝ → ℝ)
    (hd : ∀ r, HasDerivAt f 0 r) (r₀ : ℝ) (h0 : f r₀ = 0) :
    ∀ r, f r = 0 := by
  have hconst : ∀ x y, f x = f y :=
    is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv)
  intro r
  rw [hconst r r₀]
  exact h0

/-! ## Reciprocity -/

/-- **Reciprocity from asymptotic flatness.**

The vacuum condition makes the sum of the temporal and radial log-scales
constant.  Requiring that the sum vanish far from the source — asymptotic
flatness, i.e. that the local unit agrees with the fiducial where there is no
matter — forces the sum to vanish everywhere.

The constant is therefore not fitted; it is fixed by the only boundary
condition the axioms permit, since by A5 the fiducial is exactly what "far
away" means. -/
theorem reciprocity_of_asymptotic_flatness (σt σr : ℝ → ℝ)
    (hvac : ∀ r, HasDerivAt (fun x => σt x + σr x) 0 r)
    (rInf : ℝ) (hflat : σt rInf + σr rInf = 0) :
    ∀ r, σt r + σr r = 0 :=
  const_of_deriv_zero_and_vanishing (fun x => σt x + σr x) hvac rInf hflat

/-- The same statement multiplicatively: the temporal and radial *scales* are
exact reciprocals, `s_t · s_r = 1`. -/
theorem scale_product_eq_one (σt σr : ℝ → ℝ)
    (hvac : ∀ r, HasDerivAt (fun x => σt x + σr x) 0 r)
    (rInf : ℝ) (hflat : σt rInf + σr rInf = 0) (r : ℝ) :
    Real.exp (σt r) * Real.exp (σr r) = 1 := by
  rw [← Real.exp_add]
  rw [reciprocity_of_asymptotic_flatness σt σr hvac rInf hflat r]
  exact Real.exp_zero

/-- Without the boundary condition, reciprocity fails: the scale product is
some constant, and any constant is compatible with the vacuum equation.  So
asymptotic flatness is doing real work and is not a convention. -/
theorem product_constant_without_flatness (σt σr : ℝ → ℝ)
    (hvac : ∀ r, HasDerivAt (fun x => σt x + σr x) 0 r) (r₁ r₂ : ℝ) :
    Real.exp (σt r₁) * Real.exp (σr r₁) = Real.exp (σt r₂) * Real.exp (σr r₂) := by
  have hconst : ∀ x y, σt x + σr x = σt y + σr y :=
    is_const_of_deriv_eq_zero (fun r => (hvac r).differentiableAt)
      (fun r => (hvac r).deriv)
  rw [← Real.exp_add, ← Real.exp_add, hconst r₁ r₂]

/-- The area element in the time–radial plane is what reciprocity conserves.
Read physically: in vacuum, gravity trades temporal scale against radial scale
and creates no scale in that plane at all. -/
theorem tr_area_element_constant (σt σr : ℝ → ℝ)
    (hvac : ∀ r, HasDerivAt (fun x => σt x + σr x) 0 r)
    (rInf : ℝ) (hflat : σt rInf + σr rInf = 0) (r : ℝ) :
    Real.exp (σt r + σr r) = 1 := by
  rw [reciprocity_of_asymptotic_flatness σt σr hvac rInf hflat r]
  exact Real.exp_zero

end SCD.Vacuum
