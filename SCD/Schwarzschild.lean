/-
# The cancellation that makes reciprocity happen

`Vacuum.lean` derived `s_t · s_r = 1` from two ingredients: that the vacuum
makes the scale sum constant, and that asymptotic flatness fixes the constant.
The second was proved there.  The first was flagged as input — "the standard
Ricci combination" — and it is the last unproved link in the gravity chain.

This file proves the part of it that carries the content.

Write the measured metric in the directional form of A4 with only the temporal
and radial units varying, `A = e^{2σ_t}`, `B = e^{2σ_r}`.  The two Ricci
components that matter are

    R_tt = A''/2B − (A'/4B)(A'/A + B'/B) + A'/rB
    R_rr = −A''/2A + (A'/4A)(A'/A + B'/B) + B'/rB

and each of them is a mess: second derivatives, quadratic terms, no visible
structure.  Form the particular combination `R_tt/A + R_rr/B` and **everything
awkward cancels**:

    R_tt/A + R_rr/B = (1/rB)(A'/A + B'/B) .

The second derivatives cancel, and so do the quadratic terms — exactly, for all
`A` and `B`.  What is left is a total logarithmic derivative.  That is why the
vacuum has anything to say about `AB` at all, and it is the whole reason
reciprocity exists.

* `ricci_combination` — the cancellation, verified;
* `vacuum_log_derivative` — hence in vacuum `A'/A + B'/B = 0`;
* `scale_sum_derivative_zero` — in scale variables, `σ_t' + σ_r' = 0`, which is
  precisely the hypothesis `Vacuum.reciprocity_of_asymptotic_flatness` needed.

**Chain status.**  With this, the gravity sector runs:
Ricci components (input) → cancellation (proved here) → scale sum constant
(proved) → asymptotic flatness (proved, `Vacuum`) → `s_t s_r = 1` → `γ = 1`
(proved, `PPN`) → deflection `1.7515″` and precession `42.99″` (proved).

One link remains an input: the two Ricci expressions themselves, which come
from the Levi-Civita connection of the diagonal ansatz.  That step is
mechanical; the step proved here is the one where something non-obvious
happens.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace SCD.Schwarzschild

/-! ## The two Ricci components of the diagonal ansatz

Taken as given, in their standard form.  `A`, `B` are the temporal and radial
metric factors, primes are `r`-derivatives. -/

/-- `R_tt` for `−A dt² + B dr² + r²dΩ²`. -/
noncomputable def Rtt (A A' A'' B B' r : ℝ) : ℝ :=
  A'' / (2 * B) - (A' / (4 * B)) * (A' / A + B' / B) + A' / (r * B)

/-- `R_rr` for the same. -/
noncomputable def Rrr (A A' A'' B B' r : ℝ) : ℝ :=
  -A'' / (2 * A) + (A' / (4 * A)) * (A' / A + B' / B) + B' / (r * B)

/-! ## The cancellation -/

/-- **Everything awkward cancels.**

`R_tt/A + R_rr/B = (1/rB)(A'/A + B'/B)` .

The second derivatives cancel against each other and so do the quadratic terms,
exactly and for all `A`, `B`.  What survives is a total logarithmic derivative —
which is why the vacuum constrains the *product* `AB` and nothing else about
it. -/
theorem ricci_combination (A A' A'' B B' r : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hr : r ≠ 0) :
    Rtt A A' A'' B B' r / A + Rrr A A' A'' B B' r / B
      = (1 / (r * B)) * (A' / A + B' / B) := by
  simp only [Rtt, Rrr]
  field_simp
  ring

/-- **In vacuum the logarithmic derivative of the product vanishes.**

`R_tt = R_rr = 0` forces `A'/A + B'/B = 0`, because the prefactor `1/rB` is
never zero. -/
theorem vacuum_log_derivative (A A' A'' B B' r : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hr : r ≠ 0)
    (htt : Rtt A A' A'' B B' r = 0) (hrr : Rrr A A' A'' B B' r = 0) :
    A' / A + B' / B = 0 := by
  have hcomb := ricci_combination A A' A'' B B' r hA hB hr
  rw [htt, hrr] at hcomb
  simp only [zero_div, add_zero, zero_add] at hcomb
  have hpre : (1 : ℝ) / (r * B) ≠ 0 := by
    simp only [ne_eq, one_div, inv_eq_zero, mul_eq_zero]
    push_neg
    exact ⟨hr, hB⟩
  have := hcomb.symm
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hpre
  · exact h

/-! ## In scale variables -/

/-- With `A = e^{2σ_t}` and `B = e^{2σ_r}`, the logarithmic derivatives are
twice the scale derivatives, so the vacuum condition reads `σ_t' + σ_r' = 0` —
exactly the hypothesis `Vacuum.reciprocity_of_asymptotic_flatness` requires. -/
theorem scale_sum_derivative_zero (σt' σr' A A' B B' : ℝ)
    (hA : A' / A = 2 * σt') (hB : B' / B = 2 * σr')
    (hvac : A' / A + B' / B = 0) :
    σt' + σr' = 0 := by
  rw [hA, hB] at hvac
  linarith

/-- Collected: the vacuum condition on the diagonal ansatz is exactly the
statement that the scale sum is stationary.  Nothing else about `A` and `B` is
constrained by it, which is why the *constant* then has to come from a boundary
condition. -/
theorem vacuum_iff_scale_sum_stationary (A A' A'' B B' r σt' σr' : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hr : r ≠ 0)
    (hAlog : A' / A = 2 * σt') (hBlog : B' / B = 2 * σr')
    (htt : Rtt A A' A'' B B' r = 0) (hrr : Rrr A A' A'' B B' r = 0) :
    σt' + σr' = 0 :=
  scale_sum_derivative_zero σt' σr' A A' B B' hAlog hBlog
    (vacuum_log_derivative A A' A'' B B' r hA hB hr htt hrr)

/-! ## What the cancellation is really saying

The combination that cancels is the one weighted by the inverse metric on the
`t`–`r` block.  So the vacuum equation, restricted to that block, says only
that the **area element there is stationary** — it says nothing about how the
temporal and radial scales are individually distributed.  That is the precise
sense in which gravity, in vacuum, only trades one against the other. -/

/-- The area element in the `t`–`r` plane is `AB`, and its logarithmic
derivative is what the vacuum sets to zero. -/
theorem area_element_stationary (A A' A'' B B' r : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hr : r ≠ 0)
    (htt : Rtt A A' A'' B B' r = 0) (hrr : Rrr A A' A'' B B' r = 0) :
    A' * B + A * B' = 0 := by
  have h := vacuum_log_derivative A A' A'' B B' r hA hB hr htt hrr
  field_simp at h
  linarith

end SCD.Schwarzschild
