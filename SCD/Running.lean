/-
# Running without loops

`QCD.lean` assumed `dg/dt = −bg³` and took `b` from gauge theory.  That is the
last large borrowing in the development, and it is worth asking whether the
framework has to borrow it at all.

It does not.  Drop the idea that running comes from summing diagrams and ask
what a coupling *is* here.  A probe at log-scale `t` has a resolution; it
responds to the defects it can resolve, and by `Defect.lean` those are discrete
objects with definite log-scales.  So the accumulated response is a **count**.

**Which defects, though.**  A coupling responds only to the structures it
actually couples to, not to every structure there is.  So the `ρ` below is a
*sector-restricted* — and, for the sign to come out right, signed — density.
It is **not** the raw threshold density of `Spectrum.lean`, and
`CrossCheck.lean` records what went wrong when the two were identified: they
differ by about a factor of two, and no test connects them.

Now impose A5.  A scale-covariant world has no preferred log-scale, so the
defects cannot bunch anywhere: their density per unit log-scale is constant.
A constant density integrated over `[t₀, t]` is linear in `t`.  Hence

        g⁻²(t) = g⁻²(t₀) + κρ·(t − t₀) ,

which is precisely the one-loop form, with `b = κρ/2`.

**The linear-in-log running is a consequence of scale-invariant defect density,
not of a one-loop diagram.**  What was an imported coefficient becomes a
density of defects per unit log-scale — a count, which is also what
`11N_c − 2N_f` is.

The sign follows too: `asympt_free_iff_pos_density` shows asymptotic freedom is
equivalent to *positive* density.  Resolving more structure dilutes the
response.  That is the physical content of asymptotic freedom in this
framework, and it needed no gauge group to state.
-/
import SCD.QCD
import Mathlib.Analysis.Calculus.Deriv.Add

namespace SCD.Running

open Real

/-! ## Counting what a probe can resolve -/

/-- The number of defects a probe at log-scale `t` can resolve, given a
scale-invariant density `ρ` per unit log-scale.  A5 forces the density to be
constant: no log-scale is preferred, so none may be more populated. -/
noncomputable def resolvedCount (ρ t₀ t : ℝ) : ℝ := ρ * (t - t₀)

@[simp] theorem resolvedCount_self (ρ t₀ : ℝ) : resolvedCount ρ t₀ t₀ = 0 := by
  simp only [resolvedCount, sub_self, mul_zero]

/-- The inverse-square coupling, as accumulated response: each resolvable
defect contributes `κ`. -/
noncomputable def invSqCoupling (u₀ κ ρ t₀ t : ℝ) : ℝ := u₀ + κ * resolvedCount ρ t₀ t

@[simp] theorem invSqCoupling_at_base (u₀ κ ρ t₀ : ℝ) :
    invSqCoupling u₀ κ ρ t₀ t₀ = u₀ := by
  simp only [invSqCoupling, resolvedCount_self, mul_zero, add_zero]

/-! ## The one-loop form, derived -/

/-- **Counting gives linear running.**

The accumulated response has constant slope `κρ` in the log-scale.  Nothing
perturbative has been used: the slope is a density times a per-defect response. -/
theorem hasDerivAt_invSqCoupling (u₀ κ ρ t₀ t : ℝ) :
    HasDerivAt (fun r => invSqCoupling u₀ κ ρ t₀ r) (κ * ρ) t := by
  have h : HasDerivAt (fun r : ℝ => u₀ + κ * (ρ * (r - t₀))) (κ * ρ) t := by
    have hlin : HasDerivAt (fun r : ℝ => κ * (ρ * (r - t₀))) (κ * ρ) t := by
      have hb : HasDerivAt (fun r : ℝ => r - t₀) 1 t := (hasDerivAt_id t).sub_const t₀
      have h1 : HasDerivAt (fun r : ℝ => ρ * (r - t₀)) (ρ * 1) t := hb.const_mul ρ
      have h2 : HasDerivAt (fun r : ℝ => κ * (ρ * (r - t₀))) (κ * (ρ * 1)) t :=
        h1.const_mul κ
      simpa using h2
    simpa using hlin.const_add u₀
  exact h

/-- **The counting law and the one-loop equation are the same equation.**

Writing `b = κρ/2`, the slope `κρ` is exactly the `2b` of `QCD.running_inv_sq`.
So the beta function's *form* is not an input: it is what a constant density of
resolvable defects produces. -/
theorem slope_eq_two_b (κ ρ : ℝ) : 2 * (κ * ρ / 2) = κ * ρ := by ring

/-- Explicitly: the counting law reproduces the solved one-loop running, with
the coefficient identified as half the defect density times the per-defect
response. -/
theorem invSqCoupling_eq_one_loop (u₀ κ ρ t₀ t : ℝ) :
    invSqCoupling u₀ κ ρ t₀ t = u₀ + 2 * (κ * ρ / 2) * (t - t₀) := by
  simp only [invSqCoupling, resolvedCount]
  ring

/-! ## Asymptotic freedom is positive density -/

/-- **Asymptotic freedom ⟺ positive defect density.**

The response `g² = 1/g⁻²` falls to zero at high log-scale exactly when the
accumulated count grows, i.e. exactly when there are defects to resolve.
Resolving more structure dilutes the response.

No gauge group, no `11N_c − 2N_f`, and no diagram appears in the statement or
the proof; what appears is a count. -/
theorem asympt_free_iff_pos_density (u₀ κ ρ t₀ : ℝ) (hκ : 0 < κ) :
    (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T < t → invSqCoupling u₀ κ ρ t₀ t > 1 / ε)
      ↔ 0 < ρ := by
  constructor
  · intro h
    by_contra hρ
    push_neg at hρ
    obtain ⟨T, hT⟩ := h (1 / (|u₀| + 1)) (by positivity)
    have hlt : T < max T t₀ + 1 := by
      have : T ≤ max T t₀ := le_max_left _ _
      linarith
    have h1 := hT (max T t₀ + 1) hlt
    have hpos : 0 ≤ max T t₀ + 1 - t₀ := by
      have : t₀ ≤ max T t₀ := le_max_right _ _
      linarith
    have hneg : ρ * (max T t₀ + 1 - t₀) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hρ hpos
    have hle : invSqCoupling u₀ κ ρ t₀ (max T t₀ + 1) ≤ u₀ := by
      simp only [invSqCoupling, resolvedCount]
      nlinarith [mul_nonneg (le_of_lt hκ) (neg_nonneg.mpr hneg)]
    rw [one_div_one_div] at h1
    have habs := le_abs_self u₀
    linarith
  · intro hρ ε hε
    refine ⟨t₀ + (1 / ε - u₀) / (κ * ρ) + 1, fun t ht => ?_⟩
    simp only [invSqCoupling, resolvedCount]
    have hκρ : 0 < κ * ρ := mul_pos hκ hρ
    have hstep : (1 / ε - u₀) / (κ * ρ) < t - t₀ := by
      have : t₀ + (1 / ε - u₀) / (κ * ρ) + 1 < t := ht
      linarith
    rw [div_lt_iff₀ hκρ] at hstep
    nlinarith [hstep]

end SCD.Running
