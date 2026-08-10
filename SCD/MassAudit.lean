/-
# Retraction: the mass tower was assumed, not derived

`Defect.lean` states

    m_k = m₀ e^{|k|Δ}

and presents it as following from A3 ("mass is inverse scale") together with the
scale stepping by `Δ` per unit of winding.  `QCD.lean` then tests the resulting
constant mass ratio against lattice glueball data and reports it **falsified**.

The audit found that the falsification was aimed at the wrong target, because
the mass law was never derived.

What the framework actually establishes about a defect is **topological**: the
winding `k` is an integer, it is additive, it cannot change continuously, and
`|k|` is invariant under orientation reversal.  What the mass law additionally
requires is **dynamical**: how much the scale field is strained by a defect of
winding `k`, which is a question about the energetics of the configuration —
something no theorem in this development addresses.

The gap is made precise below.

* `mass_law_underdetermined` — exhibits two different mass laws, an exponential
  tower and a quadratic one, **both** fully compatible with every property of
  the winding that has been proved.  So the topology does not fix the mass law:
  a further physical input is required, and none has been supplied.
* `both_laws_antiparticle_degenerate` — both satisfy the one prediction that
  *is* derived, `m_{-k} = m_k`, so the glueball data cannot discriminate the
  framework by that route.

**Consequences for what was claimed.**  The particle–antiparticle mass
degeneracy stands: it follows from `|k|` alone.  The *geometric tower* does
not; it must be demoted from prediction to hypothesis.  And the glueball test
of `QCD.geometric_tower_fails` therefore refutes **that hypothesis**, not the
framework — a materially weaker conclusion than the one previously reported,
and this file exists so that the weaker conclusion is the one on record.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace SCD.MassAudit

open Real

/-! ## Two candidate laws -/

/-- The law asserted in `Defect.lean`: a geometric tower. -/
noncomputable def massExp (m₀ Δ : ℝ) (k : ℤ) : ℝ := m₀ * Real.exp (|(k : ℝ)| * Δ)

/-- An equally available alternative: strain energy quadratic in the winding,
which is what a naive energetic estimate for a topological defect gives. -/
noncomputable def massQuad (m₀ c : ℝ) (k : ℤ) : ℝ := m₀ + c * ((k : ℝ)) ^ 2

/-! ## What the topology actually fixes -/

/-- Orientation reversal is the only constraint the proved topology imposes on
a mass law, and the exponential law satisfies it. -/
@[simp] theorem massExp_neg (m₀ Δ : ℝ) (k : ℤ) : massExp m₀ Δ (-k) = massExp m₀ Δ k := by
  simp only [massExp, Int.cast_neg, abs_neg]

/-- The quadratic law satisfies it too. -/
@[simp] theorem massQuad_neg (m₀ c : ℝ) (k : ℤ) : massQuad m₀ c (-k) = massQuad m₀ c k := by
  simp only [massQuad, Int.cast_neg]
  ring

/-- Both are positive for positive parameters, so neither is excluded on
grounds of consistency. -/
theorem massExp_pos {m₀ : ℝ} (hm : 0 < m₀) (Δ : ℝ) (k : ℤ) : 0 < massExp m₀ Δ k := by
  simp only [massExp]; positivity

theorem massQuad_pos {m₀ c : ℝ} (hm : 0 < m₀) (hc : 0 ≤ c) (k : ℤ) :
    0 < massQuad m₀ c k := by
  simp only [massQuad]
  have : 0 ≤ c * ((k : ℝ)) ^ 2 := by positivity
  linarith

/-- Both agree at zero winding, so the normalisation cannot separate them. -/
@[simp] theorem massExp_zero (m₀ Δ : ℝ) : massExp m₀ Δ 0 = m₀ := by
  simp only [massExp, Int.cast_zero, abs_zero, zero_mul, Real.exp_zero, mul_one]

@[simp] theorem massQuad_zero (m₀ c : ℝ) : massQuad m₀ c 0 = m₀ := by
  simp only [massQuad, Int.cast_zero]
  ring

/-! ## The gap, stated -/

/-- **The topology does not determine the mass law.**

Two laws that are genuinely different — their ratio at winding `1` differs —
both satisfy every property of the winding that has been proved: positivity,
agreement at `k = 0`, and invariance under orientation reversal.

Therefore the geometric tower is an **additional hypothesis**, and the constant
mass ratio it predicts is a consequence of that hypothesis rather than of the
framework. -/
theorem mass_law_underdetermined :
    ∃ (f g : ℤ → ℝ),
      (∀ k, f (-k) = f k) ∧ (∀ k, g (-k) = g k) ∧
      (∀ k, 0 < f k) ∧ (∀ k, 0 < g k) ∧
      f 0 = g 0 ∧
      f 1 ≠ g 1 := by
  refine ⟨massExp 1 1, massQuad 1 1, massExp_neg 1 1, massQuad_neg 1 1,
    fun k => massExp_pos one_pos 1 k, fun k => massQuad_pos one_pos zero_le_one k, ?_, ?_⟩
  · rw [massExp_zero, massQuad_zero]
  · have hq : massQuad 1 1 1 = 2 := by
      simp only [massQuad, Int.cast_one]; norm_num
    have he : (2.7 : ℝ) < massExp 1 1 1 := by
      simp only [massExp, Int.cast_one, abs_one, one_mul, mul_one]
      have h9 := Real.exp_one_gt_d9
      norm_num at h9 ⊢
      linarith
    rw [hq]
    intro hcon
    rw [hcon] at he
    norm_num at he

/-- Both laws reproduce the one mass statement that *is* derived — the
particle–antiparticle degeneracy — so that prediction survives the retraction
while the tower does not. -/
theorem both_laws_antiparticle_degenerate (m₀ Δ c : ℝ) (k : ℤ) :
    massExp m₀ Δ (-k) = massExp m₀ Δ k ∧ massQuad m₀ c (-k) = massQuad m₀ c k :=
  ⟨massExp_neg m₀ Δ k, massQuad_neg m₀ c k⟩

/-- The quadratic law has a *non*-constant consecutive ratio, so a spectrum
that fails the geometric-tower test is not thereby in conflict with a
defect picture at all. -/
theorem massQuad_ratio_not_constant :
    massQuad 1 1 1 * massQuad 1 1 1 ≠ massQuad 1 1 2 * massQuad 1 1 0 := by
  simp only [massQuad]
  norm_num

end SCD.MassAudit
