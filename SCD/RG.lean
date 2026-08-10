/-
# The renormalisation group as fiducial covariance

`Axioms.lean` proved that the *geometry* is untouched by a global shift of the
log-scale, `σ ↦ σ + c` (A5).  The description of *matter* need not be: to keep
predictions fixed while the fiducial unit moves, the couplings must move too.
That compensating motion is the renormalisation group.

Three consequences are proved here.

1. **Scale flow is a one-parameter group.**  Shifting the fiducial twice is
   shifting it once by the sum — nothing else is available.

2. **Self-similarity is power law.**  An observable that is multiplicative
   along the flow satisfies `O(t) = O(0)e^{γt}`: anomalous dimensions are the
   only scale-covariant behaviour, and fixed points are exactly the scale
   invariant theories.

3. **The EFT tower is forced.**  Excitations carry log-thresholds; the set of
   excitations available at log-energy `t` is monotone in `t` and locally
   constant away from thresholds.  That effective field theory must be
   *replaced* at each threshold is therefore a theorem of the scale structure,
   not an embarrassment of the method.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat

namespace SCD.RG

open Real

/-! ## The scale flow -/

/-- A **scale flow** on a space of dimensionless couplings: the action of a
shift of the fiducial log-scale.  Only the group law is postulated; it is
forced by A5, since shifting the fiducial by `t` and then by `u` is shifting
it by `t + u`. -/
structure ScaleFlow (S : Type*) where
  /-- `flow t g` is the coupling `g` re-expressed after a fiducial shift `t`. -/
  flow : ℝ → S → S
  flow_zero : ∀ g, flow 0 g = g
  flow_add : ∀ t u g, flow (t + u) g = flow t (flow u g)

namespace ScaleFlow

variable {S : Type*} (Φ : ScaleFlow S)

/-- A **fixed point** of the flow: a theory that looks the same at every
scale. -/
def IsFixedPoint (g : S) : Prop := ∀ t, Φ.flow t g = g

/-- **Fixed points are exactly the self-similar theories.**  At a fixed point
every observable is scale independent, because the state itself is. -/
theorem observable_const_at_fixedPoint {β : Type*} (O : S → β) {g : S}
    (h : Φ.IsFixedPoint g) (t : ℝ) : O (Φ.flow t g) = O g := by
  rw [h t]

/-- A fixed point remains a fixed point under the flow. -/
theorem fixedPoint_invariant {g : S} (h : Φ.IsFixedPoint g) (t : ℝ) :
    Φ.IsFixedPoint (Φ.flow t g) := by
  intro u
  rw [h t, h u]

end ScaleFlow

/-! ## Self-similarity forces power laws

An observable is *multiplicatively renormalised* if running the scale
rescales it.  We show that the Callan–Symanzik equation `Ȯ = γO` has only
exponential solutions — so the sole scale-covariant behaviour available is a
power law in the scale, with exponent the anomalous dimension `γ`. -/

/-- **Anomalous dimensions are the only scale-covariant behaviour.**

If a dimensionless observable obeys the Callan–Symanzik equation
`dO/dt = γ O`, then `O(t) = O(0)e^{γt}`, i.e. `O` is a pure power of the
scale.  In particular `γ = 0` — a fixed point — gives exact scale invariance.

This is the same computation as the dissipation law of `DarkEnergy.lean`: a
running coupling and an expanding universe are the same mathematics read at
two different scales, which is the self-similarity the framework asserts. -/
theorem callan_symanzik (γ : ℝ) (O : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt O (γ * O t) t) (t : ℝ) :
    O t = O 0 * Real.exp (γ * t) := by
  set u : ℝ → ℝ := fun r => O r * Real.exp (-γ * r) with hu_def
  have hexp : ∀ r : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-γ * x))
      (Real.exp (-γ * r) * (-γ)) r := by
    intro r
    have hin : HasDerivAt (fun x : ℝ => -γ * x) (-γ) r := by
      simpa using (hasDerivAt_id r).const_mul (-γ)
    exact (Real.hasDerivAt_exp (-γ * r)).comp r hin
  have hu : ∀ r, HasDerivAt u 0 r := by
    intro r
    have h := (hd r).mul (hexp r)
    have hz : (γ * O r) * Real.exp (-γ * r) + O r * (Real.exp (-γ * r) * (-γ)) = 0 := by
      ring
    rwa [hz] at h
  have hconst : ∀ x y, u x = u y :=
    is_const_of_deriv_eq_zero (fun r => (hu r).differentiableAt) (fun r => (hu r).deriv)
  have h0 : O t * Real.exp (-γ * t) = O 0 := by
    have := hconst t 0
    simpa [hu_def] using this
  have hne : Real.exp (γ * t) ≠ 0 := Real.exp_ne_zero _
  rw [show -γ * t = -(γ * t) by ring, Real.exp_neg] at h0
  field_simp at h0
  linear_combination h0

/-- At a fixed point (`γ = 0`) the observable is exactly constant: unbroken
scale invariance. -/
theorem scale_invariant_of_fixedPoint (O : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt O (0 * O t) t) (t : ℝ) : O t = O 0 := by
  simpa using callan_symanzik 0 O hd t

/-! ## The effective-field-theory tower is a theorem

Each excitation carries a log-threshold `μ i`: below that log-energy it cannot
be produced.  The content of the effective description at log-energy `t` is
the set of excitations with `μ i ≤ t`. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The excitations available at log-energy `t`. -/
noncomputable def active (μ : ι → ℝ) (t : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => μ i ≤ t)

theorem mem_active {μ : ι → ℝ} {t : ℝ} {i : ι} : i ∈ active μ t ↔ μ i ≤ t := by
  simp [active]

/-- **New physics appears as the scale rises, and never disappears.**  The
active content is monotone in the log-energy. -/
theorem active_mono (μ : ι → ℝ) {t t' : ℝ} (h : t ≤ t') : active μ t ⊆ active μ t' := by
  intro i hi
  rw [mem_active] at hi ⊢
  exact hi.trans h

/-- **Between thresholds the effective theory does not change.**  If no
threshold lies in `(t, t']` then the content is literally the same set — the
effective description is exact there, not approximate. -/
theorem active_eq_of_no_threshold (μ : ι → ℝ) {t t' : ℝ} (h : t ≤ t')
    (hgap : ∀ i, ¬(t < μ i ∧ μ i ≤ t')) : active μ t = active μ t' := by
  apply Finset.Subset.antisymm (active_mono μ h)
  intro i hi
  rw [mem_active] at hi ⊢
  by_contra hlt
  exact hgap i ⟨lt_of_not_ge hlt, hi⟩

/-- **The tower is finite.**  A finite excitation content admits only finitely
many distinct effective theories, one per threshold crossed.  Changing
framework at each threshold is therefore not a defect of effective field
theory: it is the exact bookkeeping of a scale-stratified world. -/
theorem active_finite_range (μ : ι → ℝ) :
    Set.Finite (Set.range (active μ)) :=
  Set.Finite.subset (Set.finite_univ (α := Finset ι)) (Set.subset_univ _)

/-- Below every threshold the effective theory is empty; above every threshold
it is complete.  The tower is exhausted. -/
theorem active_eq_univ_of_ge (μ : ι → ℝ) {t : ℝ} (h : ∀ i, μ i ≤ t) :
    active μ t = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  rw [mem_active]
  exact h i

theorem active_eq_empty_of_lt (μ : ι → ℝ) {t : ℝ} (h : ∀ i, t < μ i) :
    active μ t = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  rw [mem_active] at hi
  exact absurd hi (not_le.mpr (h i))

/-! ## Where the beta function comes from

`QCD.lean` takes the one-loop coefficient `b` as an input, borrowed from gauge
theory.  That borrowing can be pushed back one step here.

A5 says a fiducial shift is a symmetry of the geometry but not of the
description: the couplings must move to compensate.  *What* has to be
compensated is the content that is actually there — the active excitations.  So
the rate of compensation is a functional of the active set and of nothing else.

That is not enough to compute a number, and we do not pretend otherwise.  It is
enough to fix the *shape* of the beta function, and the shape is a genuine
prediction: piecewise constant, changing only where the content changes.  QCD's
coefficient does exactly this, jumping at each quark threshold. -/

/-- A beta coefficient determined by the active content: whatever the
compensation rate is, it can depend only on which excitations are present. -/
noncomputable def betaOf (Φ : Finset ι → ℝ) (μ : ι → ℝ) (t : ℝ) : ℝ := Φ (active μ t)

/-- **The beta coefficient is constant between thresholds.**

Where the content does not change, the compensation required by A5 does not
change either.  Running is *exactly* one-coefficient there, not approximately
so. -/
theorem beta_const_between_thresholds (Φ : Finset ι → ℝ) (μ : ι → ℝ) {t t' : ℝ}
    (h : t ≤ t') (hgap : ∀ i, ¬(t < μ i ∧ μ i ≤ t')) :
    betaOf Φ μ t = betaOf Φ μ t' := by
  simp only [betaOf, active_eq_of_no_threshold μ h hgap]

/-- **It changes only at thresholds, and takes finitely many values.**

So the beta function is a step function of the log-scale whose jumps sit
exactly at the masses.  The framework fixes this structure; it does not fix the
numbers, which remain an input. -/
theorem beta_finite_range (Φ : Finset ι → ℝ) (μ : ι → ℝ) :
    Set.Finite (Set.range (betaOf Φ μ)) := by
  have h : Set.range (betaOf Φ μ) = Φ '' Set.range (active μ) := by
    rw [← Set.range_comp]
    rfl
  rw [h]
  exact (active_finite_range μ).image Φ

/-- Above every threshold the coefficient settles to its complete-content
value: the deep-ultraviolet running is governed by the full spectrum. -/
theorem beta_eq_of_all_active (Φ : Finset ι → ℝ) (μ : ι → ℝ) {t : ℝ}
    (h : ∀ i, μ i ≤ t) : betaOf Φ μ t = Φ Finset.univ := by
  simp only [betaOf, active_eq_univ_of_ge μ h]

end SCD.RG
