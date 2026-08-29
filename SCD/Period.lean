/-
# What would fix the scale period — and why the one route there is closed

`Index.A6'_from_index` gives `κ = −2(n−1)Δ`: the gravitational coupling in terms
of the scale period.  That looked like the framework's most valuable open target,
because `Δ` is a pure number and so is the threshold density `ρ` that
`Spectrum.lean` measures, so

        κ·ρ  =  −2(n−1)·(Δρ)

and **fixing `Δρ` would predict Newton's constant from the mass spectrum.**  This
file goes after it.  The result is negative, and the negative result is worth
more than the attempt would have been, because it identifies the obstruction
exactly and connects two register entries that had looked unrelated.

## First, what `Δ` is — and a caveat that must not be dropped

`Δ` appears in three places and they are not all the same thing until something
is proved:

1. `Defect.quasiperiodic` — the shift of the log-scale per unit winding.  A pure
   number, and the only one of the three with an independent meaning;
2. `Index.IndexResponse` — the coefficient in `Δσ = Δ·ν`;
3. `Index.A6'_from_index` — hence `κ`.

**(1) = (2) is the continuum-limit gap `Index.lean` already flags**: reading the
index form as Gauss's law needs the passage from a boundary flux to a local
density, and the framework has no integration theory.  So "the gravitational
coupling *is* the scale period" is conditional on that step, and the claim that
`G` and `ħ` acquire one origin is conditional on it too.  Both are stated
unconditionally in places and should not be; `Audit.lean` §V.d now says so.

Everything below assumes the identification, because the point is to test what it
would buy.

## The one determination the framework offers, and the data that kills it

If the thresholds sat at the multiples of the period — the scale being periodic
and the content sitting on the lattice it defines — then the mean gap *is* the
period and `ρ = 1/Δ`, so

        Δρ = 1   and   κρ = −2(n−1) ,   i.e.  **κρ = −6 at `n = 4`** .

`coupling_under_lattice`.  That is a parameter-free prediction of the
gravitational coupling in units of the threshold density, and it is the only one
the framework has ever been in a position to make.

**It is excluded.**  A lattice has all gaps equal, hence zero gap variance,
hence `CV² = 0`; the observed value is `0.87 < CV² < 0.88`
(`Spectrum.observed_cvSq_value`).  `lattice_excluded`.

## And that is the same fact as an old retraction

The lattice hypothesis is `Defect.mass_ratio_geometric` — the geometric mass
tower `m_k = m₀e^{|k|Δ}`, which puts the log-masses on a lattice of spacing `Δ`.
`Audit.lean` §I records its retraction, on the strength of
`QCD.geometric_tower_fails` and `Spectrum.observed_not_geometric`.

What was **not** recorded is that the same retraction closed the only route from
the observed spectrum to the gravitational coupling.  `retraction_closed_the_route`
states the coincidence: the hypothesis that would fix `Δρ` and the hypothesis
that was refuted are the same hypothesis.

So the register understated the cost of that retraction, and this file corrects
it.  It is the second time in this audit that a register entry turned out to
carry more than it said — the first was A6′ itself.

## What is left

* **The root-normalisation route.**  `Dimension.density_normalization_relation`
  gives `ρ·α = k−1`, so identifying `Δ` with the root normalisation `α` would
  give `Δρ = k − 1 = 2` and `κρ = −12` at `n = 4`.  Nothing excludes it — but the
  identification is unformalised, `Dimension`'s relation is a tautology once
  `α` is defined, and this is precisely the one-equation-one-unknown trap
  `CrossCheck.lean` exists to flag.  It is a *conversion*, not a determination,
  and calling it otherwise would be the error that file was written about;
* **Measurement.**  `Δρ` is a pure number and both factors are in principle
  observable, so it can be measured.  That makes the relation a **test** rather
  than a prediction, which is a weaker thing and should be called by its name.

**Conclusion, stated plainly: the framework does not predict Newton's constant,
the one route by which it could have is closed by the mass spectrum, and what
remains is a conversion.**  `Index.lean`'s gain stands — a free dimensionful
constant became a free dimensionless one — but it does not go further, and the
earlier suggestion that it might was mine.
-/
import SCD.Index
import SCD.Spectrum
import SCD.Dimension
import SCD.Defect

namespace SCD.Period

open SCD

/-! ## I. The conversion, so the target is unambiguous -/

/-- **The dimensionless content of the coupling.**

`κ = −2(n−1)Δ`, so multiplying by the threshold density makes both sides pure
numbers.  Everything about the gravitational coupling that does not depend on the
choice of unit is in `Δρ`. -/
noncomputable def couplingTimesDensity (n : ℕ) (Δ rho : ℝ) : ℝ :=
  (-2 * ((n : ℝ) - 1) * Δ) * rho

theorem couplingTimesDensity_eq (n : ℕ) (Δ rho : ℝ) :
    couplingTimesDensity n Δ rho = -2 * ((n : ℝ) - 1) * (Δ * rho) := by
  simp only [couplingTimesDensity]; ring

/-! ## II. The lattice determination, and its exclusion -/

/-- **The lattice hypothesis.**  If the thresholds sit at the multiples of the
period, the mean gap is the period and the density is its reciprocal. -/
def LatticeSpectrum (Δ rho : ℝ) : Prop := rho * Δ = 1

/-- Under it, `Δρ = 1` exactly. -/
theorem lattice_gives_one {Δ rho : ℝ} (h : LatticeSpectrum Δ rho) : Δ * rho = 1 := by
  rw [mul_comm]; exact h

/-- **And then the coupling is fixed with no free parameter at all:**
`κρ = −2(n−1)`, which at `n = 4` is `−6`.

This is the framework's only parameter-free statement about the gravitational
coupling.  It is stated here in full so that what the next theorem destroys is
visible. -/
theorem coupling_under_lattice (n : ℕ) {Δ rho : ℝ} (h : LatticeSpectrum Δ rho) :
    couplingTimesDensity n Δ rho = -2 * ((n : ℝ) - 1) := by
  rw [couplingTimesDensity_eq, lattice_gives_one h, mul_one]

/-- At four directions: `κρ = −6`. -/
theorem coupling_under_lattice_four {Δ rho : ℝ} (h : LatticeSpectrum Δ rho) :
    couplingTimesDensity 4 Δ rho = -6 := by
  rw [coupling_under_lattice 4 h]; norm_num

/-- **A lattice has zero gap variance**, hence `CV² = 0`: all gaps are the
period. -/
theorem lattice_cvSq : Spectrum.geometricCvSq = 0 := rfl

/-- **The observed spectrum is not a lattice.**

`0.87 < CV² < 0.88`, and a lattice requires `CV² = 0`.  So the lattice
determination of the period is excluded by the mass spectrum, and with it the
only parameter-free statement the framework had about the gravitational
coupling. -/
theorem lattice_excluded : Spectrum.cvSq ≠ Spectrum.geometricCvSq :=
  Spectrum.observed_not_geometric

/-- Stated as the negative result it is: the observed `CV²` is bounded away from
the lattice value by more than `0.87`, so this is not a marginal exclusion. -/
theorem lattice_excluded_by_a_wide_margin : 0.87 < Spectrum.cvSq - Spectrum.geometricCvSq := by
  have h := Spectrum.observed_cvSq_value
  simp only [Spectrum.geometricCvSq, sub_zero]
  exact h.1

/-! ## III. The retraction that closed the route

The lattice hypothesis is the geometric mass tower, which `Audit.lean` §I already
records as retracted.  What the register did not say is that the same retraction
removed the framework's only route from the spectrum to the gravitational
coupling. -/

/-- **The geometric tower puts the log-masses on a lattice of spacing `Δ`.**

`Defect.mass_ratio_geometric` gives `m_{k+1} = e^Δ m_k`, so consecutive log-masses
differ by `Δ` — which is exactly the lattice hypothesis above. -/
theorem geometric_tower_is_the_lattice (m₀ Δ : ℝ) (k : ℤ) (hk : 0 ≤ k) :
    Defect.ScaleDefect.mass m₀ Δ (k + 1) = Real.exp Δ * Defect.ScaleDefect.mass m₀ Δ k :=
  Defect.ScaleDefect.mass_ratio_geometric m₀ Δ k hk

/-- **So the retraction cost more than the register recorded.**

The hypothesis that would have fixed `Δρ` — and hence predicted the
gravitational coupling from the mass spectrum — is the same hypothesis that
`QCD.geometric_tower_fails` and `Spectrum.observed_not_geometric` refuted.  One
retraction, two casualties, and only one of them was written down. -/
theorem retraction_closed_the_route :
    Spectrum.cvSq ≠ Spectrum.geometricCvSq
    ∧ (∀ Δ rho : ℝ, LatticeSpectrum Δ rho → couplingTimesDensity 4 Δ rho = -6) :=
  ⟨lattice_excluded, fun _ _ h => coupling_under_lattice_four h⟩

/-! ## IV. The route that remains, and what it is -/

/-- **The root-normalisation value.**  Identifying `Δ` with the root
normalisation `α` of `Dimension.alphaFromDensity` gives `Δρ = k − 1`, hence
`κρ = −2(n−1)(k−1)`, which at `n = 4`, `k = 3` is `−12`.

Nothing excludes it.  But `Dimension.density_normalization_relation` is that
definition unfolded — a tautology — and the identification of `α` with the
period is not formalised anywhere.  It is one equation with one unknown, which is
exactly what `CrossCheck.lean` exists to flag, so this is a **conversion** and
must not be reported as a determination. -/
theorem root_normalisation_value (rho : ℝ) (hrho : rho ≠ 0) (k : ℕ) :
    couplingTimesDensity 4 (Dimension.alphaFromDensity rho k) rho
      = -6 * ((k : ℝ) - 1) := by
  rw [couplingTimesDensity_eq, Dimension.density_normalization_relation rho hrho k]
  norm_num

theorem root_normalisation_at_three (rho : ℝ) (hrho : rho ≠ 0) :
    couplingTimesDensity 4 (Dimension.alphaFromDensity rho 3) rho = -12 := by
  rw [root_normalisation_value rho hrho 3]; norm_num

/-- **The two candidates give different answers**, which is what makes the
question a real one rather than a coincidence waiting to be noticed: `−6` from
the lattice and `−12` from the root normalisation.  One is excluded by data and
the other is a conversion, so the framework has no answer. -/
theorem candidates_disagree (rho : ℝ) (hrho : rho ≠ 0) {Δ : ℝ}
    (hlat : LatticeSpectrum Δ rho) :
    couplingTimesDensity 4 Δ rho ≠ couplingTimesDensity 4 (Dimension.alphaFromDensity rho 3) rho := by
  rw [coupling_under_lattice_four hlat, root_normalisation_at_three rho hrho]
  norm_num

/-! ## V. The conclusion, as a statement rather than a mood -/

/-- **The framework does not predict Newton's constant.**

Collected: the coupling's dimensionless content is `Δρ`; the lattice
determination would fix it at `1` and is excluded by the spectrum; the
root-normalisation route is a conversion; and the two candidates disagree.  What
`Index.lean` bought is real — a free *dimensionful* constant became a free
*dimensionless* one — and it does not go further.

Anyone tempted to fix `Δρ` by matching `G` should read `CrossCheck.lean` first:
one equation with one unknown always has a solution, and reporting it as a
prediction is the error this development has already made once. -/
theorem no_prediction_of_the_coupling :
    (Spectrum.cvSq ≠ Spectrum.geometricCvSq)
    ∧ (∀ rho : ℝ, rho ≠ 0 →
        couplingTimesDensity 4 (Dimension.alphaFromDensity rho 3) rho = -12)
    ∧ (∀ Δ rho : ℝ, LatticeSpectrum Δ rho → couplingTimesDensity 4 Δ rho = -6) :=
  ⟨lattice_excluded, fun rho h => root_normalisation_at_three rho h,
   fun _ _ h => coupling_under_lattice_four h⟩

end SCD.Period
