/-
# The layers: incompatibility appears, thresholds are computed, outcomes are classes

`Resolution.lean` gave resolution an algebraic form and listed four things it did
not do.  Three are done here.  The fourth — that the filtration is **postulated**,
with nothing in A1–A7 building one — is untouched and stays in the register.

## I.  Incompatibility appears at a finite resolution

This was the item with physical content, and without it the resolution index was
decoration: `Resolution.lean` showed an incompatible pair at the sharpest
resolution and no incompatibility at the coarsest, which is consistent with the
index doing nothing in between.

`matFilt` cuts `Triple.Mat 2` by powers of the scalar matrix `X₀`.  Then
`compat_zero` and `incompat_one`:

> `E₀₀` and `E₀₁` are **jointly resolvable at resolution `0` and not at
> resolution `1`.**

Their commutator is `E₀₁`, whose `(0,1)` entry is `1`; if it were `X₀·B` then
evaluating at zero would give `1 = 0`.  So a coarse probe sees a compatible pair
and a finer one sees an incompatibility — the index is doing work.

## II.  The algebraic resolution *is* `Emergence.resolved`

`Resolution.lean` left the two notions standing side by side, real thresholds on
one side and ideals on the other.  `HasThreshold` is the bridge: a function
giving, for each element, the resolution above which it becomes visible.  Given
one, `resolved_is_emergence_resolved` says what a probe resolves in a family of
ring elements is **exactly** `Emergence.resolved` of the induced thresholds.  The
`+1` is the difference between *invisible up to `k`* and *visible from `k`*, not
a difference of content.

And the thresholds are not free data.  `monomial_threshold`: filtering
`Polynomial ℝ` by powers of `X`, the threshold of `Xʲ` is `j` — **its degree**.
`Emergence.lean` takes `μ` as given; here it is read off the ring.

**What this does not claim.**  The bridge is to `Emergence.resolved`'s *form*.
Nothing here connects `thr` to a measured spectrum, so §V.x's gap —
`Spectrum.gaps` against `Internal.record` — is **not** closed by it.  Two notions
of resolution have been identified with each other; neither has been identified
with a measurement.

## III.  What an outcome would be, and what is missing

`Indistinguishable F k a b` says the difference is invisible at `k`.  It is an
equivalence (`indist_equivalence`), so **a resolution partitions the ring**, and a
class is what a probe of that resolution can report — which is what an *outcome*
would be.  `indist_of_le`: classes merge as the probe coarsens, which is the
behaviour any account of outcomes has to have.

`compatible_iff_orders_indistinguishable` is an unfolding and is labelled one.
Its worth is the reading: *two things are jointly resolvable exactly when the
order of operating on them is invisible* — `Ordering.lean`'s obstruction and
`Triple.influence_asymmetry`'s discrepancy, seen at a resolution.

**And then it stops.**  A probability is a weight on the classes and there is
none.  The framework's only measure-like notion is **counting** — `Entropy.lean`
derives the arrow from finite resolution and a bijective microdynamics,
`Attraction.lean` makes the source a count — so if a weight is ever to come from
inside, that is where it would come from.  Whether the classes are finite in any
model is not established here, and without that the counting route is a direction
rather than an argument.

So G4 acquires **vocabulary and no theory**, and saying which is which is the
point of the section.
-/
import SCD.Resolution
import SCD.Emergence

namespace SCD.Layers

open SCD ScaleAlgebra Quantum Resolution MvPolynomial


open SCD ScaleAlgebra Quantum Resolution MvPolynomial

/-! ## Gap 3: incompatibility appears at a finite resolution -/

/-- The central element the layers are cut by: the scalar matrix `X₀`. -/
noncomputable def xs : Triple.Mat 2 := (X 0 : MvPolynomial (Fin 2) ℝ) • (1 : Triple.Mat 2)

theorem xs_central (y : Triple.Mat 2) : xs * y = y * xs := by
  simp only [xs, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- The layered filtration on the matrix model. -/
noncomputable def matFilt : Filtration (Triple.Mat 2) := powerFiltration xs xs_central

/-- Two matrix units. -/
noncomputable def e00 : Triple.Mat 2 := !![1, 0; 0, 0]
noncomputable def e01 : Triple.Mat 2 := !![0, 1; 0, 0]

theorem ad_e00_e01 : ad e00 e01 = e01 := by
  simp only [ad, e00, e01]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Compatible at the coarsest resolution.** -/
theorem compat_zero : matFilt.Compatible 0 e00 e01 :=
  compatible_at_zero xs xs_central e00 e01

/-- **And incompatible one step finer.**

`[E₀₀, E₀₁] = E₀₁`, whose `(0,1)` entry is `1`; if it were `X₀ · B` then
evaluating at zero would give `1 = 0`.  So the pair is jointly resolvable at
resolution `0` and not at resolution `1`: **incompatibility appears at a finite
order**, which is the statement with physical content. -/
theorem incompat_one : ¬ matFilt.Compatible 1 e00 e01 := by
  rintro ⟨B, hB⟩
  rw [ad_e00_e01] at hB
  have h01 := congrFun (congrFun hB 0) 1
  simp only [xs, pow_one, Matrix.smul_mul, Matrix.smul_apply, Matrix.one_mul,
    e01, smul_eq_mul] at h01
  have := congrArg (MvPolynomial.eval (fun _ => (0 : ℝ))) h01
  simp at this

/-! ## Gap 2: the algebraic resolution is `Emergence.resolved` -/

variable {A : Type*} [Ring A]

/-- A **threshold function** for a filtration: the resolution above which an
element becomes visible. -/
def HasThreshold (F : Filtration A) (thr : A → ℕ) : Prop :=
  ∀ (k : ℕ) (a : A), F.Resolved k a ↔ thr a < k

/-- **The algebraic resolved-set is `Emergence.resolved`.**

Given a threshold function, what a probe of resolution `k` resolves in a family
of ring elements is exactly `Emergence.resolved` of the induced thresholds.  The
`+1` is the difference between "invisible up to `k`" and "visible from `k`", not
a change of content. -/
theorem resolved_is_emergence_resolved {F : Filtration A} {thr : A → ℕ}
    (h : HasThreshold F thr) (e : ℕ → A) (k : ℕ) :
    {i | F.Resolved k (e i)}
      = Emergence.resolved (fun i => ((thr (e i) : ℝ) + 1)) (k : ℝ) := by
  ext i
  simp only [Set.mem_setOf_eq, Emergence.mem_resolved, h k (e i)]
  constructor
  · intro hlt
    have : (thr (e i) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlt
    exact this
  · intro hle
    have : (thr (e i) : ℕ) + 1 ≤ k := by exact_mod_cast hle
    exact this

/-! ### A threshold function that is not postulated

Monomials in one variable, filtered by powers of the variable: the threshold of
`Xʲ` is `j`, which is its degree.  So the thresholds `Emergence.lean` takes as
free data are, here, computed from the ring. -/

noncomputable def polyFilt : Filtration (Polynomial ℝ) :=
  powerFiltration Polynomial.X (fun y => by ring)

theorem monomial_threshold (j k : ℕ) :
    polyFilt.Resolved k (Polynomial.X ^ j) ↔ j < k := by
  constructor
  · intro h
    by_contra hkj
    have hk : k ≤ j := Nat.le_of_not_lt hkj
    exact h ⟨Polynomial.X ^ (j - k), by rw [← pow_add, Nat.add_sub_cancel' hk]⟩
  · rintro hjk ⟨B, hB⟩
    have hX : (Polynomial.X : Polynomial ℝ) ≠ 0 := Polynomial.X_ne_zero
    have hB0 : B ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hB
      exact pow_ne_zero j hX hB
    have hd := congrArg Polynomial.natDegree hB
    rw [Polynomial.natDegree_mul (pow_ne_zero k hX) hB0,
      Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at hd
    omega

/-- **So the thresholds are computed, not postulated.**

`Emergence.lean` takes the thresholds `μ` as free data.  Here they are read off
the ring: the threshold of a monomial is its degree. -/
theorem polyFilt_hasThreshold_on_monomials (j k : ℕ) :
    polyFilt.Resolved k (Polynomial.X ^ j) ↔ (fun i => i) j < k :=
  monomial_threshold j k

/-! ## Gap 4: what an outcome would be, and what is missing -/

/-- Two elements **agree at resolution `k`** when their difference is invisible
there. -/
def Indistinguishable (F : Filtration A) (k : ℕ) (a b : A) : Prop := F.mem k (a - b)

theorem indist_refl (F : Filtration A) (k : ℕ) (a : A) : Indistinguishable F k a a := by
  rw [Indistinguishable, sub_self]; exact F.zero_mem k

theorem indist_symm {F : Filtration A} {k : ℕ} {a b : A}
    (h : Indistinguishable F k a b) : Indistinguishable F k b a := by
  rw [Indistinguishable, show b - a = -(a - b) by abel]
  exact F.neg_mem k _ h

theorem indist_trans {F : Filtration A} {k : ℕ} {a b c : A}
    (hab : Indistinguishable F k a b) (hbc : Indistinguishable F k b c) :
    Indistinguishable F k a c := by
  rw [Indistinguishable, show a - c = (a - b) + (b - c) by abel]
  exact F.add_mem k _ _ hab hbc

/-- **Agreeing at a resolution is an equivalence**, so a resolution partitions
the ring.  A class is what an *outcome* would be: what a probe of that resolution
can report. -/
theorem indist_equivalence (F : Filtration A) (k : ℕ) :
    Equivalence (Indistinguishable F k) :=
  ⟨indist_refl F k, indist_symm, indist_trans⟩

/-- **A coarser probe identifies more.**  Classes merge as resolution coarsens,
which is the behaviour an account of outcomes has to have. -/
theorem indist_of_le {F : Filtration A} {k l : ℕ} (h : k ≤ l) {a b : A}
    (hl : Indistinguishable F l a b) : Indistinguishable F k a b :=
  F.antitone k l h _ hl

/-- **Compatibility is indistinguishability of the two orders.**

This is an unfolding of the two definitions and is stated as one — `ad a b` is
`a*b - b*a`, so it says nothing new by itself.  What it is worth is the reading:
*two things are jointly resolvable exactly when the order of operating on them is
invisible*, which is `Ordering.lean`'s obstruction and
`Triple.influence_asymmetry`'s discrepancy seen at a resolution. -/
theorem compatible_iff_orders_indistinguishable (F : Filtration A) (k : ℕ) (a b : A) :
    F.Compatible k a b ↔ Indistinguishable F k (a * b) (b * a) := Iff.rfl


end SCD.Layers
