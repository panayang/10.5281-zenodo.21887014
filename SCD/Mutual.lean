/-
# Why observation is blind to anisotropy — the real reason — and a symmetric
# three-place candidate

## 0.  A correction first

`Triple.lean` §IV and `Audit` §V.u said the observation process is blind to the
leading anisotropic correction `[σ_a, σ_b]` because *"every term in `influence`
carries a single directional scale `σ_c`"*.  **That is false.**  Reading the
definition:

        influence σ a b c = ∂_a∂_b σ_c − (∂_bσ_a)(∂_aσ_c)
                                        − (∂_aσ_b)(∂_bσ_c) + (∂_aσ_c)(∂_bσ_c)

the second and third terms carry `σ_a` and `σ_b` — the *observed* pair's scales —
multiplied against the observer's.  `influence_sees_the_pair_scales` exhibits two
configurations agreeing on `σ_c` and differing in the influence, so the
dependence is real.

## I.  The real reason, which is sharper

The observed pair's scales are present in the process and absent from the
**asymmetry**:

> `asymmetry_depends_only_on_the_observer` — the difference between the two
> readings of one observation is a function of `σ_c` alone.

And the reason is not that the cross terms are missing but that they **exchange
exactly**: the second term of `influence σ a b c` is, factor for factor and in the
same order, the third term of `influence σ b a c`.  So they cancel in the
difference and the quantum content is carried entirely by `(∂_aσ_c)(∂_bσ_c)`.

**Which is exactly the diagnosis you reached: the observation is made by a single
direction and its content is independent of how the observer stands relative to
the pair.**  The relative structure is in the expression and cancels out of what
can be observed.

## II.  And that cancellation rests on an ordering nothing fixes

`Diagonal.lean` computes the connection and the Ricci contraction over a
**`CommRing`**.  In a commutative ring the order of the factors in each term is
not a choice — there is nothing to choose.  Carrying those formulas to a
non-commutative ring **requires an operator ordering, and the commutative
computation does not determine it.**

So `influence`'s blindness is downstream of an *unforced* choice: the particular
ordering under which the two cross terms exchange.  That is a statement about the
development rather than a theorem, and it is where the three candidates you named
have to be settled — not by preference, but by whatever fixes the ordering.  At
present nothing does, and this is registered.

## III.  The third candidate, implemented

Of the three you raised — relative direction, scale–scale relations, and
observer/observed not being unequal — the third is the one that can be built now,
because the framework already contains its two-index case.

`Pattern.wedge v w i j = v_i w_j − v_j w_i` is the **antisymmetrised product of a
pair**, and `wedge_self_eq_commutator` says `wedge σ σ a b = [σ_a, σ_b]` — the
rotational label, and the leading anisotropic object.  The three-index version is
forced by the same construction:

> **`triWedge σ a b c = σ_a[σ_b,σ_c] + σ_b[σ_c,σ_a] + σ_c[σ_a,σ_b]`**,

and `triWedge_eq_alternating` proves this **is** the totally antisymmetrised triple
product `Σ_π sgn(π) σ_{π(a)}σ_{π(b)}σ_{π(c)}`.  So it is not an invention with a
convenient shape; it is the next term in a sequence the framework already
started.

What it has that `influence` lacks:

* **all three directions enter identically** — swapping any two flips the sign
  (`triWedge_antisymm`), so no direction is the observer and no pair is the
  observed.  Your third option, exactly;
* **it is built from the leading commutator.**  `triWedge_from_dirCommutator`: its
  brackets are `Anisotropic.dirCommutator`, the object that carries `ħ` times
  *two* gradients (`NCSize.dir_commutator_star`), where the pair-swap asymmetry of
  `Triple.lean` carries four;
* **it vanishes exactly where it should** — identically in a commutative ring
  (`triWedge_comm_zero`) and on the isotropic locus where all directional scales
  agree (`triWedge_isotropic_zero`), which is `Anisotropic.dirCommutator_isotropic`
  one level up;
* **and it is not identically zero** (`triWedge_witness`): in two-by-two matrices,
  three matrix units give `2E₀₀ + E₁₁`.

## IV.  What this is and is not

**It is a proposal.**  Nothing derives that observation must take this form.  What
is shown is that your third option is *implementable natively* — the object is
the framework's own wedge at three indices, it treats the parties equally, and it
reaches the leading anisotropic sector that `influence` cannot.

**What would make it forced** is an argument that the three-place observation
must be totally antisymmetric.  There is a candidate reason and it is not
developed here: `Explanation.cycle_of_three` says the minimal determination
structure is a three-cycle in which each direction is the observer for exactly one
pair, so a description privileging one role has broken a symmetry the structure
has.  Turning that into a derivation is the open item.

**And the ordering question of §II is prior to all of this.**  Until something
fixes the operator ordering in the non-commutative extension of `Diagonal.lean`,
both `influence` and `triWedge` are choices, and the difference between them is a
choice about what observation is.  That is the honest state.
-/
import SCD.Triple
import SCD.Anisotropic
import SCD.Pattern

namespace SCD.Mutual

open SCD ScaleAlgebra Quantum

/-! ## I. The correction: the pair's scales are present, and cancel -/

section Correction

open MvPolynomial

/-- Two configurations agreeing on the observer's scale `σ₂` and differing in the
observed pair's. -/
noncomputable def withPair : Fin 3 → MvPolynomial (Fin 3) ℝ := ![X 1, 0, X 0]

/-- The same with the pair flat. -/
noncomputable def withoutPair : Fin 3 → MvPolynomial (Fin 3) ℝ := ![0, 0, X 0]

/-- **The observed pair's scales are in the process.**

The two configurations agree on `σ₂` — the observer — and give different
influences.  So `Triple.lean`'s claim that only `σ_c` appears was wrong: the
second and third terms of `influence` carry `σ_a` and `σ_b`. -/
theorem influence_sees_the_pair_scales :
    withPair 2 = withoutPair 2
    ∧ Determination.influence withPair 0 1 2
        ≠ Determination.influence withoutPair 0 1 2 := by
  refine ⟨rfl, ?_⟩
  intro h
  have hv := congrArg (eval (fun _ => (0 : ℝ))) h
  simp [Determination.influence, withPair, withoutPair] at hv

end Correction

variable {n : ℕ} {M : Type*} [Ring M]

section NeedsScaleAlgebra

variable [ScaleAlgebra n M]

/-- **But the asymmetry sees only the observer.**

The difference between the two readings of one observation is a function of `σ_c`
alone — `Triple.influence_asymmetry` restated as an independence.  The observed
pair's scales are present in the process and absent from what distinguishes the
two readings, because the two cross terms exchange factor for factor.

This is the precise sense in which the observation is made *by a single
direction*: the relative structure between observer and pair is in the expression
and cancels out of the observable part. -/
theorem asymmetry_depends_only_on_the_observer (σ σ' : Fin n → M) (a b c : Fin n)
    (h : σ c = σ' c) :
    Triple.inf σ a b c - Triple.inf σ b a c
      = Triple.inf σ' a b c - Triple.inf σ' b a c := by
  rw [Triple.influence_asymmetry, Triple.influence_asymmetry, h]

end NeedsScaleAlgebra

/-! ## II. The symmetric three-place candidate -/

/-- **The three-index wedge.**

`Pattern.wedge` antisymmetrises a product of two; this antisymmetrises a product
of three.  All three directions enter identically — there is no observer and no
observed pair.

A proposal, not a derivation: nothing shows observation must take this form. -/
def triWedge (σ : Fin n → M) (a b c : Fin n) : M :=
  σ a * ad (σ b) (σ c) + σ b * ad (σ c) (σ a) + σ c * ad (σ a) (σ b)

/-- **It is the totally antisymmetrised triple product.**

So it is the next term in a sequence the framework already started with the
wedge, rather than an object with a convenient shape. -/
theorem triWedge_eq_alternating (σ : Fin n → M) (a b c : Fin n) :
    triWedge σ a b c
      = σ a * σ b * σ c - σ a * σ c * σ b - σ b * σ a * σ c
        + σ b * σ c * σ a + σ c * σ a * σ b - σ c * σ b * σ a := by
  simp only [triWedge, ad]
  noncomm_ring

/-- **Swapping any two directions flips the sign**, so no direction plays a
privileged role.  This is the content of "observer and observed are not
unequal". -/
theorem triWedge_antisymm (σ : Fin n → M) (a b c : Fin n) :
    triWedge σ a b c = - triWedge σ b a c := by
  simp only [triWedge, ad]
  noncomm_ring

/-- **Its brackets are the leading anisotropic object.**

`Anisotropic.dirCommutator` carries `ħ` times *two* gradients
(`NCSize.dir_commutator_star`), where the pair-swap asymmetry of `Triple.lean`
carries four.  So this candidate reaches the sector observation was blind to. -/
theorem triWedge_from_dirCommutator (σ : Fin n → M) (a b c : Fin n) :
    triWedge σ a b c
      = σ a * Anisotropic.dirCommutator σ b c
        + σ b * Anisotropic.dirCommutator σ c a
        + σ c * Anisotropic.dirCommutator σ a b := rfl

/-- **It vanishes identically in the commutative sector.** -/
theorem triWedge_comm_zero {A : Type*} [CommRing A]
    (σ : Fin n → A) (a b c : Fin n) : triWedge σ a b c = 0 := by
  simp only [triWedge, ad]
  ring

/-- **And on the isotropic locus**, where every direction carries the same scale
— `Anisotropic.dirCommutator_isotropic` one level up. -/
theorem triWedge_isotropic_zero (σ₀ : M) (a b c : Fin n) :
    triWedge (fun _ => σ₀) a b c = 0 := by
  simp only [triWedge, ad]
  noncomm_ring

/-! ## III. It is not identically zero -/

section Witness

/-- Three matrix units, as a directional scale pattern on three directions. -/
def units3 : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ := ![!![1, 0; 0, 0], !![0, 1; 0, 0], !![0, 0; 1, 0]]

/-- **The symmetric candidate is not trivial.**

With `σ₀ = E₀₀`, `σ₁ = E₀₁`, `σ₂ = E₁₀` the value is `2E₀₀ + E₁₁`, and no
derivative is taken anywhere — the object is zeroth order, which is what makes it
the leading one. -/
theorem triWedge_witness :
    triWedge units3 0 1 2 = !![2, 0; 0, 1] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [triWedge, ad, units3, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem triWedge_not_identically_zero :
    ∃ (σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (a b c : Fin 3), triWedge σ a b c ≠ 0 := by
  refine ⟨units3, 0, 1, 2, ?_⟩
  rw [triWedge_witness]
  intro h
  have := congrFun (congrFun h 1) 1
  norm_num at this

/-- **Collected: the correction and the candidate.**

The observed pair's scales are in the process and cancel out of the asymmetry;
the symmetric three-index object treats all parties alike, is built from the
leading commutator, vanishes classically and isotropically, and is not
identically zero. -/
theorem summary :
    (withPair 2 = withoutPair 2
      ∧ Determination.influence withPair 0 1 2
          ≠ Determination.influence withoutPair 0 1 2)
    ∧ (∃ (σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (a b c : Fin 3), triWedge σ a b c ≠ 0) :=
  ⟨influence_sees_the_pair_scales, triWedge_not_identically_zero⟩

end Witness

end SCD.Mutual
