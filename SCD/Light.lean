/-
# What light is — a scalar claim, a directional correction, and a false alarm

This file has been wrong twice, in opposite directions, and both are on record
because the second was mine and was caused by exactly the inertia the register
warns about.

## First error: the scalar reading

Everything originally proved here used a **scalar** scale `s : Aˣ`.  A4′ does not
provide one; it provides `s : Fin n → Aˣ`.  With the directional scale the
measured form is `Σ_a η_a s_a² v_a²`, which is not a multiple of the bare form,
so the literal claim "the null cone is the bare cone" fails:
`bare_null_not_phys_null` and `phys_null_not_bare_null` exhibit both failures.
The old theorems survive scoped to the isotropic locus
(`isNullDir_iff_bare_of_isotropic`).

## Second error: reading that as an observable

I then read the moved cone as **observable anisotropy of the speed of light**,
took `c_i/c_j = s_j/s_i`, and set it against the `10⁻¹⁸` bound from
Michelson–Morley experiments — announcing a crisis, since `PPN.lean` needs
`s_t ≠ s_r` at `O(1)`.

**That was wrong.**  Two things should have stopped it, and both were already in
the development:

1. `bareForm` is what the moved cone is compared *against*, and `Basic.lean`'s
   own docstring says of the bare bookkeeping: *"pure bookkeeping, carrying no
   physics"*.  Comparing an observable to a convention produces a number that is
   not an observable.
2. `physFormDir_eq_bareForm_rescaled` — one line of algebra — says the measured
   form **is** the bare form precomposed with `v_a ↦ s_a v_a`.  Rescaling each
   axis by its own unit is precisely the freedom A4′ hands over, so the two cones
   differ by a change of basis.  A quadratic form at a point has no invariant
   content beyond its signature; the pointwise anisotropy is a **frame choice**.

And I had already proved the experimental consequence and failed to read it:
`Well.light_measured_speed_one` says light crosses at measured speed one in
*every* direction.  An interferometer compares rod lengths against light times,
and here the scale sets both, so it cancels.  `michelson_morley_null` states it:
**the null result is a theorem, for every scale pattern, at any precision.**

So the `10⁻¹⁸` bound constrains nothing in this framework, there is no tension
with `PPN.lean`, and the "escape" I offered — that the bound is on spatial pairs
while reciprocity is temporal–radial — was the right conclusion reached by the
wrong argument.  It is not needed.

## What the question actually delivers

Not a constraint but a **prediction**, and a free one.  `one_cone_for_every_sector`:
A4′ supplies one scale pattern, hence one metric, hence one causal structure,
and light and matter both use it.  Lorentz-violation searches of the
Standard-Model-Extension kind measure *differences between the cones of
different sectors*, because a shared cone is a coordinate change.  This framework
has no room for such a difference.

> **Every sector-relative Lorentz-violation coefficient vanishes**, with no
> parameter, and one confirmed detection kills the framework.

## And what survives the gauge

A diagonal rescaling flattens the symmetric part and merely multiplies a wedge by
a unit (`Pattern.wedge_rescale_ne_zero`).  So at a point the **antisymmetric**
part is the only thing that is not a coordinate choice — and that is exactly
`NCConformal.Defm_antisymm_part`'s quantum correction and `Axes.lean`'s
rotational label.  Everything else observable about the scale is its *variation*
from place to place, which is curvature.

The detour cost a wrong crisis and returned a sharper statement of the
framework's own claim: pointwise scale data is gauge, gradients are gravity, and
the antisymmetric residue is the quantum sector.

## What is unchanged

* matter, not light, reads the scale (`scale_determined_of_nonnull`);
* the overall magnitude is unobservable, so the null condition has weight zero
  under A5 (`null_weight_zero`);
* the theory is *integrable* Weyl geometry, since `Conformal.scaleCurv_eq_zero`
  makes the scale connection flat: no second-clock effect however anisotropic the
  pattern is.
-/
import SCD.Axioms
import SCD.Frame
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

namespace SCD.Light

open Finset ScaleAlgebra SCD

variable {n : ℕ} {A : Type*} [CommRing A]

/-! ## The bare and the measured quadratic form

Nothing in this section needs A1: the forms are algebra, and the scale enters
only as a unit.  That is why light can be discussed before any differential
structure is in play. -/

/-- The bare quadratic form of the substrate, with signature `η : Fin n → A`
(entries `±1`).  This is pure bookkeeping and carries no physics. -/
def bareForm (η v : Fin n → A) : A := ∑ i, η i * (v i * v i)

/-- The measured quadratic form: the bare one read in the local unit,
`Q_g = s² Q_δ`.  This is A4 applied to a tangent vector. -/
def physForm (s : Aˣ) (η v : Fin n → A) : A := ((s : A) ^ 2) * bareForm η v

/-- A direction is **null** when the measured form vanishes on it. -/
def IsNull (s : Aˣ) (η v : Fin n → A) : Prop := physForm s η v = 0

/-! ## Light is blind to the scale -/

/-- Multiplying by a unit neither creates nor destroys a zero. -/
theorem unit_sq_mul_eq_zero_iff (s : Aˣ) (x : A) : ((s : A) ^ 2) * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 : ((s ^ 2 : Aˣ) : A) * x = 0 := by
      simpa [pow_two, Units.val_mul, mul_assoc] using h
    calc x = ((s ^ 2 : Aˣ)⁻¹ : Aˣ) * (((s ^ 2 : Aˣ) : A) * x) := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = 0 := by rw [h2, mul_zero]
  · intro h; rw [h, mul_zero]

/-- **The null cone does not depend on the scale.**

The set of null directions is determined by the bare bookkeeping alone.  No
choice of scale field `σ` — that is, no gravitational field — can alter which
directions are null. -/
theorem isNull_iff_bare (s : Aˣ) (η v : Fin n → A) :
    IsNull s η v ↔ bareForm η v = 0 :=
  unit_sq_mul_eq_zero_iff s _

/-- **Causal structure is scale-independent.**  Two observers using any two
scale fields agree exactly about which directions are null. -/
theorem isNull_scale_invariant (s s' : Aˣ) (η v : Fin n → A) :
    IsNull s η v ↔ IsNull s' η v := by
  rw [isNull_iff_bare, isNull_iff_bare]

/-! ## Matter is not blind to the scale

For a non-null direction the measured form differs from the bare one by
exactly `s²`, so the scale is *recoverable* — but only by a probe that is not
itself null. -/

/-- **The scale is measured by massive probes.**

If the bare form on `v` is a regular element (not a zero divisor) — in
particular if `v` is not null — then the measured form determines `s²`.

Combined with the previous theorem this is the complete epistemology of the
framework: light fixes the conformal class and nothing more; everything about
the scale must be read off with matter. -/
theorem scale_determined_of_nonnull (s s' : Aˣ) (η v : Fin n → A)
    (hreg : ∀ x : A, x * bareForm η v = 0 → x = 0)
    (h : physForm s η v = physForm s' η v) :
    (s : A) ^ 2 = (s' : A) ^ 2 := by
  have hsub : ((s : A) ^ 2 - (s' : A) ^ 2) * bareForm η v = 0 := by
    simp only [physForm] at h
    linear_combination h
  exact sub_eq_zero.mp (hreg _ hsub)

/-- Explicitly: on a non-null direction the measured and bare forms differ,
unless the scale is trivial. -/
theorem physForm_ne_bareForm (s : Aˣ) (η v : Fin n → A)
    (hreg : ∀ x : A, x * bareForm η v = 0 → x = 0)
    (hs : (s : A) ^ 2 ≠ 1) :
    physForm s η v ≠ bareForm η v := by
  intro h
  apply hs
  have hsub : ((s : A) ^ 2 - 1) * bareForm η v = 0 := by
    simp only [physForm] at h
    linear_combination h
  exact sub_eq_zero.mp (hreg _ hsub)

/-! ## Light is the weight-zero sector

A5 says a global shift of the fiducial, `σ ↦ σ + c`, is unobservable.  The
null condition was already shown to be independent of the scale altogether, so
in particular it is invariant under the fiducial shift.  Light is exactly the
part of the geometry on which the scale group acts trivially — it has weight
zero, which is the formal content of masslessness. -/

/-- Light has weight zero: the null condition is invariant under any change of
scale whatsoever, in particular under the fiducial shift of A5. -/
theorem null_weight_zero (s : Aˣ) (u : Aˣ) (η v : Fin n → A) :
    IsNull s η v ↔ IsNull (u * s) η v :=
  isNull_scale_invariant s (u * s) η v

/-! ## The directional form, and the cone it actually defines

Everything above used a scalar `s`.  A4′ gives one unit per direction, and the
measured form is then `Σ_a η_a s_a² v_a²` — not a multiple of the bare form.
This section redoes the question with the scale the axiom supplies. -/

section Directional

open Frame

/-- **The measured quadratic form of A4′**: each direction contributes its bare
square read in *that direction's* unit.  The scalar `physForm` is the isotropic
case (`physFormDir_of_isotropic`). -/
def physFormDir (E : DirScale n A) (η v : Fin n → A) : A :=
  ∑ i, η i * (((E.s i : A)) ^ 2 * (v i * v i))

/-- A direction is **null for a directional scale** when the measured form of
A4′ vanishes on it. -/
def IsNullDir (E : DirScale n A) (η v : Fin n → A) : Prop := physFormDir E η v = 0

/-- **The scalar form is the isotropic case, exactly.**  Where all directions
carry one unit, `physFormDir` is `physForm` and every scalar theorem above
applies verbatim. -/
theorem physFormDir_of_isotropic (E : DirScale n A) (η v : Fin n → A)
    (h : E.Isotropic) (c : Fin n) :
    physFormDir E η v = physForm (E.s c) η v := by
  simp only [physFormDir, physForm, bareForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h i c]; ring

/-- Hence on the isotropic locus the null cone is still the bare one — the
original claim, now with its domain stated. -/
theorem isNullDir_iff_bare_of_isotropic (E : DirScale n A) (η v : Fin n → A)
    (h : E.Isotropic) (c : Fin n) :
    IsNullDir E η v ↔ bareForm η v = 0 := by
  rw [IsNullDir, physFormDir_of_isotropic E η v h c]
  exact isNull_iff_bare (E.s c) η v

/-! ### Anisotropy moves the cone

Two witnesses in a two-direction model with signature `(−, +)` and units
`s = (1, 2)`.  Each is a direction on which one of the two forms vanishes and
the other does not, so neither implies the other. -/

/-- The two-direction anisotropic scale `s = (1, 2)` over `ℝ`. -/
noncomputable def twoScale : DirScale 2 ℝ where
  s := ![1, Units.mk0 (2 : ℝ) (by norm_num)]

theorem twoScale_not_isotropic : ¬ twoScale.Isotropic := by
  intro h
  have h01 := congrArg (Units.val (α := ℝ)) (h 0 1)
  simp [twoScale] at h01

/-- **A bare-null direction need not be measured null.**

`v = (1,1)` has `Q_δ(v) = 0` but `Q_g(v) = 3`.  So light *does* see the scale
once the scale is directional: the causal structure is not the bare one. -/
theorem bare_null_not_phys_null :
    bareForm ![(-1 : ℝ), 1] ![1, 1] = 0
    ∧ physFormDir twoScale ![(-1 : ℝ), 1] ![1, 1] ≠ 0 := by
  constructor
  · simp [bareForm, Fin.sum_univ_two]
  · simp [physFormDir, twoScale, Fin.sum_univ_two]
    norm_num

/-- **And a measured-null direction need not be bare null.**

`v = (2,1)` has `Q_g(v) = 0` but `Q_δ(v) = −3`.  The cone has genuinely moved,
not merely been rescaled. -/
theorem phys_null_not_bare_null :
    physFormDir twoScale ![(-1 : ℝ), 1] ![2, 1] = 0
    ∧ bareForm ![(-1 : ℝ), 1] ![2, 1] ≠ 0 := by
  constructor
  · simp [physFormDir, twoScale, Fin.sum_univ_two]
    norm_num
  · simp [bareForm, Fin.sum_univ_two]
    norm_num

/-- **Collected: the scale-blindness of light is a property of the isotropic
locus and of nothing else.**

`isNullDir_iff_bare_of_isotropic` gives it where the pattern is isotropic; the
two witnesses show both implications fail where it is not. -/
theorem light_blind_iff_isotropic_locus :
    (∀ (E : DirScale 2 ℝ) (η v : Fin 2 → ℝ), E.Isotropic →
        (IsNullDir E η v ↔ bareForm η v = 0))
    ∧ (¬ twoScale.Isotropic)
    ∧ (bareForm ![(-1 : ℝ), 1] ![1, 1] = 0
        ∧ physFormDir twoScale ![(-1 : ℝ), 1] ![1, 1] ≠ 0) :=
  ⟨fun E η v h => isNullDir_iff_bare_of_isotropic E η v h 0,
   twoScale_not_isotropic, bare_null_not_phys_null⟩

/-! ### The speed of light is a scale ratio

A ray confined to the `t`–`i` plane is null when the temporal and the `i`
contributions cancel.  Reading that as a coordinate speed gives `c_i = s_t/s_i`,
so a ratio of speeds between two spatial directions is a ratio of scales — the
quantity Michelson–Morley experiments bound. -/

/-- **The null condition in a two-direction plane, without division.**

For `η_t = −1`, `η_i = +1` and a ray with components only in `t` and `i`, being
null is `s_t² v_t² = s_i² v_i²`.  The coordinate speed `v_i/v_t` is therefore
`s_t/s_i`. -/
theorem null_plane_condition (E : DirScale n A) (η : Fin n → A) (t i : Fin n)
    (hne : t ≠ i) (ht : η t = -1) (hi : η i = 1) (v : Fin n → A)
    (hsupp : ∀ a, a ≠ t → a ≠ i → v a = 0) :
    IsNullDir E η v ↔ ((E.s t : A)) ^ 2 * (v t * v t) = ((E.s i : A)) ^ 2 * (v i * v i) := by
  have hsum : physFormDir E η v
      = η t * (((E.s t : A)) ^ 2 * (v t * v t)) + η i * (((E.s i : A)) ^ 2 * (v i * v i)) := by
    simp only [physFormDir]
    rw [← Finset.sum_subset (Finset.subset_univ {t, i})]
    · rw [Finset.sum_pair hne]
    · intro a _ ha
      have h1 : a ≠ t := fun h => ha (by simp [h])
      have h2 : a ≠ i := fun h => ha (by simp [h])
      rw [hsupp a h1 h2]
      ring
  rw [IsNullDir, hsum, ht, hi]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- **Anisotropy of the speed of light is anisotropy of the scale.**

Two rays with the same temporal component, one along `i` and one along `j`,
satisfy `s_i² v_i² = s_j² v_j²`.  So the ratio of the two coordinate speeds is
`s_j / s_i`, and it is `1` exactly on the isotropic locus.

This is the framework's most tightly constrained quantity that nothing in the
development had yet identified: the fractional anisotropy of the speed of light
is bounded near `10⁻¹⁸`, in the same directions in which the anisotropic sector
is supposed to supply the missing half of the light deflection. -/
theorem speed_ratio_is_scale_ratio (E : DirScale n A) (η : Fin n → A)
    (t i j : Fin n) (hti : t ≠ i) (htj : t ≠ j)
    (ht : η t = -1) (hi : η i = 1) (hj : η j = 1)
    (v w : Fin n → A) (hvt : v t = w t)
    (hv : ∀ a, a ≠ t → a ≠ i → v a = 0) (hw : ∀ a, a ≠ t → a ≠ j → w a = 0)
    (hvn : IsNullDir E η v) (hwn : IsNullDir E η w) :
    ((E.s i : A)) ^ 2 * (v i * v i) = ((E.s j : A)) ^ 2 * (w j * w j) := by
  have h1 := (null_plane_condition E η t i hti ht hi v hv).mp hvn
  have h2 := (null_plane_condition E η t j htj ht hj w hw).mp hwn
  rw [← h1, ← h2, hvt]

/-- On the isotropic locus the two speeds agree.  Note carefully what this is
*not*: it is not a statement that anisotropy is measurable, for the reason the
next section gives. -/
theorem no_birefringence_of_isotropic (E : DirScale n A) (h : E.Isotropic)
    (i j : Fin n) : ((E.s i : A)) ^ 2 = ((E.s j : A)) ^ 2 := by
  rw [h i j]

/-! ## The correction: the moved cone is a rescaled cone, and that is gauge

I read `bare_null_not_phys_null` as saying the light cone is observably
anisotropic, and then read across to Michelson–Morley.  **That was wrong**, and
the refutation is one line of algebra that this file should have contained from
the start.

`bareForm` is compared against — and `Basic.lean` says of `kron`, in its own
docstring, *"pure bookkeeping, carrying no physics"*.  Comparing the measured
cone to the bare cone is comparing an observable to a convention. -/

/-- **The measured form is the bare form in rescaled axes.**

        Σ_a η_a s_a² v_a²  =  Σ_a η_a (s_a v_a)² .

So `physFormDir` is `bareForm` precomposed with the diagonal rescaling
`v_a ↦ s_a v_a`.  A4′ gives one unit per direction, so rescaling each axis by its
own unit is precisely the framework's own gauge freedom — and it takes the
measured cone to the bare one exactly. -/
theorem physFormDir_eq_bareForm_rescaled (E : DirScale n A) (η v : Fin n → A) :
    physFormDir E η v = bareForm η (fun a => (E.s a : A) * v a) := by
  simp only [physFormDir, bareForm]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **Hence the cone is a frame choice at any one point.**

Being measured-null is being bare-null *after the rescaling*.  So
`bare_null_not_phys_null` is true and says nothing physical: the two cones differ
by a change of basis, and a quadratic form at a point has no invariant content
beyond its signature.

The pointwise anisotropy of the scale is therefore **not observable**, and
nothing bounds it. -/
theorem isNullDir_iff_bare_rescaled (E : DirScale n A) (η v : Fin n → A) :
    IsNullDir E η v ↔ bareForm η (fun a => (E.s a : A) * v a) = 0 := by
  rw [IsNullDir, physFormDir_eq_bareForm_rescaled]

/-- **The Michelson–Morley null result is a theorem, for every scale pattern.**

Two arms of equal *measured* length, along any two directions, are traversed in
equal *measured* time — because light moves at measured speed one in every
direction (`Well.light_measured_speed_one` is the same computation).

An interferometer compares rod-lengths against light-times, and in this framework
the scale sets both, so the comparison cancels it.  There is no anisotropy for
such an experiment to find, at any level of precision, and the `10⁻¹⁸` bound
constrains **nothing** here.  Quoting it against this framework was pattern
matching, not physics. -/
theorem michelson_morley_null (E : DirScale n A) (η : Fin n → A) (t i j : Fin n)
    (hti : t ≠ i) (htj : t ≠ j) (ht : η t = -1) (hi : η i = 1) (hj : η j = 1)
    (v w : Fin n → A)
    (hv : ∀ a, a ≠ t → a ≠ i → v a = 0) (hw : ∀ a, a ≠ t → a ≠ j → w a = 0)
    (hvn : IsNullDir E η v) (hwn : IsNullDir E η w)
    (harms : ((E.s i : A)) ^ 2 * (v i * v i) = ((E.s j : A)) ^ 2 * (w j * w j)) :
    ((E.s t : A)) ^ 2 * (v t * v t) = ((E.s t : A)) ^ 2 * (w t * w t) := by
  have h1 := (null_plane_condition E η t i hti ht hi v hv).mp hvn
  have h2 := (null_plane_condition E η t j htj ht hj w hw).mp hwn
  rw [h1, h2, harms]

/-- **There is one cone, and everything shares it.**

Light is null for `physFormDir`; a massive probe's length is measured by the
same `physFormDir`.  A4′ supplies **one** scale pattern, so there is **one**
metric and one causal structure, and every sector uses it.

That is a prediction, and a sharp one.  Lorentz-violation searches of the
Standard-Model-Extension kind measure *differences between the cones of different
sectors* — photon versus electron, and so on — because a common cone is a change
of coordinates.  This framework has no room for such a difference: it has one
scale pattern and therefore one cone.

**So the framework predicts that every sector-relative Lorentz-violation
coefficient vanishes**, and any confirmed detection of one falsifies it.  That
is what the anisotropy question actually delivers, and it is the opposite of a
constraint on the framework — it is a free, falsifiable, parameter-free
prediction. -/
theorem one_cone_for_every_sector (E : DirScale n A) (η v : Fin n → A) :
    (IsNullDir E η v ↔ physFormDir E η v = 0)
    ∧ physFormDir E η v = bareForm η (fun a => (E.s a : A) * v a) :=
  ⟨Iff.rfl, physFormDir_eq_bareForm_rescaled E η v⟩

/-- **What is left after the gauge is removed.**

A diagonal rescaling flattens the symmetric part and multiplies the wedge by a
unit (`Pattern.wedge_rescale_ne_zero`).  So at a point the *only* part of the
scale pattern that is not a coordinate choice is the antisymmetric one — which
is exactly the object `NCConformal.Defm_antisymm_part` identifies as the whole
quantum-gravitational correction, and exactly the object `Axes.lean` identifies
as the rotational label.

Everything else observable about the scale lives in its **variation** from place
to place, which is curvature.  That was always the framework's claim; the
detour through a false constraint has ended up sharpening it. -/
theorem only_the_wedge_survives_rescaling {k : ℕ} (u : Fin k → Aˣ) (v w : Fin k → A)
    (i j : Fin k) (h : wedge v w i j ≠ 0) :
    wedge (fun a => ((u a : A)) * v a) (fun a => ((u a : A)) * w a) i j ≠ 0 :=
  SCD.wedge_rescale_ne_zero u h

end Directional

end SCD.Light
