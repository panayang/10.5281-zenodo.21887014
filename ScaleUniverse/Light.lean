/-
# What light is

In this framework the question "what is light?" has a sharp answer, and it is
not "a wave" or "a particle".

The measured quadratic form is the bare one carrying the scale factor,
`Q_g = s² Q_δ`.  Since `s` is a unit, multiplying by it cannot create or
destroy a zero.  Therefore:

* **the null cone is exactly the same for every scale field** — light does not
  see `σ` at all;
* **for every non-null direction the scale is recoverable** from the ratio of
  the measured to the bare form — matter does see `σ`, and is the only thing
  that does.

Together these say: *light is the comparator of scale, and is itself blind to
it.*  The causal (conformal) structure is what survives forgetting the scale;
the scale is what is left over once the causal structure is quotiented out.
Light is precisely the weight-zero part of the geometry — the part that A5's
fiducial shift cannot touch — which is why it, alone, can carry the comparison
of local units from one event to another without circularity.

This also settles why the theory is *integrable* Weyl geometry rather than
Weyl's original one: `Conformal.scaleCurv_eq_zero` shows the scale connection
is flat, so transporting a unit along a closed loop returns it unchanged and
there is no second-clock effect.
-/
import ScaleUniverse.Axioms

namespace ScaleUniverse.Light

open Finset ScaleAlgebra ScaleUniverse

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-! ## The bare and the measured quadratic form -/

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

end ScaleUniverse.Light
