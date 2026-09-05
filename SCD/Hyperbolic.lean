/-
# One of the two obstructions removed, and the source law is hyperbolic

§V.au found `κ` and the observables in different geometries, joined only by
`Anisotropic.ChrDir_of_isotropic`, whose hypotheses are **two**: the isotropic
locus *and* Euclidean signature.  §V.av removed the worry about the coefficient.
This file removes **one** of the two hypotheses and is explicit that the other
survives — the one the physics violates.

## What is closed

`diagonal_chr_isotropic`: at the isotropic locus, `Diagonal.Chr η w σ` **is**
`EtaTrace.ChrE η σ`, at **any** signature.  `diagonal_ric_isotropic` carries it to
the Ricci tensors; the two files contract differently — `Diagonal` differentiates
the trace along one index, `EtaTrace` along the other — and `hess_symm` closes the
difference.

So the sectors are the same geometry wherever the scale is isotropic, with no
Euclidean restriction.  That is strictly more than the development had.

## What is not closed, said first rather than last

**The physics is anisotropic.**  `Diagonal.vacuum_scale_sum` gives
`σ_t' + σ_r' = 0`, so the Schwarzschild-like solution the gravity chain runs
through has `σ_t ≠ σ_r`.  The bridge above holds where all directional scales
agree, and there they do not.

> **The signature obstruction is gone; the isotropy obstruction is not, and it is
> the one the observables sit outside.**

§V.au's disconnect therefore narrows from two obstructions to one, and the
remaining task is now exactly stateable: `RscE_eq` for a **directional** scale.
Calling this a closure would be the "same shape for same object" error §V.av
named in advance, one section early.

## The wave equation, which is what the corrected operator buys

§V.av showed A6″'s operator is the d'Alembertian, so the source law
`□σ = Δ·ν` is **hyperbolic**.  The consequence is here.

`WaveProfile k m σ` is the algebraic surrogate for a disturbance with wavefronts
normal to `k`: the Hessian is rank one along `k`.  No analysis is used, because
none is available — `Index.lean` records the same limitation about Gauss's law.

* `lapE_of_waveProfile` — the d'Alembertian of such a profile is
  `Light.bareForm η k * m`, the framework's **own** quadratic form on `k`;
* `vacuum_wave_is_null` — in vacuum, with a non-degenerate profile,
  `Light.bareForm η k = 0`;
* `characteristic_is_null` — and that is `Light.IsNull` for any unit scale, since
  `physForm` is `s²` times the bare form;
* `null_is_unit_speed` — with a Lorentzian signature it reads
  `∑_{i≠t} kᵢ² = kₜ²`.

> **Scale disturbances propagate on the framework's own null cone.**

`Light.lean` defined that cone **kinematically** — the directions on which the
measured form vanishes — and nothing said anything propagates along it.  This is
the dynamical half, and the two cones coincide.

## What is not claimed about the waves

That these are gravitational waves.  The disturbance here is of the **scalar**
scale; a gravitational wave is a transverse traceless mode, which is
directional, and `Waves.lean`'s monopole and dipole discussion is about the
radiative multipoles rather than this.  What is claimed is narrower and was not
available before: the source law has characteristics, they are null, and the null
cone they pick out is the one the framework already had.

Nor is any existence claimed.  `WaveProfile` is an ansatz; nothing here shows a
scale algebra containing a non-trivial one.  That is the same debt `ExpPoly.lean`
was written to pay for `ScaleField`, and it is unpaid here.
-/
import SCD.EtaTrace
import SCD.Diagonal
import SCD.Light

namespace SCD.Hyperbolic

open SCD ScaleAlgebra Finset

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]
variable (η : Fin n → A) (w : Aˣ) (σ : A)


omit [ScaleAlgebra n A] in
/-- With one unit in every direction, every ratio is `1`. -/
theorem ratio_const (a u : Fin n) : Diagonal.ratio (fun _ : Fin n => w) a u = 1 := by
  simp only [Diagonal.ratio]
  rw [mul_inv_cancel]; rfl

/-- **The anisotropic connection at the isotropic locus is the conformal one —
at any signature.** -/
theorem diagonal_chr_isotropic (u a b : Fin n) :
    Diagonal.Chr η (fun _ => w) (fun _ => σ) u a b = EtaTrace.ChrE η σ u a b := by
  simp only [Diagonal.Chr, EtaTrace.ChrE, ratio_const, mul_one, sig]
  ring

/-- **And so are the Ricci tensors.**

The two files contract differently — `Diagonal` differentiates the connection's
trace along one index and `EtaTrace` along the other — and `hess_symm` closes the
difference. -/
theorem diagonal_ric_isotropic (hη : ∀ a, η a * η a = 1) (b e : Fin n) :
    Diagonal.Ric η (fun _ => w) (fun _ => σ) b e = EtaTrace.RicE η σ b e := by
  simp only [Diagonal.Ric, EtaTrace.RicE, EtaTrace.RmE,
    diagonal_chr_isotropic η w σ, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h2 : d b (∑ c, EtaTrace.ChrE η σ c c e) = ∑ a, d e (EtaTrace.ChrE η σ a b a) := by
    rw [EtaTrace.sum_ChrE_diag η hη, d_nsmul]
    have h : ∀ a : Fin n, d e (EtaTrace.ChrE η σ a b a)
        = d e (EtaTrace.ChrE η σ a a b) := fun a => by rw [EtaTrace.ChrE_symm η]
    rw [Finset.sum_congr rfl (fun a _ => h a), ← d_sum, EtaTrace.sum_ChrE_diag η hη, d_nsmul]
    exact congrArg _ (hess_symm σ b e)
  have h3 : (∑ x, (∑ c, EtaTrace.ChrE η σ c c x) * EtaTrace.ChrE η σ x b e)
      = ∑ a, ∑ m, EtaTrace.ChrE η σ a a m * EtaTrace.ChrE η σ m b e := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => by rw [← Finset.sum_mul]
  have h4 : (∑ c, ∑ x, EtaTrace.ChrE η σ c b x * EtaTrace.ChrE η σ x c e)
      = ∑ a, ∑ m, EtaTrace.ChrE η σ a e m * EtaTrace.ChrE η σ m b a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => by
      rw [EtaTrace.ChrE_symm η σ c b x, EtaTrace.ChrE_symm η σ x c e]
      ring
  rw [h2, h3, h4]
  ring

/-! ## The wave equation -/

/-- A **wave profile**: the Hessian is rank one along a covector `k`.

This is the algebraic surrogate for a disturbance with wavefronts normal to `k`;
`m` is its profile.  No analysis is used and none is available. -/
def WaveProfile (k : Fin n → A) (m σ : A) : Prop := ∀ i j, hess σ i j = k i * k j * m

/-- **The d'Alembertian of a wave profile is the bare form of its covector.** -/
theorem lapE_of_waveProfile {k : Fin n → A} {m : A} (h : WaveProfile k m σ) :
    EtaTrace.lapE n η σ = Light.bareForm η k * m := by
  simp only [EtaTrace.lapE, Light.bareForm, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [h i i]; ring

/-- **So in vacuum the covector is null.**

`□σ = Δ·ν` with no source is `□σ = 0`, and for a non-degenerate profile that
forces `∑ᵢ ηᵢ kᵢ² = 0` — which is `Light.bareForm`, the framework's own null
condition.  **Scale disturbances propagate on the light cone.** -/
theorem vacuum_wave_is_null {k : Fin n → A} {m : A} (hm : IsUnit m)
    (h : WaveProfile k m σ) (hvac : EtaTrace.lapE n η σ = 0) :
    Light.bareForm η k = 0 := by
  have := (lapE_of_waveProfile η σ h).symm.trans hvac
  obtain ⟨u, hu⟩ := hm
  rw [← hu] at this
  exact (Units.mul_left_inj u).mp (by rw [this, zero_mul])

omit [ScaleAlgebra n A] in
/-- **And the characteristic cone is the measured null cone**, for any unit
scale: `physForm` is `s²` times the bare form. -/
theorem characteristic_is_null (s : Aˣ) {k : Fin n → A}
    (h : Light.bareForm η k = 0) : Light.IsNull s η k := by
  simp only [Light.IsNull, Light.physForm, h, mul_zero]

omit [ScaleAlgebra n A] in
/-- **With a Lorentzian signature the cone has unit speed.** -/
theorem null_is_unit_speed {k : Fin n → A} (t : Fin n) (ht : η t = -1)
    (hrest : ∀ i, i ≠ t → η i = 1) (h : Light.bareForm η k = 0) :
    (∑ i ∈ Finset.univ.erase t, k i * k i) = k t * k t := by
  rw [Light.bareForm, ← Finset.add_sum_erase _ _ (Finset.mem_univ t), ht] at h
  have hb : ∀ i ∈ Finset.univ.erase t, η i * (k i * k i) = k i * k i := by
    intro i hi; rw [hrest i (Finset.ne_of_mem_erase hi), one_mul]
  rw [Finset.sum_congr rfl hb] at h
  linear_combination h

/-- **A source drives the wave**: with the corrected operator, A6″ is
`□σ = Δ·ν`, and a wave profile reads it as the bare form times the profile. -/
theorem sourced_wave {k : Fin n → A} {m Δ ν : A} (h : WaveProfile k m σ)
    (hsrc : EtaTrace.lapE n η σ = Δ * ν) : Light.bareForm η k * m = Δ * ν := by
  rw [← lapE_of_waveProfile η σ h]; exact hsrc


end SCD.Hyperbolic
