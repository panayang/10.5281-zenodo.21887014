/-
# Emergence of Riemannian geometry from a position-dependent scale

The central regression theorem of the programme.

We *do not* postulate a curved manifold.  We postulate flat Euclidean
bookkeeping `δ` together with the dimensionless log-scale `σ`, and we declare
that the physically measured line element is the bare one re-read in the local
unit:

        g = e^{2σ} δ .

Everything below is then forced.  The Levi-Civita data of `g` turn out to be
polynomial in the derivatives of `σ`, and Ricci and the scalar curvature are
computed in closed form.  Curvature is therefore *not* extra structure: it is
exactly the second-order inhomogeneity of the scale field.

Every statement is an identity in an arbitrary `ScaleAlgebra`, hence holds in
any concrete model of the substrate.
-/
import SCD.Basic

namespace SCD

open Finset ScaleAlgebra

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-! ## Derived scale quantities -/

/-- The scale gradient `σ_i = ∂_i σ`.  Dimensionless. -/
def sig (σ : A) (i : Fin n) : A := d i σ

/-- The scale Hessian `σ_{ij} = ∂_i ∂_j σ`. -/
def hess (σ : A) (i j : Fin n) : A := d i (sig σ j)

theorem hess_symm (σ : A) (i j : Fin n) : hess σ i j = hess σ j i :=
  d_comm i j σ

/-- The same fact, stated in unfolded form so that it can be used to rewrite
goals in which `hess` has already been expanded. -/
theorem d_sig_comm (σ : A) (i j : Fin n) : d i (sig σ j) = d j (sig σ i) :=
  d_comm i j σ

variable (n) in
/-- Flat Laplacian of the scale, `Δσ`. -/
def lap (σ : A) : A := ∑ i : Fin n, hess σ i i

variable (n) in
/-- Squared scale gradient, `|∇σ|²`. -/
def gradsq (σ : A) : A := ∑ i : Fin n, sig σ i * sig σ i

/-- Auxiliary: pulling a constant out of a `gradsq` sum. -/
theorem sum_mul_gradsq (σ : A) (c : A) :
    ∑ m : Fin n, c * (sig σ m * sig σ m) = c * gradsq n σ := by
  rw [gradsq, Finset.mul_sum]

/-- Auxiliary: a constant summed over `Fin n`. -/
theorem sum_const_fin (m : ℕ) (c : A) : ∑ _a : Fin m, c = (m : A) * c := by
  simp [Finset.sum_const, nsmul_eq_mul]

/-! ## The scale connection is integrable: no second clock effect

Weyl's 1918 unified theory postulated an *independent* one-form `A` measuring
how the unit of length changes from point to point.  Einstein's objection was
decisive: a non-integrable `A` makes atomic spectra depend on world-line
history (the "second clock effect"), contrary to observation.

Here `A` is not independent — it is `dσ`, the gradient of the global scalar
`σ`.  Its curvature vanishes identically, purely because mixed partials
commute.  The second clock effect is therefore absent *by construction*, which
is exactly why an integrable scale geometry succeeds where Weyl's original
non-integrable one failed. -/

/-- The scale connection one-form, `A_i = ∂_i σ`. -/
def scaleConn (σ : A) (i : Fin n) : A := sig σ i

/-- Curvature of the scale connection, `F_{ij} = ∂_i A_j − ∂_j A_i`. -/
def scaleCurv (σ : A) (i j : Fin n) : A := d i (scaleConn σ j) - d j (scaleConn σ i)

/-- **No second clock effect.**  The scale connection is flat. -/
@[simp] theorem scaleCurv_eq_zero (σ : A) (i j : Fin n) : scaleCurv σ i j = 0 := by
  simp only [scaleCurv, scaleConn, sig]
  rw [d_comm]
  ring

/-! ## Levi-Civita data of `g = e^{2σ} δ` -/

/-- Christoffel symbols `Γ^a_{bc}` of `g = e^{2σ}δ`.

Indices are raised and lowered with `δ`, so upper and lower positions agree.
The conformal factor cancels out of `Γ` entirely, leaving a polynomial in
`∇σ`: the connection sees only *changes* of scale, never the scale itself. -/
def Chr (σ : A) (a b c : Fin n) : A :=
  (kron a b : A) * sig σ c + (kron a c : A) * sig σ b - (kron b c : A) * sig σ a

theorem Chr_symm (σ : A) (a b c : Fin n) : Chr σ a b c = Chr σ a c b := by
  simp only [Chr, kron_symm b c]
  ring

/-- Riemann tensor `R^a_{bce}` built from `Γ` by the standard formula. -/
def Rm (σ : A) (a b c e : Fin n) : A :=
  d c (Chr σ a b e) - d e (Chr σ a b c)
    + ∑ m, (Chr σ a c m * Chr σ m b e - Chr σ a e m * Chr σ m b c)

/-- Ricci tensor, `R_{be} = R^a_{bae}`. -/
def Ric (σ : A) (b e : Fin n) : A := ∑ a, Rm σ a b a e

variable (n) in
/-- The `δ`-trace of Ricci.  The true scalar curvature of `g` is `e^{-2σ}`
times this; we keep the conformal factor explicit so that no invertibility
hypothesis is ever needed. -/
def RscBare (σ : A) : A := ∑ b : Fin n, Ric σ b b

/-! ### Contractions of the Christoffel symbols -/

/-- `∑_a ∂_a Γ^a_{be} = 2 σ_{be} − δ_{be} Δσ`. -/
theorem sum_d_Chr (σ : A) (b e : Fin n) :
    ∑ a, d a (Chr σ a b e) = 2 * hess σ b e - (kron b e : A) * lap n σ := by
  have h : ∀ a : Fin n, d a (Chr σ a b e)
      = (kron a b : A) * hess σ a e + (kron a e : A) * hess σ a b
        - (kron b e : A) * hess σ a a := by
    intro a
    simp only [Chr, d_sub, d_add, d_kron_mul, hess]
  rw [Finset.sum_congr rfl (fun a _ => h a)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_kron_left]
  rw [← Finset.mul_sum, hess_symm σ e b]
  simp only [lap]
  ring

/-- `Γ^a_{am} = δ_{aa} σ_m`, so `∑_a Γ^a_{am} = n σ_m`. -/
theorem sum_Chr_diag (σ : A) (m : Fin n) :
    ∑ a, Chr σ a a m = (n : A) * sig σ m := by
  have h : ∀ a : Fin n, Chr σ a a m = (kron a a : A) * sig σ m := by
    intro a; simp only [Chr, kron_symm a m]; ring
  rw [Finset.sum_congr rfl (fun a _ => h a)]
  simp only [kron_self, one_mul, sum_const_fin]

/-- `∑_a ∂_e Γ^a_{ba} = n σ_{eb}`. -/
theorem sum_d_Chr_trace (σ : A) (b e : Fin n) :
    ∑ a, d e (Chr σ a b a) = (n : A) * hess σ e b := by
  have h : ∀ a : Fin n, d e (Chr σ a b a) = d e (Chr σ a a b) := by
    intro a; rw [Chr_symm]
  rw [Finset.sum_congr rfl (fun a _ => h a), ← d_sum, sum_Chr_diag, d_nsmul]
  rfl

/-- `∑_m (n σ_m) Γ^m_{be} = n (2 σ_b σ_e − δ_{be}|∇σ|²)`. -/
theorem sum_ChrTrace_Chr (σ : A) (b e : Fin n) :
    ∑ m, ((n : A) * sig σ m) * Chr σ m b e
      = (n : A) * (2 * (sig σ b * sig σ e) - (kron b e : A) * gradsq n σ) := by
  have h : ∀ m : Fin n, ((n : A) * sig σ m) * Chr σ m b e
      = (kron m b : A) * ((n : A) * (sig σ e * sig σ m))
        + (kron m e : A) * ((n : A) * (sig σ b * sig σ m))
        - ((n : A) * (kron b e : A)) * (sig σ m * sig σ m) := by
    intro m; simp only [Chr]; ring
  rw [Finset.sum_congr rfl (fun m _ => h m)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_kron_left,
    sum_mul_gradsq]
  ring

/-- **Master contraction.**  The quadratic term of the Riemann tensor, in full
generality (no indices contracted):

`∑_m Γ^a_{cm} Γ^m_{be} = 2δ_{ac}σ_bσ_e − δ_{ac}δ_{be}|∇σ|² + δ_{ab}σ_cσ_e
                          + δ_{ae}σ_bσ_c − δ_{bc}σ_aσ_e − δ_{ce}σ_aσ_b`.

Every later curvature statement is a specialisation of this one identity. -/
theorem sum_Chr_Chr_full (σ : A) (a b c e : Fin n) :
    ∑ m, Chr σ a c m * Chr σ m b e
      = (kron a c : A) * (2 * (sig σ b * sig σ e))
        - (kron a c : A) * ((kron b e : A) * gradsq n σ)
        + (kron a b : A) * (sig σ c * sig σ e)
        + (kron a e : A) * (sig σ b * sig σ c)
        - (kron c b : A) * (sig σ a * sig σ e)
        - (kron c e : A) * (sig σ a * sig σ b) := by
  have h : ∀ m : Fin n, Chr σ a c m * Chr σ m b e
      = (kron m b : A) * ((kron a c : A) * (sig σ m * sig σ e))
        + (kron m e : A) * ((kron a c : A) * (sig σ m * sig σ b))
        - ((kron a c : A) * (kron b e : A)) * (sig σ m * sig σ m)
        + (kron a m : A) * ((kron m b : A) * (sig σ c * sig σ e))
        + (kron a m : A) * ((kron m e : A) * (sig σ c * sig σ b))
        - (kron a m : A) * ((kron b e : A) * (sig σ c * sig σ m))
        - (kron c m : A) * ((kron m b : A) * (sig σ a * sig σ e))
        - (kron c m : A) * ((kron m e : A) * (sig σ a * sig σ b))
        + (kron c m : A) * ((kron b e : A) * (sig σ a * sig σ m)) := by
    intro m; simp only [Chr]; ring
  rw [Finset.sum_congr rfl (fun m _ => h m)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_kron_left,
    sum_kron_right, sum_mul_gradsq]
  ring

/-- The doubly contracted case, obtained from the master identity:
`∑_{a,m} Γ^a_{em} Γ^m_{ba} = (n+2) σ_b σ_e − 2 δ_{be} |∇σ|²`. -/
theorem sum_Chr_Chr (σ : A) (b e : Fin n) :
    ∑ a, ∑ m, Chr σ a e m * Chr σ m b a
      = ((n : A) + 2) * (sig σ b * sig σ e) - 2 * ((kron b e : A) * gradsq n σ) := by
  rw [Finset.sum_congr rfl (fun a _ => sum_Chr_Chr_full σ a b e a)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_kron_left,
    sum_kron_right, sum_mul_gradsq, kron_self, one_mul, sum_const_fin]
  rw [kron_symm e b]
  ring

/-! ## The regression theorems -/

/-- **Ricci curvature is the second-order inhomogeneity of the scale.**

`R_{be} = −(n−2)(σ_{be} − σ_b σ_e) − δ_{be}(Δσ + (n−2)|∇σ|²)`.

Read physically: gravity *is* the failure of the local unit of measure to vary
affinely across the substrate. -/
theorem Ric_eq (σ : A) (b e : Fin n) :
    Ric σ b e
      = -((n : A) - 2) * (hess σ b e - sig σ b * sig σ e)
        - (kron b e : A) * (lap n σ + ((n : A) - 2) * gradsq n σ) := by
  have hsplit : Ric σ b e
      = (∑ a, d a (Chr σ a b e)) - (∑ a, d e (Chr σ a b a))
        + ((∑ a, ∑ m, Chr σ a a m * Chr σ m b e)
            - ∑ a, ∑ m, Chr σ a e m * Chr σ m b a) := by
    simp only [Ric, Rm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hdiag : (∑ a, ∑ m, Chr σ a a m * Chr σ m b e)
      = (n : A) * (2 * (sig σ b * sig σ e) - (kron b e : A) * gradsq n σ) := by
    rw [Finset.sum_comm]
    have h : ∀ m : Fin n, ∑ a, Chr σ a a m * Chr σ m b e
        = ((n : A) * sig σ m) * Chr σ m b e := by
      intro m; rw [← Finset.sum_mul, sum_Chr_diag]
    rw [Finset.sum_congr rfl (fun m _ => h m)]
    exact sum_ChrTrace_Chr σ b e
  rw [hsplit, sum_d_Chr, sum_d_Chr_trace, hdiag, sum_Chr_Chr, hess_symm σ e b]
  ring

/-- **Scalar curvature of `g = e^{2σ}δ`.**

`e^{2σ} R = −2(n−1) Δσ − (n−1)(n−2) |∇σ|²`.

For `n = 3` this is the Hamiltonian constraint of a conformally flat slice;
its linearisation is Poisson's equation. -/
theorem RscBare_eq (σ : A) :
    RscBare n σ
      = -2 * ((n : A) - 1) * lap n σ - ((n : A) - 1) * ((n : A) - 2) * gradsq n σ := by
  have h : ∀ b : Fin n, Ric σ b b
      = -((n : A) - 2) * (hess σ b b - sig σ b * sig σ b)
        - (lap n σ + ((n : A) - 2) * gradsq n σ) := by
    intro b; rw [Ric_eq]; simp only [kron_self, one_mul]
  have hsum : (∑ b : Fin n, (hess σ b b - sig σ b * sig σ b)) = lap n σ - gradsq n σ := by
    simp only [Finset.sum_sub_distrib, lap, gradsq]
  simp only [RscBare]
  rw [Finset.sum_congr rfl (fun b _ => h b)]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_const_fin, hsum]
  ring

/-! ## Curvature *is* scale deformation

The results above contract indices.  The sharper statement, and the true
content of the programme, keeps them all free: the entire Riemann tensor is a
*linear* function of one symmetric tensor built from `σ`. -/

variable (n) in
/-- The **scale deformation tensor**

  `D_{ij} = 2σ_{ij} − 2σ_iσ_j + δ_{ij}|∇σ|²`,

the obstruction to the local unit of measure varying "affinely" across the
substrate.  (It is twice the geometrically natural tensor; the factor is
carried explicitly so that no division by `2` is ever required, keeping every
statement valid over an arbitrary commutative ring.) -/
def Defm (σ : A) (i j : Fin n) : A :=
  2 * hess σ i j - 2 * (sig σ i * sig σ j) + (kron i j : A) * gradsq n σ

theorem Defm_symm (σ : A) (i j : Fin n) : Defm n σ i j = Defm n σ j i := by
  simp only [Defm, hess_symm σ i j, kron_symm i j]
  ring

/-- The derivative part of the Riemann tensor. -/
theorem d_Chr_diff (σ : A) (a b c e : Fin n) :
    d c (Chr σ a b e) - d e (Chr σ a b c)
      = (kron a e : A) * hess σ b c - (kron b e : A) * hess σ a c
        - (kron a c : A) * hess σ b e + (kron b c : A) * hess σ a e := by
  simp only [Chr, d_sub, d_add, d_kron_mul, hess]
  rw [d_sig_comm σ c b, d_sig_comm σ c a, d_sig_comm σ e b, d_sig_comm σ e a,
    d_sig_comm σ e c]
  ring

/-- **The master regression theorem: curvature is scale deformation.**

`2 R^a_{bce} = δ_{ae} D_{bc} − δ_{ac} D_{be} + δ_{bc} D_{ae} − δ_{be} D_{ac}`.

The Riemann tensor of `g = e^{2σ}δ` is exactly the Kulkarni–Nomizu product of
the bare Euclidean bookkeeping `δ` with the scale deformation `D`.  Nothing
about curvature is independent of the scale field: geometry is *bookkeeping ×
scale deformation*, and nothing else. -/
theorem two_Rm_eq (σ : A) (a b c e : Fin n) :
    2 * Rm σ a b c e
      = (kron a e : A) * Defm n σ b c - (kron a c : A) * Defm n σ b e
        + (kron b c : A) * Defm n σ a e - (kron b e : A) * Defm n σ a c := by
  have hsplit : Rm σ a b c e
      = (d c (Chr σ a b e) - d e (Chr σ a b c))
        + ((∑ m, Chr σ a c m * Chr σ m b e) - ∑ m, Chr σ a e m * Chr σ m b c) := by
    simp only [Rm, Finset.sum_sub_distrib]
  rw [hsplit, d_Chr_diff, sum_Chr_Chr_full, sum_Chr_Chr_full]
  simp only [Defm]
  rw [kron_symm c b, kron_symm e b, kron_symm e c]
  ring

/-! ### Flatness and vacuum

Over any ring in which `2` is invertible — in particular any `ℝ`-algebra, which
is the case for every physical model — the master identity gives at once that
a deformation-free scale field is *exactly* a flat geometry.  Vacuum is a
statement about the *uniformity* of scale change, never about the absence of
scale. -/

/-- **Deformation-free scale ⟹ flat space.**  Not merely Ricci-flat: the whole
Riemann tensor vanishes. -/
theorem Rm_eq_zero_of_Defm_eq_zero [Invertible (2 : A)] (σ : A)
    (h : ∀ i j, Defm n σ i j = 0) (a b c e : Fin n) :
    Rm σ a b c e = 0 := by
  have h2 : 2 * Rm σ a b c e = 0 := by
    rw [two_Rm_eq, h b c, h b e, h a e, h a c]
    ring
  calc Rm σ a b c e = ⅟(2 : A) * (2 * Rm σ a b c e) := by
        rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = 0 := by rw [h2, mul_zero]

/-- Consequently Ricci vanishes as well. -/
theorem Ric_eq_zero_of_Defm_eq_zero [Invertible (2 : A)] (σ : A)
    (h : ∀ i j, Defm n σ i j = 0) (b e : Fin n) :
    Ric σ b e = 0 := by
  simp only [Ric, Rm_eq_zero_of_Defm_eq_zero σ h, Finset.sum_const_zero]

/-- Conversely, the deformation tensor is recovered from curvature by tracing,
so `D` carries exactly the same information as `R`:
`2 R_{be} = −(n−2) D_{be} − δ_{be} tr D`. -/
theorem two_Ric_eq (σ : A) (b e : Fin n) :
    2 * Ric σ b e
      = -((n : A) - 2) * Defm n σ b e - (kron b e : A) * (2 * lap n σ + ((n : A) - 2) * gradsq n σ) := by
  rw [Ric_eq]
  simp only [Defm]
  ring

end SCD
