/-
# The diagonal ansatz, computed — closing the last input in the gravity chain

`Schwarzschild.lean` proves the cancellation that makes reciprocity happen, but
it **posits** the two Ricci components it cancels, in their textbook form.
`Vacuum.lean` says so plainly — "the standard Ricci combination … is taken as
input" — and the assumption audit found that this was never in the register
even though the whole quantitative chain runs through it.

This file removes it.  The connection and the curvature are computed from A4′'s
own metric, and the cancellation comes out with more structure than the textbook
route shows.

## The setting, in the framework's own terms

A4′ gives `g_ab = η_a w_a δ_ab` with `w_a = e^{2σ_a}` a unit — a diagonal metric
with one scale per direction, and no ansatz imposed.  "Static and spherically
symmetric" is then not an extra structure but a **condition**: every scale varies
along one direction only.  `Static` below says exactly that and nothing more.

## Validation before use

`metric_compatible` proves `∂_c g_ab = Γ^d_{ca} g_db + Γ^d_{cb} g_ad` for the
connection defined here, with no staticity assumed.  That is the defining
property of Levi-Civita, so it certifies the Christoffel formula rather than
asking the reader to trust a transcription — which matters, because a sign error
here would propagate into the deflection number.

## What the computation shows

Under staticity the connection has only three families of nonvanishing
components (`chr_rr_r`, `chr_diag_r`, `chr_r_aa`, and `chr_eq_zero` for the
rest).  The Ricci components then come out as

    R_tt = −η_tη_r (w_t/w_r) [ σ_t'' − 2σ_t'σ_r' + σ_t' S ]        (t ≠ r)
    R_rr = −Σ_{a≠r} [ σ_a'' − σ_a'σ_r' + (σ_a')² ]

with `S = Σ_a σ_a'`, and then the combination `R_tt/A + R_rr/B` — which is
`R^r_r − R^t_t` — has the property `Schwarzschild.lean` observed and could not
explain:

> **every term built from `σ_t` and `σ_r` alone cancels identically.**

`combination_is_transverse`.  The second derivative `σ_t''`, the square
`(σ_t')²` and the cross term `σ_t'σ_r'` all disappear, and what is left is a sum
over the **transverse** directions only, in which `σ_t' + σ_r'` appears linearly:

    R^r_r − R^t_t = −(1/w_r) Σ_{a ∉ {t,r}} [ σ_a'' + (σ_a')² − σ_a'(σ_t' + σ_r') ] .

So the vacuum has something to say about `σ_t + σ_r` **only because there are
transverse directions**, and the amount it says is proportional to how many.
That is the structural reason for the cancellation, and it is invisible in the
`R_tt/A + R_rr/B` presentation.

## Where the textbook expression comes from

Setting the transverse scales to the areal radius, `σ_a = log r`, gives
`σ_a'' + (σ_a')² = 0` — the transverse bracket vanishes identically — and the
remaining term is `−σ_a'(σ_t' + σ_r') = −(σ_t' + σ_r')/r`.  With `n − 2`
transverse directions,

    R^r_r − R^t_t = (n−2)/(r w_r) · (σ_t' + σ_r') ,

which at `n = 4` is `(2/(r w_r))(σ_t' + σ_r') = (1/(rB))(A'/A + B'/B)`: exactly
`Schwarzschild.ricci_combination`, now derived.  `areal_transverse_condition`
isolates `σ_a'' + (σ_a')² = 0` as what "the transverse coordinate is a radius"
means here — a *definition of the coordinate*, not a further physical input.

## What is derived

Everything, and in the framework's own algebraic setting:

* `metric_compatible` — the connection is Levi-Civita, certified rather than
  transcribed;
* `chr_eq_zero`, `chr_rrr`, `chr_diag_r`, `chr_r_aa`, `trace_chr_r` — under
  staticity only three families survive, with their values and trace;
* `ric_tt`, `ric_rr` — the two Ricci components, contracted from the connection:

      R_tt = −η_tη_r (w_t/w_r) [ σ_t'' − 2σ_r'σ_t' + S σ_t' ] ,   S = Σ_a σ_a'
      R_rr = σ_r'' − S' + S σ_r' − Σ_c (σ_c')² ;

* `combination_is_transverse` — **the cancellation, derived.**  For a Lorentzian
  pair `η_tη_r = −1`,

      (w_r/w_t)·R_tt + R_rr = −Σ_{a ∉ {t,r}} [ σ_a'' + (σ_a')² − σ_a'(σ_t'+σ_r') ] .

  Every term built from `σ_t` and `σ_r` alone cancels identically — `σ_t''`,
  `(σ_t')²` and `σ_t'σ_r'` all disappear;
* `combination_areal` — with the transverse scales at the areal radius
  (`σ_a'' + (σ_a')² = 0`, which is what "the transverse coordinate is a radius"
  means, a choice of coordinate) the combination becomes a **product**:

      (w_r/w_t)·R_tt + R_rr = (Σ_{a transverse} σ_a') · (σ_t' + σ_r') ;

* `vacuum_scale_sum` — hence `R_tt = R_rr = 0` gives `σ_t' + σ_r' = 0`.

## What that explains

`Schwarzschild.ricci_combination` writes the same thing as
`(1/(rB))(A'/A + B'/B)` and can only observe that the cancellation happens.  Here
the reason is visible: **the vacuum constrains `σ_t + σ_r` only because there are
transverse directions**, and the prefactor is not `1/r` by fiat — it is the
*total transverse scale gradient*, which for the areal configuration is `(n−2)/r`.
The `n − 2` is a count of transverse directions and the `1/r` is their common
gradient.  At `n = 4` that is `2/r`, matching the textbook expression exactly.

## Status of the input this replaces

`Vacuum.lean` and `Schwarzschild.lean` took the two Ricci expressions as input.
They are derived here, so the register entry in `Audit.lean` §V.a is discharged.
The derivation is algebraic and those two files are real-analytic; the statements
correspond term for term and rewiring them is a refactor, not a gap.
`Reciprocity.lean` and `Chain.lean` carry the consequences.

## The general case, and the cancellation seen twice

Dropping staticity, the connection has a short and uniform list
(`chr_gen_diag`, `chr_gen_off`, `chr_gen_zero`) and the **off-diagonal** Ricci —
which vanishes identically in the static case — does not.  `ric_offdiag`:

    R_ab  =  −Σ_{c ∉ {a,b}} [ ∂_a∂_b σ_c − (∂_bσ_a)(∂_aσ_c)
                               − (∂_aσ_b)(∂_bσ_c) + (∂_aσ_c)(∂_bσ_c) ]

**Every term built from `σ_a` and `σ_b` alone cancels identically** — the second
derivatives `∂_a∂_bσ_a` and `∂_a∂_bσ_b`, the products `(∂_aσ_a)(∂_bσ_a)` and
`(∂_aσ_b)(∂_bσ_b)`, and the cross term `(∂_bσ_a)(∂_aσ_b)`.  This is the same
cancellation as `combination_is_transverse`, now in a different component, so it
is not an artefact of the static ansatz:

> **No pair of directions carries its own curvature.  Every component is carried
> by the complement.**

## And a constraint that was invisible

A4′ gives a metric that is diagonal *by construction*, so in vacuum the
off-diagonal equations `R_ab = 0` are **not** part of the diagonal system — they
are extra conditions on the scale pattern, the price of insisting the metric stay
diagonal in the bare frame.

`offdiag_zero_in_two`: with two directions there is nothing transverse to a pair,
so the constraint is empty and diagonality is free.  For `n ≥ 3` it is not.  That
is the same shape as `Openness.no_dissipation_in_one_direction`, where openness
needed a transverse direction to leak into.

And the constraints are indexed by unordered **pairs**, which is the index set of
`Pattern.rotDim2` — the doubled dimension of `Λ²p`.  So A7, `rotDim2 = scaleDim2`,
acquires a reading it did not have:

> **the number of constraints on the diagonal ansatz equals the number of scale
> functions they constrain.**

Neither over- nor under-determined.  That is a gloss on a count rather than a new
theorem, and what makes it available is `ric_offdiag` showing the components are
pair-indexed.

## What remains a hypothesis

Staticity and the areal transverse coordinate, in the theorems that use them; the
general results above use neither.
-/
import SCD.Conformal
import SCD.Frame

namespace SCD.Diagonal

open SCD ScaleAlgebra Finset

variable {n : ℕ} {A : Type*} [CommRing A] [ScaleAlgebra n A]

/-! ## The metric of A4′, and its Levi-Civita connection -/

variable (η : Fin n → A) (w : Fin n → Aˣ) (σ : Fin n → A)

/-- The measured metric of A4′: diagonal, with `w_a = e^{2σ_a}` in direction
`a`. -/
def met (a b : Fin n) : A := (kron a b : A) * (η a * (w a : A))

/-- The ratio of two directional metric factors, `w_a / w_u`.  This is the only
place the scale enters the connection other than through its gradient, and it is
what distinguishes the anisotropic connection from the conformal one. -/
def ratio (a u : Fin n) : A := ((w a * (w u)⁻¹ : Aˣ) : A)

omit [ScaleAlgebra n A] in
@[simp] theorem ratio_self (a : Fin n) : ratio w a a = 1 := by
  simp only [ratio, mul_inv_cancel, Units.val_one]

omit [ScaleAlgebra n A] in
theorem ratio_mul (a u : Fin n) : ratio w a u * (w u : A) = (w a : A) := by
  simp only [ratio, Units.val_mul]
  calc ((w a : A)) * (((w u)⁻¹ : Aˣ) : A) * ((w u : A))
      = ((w a : A)) * ((((w u)⁻¹ : Aˣ) : A) * ((w u : A))) := by ring
    _ = ((w a : A)) := by rw [(w u).inv_mul, mul_one]

/-- **The Christoffel symbols of the diagonal metric.**

        Γ^u_{ab} = δ_ub ∂_a σ_u + δ_ua ∂_b σ_u − δ_ab η_aη_u (w_a/w_u) ∂_u σ_a .

Derived from `Γ = ½ g^{ud}(∂_a g_{db} + ∂_b g_{da} − ∂_d g_{ab})` with `g`
diagonal; `metric_compatible` below certifies it. -/
def Chr (u a b : Fin n) : A :=
  (kron u b : A) * d a (σ u) + (kron u a : A) * d b (σ u)
    - (kron a b : A) * (η a * η u * ratio w a u * d u (σ a))

/-! ### Validation: the connection is metric

Proved with no staticity and no signature condition beyond `η² = 1`.  This is
what makes the formula above a transcription that has been checked rather than
one that has been trusted. -/

omit [ScaleAlgebra n A] in
/-- A Kronecker delta may substitute its own indices inside anything. -/
theorem kron_subst (f : Fin n → A) (x y : Fin n) :
    (kron x y : A) * f x = (kron x y : A) * f y := by
  by_cases h : x = y
  · subst h; rfl
  · rw [show (kron x y : A) = 0 from if_neg h]; ring

/-- **The connection is metric-compatible**, which is what certifies it as the
Levi-Civita connection of `met`.

No staticity is assumed and no property of the signature beyond `η² = 1` and its
constancy.  A sign error in `Chr` would show up here, which is the point of
proving it before using it. -/
theorem metric_compatible (hη : ∀ a : Fin n, η a * η a = 1)
    (hηc : ∀ a b : Fin n, d b (η a) = 0)
    (hw : ∀ a b : Fin n, d b (w a : A) = 2 * (w a : A) * d b (σ a)) (c a b : Fin n) :
    d c (met η w a b)
      = (∑ e, Chr η w σ e c a * met η w e b) + ∑ e, Chr η w σ e c b * met η w a e := by
  have hL : d c (met η w a b) = (kron a b : A) * (η a * (2 * (w a : A) * d c (σ a))) := by
    simp only [met]
    rw [d_kron_mul, d_mul, hηc a c, zero_mul, zero_add, hw a c]
  have h1 : (∑ e, Chr η w σ e c a * met η w e b) = Chr η w σ b c a * (η b * (w b : A)) := by
    simp only [met]
    have hh : ∀ e : Fin n, Chr η w σ e c a * ((kron e b : A) * (η e * (w e : A)))
        = (kron e b : A) * (Chr η w σ e c a * (η e * (w e : A))) := fun e => by ring
    rw [Finset.sum_congr rfl fun e _ => hh e, sum_kron_left]
  have h2 : (∑ e, Chr η w σ e c b * met η w a e) = Chr η w σ a c b * (η a * (w a : A)) := by
    simp only [met]
    have hh : ∀ e : Fin n, Chr η w σ e c b * ((kron a e : A) * (η a * (w a : A)))
        = (kron a e : A) * (Chr η w σ e c b * (η a * (w a : A))) := fun e => by ring
    rw [Finset.sum_congr rfl fun e _ => hh e, sum_kron_right]
  -- the three cancellations, each an index substitution under a delta
  have e1 : (kron b a : A) * (d c (σ b) * (η b * (w b : A)))
      = (kron a b : A) * (d c (σ a) * (η a * (w a : A))) := by
    rw [kron_symm b a]
    exact (kron_subst (fun x => d c (σ x) * (η x * (w x : A))) a b).symm
  have e2 : (kron c a : A) * ((η c * η b * ratio w c b * d b (σ c)) * (η b * (w b : A)))
      = (kron a c : A) * (d b (σ a) * (η a * (w a : A))) := by
    have hstep : (kron c a : A) * ((η c * η b * ratio w c b * d b (σ c)) * (η b * (w b : A)))
        = (kron a c : A) * ((η c * (w c : A)) * d b (σ c)) := by
      rw [kron_symm c a]
      have hr : ratio w c b * (w b : A) = (w c : A) := ratio_mul w c b
      calc (kron a c : A) * ((η c * η b * ratio w c b * d b (σ c)) * (η b * (w b : A)))
          = (kron a c : A) * ((η b * η b) * (η c * (ratio w c b * (w b : A)) * d b (σ c))) := by
            ring
        _ = (kron a c : A) * ((η c * (w c : A)) * d b (σ c)) := by rw [hr, hη b, one_mul]
    rw [hstep]
    have := (kron_subst (fun x => (η x * (w x : A)) * d b (σ x)) a c).symm
    rw [this]
    ring
  have e3 : (kron c b : A) * ((η c * η a * ratio w c a * d a (σ c)) * (η a * (w a : A)))
      = (kron b c : A) * (d a (σ b) * (η b * (w b : A))) := by
    have hstep : (kron c b : A) * ((η c * η a * ratio w c a * d a (σ c)) * (η a * (w a : A)))
        = (kron b c : A) * ((η c * (w c : A)) * d a (σ c)) := by
      rw [kron_symm c b]
      have hr : ratio w c a * (w a : A) = (w c : A) := ratio_mul w c a
      calc (kron b c : A) * ((η c * η a * ratio w c a * d a (σ c)) * (η a * (w a : A)))
          = (kron b c : A) * ((η a * η a) * (η c * (ratio w c a * (w a : A)) * d a (σ c))) := by
            ring
        _ = (kron b c : A) * ((η c * (w c : A)) * d a (σ c)) := by rw [hr, hη a, one_mul]
    rw [hstep]
    have := (kron_subst (fun x => (η x * (w x : A)) * d a (σ x)) b c).symm
    rw [this]
    ring
  rw [hL, h1, h2]
  simp only [Chr]
  linear_combination -e1 + e2 + e3

/-! ## The static configuration

"Static and spherically symmetric" is not an extra structure here.  It is the
condition that every directional scale varies along **one** direction — the one
`Signature.lean` would call radial.  Everything below assumes only that. -/

variable (r : Fin n)

/-- The derivative along the distinguished direction: `σ_a'`. -/
def sp (a : Fin n) : A := d r (σ a)

/-- The total, `S = Σ_a σ_a'`.  It is the trace of the connection and it is what
the Ricci computation contracts against. -/
def totalSp : A := ∑ a, sp σ r a

/-- **The ratio's derivative.**  `(w_a/w_u)' = 2(σ_a' − σ_u')(w_a/w_u)` — the only
fact about the metric factors the curvature computation needs beyond A2. -/
theorem d_ratio (hw : ∀ a b : Fin n, d b (w a : A) = 2 * (w a : A) * d b (σ a))
    (a u c : Fin n) :
    d c (ratio w a u) = ratio w a u * (2 * d c (σ a) - 2 * d c (σ u)) := by
  have hmul : ratio w a u * (w u : A) = (w a : A) := ratio_mul w a u
  have hd : d c (ratio w a u * (w u : A)) = 2 * (w a : A) * d c (σ a) := by
    rw [hmul, hw a c]
  rw [d_mul, hw u c] at hd
  have hcancel : (d c (ratio w a u)) * (w u : A)
      = ratio w a u * (2 * (w u : A) * (d c (σ a) - d c (σ u))) := by
    have hra : ratio w a u * (2 * (w u : A) * d c (σ a)) = 2 * (w a : A) * d c (σ a) := by
      calc ratio w a u * (2 * (w u : A) * d c (σ a))
          = 2 * (ratio w a u * (w u : A)) * d c (σ a) := by ring
        _ = 2 * (w a : A) * d c (σ a) := by rw [hmul]
    linear_combination hd - hra
  have hinv : ((w u)⁻¹ : Aˣ) * (w u : A) = 1 := (w u).inv_mul
  calc d c (ratio w a u)
      = (d c (ratio w a u) * (w u : A)) * (((w u)⁻¹ : Aˣ) : A) := by
        rw [mul_assoc, (w u).mul_inv, mul_one]
    _ = (ratio w a u * (2 * (w u : A) * (d c (σ a) - d c (σ u))))
          * (((w u)⁻¹ : Aˣ) : A) := by rw [hcancel]
    _ = ratio w a u * (2 * d c (σ a) - 2 * d c (σ u))
          * ((w u : A) * (((w u)⁻¹ : Aˣ) : A)) := by ring
    _ = ratio w a u * (2 * d c (σ a) - 2 * d c (σ u)) := by rw [(w u).mul_inv, mul_one]

section Static

variable (hstat : ∀ (a b : Fin n), b ≠ r → d b (σ a) = 0)
include hstat

/-- **The connection has only three nonvanishing families.**

Everything not of one of the shapes `Γ^r_{rr}`, `Γ^a_{ar}`, `Γ^a_{ra}`,
`Γ^r_{aa}` vanishes.  The three conditions below are exactly the three terms of
`Chr` being able to survive: a delta must fire, and the surviving derivative must
be along `r`. -/
theorem chr_eq_zero (u a b : Fin n)
    (h : ¬((u = b ∧ a = r) ∨ (u = a ∧ b = r) ∨ (a = b ∧ u = r))) :
    Chr η w σ u a b = 0 := by
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  have t1 : (kron u b : A) * d a (σ u) = 0 := by
    by_cases hub : u = b
    · rw [hstat u a (h1 hub), mul_zero]
    · rw [show (kron u b : A) = 0 from if_neg hub, zero_mul]
  have t2 : (kron u a : A) * d b (σ u) = 0 := by
    by_cases hua : u = a
    · rw [hstat u b (h2 hua), mul_zero]
    · rw [show (kron u a : A) = 0 from if_neg hua, zero_mul]
  have t3 : (kron a b : A) * (η a * η u * ratio w a u * d u (σ a)) = 0 := by
    by_cases hab : a = b
    · rw [hstat a u (h3 hab), mul_zero, mul_zero]
    · rw [show (kron a b : A) = 0 from if_neg hab, zero_mul]
  simp only [Chr, t1, t2, t3, sub_zero, add_zero]

omit hstat in
/-- `Γ^r_{rr} = σ_r'`. -/
theorem chr_rrr (hη : ∀ a : Fin n, η a * η a = 1) : Chr η w σ r r r = sp σ r r := by
  simp only [Chr, kron_self, one_mul, ratio_self, mul_one, sp]
  rw [show η r * η r = 1 from hη r]
  ring

/-- `Γ^a_{ar} = σ_a'` for `a ≠ r`. -/
theorem chr_diag_r (a : Fin n) (ha : a ≠ r) : Chr η w σ a a r = sp σ r a := by
  simp only [Chr, kron_self, one_mul, sp,
    show (kron a r : A) = 0 from if_neg ha]
  rw [hstat a a ha]
  ring

/-- `Γ^a_{ra} = σ_a'` for `a ≠ r`: the connection is symmetric in the lower
pair, so this is the same component. -/
theorem chr_diag_r' (a : Fin n) (ha : a ≠ r) : Chr η w σ a r a = sp σ r a := by
  simp only [Chr, kron_self, one_mul, sp,
    show (kron a r : A) = 0 from if_neg ha,
    show (kron r a : A) = 0 from if_neg (Ne.symm ha)]
  rw [hstat a a ha]
  ring

omit hstat in
/-- `Γ^r_{aa} = −η_aη_r (w_a/w_r) σ_a'` for `a ≠ r` — the one family that carries
the metric-factor ratio, and hence the one place the anisotropy enters. -/
theorem chr_r_aa (a : Fin n) (ha : a ≠ r) :
    Chr η w σ r a a = -(η a * η r * ratio w a r * sp σ r a) := by
  simp only [Chr, kron_self, one_mul, sp,
    show (kron r a : A) = 0 from if_neg (Ne.symm ha)]
  ring

/-- **The trace of the connection is `S` along `r`, and zero elsewhere.**

`Γ^c_{cb}` is `Σ_a σ_a'` when `b = r` and vanishes otherwise, which is what makes
the second term of the Ricci tensor so simple in the static case. -/
theorem trace_chr_r (hη : ∀ a : Fin n, η a * η a = 1) :
    (∑ c, Chr η w σ c c r) = totalSp σ r := by
  simp only [totalSp]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : c = r
  · rw [hc]; exact chr_rrr η w σ r hη
  · exact chr_diag_r η w σ r hstat c hc

/-- And off the distinguished direction the trace vanishes identically. -/
theorem trace_chr_off (b : Fin n) (hb : b ≠ r) : (∑ c, Chr η w σ c c b) = 0 := by
  refine Finset.sum_eq_zero fun c _ => ?_
  refine chr_eq_zero η w σ r hstat c c b ?_
  rintro (⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨h1, h2⟩)
  · exact hb (h1 ▸ h2)
  · exact hb h2
  · exact hb (h1 ▸ h2)

/-! ## The Ricci tensor -/

/-- The Ricci tensor of the connection, in the standard contraction. -/
def Ric (a b : Fin n) : A :=
  (∑ c, d c (Chr η w σ c a b)) - d a (∑ c, Chr η w σ c c b)
    + (∑ e, (∑ c, Chr η w σ c c e) * Chr η w σ e a b)
    - ∑ c, ∑ e, Chr η w σ c a e * Chr η w σ e c b

/-- Off the distinguished direction, `Γ^c_{tt}` survives only at `c = r`. -/
theorem chr_off_tt {t : Fin n} (ht : t ≠ r) {c : Fin n} (hc : c ≠ r) :
    Chr η w σ c t t = 0 := by
  refine chr_eq_zero η w σ r hstat c t t ?_
  rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
  · exact ht h
  · exact ht h
  · exact hc h

/-- **`R_tt`, contracted.**  Three of the four terms collapse to a single
Christoffel component, and the fourth to twice it. -/
theorem ric_tt (hη : ∀ a : Fin n, η a * η a = 1) {t : Fin n} (ht : t ≠ r) :
    Ric η w σ t t
      = d r (Chr η w σ r t t) + totalSp σ r * Chr η w σ r t t
        - 2 * (sp σ r t * Chr η w σ r t t) := by
  have hz1 : ∀ c ∈ Finset.univ, c ≠ r → d c (Chr η w σ c t t) = 0 := by
    intro c _ hc; rw [chr_off_tt η w σ r hstat ht hc, d_zero]
  have hT1 : (∑ c, d c (Chr η w σ c t t)) = d r (Chr η w σ r t t) :=
    Finset.sum_eq_single r hz1 (fun h => absurd (Finset.mem_univ r) h)
  have hT2 : d t (∑ c, Chr η w σ c c t) = 0 := by
    rw [trace_chr_off η w σ r hstat t ht, d_zero]
  have hz3 : ∀ e ∈ Finset.univ, e ≠ r →
      (∑ c, Chr η w σ c c e) * Chr η w σ e t t = 0 := by
    intro e _ he; rw [chr_off_tt η w σ r hstat ht he, mul_zero]
  have hT3 : (∑ e, (∑ c, Chr η w σ c c e) * Chr η w σ e t t)
      = totalSp σ r * Chr η w σ r t t := by
    rw [Finset.sum_eq_single r hz3 (fun h => absurd (Finset.mem_univ r) h),
      trace_chr_r η w σ r hstat hη]
  have ht' : (∑ e, Chr η w σ t t e * Chr η w σ e t t)
      = sp σ r t * Chr η w σ r t t := by
    have hz : ∀ e ∈ Finset.univ, e ≠ r → Chr η w σ t t e * Chr η w σ e t t = 0 := by
      intro e _ he
      have : Chr η w σ t t e = 0 := by
        refine chr_eq_zero η w σ r hstat t t e ?_
        rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
        · exact ht h
        · exact he h
        · exact ht h
      rw [this, zero_mul]
    rw [Finset.sum_eq_single r hz (fun h => absurd (Finset.mem_univ r) h),
      chr_diag_r η w σ r hstat t ht]
  have hr' : (∑ e, Chr η w σ r t e * Chr η w σ e r t)
      = Chr η w σ r t t * sp σ r t := by
    have hz : ∀ e ∈ Finset.univ, e ≠ t → Chr η w σ r t e * Chr η w σ e r t = 0 := by
      intro e _ he
      have : Chr η w σ r t e = 0 := by
        refine chr_eq_zero η w σ r hstat r t e ?_
        rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · exact ht h
        · exact ht h.symm
        · exact he h.symm
      rw [this, zero_mul]
    rw [Finset.sum_eq_single t hz (fun h => absurd (Finset.mem_univ t) h),
      chr_diag_r' η w σ r hstat t ht]
  have hinner : ∀ c ∈ Finset.univ.erase t, c ≠ r →
      (∑ e, Chr η w σ c t e * Chr η w σ e c t) = 0 := by
    intro c hc hcr
    have hct : c ≠ t := (Finset.mem_erase.mp hc).1
    refine Finset.sum_eq_zero fun e _ => ?_
    have : Chr η w σ c t e = 0 := by
      refine chr_eq_zero η w σ r hstat c t e ?_
      rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩)
      · exact ht h
      · exact hct h
      · exact hcr h
    rw [this, zero_mul]
  have hT4 : (∑ c, ∑ e, Chr η w σ c t e * Chr η w σ e c t)
      = 2 * (sp σ r t * Chr η w σ r t t) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t),
      Finset.sum_eq_single_of_mem r
        (Finset.mem_erase.mpr ⟨Ne.symm ht, Finset.mem_univ r⟩) hinner,
      ht', hr']
    ring
  simp only [Ric, hT1, hT2, hT3, hT4]
  ring

/-- **`R_rr`, contracted.**  Here the connection is diagonal in both index pairs,
so the quadratic term is a plain sum of squares. -/
theorem ric_rr (hη : ∀ a : Fin n, η a * η a = 1) :
    Ric η w σ r r
      = d r (sp σ r r) - d r (totalSp σ r) + totalSp σ r * sp σ r r
        - ∑ c, sp σ r c * sp σ r c := by
  have hchr : ∀ c e : Fin n, c ≠ e → Chr η w σ c r e = 0 := by
    intro c e hce
    refine chr_eq_zero η w σ r hstat c r e ?_
    rintro (⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hce h1
    · exact hce (h1.trans h2.symm)
    · exact hce (h2.trans h1)
  have hdiag : ∀ c : Fin n, Chr η w σ c r c = sp σ r c := by
    intro c
    by_cases hc : c = r
    · rw [hc]; exact chr_rrr η w σ r hη
    · exact chr_diag_r' η w σ r hstat c hc
  have hdiag' : ∀ c : Fin n, Chr η w σ c c r = sp σ r c := by
    intro c
    by_cases hc : c = r
    · rw [hc]; exact chr_rrr η w σ r hη
    · exact chr_diag_r η w σ r hstat c hc
  have hz1 : ∀ c ∈ Finset.univ, c ≠ r → d c (Chr η w σ c r r) = 0 := by
    intro c _ hc; rw [hchr c r hc, d_zero]
  have hT1 : (∑ c, d c (Chr η w σ c r r)) = d r (sp σ r r) := by
    rw [Finset.sum_eq_single r hz1 (fun h => absurd (Finset.mem_univ r) h), hdiag r]
  have hz3 : ∀ e ∈ Finset.univ, e ≠ r →
      (∑ c, Chr η w σ c c e) * Chr η w σ e r r = 0 := by
    intro e _ he; rw [hchr e r he, mul_zero]
  have hT3 : (∑ e, (∑ c, Chr η w σ c c e) * Chr η w σ e r r)
      = totalSp σ r * sp σ r r := by
    rw [Finset.sum_eq_single r hz3 (fun h => absurd (Finset.mem_univ r) h),
      trace_chr_r η w σ r hstat hη, hdiag r]
  have hT4 : (∑ c, ∑ e, Chr η w σ c r e * Chr η w σ e c r)
      = ∑ c, sp σ r c * sp σ r c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    have hz : ∀ e ∈ Finset.univ, e ≠ c → Chr η w σ c r e * Chr η w σ e c r = 0 := by
      intro e _ he; rw [hchr c e (Ne.symm he), zero_mul]
    rw [Finset.sum_eq_single c hz (fun h => absurd (Finset.mem_univ c) h),
      hdiag c, hdiag' c]
  simp only [Ric, hT1, hT3, hT4, trace_chr_r η w σ r hstat hη]

/-! ## The combination, and where the cancellation comes from -/

/-- The **transverse** directions: everything other than the distinguished
direction and the one being paired with it. -/
def transverse (r t : Fin n) : Finset (Fin n) := (Finset.univ.erase r).erase t

omit hstat [ScaleAlgebra n A] in
/-- Splitting a sum into the two distinguished directions and the transverse
remainder. -/
theorem sum_split (f : Fin n → A) {t : Fin n} (ht : t ≠ r) :
    ∑ a, f a = f r + f t + ∑ a ∈ transverse r t, f a := by
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ r),
    ← Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩)]
  simp only [transverse]
  ring

/-- **`R_tt` with the mixed index**, i.e. multiplied by `w_r/w_t`.

Everything the metric factors contribute cancels: `(w_r/w_t)(w_t/w_r) = 1`, so
the mixed component is a pure expression in the scale derivatives. -/
theorem ric_tt_mixed (hη : ∀ a : Fin n, η a * η a = 1)
    (hηc : ∀ a b : Fin n, d b (η a) = 0)
    (hw : ∀ a b : Fin n, d b (w a : A) = 2 * (w a : A) * d b (σ a))
    {t : Fin n} (ht : t ≠ r) :
    ratio w r t * Ric η w σ t t
      = -(η t * η r)
          * (d r (sp σ r t) - 2 * (sp σ r r * sp σ r t) + totalSp σ r * sp σ r t) := by
  have hchr : Chr η w σ r t t = -(η t * η r * ratio w t r * sp σ r t) :=
    chr_r_aa η w σ r t ht
  have hd : d r (Chr η w σ r t t)
      = -(η t * η r * ratio w t r
          * (2 * (sp σ r t * sp σ r t) - 2 * (sp σ r r * sp σ r t) + d r (sp σ r t))) := by
    rw [hchr]
    simp only [d_neg, d_mul, hηc t r, hηc r r, d_ratio w σ hw t r r, zero_mul, mul_zero,
      zero_add, add_zero]
    simp only [sp]
    ring
  have hrt : ratio w r t * ratio w t r = 1 := by
    have hu : (w r * (w t)⁻¹) * (w t * (w r)⁻¹) = (1 : Aˣ) := by
      rw [mul_assoc, ← mul_assoc ((w t)⁻¹), inv_mul_cancel, one_mul, mul_inv_cancel]
    simp only [ratio, ← Units.val_mul, hu, Units.val_one]
  rw [ric_tt η w σ r hstat hη ht, hd, hchr]
  have hexp : ratio w r t
      * (-(η t * η r * ratio w t r
            * (2 * (sp σ r t * sp σ r t) - 2 * (sp σ r r * sp σ r t) + d r (sp σ r t)))
        + totalSp σ r * -(η t * η r * ratio w t r * sp σ r t)
        - 2 * (sp σ r t * -(η t * η r * ratio w t r * sp σ r t)))
      = (ratio w r t * ratio w t r)
        * (-(η t * η r)
            * (d r (sp σ r t) - 2 * (sp σ r r * sp σ r t) + totalSp σ r * sp σ r t)) := by
    ring
  rw [hexp, hrt, one_mul]

/-- **The cancellation, derived.**

        (w_r/w_t)·R_tt + R_rr
          =  −Σ_{a ∉ {t,r}} [ σ_a'' + (σ_a')² − σ_a'(σ_t' + σ_r') ]

for a Lorentzian pair `η_tη_r = −1`.  **Every term built from `σ_t` and `σ_r`
alone cancels identically** — the second derivative `σ_t''`, the square
`(σ_t')²` and the cross term `σ_t'σ_r'` all disappear — and what is left is a sum
over the transverse directions in which `σ_t' + σ_r'` appears linearly.

This is what `Schwarzschild.ricci_combination` observed and could not explain.
The reason is now visible: **the vacuum constrains `σ_t + σ_r` only because there
are transverse directions**, and by an amount proportional to how many. -/
theorem combination_is_transverse (hη : ∀ a : Fin n, η a * η a = 1)
    (hηc : ∀ a b : Fin n, d b (η a) = 0)
    (hw : ∀ a b : Fin n, d b (w a : A) = 2 * (w a : A) * d b (σ a))
    {t : Fin n} (ht : t ≠ r) (hLor : η t * η r = -1) :
    ratio w r t * Ric η w σ t t + Ric η w σ r r
      = -∑ a ∈ transverse r t,
          (d r (sp σ r a) + sp σ r a * sp σ r a
            - sp σ r a * (sp σ r t + sp σ r r)) := by
  have hS : totalSp σ r
      = sp σ r r + sp σ r t + ∑ a ∈ transverse r t, sp σ r a :=
    sum_split r (sp σ r) ht
  have hdS : d r (totalSp σ r)
      = d r (sp σ r r) + d r (sp σ r t) + ∑ a ∈ transverse r t, d r (sp σ r a) := by
    rw [totalSp, d_sum]
    exact sum_split r (fun a => d r (sp σ r a)) ht
  have hsq : (∑ c, sp σ r c * sp σ r c)
      = sp σ r r * sp σ r r + sp σ r t * sp σ r t
        + ∑ a ∈ transverse r t, sp σ r a * sp σ r a :=
    sum_split r (fun a => sp σ r a * sp σ r a) ht
  have hRHS : (∑ a ∈ transverse r t,
        (d r (sp σ r a) + sp σ r a * sp σ r a - sp σ r a * (sp σ r t + sp σ r r)))
      = (∑ a ∈ transverse r t, d r (sp σ r a))
        + (∑ a ∈ transverse r t, sp σ r a * sp σ r a)
        - (∑ a ∈ transverse r t, sp σ r a) * (sp σ r t + sp σ r r) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]
  rw [ric_tt_mixed η w σ r hstat hη hηc hw ht, ric_rr η w σ r hstat hη, hLor, hRHS,
    hdS, hsq]
  rw [show totalSp σ r * sp σ r t
      = (sp σ r r + sp σ r t + ∑ a ∈ transverse r t, sp σ r a) * sp σ r t by rw [hS],
    show totalSp σ r * sp σ r r
      = (sp σ r r + sp σ r t + ∑ a ∈ transverse r t, sp σ r a) * sp σ r r by rw [hS]]
  ring

/-! ## What the transverse condition is, and the vacuum conclusion -/

omit hstat in
/-- **The areal condition.**  A transverse scale equal to the logarithm of the
radial coordinate satisfies `σ_a'' + (σ_a')² = 0`.  That is what "the transverse
coordinate is a radius" means here — a choice of coordinate, not a further
physical input — and it is exactly what makes the transverse bracket collapse. -/
def Areal (t : Fin n) : Prop :=
  ∀ a ∈ transverse r t, d r (sp σ r a) + sp σ r a * sp σ r a = 0

/-- **Under the areal condition the combination is a product.**

        (w_r/w_t)·R_tt + R_rr  =  (Σ_{a transverse} σ_a') · (σ_t' + σ_r')

This is the framework-native form of `Schwarzschild.ricci_combination`'s
`(1/(rB))(A'/A + B'/B)`: the prefactor is not `1/r` by fiat, it is the **total
transverse scale gradient**, which for the areal configuration is `(n−2)/r`.  So
the `n − 2` in the textbook formula is a count of transverse directions, and the
`1/r` is their common gradient. -/
theorem combination_areal (hη : ∀ a : Fin n, η a * η a = 1)
    (hηc : ∀ a b : Fin n, d b (η a) = 0)
    (hw : ∀ a b : Fin n, d b (w a : A) = 2 * (w a : A) * d b (σ a))
    {t : Fin n} (ht : t ≠ r) (hLor : η t * η r = -1) (hareal : Areal σ r t) :
    ratio w r t * Ric η w σ t t + Ric η w σ r r
      = (∑ a ∈ transverse r t, sp σ r a) * (sp σ r t + sp σ r r) := by
  rw [combination_is_transverse η w σ r hstat hη hηc hw ht hLor]
  have hsplit : (∑ a ∈ transverse r t,
        (d r (sp σ r a) + sp σ r a * sp σ r a - sp σ r a * (sp σ r t + sp σ r r)))
      = -((∑ a ∈ transverse r t, sp σ r a) * (sp σ r t + sp σ r r)) := by
    rw [Finset.sum_congr rfl fun a ha => by
      rw [show d r (sp σ r a) + sp σ r a * sp σ r a
          - sp σ r a * (sp σ r t + sp σ r r)
          = (d r (sp σ r a) + sp σ r a * sp σ r a)
            - sp σ r a * (sp σ r t + sp σ r r) by ring, hareal a ha,
        zero_sub]]
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
  rw [hsplit, neg_neg]

/-- **The vacuum forces the scale sum to be stationary.**

`R_tt = R_rr = 0`, with the areal condition on the transverse directions, gives
`(Σ σ_a')·(σ_t' + σ_r') = 0`; where the transverse total is not a zero divisor —
it is `(n−2)/r` for the areal configuration — that is `σ_t' + σ_r' = 0`.

**This is what `Vacuum.lean` and `Schwarzschild.lean` took as input.**  It is
derived here from A4′'s metric, the connection certified by
`metric_compatible`, and staticity.  No Ricci expression is transcribed and no
`1/r` is inserted by hand. -/
theorem vacuum_scale_sum (hη : ∀ a : Fin n, η a * η a = 1)
    (hηc : ∀ a b : Fin n, d b (η a) = 0)
    (hw : ∀ a b : Fin n, d b (w a : A) = 2 * (w a : A) * d b (σ a))
    {t : Fin n} (ht : t ≠ r) (hLor : η t * η r = -1)
    (hareal : Areal σ r t)
    (hreg : ∀ x : A, (∑ a ∈ transverse r t, sp σ r a) * x = 0 → x = 0)
    (htt : Ric η w σ t t = 0) (hrr : Ric η w σ r r = 0) :
    sp σ r t + sp σ r r = 0 := by
  have hcomb := combination_areal η w σ r hstat hη hηc hw ht hLor hareal
  rw [htt, hrr, mul_zero, add_zero] at hcomb
  exact hreg _ hcomb.symm

end Static

/-! ## The general case: dropping staticity

Everything above assumed every scale varies along one direction.  Without that,
two things change: the connection has a longer list of nonvanishing components,
and the **off-diagonal** Ricci components — which vanish identically in the
static case — do not.

That second object is the interesting one.  A4′ gives a metric that is diagonal
*by construction*: one scale per direction, `g_ab = η_a w_a δ_ab`.  So in vacuum
the equations `R_ab = 0` for `a ≠ b` are not part of the diagonal system — they
are **extra constraints on the scale pattern**, the price of insisting that the
metric stay diagonal in the bare frame. -/

section General

variable (hη : ∀ a : Fin n, η a * η a = 1)
include hη

omit hη [ScaleAlgebra n A] in
/-- The two ratios of a pair are inverse. -/
theorem ratio_inv (a b : Fin n) : ratio w a b * ratio w b a = 1 := by
  have hu : (w a * (w b)⁻¹) * (w b * (w a)⁻¹) = (1 : Aˣ) := by
    rw [mul_assoc, ← mul_assoc ((w b)⁻¹), inv_mul_cancel, one_mul, mul_inv_cancel]
  simp only [ratio, ← Units.val_mul, hu, Units.val_one]

/-- **`Γ^a_{ab} = ∂_b σ_a`, with no staticity.**  The two delta-carrying terms
cancel against the third whenever the upper index matches a lower one. -/
theorem chr_gen_diag (a b : Fin n) : Chr η w σ a a b = ScaleAlgebra.d b (σ a) := by
  simp only [Chr, kron_self, one_mul, ratio_self, mul_one]
  rw [show η a * η a = 1 from hη a]
  ring

omit hη in
/-- **`Γ^u_{aa} = −η_aη_u (w_a/w_u) ∂_u σ_a` for `u ≠ a`** — the family carrying
the scale ratio, and the only place the anisotropy enters the connection. -/
theorem chr_gen_off (u a : Fin n) (h : u ≠ a) :
    Chr η w σ u a a = -(η a * η u * ratio w a u * ScaleAlgebra.d u (σ a)) := by
  simp only [Chr, kron_self, one_mul, show (kron u a : A) = 0 from if_neg h]
  ring

omit hη in
/-- **And everything else vanishes**: the upper index must match a lower one, or
the two lower ones must agree. -/
theorem chr_gen_zero (u a b : Fin n) (hua : u ≠ a) (hub : u ≠ b) (hab : a ≠ b) :
    Chr η w σ u a b = 0 := by
  simp only [Chr, show (kron u a : A) = 0 from if_neg hua,
    show (kron u b : A) = 0 from if_neg hub, show (kron a b : A) = 0 from if_neg hab]
  ring

/-- **The trace of the connection is the gradient of the total log-scale.** -/
theorem trace_gen (b : Fin n) :
    (∑ c, Chr η w σ c c b) = ScaleAlgebra.d b (∑ c, σ c) := by
  rw [ScaleAlgebra.d_sum]
  exact Finset.sum_congr rfl fun c _ => chr_gen_diag η w σ hη c b

/-! ### The off-diagonal Ricci is purely transverse

The same cancellation as in the static case, and now visibly not an accident of
it: **every term built from `σ_a` and `σ_b` alone drops out**, and what survives
is a sum over the directions *other* than the two being paired. -/

variable (n) in
/-- The expression the off-diagonal Ricci reduces to: a sum over the transverse
directions, with `σ_a` and `σ_b` entering only through their gradients along the
*other* pair member. -/
def offDiagTransverse (σ : Fin n → A) (a b : Fin n) : A :=
  -∑ c ∈ transverse a b,
    (ScaleAlgebra.d a (ScaleAlgebra.d b (σ c))
      - ScaleAlgebra.d b (σ a) * ScaleAlgebra.d a (σ c)
      - ScaleAlgebra.d a (σ b) * ScaleAlgebra.d b (σ c)
      + ScaleAlgebra.d a (σ c) * ScaleAlgebra.d b (σ c))

omit hη in
/-- The connection is symmetric in its lower pair, without staticity. -/
theorem chr_lower_symm (u a b : Fin n) : Chr η w σ u a b = Chr η w σ u b a := by
  by_cases h : a = b
  · subst h; rfl
  · simp only [Chr, show (kron a b : A) = 0 from if_neg h,
      show (kron b a : A) = 0 from if_neg (Ne.symm h)]
    ring

/-- **The off-diagonal Ricci is purely transverse.**

        R_ab  =  −Σ_{c ∉ {a,b}} [ ∂_a∂_b σ_c − (∂_bσ_a)(∂_aσ_c)
                                   − (∂_aσ_b)(∂_bσ_c) + (∂_aσ_c)(∂_bσ_c) ]

**Every term built from `σ_a` and `σ_b` alone cancels identically** — the second
derivatives `∂_a∂_bσ_a`, `∂_a∂_bσ_b`, the products `(∂_aσ_a)(∂_bσ_a)`,
`(∂_aσ_b)(∂_bσ_b)`, and the cross term `(∂_bσ_a)(∂_aσ_b)` all drop out.  What
survives is a sum over the directions *other* than the pair.

This is the same cancellation as `combination_is_transverse`, and seeing it twice
in two different components shows it is not an accident of the static ansatz.
It is a property of diagonal metrics: **no pair of directions carries its own
curvature; every component is carried by the complement.** -/
theorem ric_offdiag (a b : Fin n) (hab : a ≠ b) :
    Ric η w σ a b = offDiagTransverse n σ a b := by
  have hba : b ≠ a := Ne.symm hab
  have hmem : ∀ c ∈ transverse a b, c ≠ a ∧ c ≠ b := fun c hc =>
    ⟨(Finset.mem_erase.mp (Finset.mem_of_mem_erase hc)).1, (Finset.mem_erase.mp hc).1⟩
  -- T1
  have h1z : (∑ c ∈ transverse a b, ScaleAlgebra.d c (Chr η w σ c a b)) = 0 :=
    Finset.sum_eq_zero fun c hc => by
      rw [chr_gen_zero η w σ c a b (hmem c hc).1 (hmem c hc).2 hab, ScaleAlgebra.d_zero]
  have hT1 : (∑ c, ScaleAlgebra.d c (Chr η w σ c a b))
      = ScaleAlgebra.d a (ScaleAlgebra.d b (σ a))
        + ScaleAlgebra.d a (ScaleAlgebra.d b (σ b)) := by
    rw [sum_split (r := a) (fun c => ScaleAlgebra.d c (Chr η w σ c a b)) hba, h1z, add_zero,
      chr_gen_diag η w σ hη a b, chr_lower_symm η w σ b a b,
      chr_gen_diag η w σ hη b a, ScaleAlgebra.d_comm b a (σ b)]
  -- T2
  have hT2 : ScaleAlgebra.d a (∑ c, Chr η w σ c c b)
      = ScaleAlgebra.d a (ScaleAlgebra.d b (σ a))
        + ScaleAlgebra.d a (ScaleAlgebra.d b (σ b))
        + ∑ c ∈ transverse a b, ScaleAlgebra.d a (ScaleAlgebra.d b (σ c)) := by
    rw [trace_gen η w σ hη b, sum_split (r := a) σ hba]
    simp only [ScaleAlgebra.d_add, ScaleAlgebra.d_sum]
  -- T3
  have h3z : (∑ e ∈ transverse a b,
      (∑ c, Chr η w σ c c e) * Chr η w σ e a b) = 0 :=
    Finset.sum_eq_zero fun e he => by
      rw [chr_gen_zero η w σ e a b (hmem e he).1 (hmem e he).2 hab, mul_zero]
  have hT3 : (∑ e, (∑ c, Chr η w σ c c e) * Chr η w σ e a b)
      = ScaleAlgebra.d a (∑ c, σ c) * ScaleAlgebra.d b (σ a)
        + ScaleAlgebra.d b (∑ c, σ c) * ScaleAlgebra.d a (σ b) := by
    rw [sum_split (r := a) (fun e => (∑ c, Chr η w σ c c e) * Chr η w σ e a b) hba,
      h3z, add_zero, trace_gen η w σ hη a, trace_gen η w σ hη b,
      chr_gen_diag η w σ hη a b, chr_lower_symm η w σ b a b,
      chr_gen_diag η w σ hη b a]
  -- T4, inner sums
  have hInA : (∑ e, Chr η w σ a a e * Chr η w σ e a b)
      = ScaleAlgebra.d a (σ a) * ScaleAlgebra.d b (σ a)
        + ScaleAlgebra.d b (σ a) * ScaleAlgebra.d a (σ b) := by
    have hz : (∑ e ∈ transverse a b, Chr η w σ a a e * Chr η w σ e a b) = 0 :=
      Finset.sum_eq_zero fun e he => by
        rw [chr_gen_zero η w σ e a b (hmem e he).1 (hmem e he).2 hab, mul_zero]
    rw [sum_split (r := a) (fun e => Chr η w σ a a e * Chr η w σ e a b) hba, hz, add_zero,
      chr_gen_diag η w σ hη a a, chr_gen_diag η w σ hη a b,
      chr_lower_symm η w σ b a b, chr_gen_diag η w σ hη b a]
  have hInB : (∑ e, Chr η w σ b a e * Chr η w σ e b b)
      = ScaleAlgebra.d a (σ b) * ScaleAlgebra.d b (σ b)
        + ScaleAlgebra.d b (σ a) * ScaleAlgebra.d a (σ b) := by
    have hz : (∑ e ∈ transverse a b, Chr η w σ b a e * Chr η w σ e b b) = 0 :=
      Finset.sum_eq_zero fun e he => by
        rw [chr_gen_zero η w σ b a e hba (Ne.symm (hmem e he).2) (Ne.symm (hmem e he).1),
          zero_mul]
    have hpair : Chr η w σ b a a * Chr η w σ a b b
        = ScaleAlgebra.d b (σ a) * ScaleAlgebra.d a (σ b) := by
      rw [chr_gen_off η w σ b a hba, chr_gen_off η w σ a b hab]
      have hr : ratio w a b * ratio w b a = 1 := ratio_inv w a b
      calc -(η a * η b * ratio w a b * ScaleAlgebra.d b (σ a))
              * -(η b * η a * ratio w b a * ScaleAlgebra.d a (σ b))
          = ((η a * η a) * (η b * η b)) * ((ratio w a b * ratio w b a)
              * (ScaleAlgebra.d b (σ a) * ScaleAlgebra.d a (σ b))) := by ring
        _ = ScaleAlgebra.d b (σ a) * ScaleAlgebra.d a (σ b) := by
            rw [hη a, hη b, hr]; ring
    rw [sum_split (r := a) (fun e => Chr η w σ b a e * Chr η w σ e b b) hba, hz, add_zero,
      hpair, chr_lower_symm η w σ b a b, chr_gen_diag η w σ hη b a,
      chr_gen_diag η w σ hη b b]
    ring
  have hInT : ∀ c ∈ transverse a b,
      (∑ e, Chr η w σ c a e * Chr η w σ e c b)
        = ScaleAlgebra.d a (σ c) * ScaleAlgebra.d b (σ c) := by
    intro c hc
    have hca : c ≠ a := (hmem c hc).1
    have hcb : c ≠ b := (hmem c hc).2
    have hz : ∀ e ∈ Finset.univ, e ≠ c →
        Chr η w σ c a e * Chr η w σ e c b = 0 := by
      intro e _ hec
      by_cases hea : e = a
      · rw [hea, chr_gen_zero η w σ a c b (Ne.symm hca) hab hcb, mul_zero]
      · rw [chr_gen_zero η w σ c a e hca (Ne.symm hec) (Ne.symm hea), zero_mul]
    rw [Finset.sum_eq_single c hz (fun h => absurd (Finset.mem_univ c) h),
      chr_lower_symm η w σ c a c, chr_gen_diag η w σ hη c a,
      chr_gen_diag η w σ hη c b]
  have hT4 : (∑ c, ∑ e, Chr η w σ c a e * Chr η w σ e c b)
      = (ScaleAlgebra.d a (σ a) * ScaleAlgebra.d b (σ a)
          + ScaleAlgebra.d b (σ a) * ScaleAlgebra.d a (σ b))
        + (ScaleAlgebra.d a (σ b) * ScaleAlgebra.d b (σ b)
          + ScaleAlgebra.d b (σ a) * ScaleAlgebra.d a (σ b))
        + ∑ c ∈ transverse a b,
            ScaleAlgebra.d a (σ c) * ScaleAlgebra.d b (σ c) := by
    rw [sum_split (r := a) (fun c => ∑ e, Chr η w σ c a e * Chr η w σ e c b) hba,
      hInA, hInB, Finset.sum_congr rfl hInT]
  -- the totals of the transverse sums
  have hSa : ScaleAlgebra.d a (∑ c, σ c)
      = ScaleAlgebra.d a (σ a) + ScaleAlgebra.d a (σ b)
        + ∑ c ∈ transverse a b, ScaleAlgebra.d a (σ c) := by
    rw [sum_split (r := a) σ hba]
    simp only [ScaleAlgebra.d_add, ScaleAlgebra.d_sum]
  have hSb : ScaleAlgebra.d b (∑ c, σ c)
      = ScaleAlgebra.d b (σ a) + ScaleAlgebra.d b (σ b)
        + ∑ c ∈ transverse a b, ScaleAlgebra.d b (σ c) := by
    rw [sum_split (r := a) σ hba]
    simp only [ScaleAlgebra.d_add, ScaleAlgebra.d_sum]
  -- split the transverse sum on the right
  have hRHS : (∑ c ∈ transverse a b,
        (ScaleAlgebra.d a (ScaleAlgebra.d b (σ c))
          - ScaleAlgebra.d b (σ a) * ScaleAlgebra.d a (σ c)
          - ScaleAlgebra.d a (σ b) * ScaleAlgebra.d b (σ c)
          + ScaleAlgebra.d a (σ c) * ScaleAlgebra.d b (σ c)))
      = (∑ c ∈ transverse a b, ScaleAlgebra.d a (ScaleAlgebra.d b (σ c)))
        - ScaleAlgebra.d b (σ a) * (∑ c ∈ transverse a b, ScaleAlgebra.d a (σ c))
        - ScaleAlgebra.d a (σ b) * (∑ c ∈ transverse a b, ScaleAlgebra.d b (σ c))
        + ∑ c ∈ transverse a b,
            ScaleAlgebra.d a (σ c) * ScaleAlgebra.d b (σ c) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  -- assemble
  simp only [Ric, hT1, hT2, hT3, hT4, hSa, hSb, offDiagTransverse, hRHS]
  ring

/-- **Consistency check: the static case has no off-diagonal Ricci.**

Every term of the transverse expression carries a derivative along `a` or along
`b`, and staticity kills all but one direction — so for `a ≠ b` at least one
factor vanishes.  This is why `ric_tt` and `ric_rr` were the whole story there. -/
theorem offdiag_vanishes_of_static (r : Fin n)
    (hstat : ∀ x y : Fin n, y ≠ r → ScaleAlgebra.d y (σ x) = 0) (a b : Fin n)
    (hab : a ≠ b) : Ric η w σ a b = 0 := by
  rw [ric_offdiag η w σ hη a b hab, offDiagTransverse]
  have hz : ∀ c ∈ transverse a b,
      ScaleAlgebra.d a (ScaleAlgebra.d b (σ c))
        - ScaleAlgebra.d b (σ a) * ScaleAlgebra.d a (σ c)
        - ScaleAlgebra.d a (σ b) * ScaleAlgebra.d b (σ c)
        + ScaleAlgebra.d a (σ c) * ScaleAlgebra.d b (σ c) = 0 := by
    intro c _
    by_cases hbr : b = r
    · have har : a ≠ r := by rw [← hbr]; exact hab
      rw [ScaleAlgebra.d_comm a b (σ c), hstat c a har, hstat b a har,
        ScaleAlgebra.d_zero]
      ring
    · rw [hstat c b hbr, hstat a b hbr, ScaleAlgebra.d_zero]
      ring
  rw [Finset.sum_eq_zero hz, neg_zero]

end General

/-! ## What the general computation says

Two structural consequences, and a reading of A7 that was not visible before. -/

section Consequences

variable {A : Type*} [CommRing A]

/-- With only two directions there is nothing transverse to a pair. -/
theorem transverse_empty_of_two (a b : Fin 2) (hab : a ≠ b) :
    transverse a b = (∅ : Finset (Fin 2)) := by
  revert hab
  revert a b
  decide

/-- **In two directions the diagonal ansatz is free.**

There is no direction outside a pair, so the off-diagonal Ricci vanishes
identically and diagonality costs nothing.  For `n ≥ 3` it does cost something:
each pair contributes a constraint, and the constraint is carried entirely by the
*other* directions.

So "one scale per direction" is a genuine restriction exactly where there is
somewhere for the restriction to live — which is the same shape as
`Openness.no_dissipation_in_one_direction`, where openness needed a transverse
direction to leak into. -/
theorem offdiag_zero_in_two [ScaleAlgebra 2 A] (η : Fin 2 → A) (w : Fin 2 → Aˣ)
    (σ : Fin 2 → A) (hη : ∀ a : Fin 2, η a * η a = 1) (a b : Fin 2) (hab : a ≠ b) :
    Ric η w σ a b = 0 := by
  rw [ric_offdiag η w σ hη a b hab, offDiagTransverse,
    transverse_empty_of_two a b hab, Finset.sum_empty, neg_zero]

/-- **The constraints are indexed by the rotation sector.**

`ric_offdiag` gives one equation per unordered **pair** of directions, and
`Pattern.rotDim2 m = (m+1)m` is twice the number of such pairs among `m+1`
directions — the doubled dimension of `Λ²p`.  So the diagonality constraints are
counted by the *same* index set the coupling generates rotations in.

Then A7, `rotDim2 = scaleDim2`, reads:

> **the number of constraints on the diagonal ansatz equals the number of scale
> functions it constrains.**

The system is neither over- nor under-determined, and that is a reading of A7
this development did not have.  It is a *gloss* on a count, not a new theorem —
what makes it available is `ric_offdiag`, which shows the components are
pair-indexed. -/
theorem constraint_count (m : ℕ) : rotDim2 m = (m + 1) * m := rfl

/-- And under A7 the two counts agree, at exactly one dimension. -/
theorem constraints_match_functions (m : ℕ) :
    Observability m ↔ m = 2 := observability_iff_two m

end Consequences

end SCD.Diagonal
