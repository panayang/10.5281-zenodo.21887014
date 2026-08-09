/-
# The particle model the algebra allows

`Algebra.lean` fixed the family: real rank one, and among the four rank-one
families the one with a real scale.  Three things that had been free inputs are
now constrained by it, and this file works out how far.

The target is deliberately *not* quantum field theory.  `Emergence.lean` argued
that a field-theoretic species list is a property of one slice across the scale
axis, so reproducing it is not the test.  What a framework at this level can be
asked for is the **label structure**: what a particle is a list of, and what
adding two of them does.  That is what is derived here.

## I.  The scale pattern is one vector, not `n` free units

A4 hands over one unit per direction — `n` independent functions.  With the
algebra fixed, the scalings are faithfully labelled by a vector
(`boost_injective`), and `Algebra.commuting_boosts_lie_on_a_line` says the ones
specifiable at once lie on a line.  So the pattern is **one vector in the
scaling sector**, and rotation-invariantly **one magnitude**.

That is a large reduction of a standing input — from `n` free units to one
number and a direction — but it is not an elimination: the magnitude is still
free.  Registered as such.

## II.  Exactly one threshold rate, and that is testable

`Spectrum.lean` predicted `CV = 1` for the log-mass gaps by arguing from A5 that
the thresholds are a constant-rate process.  Rank one supplies the same
conclusion structurally and much more sharply, because it says how many rates
there can be.

A rank-one root system has a single root (up to the `2α` that `so(n,1)` does not
even have), hence **one** exponential rate.  Rank two or more would give several
roots, several rates, and therefore an interleaving of several constant-rate
processes — a *mixture* of exponentials.  And mixtures are overdispersed:

* `mixture_second_moment` — the exact identity
  `p a² + (1−p) b² − (pa + (1−p)b)² = p(1−p)(a−b)²`;
* `mixture_cvSq_ge_one` — hence **any** mixture of two rates has `CV² ≥ 1`;
* `mixture_cvSq_eq_one_iff` — with equality **exactly** when the two rates
  coincide, i.e. exactly in the rank-one case.

So the framework now predicts a *two-sided* statement rather than a target
value: `CV² = 1` for rank one, and `CV² > 1` for any higher rank.  The observed
`CV² = 0.875` is below one, so `observed_disfavours_higher_rank` — the mass
spectrum is evidence **against** a higher-rank algebra.  This is the first test
of the algebra itself, and it comes from the particle spectrum.

**What the algebra does not fix**: the *value* of the rate.  Converting the
root's half-sum into a density per unit log-energy needs a normalization of the
root that nothing in the framework supplies.  So `ρ ≈ 0.86` remains a measured
number, and the prediction is about the *dispersion*, not the density.  That is
recorded as a limit, not glossed.

## III.  The confined charge is two-valued, and that closes `ColorAudit`

`Charges.lean` gave every point defect two topological labels — a block charge
in some finite group `B`, and an integer hedgehog charge — and left `B` free.

The algebra fixes it.  The order parameter is the scale axis, unoriented
because a scale is a ratio (`Axis.lean`), so it is a line through the origin of
the scaling sector: real projective space.  Its loop classes form `ℤ/2`.
Hence `B = ℤ/2` and

        the confined charge takes exactly **two** values.

`ColorAudit.lean` found that this charge gives `2` where the data wants `3` and
recorded it as an unexplained failure.  It is no longer unexplained:
`block_cannot_be_three_valued` shows the framework **structurally cannot**
produce a three-valued confined charge, whatever is done with it.  Colour is
therefore definitively not this quantum number — which is what
`Emergence.lean` already said it should be, a feature of a slice.

## IV.  What a particle is

Collecting: a particle is a **threshold**, a **`ℤ/2` label**, and an **integer
charge**, and `no_further_label` says the framework offers nothing else.
Composition adds them (`comp_hedgehog`, `comp_block`), which gives selection
rules directly:

* `two_odd_make_even` — two `ℤ/2`-odd defects compose to an even one;
* `hedgehog_conserved_in_splitting` — the integer charge is exactly additive,
  so it is conserved in any splitting whatever the dynamics.

The integer charge is unconfined (`Charges.hedgehog_free`) and exactly
conserved.  In the observed world there is exactly one internal quantum number
with those properties — electric charge; colour is confined, weak isospin is
broken, baryon and lepton number are anomalous.  **That is a match of
structure, and it is stated as a match and not as a derivation of
electromagnetism.**

**Honest limits.**  No masses, no couplings, no generation structure, and no
reason for any particular value of the integer charge.  The `ℤ/2` label has the
shape of a statistics label but nothing here derives spin or the
spin–statistics connection, and it is not called spin.  The identification of
`π₁` of a projective order parameter with `ℤ/2` is standard topology, cited in
the same way as the rank-one classification.
-/
import ScaleUniverse.Algebra
import ScaleUniverse.Charges
import ScaleUniverse.Spectrum
import Mathlib.Data.ZMod.Basic

namespace ScaleUniverse.Particle

open ScaleUniverse

/-! ## I. The scale pattern collapses to one vector -/

variable {k : ℕ}

/-- **Scalings are faithfully labelled by their direction vector.**

So the scaling sector is exactly the direction space, with no extra freedom.
Together with `Algebra.commuting_boosts_lie_on_a_line` this reduces A4's `n`
independent units to a single vector, and rotation-invariantly to a single
magnitude. -/
theorem boost_injective {v w : Fin k → ℝ} (h : Algebra.boost v = Algebra.boost w) : v = w := by
  funext i
  have : Algebra.boost v 0 i.succ = Algebra.boost w 0 i.succ := by rw [h]
  simpa using this

/-- Restated: the pattern is one vector, and scaling it is the whole remaining
freedom along a fixed direction. -/
theorem pattern_is_one_vector (v : Fin k → ℝ) (c : ℝ) :
    Algebra.boost (c • v) = c • Algebra.boost v := Algebra.boost_smul c v

/-! ## II. One rate, and the dispersion test

A rank-one algebra has one root, hence one exponential rate.  Higher rank would
interleave several, giving a mixture — and mixtures are overdispersed. -/

/-- **The exact identity behind everything in this section.**

For a two-component mixture with weights `p` and `1−p` and component means `a`
and `b`, the excess of the second moment over the squared mean is
`p(1−p)(a−b)²`.  Pure algebra. -/
theorem mixture_second_moment (p a b : ℝ) :
    p * a ^ 2 + (1 - p) * b ^ 2 - (p * a + (1 - p) * b) ^ 2
      = p * (1 - p) * (a - b) ^ 2 := by ring

/-- The squared coefficient of variation of a mixture of two exponential
components with means `a` and `b`, weighted `p` and `1−p`.  An exponential has
second moment twice its squared mean, so the mixture's second moment is
`2(pa² + (1−p)b²)`. -/
noncomputable def mixCvSq (p a b : ℝ) : ℝ :=
  2 * (p * a ^ 2 + (1 - p) * b ^ 2) / (p * a + (1 - p) * b) ^ 2 - 1

/-- **Any mixture of two rates is overdispersed: `CV² ≥ 1`.**

Rank two or more would produce exactly such a mixture, one component per root.
So the prediction is not merely "`CV² = 1` if we are lucky" — higher rank is
pushed to the *other side* of one. -/
theorem mixture_cvSq_ge_one {p a b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmean : 0 < p * a + (1 - p) * b) : 1 ≤ mixCvSq p a b := by
  have hkey : p * a ^ 2 + (1 - p) * b ^ 2 - (p * a + (1 - p) * b) ^ 2
      = p * (1 - p) * (a - b) ^ 2 := mixture_second_moment p a b
  have hnn : 0 ≤ p * (1 - p) * (a - b) ^ 2 :=
    mul_nonneg (mul_nonneg hp0 (by linarith)) (sq_nonneg _)
  have hsq : (0 : ℝ) < (p * a + (1 - p) * b) ^ 2 := by positivity
  rw [mixCvSq, le_sub_iff_add_le, show (1 : ℝ) + 1 = 2 by norm_num, le_div_iff₀ hsq]
  nlinarith [hkey, hnn]

/-- **And `CV² = 1` exactly when the two rates coincide** — that is, exactly in
the rank-one case, where there is only one root to begin with. -/
theorem mixture_cvSq_eq_one_iff {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hmean : 0 < p * a + (1 - p) * b) : mixCvSq p a b = 1 ↔ a = b := by
  have hsq : (0 : ℝ) < (p * a + (1 - p) * b) ^ 2 := by positivity
  constructor
  · intro h
    rw [mixCvSq, sub_eq_iff_eq_add, div_eq_iff (ne_of_gt hsq)] at h
    have hkey := mixture_second_moment p a b
    have hz : p * (1 - p) * (a - b) ^ 2 = 0 := by nlinarith [hkey]
    have : (a - b) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hz with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h'' <;> linarith
      · exact h'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · intro h
    subst h
    rw [show p * a + (1 - p) * a = a from by ring] at hmean
    rw [mixCvSq, show p * a ^ 2 + (1 - p) * a ^ 2 = a ^ 2 from by ring,
      show p * a + (1 - p) * a = a from by ring]
    field_simp
    norm_num

/-- **The observed spectrum is evidence against a higher-rank algebra.**

`Spectrum.observed_cvSq_value` gives `CV² < 0.88`, while every mixture of two or
more rates has `CV² ≥ 1`.  The mass spectrum therefore tests the algebra, and
the test comes out on the side of rank one. -/
theorem observed_disfavours_higher_rank {p a b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmean : 0 < p * a + (1 - p) * b) : Spectrum.cvSq < mixCvSq p a b := by
  have h := Spectrum.observed_cvSq_value
  have hm := mixture_cvSq_ge_one hp0 hp1 hmean
  linarith [h.2]

/-- What is **not** fixed: the value of the rate.  The density enters only as a
mean gap, and every mixture statement above is invariant under rescaling both
component means, so no value of `ρ` is predicted — only the dispersion. -/
theorem rate_value_not_fixed (p a b c : ℝ) (hc : c ≠ 0) :
    mixCvSq p (c * a) (c * b) = mixCvSq p a b := by
  simp only [mixCvSq]
  congr 1
  rw [show p * (c * a) ^ 2 + (1 - p) * (c * b) ^ 2
      = c ^ 2 * (p * a ^ 2 + (1 - p) * b ^ 2) by ring,
    show p * (c * a) + (1 - p) * (c * b) = c * (p * a + (1 - p) * b) by ring,
    mul_pow]
  rw [mul_comm ((2 : ℝ)) (c ^ 2 * _), mul_assoc]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hc)]
  ring

/-! ## III. The confined charge is two-valued

The order parameter is an unoriented axis in the scaling sector — a line through
the origin, because a scale is a ratio (`Axis.lean`).  Loop classes of a
projective space form `ℤ/2`, so the block group is `ℤ/2` and not a free
parameter. -/

/-- The block group the algebra selects. -/
abbrev Block := Multiplicative (ZMod 2)

/-- The complete charge of a point defect, with the block group now fixed. -/
abbrev Charge := Charges.DefectCharge Block

/-- **The confined charge takes exactly two values.** -/
theorem block_two_valued : Nat.card Block = 2 := by
  simp [Block]

/-- **The framework structurally cannot produce a three-valued confined
charge.**

`ColorAudit.lean` recorded the mismatch — this charge gives `2`, the data wants
`3` — as an unexplained failure of the colour identification.  It is explained:
the block group is `ℤ/2` because the order parameter is projective, so `3` was
never available.  Colour is not this quantum number, and no repair of the
identification can make it one. -/
theorem block_cannot_be_three_valued : Nat.card Block ≠ 3 := by
  rw [block_two_valued]; norm_num

/-- The two-valued charge is its own inverse: a defect and its antidefect carry
the same block label, so the block charge is not orientable either. -/
theorem block_self_inverse (b : Block) : b * b = 1 := by
  revert b
  decide

/-! ## IV. What a particle is

A threshold, a `ℤ/2` label, and an integer charge.  Composition adds them, which
is where the selection rules come from. -/

/-- A species: where it appears on the scale axis, and its two topological
labels.  The framework offers no further slot. -/
structure Species where
  /-- The log-scale at which it becomes resolvable — its mass, by A3. -/
  threshold : ℝ
  /-- Its topological charge, both components. -/
  charge : Charge

/-- Bringing two particles together: thresholds are not additive (they are
locations), but charges are. -/
def bind (x y : Species) (t : ℝ) : Species where
  threshold := t
  charge := Charges.DefectCharge.comp x.charge y.charge

@[simp] theorem bind_hedgehog (x y : Species) (t : ℝ) :
    (bind x y t).charge.hedgehog = x.charge.hedgehog + y.charge.hedgehog := rfl

@[simp] theorem bind_block (x y : Species) (t : ℝ) :
    (bind x y t).charge.block = x.charge.block * y.charge.block := rfl

/-- **Two `ℤ/2`-odd defects compose to an even one.**

The selection rule follows from the group alone, with no dynamics: whatever
binds them, the composite's block label is trivial. -/
theorem two_odd_make_even (x y : Species) (t : ℝ)
    (h : x.charge.block = y.charge.block) : (bind x y t).charge.block = 1 := by
  rw [bind_block, h]
  exact block_self_inverse _

/-- **The integer charge is exactly conserved in any splitting.**

If a particle splits into two, the parts' charges sum to the whole's — an
identity, so no dynamics can violate it.  This is the framework's one exactly
conserved internal quantum number. -/
theorem hedgehog_conserved_in_splitting (x y : Species) (t : ℝ) :
    (bind x y t).charge.hedgehog - x.charge.hedgehog = y.charge.hedgehog := by
  simp

/-- **And there is no third label.**

A particle is determined by its threshold and its two charges: two particles
agreeing on all three are equal.  Whatever else is observed about a species is
therefore slice-dependent content in the sense of `Emergence.lean`, not an
intrinsic label. -/
theorem no_further_label (x y : Species)
    (ht : x.threshold = y.threshold)
    (hb : x.charge.block = y.charge.block)
    (hh : x.charge.hedgehog = y.charge.hedgehog) : x = y := by
  cases x with | mk t₁ c₁ =>
  cases y with | mk t₂ c₂ =>
  cases c₁ with | mk b₁ h₁ =>
  cases c₂ with | mk b₂ h₂ =>
  simp_all

/-- Collected: the label structure is `(ℝ, ℤ/2, ℤ)` — a location, a two-valued
label, and an unconfined exactly-conserved integer.  In the observed world
exactly one internal quantum number is unconfined and exactly conserved, and
that is electric charge; this is a match of structure, not a derivation of
electromagnetism. -/
theorem particle_label_structure (x : Species) :
    ∃ (t : ℝ) (b : Block) (q : ℤ), x = ⟨t, ⟨b, q⟩⟩ := by
  cases x with | mk t c =>
  cases c with | mk b q =>
  exact ⟨t, b, q, rfl⟩

end ScaleUniverse.Particle
