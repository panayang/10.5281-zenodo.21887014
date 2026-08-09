/-
# The last two inputs, and what they actually are

Two items remained: `n = 4` rests on a judgement, and the scale magnitude is
free.  Chasing the relation between them turned up a third thing sitting
between them that had been conflated throughout, so that is first.

## I.  Directions are the representation, not the algebra

`Direction.lean` removed the index set with the claim that **the directions are
the algebra, and their number is that algebra's dimension**.  With the algebra
now named, that claim can be checked, and it fails.

`so(3,1)` has dimension `6`.  Spacetime has `4` directions.  So the directions
are **not** the algebra: they are the space the algebra *acts on* — its defining
representation.  `algebra_bigger_than_directions` proves the mismatch at the
value the framework selects, so this is not a hypothetical.

Nothing is lost by the correction, and something is gained.  A Lie algebra of
the family `so(k,1)` carries a canonical `k+1`-dimensional defining
representation.  **So once the algebra is named, `n` is not a further input —
it is `k + 1`, and the only number left to fix is `k`.**  Two inputs collapse to
one, which is the first half of the answer to whether the two open items are
related.

## II.  Two self-matching conditions, and which one is meant

`Slice.lean` fixed `k` by requiring the rotations the scalings generate to be as
numerous as the directions A4 labels:

        dim Λ²p = dim p    ⟺    k(k−1)/2 = k    ⟺    k = 3 .

Once directions and algebra are distinguished, a *second* condition of the same
shape becomes visible — requiring the algebra to be as large as what it acts on:

        dim so(k,1) = k+1    ⟺    k(k+1)/2 = k+1    ⟺    k = 2 .

`two_matching_conditions_differ` proves they give different answers.  So
"require the structure to match itself" is **not well posed** until one says
which index set must match which — a fact worth stating plainly, because it is
exactly the kind of gap a numerical coincidence can hide in.

The framework does decide between them.  A4 assigns one scale **per direction**,
and those directions are the scaling sector `p`; `Gauge.lean` makes every
observable label a pattern among them.  So the labels available are `p`'s, and
the thing needing labels is what the coupling generates, namely `Λ²p`.  The
second condition compares the algebra with its representation, and **nothing in
the framework asks those to be equal** — the Lorentz algebra being
six-dimensional while spacetime is four-dimensional is not a defect of anything.

So `k = 3` stands, `n = 4` with it, and the judgement it rests on is now stated
sharply: *the labels A4 provides must suffice for the rotations the coupling
generates.*  That is one assumption about observability, not a numerical
preference.

## III.  The free magnitude is not a defect

The scale pattern is one vector; its direction is rotation gauge and its
magnitude is unfixed.  That looked like a second loose input.  It is not the
same kind of thing.

Every quantity the framework builds from the pattern is **homogeneous** in it:

* `wedge_smul_both` — rescaling the pattern rescales the rotational label by
  `c²`;
* `wedge_ratio_invariant` — so every *ratio* of rotational labels is
  **invariant**, and ratios are what the framework predicts.

`Spectrum.lean`'s conversion table, `Particle.rate_value_not_fixed`, and the
gravitational numbers of `Deflection.lean` and `Precession.lean` are all of this
form.  So the magnitude is not an undetermined prediction: **it is the unit in
which the predictions are expressed**, and a dimensionless theory must have
exactly one such.  The framework has exactly one, which is the minimum
possible.

`only_ratios_are_fixed` states it: the theory determines everything up to one
overall factor, and does not determine that factor because it cannot — there is
nothing left to express it in.

## IV.  And that is where the two items meet

`k` is discrete and the magnitude is continuous, so they are not one freedom.
But they are linked by a conversion, which is the sense in which the intuition
that "`n` should come from the scale" is right.

A rank-one symmetric space of parameter `k` has volume growing like `e^{(k−1)r}`
in its radial coordinate — and the radial coordinate *is* the scale coordinate
(`Algebra.lean`, III.3).  So a population at uniform density in that volume has
threshold density `(k−1)` **per unit radius**, and the observed density is per
unit log-energy.  The two differ by the root normalization `α`, which is exactly
the free magnitude:

        ρ · α = k − 1 .

`density_normalization_relation` records it.  **This is a conversion, not a
prediction** — one equation, one unknown, which is the trap `CrossCheck.lean`
was written to record.  What it does establish is that the two remaining
freedoms are not independent: fixing `k` turns a measurement of `ρ` into a
determination of the normalization, and conversely.

It is also conditional on defects being uniformly distributed in the symmetric
space's volume, which no theorem here supplies.  Registered as an assumption,
not smuggled.

## Where that leaves the inputs

* the algebra family — derived (real rank one, plus a cited classification);
* `n` — no longer independent: `k + 1` once the algebra is named;
* `k = 3` — one judgement, stated in II;
* the magnitude — not an input in the same sense: it is the unit, and a
  dimensionless theory needs exactly one.
-/
import ScaleUniverse.Axes

namespace ScaleUniverse.Dimension

open ScaleUniverse Slice

/-! ## I. The algebra is bigger than the set of directions

Sizes are written doubled so that no natural-number division appears.  The
parameter is `m`, with `k = m + 1` spatial directions and `n = m + 2`
spacetime directions. -/

/-- Twice the dimension of the rotation sector `Λ²p`, with `k = m+1`. -/
def rotDim2 (m : ℕ) : ℕ := (m + 1) * m

/-- Twice the dimension of the scaling sector `p`. -/
def scaleDim2 (m : ℕ) : ℕ := 2 * (m + 1)

/-- Twice the dimension of the whole algebra `so(k,1)`, with `k = m+1`. -/
def algDim2 (m : ℕ) : ℕ := (m + 1) * (m + 2)

/-- Twice the dimension of the defining representation, `n = k+1 = m+2`. -/
def repDim2 (m : ℕ) : ℕ := 2 * (m + 2)

/-- **The algebra is strictly bigger than the space of directions, at the value
the framework selects.**

`dim so(3,1) = 6` while spacetime has `4` directions.  So `Direction.lean`'s
claim that the directions *are* the algebra, with `n` its dimension, is false as
stated: the directions are the defining representation.

Nothing is lost — a `so(k,1)` carries a canonical `k+1`-dimensional
representation, so naming the algebra still fixes `n`. -/
theorem algebra_bigger_than_directions : repDim2 2 < algDim2 2 := by
  norm_num [repDim2, algDim2]

/-- Once the algebra is named, `n` is not an independent input: it is the
dimension of the defining representation, `k + 1`. -/
theorem rep_dim_determined (m : ℕ) : repDim2 m = 2 * ((m + 1) + 1) := rfl

/-! ## II. Two conditions of the same shape, with different answers -/

/-- The condition `Slice.lean` used: the rotations generated are as numerous as
the directions A4 labels.  Its solution is `k = 3`. -/
theorem rot_matches_scale_iff (m : ℕ) : rotDim2 m = scaleDim2 m ↔ m = 2 :=
  wedge_dim_eq_iff m

/-- The other condition that becomes visible once directions and algebra are
distinguished: the algebra as large as what it acts on.  Its solution is
`k = 2`, i.e. `n = 3`. -/
theorem alg_matches_rep_iff (m : ℕ) : algDim2 m = repDim2 m ↔ m = 1 := by
  simp only [algDim2, repDim2]
  constructor
  · intro h
    have h' : (m + 1) * (m + 2) = 2 * (m + 2) := h
    have h'' : (m + 1) * (m + 2) = 2 * (m + 2) := h'
    have := Nat.eq_of_mul_eq_mul_right (show 0 < m + 2 by omega)
      (show (m + 1) * (m + 2) = 2 * (m + 2) from h'')
    omega
  · rintro rfl; norm_num

/-- **The two conditions disagree.**

So "require the structure to match itself" is not well posed until one says
*which* index set must match *which*.  Stating this is the point: a numerical
coincidence can hide in exactly this gap.

The framework decides it — A4 labels the scaling sector, and the coupling
generates rotations that need those labels — but the decision is an assumption
about observability, not arithmetic. -/
theorem two_matching_conditions_differ :
    (rotDim2 2 = scaleDim2 2 ∧ algDim2 2 ≠ repDim2 2)
    ∧ (algDim2 1 = repDim2 1 ∧ rotDim2 1 ≠ scaleDim2 1) := by
  refine ⟨⟨by norm_num [rotDim2, scaleDim2], ?_⟩, ⟨by norm_num [algDim2, repDim2], ?_⟩⟩
  · norm_num [algDim2, repDim2]
  · norm_num [rotDim2, scaleDim2]

/-! ## III. The magnitude is the unit, not a missing prediction -/

variable {k : ℕ}

/-- **Rescaling the pattern rescales the rotational label by `c²`.** -/
theorem wedge_smul_both (c : ℝ) (v w : Fin k → ℝ) (i j : Fin k) :
    wedge (c • v) (c • w) i j = c ^ 2 * wedge v w i j := by
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

/-- **So every ratio of rotational labels is invariant under rescaling the
pattern.**

Ratios are what the framework predicts — the conversion table of
`Spectrum.lean`, the gravitational numbers, the dispersion of
`Particle.lean` — and none of them moves. -/
theorem wedge_ratio_invariant (c : ℝ) (hc : c ≠ 0) (v w : Fin k → ℝ) (i j i' j' : Fin k) :
    wedge (c • v) (c • w) i j / wedge (c • v) (c • w) i' j'
      = wedge v w i j / wedge v w i' j' := by
  rw [wedge_smul_both, wedge_smul_both]
  rcases eq_or_ne (wedge v w i' j') 0 with h | h
  · rw [h]; simp only [mul_zero, div_zero]
  · rw [mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- **The theory fixes everything up to one overall factor, and cannot fix that
factor.**

Not because a prediction is missing, but because there is nothing left to
express it in: it is the unit.  A dimensionless theory must carry exactly one
such number, and this framework carries exactly one — the minimum possible. -/
theorem only_ratios_are_fixed (c : ℝ) (hc : c ≠ 0) (v w : Fin k → ℝ) :
    (∀ i j, wedge (c • v) (c • w) i j = c ^ 2 * wedge v w i j)
    ∧ (∀ i j i' j', wedge (c • v) (c • w) i j / wedge (c • v) (c • w) i' j'
        = wedge v w i j / wedge v w i' j') :=
  ⟨fun i j => wedge_smul_both c v w i j,
   fun i j i' j' => wedge_ratio_invariant c hc v w i j i' j'⟩

/-! ## IV. Where the two remaining freedoms meet -/

/-- **The conversion linking the threshold density to the root normalization.**

A rank-one symmetric space of parameter `k` has volume growing like `e^{(k−1)r}`
in the radial coordinate, and that coordinate is the scale coordinate.  A
population at uniform density in that volume therefore has threshold density
`k−1` per unit radius, while the measured density is per unit log-energy; the
two differ by the normalization `α`.

**This is a conversion, not a prediction** — one equation, one unknown, exactly
the trap `CrossCheck.lean` records.  And it is conditional on defects being
uniformly distributed in the symmetric space's volume, which no theorem here
supplies.  Both caveats are stated rather than smuggled. -/
noncomputable def alphaFromDensity (rho : ℝ) (k : ℕ) : ℝ := ((k : ℝ) - 1) / rho

theorem density_normalization_relation (rho : ℝ) (hrho : rho ≠ 0) (k : ℕ) :
    alphaFromDensity rho k * rho = (k : ℝ) - 1 := by
  simp only [alphaFromDensity]
  field_simp

/-- Carried out at `k = 3` with the observed density: the normalization is
determined, and substituting it back returns the input — which is what makes it
a conversion rather than a test. -/
theorem normalization_returns_input (rho : ℝ) (hrho : rho ≠ 0) :
    alphaFromDensity rho 3 * rho = 2 := by
  rw [density_normalization_relation rho hrho 3]
  norm_num

end ScaleUniverse.Dimension
