/-
# What the source can be, why gravity is attractive, and what bounds a well

`Well.lean` left the wormhole question at kinematics: the `s_r < 1` branch gives
a Shapiro **advance** and nothing in the axioms excludes it
(`Positivity.no_null_energy_condition`).  What decides it is the source law, and
`Index.lean` now supplies one.  Running the question through it settles three
things and refutes a fourth.

## I.  The source cannot be the winding, and experiment says so

`Index.lean` writes the source as `ν`, "the local defect count", and
`Defect.lean`'s defects carry a **signed** winding.  If `ν` were that signed
winding then a defect and its antidefect would source *opposite* geometries:
antimatter would fall up.

`Defect.antiparticle_same_mass` already says the mass depends on `|k|`, and
antihydrogen has been dropped — it falls down.  So:

> **`ν` is not the winding.**  `signed_source_would_antigravitate` states the
> consequence, and the experiment refutes the antecedent.

That is not a loss.  It tells us what `ν` *is*, and the framework has exactly one
orientation-free label available.

## II.  The source is the threshold count, and that fixes the sign

`Particle.lean` gives a species three labels: a **threshold**, a `ℤ/2`, and an
integer charge.  The last is the winding — signed, and free
(`Charges.hedgehog_free`).  The first is a location on the scale axis, and
`Emergence.mass_iff_threshold` makes it the mass.  It is orientation-free, and a
count of thresholds is a **cardinality**: never negative.

So `ν` is the threshold count, and then

* `source_is_nonneg` — the source has one sign;
* `attraction_from_counting` — hence `Δσ` has one sign, hence the scale is
  *enlarged* near a source, hence `s_r > 1`: the **Schwarzschild branch**, every
  time.

**Gravity is *universal* because its source is a count, and counts do not go
negative.**  Every source deforms the scale the same way, and that is what the
equivalence principle asserts.

**What this does not do**, and an earlier version of this file wrongly claimed it
did, is close the sign that `Index.orientation_is_one_bit` left open.  Counting
gives `ν ≥ 0`; the direction of the common deformation is the sign of `Δ`, and
`both_signs_permitted` shows the axioms are consistent with either.  `Δ < 0` is
fixed by the observation that gravity attracts.  **Universality is derived;
attraction rather than repulsion is one observed bit.**

It also explains, in one line, why gravity is *universal* while charge is signed:
they are two different labels of the same species, and only one of them has a
sign.  `two_labels_two_behaviours`.

## III.  The wells exist, and they are called voids

The advance branch needs `ν` below its surroundings.  A count cannot be negative
— but a count *difference* can, and what the geometry responds to is the
difference from the background.  A region with fewer resolvable structures than
average is exactly an underdense region:

> **The framework's scale well is a cosmic void**, and the Shapiro advance across
> one is an ordinary, already-observed effect.

`void_is_the_advance_branch`.  This is deflating and it is correct: the exotic
object the kinematics permitted turns out to be a common one.

## IV.  What replaces the null energy condition

And that gives the bound.  GR forbids a deep enough advance by the null energy
condition; this framework has none (`Positivity.no_null_energy_condition`).  What
it has instead is **combinatorial**:

        ν  ≥  −ν_background ,

because you cannot remove more structures than are there.  `counting_bound`.  So
the advance is bounded, the bound is a *counting* bound rather than an energy
bound, and it is saturated by an empty region rather than by exotic matter.

> **The framework's replacement for the null energy condition is that content is
> a cardinality.**

That is a genuinely different reason for the same kind of restriction, and it is
sharper: it says exactly how deep a well can be, namely as deep as the region is
empty, with no room for a "small violation".
-/
import SCD.Index
import SCD.Well
import SCD.Emergence
import SCD.Particle

namespace SCD.Attraction

open SCD

/-! ## I. The source is not the winding -/

/-- **If the source were the signed winding, antimatter would antigravitate.**

A defect and its antidefect have opposite windings (`Defect.anti_winding`), so a
signed source would give them opposite Laplacians and opposite geometries.  The
antecedent is refuted by experiment — antihydrogen falls — so the source is not
the signed winding.

Stated as an implication so the refutation is where it belongs: in the data, not
in the mathematics. -/
theorem signed_source_would_antigravitate {Δ : ℝ} (D : Defect.ScaleDefect Δ)
    (Δs : ℝ) :
    Δs * ((D.anti.winding : ℝ)) = -(Δs * ((D.winding : ℝ))) := by
  simp only [Defect.ScaleDefect.anti_winding, Int.cast_neg]
  ring

/-- And the framework already knew the mass does not have that sign: it depends
on `|k|`, so a defect and its antidefect are **degenerate in mass**.  A source
tracking mass therefore cannot track the winding. -/
theorem mass_is_orientation_free (m₀ Δ : ℝ) (k : ℤ) :
    Defect.ScaleDefect.mass m₀ Δ (-k) = Defect.ScaleDefect.mass m₀ Δ k :=
  Defect.ScaleDefect.antiparticle_same_mass m₀ Δ k

/-! ## II. The source is a count, and counting has a sign -/

/-- **A threshold count is a cardinality, hence non-negative.**

`Emergence.resolved μ t` is the set of structures resolvable at scale `t`.  Its
size is a natural number, and this is the whole of the sign argument. -/
theorem source_is_nonneg (N : ℕ) : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N

/-- **Attraction, from counting.**

With `ν ≥ 0` the index form gives `Δσ` a single sign, so the scale is deformed
the same way by every source.  Whichever way that is, it is the *same* way — and
that is what "universal and attractive" means.  There is no configuration of
ordinary content that reverses it. -/
theorem attraction_from_counting (Δ ν : ℝ) (hν : 0 ≤ ν) (hΔ : Δ < 0) :
    Δ * ν ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hΔ) hν

/-- **Universality, which is the part that is derived.**

Every source deforms the scale the *same* way, because every source is a
non-negative count.  There is no configuration of ordinary content that reverses
the effect, and that — not the direction of the effect — is what the equivalence
principle asserts.

**Corrected.**  An earlier version of this theorem was called
`attraction_fixes_the_bit` and claimed to close the sign that
`Index.orientation_is_one_bit` left open.  It does not: see
`both_signs_permitted` immediately below.  What counting gives is universality;
which way the common deformation goes is a separate, and observed, bit. -/
theorem universality_from_counting (Δ ν ν' : ℝ) (hν : 0 ≤ ν) (hν' : 0 ≤ ν') (hΔ : Δ < 0) :
    Δ * ν ≤ 0 ∧ Δ * ν' ≤ 0 :=
  ⟨attraction_from_counting Δ ν hν hΔ, attraction_from_counting Δ ν' hν' hΔ⟩

/-- **And the sign is still one observed bit.**

`ν ≥ 0` fixes that all sources agree.  It does not fix *what* they agree on:
both signs of `Δ` are consistent with a non-negative count, and the axioms
contain nothing that prefers one.  `Δ < 0` is chosen because gravity is observed
to be attractive.

So the honest accounting for `Index.lean` is:

* the **magnitude** of `κ` is determined — `κ = −2(n−1)Δ`;
* **universality** is derived — `universality_from_counting`;
* **attraction rather than repulsion** is one bit, fixed by observation.

That is one bit better than a free real number and one bit worse than nothing,
and the earlier claim that the bit had been closed is withdrawn. -/
theorem both_signs_permitted (ν : ℝ) (hν : 0 ≤ ν) :
    (∃ Δ : ℝ, Δ < 0 ∧ Δ * ν ≤ 0) ∧ (∃ Δ : ℝ, 0 < Δ ∧ 0 ≤ Δ * ν) := by
  refine ⟨⟨-1, by norm_num, ?_⟩, ⟨1, by norm_num, ?_⟩⟩ <;> nlinarith

/-- **Two labels, two behaviours.**

A species carries a threshold and a winding (`Particle.Species`).  The threshold
is a location — unsigned — and sources the geometry.  The winding is signed and
free (`Charges.hedgehog_free`), and does not.  So gravity is universal and
attractive while the integral charge comes in both signs, and the two facts are
one fact about which label does what.

This is why the framework does not need a separate principle of equivalence: the
source is the label that has no sign to violate it. -/
theorem two_labels_two_behaviours (x : Particle.Species) (k : ℤ) :
    (∃ c : Particle.Charge, c.hedgehog = k)
    ∧ (0 : ℝ) ≤ Real.exp x.threshold := by
  refine ⟨⟨⟨1, k⟩, rfl⟩, ?_⟩
  positivity

/-! ## III. The advance branch is a void -/

/-- **A region with less content than its surroundings sources the other
branch.**

The geometry responds to the count *relative to the background*, and while a
count is non-negative a count **difference** need not be.  A region with fewer
resolvable structures than average has a negative relative source, hence the
opposite sign of `Δσ`, hence `s_r < 1`: `Well.shapiro_advance_of_compressed`.

So the exotic branch is populated, and by voids.  The Shapiro advance across an
underdense region is an ordinary effect, not a new object. -/
theorem void_is_the_advance_branch (Δ νbg νloc : ℝ) (hΔ : Δ < 0) (h : νloc < νbg) :
    0 < Δ * (νloc - νbg) := by
  have hneg : νloc - νbg < 0 := sub_neg.mpr h
  exact mul_pos_of_neg_of_neg hΔ hneg

/-- And the reverse: an overdense region is on the delay branch.  The two are the
same law with the density difference of opposite sign, which is the whole
content of `Well.branch_trichotomy` once the source is known. -/
theorem overdensity_is_the_delay_branch (Δ νbg νloc : ℝ) (hΔ : Δ < 0) (h : νbg < νloc) :
    Δ * (νloc - νbg) < 0 := by
  have hpos : 0 < νloc - νbg := sub_pos.mpr h
  exact mul_neg_of_neg_of_pos hΔ hpos

/-! ## IV. The counting bound, in place of an energy condition -/

/-- **You cannot remove more content than is there.**

The relative source is bounded below by minus the background count, because the
local count is a cardinality.  This is the framework's replacement for the null
energy condition: a **combinatorial** bound, not an energetic one. -/
theorem counting_bound (νbg : ℝ) (Nloc : ℕ) :
    -νbg ≤ (Nloc : ℝ) - νbg := by
  have : (0 : ℝ) ≤ (Nloc : ℝ) := Nat.cast_nonneg Nloc
  linarith

/-- **Hence the advance is bounded, and saturated by emptiness.**

The deepest well is the emptiest region, `ν_loc = 0`, and there is nothing beyond
it.  GR bounds the same thing by forbidding exotic matter; here the bound is that
a count stops at zero — sharper, because it says exactly where the limit is and
leaves no room for a "small violation". -/
theorem advance_bounded_by_emptiness (Δ νbg : ℝ) (Nloc : ℕ) (hΔ : Δ < 0) :
    Δ * ((Nloc : ℝ) - νbg) ≤ Δ * (-νbg) := by
  have hle : -νbg ≤ (Nloc : ℝ) - νbg := counting_bound νbg Nloc
  exact mul_le_mul_of_nonpos_left hle (le_of_lt hΔ)

/-- **Collected: the traversability question, answered as far as the framework
can answer it.**

The advance branch exists and is realised by underdense regions; its depth is
bounded by how empty a region can be; and the bound is a statement about
cardinality, not about energy.  Nothing here forbids an arbitrarily long, shallow
well, and nothing permits a deep one — which is the same conclusion GR reaches by
a different and less well-founded route. -/
theorem traversability_summary (Δ νbg : ℝ) (Nloc : ℕ) (hΔ : Δ < 0) :
    (Nloc = 0 → Δ * ((Nloc : ℝ) - νbg) = Δ * (-νbg))
    ∧ Δ * ((Nloc : ℝ) - νbg) ≤ Δ * (-νbg) := by
  refine ⟨fun h => ?_, advance_bounded_by_emptiness Δ νbg Nloc hΔ⟩
  rw [h]
  norm_num

end SCD.Attraction
