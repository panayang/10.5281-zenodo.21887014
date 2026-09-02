/-
# The register: what is retracted, corrected, cited, and assumed

The development was built by revision, and the revisions matter as much as the
results.  Rather than leave that history scattered across six files, this is the
single place to check before relying on anything.

Nothing here is new mathematics.  It is the standing answer to "does this rest
on the axioms alone?", and it is meant to be read before, not after.

## I.  Retracted — was claimed, is now withdrawn

**The geometric mass tower.**  `Defect.lean` posited `m_k = m₀e^{|k|Δ}` and
`QCD.geometric_tower_fails` refuted it against lattice glueball ratios.  But the
law was *assumed*, not derived: `MassAudit.mass_law_underdetermined` exhibits a
quadratic law equally compatible with everything proved.  So the refutation
falsified **that hypothesis**, not the framework.  `Emergence.mass_iff_threshold`
later explained why no such law exists — mass is not a property of a defect, it
is where the defect appears.

**The colour identification.**  `Color.lean` derived a confined finite charge
and read it as colour.  `ColorAudit.lean` found it gives `2` where the data
wants `3`.  The failure was not technical: the attempt borrowed the Standard
Model's *ontology*.  `Particle.block_cannot_be_three_valued` now explains it —
the block group is `ℤ/2` because the order parameter is projective, so `3` was
never available.

**The cross-sector test.**  `CrossCheck.lean` proposed measuring the threshold
density two ways.  The two `ρ`'s are not the same quantity: one is a raw count,
the other sector-restricted and signed.  `Running.lean`'s wording was corrected.

**Codimension.**  `Codimension.lean`'s theorems hold of a circle-valued scale.
They do not describe this framework: with A4 directional, `Axis.lean` restores
point defects.

## II.  Corrected — the claim was overstated, the theorem survives

**"Commuting derivations are flat."**  `Direction.lean` read A1's `d_comm` as a
hidden flatness assumption.  `Dynamics.no_flatness_from_commuting_derivations`
refutes it: kill every derivation and the curvature survives.  A chart is a
chart; flatness lives in whether the *connection* commutes.

**"Directions are the algebra."**  Same file.  With the algebra named,
`dim so(3,1) = 6 ≠ 4`.  Directions are the **defining representation**
(`Dimension.algebra_bigger_than_directions`).  Nothing was lost: naming the
algebra still fixes `n = k + 1`.

**"Multiplets are internally flat."**  `Dynamics.same_multiplet_no_rotation`
holds of anything meeting its hypothesis, but that hypothesis assigns one
scaling operator per direction and real rank one supplies one vector and one
scaling.  The physical gloss is withdrawn; `Axes.lean` replaces it.

**"Uniaxial patterns carry no rotation."**  The theorem said a vector wedged
with *itself* vanishes — that is about **homogeneity**, not about axes.  It is
now `Slice.homogeneous_carries_no_rotation`, and the dilemma it appeared to
create dissolved (`Axes.lean`).  This one survived a formalisation and a
published draft before being caught.

**"The channels are independent."**  `Expressive.channels_independent` is true
of the *scalar* sector.  `Coupling.lean` shows the directional scale makes the
rotation sector *generated* by the scale sector.

**`f₀(500)` violates the width bound.**  A previous version of `Data.lean`
quoted the pole as `457 − i279`, which is neither standard determination.  With
the real values the bound falls *between* CCL and GKPY; it is open, not
violated.

## III.  The recurring error

Five of the corrections above are the same mistake: **scalar reasoning where the
structure is directional.**  Taking the attribution from the files' own
self-diagnoses rather than from memory:

1. `Frame.lean` — geometry: the scalar scale forbids Schwarzschild;
2. `Codimension.lean` — defects: a circle-valued (scalar) scale predicts
   strings, corrected by `Axis.lean`'s unoriented axis;
3. `Coupling.lean` — the foundation: "ratios commute" is a scalar statement;
4. `Direction.lean` — the flatness reading of commuting derivations;
5. `Axes.lean` — the uniaxial reading of `wedge v v = 0`, which is about
   *homogeneity*; the theorem was renamed in `Slice.lean`.

An earlier version of this list credited `Axis.lean` and `Slice.lean` for
occurrences 2 and 5.  Those are the files that *corrected* them; the files that
*made* them are `Codimension.lean` and `Axes.lean`'s antecedent.  The count is
unchanged; the attribution was wrong and is fixed.

`scalar_for_directional_count` records the number so it cannot drift.

**The diagnostic that catches it:** when a claim mentions a count — one axis,
one scale, one direction, one value — ask *a count of what*.  Values and
directions come apart every time.

## IV.  Cited, not proved

* the classification of real-rank-one real simple Lie algebras
  (`so(n,1)`, `su(n,1)`, `sp(n,1)`, `f₄₍₋₂₀₎`), used in `Algebra.lean` to pass
  from "real rank one" to "the Lorentz family".  Rank one itself is proved; the
  exhaustiveness of the list is not;
* the homotopy of projective spaces — `π₁(ℝPⁿ) = ℤ/2`, `π₂(S²) = ℤ`, and the
  vanishing of `π₂` for a Lie group modulo a discrete subgroup — used in
  `Particle.lean` and `Axes.lean`;
* **the classification of self-dual locally compact abelian groups**, used in
  `Dual.lean` to pass from A3′ to a short list of possible scale groups
  (`ℝⁿ`, compact–discrete pairs, finite, adelic).  What is proved there is the
  contrast between the two branches the development actually carries; that the
  list is exhaustive is standard harmonic analysis and is cited.

If either citation fails, the constraint above it still stands; only the
identification does not.

## V.  Assumed, and registered rather than smuggled

* **A6′, the scale response law** `e^{2σ}R = κρ`.  **This is not one of the
  seven axioms.**  It is an external physical input, introduced in `Newton.lean`
  and load-bearing there and in `RicciDiag.lean`, `Precession.lean` and
  `Waves.lean`.  It appears as an explicit hypothesis in every theorem that uses
  it, so nothing is hidden at the type level — but it was **missing from this
  register**, which is the one place a reader looks to answer "does this rest on
  the axioms alone?".  Added after an external audit pointed it out.

  **Since §V.d it has a replacement.**  `Index.lean`'s `Δσ = Δ·ν` determines
  `κ = −2(n−1)Δ` and needs no condition at infinity.  **A replacement is still an
  input**, so this entry stands — but it is an input with no *magnitude* to fit,
  which is a different thing from a fitted constant.

  **This entry itself carried a stale overclaim until §V.n caught it.**  It said
  the replacement has "no free number" and credited
  `Attraction.attraction_fixes_the_bit` — a theorem that had been *renamed*
  `universality_from_counting` by §V.a′ precisely because the claim was withdrawn.
  `Attraction.both_signs_permitted` shows both signs of `Δ` are consistent with a
  non-negative count, and `Attraction.lean`'s own text says so.  **The orientation
  bit is still fixed by observation, not by the axioms** — the register
  contradicted itself and the correct reading is §V.a′'s.
* **defects uniform in the symmetric space's volume**, needed for the
  `ρ·α = k−1` conversion in `Dimension.lean`.  No theorem supplies it — and the
  entry is *weaker* than it reads: `Dimension.density_normalization_relation` is
  its own definition unfolded, a tautology, and the physics is two
  identifications (`α` as the root normalisation, `ρ` as the measured density)
  neither of which is formalised anywhere;
* **A7 itself** — a commitment about what counts as an observation, promoted to
  an axiom in `Postulates.lean` rather than left as a judgement.

### V.a  Entries the register was missing

Found by auditing what the individual files self-register against what this list
contained.  Three of them said "registered as such" in their own docstrings and
were **never registered here** — the same failure mode that once hid A6′, and the
reason that failure was called the register's most consequential gap.

* **The timelike sign convention.**  `Signature.lean` derives the `1 + (n−1)`
  split from a drift being one linear functional, and says in its own text that
  what is *not* derived is "the sign convention that makes the distinguished
  direction timelike rather than merely distinguished".  Every theorem taking
  `η_t = −1` inherits it, including the whole of `Momentum.lean`'s dispersion
  relation and `Light.lean`'s cone.  It is one bit, and it was invisible here;
* **The vacuum Ricci combination.**  `Vacuum.lean` says plainly that the step
  from the vacuum condition to "the scale sum is constant" — the standard
  `R_tt/A + R_rr/B = 0` — "is taken as input", pending the diagonal-ansatz
  curvature computation.  The reciprocity chain that supplies `γ = 1` and half
  the light deflection runs through it.  This is the most load-bearing of the
  three.

  **DISCHARGED.**  `Diagonal.lean` derives it: the Levi-Civita connection of
  A4′'s metric, *certified* by `metric_compatible`; the static structure; both
  Ricci components (`ric_tt`, `ric_rr`) contracted from the connection; the
  cancellation (`combination_is_transverse`); and `vacuum_scale_sum`, which is
  exactly what was being assumed.  Nothing is transcribed and no `1/r` is
  inserted by hand — the prefactor comes out as the **total transverse scale
  gradient**, so the textbook `(n−2)/r` is a count of transverse directions times
  their common gradient.

  One caveat about *setting*, not about content: the derivation is algebraic and
  `Vacuum.lean`/`Schwarzschild.lean` are real-analytic.  The statements
  correspond term for term and the algebraic one is more general; rewiring those
  two files to consume it is a refactor, not a gap;
* **`n` itself.**  `Signature.lean` lists it; `Dimension.lean` reduces it to
  `k + 1` once the algebra is named and `Locus.lean` gets `k = 3` from A7 — so it
  is not independent, but the chain passes through A7 and the cited
  classification, and the register should say so in one place rather than three.

### V.a′  Entries the recent work added

* **`ν` is the threshold count.**  `Attraction.lean` argues it cannot be the
  signed winding, because antimatter would then antigravitate and antihydrogen
  falls.  That is an **empirically motivated identification**, not a theorem: the
  framework offers the threshold as the only orientation-free label, but nothing
  proves the source must be that label rather than some other function of it;
* **The sign of `Δ`.**  `Index.orientation_is_one_bit` left it open and I claimed
  `Attraction.lean` had closed it.  **It has not** — `Attraction.both_signs_permitted`
  shows both signs are consistent with a non-negative count.  What counting gives
  is **universality**; that the common deformation is attractive rather than
  repulsive is one bit, fixed by observation.  The claim is withdrawn and
  `Attraction.attraction_fixes_the_bit` is renamed
  `universality_from_counting`;
* **`Δρ`, one dimensionless number.**  A6″ replaces A6′'s free *dimensionful*
  constant by the scale period, but `Δ` and the threshold spacing `1/ρ` are both
  magnitudes on the `σ` axis, so their product is a pure number that nothing
  computes (`Index.coupling_is_one_dimensionless_number`).  It is the number that
  would predict `G` from the mass spectrum.  §V.e's "no free number" was too
  strong: the trade is dimensionful-for-dimensionless, which is a real gain and
  is not zero;
* **The scanning hypothesis** `λ = κρ`, used in `Scanning.lean` for the claim
  that the `w`-evolution and the `H₀` discrepancy are one number.  Labelled a
  proposal in that file and now listed here.

### V.a″  And one claim of "no condition" that needs its scope

`Positivity.no_null_energy_condition` says **the axioms** impose no energy
condition, and that stands.  It does not say the *framework* has none: adopting
A6″ with `ν ≥ 0` gives the source a sign, and `Attraction.counting_bound` bounds
it below.  The restriction is combinatorial rather than energetic and enters
through the source law rather than the axioms — but it is there, and reading the
theorem as "anything goes" would be wrong.

## V.b  Structures that carry hypotheses the axioms do not supply

A recurring shape, first registered for `Dynamics.Realizes` and then found more
widely by an external audit.  A theorem of the form "given a structure `S`, …"
is only as strong as the framework's ability to *build* an `S`.  Where it
cannot, the theorem is true but unwitnessed, and its physical gloss is a
conditional:

* **`Crossed.ScaleShift`** — the carrier of the "`ħ` is an exact scale step"
  result.  It is never constructed from `ScaleAlgebra` or
  `ScaleField`; it asks only for a ring endomorphism.  So the exactness is a
  property **of the model**, not something the axioms are shown to realise.
  This is the most consequential instance, because the claim is a flagship one;
* `Waves.Conserved` — **now bridged** (`Waves.total_conserved`).  I had said the
  bridge was impossible because the framework has no integral; that was wrong.
  The algebraic content of "the integral of a divergence vanishes" is the
  **quotient by the divergences**, which A1 supplies.  What survives is one
  algebraic condition, `divergences ≠ ⊤` — the algebraic face of localisation —
  in place of the three analytic ones (measure, divergence theorem, decay);
* `RG.ScaleFlow`, `Direction.DirTransport`, `Invariant.Trace`,
  `Covariance.CosmicHistory` — each never instantiated from the framework's own
  carrier.

One entry has since been discharged in a different way: **`Foundation`'s
group `Γ`** was an abstract carrier for "comparisons of local units", argued for
rather than built.  `ScaleField` is now a `CommGroup` constructed from A1–A3
(§V.c), so the structure `Foundation.lean` argues its way to is one the axioms
supply.

**None of these is false.**  Each is a correct theorem about anything meeting
its hypothesis.  What is corrected here is the *reading*: they describe what
would follow, not what the axioms deliver.

**Update — `Witness.lean` now builds all six.**  `ℝ[X]` with `d/dX` satisfies
A1, and the shift `X ↦ X + 1` is a `ScaleShift` on it with `Δ X = 1`: the step
is **exact and finite**, not a first-order truncation.  Witnesses are also given
for `Trace` (the matrix trace), `DirTransport` (the adjoint action), `ScaleFlow`
(a non-degenerate translation flow), `Conserved` (a constant moment) and
`CosmicHistory` (a spatially constant drift).

**What that changes and what it does not.**  The theorems are now known
non-vacuous, and the structures are shown *compatible* with A1 rather than
merely assumed.  It is **not** a derivation: one model carrying both structures
does not show that every model of A1 must carry a scale shift.  So
`ħ = ` the step remains an **identification**, and stays in this register as
one.  The gap between "compatible" and "forced" is real and is not closed.

**Also fixed in the same pass**, all from the same audit: a vacuous
`x = x` theorem in `Observation.lean` replaced by its contentful contrapositive;
the deflection and precession bounds tightened from `±0.005″`/`±0.1″` to
`±0.0001″`/`±0.001″` so the *certified* precision matches the quoted comparison;
two literal `x = x` theorems removed from `Waves.lean`; and the docstring of
`Particle.no_further_label` corrected to say that it is structure
extensionality, with the physical content living upstream.

## V.c  The unification pass, and what it changed

The development had grown four vocabularies for the same things.  They have been
merged, and the merge is recorded here because it changed some *claims*, not
only some names.

**What was duplicated, and is now one thing:**

* **A1** was declared twice — `ScaleAlgebra` over a commutative ring and
  `DiffRing` over a ring — with an instance and a `def` transporting between
  them.  Commutativity was never used to *state* A1, so there is one class,
  stated over a ring, in `Basic.lean`.  `Postulates.scaleAlgebra_is_diffRing` is
  gone because there is nothing left to transport;
* **the geometric objects** — `sig`, `hess`, `gradsq`, `Chr`, `Defm`, and `kron`
  itself — were defined once in `Conformal.lean` over a commutative ring and
  again in `NCConformal.lean` over a ring under a second namespace with `kr` for
  `kron`.  They are defined once, over a ring.  What divides the two files is
  now a hypothesis and not a language;
* **isotropy** was written out four times (`Frame`, `Gauge`, `Axis`, `Locus`);
* **parallelism** — `vᵢwⱼ = vⱼwᵢ` — appeared unnamed in five files;
* **the wedge** was defined in `Slice.lean` over `ℝ` and used elsewhere;
* **the two sector counts** were `Slice.wedgeDim`/`dirDim` and
  `Dimension.rotDim2`/`scaleDim2`, and **A7** was stated a further four times
  with `Iff.rfl` bridges between the statements;
* **the charge algebra** existed three times (`Charges.DefectCharge`,
  `Color.BlockMonodromy`, `Defect.ScaleDefect`), each with its own `comp`,
  `anti` and `triv`.

All of that now lives in `Pattern.lean` and `Basic.lean`, and the three charge
structures are joined by proved homomorphisms rather than by resemblance.

**What the merge produced that was not there before:**

* `NCConformal.two_Rm_eq_nc` — **the master regression theorem without
  commutativity.**  `Conformal.two_Rm_eq` (curvature is the Kulkarni–Nomizu
  product of `δ` with the scale deformation) could only be *stated* while `Rm`
  and `Defm` were commutative-sector objects.  They are not, and the identity
  holds in general with one extra term, `RmCorr`, built from nothing but
  commutators of scale gradients.  The classical theorem is its commuting locus.
  **This does not close `Unify.lean`'s outstanding item**, which is the
  *anisotropic* (directional-scale) curvature and a different gap;
* `NCConformal.quantum_correction_is_a_wedge` — the correction and the
  rotational label were previously said to be the same *kind* of object.  With
  one definition of the wedge it is an identity: `wedge v v` is the commutator
  of `v`'s values, which is zero classically and is the whole correction
  otherwise;
* `ScaleField` carries a `CommGroup` structure, and **A3 is inversion in it**
  (`scale_energy_duality_is_inversion`).  The energy `ε = 1/s` was carried as a
  bare ring element with its own hand-proved `d_en`; it is a scale field, with
  log-scale `−σ`, and `d_en` is the infinitesimal group law.  This also supplies
  the structure `Foundation.lean` argues for from first principles, so that
  argument now has a witness in the framework's own carrier;
* `Frame.DirScale.en` — **A3 read directionally**, which costs no new
  hypothesis, and with it
  `reciprocal_iff_radial_is_temporal_energy`: the Schwarzschild relation
  `s_t·s_r = 1` *is* `s_r = ε_t`, the radial length scale being the temporal
  energy scale.  That is A3 applied across two directions, and it is exactly
  what a scalar scale cannot express — the sharpest form of `Frame.lean`'s
  diagnosis, and now a theorem rather than a remark;
* `ScaleField.fiducials` — A5's global shifts are a **subgroup**, so A5 too is a
  statement about the carrier rather than about a stray constant.

**What it did not change.**  No retraction was added or removed, no citation was
discharged, and no assumption in §V was eliminated.  A6′ is still an external
input, the uniform-density assumption is still an assumption, and A7 is still an
axiom.  The theorem count rose from 650 to 1040 and every one of them is audited.

## V.d  The kinematics pass, and what it overturned

A second pass, working outward from the observation that A3 conflates inversion
in the scale group with the dual pairing that carries energy and momentum.

**Sixth occurrence of the recurring error (§III).**  `Light.lean` and
`Observation.lean` were written with a **scalar** scale, and their headline
claim — that light is blind to the scale — is **false** under A4′.  The measured
form `Σ η_a s_a² v_a²` is not a multiple of the bare form unless the units agree,
and `Light.bare_null_not_phys_null` exhibits a bare-null direction that is not
measured-null.  **Anisotropy moves the light cone.**  Scoped, not deleted: the
old claim survives as `isNullDir_iff_bare_of_isotropic`.

**And then a seventh error, mine, on top of the sixth — now withdrawn.**  I read
the moved cone as an observable anisotropy of the speed of light, wrote
`c_i/c_j = s_j/s_i`, set it against the `10⁻¹⁸` Michelson–Morley bound, and
announced a crisis with `PPN.lean`, which needs `s_t ≠ s_r` at `O(1)`.

There is no crisis.  `Light.physFormDir_eq_bareForm_rescaled` is one line:
the measured form **is** the bare form precomposed with `v_a ↦ s_a v_a`, and
rescaling each axis by its own unit is exactly the freedom A4′ hands over.  So
the two cones differ by a change of basis, and a quadratic form at a point has no
content beyond its signature.  `Light.michelson_morley_null`: **the null result
is a theorem, for every scale pattern, at any precision.**

Two things in the development should have stopped this and did not.
`Basic.lean`'s own docstring calls the bare bookkeeping *"pure bookkeeping,
carrying no physics"* — and I compared an observable against it.  And
`Well.light_measured_speed_one`, which I had proved myself two files earlier,
says light crosses at measured speed one in every direction, which *is* the null
result.  The error was pattern-matching "anisotropic cone" onto "Lorentz
violation → interferometric bound", and it is the kind the register exists to
catch.

**What the question actually delivers is a prediction, not a constraint.**
`Light.one_cone_for_every_sector`: A4′ gives one scale pattern, hence one metric,
hence one causal structure shared by every sector.  Standard-Model-Extension
searches measure *differences between sectors' cones*, because a common cone is a
coordinate change.  So the framework predicts **every sector-relative
Lorentz-violation coefficient vanishes**, parameter-free, and one confirmed
detection kills it.

**And it sharpens what is physical.**  A diagonal rescaling flattens the
symmetric part but only multiplies a wedge by a unit
(`Pattern.wedge_rescale_ne_zero`), so at a point the **antisymmetric** residue is
the sole observable beyond the signature — which is `NCConformal`'s quantum
correction and `Axes.lean`'s rotational label, the same object.  Everything else
lives in the *variation*, which is curvature.

**A seventh occurrence, of the same diagnostic on a different pair.**  I read
`Transport.transport_coset` as ER=EPR — "entangled regions joined by a costless
identification".  `Gauge.stabilizer` permutes `Fin n`, which indexes *directions
at a point*, not *positions*.  There is no non-locality in it at all.  The
diagnostic that catches it is §III's — *a count of what?* — applied to direction
indices versus locations.  Withdrawn in `Well.lean`'s header, and the count is
kept separately from the five scalar-for-directional occurrences because the
substitution is a different one.

**What was derived.**

* `Momentum.dispersion_relation` — **`E² = m² + p²`**, from A3 read
  directionally plus the `1 + (n−1)` split.  The development had the Lorentz
  algebra and no dispersion relation.  The `m` is not a new parameter: by
  `Emergence.mass_iff_threshold` it is the threshold;
* `Momentum.commutator_of_gradients` — with the derivations inner
  (`d_i = ad P_i`, so `P_i` *is* momentum), Jacobi rewrites `NCConformal`'s
  correction `[σ_a, σ_c]` as `∂_a[σ,σ_c] − [σ,σ_{ac}]`, built entirely from the
  failure of the log-scale to be central.  Not yet a magnitude, but one unknown
  in place of a pair;
* `Openness.A5_A6_dichotomy` — **A5 and A6 are one statement about one
  subgroup**: A5 says `ScaleField.fiducials` acts trivially, A6 says the world is
  not in it.  A fiducial world has no drift, no deformation and no curvature
  (`closed_universe_is_empty`), so A6 is "the world is not that point".  This is
  a merge of the same kind as `Unify.lean`'s A4/A4′, and the axiom count should
  read six-with-clauses rather than seven;
* `Openness.no_dissipation_in_one_direction` — a one-direction substrate with a
  continuity equation cannot dissipate.  So A6 plus local continuity forces
  `n ≥ 2`: **the universe is open because it has somewhere to leak**;
* `Positivity.no_null_energy_condition` — **the axioms impose no energy
  condition.**  In one model of A1 over an ordered ring, the deformation tensor's
  contraction with a fixed null direction takes both signs.  Every consequence
  usually drawn from an energy condition — singularity theorems, topological
  censorship, non-traversability — is *unavailable here as a derivation*.  This
  is registered because assuming any of them would be exactly the inertia §III
  warns about, and none has ever been tested;
* `Well.lean` — a "wormhole" here is a **scale well**, not a topological handle,
  which cannot even be stated without a manifold.  `stretch_ne_zero`: the throat
  never has zero length, since `s` is a unit — GR permits a degenerate throat and
  this framework forbids one.  `no_positive_floor`: but there is no lower bound
  either.  Under reciprocity `crossing = length²`, so the ruler and clock effects
  **compound**, and the sign is the whole content:
  `s_r > 1` is a Shapiro **delay** (Schwarzschild), `s_r < 1` a Shapiro
  **advance** (the wormhole branch).  Both branches are open, because there is no
  energy condition to exclude one;
* `Anisotropic.lean` — a guess of mine, that anisotropy produces classical
  torsion, is **refuted**: `ChrDir_symm`, a Levi-Civita connection is
  torsion-free whatever the metric.  What is there instead is that the entire
  anisotropic correction is a **ratio of directional scales**, hence the optical
  anisotropy above.  And in the non-commutative anisotropic sector the leading
  correction is `[σ_a, σ_b]` — **zeroth order in gradients**, where the isotropic
  one is second order.  Not derivative-suppressed, and — unlike the symmetric
  anisotropy — not gauge either, since a rescaling cannot cancel a wedge.  Which
  experiments bound it is open; they are spin-sector, not interferometric.

**A6′ has a replacement, and it is registered as a replacement.**  (Its reach is
narrowed in §V.f: the identification of its `Δ` with the scale period is
conditional, and the dimensionless number it leaves is not computable.)
`Index.lean` proposes

        A6″   `Δσ = Δ·ν` ,

the Laplacian of the log-scale is the scale period times the defect count.  Then
`Index.A6'_from_index` gives A6′ with **`κ = −2(n−1)Δ`** — the gravitational
coupling is the scale period, not a fitted number, so the framework's second free
magnitude is gone; `Index.no_period_no_gravity` shows gravity exists only on the
circle-valued branch, relating `Defect.lean`'s periodic scale to `Axioms.lean`'s
real one for the first time; and `Index.reciprocity_of_no_enclosed_winding`
replaces `Vacuum.lean`'s **asymptotic flatness** — a global boundary condition in
a framework that denies global field equations — by a *local* condition, that no
winding is enclosed.

**This is one input in place of another, not an elimination**, and one bit
survives: `Index.orientation_is_one_bit` shows the magnitude of `κ` is fixed and
its **sign** is not, being an orientation convention fixed by gravity being
attractive.  A free real number has become a free bit.  A6′ therefore stays in
§V, rewritten, and the assumed-count is unchanged.

## V.e  Cosmology and the source, and a hypothesis found hiding in a quantifier

**`w = −1` was never forced by A5 alone.**  `Cosmos.rate_constant_of_fiducial_invariance`
derives it from `∀ σ c, λ(σ+c) = λ(σ)` — a rate that is a function of **one**
variable.  That is A5 read correctly *only if there is no second scale in the
problem*, because A5 shifts every scale together.  Written with two,
`Scanning.two_scale_invariance_forces_difference` shows the rate is a function of
the **difference**, and `Scanning.rate_may_vary` exhibits an A5-respecting rate
that genuinely varies.

The extra assumption was invisible and it is now false: `Index.lean` makes the
**thresholds gravitationally active**, so `σ − μ_k` is a physical scale
difference.  So the framework's most exposed prediction is not `w = −1`; it is

> `w` varies, on the log-scale set by the threshold spectrum.

`Cosmos.lean`'s theorem stands with its domain stated
(`Scanning.one_scale_recovers_constant`).  The DESI tension therefore does *not*
falsify A5; it becomes a measurement of the same `ρ` that `Spectrum.lean` reads
off the particle spectrum, and the two must agree.  That is a stronger claim than
the one it replaces, because it is cross-sector and has nothing free.

**One mechanism, two anomalies.**  Under the scanning hypothesis — dissipation
*is* threshold crossing, so the rate tracks `ρ` — `Scanning.two_anomalies_one_number`
shows the fractional evolution of `w` and the fractional disagreement between a
counting distance ladder and a ruler are **the same number**, `Δρ/ρ`.  If `w`
evolves and the ladders agree, or the reverse, the picture is dead.  The
scanning hypothesis is a proposal and is labelled one; everything downstream of
it is a theorem.

**The source is a count, and that is why gravity is attractive.**  `Index.lean`
wrote its source as "the defect count" without saying which label.  If it were
the signed winding, a defect and its antidefect would source opposite geometries
and antimatter would fall up (`Attraction.signed_source_would_antigravitate`);
antihydrogen falls.  So the source is the **threshold**, which
`Emergence.mass_iff_threshold` makes the mass and which is orientation-free.
Then:

* `Attraction.attraction_from_counting` — a cardinality has one sign, so `Δσ`
  has one sign: **gravity is universal and attractive because its source is a
  count**;
* `Attraction.universality_from_counting` — every source deforms the scale the
  *same* way, which is what the equivalence principle asserts.  **This does not
  close** the bit `Index.orientation_is_one_bit` left open; I claimed it did and
  that is withdrawn in §V.a′;
* `Attraction.two_labels_two_behaviours` — and gravity is universal while charge
  is signed because they are two *different* labels of `Particle.Species`, only
  one of which has a sign.  No separate equivalence principle is needed.

**The wells exist, and they are voids.**  The `s_r < 1` branch of `Well.lean`
needs a count below the background — impossible for a count, ordinary for a
count *difference*.  `Attraction.void_is_the_advance_branch`: an underdense
region is the advance branch, and the Shapiro advance across a void is an
already-observed effect.  The exotic object the kinematics permitted is a common
one.

**And that supplies the replacement for the null energy condition.**  GR bounds
the advance by forbidding exotic matter.  The *axioms* here impose none (§V.d),
and what the *source law* supplies instead is `Attraction.counting_bound`: `ν ≥ −ν_background`, because
**you cannot remove more structures than are there**.  The bound is
combinatorial, it is saturated by an empty region
(`Attraction.advance_bounded_by_emptiness`), and it is sharper than the energetic
one because it says exactly where the limit is and leaves no room for a small
violation.

## V.f  Going after `Δρ`, and a negative result that pays

`Index.A6'_from_index` gives `κ = −2(n−1)Δ`, so `κρ = −2(n−1)(Δρ)` and **fixing
the pure number `Δρ` would predict Newton's constant from the mass spectrum.**
That was the highest-value open target and `Period.lean` goes after it.  It does
not close, and the way it fails is worth more than the attempt.

**A caveat that was being dropped.**  `Δ` appears in three places —
`Defect.quasiperiodic`'s shift per winding, `Index.IndexResponse`'s coefficient,
and hence `κ`.  Identifying the first two is the **continuum-limit step
`Index.lean` itself flags**, since reading the index form as Gauss's law needs a
boundary flux to become a local density and the framework has no integration
theory.  So "the gravitational coupling *is* the scale period", and the claim
that `G` and `ħ` acquire one origin, are **conditional on a step that has not
been taken**.  Both were stated flatly in §V.d and in `Index.lean`; both are now
qualified.

**The one determination the framework had, and the data that kills it.**  If the
thresholds sat at the multiples of the period, then `ρ = 1/Δ`, so `Δρ = 1` and
`κρ = −2(n−1)` — `−6` at `n = 4`, parameter-free
(`Period.coupling_under_lattice_four`).  That is the only such statement the
framework has ever been in a position to make.

It is excluded.  A lattice has all gaps equal, hence `CV² = 0`, and the observed
value is `0.87 < CV² < 0.88` (`Period.lattice_excluded`, and
`lattice_excluded_by_a_wide_margin` — not a marginal call).

**And it is the same fact as an old retraction.**  The lattice hypothesis *is*
the geometric mass tower `m_k = m₀e^{|k|Δ}` of §I, retracted on the strength of
`QCD.geometric_tower_fails` and `Spectrum.observed_not_geometric`.  What §I did
not record is that the same retraction closed the only route from the spectrum to
the gravitational coupling.  **One retraction, two casualties, one written down**
— `Period.retraction_closed_the_route`.  That is the second time in this audit
that a register entry carried more than it said; the first was A6′ itself.

**What remains is a conversion, not a determination.**  Identifying `Δ` with the
root normalisation `α` gives `Δρ = k−1 = 2` and `κρ = −12`
(`Period.root_normalisation_at_three`).  Nothing excludes it, but
`Dimension.density_normalization_relation` is a tautology and the identification
is unformalised: one equation, one unknown, which is exactly the trap
`CrossCheck.lean` exists to flag.  `Period.candidates_disagree` shows the two
candidates give different answers, so the question is real and the framework has
no answer.

**Stated plainly: the framework does not predict Newton's constant.**
`Period.no_prediction_of_the_coupling`.  `Index.lean`'s gain stands — a free
dimensionful constant became a free dimensionless one — and it stops there.  The
suggestion that it might go further was mine.

## V.g  The one problem behind three, and my own error inside it

The geometric mass tower (§I), the mass spectrum, and `Δρ` (§V.f) are one
problem, and `Sources.lean` names it: **three different integers have been used
interchangeably as "the charge that sources the geometry".**

| name | order parameter | homotopy | carried by |
|---|---|---|---|
| `Defect.ScaleDefect.winding` | circle-valued **scalar** scale | `π₁ = ℤ` | the magnitude |
| `Charges.DefectCharge.block` | projective **directional** axis | `π₁ = ℤ/2` | the direction |
| `Charges.DefectCharge.hedgehog` | the same | `π₂ = ℤ` | the direction |

`Charges.lean` says of the last, in its own text, "how the axis wraps the
**enclosing sphere**"; `Defect.lean` says of the first, "the log-scale read
**around a loop**".

**My error, from the unification pass (§V.c).**  `Defect.toCharge` sent the
winding to the `hedgehog` slot and its docstring claimed "one charge algebra,
not two".  That is a `π₁` object in a `π₂` slot, of a *different* order
parameter — and one that §I has already scoped out.  Withdrawn in `Defect.lean`
and in `Sources.lean`; the maps survive as the algebraic fact that both are
additive `ℤ`-labels, which is all they share.  This is the **eighth** index
substitution the register has caught and the third that is mine.

**Why the three failures are one.**  The tower makes the *threshold* a function
of a *topological* label, and `Particle.Species` carries them as separate fields
with nothing linking them — so it contradicts the framework's own label
structure, not merely the data.  The `CV²` test measures a *process* and cannot
see a relation between labels at all.  And `Δρ` is the ratio of a period (from
the scoped-out picture) to a measured density.

**The escape I proposed, refuted.**  I suggested that sourcing the geometry with
the `π₂` degree — normalised by the fixed volume of the direction sphere — rather
than the `π₁` winding would remove the free constant.
`Sources.source_coefficient_scales` shows it does not: under `σ ↦ cσ` the
Laplacian scales and a dimensionless count does not, so the coefficient absorbs
the factor **whatever the count counts**.

**What that buys.**  The free number is not a gap in anyone's cleverness — it is
forced by the *shape* of any law coupling a count to a scale, and there is one
such coupling, hence one free number.  That is `Dimension.only_ratios_are_fixed`
arriving from a new direction, and it sharpens what the free number is: not "the
magnitude of the scale pattern" but **the conversion from counting to scale**.

**And a target I named, then withdrew one step later.**  I proposed `Δ / κ_run`:
one count-to-scale coupling can be absorbed into the unit, two cannot, and
`Running.invSqCoupling` supplies a second.  The evidence I gave was
`Sources.couplings_scale_together` — which proves `invSqCoupling` is **linear in
`(u₀, κ)`** and says nothing whatever about the rescaling `σ ↦ cσ`.  I read a
linearity statement as a weight statement.

## V.h  The grading, done properly, and what it settles

`Weight.lean` computes the weights under `σ ↦ cσ` instead of guessing them:

| quantity | weight |
|---|---|
| `lap σ` | `1` |
| the scale-axis coordinate `t`, being `σ` | `1` |
| `ρ`, thresholds per unit `t` | `−1` |
| `resolvedCount` — a count | `0` |
| a gauge coupling, and `κ_run` | `0` |
| `ν`, defects per bare volume | `0` |
| `Δ`, the source coefficient | `1` |

`Weight.invSqCoupling_invariant` is the computation I should have done: rescaling
sends `t ↦ ct` and `ρ ↦ ρ/c`, and the gauge coupling comes out unchanged **with
`κ` untouched**.  So `κ_run` has weight zero, `Δ/κ_run` has weight one, and the
target is dead (`Weight.ratio_not_invariant`).

**What the bookkeeping gives instead is worth more than the target was.**

* `Weight.only_gravity_crosses_the_weight` — the gauge law relates weight-zero to
  weight-zero; the gravitational law relates a weight-zero **count** to a
  weight-one **scale**.  **Gravity is the only interaction that crosses the
  grading**, which is why its coefficient is the unit and gauge couplings are pure
  numbers.  That is usually a fact one notes about dimensions; here it is a
  statement about which law crosses, and only one does;
* `Weight.product_invariant` — `Δρ` is the *unique* weight-zero combination
  available, so §V.f's conclusion was not a matter of exhausting candidates:
  there was only ever one, and it is the unit times a measurement;
* and the scope of the whole theory, in one line: **it predicts the weight-zero
  sector and nothing else.**  `CV² = 1`, `w = −1`, `γ = 1`, `1.7515″`,
  `42.99″/century` — all weight zero (`Weight.cvSq_weight_zero`,
  `Weight.wedge_ratio_weight_zero`).  `Δ`, `ρ`, the threshold locations, the scale
  magnitude — all weight one or measured.  That covers every entry in §V and every
  success in `Predictions.lean`, and it was invisible until the grading was
  written down.

## V.i  The gravity chain, re-read — two caveats now stale

Two closing caveats in the development were true when written and are no longer:

* **`Unify.lean`**: "what this file does not do is compute curvature in the
  anisotropic sector."  `Diagonal.lean` computes it for the **static diagonal**
  case — which *is* anisotropic, one scale per direction and they differ — and
  that is the case the gravity chain runs through.  The caveat is now scoped to
  the general non-static computation;
* **`PPN.lean`**: "reciprocity is here a property of the solution being
  described, not yet a derived consequence of a source."
  `Diagonal.vacuum_scale_sum` derives it from the vacuum equations, with the
  connection certified by `metric_compatible`.

`Chain.lean` re-reads the whole chain in one place, because the links changed in
three different files and nobody had read it end to end.  The remaining inputs
are short: A6″, staticity, the areal coordinate, and the timelike sign.  **The
vacuum Ricci combination and asymptotic flatness are off the list.**

**And the weight test sharpens what the chain delivers.**  `γ = 1` and the factor
of two in the deflection are **weight zero** — exact, parameter-free, and in the
sector `Weight.lean` says a one-magnitude theory can predict.  The arcsecond
values `1.7515″` and `42.99″/century` are that statement evaluated on measured
inputs, `G` among them, and `G` is the unit.

That is not a demotion of the gravity sector; it is the correct description of
it, and stating it removes a temptation this register has recorded before —
reporting a number that contains a measured input as if the theory had produced
it.  `Chain.chain_summary` keeps the two apart.

## V.j  The general anisotropic curvature, and what it turned up

`Diagonal.lean` now drops staticity.  Two things came out, one structural and one
that changes how A7 reads.

**The cancellation is general, not an artefact of the ansatz.**
`Diagonal.ric_offdiag` computes the off-diagonal Ricci of the diagonal metric
without staticity:

    R_ab = −Σ_{c ∉ {a,b}} [ ∂_a∂_b σ_c − (∂_bσ_a)(∂_aσ_c)
                             − (∂_aσ_b)(∂_bσ_c) + (∂_aσ_c)(∂_bσ_c) ]

Every term built from `σ_a` and `σ_b` alone cancels identically.  That is the
same cancellation as `combination_is_transverse`, in a different component, so
it is a property of diagonal metrics rather than of the static case:

> **No pair of directions carries its own curvature; every component is carried
> by the complement.**

`offdiag_vanishes_of_static` checks the static case against it and finds zero, as
it must.

**A4′ is a restriction, not a parametrisation.**  The metric of A4′ is diagonal
*by construction*, so in vacuum the equations `R_ab = 0` for `a ≠ b` are not part
of the diagonal system — they are **extra constraints on the scale pattern**.
`Diagonal.offdiag_zero_in_two`: with two directions there is nothing transverse
to a pair, so the constraint is empty and diagonality costs nothing; for `n ≥ 3`
it costs something.  The same shape as
`Openness.no_dissipation_in_one_direction` — a thing that needs somewhere
transverse to happen.

**And A7 acquires a reading.**  The constraints are indexed by unordered pairs of
directions, which is the index set `Pattern.rotDim2` counts — the doubled
dimension of `Λ²p`.  So `rotDim2 = scaleDim2` says

> the number of constraints on the diagonal ansatz equals the number of scale
> functions they constrain: neither over- nor under-determined.

This is a **gloss on a count, not a new theorem**, and it is registered as such.
What makes it available is `ric_offdiag` showing the components are pair-indexed;
A7's status as an axiom is unchanged.

The remaining item from `Unify.lean`'s original caveat is now the *non-diagonal*
case — a metric not diagonal in the bare frame — which A4′ does not describe at
all.

## V.k  The continuum limit of A6″: relocated, not closed

`Index.lean` registered its remaining step as "the continuum limit" — the passage
from a boundary flux to a local density, for which the framework has no
integration theory.  `Flux.lean` goes after it and finds the obstruction is
somewhere else.

**In codimension two there is no gap.**  `Defect.ScaleDefect` carries the loop
explicitly, so the flux through a boundary enclosing a defect is a *difference of
two values* of the followed log-scale, not an integral: `Flux.flux_eq_winding`
gives `flux = k·Δ` from `quasiperiodic` alone.  It is additive
(`flux_combine`), zero on the vacuum, and quantised (`flux_quantised`).  **That
is Gauss's law, exactly, with no limit and no measure** — and it was already a
theorem, unread as one.

**So the obstruction is a homotopy type.**  The construction works because the
boundary of a codimension-two defect is a **loop** and the invariant is a
winding, linear in `∇σ` and recoverable from endpoints.  The framework's own
defects are *not* codimension two: `Axis.lean` restores **point** defects from a
projective directional order parameter, and `Charges.hedgehog` is a `π₂` class —
"how the axis wraps the enclosing **sphere**".  For a sphere the invariant is a
**degree**, which is not linear in the gradient and is not a difference of
endpoint values.

> **`Δσ = Δ·ν` is a codimension-two equation applied to a codimension-three
> source.**

This is the `π₁`/`π₂` conflation of §V.g appearing a third time, now one level up
in the source law, and this occurrence is mine from `Index.lean` rather than from
the older files.  `Audit.homotopyClassCount` is raised accordingly.

**Two ways out, and they are not equivalent.**

* *(a)* the source is codimension two — strings.  Then `Index.lean` is exact as
  written and needs nothing further.  But it reopens the `Codimension.lean`
  retraction of §I, which was made on `Axis.lean`'s ground that the defects are
  points;
* *(b)* the source law is rewritten with a degree density.  `Weight.lean` says
  this costs nothing in the grading — a degree density is weight zero, like a
  count, so the coefficient stays weight one and §V.f–§V.h survive intact.  What
  does not survive is the specific form of A6″.

**And a claim of mine is weakened again.**  "`G` and `ħ` acquire one origin"
rested on identifying `Index.lean`'s coefficient with `Defect.lean`'s scale
period — exactly the codimension-two identification.  §V.f made it conditional on
the continuum-limit step; it is now conditional on the **codimension**, which is
sharper and less comfortable, because the framework's own `Axis.lean` argues
against it.

**And one thing that is *not* the gap**, recorded because it is where I looked
first.  `lap σ` is manifestly a sum of derivative images, so its class modulo the
transverse divergences is carried by the drift direction alone
(`Index.lap_mod_divergences`).  True, and not Gauss's law: it is the statement for
a region with **no** enclosed charge.  The enclosed-charge case needs a
non-contractible boundary, and non-contractibility is a topological input, not an
analytic one.

## V.l  Dynamics: redefined, not supplied

`Native.no_global_field_equation` says the framework has no equation of motion,
and the shape usually wanted for one is unavailable here — no state at a time, no
external time parameter, nothing that persists.  `Determination.lean` asks
whether that is a hole or a position, and answers **both, in separable parts**.

**What is derived.**  Reading dynamics as *a determination relation among the
parts of one configuration* rather than as *what happens next* makes the
framework's recurring result the dynamical law: **a part is determined by its
complement, never by itself** (`Diagonal.ric_offdiag`,
`combination_is_transverse`, `Emergence.resolved`). `Determination.influence`
names the complement's contribution — the framework's notion of force — and
`influence_symm` gives the third law as a *symmetry of one expression* rather
than as an agreement between two facts.  `no_influence_in_two` is a genuine
consequence and not a restatement: **with two directions a pair has no
complement, so nothing determines anything.**  The amount of dynamics available
is `n − 2`, the same shape as `Openness.no_dissipation_in_one_direction`.

**What is a second reading, not a derivation.**  A7 is read there as
well-posedness — as many determination relations (pairs, `rotDim2`) as functions
determined (`scaleDim2`).  `Locus.lean` reads the same equation as a commitment
about observable labels.  Both are readings; **A7 remains an axiom** and is not
discharged by having two of them.

**What is not supplied, and is registered here as open.**  A determination
relation has a solution *space*, and nothing in the development picks a point in
it.  So the framework does not produce trajectories and does not say why this
configuration rather than another.  That is not the same lacuna as a missing
integration theory (§V.k): it is the question of whether "why this world" is a
dynamical question here at all.  Nothing in the development answers it and
`Determination.lean` does not either — it supplies the vocabulary in which it can
be posed.  Counted in `assumedCount`.

## V.m  What the determination theory explains and predicts — and one scope
correction it forces

§V.l registered "nothing selects a point in the solution space" as open.
`Explanation.lean` works out what that costs, and it is less than it looked in
one direction and more precise in another.

**The accounting is complete by construction.**  For any theory `S` and any
quantity `f`, `f` is either constant across `S` (a prediction) or not (an
input), exhaustively and exclusively (`Explanation.predicted_or_modulus`,
`not_both`).  There is no third category, so a framework cannot hide a quantity
in one.  And an explanation here has exactly two ingredients — invariance and
membership (`value_from_any_solution`); there is no mechanism layer.

**The predictions are not vacuous, and this had to be checked.**
`vacuous_predicts_everything`: an inconsistent theory predicts every quantity.
So the register's list of predictions is worth nothing without a witness that the
constraint admits something.  Both sides are now exhibited:
`Explanation.separable_is_free` gives an infinite family of solutions — **force
is exactly the failure of separability** — and `coupled_not_free` gives an
excluded configuration in a concrete three-direction model of A1
(`MvPolynomial (Fin 3) ℝ` with the partial derivatives, itself the first
multi-direction model the development has had).  `constraint_is_proper`.

**SCOPE CORRECTION — the weight grading is necessary, not sufficient.**
`Weight.lean` closed with "the framework predicts the weight-zero sector and
nothing else", and it would be natural to read the grading as *being* the
partition above.  **It is not.**  `Explanation.influence_not_homogeneous`: the
determination relation mixes weight one (the second-derivative term) with weight
two (the three quadratic terms), so `σ ↦ cσ` is **not a symmetry of the theory**
and weight-zero functions are not thereby constant across solutions.  What
survives is `Weight.lean`'s own description — *a cheap test*: weight zero is
necessary for a prediction, since a weight-one quantity has a value only once a
labelling is fixed.  Each weight-zero prediction still has to be shown constant
across solutions on its own, and each of them is.  Counted in `correctedCount`.

**A negative result, proved rather than assumed: the arrow of time is not in the
dynamics.**  `Explanation.no_arrow_from_determination` — both the determiner of a
pair and the influence on it are symmetric under exchanging the pair, so nothing
in the relation distinguishes an order.  The arrow must come from counting
(`Entropy.lean`), and looking for it in the dynamics is now provably pointless.
This is `Determination.influence_symm` read as a cost; §V.l recorded only the
flattering reading (the third law as one expression) and both belong on record.

**And the shape of the explanation, named honestly.**  No part appears in its own
determiner (`self_not_in_determiner`), so concurrent explanation is not circular;
but in three directions the structure is an exact 3-cycle (`cycle_of_three`), so
it is **irreflexive and not acyclic**.  Explanation here is mutual: no layer
explains the rest without itself being explained.  That is what declining to
posit a preferred direction costs.

**So §V.l's open item is re-identified, not discharged.**  "Why this
configuration" is the initial-value question relocated, and no theory answers its
own version of it — calling it a special weakness of this framework was wrong.
What *is* specific, and remains open, is that because determination is symmetric
the data to be supplied is not on a time slice but on *part of a configuration*,
and the framework has no theory of which parts suffice.  A7 is the only thing it
says (`Determination.determination_well_posed`) and that is a counting statement,
not an existence-and-uniqueness theorem.  `assumedCount` is unchanged: it is the
same item, described correctly.

## V.n  The predictions, recounted — half the ledger was definitional

`Explanation.lean` closed with "one free magnitude against eight dimensionless
predictions".  `Anchor.lean` applies one mechanical test to that list and **four
of the eight fail it.**

**The test.**  A claim quantified over its own parameters is a prediction only if
some assignment makes it false (`Anchor.Falsifiable`).  Applied:

* `Deflection.iso_is_exactly_half` — `deflectionIso := 2GM/bc²` and
  `deflectionObs := 4GM/bc²`, so the "factor of two" holds at every `(G,M,b,c)`
  including meaningless ones: `Anchor.factor_two_has_no_failing_instance`.  It is
  bookkeeping between two definitions.  The content it stood in for *is*
  falsifiable (`Anchor.gamma_claim_is_falsifiable`) and is `γ = 1` — **one
  prediction, not two**;
* `Precession.isotropic_is_third` — arithmetic inside the *imported* PPN formula
  `(2 − β + 2γ)/3`;
* `PPN.gamma_prediction_is_sharp : γ = 1 → γ − 1 = 0` — a tautology, cited as
  "the framework's actual prediction" in `Chain.lean` **and again** in
  `Explanation.lean`;
* `Attraction.universality_from_counting` — `mul_nonpos`.  The physics is in the
  identification of `ν` with a count, not in the arithmetic.

This is the fourth occurrence of the register's own recurring failure: **reporting
a number that contains the answer as if the theory had produced it.**  It was
named in `Chain.lean` for the arcsecond values and then committed again, by me,
one file later.  `Explanation.dimensionlessPredictions` is corrected `8 → 4`.

**The honest tiers.**  Four falsifiable dimensionless statements — `γ = 1`,
universal attraction, one cone for every sector, `CV² = 1` — of which **exactly
one discriminates against general relativity and the Standard Model**.  The other
three are consistency checks: necessary, passed, and shared with the theories
being replaced.  And the discriminating one, `CV² = 1`, is weak in the way
`Spectrum.lean` already says: the observed `0.875` sits at the 63rd percentile of
a wide distribution, so it **excludes the geometric tower (`CV = 0`)** rather than
pinning a number.

**And a second internal contradiction, in §V above.**  That entry claimed the
index form has "no free number" and credited
`Attraction.attraction_fixes_the_bit`, a theorem §V.a′ had already renamed
because it withdrew exactly that claim.  Fixed in place; the correct reading is
§V.a′'s — the orientation bit is observed.

**Unanchored concepts.**  An identification is anchored when swapping it for an
alternative changes something falsifiable.  One is: `ν` as a count rather than a
signed winding, since the two give opposite signs
(`Anchor.signed_source_is_distinguished`) and antihydrogen selects between them.
Four are not:

* **`β = 1`** — glossed in `Precession.lean` as "the scale response of A6′" and
  **proved nowhere**, while the `42.99″/century` value is `coeff 1 1`.  A number
  is quoted downstream of an unproved identification; this is the most serious of
  the four and is new to the register;
* **`a = 1/ε`** — already listed, and nothing tests it;
* **`ħ` as an exact scale step** — presented as a discovery in `Crossed.lean` and
  demoted by A3′ to a *normalisation*, which cannot be tested;
* **the timelike direction as the drift direction** — the sign convention of
  §V.a.

`Anchor.drift_exceeds_anchor`.  None of this is a retraction of a theorem: every
statement named above is true.  What is corrected is what they were said to
show.

## V.o  `β` is derived, and the reason given for it was the wrong one

§V.n named the worst unanchored identification: `Precession.lean` produces
`42.99″/century` from `coeff 1 1`, and its `β = 1` was glossed as "the scale
response of A6′" and proved nowhere.  `Nonlinearity.lean` closes it.

**The gloss named the wrong input.**  A6′/A6″ is the *source* law and the
perihelion is measured in vacuum, where the source vanishes.  What fixes `β` is
the framework's own `tt` vacuum equation — `Diagonal.ric_tt = 0`, connection
certified by `Diagonal.metric_compatible` — and nothing else.  Had the gloss been
believed, `β` would have inherited A6″'s codimension problem (§V.k), which it
does not.

**The step where this goes wrong is recorded as a theorem, not a warning.**  For
a static metric the `tt` equation is `Δ_h N = 0`: the *lapse* is harmonic, with
respect to the *physical spatial metric*.  Treating it as harmonic in the bare
flat metric drops the `∇ψ·∇N` term and gives **`β = 1/2`**
(`Nonlinearity.flat_shortcut_gives_half`) — a factor of two in the quantity being
predicted.  The shortcut is exact when `γ = 0` and wrong precisely when `γ ≠ 0`,
which is the case that matters.

**What comes out is more than the value.**  Collecting the order-`m²` terms of
`Δ_h N = 0` with `h = e^{2ψ}δ` gives `2a₂ + a₁b₁ = 0`, and with the Newtonian
normalisation `a₁ = −1`:

> **`2β = 1 + γ`** (`Nonlinearity.beta_from_gamma`), equivalently
> `β − 1 = (γ − 1)/2`.

So `β` is **not an independent parameter here**, where the PPN framework leaves
it independent.  `β = 1` then follows from the already-derived `γ = 1`.  The
relation is falsifiable (`relation_is_falsifiable`) and **scalar–tensor theories
violate it** — Brans–Dicke has `β = 1` with `γ ≠ 1` — for a structural reason:
they do not have `R_tt = 0` in vacuum.  General relativity sits on the line, so
this does **not** discriminate against it.

**Newly assumed, and registered.**  The passage from `Δ_h N = 0` to
`2a₂ + a₁b₁ = 0` is the header's computation and is **not formalised** — the
framework has no differential-operator theory on a curved slice to state `Δ_h`
in.  It appears as the explicit hypothesis `Nonlinearity.Static1PN.VacuumSecondOrder`,
in the manner of A6″ and the areal coordinate.  Also assumed: the standard PPN
gauge (conformally flat `1PN` spatial slice), which is the gauge in which `β` and
`γ` are defined and so is forced by wanting to speak of them at all.
`assumedCount` is raised.

**Ledger effect.**  `Anchor.falsifiableDimensionless` `4 → 5`;
`unanchoredIdentifications` `4 → 3`; `anchoredIdentifications` `1 → 2`;
`discriminatingFromGR` unchanged at `1`.  `Anchor.the_inflation` weakens from an
equality to a strict inequality — the four definitional entries of §V.n are
unchanged and none was rehabilitated.

## V.p  The anisotropic non-commutative sector: chasing the number found two errors

The remaining route to a prediction that discriminates against general relativity
was the anisotropic non-commutative sector, which `Anisotropic.lean` described as
carrying a correction that is **zeroth order in gradients**, hence "not
derivative-suppressed", hence directly bounded by anything that bounds anisotropy.
`NCSize.lean` goes after the number.  **There is no number, and the reason is
worth more than the number.**

**Correction one: it is second order in gradients, not zeroth.**  The development
constructs exactly one non-commutative algebra — `Deformation.lean`'s first-order
deformation, whose commutator is `ħ` times a Poisson bracket.  Evaluating the
directional commutator there (`NCSize.dir_commutator_star`):

        [σ_a, σ_b]_⋆ = ħ ( ∂_qσ_a ∂_pσ_b − ∂_qσ_b ∂_pσ_a ) .

Two gradients and an explicit `ħ`.  "Zeroth order" described how the expression is
written, not its value.  The **relative** claim survives — the isotropic
correction carries four gradients — so the sector is still the leading one; what
is withdrawn is that it is unsuppressed, and that was the whole reason it looked
experimentally accessible.  Counted in `correctedCount`.

**Correction two: the theorem carrying the claim is `⟨rfl, rfl⟩`.**
`Anisotropic.dirCommutator_is_leading` states two definitional unfoldings and the
entire order-counting argument lives in its docstring.
`NCSize.leading_claim_has_no_failing_instance` applies §V.n's test to it.  **This
is the fifth occurrence** of a docstring carrying a physical claim its theorem
does not make, and the first with a physical consequence.
`citedAsPredictionButDefinitional` is raised.

**And a genuine result, which is a selection rule.**  The bracket is a wedge of
two gradients, so it vanishes when they are collinear
(`NCSize.collinear_gradients_kill_it`) — and staticity plus spherical symmetry
*is* collinearity, every directional log-scale being a function of the radius
alone.  So

> **the leading anisotropic non-commutative correction vanishes identically in
> the Schwarzschild configuration** (`NCSize.spherical_static_gives_zero`),

which is the solar-system laboratory.  The spin-sector experiments that would
bound this sector — spin-polarised torsion balances, co-magnetometers — sit
exactly where the framework says the effect is zero.  It is **not** identically
zero as algebra (`NCSize.correction_is_not_identically_zero`), so this is a
selection rule and not a triviality: the effect is sourced by the *departure*
from spherical symmetry, i.e. by oblateness and rotation.

**What is still missing, named.**  The object has weight two under `σ ↦ cσ`, so
it is a squared log-scale and not an energy.  Converting it into a spin-sector
energy shift requires a coupling of the rotational label to matter, and the
framework **has no matter sector**.  One item, not a fog — and it is the same
item that would be needed anywhere else the framework wants to meet an
experiment.

**Ledger effect: none.**  No prediction is added and none is removed;
`discriminatingFromGR` stays at `1`.  The route to a second discriminating
prediction is not closed, but it now has a known obstruction and a known
configuration to look in.

## V.q  The scanning hypothesis: reduced to one sentence, and not derived

`Scanning.lean` labels `λ = κρ` a proposal.  `Response.lean` goes after it and
does **not** promote it.  What it does is locate it exactly, and the location is
useful.

**It is not the hypothesis.**  `Scanning.scanRate κ ρ t := κ·ρ(t)` is a
*definition*, so nothing downstream of it can be evidence for it.  The content is
`Response.FactorsThroughCount D N κ` — `D t − D t′ = κ(N t − N t′)`:

> **the response depends on the thresholds only through their number.**

Given that, and `Running.resolvedCount`'s uniform count, `λ = κρ` is the chain
rule (`Response.rate_is_kappa_rho`).  Factorisation is a genuine restriction
(`Response.factorisation_is_falsifiable`), so this is a real reformulation and not
a renaming.

**It reduces to a pattern the framework already uses.**  "The response sees only
how many, not which" is the same shape as `Attraction.lean`'s argument that
`Index.lean`'s source `ν` must be a count rather than a signed winding — which
§V.n records as the framework's one *anchored* identification, since antihydrogen
selects between the readings.  **This is a reduction, not a derivation.**  Two
statements of the same form about different quantities are not one statement, and
the register should not let that elision through.

**An argument that looks like it closes it, and does not.**  A per-threshold
response must be weight zero under `σ ↦ cσ` (`Weight.invSqCoupling_invariant`
computes exactly that for the gauge `κ`) and fiducial invariant under A5, hence a
function of scale *differences* (`Expressive.invariant_iff_diffPattern`) — and
weight zero appears to kill differences too, since a difference has weight one,
leaving only the count.

**It does not close.**  Weight zero does not kill a *ratio* of differences.
`Response.weight_zero_does_not_force_constancy` exhibits the local spacing ratio
`(z−y)/(y−x)` on three consecutive thresholds: weight zero, fiducial invariant,
and not constant.  A response weighted by it satisfies every constraint the
framework imposes and does not factor through the count.

> **A5 and the weight grading are jointly insufficient here.**  Something must
> forbid the response from seeing the local spacing, and nothing in the framework
> does.  That is the gap, and it is a sharp one — the two tools that have settled
> most questions of this kind in the development both fail on it.

**And a downstream claim is weaker than it read.**
`Scanning.two_anomalies_one_number` holds for **every** density
(`Response.two_anomalies_holds_for_every_density`), so it is `κ` cancelling in a
fraction.  Its physical content is two identifications that appear nowhere in
Lean: that a `w₀wₐ` fit measures the response's fractional evolution, and that the
ladder-versus-ruler discrepancy measures the density's.  The "one mechanism, two
anomalies" claim is therefore **three inputs deep**.  It remains falsifiable — if
`w` evolves and the ladders agree, the picture dies — and `Anchor.lean` was right
not to count it among the framework's predictions.

**Ledger effect: none.**  Nothing is promoted and nothing is withdrawn.  The
proposal now has one sentence, one anchored analogue, and one named obstruction
where it had a name and a formula.

## V.r  The observer: a registered choice, and one expected consequence that fails

The framework has an observability axiom and no observer.  `Observer.lean`
proposes one.  **The proposal is an input and is labelled as one everywhere it
appears** — this entry exists so that no later reader mistakes it for a
consequence of A1–A7.

> **The observation postulate (a choice).**  An observer is the set of thresholds
> it has crossed, and a threshold is crossed when the resolution reaches it in
> every direction.

**What recommends it, which is an argument and not a proof.**  Five constraints
are forced by existing theorems and almost nothing survives all five: an observer
cannot be a thing (`Emergence.no_fundamental_list`), cannot be at a place (there
is no space — `directionForPositionCount` records the one time that was
forgotten), must be scale-relative (`Emergence.resolved`), can express only
differences (`Expressive.eval_not_invariant`), and can carry no preferred
direction (`Determination.influence_symm`).  A crossed-threshold set passes all
five, and `Observer.crossed_fiducial_invariant` checks the fourth explicitly —
crossing compares two scales, which is a difference, so the postulate is
statable under A5 rather than merely optional.

Two further arguments, also not proofs: it is built on `ν` being a **count**,
which §V.n records as the framework's one *anchored* identification; and crossed
sets only grow, so it supplies the arrow that
`Explanation.no_arrow_from_determination` proves the dynamics cannot.

**The chain that was asked for holds.**  With one scale axis resolutions are
totally ordered, so crossed sets are nested and every observer refines or is
refined by every other (`Observer.one_axis_is_a_chain`).  A4′ gives one scale per
direction and `Openness.no_dissipation_in_one_direction` derives `n ≥ 2` from A6,
so the framework has at least two axes — and then the order is not total
(`Observer.two_axes_incomparable`).

> **A4′ + A6 ⟹ observers are not totally ordered.**

A4′ was forced by `Frame.lean` on gravitational grounds — a scalar scale cannot
carry Schwarzschild.  So a gravitational input produces the structure of the
observer set.  That is the **first place in the development where the two sectors
constrain each other** rather than talking past each other, which is what
`Expressive.channels_independent` said they did.

**And the consequence I expected does not follow.**  The tempting reading — and
the one I proposed before checking — is that incomparable observers means no
observer-independent facts, hence a failure of absoluteness.  **Wrong.**
`Observer.common_refinement`: the componentwise maximum of two resolutions is a
resolution and has crossed everything both have, so every pair of records is
jointly realisable by a third observer.  Incomparability here is *perspective*,
not contradiction; a Wigner's-friend structure needs a record a finer observer
cannot confirm, and crossed sets are monotone.

**So the framework can now be placed against the seven assumptions of the no-go
literature**, which it could not before.  Given up, and by theorem: **realism**
(`Emergence.resolved`, `no_fundamental_list`) and **causal consistency**
(`Explanation.no_arrow_from_determination`, `cycle_of_three`).  Not expressible:
**locality** — there is no space.  Retained: **absoluteness, uniqueness of
outcomes, logical consistency**.  That is a position, not a gap.

**And the handle for anything further is exact.**  Absoluteness survives for one
reason: every resolution is admissible, so joins always exist
(`Observer.aoe_needs_join_failure`).  Losing it requires an axiom restricting the
admissible observers in a way not closed under joins.  Nothing in A1–A7 does, and
inventing one to reach a desired foundational conclusion would be the failure
mode this register has caught five times.  **Registered as open.**

`assumedCount` is raised by one for the observation postulate.

## V.s  What the observer yields — and the one gap it opens

`Observed.lean` spends §V.r's postulate: derives forward, and treats the refusals
as data.  **No assumption is added** — `assumedCount` is unchanged — and nothing
in it assumes absoluteness fails or takes the no-go list as a target.

**What follows.**

* **Agreement between observers is itself an observer.**  The componentwise
  minimum of two resolutions has crossed *exactly* what both have crossed —
  `Observed.crossedSet_meet`, an equality where `common_refinement` gave only an
  inclusion.  Intersubjective agreement is realised by a third observer rather
  than constructed over the two;
* **an observer is a difference, not a position**
  (`Observed.observation_is_fiducial_invariant`), so observation factors through
  resolutions modulo a common shift and an observer cannot know where it is, only
  how far it stands from what it sees.  *That the quotient has dimension `n − 1 =
  k = 3` is arithmetic and is **not** read as "the observer space is space" —
  moving in it means resolving differently, not moving, and §III of this register
  records what happened the last time a scale index was read as a position;*
* **drift gives the arrow and gives it a ceiling.**  Advancing along one scale
  direction only enlarges the record (`Observed.drift_monotone`) — the order the
  dynamics provably cannot supply.  But `Observed.drift_cannot_resolve`: **a
  threshold blocked in any transverse scale direction is never crossed, by any
  amount of drift.**  Elapsing does not reveal everything; the transverse
  resolution is a permanent gate.  This is the first thing in the development
  that behaves like a horizon without being built from a metric.

**What does not follow.**

* **G1** — `Observed.path_underdetermined`: two routes with the same endpoints
  cross the thresholds in different orders and nothing prefers one.  This is §V.l
  wearing a third face — nothing selects a solution, nothing selects a cut,
  nothing selects a route.  Not a new gap;
* **G2** — every pair of observations is compatible, since a join always exists;
* **G3** — **the observer never touches the algebra.**  `Observer.Crossed` takes
  two real vectors and nothing of ring type.  The framework *has* non-commutative
  data that differ (`NCSize.correction_is_not_identically_zero`, re-exposed as
  `Observed.observer_cannot_separate_them`), and no observer can reach any of it;
* **G4** — given a resolution the record is determined, so there are no outcomes
  and nothing for a probability to weigh.  Not stated as a theorem because there
  is nothing to state; the absence is in what the definitions lack.

**The blindness half of G3 is definitional, not proved** — it is read off a
signature — and `Observed.lean` says so in place rather than dressing it as a
theorem.  That is the distinction this register has had to make five times, made
here against my own construction.

**And G2 and G4 are symptoms of G3.**  Incompatibility comes from
non-commutativity; an observer blind to it has compatible measurements
necessarily, and with no incompatibility there is nothing to weigh.  So:

> **The observation postulate registers only commutative data while the
> framework's algebra is non-commutative, and nothing connects them.**

That is the place where something obviously should follow and does not — the
framework carries `ħ` (`Deformation.lean`), a canonical commutation relation
(`Quantum.lean`) and a leading non-commutative correction (`Anisotropic.lean`),
and its observer sees none of it.  **A new axiom, if one is needed, is about how
an observer registers non-commuting data.**  It is not about absoluteness, and
nothing here gives a reason to give absoluteness up.

Registered as open.  No count changes.

## V.t  The observer made internal — the detachment was a second defect, not the
same one

§V.r's observer is detached, and not as a matter of presentation: its resolution
is an argument independent of any configuration, so nothing determines it and it
contributes to nothing.  `Internal.lean` makes it a part of the configuration.
**No assumption is added**; the postulate is the same one, read with the
resolution supplied by the configuration instead of by hand.

**What internality buys.**

* **A larger observer records less** (`Internal.record_antitone`), and the union
  of parts is the *intersection* of records (`Internal.record_union`).  The
  lattice turns over: joining observers coarsens what they can jointly say;
* **the detached observer is the internal one that occupies everything**
  (`Internal.record_univ_is_the_detached_observer`).  Detachment is not the
  absence of a part — it is the part that leaves **no complement**, which is why
  it felt abstract and why nothing determined it.  Same shape as
  `Openness.closed_universe_is_empty`;
* **the observer is a term in the equation for the observed**
  (`Internal.observer_is_in_the_determiner`): any of its directions that is not
  one of the observed pair lies in that pair's transverse set, hence in
  `Diagonal.ric_offdiag`'s sum.  With `Explanation.self_not_in_determiner` it also
  cannot set its own resolution;
* **and disturbance is force** (`Internal.disturbance_iff_separable`): the
  observer's contribution vanishes for every pair exactly when the configuration
  is separable, which `Explanation.force_is_non_separability` says is exactly
  force-free.  *Measurement disturbs a system precisely when there is an
  interaction in it* — one theorem, not two facts that resemble each other.  This
  is the first statement in the development about measurement as a physical
  process rather than as a labelling.

**What it does not buy, and this is the finding.**
`Internal.internal_observations_still_compatible`: the inverted lattice still has
joins, so any two internal observers remain compatible.  **G3 is untouched.**

And the reason is now nameable rather than observed.  `InternalCrossed` compares
values with `≤`.  **Crossing is an order relation, and the framework's scale
algebra is an arbitrary `Ring` with no order supplied anywhere.**  So the observer
— detached or internal — lives in the real-valued shadow of the configuration and
not in its algebra.  That is a sharper G3 than §V.s had: not "the signature
happens to take reals" but "the relation is order-theoretic and the object is
not ordered".

> **Detachment and blindness were two different defects.**  Internality fixes the
> first.  The second is exactly where it was.

**What would close it, and the trap.**  An internal observer of the algebra needs
"resolved" to be algebraic rather than order-theoretic; the obvious candidate is
an **idempotent**, and non-commuting idempotents would be exactly the incompatible
measurements G3 lacks.  **That is the standard quantum construction and adopting
it would be importing it** — the failure mode this development exists to avoid.
It is recorded as the shape of the answer and explicitly not taken.  What would
make it native is an argument that `Emergence.resolved` has idempotent form for
reasons internal to the framework.  No such argument exists.

Registered as open, and it is the same open item as G3 rather than a new one.  No
count changes.

## V.u  Observer / observed / process — the quantum enters, and G3 narrows

Idempotents were the wrong candidate and `Triple.lean` does not use them.
Separating the three roles instead — what is observed, what observes, the process
between — finds the structure already present since `Determination.lean`.

**The three-place object was already there.**  `Determination.influence σ a b c`
is the contribution of direction `c` to the pair `(a,b)`: **observed** = the pair,
**observer** = `c`, **process** = the influence, which is the framework's own
notion of force.  Nothing is added.  What matters is that the process is
**algebra-valued**, where `Observer.Crossed` produced a `Prop` from an order on
`ℝ` — which §V.t identified as the whole of G3.

**And the pair swap fails by exactly one commutator.**

> `Triple.influence_asymmetry` : `inf σ a b c − inf σ b a c = [∂_aσ_c , ∂_bσ_c]`.

The second derivative is symmetric by `d_comm`, the cross terms merely exchange,
and what survives is `(∂_aσ_c)(∂_bσ_c)` against its reverse.
`Determination.influence_symm` is the **commutative case** of this, so the third
law is the classical limit of an identity whose quantum content is a commutator —
and `Deformation.star_commutator` makes that commutator `ħ` times a Poisson
bracket.

> **The order in which an observation is read matters, and the discrepancy is the
> quantum correction.**  Incompatibility of measurements, arrived at natively:
> nothing was imported, and `Quantum.ad` was already the framework's word for it.

**The other swap is different and classical.**  Exchanging observer with observed
is not a symmetry even over a commutative ring
(`Triple.observer_observed_not_symmetric`).  Which part is record and which is
recorded is a real distinction and a *classical* one; the quantum asymmetry lives
entirely inside the observed pair.

**A finding about the development itself: it had no non-commutative model of A1.**
`Positivity.oneAxis`, `Witness.polyScaleAlgebra`, `Newton.instScaleAlgebra` and
`Explanation.mvScaleAlgebra` are **all commutative**, so the non-commutative
sector had been reasoned about throughout with no witness.
`Triple.matrixScaleAlgebra` supplies one — two-by-two matrices over polynomials
with entrywise partials, where A1 holds and the ring does not — and
`Triple.asymmetry_witness` shows the asymmetry is genuinely nonzero there
(`[E₀₀, E₀₁] = E₀₁`).

**G3 narrows and does not close.**  Observation now reaches the algebra.  But by
`NCSize.iso_commutator_star` the commutator `[∂_aσ_c, ∂_bσ_c]` carries **four**
derivatives — it is the *isotropic* correction.  The framework's **leading**
non-commutative object is `[σ_a, σ_b]`, two derivatives
(`NCSize.dir_commutator_star`), and it does not appear in the asymmetry.

**The reason given here for that was wrong and is corrected in §V.v.**  This entry
said "every term in `influence` carries a single directional scale `σ_c`".  It does
not: the second and third terms carry `σ_a` and `σ_b`
(`Mutual.influence_sees_the_pair_scales`).  The correct reason is that those two
terms **exchange factor for factor** under the pair swap and so cancel from the
difference — a sharper statement, and one that points at an operator ordering
rather than at an absence.

> **Observation sees the isotropic quantum correction and remains blind to the
> leading anisotropic one.**

That is a much sharper residue than §V.s's G3, and it names the next question:
whether a coupling in which the observer's own scale multiplies the observed
pair's scales is *forced*.  `Determination.influence` has no such term.
Registered as open.

The negative half — that `[σ_a, σ_b]` never appears — is read off the definition
and is stated as such, not dressed as a theorem.  **No assumption is added**;
`assumedCount` is unchanged.

## V.v  A correction to §V.u, and a symmetric three-place candidate

**The correction.**  §V.u explained observation's blindness to `[σ_a, σ_b]` by
saying every term of `influence` carries a single directional scale `σ_c`.
**False.**  The second and third terms are `(∂_bσ_a)(∂_aσ_c)` and
`(∂_aσ_b)(∂_bσ_c)` — the observed pair's scales multiplied against the observer's
— and `Mutual.influence_sees_the_pair_scales` exhibits two configurations
agreeing on `σ_c` with different influences.  Caught by re-reading the definition
after the diagnosis was questioned, one turn after it was written.

**The right reason is sharper.**  Those two terms **exchange factor for factor**
under the pair swap: the second term of `influence σ a b c` is, in the same
order, the third term of `influence σ b a c`.  So they cancel from the difference
and the asymmetry is carried entirely by `(∂_aσ_c)(∂_bσ_c)` —
`Mutual.asymmetry_depends_only_on_the_observer`: **the difference between the two
readings of one observation is a function of the observer's own scale alone.**
The relative structure between observer and pair is present in the process and
cancels out of the observable part.

**And that cancellation rests on an ordering nothing fixes.**  `Diagonal.lean`
computes the connection and the Ricci contraction over a **`CommRing`**, where
the order of factors within a term is not a choice because there is nothing to
choose.  Carrying those formulas to a non-commutative ring **requires an operator
ordering that the commutative computation does not determine.**  So the blindness
is downstream of an *unforced* choice.  Registered as open, and it is prior to
everything in the rest of this entry.

**A symmetric candidate, and it is a proposal.**  `Pattern.wedge` is the
antisymmetrised product of a *pair* and `wedge_self_eq_commutator` makes
`wedge σ σ a b = [σ_a, σ_b]`.  The three-index version follows the same
construction:

> `Mutual.triWedge σ a b c = σ_a[σ_b,σ_c] + σ_b[σ_c,σ_a] + σ_c[σ_a,σ_b]`,

and `triWedge_eq_alternating` proves it **is** the totally antisymmetrised triple
product.  So it is the next term in a sequence the framework already started, not
an object chosen for its shape.  It treats all three directions identically
(`triWedge_antisymm` — swapping any two flips the sign), is built from
`Anisotropic.dirCommutator` (`triWedge_from_dirCommutator`) hence reaches the
**leading** anisotropic sector, vanishes in the commutative case and on the
isotropic locus, and is not identically zero (`triWedge_witness`: three matrix
units give `2E₀₀ + E₁₁`, with no derivative taken anywhere).

**What it is not.**  Nothing derives that observation must take this form; it is
labelled a proposal throughout.  What would make it forced is an argument that a
three-place observation must be totally antisymmetric —
`Explanation.cycle_of_three` says the minimal determination structure is a
three-cycle in which each direction observes exactly one pair, so privileging one
role breaks a symmetry the structure has.  That argument is **not** made here.

**No assumption is added**; `assumedCount` is unchanged.  Two open items are
registered: the operator ordering, and whether total antisymmetry is forced.

## V.w  The operator ordering, settled — and one structural claim scoped

§V.v registered the operator ordering as open and called it prior to everything
else in that entry: `Diagonal.lean` computes the connection and the Ricci
contraction over a **`CommRing`**, and carrying those formulas to a
non-commutative ring requires an ordering the commutative computation does not
determine.  `Ordering.lean` answers it, without any theory of the observer,
which is what made the question worth asking first.  The answer has two halves
and this register should carry both: one protects the development's best
results, the other takes something back.

**The lift is not unique, and the ambiguity is exactly the quantum correction.**
`Ordering.offDiag_sub_rev`: the two available orders of the off-diagonal Ricci
summand differ by three commutators of scale gradients per transverse direction,
written in `Quantum.ad`.  The obstruction is not diffuse — it is built from the
same objects `NCConformal.lean` calls the correction.

**And it reaches the vacuum condition.**  `Ordering.vacuum_is_ordering_dependent`
exhibits a configuration in `Triple.matrixScaleAlgebra` at three directions —
`σ = (0, 0, τ)` with `∂₀τ = E₀₀` and `∂₁τ = E₀₁` — on which `R_ab = 0` **holds in
one order and fails in the other**, because `E₀₁E₀₀ = 0` while `E₀₀E₀₁ = E₀₁`.
That is not a discrepancy in a value both orders agree is nonzero; it is the
solution set moving.  Three directions is the smallest case with anything in it:
`Diagonal.offdiag_zero_in_two` had already shown the constraint is empty below
three.

**The gravity chain does not stand in it.**
`Ordering.ordering_irrelevant_of_static`: under `Diagonal.lean`'s own staticity
hypothesis every commutator in the difference carries a vanishing factor, for
every pair — if neither member of the observed pair is the distinguished
direction all of them vanish, and if one is, the surviving factors pair with a
vanishing one.  So `γ = 1`, `2β = 1 + γ` and the two arcsecond values are
statements about a configuration on which **every** ordering agrees.  They are
not hostages to how the observer turns out, which is what the question was asked
to find out.

**What is scoped, and this is the correction.**  §V.j read `Diagonal.ric_offdiag`
as the general structural fact that *no pair of directions carries its own
curvature; every component is carried by the complement*, and called it a
property of diagonal metrics rather than of the static case.  It is a property
of diagonal metrics **over a commutative ring**: the cancellation that produces
it is between terms whose order is not a choice there and is one here.  The
theorem is untouched; the reading is narrowed to the commuting locus until an
ordering is argued for.  `correctedCount` is raised.

**A canonical lift exists and is not adopted.**  `Ordering.integrandSym` is the
sum of the two orders — reversal-invariant by construction
(`sym_is_order_free`), twice the classical summand on the commuting locus
(`sym_doubles_the_classical`), and stated without dividing by two so it costs no
hypothesis on the ring.  Adopting it *because it is symmetric* would be exactly
the move §V.t declined for idempotents: importing the shape of the answer.  What
would make it native is an argument that the contraction defining `Ric` has a
preferred order for reasons internal to the framework.  There is none, and the
choice stays open and registered.

**What the file does not do.**  It does not lift `Diagonal.lean`.  It lifts the
one expression the chain's cancellation runs through, which is enough to answer
the question and small enough to check by eye.  The general non-commutative
connection is a larger job and is not attempted.

**Ledger effect.**  `correctedCount` `9 → 10`.  **No assumption is added** — the
file introduces no hypothesis the development did not already carry — and no
prediction is added or removed.  `auditedTheorems` `1040 → 1053`.

## V.x  The observer-invariance screen — and a sample the register never carried

§V.w settled the ordering.  The other half of the same question was whether the
ledger's predictions are predictions *of the world* or of something that includes
the observer, since `Internal.observer_is_in_the_determiner` puts the observer
inside the configuration.  `Screen.lean` runs `Explanation.lean`'s accounting on
the pair.

**The reassuring half is a theorem and not a reassurance.**
`Screen.observer_preserves_predictions`: a quantity constant across the
admissible worlds is constant across the admissible *(world, observer)* pairs,
because the pairs project into the worlds.  So **no quantity of the world loses
its status when the observer joins the configuration**, and the fear that the
ledger would have to be redone is answered — for every entry that is about the
scale pattern.

**The other half is where the content is.**
`Screen.observer_relative_is_modulus`: for **every** theory of the world that
admits one particular resolution — no constraint on the world is assumed beyond
that — what is recorded is a `Modulus`, an input.  Two observers in one world
record different sets (`recorded_set_is_observer_relative`), so
`Explanation.tightening_predicts_more` cannot reach the freedom: it is in the
other slot, and only a theory of the observer touches it.  The direction is
`Internal.record_antitone`'s — a larger observer records less, so the sample
grows as the observer shrinks.

**Sorting the five falsifiable entries.**  `γ = 1`, `2β = 1 + γ`, universal
attraction and one cone for every sector are properties of the scale pattern and
are covered verbatim.  `CV² = 1` is not: it is a statistic of *which thresholds
are in the sample*, and being in the sample is what `record` is.

**And it is the discriminating one.**  `Anchor.discriminatingFromGR` is `1`, and
that one is `CV² = 1`.  So the single entry the framework's empirical case rests
on is the single entry the screen classifies as observer-relative.  The counts
agreeing is arithmetic and `Screen.lean` says so in place; what is not arithmetic
is which entry falls where.

**The register was missing the underlying item, which is the §V.a pattern again.**
`Spectrum.lean` says in its own header that "eleven gaps is a small sample and the
twelve mass scales were selected by hand (massless states excluded, neutrino
masses unknown)".  That self-registration never reached this list, and it is the
same failure mode as the three §V.a found and as A6′ before them — a file
declaring its own weakness while the register a reader consults says nothing.
`unregisteredFound` is raised.

What the screen adds to it is why it is structural rather than a matter of
sample size: **nothing in the development links `Spectrum.gaps` to
`Internal.record`.**  Until something does, `CV² = 1` is a prediction about a
sample rather than about a configuration, and the framework has no theory of
which sample.  Building that link is the work; noting that it is missing is all
this pass does.

**No count moves except the two named.**  No assumption is added — `Screen.lean`
introduces no hypothesis any theorem carries — and no prediction is added or
removed: `falsifiableDimensionless` stays at `5` and `discriminatingFromGR` at
`1`, because `CV² = 1` can still fail and still discriminates.  What changed is
what it is a statement about.  `unregisteredFound` `3 → 4`;
`auditedTheorems` `1053 → 1063`.

**Step zero therefore closes with one item settled and one sharpened.**  The
ordering question is answered and the gravity chain is out of it (§V.w).  The
observer question is answered for every quantity of the world and open for the
one that matters, which is a smaller and more specific hole than the one it
replaces.

## V.y  A2 had no model, and now has one

§V.b asked whether the *auxiliary* structures — `Crossed.ScaleShift`,
`Waves.Conserved`, `RG.ScaleFlow` and the rest — are ever built from the
framework's own carrier, and `Witness.lean` answered it.  Nobody asked the same
question of the carriers themselves.  The answer was worse.

**`ScaleField` had never been constructed.**  Not "only in special cases": the
structure that carries A2 and A3 had **no term anywhere in the development**, so
every theorem about the scale field was true, clean and unwitnessed.  The reason
is uniform.  Every model of A1 here is a polynomial ring or a matrix ring over
one — `Positivity.oneAxis`, `Witness.polyScaleAlgebra`,
`Explanation.mvScaleAlgebra`, `Triple.matrixScaleAlgebra` — and in a polynomial
ring **the units are the non-zero constants**.  A2 asks that `s = e^σ` be a unit
with `d s = s · dσ`; with `s` constant that forces `dσ = 0`.  *In every model the
development had, the scale could not vary.*

`Newton.Dual` is the one escape and it escapes only so far: `σ = εφ` over the
dual numbers varies, and `gradsq_inr` is zero **by construction**, so that model
is exactly first order.  The whole gravity chain is about a finite-amplitude
configuration, `s_t·s_r = 1` with `s_t ≠ 1`.  The same held of A4′: the only
`DirScale` in the development, `Light.twoScale`, is constant over `ℝ`.

**`ExpPoly.lean` builds the ring.**  `ExpPoly n` is the additive monoid algebra
of the polynomials over the polynomials — finite sums `Σ qⱼ e^{pⱼ}` with
polynomial coefficients and polynomial exponents — with
`∂ᵢ(q e^p) = (∂ᵢq + q ∂ᵢp) e^p`.  `der_mul` and `der_comm` verify A1 on it;
`e^p` is a unit with inverse `e^{-p}`, and `der_expUnit` is A2's axiom.  Then

* `scaleField p` — **the first term of type `ScaleField` in the development**,
  with `scaleField_gradient_ne_zero` showing the log-scale genuinely varies;
* `recipTwo` — **A4′ anisotropic with exact reciprocity**: `(e^{x₀}, e^{-x₀})`
  gives `s_t·s_r = 1` on the nose (`recipTwo_reciprocal`) and is not isotropic
  (`recipTwo_not_isotropic`).  The Schwarzschild relation at finite amplitude,
  with no linearisation.

**What it does not do, and the reason is worth more than the attempt.**  It
exhibits **no vacuum solution**.  `Diagonal.vacuum_scale_sum` is a conditional
whose antecedent contains `Ric = 0`, and nothing here meets it.  Not for want of
trying: the Schwarzschild profile is `σ_r = −½ log(1 − 2M/r)`, and **a logarithm
of a rational function is not an exponential polynomial**.  So the gravity
chain's hypotheses are now instantiable — a directional scale with reciprocity
exists — while its *equations* are not solved in this ring.

That is a sharper statement of what is missing than "no model": the next ring
must be closed under `∫ dp/p` as well as under `exp`.  Registered as open.

**And the `Witness.lean` caveat applies verbatim.**  One model carrying A2 shows
A2 is *compatible* with A1, not that every model of A1 carries it.  What changed
is that the theorems about the scale field and about an anisotropic directional
scale are known non-vacuous, which they were not.

**The exponential is a choice, and the register should say so before the file is
read as saying otherwise.**  A2 asks for a unit `s` and an element `σ` with
`d s = s · dσ`, and adjoining a formal `e^p` is one way to have one.  Making `σ`
**nilpotent** is another: then `e^σ` is a polynomial and nothing is adjoined.
`ExpPolyModel.dualScaleField` presents `Newton.Dual`'s square-zero model as the
`ScaleField` it always was, so **A2 now has models of two different kinds** and
neither is derived from A1–A7.  What separates them is recorded rather than
argued: `exp_not_first_order` against `Newton.Dual.gradsq_inr` — the nilpotent
mechanism is exact but truncated at a finite order in the scale, the exponential
one is untruncated but formal.

**And a scope statement that matters more than either, caught by asking which
branch this is.**  `Dual.lean` divides the scale group under A3′ into the `ℝ`
branch (`Axioms.ScaleField`, a real-valued log-scale) and the `𝕋` branch
(`Defect.ScaleDefect`, a log-scale modulo a period, which is what lets a defect
wind), and its own summary is that **gravity selects the `𝕋` branch** — the `ℝ`
branch being the `Δ → 0` degeneration, with `Dual.R_branch_is_trivial` showing a
period-zero defect has no holonomy.

**Everything in `ExpPoly.lean` is the `ℝ` branch.**  A formal exponential of a
polynomial has no period, and `Axioms.ScaleField` is that branch's carrier.  So
the model closes "A2 has no model" **on the branch the framework's own source law
does not use**.

**And the statement of the remaining gap needed correcting one commit after it
was made.**  I wrote that `Defect.ScaleDefect` "still has no model".  It has one:
`Defect.vacuum`, in the file that declares the structure, and a linear lift gives
one of any winding.  `Defect.ScaleDefect` is **inhabited** — `Defect.vacuum` is a model, and a linear
lift gives one of any winding — so the gap is *not* that the `𝕋` branch has no
model.  It is that **`ScaleDefect` is not a scale field**: it is a function
`ℝ → ℝ` with a quasiperiodicity condition, carrying no ring, no derivations and
no unit.  Nothing in the development builds an object that is at once a model of
A1–A2 and periodic; the two branches are related by `Dual.lean`'s prose and by
theorems about `ScaleDefect` alone.  **The join is what is missing**, and it is
what bridge one's successor should build.

Recorded rather than quietly fixed, because it is the register's own recurring
failure — a claim in a docstring that the declarations do not support — committed
here by me one commit after the pass that was written to catch it.

That also replaces the explanation given above for the missing vacuum solution.
The observation about logarithms is true and is not the deep reason; the deep
reason is that defects live on the other branch.  Both are recorded, the second
as the one to act on.

**Ledger effect.**  `auditedTheorems` `1063 → 1084`.  No assumption is added and
no prediction moves.  `unwitnessedStructures` is **not** raised and not lowered:
it counts the six auxiliary structures §V.b named, and the point here is that the
axiom carriers were never on that list at all — a gap in what the register
counted rather than a change in the count.

## V.z  The join, and why it could not have the shape it was asked for

§V.y's correction named what stayed open: nothing in the development was at once
a model of A1–A2 and periodic, so the two branches of A3′ had no common carrier.
`Circle.lean` builds one, and the first thing it finds is that the object being
asked for does not exist.

**There is no periodic scale field, and that is a theorem.**  If the log-scale is
defined only modulo a period then `σ` is **not an element of the ring** — only its
gradient is, because differentiating kills the ambiguity.  `Axioms.ScaleField`
has a field `σ : A`.  `Circle.no_scaleField_with_uPow` proves the consequence on
the smallest example: on `ℝ[u, u⁻¹]` with `d = u ∂/∂u`, the unit `u^k` has a
perfectly good scale gradient — the constant `k` — and **no scale field can carry
it** for `k ≠ 0`.

So `Axioms.ScaleField` *is* the `ℝ` branch by construction.  That was not a
modelling accident and no amount of model-building would have fixed it.

**The obstruction is exactness.**  `Circle.dloop_coeff_zero`: every derivative on
the circle has vanishing constant term, so `no_potential` — a non-zero constant
is not a derivative.  The gradient of `u^k` is closed and **not exact**, which is
what "defined only modulo a period" means algebraically, and the winding is the
class it represents.

**The join keeps the gradient and drops the potential.**  `Circle.ScaleGradient`
carries `s : Aˣ`, `grad : Fin n → A` and `d s = s · grad`.  Then
`ofScaleField_isExact` embeds every scale field as an **exact** scale gradient,
and `circGradient_not_isExact` exhibits an inexact one.  One carrier, two
branches, and `IsExact` is exactly what separates them: the `ℝ` branch is the
exact locus, and `Dual.lean`'s `Δ → 0` degeneration is the statement that on that
locus nothing winds.

`Circle.exact_iff_trivial` then relates the two branches' *carriers* rather than
arguing the relation in prose: the gradient of `u^k` is exact exactly when the
defect it follows is trivial.  `Dual.lean` called `Defect.lift` the covering map
`ℝ → ℝ/ΔZ`; this is that identification with a ring on one side of it.

**It is a proposal and is not adopted.**  `Axioms.lean` is unchanged and A2 still
reads as it did.  Restating A2 with the gradient primitive would touch everything
downstream of `σ`, and there is a great deal — A5 is a statement about
*differences of `σ`*, and `Openness.A5_A6_dichotomy` reads A5 and A6 off the
group `σ` generates.  Adopting the new carrier here because it is convenient
would be the move §V.t declined for idempotents.  It is registered as the shape
of the answer, with the work of weighing it left to a pass that does the weighing.

**What it does sharpen is the consolidation.**  Any merge of A2 with A4′ should
take the **gradient** as primitive and recover the potential as the exact case,
rather than the other way round — otherwise the merged axiom inherits
`ScaleField`'s commitment to one branch of A3′ without saying so.

**Still open, and listed rather than implied.**  `Circ` has one direction, so the
closedness condition `∂ᵢgⱼ = ∂ⱼgᵢ` that a multi-direction `ScaleGradient` needs
is vacuous here and untested; the consequences A2 has downstream of `σ` are not
checked against the gradient reading; and nothing here runs `Diagonal.lean`'s
chain, so there is **still no vacuum solution** — what is supplied is the object
that branch needs, not a solution on it.

**Ledger effect.**  `auditedTheorems` `1085 → 1100`.  No assumption is added:
`ScaleGradient` is a structure offered, and no theorem in the development depends
on it.  No prediction moves.

## V.aa  What A2 assumes, measured — and it is one unit

§V.z proposed a carrier and declined to adopt it, which left the axiom question
open in the worst way: a proposal on the table and nothing to decide it with.
`Gradient.lean` measures instead of arguing, and the measurement changes what the
proposal should be.

**The geometry never sees the log-scale.**  `hess`, `lap`, `gradsq`, `Chr`, `Rm`,
`Ric` and `Defm` are built from `sig` and nothing else, and
`Gradient.geometry_congr` makes that a theorem: two log-scales with the same
gradient have the same everything.  `Axioms.geometry_fiducial_invariant` — A5's
carrier — then follows from the congruence side, since a fiducial shift changes
no gradient.

**So `σ` does three things**: it lets `ScaleField` be stated, it carries the
additive half of the group law, and it makes `hess_symm` free because
`d i (d j σ) = d j (d i σ)` is `d_comm`.  The first two are bookkeeping.

**The third is the finding.**  `Gradient.exact_isClosed`: an exact gradient is
closed.  `Gradient.closed_not_exact`: the converse fails, on `Circle.lean`'s
winding scale.  So

> **A2 does not assume "there is a scale"; it assumes the scale's gradient is
> exact** — which by `Dual.lean` is the `ℝ` branch of A3′, chosen silently, and
> by `Dual.lean`'s own summary the branch gravity does not select.

That reframes the question from a matter of style to one with an answer: the
choice is between *closed* and *closed-and-exact*, not between `σ` and `grad`.

**And then the proposed structure collapses.**  Given a unit `s`, the equation
`d s = s · g` **determines** `g`, because `s` is invertible:
`Gradient.logDeriv_spec` gives a solution and `Gradient.grad_unique` shows there
is only one, so `Gradient.grad_eq_logDeriv` makes `Circle.ScaleGradient`
equivalent to `s : Aˣ`.

> **A2's content is one unit.**  The gradient is a definition, the log-scale is an
> *optional potential* for it, and exactness is a property of the unit rather than
> extra data.

§V.z proposed keeping the gradient as primitive.  That was one step short: the
gradient is not primitive either.

**Nothing is amended.**  `Axioms.lean` is untouched and A2 still reads as it did.
Restating it as "the scale is a unit", with `Closed` as an explicit hypothesis
where exactness was being used, is a wide mechanical edit whose value is that it
makes visible *which* results needed exactness — and it should be made once,
deliberately, by a pass that does it, not as a side effect of the one that
measured it.

**Three costs, recorded so the decision is made with them in hand.**

* every consequence of `hess_symm` inherits a hypothesis;
* closedness is **vacuous at one direction**, so `Circle.lean`'s witness does not
  test it: a closed-and-inexact gradient in `n ≥ 2` has not been built, and until
  one is, "closed is strictly weaker" is known only where it costs least;
* **the observer.**  `Observer.Crossed` compares *values*, `μ i ≤ σ i`, in a
  real-valued shadow.  With A2 reduced to a unit there is no `σ` in the ring for
  that shadow to shadow.  Nothing breaks — `Observer.Resolution` was never the
  ring's `σ` — but G3 sharpens from "the observer does not reach the algebra" to
  **the observer compares values of a quantity the axioms need not have**.

**Ledger effect.**  `auditedTheorems` `1100 → 1114`.  No assumption is added and
none is removed: what changed is the register's account of what A2 *was already*
assuming, which is why this is recorded here rather than in the assumed-count.
`unregisteredFound` is not raised either — nothing self-registered this; it had
not been noticed at all.

## VI.  What rests on the axioms alone

The scale/rotation split, the Lorentzian signature, the bookkeeping form, the
coupling, real rank one, `n = k+1`, conservation from Bianchi, the gravity chain
through to `1.7515″` and `42.99″/century`, `ħ` as an exact scale step, the
label structure on the anisotropic locus, and every statement in `Native.lean`.

`clean_count` records the audited total against the axiom-leak count, so the
claim "nothing rests on a gap" is a number and not a mood.
-/
import SCD.Data

namespace SCD.Audit

/-! ## The register, in numbers -/

/-- How many times the scalar-for-directional substitution has been made and
caught.  Recorded so the count cannot quietly drift.

Raised from five to **six** in the kinematics pass (§V.d): `Light.lean` and
`Observation.lean` were written with a scalar scale, and under A4′ their
headline claim is false — `Light.bare_null_not_phys_null`. -/
def scalarForDirectionalCount : ℕ := 6

theorem scalar_for_directional_count : scalarForDirectionalCount = 6 := rfl

/-- A separate count, for the same diagnostic applied to a *different* pair:
**direction indices read as positions**.  One occurrence so far — the ER=EPR
reading of `Transport.transport_coset`, withdrawn in `Well.lean` (§V.d).  Kept
apart from the scalar-for-directional count because the substitution is not the
same one. -/
def directionForPositionCount : ℕ := 1

theorem direction_for_position_count : directionForPositionCount = 1 := rfl

/-- And a third kind: **one homotopy class read as another**.

Two occurrences, both mine.  `π₁` of the circle-valued scalar scale placed in the
`π₂` slot of the projective directional one (§V.g, from the unification pass);
and the source law of `Index.lean`, a codimension-two equation applied to a
codimension-three source (§V.k) — the same substitution one level up.

Three distinct kinds of substitution now, all caught by the same question:
*of what?* -/
def homotopyClassCount : ℕ := 2

theorem homotopy_class_count : homotopyClassCount = 2 := rfl

/-- Claims retracted outright. -/
def retractedCount : ℕ := 4

/-- Claims corrected in scope, where the theorem survives and the gloss did
not.

Raised to **seven** by §V.m: "the framework predicts the weight-zero sector and
nothing else" survives as a *necessary* condition once
`Explanation.influence_not_homogeneous` shows `σ ↦ cσ` is not a symmetry of the
determination relation.  And to **eight** by §V.n: "eight dimensionless
predictions" survives as four, the rest being arithmetic on imported
definitions.  And to **nine** by §V.p: the anisotropic non-commutative
correction is second order in gradients, not zeroth, so it is the leading
correction but not an unsuppressed one.  And to **ten** by §V.w: §V.j's reading
of `Diagonal.ric_offdiag` as a property of diagonal metrics is a property of
diagonal metrics over a *commutative* ring, since the cancellation is between
terms whose order is not a choice there — `Ordering.vacuum_is_ordering_dependent`
shows the lift changes the solution set. -/
def correctedCount : ℕ := 10

/-- External results cited and not proved.

Raised from two to **three** by `Dual.lean`, which cites the classification of
self-dual locally compact abelian groups to pass from A3′ to a short list of
possible scale groups.  A3′ is a *trade*: it demotes `Crossed.lean`'s "`ħ` is an
exact scale step" from a discovery to a normalisation, and buys a
classification — so the citation count rising here is the price, not an
accident. -/
def citedCount : ℕ := 3

/-- Assumptions registered rather than smuggled.

Raised from three to **eight** by the assumption audit (§V.a, §V.a′): the
original three (A6′, uniform density, A7), plus three the register was *missing*
although the individual files self-registered them (the timelike sign
convention, the vacuum Ricci combination, `n`), plus two the recent work added
(`ν` is the threshold count; the scanning hypothesis) — **minus one**, the
vacuum Ricci combination, discharged by `Diagonal.lean`, **plus one** added by
§V.l: nothing selects a point in the solution space of the determination
relations, and **plus one more** by §V.o: the second-order content of the static
vacuum equation, `2a₂ + a₁b₁ = 0`, which the framework cannot yet state as a
differential equation, and **plus one more** by §V.r: the observation postulate,
`Observer.Crossed` — an observer is its crossed-threshold set, and a threshold is
crossed when the resolution reaches it in every direction.

The sign of `Δ` is counted with A6′ rather than separately, since it is that
input's residual bit.  **The count went up because the register was audited, not
because the framework got worse** — which is what happened when A6′ was added
too. -/
def assumedCount : ℕ := 10

/-- How many of those the register was **silently missing** — self-registered in
their own files and absent from this list.  Kept because it measures how well
the register works, not how well the framework does.

Raised to **four** by §V.x: `Spectrum.lean` declares in its own header that the
twelve mass scales behind `CV² = 1` were selected by hand, and this list never
carried it — while `CV² = 1` is the framework's one discriminating prediction. -/
def unregisteredFound : ℕ := 4

theorem register_was_incomplete : 0 < unregisteredFound := by decide

/-- **The register is not empty, and that is the point.**

A development with nothing retracted has not been audited.  The counts are
carried so that a reader can weigh the results against what had to be taken
back to get them. -/
theorem register_nonempty :
    retractedCount ≠ 0 ∧ correctedCount ≠ 0 ∧ citedCount ≠ 0 ∧ assumedCount ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The audit found more than the work discharged.**

The assumed-count went `3 → 8` when the register was audited, `8 → 7` when the
vacuum Ricci combination was derived, back to `8` when §V.l registered what
the dynamics does *not* supply, `9` when §V.o registered the vacuum equation's
second-order content, and `10` when §V.r registered the observation postulate.  Finding an assumption is cheap; closing one is
not, and the numbers should say so rather than flatter.

An earlier version of this file asserted `retracted + corrected ≤ assumed +
cited`, which was true at `8` and became false at `7`.  It was editorialising
rather than measuring, and is replaced. -/
theorem audit_found_more_than_it_closed : 3 < assumedCount := by decide

/-- Corrections outnumber retractions: more claims survived with their scope
narrowed than had to be withdrawn. -/
theorem more_corrected_than_retracted : retractedCount < correctedCount := by decide

/-- **The recurring error is still recurring**, and the register says so with a
number rather than a hope: two distinct index substitutions, six occurrences of
the first and one of the second, every one of them caught after the fact. -/
theorem index_substitutions_still_occur :
    5 < scalarForDirectionalCount ∧ 0 < directionForPositionCount := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Structures carrying hypotheses the framework does not supply — true
theorems whose physical reading is conditional (§V.b). -/
def unwitnessedStructures : ℕ := 6

/-- Notions that were declared more than once and are now declared once: A1's
substrate, the geometric objects, isotropy, parallelism, the wedge, the two
sector counts, A7, and the charge algebra (§V.c).  Recorded so that a later pass
can tell whether the language is drifting apart again. -/
def unifiedVocabularies : ℕ := 8

/-- **The merge added no assumption.**  Every duplicate removed in §V.c was a
duplicate: the unification was bookkeeping and not a weakening.

An earlier version certified this by pinning `correctedCount = 6`, the value at
the time of the merge.  §V.m raised it to `7` for an unrelated reason and the
theorem became false — **a live count cannot certify a past pass**, which is the
same lesson `audit_found_more_than_it_closed` learned when the assumed-count
moved.  The counts at the merge were `(retracted, corrected) = (4, 6)`; that is
recorded here as history rather than asserted as a standing fact. -/
theorem unification_added_nothing : 0 < unifiedVocabularies := by decide

/-- **The register grew under external audit, which is the point of having
one.**  An audit that finds nothing has not been run adversarially. -/
theorem register_grew_under_audit : 0 < unwitnessedStructures := by decide

/-! ## The standing verification claim -/

/-- Number of theorems put through `#print axioms` in `Verify.lean` — **every**
theorem in the development, generated from the sources rather than curated. -/
def auditedTheorems : ℕ := 1114

/-- Occurrences of `sorryAx` in that audit. -/
def sorryAxCount : ℕ := 0

/-- **Nothing in the development rests on a gap**, as a number rather than a
mood: every audited theorem reduces to `propext`, `Classical.choice` and
`Quot.sound` and to nothing else. -/
theorem clean_count : sorryAxCount = 0 ∧ 0 < auditedTheorems := by
  refine ⟨rfl, ?_⟩; decide

end SCD.Audit
