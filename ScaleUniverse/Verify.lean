/-
# Verification

Machine audit of the whole development.

`#print axioms` reports, for each theorem, the complete set of unproved
assumptions it ultimately rests on.  Every theorem below must report only

  `propext`, `Classical.choice`, `Quot.sound`

which are Lean's three standard logical axioms (they are what makes the
ambient logic classical set-theoretic mathematics).  Any occurrence of
`sorryAx` would mean an unfinished proof and would be reported here.

Note that `ScaleAlgebra`, `ScaleField` and the various physical hypotheses are
*not* Lean axioms.  They are typeclasses, structures and explicit hypotheses,
so they appear in the statements of the theorems rather than being smuggled in
behind them.  Nothing in this development postulates a physical result and
then calls it proved.
-/
import ScaleUniverse

namespace ScaleUniverse.Verify

/-! ## Sector I — emergence of geometry -/

-- Curvature is exactly the Kulkarni–Nomizu product of δ with scale deformation
#print axioms ScaleUniverse.two_Rm_eq
#print axioms ScaleUniverse.Ric_eq
#print axioms ScaleUniverse.RscBare_eq
#print axioms ScaleUniverse.Rm_eq_zero_of_Defm_eq_zero
#print axioms ScaleUniverse.Ric_eq_zero_of_Defm_eq_zero
#print axioms ScaleUniverse.two_Ric_eq

-- Integrable Weyl geometry: no second clock effect
#print axioms ScaleUniverse.scaleCurv_eq_zero

/-! ## Sector II — the axiom system -/

#print axioms ScaleUniverse.ScaleField.en_mul_scale
#print axioms ScaleUniverse.ScaleField.d_en
#print axioms ScaleUniverse.geometry_fiducial_invariant

/-! ## Sector III — the Newtonian limit -/

#print axioms ScaleUniverse.RscBare_linear
#print axioms ScaleUniverse.poisson
#print axioms ScaleUniverse.poisson_three
#print axioms ScaleUniverse.Dual.gradsq_inr
#print axioms ScaleUniverse.Dual.poisson_exact

/-! ## Sector IV — renormalisation group and the EFT tower -/

#print axioms ScaleUniverse.RG.callan_symanzik
#print axioms ScaleUniverse.RG.scale_invariant_of_fixedPoint
#print axioms ScaleUniverse.RG.ScaleFlow.observable_const_at_fixedPoint
#print axioms ScaleUniverse.RG.active_mono
#print axioms ScaleUniverse.RG.active_eq_of_no_threshold
#print axioms ScaleUniverse.RG.active_finite_range

/-! ## Sector V — particle scales -/

#print axioms ScaleUniverse.Particles.one_le_scaleRatio
#print axioms ScaleUniverse.Particles.lifetime_ge
#print axioms ScaleUniverse.Particles.lifetime_mono
#print axioms ScaleUniverse.Particles.lifetime_at_rest

/-! ## Sector VI — dark matter -/

#print axioms ScaleUniverse.Dark.detection_failure
#print axioms ScaleUniverse.Dark.dark_matter_exists
#print axioms ScaleUniverse.Dark.response_vanishes

/-! ## Sector VII — dark energy -/

#print axioms ScaleUniverse.Cosmology.dissipation_solution
#print axioms ScaleUniverse.Cosmology.energy_strictly_decreasing
#print axioms ScaleUniverse.Cosmology.scaleFactor_eq
#print axioms ScaleUniverse.Cosmology.hasDerivAt_scaleFactor
#print axioms ScaleUniverse.Cosmology.acceleration_pos
#print axioms ScaleUniverse.Cosmology.open_universe_accelerates

/-! ## Sector VIII — arrow of time -/

#print axioms ScaleUniverse.Entropy.entropy_nondecreasing
#print axioms ScaleUniverse.Entropy.no_reverse_law
#print axioms ScaleUniverse.Entropy.evolve_no_reverse_law
#print axioms ScaleUniverse.Entropy.entropy_production_implies_nonequilibrium

/-! ## Sector X — the non-commutative foundation and quantum mechanics -/

#print axioms ScaleUniverse.Quantum.ad_leibniz
#print axioms ScaleUniverse.Quantum.ad_jacobi
#print axioms ScaleUniverse.Quantum.ad_comm_of_commute
#print axioms ScaleUniverse.Quantum.ad_pow
#print axioms ScaleUniverse.Quantum.robertson
#print axioms ScaleUniverse.Quantum.heisenberg

/-! ## Sector XI — local covariance under dissipation -/

#print axioms ScaleUniverse.Covariance.CosmicHistory.Rm_eq
#print axioms ScaleUniverse.Covariance.CosmicHistory.field_equation_form_invariant
#print axioms ScaleUniverse.Covariance.CosmicHistory.no_local_expansion

/-! ## Sector XII — singularity resolution -/

#print axioms ScaleUniverse.Singularity.ScaleField.scale_ne_zero
#print axioms ScaleUniverse.Singularity.ScaleField.energy_ne_zero
#print axioms ScaleUniverse.Singularity.ScaleField.conformal_factor_isUnit
#print axioms ScaleUniverse.Singularity.curvature_indep_of_scale_value

/-! ## Sector XIII — testable predictions -/

#print axioms ScaleUniverse.Predictions.powerlaw_accel_numerator
#print axioms ScaleUniverse.Predictions.accelerates_iff
#print axioms ScaleUniverse.Predictions.eos_dissipationExponent
#print axioms ScaleUniverse.Predictions.eos_eq_neg_one_iff
#print axioms ScaleUniverse.Predictions.eos_lt_third_iff
#print axioms ScaleUniverse.Predictions.muon_matches_experiment
#print axioms ScaleUniverse.Predictions.poundRebka_value
#print axioms ScaleUniverse.Predictions.darkEnergyDensity_value
#print axioms ScaleUniverse.Predictions.logScale_ratio_const

/-! ## Sector XIV — A4 weakened: the directional scale -/

#print axioms ScaleUniverse.Frame.DirScale.reciprocal_metric
#print axioms ScaleUniverse.Frame.DirScale.isotropic_reciprocal_forces_flat
#print axioms ScaleUniverse.Frame.DirScale.isotropic_reciprocal_metric_bare
#print axioms ScaleUniverse.Frame.exists_reciprocal_nonisotropic

/-! ## Sector XV — the classical limit (deformation quantization) -/

#print axioms ScaleUniverse.Deformation.star_assoc
#print axioms ScaleUniverse.Deformation.star_classical
#print axioms ScaleUniverse.Deformation.star_commutator
#print axioms ScaleUniverse.Deformation.star_comm_iff_poisson_zero
#print axioms ScaleUniverse.Deformation.Biderivation.poisson_leibniz_left
#print axioms ScaleUniverse.Deformation.ccr_of_canonical

/-! ## Sector XVI — particles as scale defects -/

#print axioms ScaleUniverse.Defect.ScaleDefect.winding_unique
#print axioms ScaleUniverse.Defect.ScaleDefect.stable_of_winding_ne_zero
#print axioms ScaleUniverse.Defect.ScaleDefect.winding_eq_zero_of_trivial
#print axioms ScaleUniverse.Defect.ScaleDefect.pair_winding_zero
#print axioms ScaleUniverse.Defect.ScaleDefect.antiparticle_same_mass
#print axioms ScaleUniverse.Defect.ScaleDefect.mass_ratio_geometric
#print axioms ScaleUniverse.Defect.ScaleDefect.mass_ratio_const

/-! ## Sector XVII — axiom coherence: A4 is the isotropic locus of A4' -/

#print axioms ScaleUniverse.Unify.toMetric_of_isotropic
#print axioms ScaleUniverse.Unify.isotropic_iff_ofScalar
#print axioms ScaleUniverse.Unify.sector_coherence
#print axioms ScaleUniverse.Unify.not_isotropic_of_ne

/-! ## Sector XVIII — the strong sector -/

#print axioms ScaleUniverse.QCD.running_inv_sq
#print axioms ScaleUniverse.QCD.asymptotic_freedom
#print axioms ScaleUniverse.QCD.lambda_invariant
#print axioms ScaleUniverse.QCD.hadron_mass_ratio
#print axioms ScaleUniverse.QCD.geometric_tower_fails
#print axioms ScaleUniverse.QCD.lightestGlueballInLambda_value

/-! ## Sector XIX — curvature as a commutator (anisotropic sector) -/

#print axioms ScaleUniverse.Connection.comm_covD
#print axioms ScaleUniverse.Connection.bianchi
#print axioms ScaleUniverse.Connection.curv_of_central
#print axioms ScaleUniverse.Connection.curv_gradient_eq_zero
#print axioms ScaleUniverse.Connection.curv_split
#print axioms ScaleUniverse.Connection.curv_eq_rotation_part
#print axioms ScaleUniverse.Connection.curv_pure_scale_eq_zero
#print axioms ScaleUniverse.Connection.F_antisymm

/-! ## Sector XX — scale-native origin of the beta function -/

#print axioms ScaleUniverse.RG.beta_const_between_thresholds
#print axioms ScaleUniverse.RG.beta_finite_range
#print axioms ScaleUniverse.RG.beta_eq_of_all_active

/-! ## Sector XXI — non-commutativity, exactly (no ħ-expansion) -/

#print axioms ScaleUniverse.Crossed.shift_mul_eq
#print axioms ScaleUniverse.Crossed.commutator_eq
#print axioms ScaleUniverse.Crossed.comm_iff_shift_trivial
#print axioms ScaleUniverse.Crossed.delta_twisted_leibniz
#print axioms ScaleUniverse.Crossed.delta_leibniz_of_untwisted

/-! ## Sector XXII — internal symmetry as scale-pattern stabilizer -/

#print axioms ScaleUniverse.Gauge.stabilizer_eq_bot_of_injective
#print axioms ScaleUniverse.Gauge.stabilizer_eq_top_of_isotropic
#print axioms ScaleUniverse.Gauge.sameOrbit_iff_eq_scale
#print axioms ScaleUniverse.Gauge.internal_symmetry_determined

/-! ## Sector XXIII — running from counting, not loops -/

#print axioms ScaleUniverse.Running.hasDerivAt_invSqCoupling
#print axioms ScaleUniverse.Running.invSqCoupling_eq_one_loop
#print axioms ScaleUniverse.Running.asympt_free_iff_pos_density

/-! ## Sector XXIV — transport determined by the scale pattern -/

#print axioms ScaleUniverse.Transport.transport_unique_of_nondegenerate
#print axioms ScaleUniverse.Transport.transport_coset
#print axioms ScaleUniverse.Transport.transports_of_stabilizer
#print axioms ScaleUniverse.Transport.transport_unique_iff_stabilizer_trivial
#print axioms ScaleUniverse.Transport.nondegenerate_no_gauge_freedom

/-! ## Sector XXV — confinement and fractional charge -/

#print axioms ScaleUniverse.Color.BlockMonodromy.confinement
#print axioms ScaleUniverse.Color.BlockMonodromy.pair_observable
#print axioms ScaleUniverse.Color.BlockMonodromy.bound_state_size
#print axioms ScaleUniverse.Color.BlockMonodromy.no_partial_state
#print axioms ScaleUniverse.Color.BlockMonodromy.constituent_charge_fraction
#print axioms ScaleUniverse.Color.BlockMonodromy.constituent_charge_rat
#print axioms ScaleUniverse.Color.BlockMonodromy.bound_charge_divisible

/-! ## Sector XXVI — audit: light, redshift, and the observer -/

#print axioms ScaleUniverse.Observation.null_has_energy
#print axioms ScaleUniverse.Observation.redshift_is_scale_ratio
#print axioms ScaleUniverse.Observation.obsEnergy_rescale
#print axioms ScaleUniverse.Observation.redshift_fiducial_invariant
#print axioms ScaleUniverse.Observation.causal_structure_still_blind

/-! ## Sector XXVII — audit: the mass law is not determined by the topology -/

#print axioms ScaleUniverse.MassAudit.mass_law_underdetermined
#print axioms ScaleUniverse.MassAudit.both_laws_antiparticle_degenerate
#print axioms ScaleUniverse.MassAudit.massQuad_ratio_not_constant

/-! ## Sector XXVIII — rebuilt foundation: the scale/rotation split is canonical -/

#print axioms ScaleUniverse.Foundation.scale_mul
#print axioms ScaleUniverse.Foundation.scale_commutator
#print axioms ScaleUniverse.Foundation.curvature_is_scale_invisible
#print axioms ScaleUniverse.Foundation.scale_eq_iff_differ_by_rotation
#print axioms ScaleUniverse.Foundation.commutator_eq_one_of_comm
#print axioms ScaleUniverse.Foundation.comm_of_scale_injective

/-! ## Sector XXIX — signature derived from dissipation -/

#print axioms ScaleUniverse.Signature.codim_ker_eq_one
#print axioms ScaleUniverse.Signature.no_time_of_no_drift
#print axioms ScaleUniverse.Signature.spatial_eq_top_of_no_drift
#print axioms ScaleUniverse.Signature.spatial_ne_top_of_drift
#print axioms ScaleUniverse.Signature.spatial_smul
#print axioms ScaleUniverse.Signature.signature_from_dissipation

/-! ## Sector XXX — the bookkeeping form derived from a trace -/

#print axioms ScaleUniverse.Invariant.Trace.form_symm
#print axioms ScaleUniverse.Invariant.Trace.form_invariant
#print axioms ScaleUniverse.Invariant.Trace.form_ad_skew
#print axioms ScaleUniverse.Invariant.Trace.form_add_left

/-! ## Sector XXXI — quantitative gravity: the isotropic sector gets half -/

#print axioms ScaleUniverse.Deflection.iso_is_exactly_half
#print axioms ScaleUniverse.Deflection.iso_ratio_half
#print axioms ScaleUniverse.Deflection.missing_half
#print axioms ScaleUniverse.Deflection.solarObs_value
#print axioms ScaleUniverse.Deflection.solarIso_value
#print axioms ScaleUniverse.Deflection.iso_fails_by_far

/-! ## Sector XXXII — directions are the algebra; A1's hidden flatness -/

#print axioms ScaleUniverse.Direction.DirTransport.curv_antisymm
#print axioms ScaleUniverse.Direction.DirTransport.flat_iff_lie_hom
#print axioms ScaleUniverse.Direction.DirTransport.curv_of_abelian
#print axioms ScaleUniverse.Direction.DirTransport.commute_iff_bracket_acts_trivially
#print axioms ScaleUniverse.Direction.DirTransport.transport_determined_by_generators

/-! ## Sector XXXIII — the other half of light deflection -/

#print axioms ScaleUniverse.PPN.gamma_zero_is_isotropic
#print axioms ScaleUniverse.PPN.gamma_one_is_observed
#print axioms ScaleUniverse.PPN.reciprocal_expansion
#print axioms ScaleUniverse.PPN.gamma_eq_one_of_reciprocal
#print axioms ScaleUniverse.PPN.gamma_eq_one_first_order
#print axioms ScaleUniverse.PPN.deflection_reciprocal_eq_observed
#print axioms ScaleUniverse.PPN.halves_equal

/-! ## Sector XXXIV — defect codimension: the framework predicts strings -/

#print axioms ScaleUniverse.Codimension.pointlike_iff_two_dim
#print axioms ScaleUniverse.Codimension.three_dim_gives_strings
#print axioms ScaleUniverse.Codimension.pointlike_forces_three
#print axioms ScaleUniverse.Codimension.no_pointlike_in_four
#print axioms ScaleUniverse.Codimension.string_mass_not_topological
#print axioms ScaleUniverse.Codimension.stringMass_strictMono
#print axioms ScaleUniverse.Codimension.extended_or_low_dimensional

/-! ## Sector XXXV — reciprocity fixed by asymptotic flatness -/

#print axioms ScaleUniverse.Vacuum.const_of_deriv_zero_and_vanishing
#print axioms ScaleUniverse.Vacuum.reciprocity_of_asymptotic_flatness
#print axioms ScaleUniverse.Vacuum.scale_product_eq_one
#print axioms ScaleUniverse.Vacuum.product_constant_without_flatness
#print axioms ScaleUniverse.Vacuum.tr_area_element_constant

/-! ## Sector XXXVI — point particles restored by the directional scale -/

#print axioms ScaleUniverse.Axis.bareForm_neg
#print axioms ScaleUniverse.Axis.physForm_neg
#print axioms ScaleUniverse.Axis.neg_indistinguishable
#print axioms ScaleUniverse.Axis.isotropic_no_order_parameter
#print axioms ScaleUniverse.Axis.nondegenerate_full_frame
#print axioms ScaleUniverse.Axis.uniaxial_stabilizer
#print axioms ScaleUniverse.Axis.uniaxial_axis_distinguished

/-! ## Sector XXXVII — two topological charges, one confined -/

#print axioms ScaleUniverse.Charges.DefectCharge.block_confined
#print axioms ScaleUniverse.Charges.DefectCharge.hedgehog_free
#print axioms ScaleUniverse.Charges.DefectCharge.exactly_one_confined
#print axioms ScaleUniverse.Charges.DefectCharge.charges_independent
#print axioms ScaleUniverse.Charges.DefectCharge.observable_pair_any_hedgehog

/-! ## Sector XXXVIII — Mercury perihelion -/

#print axioms ScaleUniverse.Precession.coeff_reciprocal
#print axioms ScaleUniverse.Precession.coeff_isotropic
#print axioms ScaleUniverse.Precession.isotropic_is_third
#print axioms ScaleUniverse.Precession.mercury_value
#print axioms ScaleUniverse.Precession.mercury_isotropic_value

/-! ## Sector XXXIX — audit: the colour block is not the spatial block -/

#print axioms ScaleUniverse.ColorAudit.identification_predicts_two
#print axioms ScaleUniverse.ColorAudit.identification_fails_baryon
#print axioms ScaleUniverse.ColorAudit.identification_fails_charge
#print axioms ScaleUniverse.ColorAudit.spatial_block_is_not_colour_block
#print axioms ScaleUniverse.ColorAudit.three_matches_charge

/-! ## Sector XL — the Ricci cancellation closing the gravity chain -/

#print axioms ScaleUniverse.Schwarzschild.ricci_combination
#print axioms ScaleUniverse.Schwarzschild.vacuum_log_derivative
#print axioms ScaleUniverse.Schwarzschild.scale_sum_derivative_zero
#print axioms ScaleUniverse.Schwarzschild.vacuum_iff_scale_sum_stationary
#print axioms ScaleUniverse.Schwarzschild.area_element_stationary

/-! ## Sector XLI — gravity closed: Ricci from the connection -/

#print axioms ScaleUniverse.RicciDiag.ricciTT_eq
#print axioms ScaleUniverse.RicciDiag.ricciRR_eq
#print axioms ScaleUniverse.RicciDiag.gravity_chain
#print axioms ScaleUniverse.RicciDiag.area_stationary_derived

/-! ## Sector XLII — content is a slice: no fundamental particles -/

#print axioms ScaleUniverse.Emergence.resolved_mono
#print axioms ScaleUniverse.Emergence.content_never_complete
#print axioms ScaleUniverse.Emergence.always_more_above
#print axioms ScaleUniverse.Emergence.no_fundamental_list
#print axioms ScaleUniverse.Emergence.mass_iff_threshold
#print axioms ScaleUniverse.Emergence.mass_mono
#print axioms ScaleUniverse.Emergence.content_eq_of_no_threshold
#print axioms ScaleUniverse.Emergence.content_changes_only_at_threshold

/-! ## Sector XLIII — the threshold-structure prediction and its data test -/

#print axioms ScaleUniverse.Spectrum.mass_threshold_inverse
#print axioms ScaleUniverse.Spectrum.equal_gaps_variance_zero
#print axioms ScaleUniverse.Spectrum.observed_cvSq_value
#print axioms ScaleUniverse.Spectrum.meanGap_value
#print axioms ScaleUniverse.Spectrum.observed_not_geometric
#print axioms ScaleUniverse.Spectrum.observed_within_scale_invariant_range
#print axioms ScaleUniverse.Spectrum.densityFromGaps_value
#print axioms ScaleUniverse.Spectrum.density_gap_inverse

/-! ## Sector XLIV — audit: the proposed cross-sector test does not exist -/

#print axioms ScaleUniverse.CrossCheck.rhoAll_value
#print axioms ScaleUniverse.CrossCheck.rhoQuark_value
#print axioms ScaleUniverse.CrossCheck.densities_differ
#print axioms ScaleUniverse.CrossCheck.density_ratio_near_two
#print axioms ScaleUniverse.CrossCheck.sector_relation_is_identity
#print axioms ScaleUniverse.CrossCheck.no_second_determination
#print axioms ScaleUniverse.CrossCheck.quarkCvSq_value
#print axioms ScaleUniverse.CrossCheck.quark_not_geometric

/-! ## Sector XLV — what the framework can express at all -/

#print axioms ScaleUniverse.Expressive.invariant_factors
#print axioms ScaleUniverse.Expressive.diffPattern_invariant
#print axioms ScaleUniverse.Expressive.invariant_iff_diffPattern
#print axioms ScaleUniverse.Expressive.eval_not_invariant
#print axioms ScaleUniverse.Expressive.scale_says_nothing_about_rotation
#print axioms ScaleUniverse.Expressive.rotation_says_nothing_about_scale
#print axioms ScaleUniverse.Expressive.channels_independent
#print axioms ScaleUniverse.Expressive.neither_channel_complete

/-! ## Sector XLVI — the scale/rotation coupling, derived -/

#print axioms ScaleUniverse.Coupling.bracket_scaling_scaling
#print axioms ScaleUniverse.Coupling.bracket_rotation_scaling
#print axioms ScaleUniverse.Coupling.bracket_rotation_rotation
#print axioms ScaleUniverse.Coupling.coupling_structure
#print axioms ScaleUniverse.Coupling.no_rotation_of_commuting
#print axioms ScaleUniverse.Coupling.boost_bracket_eq_rotation
#print axioms ScaleUniverse.Coupling.scalings_do_not_commute

/-! ## Sector XLVII — dynamics from the coupling -/

#print axioms ScaleUniverse.Dynamics.no_flatness_from_commuting_derivations
#print axioms ScaleUniverse.Dynamics.nonflat_witness
#print axioms ScaleUniverse.Dynamics.commutative_sector_transports_commute
#print axioms ScaleUniverse.Dynamics.commutative_curvature_undetectable
#print axioms ScaleUniverse.Dynamics.source_conserved_of_field_equation
#print axioms ScaleUniverse.Dynamics.no_field_equation_of_nonconserved
#print axioms ScaleUniverse.Dynamics.source_antisymm
#print axioms ScaleUniverse.Dynamics.field_equation_content
#print axioms ScaleUniverse.Dynamics.same_multiplet_no_rotation
#print axioms ScaleUniverse.Dynamics.rotation_implies_different_multiplet
#print axioms ScaleUniverse.Dynamics.larger_multiplet_fewer_generators
#print axioms ScaleUniverse.Dynamics.multiplet_change_needs_pattern_change

/-! ## Sector XLVIII — which algebra: real rank one -/

#print axioms ScaleUniverse.Algebra.scaling_rotation_orthogonal
#print axioms ScaleUniverse.Algebra.boost_isScaling
#print axioms ScaleUniverse.Algebra.boost_add
#print axioms ScaleUniverse.Algebra.boost_smul
#print axioms ScaleUniverse.Algebra.boost_mul_succ_succ
#print axioms ScaleUniverse.Algebra.boost_bracket_spatial
#print axioms ScaleUniverse.Algebra.boosts_commute_iff_parallel
#print axioms ScaleUniverse.Algebra.commuting_boosts_lie_on_a_line
#print axioms ScaleUniverse.Algebra.commuting_family_one_parameter
#print axioms ScaleUniverse.Algebra.no_two_dimensional_commuting_family
#print axioms ScaleUniverse.Algebra.commuting_drifts_proportional
#print axioms ScaleUniverse.Algebra.boost_eq_zero_iff

/-! ## Sector XLIX — the particle model the algebra allows -/

#print axioms ScaleUniverse.Particle.boost_injective
#print axioms ScaleUniverse.Particle.pattern_is_one_vector
#print axioms ScaleUniverse.Particle.mixture_second_moment
#print axioms ScaleUniverse.Particle.mixture_cvSq_ge_one
#print axioms ScaleUniverse.Particle.mixture_cvSq_eq_one_iff
#print axioms ScaleUniverse.Particle.observed_disfavours_higher_rank
#print axioms ScaleUniverse.Particle.rate_value_not_fixed
#print axioms ScaleUniverse.Particle.block_two_valued
#print axioms ScaleUniverse.Particle.block_cannot_be_three_valued
#print axioms ScaleUniverse.Particle.block_self_inverse
#print axioms ScaleUniverse.Particle.two_odd_make_even
#print axioms ScaleUniverse.Particle.hedgehog_conserved_in_splitting
#print axioms ScaleUniverse.Particle.no_further_label
#print axioms ScaleUniverse.Particle.particle_label_structure

/-! ## Sector L — slice artifacts, rotation, and why three -/

#print axioms ScaleUniverse.Slice.newContent_nonempty_of_threshold
#print axioms ScaleUniverse.Slice.newContent_mono
#print axioms ScaleUniverse.Slice.newContent_empty_of_no_threshold
#print axioms ScaleUniverse.Slice.no_finite_universal_labelling
#print axioms ScaleUniverse.Slice.label_count_measures_range
#print axioms ScaleUniverse.Slice.wedge_eq_bracket
#print axioms ScaleUniverse.Slice.wedge_bilinear_left
#print axioms ScaleUniverse.Slice.wedge_eq_zero_iff_parallel
#print axioms ScaleUniverse.Slice.homogeneous_carries_no_rotation
#print axioms ScaleUniverse.Slice.rotation_requires_biaxial
#print axioms ScaleUniverse.Slice.wedge_dim_eq_iff
#print axioms ScaleUniverse.Slice.three_is_unique
#print axioms ScaleUniverse.Slice.more_wedges_than_directions
#print axioms ScaleUniverse.Slice.fewer_wedges_than_directions

/-! ## Sector LI — the axis question, settled -/

#print axioms ScaleUniverse.Axes.rotation_needs_variation
#print axioms ScaleUniverse.Axes.combable_no_rotation
#print axioms ScaleUniverse.Axes.wound_carries_rotation
#print axioms ScaleUniverse.Axes.rotationless_is_trivial
#print axioms ScaleUniverse.Axes.rotation_iff_variation
#print axioms ScaleUniverse.Axes.no_second_axis
#print axioms ScaleUniverse.Axes.axis_or_variation
#print axioms ScaleUniverse.Axes.axis_stabilizer_nontrivial
#print axioms ScaleUniverse.Axes.multiplet_flatness_needs_per_direction_scalings

/-! ## Sector LII — the last two inputs -/

#print axioms ScaleUniverse.Dimension.algebra_bigger_than_directions
#print axioms ScaleUniverse.Dimension.rep_dim_determined
#print axioms ScaleUniverse.Dimension.rot_matches_scale_iff
#print axioms ScaleUniverse.Dimension.alg_matches_rep_iff
#print axioms ScaleUniverse.Dimension.two_matching_conditions_differ
#print axioms ScaleUniverse.Dimension.wedge_smul_both
#print axioms ScaleUniverse.Dimension.wedge_ratio_invariant
#print axioms ScaleUniverse.Dimension.only_ratios_are_fixed
#print axioms ScaleUniverse.Dimension.density_normalization_relation
#print axioms ScaleUniverse.Dimension.normalization_returns_input

/-! ## Sector LIII — A7, and the locus audit -/

#print axioms ScaleUniverse.Locus.three_from_observability
#print axioms ScaleUniverse.Locus.observability_fails_elsewhere
#print axioms ScaleUniverse.Locus.observability_iff_three
#print axioms ScaleUniverse.Locus.no_scale_invariant_interaction
#print axioms ScaleUniverse.Locus.constant_coupling_iff_no_content
#print axioms ScaleUniverse.Locus.isotropic_pair_parallel
#print axioms ScaleUniverse.Locus.isotropic_no_rotation
#print axioms ScaleUniverse.Locus.labels_require_anisotropy
#print axioms ScaleUniverse.Locus.everything_switches_on_together
#print axioms ScaleUniverse.Locus.particle_locus_is_anisotropic

/-! ## Sector LIV — what the position predicts -/

#print axioms ScaleUniverse.Cosmos.shift_invariant_is_constant
#print axioms ScaleUniverse.Cosmos.rate_constant_of_fiducial_invariance
#print axioms ScaleUniverse.Cosmos.w_does_not_evolve
#print axioms ScaleUniverse.Cosmos.scale_ratio_depends_only_on_difference
#print axioms ScaleUniverse.Cosmos.no_first_moment
#print axioms ScaleUniverse.Cosmos.finite_lookback_no_origin
#print axioms ScaleUniverse.Cosmos.isotropic_gravitates_without_labels
#print axioms ScaleUniverse.Cosmos.dark_matter_has_no_species
#print axioms ScaleUniverse.Cosmos.resolvable_needs_width_below_gap
#print axioms ScaleUniverse.Cosmos.broad_structures_unresolvable
#print axioms ScaleUniverse.Cosmos.resolvability_boundary

/-! ## Sector LV — the non-commutative curvature, and the first correction -/

#print axioms ScaleUniverse.NCConformal.NCScale.hess_symm
#print axioms ScaleUniverse.NCConformal.NCScale.Chr_symm
#print axioms ScaleUniverse.NCConformal.NCScale.Defm_antisymm_part
#print axioms ScaleUniverse.NCConformal.NCScale.Defm_symm_iff_commutator
#print axioms ScaleUniverse.NCConformal.NCScale.Defm_symm_iff_commute
#print axioms ScaleUniverse.NCConformal.NCScale.symmetric_part_uncorrected
#print axioms ScaleUniverse.NCConformal.NCScale.correction_is_pure_antisymmetric
#print axioms ScaleUniverse.NCConformal.NCScale.sum_Chr_Chr_full_nc
#print axioms ScaleUniverse.NCConformal.NCScale.sum_Chr_Chr_full_classical
#print axioms ScaleUniverse.NCConformal.NCScale.quantum_correction_couples_to_rotation
#print axioms ScaleUniverse.NCConformal.NCScale.correction_vanishes_on_commuting
#print axioms ScaleUniverse.Cosmos.two_dark_routes_differ

/-! ## Sector LVI — black holes, waves, and the borrowed questions -/

#print axioms ScaleUniverse.Horizon.gtt_ne_zero
#print axioms ScaleUniverse.Horizon.reciprocal_never_degenerate
#print axioms ScaleUniverse.Horizon.redshift_never_infinite
#print axioms ScaleUniverse.Horizon.no_degeneracy_anywhere
#print axioms ScaleUniverse.Horizon.null_cone_scale_independent
#print axioms ScaleUniverse.Horizon.waves_travel_on_the_light_cone
#print axioms ScaleUniverse.Horizon.no_energy_dependent_speed
#print axioms ScaleUniverse.Horizon.entropy_of_scale_ratio
#print axioms ScaleUniverse.Horizon.entropy_doubling_is_additive
#print axioms ScaleUniverse.Horizon.entropy_increment_independent_of_size
#print axioms ScaleUniverse.Horizon.no_minimum_length
#print axioms ScaleUniverse.Horizon.no_final_description

/-! ## Sector LVII — the framework asking its own questions -/

#print axioms ScaleUniverse.Native.not_two_places_of_parallel
#print axioms ScaleUniverse.Native.separation_is_oriented
#print axioms ScaleUniverse.Native.single_anisotropy_boundary
#print axioms ScaleUniverse.Native.label_forces_anisotropy
#print axioms ScaleUniverse.Native.zero_window_resolves_nothing
#print axioms ScaleUniverse.Native.content_is_interval_valued
#print axioms ScaleUniverse.Native.no_global_field_equation
#print axioms ScaleUniverse.Native.ordering_discrepancy_is_the_observable
#print axioms ScaleUniverse.Native.parity_conserved_under_binding
#print axioms ScaleUniverse.Native.both_labels_conserved
#print axioms ScaleUniverse.Native.no_maximum_anisotropy
#print axioms ScaleUniverse.Native.no_cutoff_either_end

/-! ## Sector LVIII — confronting the data -/

#print axioms ScaleUniverse.Data.desi_tension_exceeds_three_sigma
#print axioms ScaleUniverse.Data.desi_significance_dataset_dependent
#print axioms ScaleUniverse.Data.falsification_threshold
#print axioms ScaleUniverse.Data.kappa_below_bound
#print axioms ScaleUniverse.Data.rho_below_bound
#print axioms ScaleUniverse.Data.delta_below_bound
#print axioms ScaleUniverse.Data.z_boson_far_inside
#print axioms ScaleUniverse.Data.ccl_above_bound
#print axioms ScaleUniverse.Data.gkpy_below_bound
#print axioms ScaleUniverse.Data.determinations_straddle_bound
#print axioms ScaleUniverse.Data.gkpy_updated_inside
#print axioms ScaleUniverse.Data.desi_combinations_disagree_internally
#print axioms ScaleUniverse.Data.bound_separates_kappa_from_sigma
#print axioms ScaleUniverse.Data.breit_wigner_spans_the_bound
#print axioms ScaleUniverse.Data.dispersion_limit_above_planck
#print axioms ScaleUniverse.Data.one_charge_prediction
#print axioms ScaleUniverse.Data.zero_nu_beta_beta_decides
#print axioms ScaleUniverse.Data.scorecard

/-! ## Sector IX — light -/

#print axioms ScaleUniverse.Light.isNull_iff_bare
#print axioms ScaleUniverse.Light.isNull_scale_invariant
#print axioms ScaleUniverse.Light.scale_determined_of_nonnull
#print axioms ScaleUniverse.Light.physForm_ne_bareForm
#print axioms ScaleUniverse.Light.null_weight_zero

end ScaleUniverse.Verify
