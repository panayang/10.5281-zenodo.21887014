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
import SCD

namespace SCD.Verify

/-! ## Sector I — emergence of geometry -/

-- Curvature is exactly the Kulkarni–Nomizu product of δ with scale deformation
#print axioms SCD.two_Rm_eq
#print axioms SCD.Ric_eq
#print axioms SCD.RscBare_eq
#print axioms SCD.Rm_eq_zero_of_Defm_eq_zero
#print axioms SCD.Ric_eq_zero_of_Defm_eq_zero
#print axioms SCD.two_Ric_eq

-- Integrable Weyl geometry: no second clock effect
#print axioms SCD.scaleCurv_eq_zero

/-! ## Sector II — the axiom system -/

#print axioms SCD.ScaleField.en_mul_scale
#print axioms SCD.ScaleField.d_en
#print axioms SCD.geometry_fiducial_invariant

/-! ## Sector III — the Newtonian limit -/

#print axioms SCD.RscBare_linear
#print axioms SCD.poisson
#print axioms SCD.poisson_three
#print axioms SCD.Dual.gradsq_inr
#print axioms SCD.Dual.poisson_exact

/-! ## Sector IV — renormalisation group and the EFT tower -/

#print axioms SCD.RG.callan_symanzik
#print axioms SCD.RG.scale_invariant_of_fixedPoint
#print axioms SCD.RG.ScaleFlow.observable_const_at_fixedPoint
#print axioms SCD.RG.active_mono
#print axioms SCD.RG.active_eq_of_no_threshold
#print axioms SCD.RG.active_finite_range

/-! ## Sector V — particle scales -/

#print axioms SCD.Particles.one_le_scaleRatio
#print axioms SCD.Particles.lifetime_ge
#print axioms SCD.Particles.lifetime_mono
#print axioms SCD.Particles.lifetime_at_rest

/-! ## Sector VI — dark matter -/

#print axioms SCD.Dark.detection_failure
#print axioms SCD.Dark.dark_matter_exists
#print axioms SCD.Dark.response_vanishes

/-! ## Sector VII — dark energy -/

#print axioms SCD.Cosmology.dissipation_solution
#print axioms SCD.Cosmology.energy_strictly_decreasing
#print axioms SCD.Cosmology.scaleFactor_eq
#print axioms SCD.Cosmology.hasDerivAt_scaleFactor
#print axioms SCD.Cosmology.acceleration_pos
#print axioms SCD.Cosmology.open_universe_accelerates

/-! ## Sector VIII — arrow of time -/

#print axioms SCD.Entropy.entropy_nondecreasing
#print axioms SCD.Entropy.no_reverse_law
#print axioms SCD.Entropy.evolve_no_reverse_law
#print axioms SCD.Entropy.entropy_production_implies_nonequilibrium

/-! ## Sector X — the non-commutative foundation and quantum mechanics -/

#print axioms SCD.Quantum.ad_leibniz
#print axioms SCD.Quantum.ad_jacobi
#print axioms SCD.Quantum.ad_comm_of_commute
#print axioms SCD.Quantum.ad_pow
#print axioms SCD.Quantum.robertson
#print axioms SCD.Quantum.heisenberg

/-! ## Sector XI — local covariance under dissipation -/

#print axioms SCD.Covariance.CosmicHistory.Rm_eq
#print axioms SCD.Covariance.CosmicHistory.field_equation_form_invariant
#print axioms SCD.Covariance.CosmicHistory.no_local_expansion

/-! ## Sector XII — singularity resolution -/

#print axioms SCD.Singularity.ScaleField.scale_ne_zero
#print axioms SCD.Singularity.ScaleField.energy_ne_zero
#print axioms SCD.Singularity.ScaleField.conformal_factor_isUnit
#print axioms SCD.Singularity.curvature_indep_of_scale_value

/-! ## Sector XIII — testable predictions -/

#print axioms SCD.Predictions.powerlaw_accel_numerator
#print axioms SCD.Predictions.accelerates_iff
#print axioms SCD.Predictions.eos_dissipationExponent
#print axioms SCD.Predictions.eos_eq_neg_one_iff
#print axioms SCD.Predictions.eos_lt_third_iff
#print axioms SCD.Predictions.muon_matches_experiment
#print axioms SCD.Predictions.poundRebka_value
#print axioms SCD.Predictions.darkEnergyDensity_value
#print axioms SCD.Predictions.logScale_ratio_const

/-! ## Sector XIV — A4 weakened: the directional scale -/

#print axioms SCD.Frame.DirScale.reciprocal_metric
#print axioms SCD.Frame.DirScale.isotropic_reciprocal_forces_flat
#print axioms SCD.Frame.DirScale.isotropic_reciprocal_metric_bare
#print axioms SCD.Frame.exists_reciprocal_nonisotropic

/-! ## Sector XV — the classical limit (deformation quantization) -/

#print axioms SCD.Deformation.star_assoc
#print axioms SCD.Deformation.star_classical
#print axioms SCD.Deformation.star_commutator
#print axioms SCD.Deformation.star_comm_iff_poisson_zero
#print axioms SCD.Deformation.Biderivation.poisson_leibniz_left
#print axioms SCD.Deformation.ccr_of_canonical

/-! ## Sector XVI — particles as scale defects -/

#print axioms SCD.Defect.ScaleDefect.winding_unique
#print axioms SCD.Defect.ScaleDefect.stable_of_winding_ne_zero
#print axioms SCD.Defect.ScaleDefect.winding_eq_zero_of_trivial
#print axioms SCD.Defect.ScaleDefect.pair_winding_zero
#print axioms SCD.Defect.ScaleDefect.antiparticle_same_mass
#print axioms SCD.Defect.ScaleDefect.mass_ratio_geometric
#print axioms SCD.Defect.ScaleDefect.mass_ratio_const

/-! ## Sector XVII — axiom coherence: A4 is the isotropic locus of A4' -/

#print axioms SCD.Unify.toMetric_of_isotropic
#print axioms SCD.Unify.isotropic_iff_ofScalar
#print axioms SCD.Unify.sector_coherence
#print axioms SCD.Unify.not_isotropic_of_ne

/-! ## Sector XVIII — the strong sector -/

#print axioms SCD.QCD.running_inv_sq
#print axioms SCD.QCD.asymptotic_freedom
#print axioms SCD.QCD.lambda_invariant
#print axioms SCD.QCD.hadron_mass_ratio
#print axioms SCD.QCD.geometric_tower_fails
#print axioms SCD.QCD.lightestGlueballInLambda_value

/-! ## Sector XIX — curvature as a commutator (anisotropic sector) -/

#print axioms SCD.Connection.comm_covD
#print axioms SCD.Connection.bianchi
#print axioms SCD.Connection.curv_of_central
#print axioms SCD.Connection.curv_gradient_eq_zero
#print axioms SCD.Connection.curv_split
#print axioms SCD.Connection.curv_eq_rotation_part
#print axioms SCD.Connection.curv_pure_scale_eq_zero
#print axioms SCD.Connection.F_antisymm

/-! ## Sector XX — scale-native origin of the beta function -/

#print axioms SCD.RG.beta_const_between_thresholds
#print axioms SCD.RG.beta_finite_range
#print axioms SCD.RG.beta_eq_of_all_active

/-! ## Sector XXI — non-commutativity, exactly (no ħ-expansion) -/

#print axioms SCD.Crossed.shift_mul_eq
#print axioms SCD.Crossed.commutator_eq
#print axioms SCD.Crossed.comm_iff_shift_trivial
#print axioms SCD.Crossed.delta_twisted_leibniz
#print axioms SCD.Crossed.delta_leibniz_of_untwisted

/-! ## Sector XXII — internal symmetry as scale-pattern stabilizer -/

#print axioms SCD.Gauge.stabilizer_eq_bot_of_injective
#print axioms SCD.Gauge.stabilizer_eq_top_of_isotropic
#print axioms SCD.Gauge.sameOrbit_iff_eq_scale
#print axioms SCD.Gauge.internal_symmetry_determined

/-! ## Sector XXIII — running from counting, not loops -/

#print axioms SCD.Running.hasDerivAt_invSqCoupling
#print axioms SCD.Running.invSqCoupling_eq_one_loop
#print axioms SCD.Running.asympt_free_iff_pos_density

/-! ## Sector XXIV — transport determined by the scale pattern -/

#print axioms SCD.Transport.transport_unique_of_nondegenerate
#print axioms SCD.Transport.transport_coset
#print axioms SCD.Transport.transports_of_stabilizer
#print axioms SCD.Transport.transport_unique_iff_stabilizer_trivial
#print axioms SCD.Transport.nondegenerate_no_gauge_freedom

/-! ## Sector XXV — confinement and fractional charge -/

#print axioms SCD.Color.BlockMonodromy.confinement
#print axioms SCD.Color.BlockMonodromy.pair_observable
#print axioms SCD.Color.BlockMonodromy.bound_state_size
#print axioms SCD.Color.BlockMonodromy.no_partial_state
#print axioms SCD.Color.BlockMonodromy.constituent_charge_fraction
#print axioms SCD.Color.BlockMonodromy.constituent_charge_rat
#print axioms SCD.Color.BlockMonodromy.bound_charge_divisible

/-! ## Sector XXVI — audit: light, redshift, and the observer -/

#print axioms SCD.Observation.null_has_energy
#print axioms SCD.Observation.redshift_is_scale_ratio
#print axioms SCD.Observation.obsEnergy_rescale
#print axioms SCD.Observation.redshift_fiducial_invariant
#print axioms SCD.Observation.causal_structure_still_blind

/-! ## Sector XXVII — audit: the mass law is not determined by the topology -/

#print axioms SCD.MassAudit.mass_law_underdetermined
#print axioms SCD.MassAudit.both_laws_antiparticle_degenerate
#print axioms SCD.MassAudit.massQuad_ratio_not_constant

/-! ## Sector XXVIII — rebuilt foundation: the scale/rotation split is canonical -/

#print axioms SCD.Foundation.scale_mul
#print axioms SCD.Foundation.scale_commutator
#print axioms SCD.Foundation.curvature_is_scale_invisible
#print axioms SCD.Foundation.scale_eq_iff_differ_by_rotation
#print axioms SCD.Foundation.commutator_eq_one_of_comm
#print axioms SCD.Foundation.comm_of_scale_injective

/-! ## Sector XXIX — signature derived from dissipation -/

#print axioms SCD.Signature.codim_ker_eq_one
#print axioms SCD.Signature.no_time_of_no_drift
#print axioms SCD.Signature.spatial_eq_top_of_no_drift
#print axioms SCD.Signature.spatial_ne_top_of_drift
#print axioms SCD.Signature.spatial_smul
#print axioms SCD.Signature.signature_from_dissipation

/-! ## Sector XXX — the bookkeeping form derived from a trace -/

#print axioms SCD.Invariant.Trace.form_symm
#print axioms SCD.Invariant.Trace.form_invariant
#print axioms SCD.Invariant.Trace.form_ad_skew

/-! ## Sector XXXI — quantitative gravity: the isotropic sector gets half -/

#print axioms SCD.Deflection.iso_is_exactly_half
#print axioms SCD.Deflection.iso_ratio_half
#print axioms SCD.Deflection.missing_half
#print axioms SCD.Deflection.solarObs_value
#print axioms SCD.Deflection.solarIso_value
#print axioms SCD.Deflection.iso_fails_by_far

/-! ## Sector XXXII — directions are the algebra; A1's hidden flatness -/

#print axioms SCD.Direction.DirTransport.curv_antisymm
#print axioms SCD.Direction.DirTransport.flat_iff_lie_hom
#print axioms SCD.Direction.DirTransport.curv_of_abelian
#print axioms SCD.Direction.DirTransport.commute_iff_bracket_acts_trivially
#print axioms SCD.Direction.DirTransport.transport_determined_by_generators

/-! ## Sector XXXIII — the other half of light deflection -/

#print axioms SCD.PPN.gamma_zero_is_isotropic
#print axioms SCD.PPN.gamma_one_is_observed
#print axioms SCD.PPN.reciprocal_expansion
#print axioms SCD.PPN.gamma_eq_one_of_reciprocal
#print axioms SCD.PPN.gamma_eq_one_first_order
#print axioms SCD.PPN.deflection_reciprocal_eq_observed
#print axioms SCD.PPN.halves_equal

/-! ## Sector XXXIV — defect codimension: the framework predicts strings -/

#print axioms SCD.Codimension.pointlike_iff_two_dim
#print axioms SCD.Codimension.three_dim_gives_strings
#print axioms SCD.Codimension.pointlike_forces_three
#print axioms SCD.Codimension.no_pointlike_in_four
#print axioms SCD.Codimension.string_mass_not_topological
#print axioms SCD.Codimension.stringMass_strictMono
#print axioms SCD.Codimension.extended_or_low_dimensional

/-! ## Sector XXXV — reciprocity fixed by asymptotic flatness -/

#print axioms SCD.Vacuum.const_of_deriv_zero_and_vanishing
#print axioms SCD.Vacuum.reciprocity_of_asymptotic_flatness
#print axioms SCD.Vacuum.scale_product_eq_one
#print axioms SCD.Vacuum.product_constant_without_flatness
#print axioms SCD.Vacuum.tr_area_element_constant

/-! ## Sector XXXVI — point particles restored by the directional scale -/

#print axioms SCD.Axis.bareForm_neg
#print axioms SCD.Axis.physForm_neg
#print axioms SCD.Axis.neg_indistinguishable
#print axioms SCD.Axis.isotropic_no_order_parameter
#print axioms SCD.Axis.nondegenerate_full_frame
#print axioms SCD.Axis.uniaxial_stabilizer
#print axioms SCD.Axis.uniaxial_axis_distinguished

/-! ## Sector XXXVII — two topological charges, one confined -/

#print axioms SCD.Charges.DefectCharge.block_confined
#print axioms SCD.Charges.DefectCharge.hedgehog_free
#print axioms SCD.Charges.DefectCharge.exactly_one_confined
#print axioms SCD.Charges.DefectCharge.charges_independent
#print axioms SCD.Charges.DefectCharge.observable_pair_any_hedgehog

/-! ## Sector XXXVIII — Mercury perihelion -/

#print axioms SCD.Precession.coeff_reciprocal
#print axioms SCD.Precession.coeff_isotropic
#print axioms SCD.Precession.isotropic_is_third
#print axioms SCD.Precession.mercury_value
#print axioms SCD.Precession.mercury_isotropic_value

/-! ## Sector XXXIX — audit: the colour block is not the spatial block -/

#print axioms SCD.ColorAudit.identification_predicts_two
#print axioms SCD.ColorAudit.identification_fails_baryon
#print axioms SCD.ColorAudit.identification_fails_charge
#print axioms SCD.ColorAudit.spatial_block_is_not_colour_block
#print axioms SCD.ColorAudit.three_matches_charge

/-! ## Sector XL — the Ricci cancellation closing the gravity chain -/

#print axioms SCD.Schwarzschild.ricci_combination
#print axioms SCD.Schwarzschild.vacuum_log_derivative
#print axioms SCD.Schwarzschild.scale_sum_derivative_zero
#print axioms SCD.Schwarzschild.vacuum_iff_scale_sum_stationary
#print axioms SCD.Schwarzschild.area_element_stationary

/-! ## Sector XLI — gravity closed: Ricci from the connection -/

#print axioms SCD.RicciDiag.ricciTT_eq
#print axioms SCD.RicciDiag.ricciRR_eq
#print axioms SCD.RicciDiag.gravity_chain
#print axioms SCD.RicciDiag.area_stationary_derived

/-! ## Sector XLII — content is a slice: no fundamental particles -/

#print axioms SCD.Emergence.resolved_mono
#print axioms SCD.Emergence.content_never_complete
#print axioms SCD.Emergence.always_more_above
#print axioms SCD.Emergence.no_fundamental_list
#print axioms SCD.Emergence.mass_iff_threshold
#print axioms SCD.Emergence.mass_mono
#print axioms SCD.Emergence.content_eq_of_no_threshold
#print axioms SCD.Emergence.content_changes_only_at_threshold

/-! ## Sector XLIII — the threshold-structure prediction and its data test -/

#print axioms SCD.Spectrum.mass_threshold_inverse
#print axioms SCD.Spectrum.equal_gaps_variance_zero
#print axioms SCD.Spectrum.observed_cvSq_value
#print axioms SCD.Spectrum.meanGap_value
#print axioms SCD.Spectrum.observed_not_geometric
#print axioms SCD.Spectrum.observed_within_scale_invariant_range
#print axioms SCD.Spectrum.densityFromGaps_value
#print axioms SCD.Spectrum.density_gap_inverse

/-! ## Sector XLIV — audit: the proposed cross-sector test does not exist -/

#print axioms SCD.CrossCheck.rhoAll_value
#print axioms SCD.CrossCheck.rhoQuark_value
#print axioms SCD.CrossCheck.densities_differ
#print axioms SCD.CrossCheck.density_ratio_near_two
#print axioms SCD.CrossCheck.sector_relation_is_identity
#print axioms SCD.CrossCheck.no_second_determination
#print axioms SCD.CrossCheck.quarkCvSq_value
#print axioms SCD.CrossCheck.quark_not_geometric

/-! ## Sector XLV — what the framework can express at all -/

#print axioms SCD.Expressive.invariant_factors
#print axioms SCD.Expressive.diffPattern_invariant
#print axioms SCD.Expressive.invariant_iff_diffPattern
#print axioms SCD.Expressive.eval_not_invariant
#print axioms SCD.Expressive.scale_says_nothing_about_rotation
#print axioms SCD.Expressive.rotation_says_nothing_about_scale
#print axioms SCD.Expressive.channels_independent
#print axioms SCD.Expressive.neither_channel_complete

/-! ## Sector XLVI — the scale/rotation coupling, derived -/

#print axioms SCD.Coupling.bracket_scaling_scaling
#print axioms SCD.Coupling.bracket_rotation_scaling
#print axioms SCD.Coupling.bracket_rotation_rotation
#print axioms SCD.Coupling.coupling_structure
#print axioms SCD.Coupling.no_rotation_of_commuting
#print axioms SCD.Coupling.boost_bracket_eq_rotation
#print axioms SCD.Coupling.scalings_do_not_commute

/-! ## Sector XLVII — dynamics from the coupling -/

#print axioms SCD.Dynamics.no_flatness_from_commuting_derivations
#print axioms SCD.Dynamics.nonflat_witness
#print axioms SCD.Dynamics.commutative_sector_transports_commute
#print axioms SCD.Dynamics.commutative_curvature_undetectable
#print axioms SCD.Dynamics.source_conserved_of_field_equation
#print axioms SCD.Dynamics.no_field_equation_of_nonconserved
#print axioms SCD.Dynamics.source_antisymm
#print axioms SCD.Dynamics.field_equation_content
#print axioms SCD.Dynamics.same_multiplet_no_rotation
#print axioms SCD.Dynamics.rotation_implies_different_multiplet
#print axioms SCD.Dynamics.larger_multiplet_fewer_generators
#print axioms SCD.Dynamics.multiplet_change_needs_pattern_change

/-! ## Sector XLVIII — which algebra: real rank one -/

#print axioms SCD.Algebra.scaling_rotation_orthogonal
#print axioms SCD.Algebra.boost_isScaling
#print axioms SCD.Algebra.boost_add
#print axioms SCD.Algebra.boost_smul
#print axioms SCD.Algebra.boost_mul_succ_succ
#print axioms SCD.Algebra.boost_bracket_spatial
#print axioms SCD.Algebra.boosts_commute_iff_parallel
#print axioms SCD.Algebra.commuting_boosts_lie_on_a_line
#print axioms SCD.Algebra.commuting_family_one_parameter
#print axioms SCD.Algebra.no_two_dimensional_commuting_family
#print axioms SCD.Algebra.commuting_drifts_proportional
#print axioms SCD.Algebra.boost_eq_zero_iff

/-! ## Sector XLIX — the particle model the algebra allows -/

#print axioms SCD.Particle.boost_injective
#print axioms SCD.Particle.pattern_is_one_vector
#print axioms SCD.Particle.mixture_second_moment
#print axioms SCD.Particle.mixture_cvSq_ge_one
#print axioms SCD.Particle.mixture_cvSq_eq_one_iff
#print axioms SCD.Particle.observed_disfavours_higher_rank
#print axioms SCD.Particle.rate_value_not_fixed
#print axioms SCD.Particle.block_two_valued
#print axioms SCD.Particle.block_cannot_be_three_valued
#print axioms SCD.Particle.block_self_inverse
#print axioms SCD.Particle.two_odd_make_even
#print axioms SCD.Particle.hedgehog_conserved_in_splitting
#print axioms SCD.Particle.no_further_label
#print axioms SCD.Particle.particle_label_structure

/-! ## Sector L — slice artifacts, rotation, and why three -/

#print axioms SCD.Slice.newContent_nonempty_of_threshold
#print axioms SCD.Slice.newContent_mono
#print axioms SCD.Slice.newContent_empty_of_no_threshold
#print axioms SCD.Slice.no_finite_universal_labelling
#print axioms SCD.Slice.label_count_measures_range
#print axioms SCD.Slice.wedge_eq_bracket
#print axioms SCD.Slice.wedge_bilinear_left
#print axioms SCD.Slice.wedge_eq_zero_iff_parallel
#print axioms SCD.Slice.homogeneous_carries_no_rotation
#print axioms SCD.Slice.rotation_requires_biaxial
#print axioms SCD.Slice.wedge_dim_eq_iff
#print axioms SCD.Slice.three_is_unique
#print axioms SCD.Slice.more_wedges_than_directions
#print axioms SCD.Slice.fewer_wedges_than_directions

/-! ## Sector LI — the axis question, settled -/

#print axioms SCD.Axes.rotation_needs_variation
#print axioms SCD.Axes.combable_no_rotation
#print axioms SCD.Axes.wound_carries_rotation
#print axioms SCD.Axes.rotationless_is_trivial
#print axioms SCD.Axes.rotation_iff_variation
#print axioms SCD.Axes.no_second_axis
#print axioms SCD.Axes.axis_or_variation
#print axioms SCD.Axes.axis_stabilizer_nontrivial
#print axioms SCD.Axes.multiplet_flatness_needs_per_direction_scalings

/-! ## Sector LII — the last two inputs -/

#print axioms SCD.Dimension.algebra_bigger_than_directions
#print axioms SCD.Dimension.rep_dim_determined
#print axioms SCD.Dimension.rot_matches_scale_iff
#print axioms SCD.Dimension.alg_matches_rep_iff
#print axioms SCD.Dimension.two_matching_conditions_differ
#print axioms SCD.Dimension.wedge_smul_both
#print axioms SCD.Dimension.wedge_ratio_invariant
#print axioms SCD.Dimension.only_ratios_are_fixed
#print axioms SCD.Dimension.density_normalization_relation
#print axioms SCD.Dimension.normalization_returns_input

/-! ## Sector LIII — A7, and the locus audit -/

#print axioms SCD.Locus.three_from_observability
#print axioms SCD.Locus.observability_fails_elsewhere
#print axioms SCD.Locus.observability_iff_three
#print axioms SCD.Locus.no_scale_invariant_interaction
#print axioms SCD.Locus.constant_coupling_iff_no_content
#print axioms SCD.Locus.isotropic_pair_parallel
#print axioms SCD.Locus.isotropic_no_rotation
#print axioms SCD.Locus.labels_require_anisotropy
#print axioms SCD.Locus.everything_switches_on_together
#print axioms SCD.Locus.particle_locus_is_anisotropic

/-! ## Sector LIV — what the position predicts -/

#print axioms SCD.Cosmos.shift_invariant_is_constant
#print axioms SCD.Cosmos.rate_constant_of_fiducial_invariance
#print axioms SCD.Cosmos.w_does_not_evolve
#print axioms SCD.Cosmos.scale_ratio_depends_only_on_difference
#print axioms SCD.Cosmos.no_first_moment
#print axioms SCD.Cosmos.finite_lookback_no_origin
#print axioms SCD.Cosmos.isotropic_gravitates_without_labels
#print axioms SCD.Cosmos.dark_matter_has_no_species
#print axioms SCD.Cosmos.resolvable_needs_width_below_gap
#print axioms SCD.Cosmos.broad_structures_unresolvable
#print axioms SCD.Cosmos.resolvability_boundary

/-! ## Sector LV — the non-commutative curvature, and the first correction -/

#print axioms SCD.NCConformal.hess_symm
#print axioms SCD.NCConformal.Chr_symm
#print axioms SCD.NCConformal.Defm_antisymm_part
#print axioms SCD.NCConformal.Defm_symm_iff_commutator
#print axioms SCD.NCConformal.Defm_symm_iff_commute
#print axioms SCD.NCConformal.symmetric_part_uncorrected
#print axioms SCD.NCConformal.correction_is_pure_antisymmetric
#print axioms SCD.NCConformal.sum_Chr_Chr_full_nc
#print axioms SCD.NCConformal.sum_Chr_Chr_full_classical
#print axioms SCD.NCConformal.quantum_correction_couples_to_rotation
#print axioms SCD.NCConformal.correction_vanishes_on_commuting
#print axioms SCD.Cosmos.two_dark_routes_differ

/-! ## Sector LVI — black holes, waves, and the borrowed questions -/

#print axioms SCD.Horizon.gtt_ne_zero
#print axioms SCD.Horizon.reciprocal_never_degenerate
#print axioms SCD.Horizon.redshift_never_infinite
#print axioms SCD.Horizon.no_degeneracy_anywhere
#print axioms SCD.Horizon.null_cone_scale_independent
#print axioms SCD.Horizon.waves_travel_on_the_light_cone
#print axioms SCD.Horizon.no_energy_dependent_speed
#print axioms SCD.Horizon.entropy_of_scale_ratio
#print axioms SCD.Horizon.entropy_doubling_is_additive
#print axioms SCD.Horizon.entropy_increment_independent_of_size
#print axioms SCD.Horizon.no_minimum_length
#print axioms SCD.Horizon.no_final_description

/-! ## Sector LVII — the framework asking its own questions -/

#print axioms SCD.Native.not_two_places_of_parallel
#print axioms SCD.Native.separation_is_oriented
#print axioms SCD.Native.single_anisotropy_boundary
#print axioms SCD.Native.label_forces_anisotropy
#print axioms SCD.Native.zero_window_resolves_nothing
#print axioms SCD.Native.content_is_interval_valued
#print axioms SCD.Native.no_global_field_equation
#print axioms SCD.Native.ordering_discrepancy_is_the_observable
#print axioms SCD.Native.parity_conserved_under_binding
#print axioms SCD.Native.both_labels_conserved
#print axioms SCD.Native.no_maximum_anisotropy
#print axioms SCD.Native.no_cutoff_either_end

/-! ## Sector LVIII — confronting the data -/

#print axioms SCD.Data.desi_tension_exceeds_three_sigma
#print axioms SCD.Data.desi_significance_dataset_dependent
#print axioms SCD.Data.falsification_threshold
#print axioms SCD.Data.kappa_below_bound
#print axioms SCD.Data.rho_below_bound
#print axioms SCD.Data.delta_below_bound
#print axioms SCD.Data.z_boson_far_inside
#print axioms SCD.Data.ccl_above_bound
#print axioms SCD.Data.gkpy_below_bound
#print axioms SCD.Data.determinations_straddle_bound
#print axioms SCD.Data.gkpy_updated_inside
#print axioms SCD.Data.desi_combinations_disagree_internally
#print axioms SCD.Data.bound_separates_kappa_from_sigma
#print axioms SCD.Data.breit_wigner_spans_the_bound
#print axioms SCD.Data.dispersion_limit_above_planck
#print axioms SCD.Data.one_charge_prediction
#print axioms SCD.Data.zero_nu_beta_beta_decides
#print axioms SCD.Data.scorecard

/-! ## Sector IX — light -/

#print axioms SCD.Light.isNull_iff_bare
#print axioms SCD.Light.isNull_scale_invariant
#print axioms SCD.Light.scale_determined_of_nonnull
#print axioms SCD.Light.physForm_ne_bareForm
#print axioms SCD.Light.null_weight_zero

end SCD.Verify
