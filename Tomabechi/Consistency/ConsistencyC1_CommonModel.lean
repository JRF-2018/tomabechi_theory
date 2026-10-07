import Tomabechi.Consistency.ConsistencyC1_O24
import Tomabechi.Consistency.ConsistencyC1_Theorem3Bridge
import Tomabechi.Consistency.ConsistencyC1_DataIdentifications
import Tomabechi.Consistency.ConsistencyR1_C1Information
import Tomabechi.Consistency.ConsistencyR3_CommonBase

/-!
# C1 common rate-3 two-agent model

This module bundles the proved Theorem 1, 2, 4, 20, O02, and O24 instances
around one rate-3 consensus flow. The Euclidean-space trajectory in Theorem 20
is the coordinate transport of the same function-space trajectory.
-/

noncomputable section

namespace Tomabechi.Consistency.ConsistencyC1CommonModel

open Filter
open scoped Topology
open Tomabechi.Theorem1
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1O24
open Tomabechi.Consistency.ConsistencyC1Theorem3Bridge
open Tomabechi.Consistency.ConsistencyC1DataIdentifications
open Tomabechi.Theorem3
open Tomabechi.Examples.Theorem2

/-- The entry-level quantitative results returned by the common C1 model,
separated by theorem so that callers can inspect each claim by name. -/
structure C1EntryConclusions (x : AgentState) (t₀ T : ℝ) where
  shared_base_matches_theorem1 : ∀ t,
    Tomabechi.Consistency.R3.commonBaseContract.V0 x t = consensusV0 x t
  shared_base_theorem4_effective : ∀ t,
    Theorem4.effectivePotential
        (Tomabechi.Consistency.R3.commonBaseContract.V0 x t)
        (Tomabechi.Consistency.R3.commonBasePresenceP x t)
        (Tomabechi.Consistency.R3.commonBasePresenceQ x t) 1 =
      Tomabechi.Consistency.R3.commonBaseTheorem4Effective x t
  shared_base_theorem4_effective_decay : ∀ s, t₀ ≤ s →
    Tomabechi.Consistency.R3.commonBaseTheorem4Effective
        (consensusOptimalFlow.flow t₀ x s) s ≤
      2 * Tomabechi.Consistency.R3.commonBaseTheorem4Effective x t₀ *
        Real.exp (-6 * (s - t₀))
  shared_base_theorem4_cost_argmin : x ∈ box → ∀ u : C1GainSignal,
    Tomabechi.Consistency.R3.commonBaseTheorem4FiniteHorizonCost
        x t₀ T c1MaxGainSignal ≤
      Tomabechi.Consistency.R3.commonBaseTheorem4FiniteHorizonCost x t₀ T u
  shared_base_theorem20_box_value :
    Tomabechi.Consistency.R3.commonBaseContract.V0 x 0 =
      1 + 2 * Tomabechi.Consistency.R3.commonBaseD x
  shared_base_theorem20_excess_euclidean_distance : x ∈ box →
    Tomabechi.Consistency.R3.commonBaseTheorem20Effective x - 1 =
      12 * c1EuclideanSymbolDistance (WithLp.toLp 2 x)
  shared_base_theorem20_effective_excess_decay : ∀ s, t₀ ≤ s →
    Tomabechi.Consistency.R3.commonBaseTheorem20Effective
        (consensusOptimalFlow.flow t₀ x s) - 1 =
      (Tomabechi.Consistency.R3.commonBaseTheorem20Effective x - 1) *
        Real.exp (-6 * (s - t₀))
  shared_base_theorem20_cost_argmin : x ∈ box → ∀ u : C1GainSignal,
    Tomabechi.Consistency.R3.commonBaseTheorem20FiniteHorizonCost
        x t₀ T c1MaxGainSignal ≤
      Tomabechi.Consistency.R3.commonBaseTheorem20FiniteHorizonCost x t₀ T u
  shared_base_theorem20_minimum_target : ∀ t, t₀ ≤ t →
    (Tomabechi.Consistency.R3.commonBaseTheorem20Effective
      (consensusOptimalFlow.flow t₀ x t) - 1 ≤ 0 ↔
      WithLp.toLp 2 (consensusOptimalFlow.flow t₀ x t) ∈ c1EuclideanSymbolTarget)
  theorem1_reachable : ∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈
    closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀)
  theorem1_distance : ∀ t, t₀ ≤ t → Metric.infDist
    (consensusOptimalFlow.flow t₀ x t) (consensusOptimalTheorem1Target t₀ t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))
  theorem1_tendsto : Filter.Tendsto
    (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (consensusOptimalTheorem1Target t₀ t)) atTop (𝓝 0)
  theorem2_shared_distance : ∀ t, t₀ ≤ t → Metric.infDist
    (consensusOptimalFlow.flow t₀ x t) (DA.sharedTCZ box t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))
  theorem2_individual_residual : ∀ t, t₀ ≤ t → ∀ i,
    DA.individual i ((consensusOptimalFlow.flow t₀ x t) i) t ≤
      (DA.potential x t₀ / DA.individualWeight i) * Real.exp (-6 * (t - t₀))
  theorem2_edge_mismatch : ∀ t, t₀ ≤ t → ∀ e,
    DA.mismatch e ((consensusOptimalFlow.flow t₀ x t) (DA.endpoint e).1)
      ((consensusOptimalFlow.flow t₀ x t) (DA.endpoint e).2) t ≤
      (DA.potential x t₀ / DA.edgeWeight e) * Real.exp (-6 * (t - t₀))
  theorem4_reachable : ∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈
    closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀)
  theorem4_weighted_distance : ∀ t, t₀ ≤ t → Metric.infDist
    (consensusOptimalFlow.flow t₀ x t)
    (Theorem4.weightedTCZ
      (closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀))
      consensusPresenceV0 consensusPresenceP consensusPresenceQ 1 1 t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))
  shared_base_theorem4_weighted_distance : ∀ t, t₀ ≤ t → Metric.infDist
    (consensusOptimalFlow.flow t₀ x t)
    (Theorem4.weightedTCZ
      (closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀))
      Tomabechi.Consistency.R3.commonBaseV0
      Tomabechi.Consistency.R3.commonBasePresenceP
      Tomabechi.Consistency.R3.commonBasePresenceQ 1 0 t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))
  theorem4_tendsto : Filter.Tendsto
    (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (Theorem4.weightedTCZ
        (closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀))
        consensusPresenceV0 consensusPresenceP consensusPresenceQ 1 1 t))
      atTop (𝓝 0)
  baselineCost_argmin : ∀ u : C1GainSignal,
    consensusFiniteHorizonCost x t₀ T c1MaxGainSignal ≤
      consensusFiniteHorizonCost x t₀ T u
  theorem1Cost_argmin : ∀ u : C1GainSignal,
    consensusTheorem1HorizonCost x t₀ T c1MaxGainSignal ≤
      consensusTheorem1HorizonCost x t₀ T u
  theorem1Cost_finite : consensusTheorem1HorizonCost x t₀ T c1MaxGainSignal < ⊤
  o24_distance : ∀ t, t₀ ≤ t → Metric.infDist
    ((optimalConsensusSelfEgoTCZAdapter t₀).flow.flow t₀ x t)
    ((optimalConsensusSelfEgoTCZAdapter t₀).TCZ t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))
  theorem20_distanceSquared : ∀ t, t₀ ≤ t →
    c1EuclideanSymbolDistance
      (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t) ≤
      c1EuclideanSymbolDistance
        (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t₀) *
        Real.exp (-(t - t₀))
  theorem20_distance : ∀ t, t₀ ≤ t → Metric.infDist
    (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t)
    c1EuclideanSymbolTarget ≤
      2 * Real.sqrt (c1EuclideanSymbolDistance
        (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t₀)) *
        Real.exp (-((1 / 2 : ℝ) * (t - t₀)))
  theorem20_tendsto : Filter.Tendsto
    (fun t => Metric.infDist
      (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t)
      c1EuclideanSymbolTarget) atTop (𝓝 0)

/-- The concrete O13 symbolic and Euclidean premises kept together as a
separate audit object. The theorem 20 wrapper's (20.A/B), PL, compactness,
invariance, and distance-error inputs are represented by the actual applied
entry conclusion stored in `C1EntryConclusions`. -/
structure C1O13Witness where
  common_information_bottom :
    (⊥ : Tomabechi.Consistency.R1.CommonConcept) ∈
      Tomabechi.Consistency.R1.c1InformationImage
  common_information_join : ∀ {a b : Tomabechi.Consistency.R1.CommonConcept},
    a ∈ Tomabechi.Consistency.R1.c1InformationImage →
      b ∈ Tomabechi.Consistency.R1.c1InformationImage →
        a ⊔ b ∈ Tomabechi.Consistency.R1.c1InformationImage
  common_information_meet : ∀ {a b : Tomabechi.Consistency.R1.CommonConcept},
    a ∈ Tomabechi.Consistency.R1.c1InformationImage →
      b ∈ Tomabechi.Consistency.R1.c1InformationImage →
        a ⊓ b ∈ Tomabechi.Consistency.R1.c1InformationImage
  common_information_proper :
    Tomabechi.Consistency.R1.c1InformationImage ≠ Set.univ
  common_selected_symbols_in_information :
    Tomabechi.Consistency.R1.c1SymbolImage ⊆
      Tomabechi.Consistency.R1.c1InformationImage
  common_symbol_address_is_lub : IsLUB
    Tomabechi.Consistency.R1.c1SymbolImage
    Tomabechi.Consistency.R1.c1SymbolAddressImage
  common_information_law_bottom :
    Tomabechi.Consistency.R1.commonConceptInformationLaw
      (⊥ : Tomabechi.Consistency.R1.CommonConcept) =
      Tomabechi.Consistency.C3.physicalLayerLaw.joint
  common_information_law_nonbottom : ∀ {a : Tomabechi.Consistency.R1.CommonConcept},
    a ≠ ⊥ → Tomabechi.Consistency.R1.commonConceptInformationLaw a =
      Tomabechi.Consistency.C3.upperJoint
  common_information_pair_joint : ∀ a : Tomabechi.Consistency.R1.CommonConcept,
    Tomabechi.Theorem19_22.directActionGoalJoint
        (Tomabechi.Consistency.R1.commonConceptInformationLaw a) =
      (Tomabechi.Consistency.R1.commonConceptInformationPair a).joint
  common_information_pair_reference : ∀ (a : Tomabechi.Consistency.R1.CommonConcept)
    [MeasureTheory.IsProbabilityMeasure
      (Tomabechi.Consistency.R1.commonConceptInformationLaw a)],
    Tomabechi.Theorem19_22.directCMIReference
        (Tomabechi.Consistency.R1.commonConceptInformationLaw a) =
      (Tomabechi.Consistency.R1.commonConceptInformationPair a).reference
  common_information_score_bottom :
    Tomabechi.Consistency.C3.cmiPairScore
      (Tomabechi.Consistency.R1.commonConceptInformationPair
        (⊥ : Tomabechi.Consistency.R1.CommonConcept)) = 0
  common_information_score_nonbottom : ∀ {a : Tomabechi.Consistency.R1.CommonConcept},
    a ≠ ⊥ → Tomabechi.Consistency.C3.cmiPairScore
      (Tomabechi.Consistency.R1.commonConceptInformationPair a) = Real.log 2
  common_information_score_positive_nonbottom :
    ∀ {a : Tomabechi.Consistency.R1.CommonConcept}, a ≠ ⊥ →
      0 < Tomabechi.Consistency.C3.cmiPairScore
        (Tomabechi.Consistency.R1.commonConceptInformationPair a)
  common_information_recovers_physical_address :
    Tomabechi.Consistency.R1.commonConceptInformationLaw
      (Tomabechi.Consistency.R1.layerAddressEmbedding (0 : WithTop ℕ)) =
      Tomabechi.Consistency.C3.physicalLayerLaw.joint
  common_information_recovers_upper_addresses : ∀ n : ℕ,
    Tomabechi.Consistency.R1.commonConceptInformationLaw
      (Tomabechi.Consistency.R1.layerAddressEmbedding ((n + 1 : ℕ) : WithTop ℕ)) =
      Tomabechi.Consistency.C3.upperJoint
  information_bottom : (∅ : C1SymbolConcept) ∈ c1SymbolInfoLattice
  information_join : ∀ {a b : C1SymbolConcept},
    a ∈ c1SymbolInfoLattice → b ∈ c1SymbolInfoLattice →
      a ∪ b ∈ c1SymbolInfoLattice
  information_meet : ∀ {a b : C1SymbolConcept},
    a ∈ c1SymbolInfoLattice → b ∈ c1SymbolInfoLattice →
      a ∩ b ∈ c1SymbolInfoLattice
  information_proper : ∀ (i : Fin 2) (t : ℝ),
    c1AvailableInformation i t ⊆ Set.univ ∧
      c1AvailableInformation i t ≠ Set.univ
  selected_symbols_in_information : c1SymbolW ⊆ c1SymbolInfoLattice
  symbol_address_is_lub :
    (∀ w ∈ c1SymbolW, w ⊆ c1SymbolAddress) ∧
      ∀ b, (∀ w ∈ c1SymbolW, w ⊆ b) → c1SymbolAddress ⊆ b
  symbolic_target_nonempty : (c1SymbolTarget c1SymbolAddress).Nonempty
  symbolic_target_closed : IsClosed (c1SymbolTarget c1SymbolAddress)
  symbolic_distance_nonnegative : ∀ x, 0 ≤ c1SymbolDistance x
  symbolic_distance_zero_iff : ∀ x,
    c1SymbolDistance x = 0 ↔ x ∈ c1SymbolTarget c1SymbolAddress
  symbolic_distance_matches_shared_potential_on_box :
    ∀ (x : AgentState) (hx : x ∈ box) (t : ℝ),
      c1SymbolDistance x = (1 / 8 : ℝ) * DA.potential x t
  symbolic_target_matches_reachable_target : ∀ t,
    {x : AgentState | x ∈ box ∧ x ∈ c1SymbolTarget c1SymbolAddress} =
      DA.sharedTCZ box t
  symbolic_distance_smooth : ContDiff ℝ 1 c1SymbolDistance
  base_presence_range : ∀ x t,
    c1SymbolBasePresence x t ∈ Set.Icc 0 1
  amplified_presence_value : ∀ x t,
    c1SymbolPresence c1SymbolAddress x t = 1
  amplification_value : ∀ x t,
    c1SymbolAmplification c1SymbolAddress x t = 1
  amplification_nonnegative : 0 ≤ c1SymbolLambda
  amplification_positive : 0 < c1SymbolLambda
  presence_amplification_formula : ∀ (u : C1SymbolConcept) (x : AgentState) (t : ℝ),
    c1SymbolPresence u x t =
      c1SymbolBasePresence x t + c1SymbolLambda * c1SymbolAmplification u x t
  base_presence_zero : ∀ x t, c1SymbolBasePresence x t = 0
  presence_range : ∀ x t,
    0 ≤ c1SymbolPresence c1SymbolAddress x t ∧
      c1SymbolPresence c1SymbolAddress x t ≤ 1
  q_range : ∀ u x t, c1SymbolQ u x t ∈ Set.Icc (-1) 1
  q_positive : ∀ u x t, 0 < c1SymbolQ u x t
  selected_q_is_one : ∀ x t, c1SymbolQ c1SymbolAddress x t = 1
  base_potential_smooth : ∀ t,
    ContDiff ℝ 1 (fun x => c1SymbolV0 x t)
  selected_presence_smooth : ∀ t,
    ContDiff ℝ 1 (fun x => c1SymbolPresence c1SymbolAddress x t)
  slope_smooth : ContDiff ℝ 1 c1SymbolSlope
  slope_derivative : ∀ d, HasDerivAt c1SymbolSlope (-1) d
  effective_potential_formula : ∀ (x : AgentState) (t : ℝ),
    c1SymbolEffectivePotential x = 3 * c1SymbolDistance x
  effective_potential_decay : ∀ (x : AgentState) (t₀ t : ℝ),
    c1SymbolEffectivePotential (consensusOptimalFlow.flow t₀ x t) =
      c1SymbolEffectivePotential x * Real.exp (-6 * (t - t₀))
  euclidean_target_nonempty : c1EuclideanSymbolTarget.Nonempty
  euclidean_target_closed : IsClosed c1EuclideanSymbolTarget
  euclidean_distance_nonnegative : ∀ x, 0 ≤ c1EuclideanSymbolDistance x
  euclidean_distance_zero_iff : ∀ x,
    c1EuclideanSymbolDistance x = 0 ↔ x ∈ c1EuclideanSymbolTarget
  euclidean_distance_gradient : ∀ x,
    HasGradientAt c1EuclideanSymbolDistance
      (c1EuclideanSymbolDistanceGradient x) x
  euclidean_base_potential_gradient : ∀ x,
    HasGradientAt (fun y => 2 * c1EuclideanSymbolDistance y)
      ((2 : ℝ) • c1EuclideanSymbolDistanceGradient x) x
  euclidean_presence_gradient : ∀ x,
    HasGradientAt (fun _ : C1EuclideanAgentState => (1 : ℝ))
      (0 : C1EuclideanAgentState) x
  euclidean_effective_potential_gradient : ∀ x,
    HasGradientAt (fun y => 3 * c1EuclideanSymbolDistance y)
      ((3 : ℕ) • c1EuclideanSymbolDistanceGradient x) x
  euclidean_distance_error : ∀ x,
    Metric.infDist x c1EuclideanSymbolTarget ≤
      2 * Real.sqrt (c1EuclideanSymbolDistance x)
  identity_mobility_left_inverse : ∀ (r : ℝ) (y : C1EuclideanAgentState),
    (ContinuousLinearMap.id ℝ C1EuclideanAgentState)
        ((ContinuousLinearMap.id ℝ C1EuclideanAgentState) y) = y
  identity_mobility_symmetric : ∀ (y z : C1EuclideanAgentState),
    inner ℝ y ((ContinuousLinearMap.id ℝ C1EuclideanAgentState) z) =
      inner ℝ ((ContinuousLinearMap.id ℝ C1EuclideanAgentState) y) z
  identity_mobility_coercive : ∀ (r : ℝ) (y : C1EuclideanAgentState),
    (1 : ℝ) * ‖y‖ ^ 2 ≤
      inner ℝ y ((ContinuousLinearMap.id ℝ C1EuclideanAgentState) y)
  identity_mobility_continuous : Continuous
    (fun _ : ℝ => ContinuousLinearMap.id ℝ C1EuclideanAgentState)
  theorem20_condition_A : ∀ (x : C1EuclideanAgentState),
    -inner ℝ (c1EuclideanSymbolDistanceGradient x)
        ((2 : ℝ) • c1EuclideanSymbolDistanceGradient x) +
      1 * 1 * (-c1EuclideanSymbolDistance x) *
        inner ℝ (c1EuclideanSymbolDistanceGradient x) (0 : C1EuclideanAgentState) ≤
      (1 / 2 : ℝ) * inner ℝ (c1EuclideanSymbolDistanceGradient x)
        (c1EuclideanSymbolDistanceGradient x)
  theorem20_condition_B :
    (1 : ℝ) * 1 * 1 * -(-1 : ℝ) ≥ (1 / 2 : ℝ) + (1 / 2 : ℝ)
  theorem20_PL : ∀ (x : C1EuclideanAgentState),
    2 * 1 * c1EuclideanSymbolDistance x ≤
      inner ℝ (c1EuclideanSymbolDistanceGradient x)
        (c1EuclideanSymbolDistanceGradient x)
  effective_field_is_negative_gradient : ∀ (x : C1EuclideanAgentState) (t : ℝ),
    euclideanConsensusOptimalFlow.vectorField x
        (euclideanConsensusOptimalFlow.feedback x t) t =
      -3 • c1EuclideanSymbolDistanceGradient x
  euclidean_initial_region_compact : IsCompact c1EuclideanBox
  euclidean_flow_forward_invariant : ∀ (x : C1EuclideanAgentState)
      (hx : x ∈ c1EuclideanBox) (t₀ t : ℝ), t₀ ≤ t →
      euclideanConsensusOptimalFlow.flow t₀ x t ∈ c1EuclideanBox
  euclidean_reachable_closure : ∀ (t₀ : ℝ), 0 ≤ t₀ →
    closedLoopReachableSet
      (policyFlowReachableAt euclideanConsensusOptimalFlow c1EuclideanBox t₀) =
        c1EuclideanBox
  closed_loop_field_smooth : ∀ t,
    ContDiff ℝ 1 (fun x : C1EuclideanAgentState =>
      euclideanConsensusOptimalFlow.vectorField x
        (euclideanConsensusOptimalFlow.feedback x t) t)
  closed_loop_field_locally_lipschitz : ∀ t,
    LocallyLipschitz (fun x : C1EuclideanAgentState =>
      euclideanConsensusOptimalFlow.vectorField x
        (euclideanConsensusOptimalFlow.feedback x t) t)

/-- Typed record of the concrete C1 model data and obligations that are not
captured by the conclusion bundle below. The universal entry conclusions for
Theorems 1, 2, 4, and 20 remain available from their named wrappers; this record
stores the control-selection premises, actual Theorem 1 cost facts, the
Theorem 3 full-`Φ₃` result on its invariant slice, O13 regularity, and only the
cross-context equalities required by C1. -/
structure C1Witness where
  initialRegion : Set AgentState
  initialRegion_eq_box : initialRegion = box
  selectedGain : C1GainSignal
  selectedGain_eq_maximum : selectedGain = c1MaxGainSignal
  selectedHorizonController : ℝ × AgentState → ℝ → ℝ
  selectedController_matches_gain : ∀ (p : ℝ × AgentState) (s : ℝ),
    selectedHorizonController p s = selectedGain.1 s
  selectedController_measurable : Measurable selectedHorizonController
  selectedController_rightLimit : ∀ (t₀ : ℝ) (x : AgentState),
    Tendsto (fun s => selectedHorizonController (t₀, x) s)
      (𝓝[>] t₀) (𝓝 (consensusOptimalFlow.feedback x t₀))
  selectedFlow : ClosedLoopPolicyFlow AgentState ℝ
  selectedFlow_eq_rate3 : selectedFlow = consensusOptimalFlow
  distinctAdmissibleControls : c1ZeroGainSignal ≠ c1MaxGainSignal
  nontrivialInitial : AgentState
  nontrivialInitial_eq : nontrivialInitial = c1Theorem3NontrivialInitial
  nontrivialInitial_in_box : nontrivialInitial ∈ initialRegion
  nontrivialInitial_zero_mean : nontrivialInitial 0 + nontrivialInitial 1 = 0
  nontrivialInitial_has_positive_abstract_residual :
    0 < c1Theorem3System.abstractResidual 0 (nontrivialInitial 0)
  selectedDifferentiableFlow : DifferentiableClosedLoopPolicyFlow AgentState ℝ
  selectedDifferentiableFlow_eq_rate3 :
    selectedDifferentiableFlow = differentiableConsensusOptimalFlow
  selectedGain_measurable : Measurable selectedGain.1
  selectedGain_rightLimit : ∀ (t₀ : ℝ) (x : AgentState),
    Tendsto (fun s => selectedGain.1 s)
      (𝓝[>] t₀) (𝓝 (consensusOptimalFlow.feedback x t₀))
  selectedOrbit_isFlow : ∀ (x : AgentState) (t₀ t : ℝ),
    selectedFlow.flow t₀ x t =
      controlledConsensusState x t₀ selectedGain t
  theorem1ActualCostArgmin : ∀ (x : AgentState) (hx : x ∈ box)
      (t₀ T : ℝ), 0 < T → ∀ u : C1GainSignal,
      consensusTheorem1HorizonCost x t₀ T c1MaxGainSignal ≤
        consensusTheorem1HorizonCost x t₀ T u
  theorem1ActualCostFinite : ∀ (x : AgentState) (hx : x ∈ box)
      (t₀ T : ℝ), 0 < T →
      consensusTheorem1HorizonCost x t₀ T c1MaxGainSignal < ⊤
  theorem3FullPotentialBound : ∀ (x : AgentState) (hx : x ∈ box)
      (hmean : x 0 + x 1 = 0) (i : Fin 2) (t₀ s : ℝ),
      0 ≤ t₀ → t₀ ≤ s →
      Metric.infDist (consensusOptimalFlow.flow t₀ x s)
          (c1Theorem3OriginalTCZ t₀ s) ≤
        Real.sqrt (c1Theorem3Potential x t₀ t₀) * Real.exp (-3 * (s - t₀)) ∧
      euclideanCoordinateNorm
          (c1Theorem3System.ι (c1Theorem3System.abstraction i
            ((consensusOptimalFlow.flow t₀ x s) i)) -
            c1Theorem3System.ι c1Theorem3System.lub) ≤
        Real.sqrt (c1Theorem3Potential x t₀ t₀ / c1Theorem3Weight i) *
          Real.exp (-3 * (s - t₀))
  theorem3FullPotentialTendsto : ∀ (x : AgentState) (hx : x ∈ box)
      (hmean : x 0 + x 1 = 0) (t₀ : ℝ), 0 ≤ t₀ →
      Filter.Tendsto
        (fun s => Metric.infDist (consensusOptimalFlow.flow t₀ x s)
          (c1Theorem3OriginalTCZ t₀ s)) atTop (𝓝 0) ∧
      ∀ i : Fin 2, Filter.Tendsto
        (fun s => euclideanCoordinateNorm
          (c1Theorem3System.ι (c1Theorem3System.abstraction i
            ((consensusOptimalFlow.flow t₀ x s) i)) -
            c1Theorem3System.ι c1Theorem3System.lub)) atTop (𝓝 0)
  theorem20ClosedLoopLocallyLipschitz : ∀ t : ℝ,
    LocallyLipschitz (fun x : C1EuclideanAgentState =>
      euclideanConsensusOptimalFlow.vectorField x
        (euclideanConsensusOptimalFlow.feedback x t) t)
  theorem2Error_allStates : ∀ (x : AgentState) (hx : x ∈ box) (t : ℝ),
    (Metric.infDist x (DA.sharedTCZ box t)) ^ 2 ≤ DA.potential x t
  theorem20Error_allStates : ∀ (x : C1EuclideanAgentState),
    Metric.infDist x c1EuclideanSymbolTarget ≤
      2 * Real.sqrt (c1EuclideanSymbolDistance x)
  sharedBaseCandidate : Tomabechi.Consistency.R3.C1CommonBaseContract
  o13Evidence : C1O13Witness
  allEntryConclusions : ∀ (x : AgentState) (hx : x ∈ box) (t₀ T : ℝ)
      (ht₀ : 0 ≤ t₀) (hT : 0 < T), C1EntryConclusions x t₀ T
  connections : ∀ (t₀ : ℝ) (ht₀ : 0 ≤ t₀), C1Connections t₀ ht₀

/-- Coordinate transport does not change the selected trajectory. -/
theorem euclidean_transport_is_same_flow
    (x : AgentState) (t₀ t : ℝ) :
    c1EuclideanCoordinates
        (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t) =
      consensusOptimalFlow.flow t₀ x t := by
  simpa [c1EuclideanCoordinates_toLp] using
    euclideanConsensusOptimalFlow_coordinates (WithLp.toLp 2 x) t₀ t

/-- One nontrivial initial state and finite horizon share the same selected
rate-3 flow across the main C1 entries. -/
theorem c1_rate3_common_model
    (x : AgentState) (hx : x ∈ box) (t₀ T : ℝ)
    (ht₀ : 0 ≤ t₀) (hT : 0 < T) :
    (∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈
      closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀)) ∧
    (∀ t, t₀ ≤ t → Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (consensusOptimalTheorem1Target t₀ t) ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))) ∧
    Filter.Tendsto (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (consensusOptimalTheorem1Target t₀ t)) atTop (𝓝 0) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist (consensusOptimalFlow.flow t₀ x t) (DA.sharedTCZ box t) ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀)) ∧
      (∀ i, DA.individual i ((consensusOptimalFlow.flow t₀ x t) i) t ≤
        (DA.potential x t₀ / DA.individualWeight i) * Real.exp (-6 * (t - t₀))) ∧
      (∀ e, DA.mismatch e
        ((consensusOptimalFlow.flow t₀ x t) (DA.endpoint e).1)
        ((consensusOptimalFlow.flow t₀ x t) (DA.endpoint e).2) t ≤
        (DA.potential x t₀ / DA.edgeWeight e) * Real.exp (-6 * (t - t₀)))) ∧
    (∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈
      closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀)) ∧
    (∀ t, t₀ ≤ t → Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (Theorem4.weightedTCZ
        (closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀))
        consensusPresenceV0 consensusPresenceP consensusPresenceQ 1 1 t) ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))) ∧
    Filter.Tendsto (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (Theorem4.weightedTCZ
        (closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀))
        consensusPresenceV0 consensusPresenceP consensusPresenceQ 1 1 t))
      atTop (𝓝 0) ∧
    (∀ u : C1GainSignal,
      consensusFiniteHorizonCost x t₀ T c1MaxGainSignal ≤
        consensusFiniteHorizonCost x t₀ T u) ∧
    (∀ u : C1GainSignal,
      consensusTheorem1HorizonCost x t₀ T c1MaxGainSignal ≤
        consensusTheorem1HorizonCost x t₀ T u) ∧
    consensusTheorem1HorizonCost x t₀ T c1MaxGainSignal < ⊤ ∧
    (∀ t, t₀ ≤ t → Metric.infDist
      ((optimalConsensusSelfEgoTCZAdapter t₀).flow.flow t₀ x t)
      ((optimalConsensusSelfEgoTCZAdapter t₀).TCZ t) ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))) ∧
    (∀ t, t₀ ≤ t →
      c1EuclideanSymbolDistance
        (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t) ≤
        c1EuclideanSymbolDistance
          (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t₀) *
          Real.exp (-(t - t₀)) ∧
      Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t)
        c1EuclideanSymbolTarget ≤
          2 * Real.sqrt (c1EuclideanSymbolDistance
            (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t₀)) *
            Real.exp (-((1 / 2 : ℝ) * (t - t₀)))) ∧
    Filter.Tendsto (fun t => Metric.infDist
      (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t)
      c1EuclideanSymbolTarget) atTop (𝓝 0) := by
  have hxEuclidean : WithLp.toLp 2 x ∈ c1EuclideanBox := by
    change c1EuclideanCoordinates (WithLp.toLp 2 x) ∈ box
    simpa using hx
  rcases consensusOptimalFlow_theorem1 x hx t₀ ht₀ with
    ⟨h1mem, h1dist, h1tendsto⟩
  rcases consensusOptimalFlow_theorem4 x hx t₀ ht₀ with
    ⟨h4mem, h4dist, h4tendsto⟩
  exact ⟨h1mem, h1dist, h1tendsto,
    (fun t ht => by
      have h := consensusOptimalFlow_theorem2_full x hx t₀ t ht
      exact ⟨h.1.2, h.2.1, h.2.2⟩),
    h4mem, h4dist, h4tendsto,
    consensus_maxGain_attains_finite_horizon_argmin x t₀ T hT,
    consensus_maxGain_attains_theorem1_horizon_argmin x hx t₀ T hT,
    consensus_maxGain_finite_theorem1_cost x hx t₀ T hT,
    (fun t ht => c1OptimalConsensusO24_distance x hx t₀ t ht₀ ht),
    consensusOptimalEuclideanFlow_theorem20
      (WithLp.toLp 2 x) hxEuclidean t₀ ht₀⟩

/-- Project the common-model conjunction into named theorem-entry fields. This
retains its original quantifiers over every box initial state and every
nonnegative start time, with a positive finite horizon for the optimization
entry. -/
theorem c1_rate3_entry_conclusions
    (x : AgentState) (hx : x ∈ box) (t₀ T : ℝ)
    (ht₀ : 0 ≤ t₀) (hT : 0 < T) : C1EntryConclusions x t₀ T := by
  rcases c1_rate3_common_model x hx t₀ T ht₀ hT with
    ⟨h1mem, h1dist, h1tendsto, h2, h4mem, h4dist, h4tendsto,
      hbaseCost, hactualCost, hfinite, hO24, h20⟩
  exact {
    shared_base_matches_theorem1 :=
      Tomabechi.Consistency.R3.commonBaseContract.theorem1_matches x hx
    shared_base_theorem4_effective :=
      fun t => Tomabechi.Consistency.R3.commonBaseContract.theorem4_effective x t
    shared_base_theorem4_effective_decay := fun s hs =>
      Tomabechi.Consistency.R3.commonBaseTheorem4Effective_rate3_decay x hx t₀ s hs
    shared_base_theorem4_cost_argmin := fun hx' u =>
      Tomabechi.Consistency.R3.commonBaseTheorem4_maxGain_argmin x hx' t₀ T hT u
    shared_base_theorem20_box_value :=
      Tomabechi.Consistency.R3.commonBaseContract.theorem20_box_value x hx
    shared_base_theorem20_excess_euclidean_distance := fun hx' =>
      Tomabechi.Consistency.R3.commonBaseTheorem20_excess_eq_euclidean_distance x hx'
    shared_base_theorem20_effective_excess_decay := fun s hs =>
      Tomabechi.Consistency.R3.commonBaseTheorem20Effective_excess_rate3_decay
        x hx t₀ s hs
    shared_base_theorem20_cost_argmin := fun hx' u =>
      Tomabechi.Consistency.R3.commonBaseTheorem20_maxGain_argmin x hx' t₀ T hT u
    shared_base_theorem20_minimum_target := fun t ht =>
      Tomabechi.Consistency.R3.commonBaseTheorem20_minimum_sublevel_iff_symbol_target
        (consensusOptimalFlow.flow t₀ x t)
        (consensusOptimalFlow_forward_invariant x hx t₀ t ht)
    theorem1_reachable := h1mem
    theorem1_distance := h1dist
    theorem1_tendsto := h1tendsto
    theorem2_shared_distance := fun t ht => (h2 t ht).1
    shared_base_theorem4_weighted_distance := fun t ht => by
      rw [consensusOptimalFlow_reachable_closure_eq_box t₀ ht₀,
        Tomabechi.Consistency.R3.commonBaseTheorem4_weightedTCZ_eq_shared]
      exact (h2 t ht).1
    theorem2_individual_residual := fun t ht => (h2 t ht).2.1
    theorem2_edge_mismatch := fun t ht => (h2 t ht).2.2
    theorem4_reachable := h4mem
    theorem4_weighted_distance := h4dist
    theorem4_tendsto := h4tendsto
    baselineCost_argmin := hbaseCost
    theorem1Cost_argmin := hactualCost
    theorem1Cost_finite := hfinite
    o24_distance := hO24
    theorem20_distanceSquared := fun t ht => (h20.1 t ht).1
    theorem20_distance := fun t ht => (h20.1 t ht).2
    theorem20_tendsto := h20.2
  }

/-- On the invariant zero-mean slice, Theorem 3's two quantitative distances
are now supplied by the same rate-3 flow and shared TCZ as the other C1 entries.
The slice contains nonzero initial states, so its LUB residual is not vacuous. -/
theorem c1_rate3_common_model_with_theorem3
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ T : ℝ) (ht₀ : 0 ≤ t₀) (hT : 0 < T) :
    ∀ s, t₀ ≤ s →
        Metric.infDist (consensusOptimalFlow.flow t₀ x s)
          (c1Theorem3OriginalTCZ t₀ s) ≤
          Real.sqrt (c1Theorem3Potential x t₀ t₀) * Real.exp (-3 * (s - t₀)) ∧
        euclideanCoordinateNorm
          (c1Theorem3System.ι
            (c1Theorem3System.abstraction 0 ((consensusOptimalFlow.flow t₀ x s) 0)) -
          c1Theorem3System.ι c1Theorem3System.lub) ≤
          Real.sqrt (c1Theorem3Potential x t₀ t₀ / c1Theorem3Weight 0) *
            Real.exp (-3 * (s - t₀)) := by
  have _hCommon := c1_rate3_common_model x hx t₀ T ht₀ hT
  intro s hs
  exact c1Theorem3_original_phi3_bound x hx hmean 0 t₀ s ht₀ hs

/-- A single explicit non-target initial state satisfies the bundled C1
conclusions, the Theorem 3 bounds, and has strictly positive initial abstract
residual. The state is non-target because its two coordinates differ. -/
theorem c1_nontrivial_witness_theorem3_bound
    (t₀ s : ℝ) (ht₀ : 0 ≤ t₀) (hs : t₀ ≤ s) :
    0 < c1Theorem3System.abstractResidual 0 (c1Theorem3NontrivialInitial 0) ∧
      Metric.infDist
          (consensusOptimalFlow.flow t₀ c1Theorem3NontrivialInitial s)
          (c1Theorem3OriginalTCZ t₀ s) ≤
        Real.sqrt (c1Theorem3Potential c1Theorem3NontrivialInitial t₀ t₀) *
          Real.exp (-3 * (s - t₀)) ∧
      euclideanCoordinateNorm
          (c1Theorem3System.ι
            (c1Theorem3System.abstraction 0
              ((consensusOptimalFlow.flow t₀ c1Theorem3NontrivialInitial s) 0)) -
          c1Theorem3System.ι c1Theorem3System.lub) ≤
        Real.sqrt (c1Theorem3Potential c1Theorem3NontrivialInitial t₀ t₀ /
          c1Theorem3Weight 0) *
          Real.exp (-3 * (s - t₀)) := by
  exact ⟨c1Theorem3NontrivialInitial_abstractResidual_positive,
    c1Theorem3_original_phi3_bound c1Theorem3NontrivialInitial
      c1Theorem3NontrivialInitial_mem_box
      c1Theorem3NontrivialInitial_zeroMean 0 t₀ s ht₀ hs⟩

/-- The typed C1 witness records the selected data, entry-level results,
Theorem 3's original full-potential target, O13 regularity, and the required
cross-context equalities. -/
noncomputable def c1O13Witness : C1O13Witness where
  common_information_bottom := Tomabechi.Consistency.R1.c1InformationImage_bottom
  common_information_join := fun ha hb =>
    Tomabechi.Consistency.R1.c1InformationImage_join_closed ha hb
  common_information_meet := fun ha hb =>
    Tomabechi.Consistency.R1.c1InformationImage_meet_closed ha hb
  common_information_proper := Tomabechi.Consistency.R1.c1InformationImage_proper
  common_selected_symbols_in_information :=
    Tomabechi.Consistency.R1.c1SymbolImage_subset_c1InformationImage
  common_symbol_address_is_lub :=
    Tomabechi.Consistency.R1.c1SymbolAddressImage_isLUB
  common_information_law_bottom :=
    Tomabechi.Consistency.R1.commonConceptInformationLaw_bottom
  common_information_law_nonbottom := fun ha =>
    Tomabechi.Consistency.R1.commonConceptInformationLaw_of_ne_bottom ha
  common_information_pair_joint :=
    Tomabechi.Consistency.R1.commonConceptInformationPair_joint_eq
  common_information_pair_reference := fun a =>
    Tomabechi.Consistency.R1.commonConceptInformationPair_reference_eq a
  common_information_score_bottom :=
    Tomabechi.Consistency.R1.commonConceptInformationPair_score_bottom
  common_information_score_nonbottom := fun ha =>
    Tomabechi.Consistency.R1.commonConceptInformationPair_score_of_ne_bottom ha
  common_information_score_positive_nonbottom := fun ha =>
    Tomabechi.Consistency.R1.commonConceptInformationPair_score_positive_of_ne_bottom ha
  common_information_recovers_physical_address :=
    Tomabechi.Consistency.R1.commonConceptInformationLaw_recovers_physical_address
  common_information_recovers_upper_addresses :=
    Tomabechi.Consistency.R1.commonConceptInformationLaw_recovers_upper_address
  information_bottom := c1SymbolInfo_bot
  information_join := fun ha hb => c1SymbolInfo_join_closed ha hb
  information_meet := fun ha hb => c1SymbolInfo_meet_closed ha hb
  information_proper := c1AvailableInformation_proper
  selected_symbols_in_information := c1SymbolW_subset_info
  symbol_address_is_lub := c1SymbolAddress_isLUB
  symbolic_target_nonempty := c1SymbolTarget_nonempty
  symbolic_target_closed := c1SymbolTarget_closed
  symbolic_distance_nonnegative := c1SymbolDistance_nonneg
  symbolic_distance_zero_iff := c1SymbolDistance_zero_iff
  symbolic_distance_matches_shared_potential_on_box :=
    c1SymbolDistance_eq_sharedPotential_on_box
  symbolic_target_matches_reachable_target := c1SymbolTarget_box_eq_sharedTCZ
  symbolic_distance_smooth := c1SymbolDistance_contDiff
  base_presence_range := c1SymbolBasePresence_unitInterval
  amplified_presence_value := c1SymbolPresence_selected
  amplification_value := c1SymbolAmplification_selected
  amplification_nonnegative := le_of_lt c1SymbolLambda_positive
  amplification_positive := c1SymbolLambda_positive
  presence_amplification_formula := by intro u x t; rfl
  base_presence_zero := by intro x t; rfl
  presence_range := c1SymbolPresence_selected_bounds
  q_range := c1SymbolQ_range
  q_positive := c1SymbolQ_positive
  selected_q_is_one := by intro x t; norm_num [c1SymbolQ]
  base_potential_smooth := c1SymbolV0_contDiff
  selected_presence_smooth := c1SymbolSelectedPresence_contDiff
  slope_smooth := c1SymbolSlope_contDiff
  slope_derivative := c1SymbolSlope_derivative
  effective_potential_formula := c1SymbolEffectivePotential_selected
  effective_potential_decay := c1SymbolEffectivePotential_optimalFlow_decay
  euclidean_target_nonempty := c1EuclideanSymbolTarget_nonempty
  euclidean_target_closed := c1EuclideanSymbolTarget_closed
  euclidean_distance_nonnegative := c1EuclideanSymbolDistance_nonneg
  euclidean_distance_zero_iff := c1EuclideanSymbolDistance_zero_iff
  euclidean_distance_gradient := c1EuclideanSymbolDistance_hasGradientAt
  euclidean_base_potential_gradient := by
    intro x
    apply (hasGradientAt_iff_hasFDerivAt).2
    have hD := (c1EuclideanSymbolDistance_hasGradientAt x).hasFDerivAt
    convert hD.const_smul (2 : ℝ) using 1
    change (InnerProductSpace.toDual ℝ C1EuclideanAgentState)
      ((2 : ℝ) • c1EuclideanSymbolDistanceGradient x) = _
    exact map_smul (InnerProductSpace.toDual ℝ C1EuclideanAgentState) 2 _
  euclidean_presence_gradient := by intro x; exact hasGradientAt_const x 1
  euclidean_effective_potential_gradient := by
    intro x
    have hEq : (fun y : C1EuclideanAgentState =>
        3 * c1EuclideanSymbolDistance y) =
        (fun y => 0 - 3 * (1 * (fun d : ℝ => -d)
          (c1EuclideanSymbolDistance y))) := by
      funext y
      simp
    rw [hEq]
    exact c1EuclideanEffectivePotential_hasGradientAt x
  euclidean_distance_error := c1EuclideanSymbolDistance_error_bound
  identity_mobility_left_inverse := by intro r y; simp
  identity_mobility_symmetric := by intro y z; simp [real_inner_comm]
  identity_mobility_coercive := by intro r y; simp [real_inner_self_eq_norm_sq]
  identity_mobility_continuous := continuous_const
  theorem20_condition_A := by
    intro x
    have hnonneg :
        0 ≤ inner ℝ (c1EuclideanSymbolDistanceGradient x)
          (c1EuclideanSymbolDistanceGradient x) := by
      rw [real_inner_self_eq_norm_sq]
      positivity
    rw [real_inner_smul_right]
    simp
    nlinarith
  theorem20_condition_B := by norm_num
  theorem20_PL := by
    intro x
    rw [c1EuclideanSymbolGradient_inner_self]
    nlinarith
  effective_field_is_negative_gradient :=
    c1EuclideanOptimalField_eq_neg_three_gradient
  closed_loop_field_smooth := c1EuclideanOptimalField_contDiff
  closed_loop_field_locally_lipschitz := c1EuclideanOptimalField_locallyLipschitz
  euclidean_initial_region_compact := c1EuclideanBox_isCompact
  euclidean_flow_forward_invariant := euclideanConsensusOptimalFlow_forward_invariant
  euclidean_reachable_closure := euclideanConsensusOptimalFlow_reachable_closure_eq_box

noncomputable def c1Witness : C1Witness where
  initialRegion := box
  initialRegion_eq_box := rfl
  selectedGain := c1MaxGainSignal
  selectedGain_eq_maximum := rfl
  selectedHorizonController := consensusSelectedHorizonControl
  selectedController_matches_gain := by
    intro p s
    simp [consensusSelectedHorizonControl, c1MaxGainSignal]
  selectedController_measurable := consensusSelectedHorizonControl_measurable
  selectedController_rightLimit := consensusSelectedHorizonControl_rightLimit
  selectedFlow := consensusOptimalFlow
  selectedFlow_eq_rate3 := rfl
  distinctAdmissibleControls := consensus_two_distinct_admissible_controls
  nontrivialInitial := c1Theorem3NontrivialInitial
  nontrivialInitial_eq := rfl
  nontrivialInitial_in_box := c1Theorem3NontrivialInitial_mem_box
  nontrivialInitial_zero_mean := c1Theorem3NontrivialInitial_zeroMean
  nontrivialInitial_has_positive_abstract_residual :=
    c1Theorem3NontrivialInitial_abstractResidual_positive
  selectedDifferentiableFlow := differentiableConsensusOptimalFlow
  selectedDifferentiableFlow_eq_rate3 := rfl
  selectedGain_measurable := c1MaxGainSignal.2.1
  selectedGain_rightLimit := by
    intro t₀ x
    simpa [c1MaxGainSignal, consensusOptimalFlow] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (3 : ℝ))
        (𝓝[>] t₀) (𝓝 3))
  selectedOrbit_isFlow := consensusOptimalFlow_eq_selected_orbit
  theorem1ActualCostArgmin := consensus_maxGain_attains_theorem1_horizon_argmin
  theorem1ActualCostFinite := consensus_maxGain_finite_theorem1_cost
  theorem3FullPotentialBound := c1Theorem3_original_phi3_bound
  theorem3FullPotentialTendsto := c1Theorem3_original_phi3_tendsto
  theorem20ClosedLoopLocallyLipschitz := c1EuclideanOptimalField_locallyLipschitz
  theorem2Error_allStates := consensus_global_error_bound
  theorem20Error_allStates := c1EuclideanSymbolDistance_error_bound
  sharedBaseCandidate := Tomabechi.Consistency.R3.commonBaseContract
  o13Evidence := c1O13Witness
  allEntryConclusions := c1_rate3_entry_conclusions
  connections := fun t₀ ht₀ => Classical.choice (c1Connections_nonempty t₀ ht₀)

theorem c1Witness_nonempty : Nonempty C1Witness := ⟨c1Witness⟩

/-- Apply every named Theorem 1/2/4/20, O02, and O24 conclusion directly from
the closed C1 witness, preserving the original initial-state, start-time, and
finite-horizon quantifiers. -/
theorem c1Witness_entry_results
    (x : AgentState) (hx : x ∈ box) (t₀ T : ℝ)
    (ht₀ : 0 ≤ t₀) (hT : 0 < T) : C1EntryConclusions x t₀ T :=
  c1Witness.allEntryConclusions x hx t₀ T ht₀ hT

/-- The witness also supplies the required context identifications for every
nonnegative start time. -/
theorem c1Witness_connections (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    C1Connections t₀ ht₀ :=
  c1Witness.connections t₀ ht₀

end Tomabechi.Consistency.ConsistencyC1CommonModel
