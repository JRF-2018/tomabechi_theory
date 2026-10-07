import Tomabechi.Consistency.ConsistencyC6_OriginalLayerInputs
import Tomabechi.Consistency.ConsistencyC6_Nondegenerate
import Tomabechi.Consistency.ConsistencyC6_ActuatorInputs
import Tomabechi.Consistency.ConsistencyC6_SignatureSelfProcess
import Tomabechi.Consistency.ConsistencyC6_TopUniqueness
import Tomabechi.Consistency.ConsistencyR1_C6Information
import Tomabechi.Consistency.ConsistencyR2_PointReachability
import Tomabechi.Consistency.ConsistencyR1_C6CommonConceptSCM
import Tomabechi.Consistency.ConsistencyR1_C6FullIndex
import Tomabechi.Consistency.ConsistencyR1_C3LiftedStage
import Tomabechi.Consistency.ConsistencyR1_CompletePath

/-!
# C6：実共有モデルの受入条件と存在

ここでの原文条件は固定した層/主体/履歴/contextでの具体化である。
ModelSignatureのC1、24/26、平均場段、測度付きC3は既に仮定の証拠を持つデータであり、
それらに含まれない層射影・積分収支・逆極限同定・自己過程・27入力を明示する。
追加条件は共有保存式と、局所contextの採用/評価/端点の同定である。
存在宣言の網羅性は各条件と原文の対応を読んで監査する必要がある。
生物学的系譜・死亡時刻の解釈モデルを主張しない。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Consistency.C2
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1CommonModel
open Tomabechi.Theorem16_25
open Tomabechi.Theorem24_26
open MeasureTheory
open Filter
open scoped Topology

/-- 原文の全層解析入力と、指定contextの原文証明データへの実同定。
C1Witnessの全入口/O13/選択性、Dの全競合24条件、Eの全初期対26条件、
M.stagesの元H-stage仮定、M.scmの全層presence/可測観測仮定は署名の型に含まれる。 -/
structure OriginalPremises (M : ModelSignature) : Prop where
  layers : OriginalLayerInputs M
  entropy : EntropyBalanceInputs M
  /-- 履歴別逆極限のmetric/位相/完備性/縮小性と、Mの同じ固定点を結ぶ。 -/
  inverse_limit : ∃ A : C6C4FlowTCZAdapter,
    A.fixed_point_system = M.fixedPoints ∧
    (∀ h i, (M.selfRepresentation h).TCZ i =
      theorem16_intervalGradientFlowLayerSystem.carrier h i)
  /-- 元平均場/枝/支持/LUBとlaw保存容量のadapterを、Mの実段/lawへ接続する。 -/
  meanfield_information : ∀ n, ∃ _A : C6C3InformationAdapter n,
    (M.stages n).toStageValleySpec =
      (Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec ∧
    M.informationLaw (n + 1) = Tomabechi.Consistency.C3.upperJoint
  /-- 同じMの全競合有限軌道の認知ODE/ACを支える積分表示。 -/
  finite_control_solution : ∀ k u x T t,
    M.data.trajectory (some k) u x T t = controlledConsensusState x T u t
  finite_disagreement_ac : ∀ k u x a b, a ≤ b →
    AbsolutelyContinuousOnInterval
      (fun t => halfDifference (M.data.trajectory (some k) u x a t)) a b
  finite_disagreement_ode : ∀ k u x T H, 0 < H →
    ∀ᵐ t ∂volume.restrict (Set.Icc T (T + H)),
      HasDerivAt (fun s => halfDifference (M.data.trajectory (some k) u x T s))
        (-(u.1 t) * halfDifference (M.data.trajectory (some k) u x T t)) t
  /-- 全初期対/全可測有界競合のCarathéodory一意性。 -/
  finite_disagreement_unique : ∀ k u x a b (y : ℝ → ℝ), a ≤ b →
    AbsolutelyContinuousOnInterval y a b → y a = halfDifference x →
    (∀ᵐ t ∂volume.restrict (Set.Icc a b), HasDerivAt y (-(u.1 t) * y t) t) →
    y b = halfDifference (M.data.trajectory (some k) u x a b)
  top_actuator : ∀ x T (hT : 0 ≤ T), TopActuatorInputs M x T hT
  top_forward_unique : ∀ x a b, 0 ≤ a → a ≤ b → ∀ y : ℝ → C6TopState,
    AbsolutelyContinuousOnInterval y a b → y a = x →
    (∀ᵐ t ∂volume.restrict (Set.Icc a b), HasDerivAt y (c6TopClosedField (y t)) t) →
    y b = M.topPath x a b
  /-- O01：最大feedbackだけでなく全有界可測競合方策を同じ実Dへ接続する。 -/
  top_control_solution : ∀ (π : C6LayeredPolicy ⊤) x a b,
    M.data.trajectory ⊤ π x a b =
      Tomabechi.Examples.Theorem27.measurableGainVectorOrbit (x 0) (x 1) a b
        (Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain π)
  top_control_field : ∀ (π : C6LayeredPolicy ⊤) x a,
    M.data.admissible ⊤ π x a → ∀ (t : Set.Ici (0 : ℝ)) y,
    c6TopNaturalDrift y + Tomabechi.Examples.Theorem27Op.GE (π.action (t, y)) =
      c6TopGainField (Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain π) t.1 y
  top_control_unique : ∀ (π : C6LayeredPolicy ⊤) x a b, a ≤ b → ∀ y : ℝ → C6TopState,
    AbsolutelyContinuousOnInterval y a b → y a = x →
    (∀ᵐ t ∂volume.restrict (Set.Icc a b), HasDerivAt y
      (c6TopGainField (Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain π) t (y t)) t) →
    y b = M.data.trajectory ⊤ π x a b
  self_reachability : ∀ h i,
    (M.selfRepresentation h).Self i
      (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4SelfEgoTCZ.reachable h i) =
      (M.selfRepresentation h).TCZ i
  self_process_a2 : ∀ d a, (M.selfProcess d a).toLawModel.Condition25A2 ()
  /-- 候補介入のΓ/出力jointそのものを、同じ外生法則で保存する。 -/
  relational_joint_invariant : ∀ d a h s,
    M.scm.model.scm.exogenousLaw.map
      (fun u => (M.scm.model.scm.stateEquation d a h u,
        M.scm.model.scm.outputEquation d a h u s)) =
    M.scm.model.scm.exogenousLaw.map
      (fun u => (M.scm.model.scm.stateEquation d a h u,
        M.scm.model.scm.outputEquation d a h u (M.scm.model.scm.candidateVariable d a u)))

/-- 共有保存・原文context採用・正baselineの保持を同じMに課す。
具体証人の存在は、これらの条件の必要性を主張するものではない。 -/
structure AdditionalConditions (M : ModelSignature) : Prop extends CommonDataCouplings M where
  /-- S0：全contextの束演算/正層列挙と、Mの実重み。 -/
  common_layers : ∀ n, ∃ _A : C6CommonLayerAdapter n,
    ∀ p : PositiveLayer, commonEntropyWeight (entropyLayerAddress p) = M.weight p
  history_centers : M.historyCenter = theorem16_intervalGradientCenter
  history_flows : M.historyFlow = theorem16_intervalGradientFlow
  original_stages : M.stages = Tomabechi.Consistency.C3.hStageSequence
  original_stage_times : M.stageTime = Tomabechi.Consistency.C3.stageTime
  original_self_representations : M.selfRepresentation = c6TypedSelfRepresentation
  stage_start : ∀ n, (M.stages n).startTime = M.stageTime n
  stage_initial : ∀ n, cognitiveCoordinate (M.stageInitial n) = (M.stages n).initial
  stage_endpoint : ∀ n,
    M.completePath (M.stageTime (n + 1)) = M.stageInitial (n + 1)
  /-- S2/K5：有限層でC1基礎評価と正baselineを保つ。 -/
  finite_c1_cost : ∀ k u x, x ∈ box → ∀ t,
    M.data.runningCost (some k) u x t = consensusV0 x t
  finite_optimal_selected : ∀ k x T,
    M.data.optimalPolicy (some k) x T = M.c1.selectedGain
  finite_positive_baseline : ∀ k u x t, 1 ≤ M.data.runningCost (some k) u x t
  cost_policy_independent : ∀ a (u v : C6LayeredPolicy a) (x : C6LayeredState a) t,
    M.data.runningCost a u x t = M.data.runningCost a v x t
  c1_evaluation : ∀ x, x ∈ box → ∀ t,
    consensusV0 x t = 1 + 16 * M.potential 1 (c1ToCompleteState x)
  c4_evaluation : ∀ h z, M.potential (M.historyCenter h) z =
    theorem16_intervalGradientPotential h (cognitiveCoordinate z)
  top_field_binding : ∀ (t : Set.Ici (0 : ℝ)) y,
    c6TopNaturalDrift y + Tomabechi.Examples.Theorem27Op.GE
      ((M.dynamics.policyEquiv M.dynamics.feedback).action (t, y)) = c6TopClosedField y

/-- 原文側の補完入力をすべて実共有データから供給する。 -/
theorem commonModel_originalPremises : OriginalPremises commonModel := by
  refine {
    layers := commonModel_originalLayerInputs
    entropy := commonModel_entropyInputs
    inverse_limit := ⟨c6C4FlowTCZAdapter, rfl, ?_⟩
    meanfield_information := fun n => ⟨c6C3InformationAdapter n, rfl,
      commonModel_couplings.stage_information n⟩
    finite_control_solution := commonModel_couplings.finite_trajectory
    finite_disagreement_ac := ?_
    finite_disagreement_ode := ?_
    finite_disagreement_unique := ?_
    top_actuator := commonModel_topActuatorInputs
    top_forward_unique := commonModel_topPath_unique
    top_control_solution := commonModel_topControl_solution
    top_control_field := commonModel_topControl_field
    top_control_unique := commonModel_topControl_unique
    self_reachability := Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4SelfEgoTCZ.self_is_tcz
    self_process_a2 := commonModel_selfProcess25A2
    relational_joint_invariant := ?_ }
  · intro h i
    exact (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4SelfEgoTCZ.tcz_is_layer_carrier h i)
  · intro k u x a b hab
    simpa only [commonModel_couplings.finite_trajectory,
      controlledConsensusState_halfDifference] using
      c1ControlledOrbit_absolutelyContinuousOnInterval (halfDifference x) a b hab u
  · intro k u x T H hH
    simpa only [commonModel_couplings.finite_trajectory,
      controlledConsensusState_halfDifference] using
      c1ControlledOrbit_ae_ode (halfDifference x) T H hH u
  · intro k u x a b y hab hac hy hode
    have h := c1ControlledState_unique_on_interval 0 (halfDifference x) a b u y
      hab hac hy (by simpa using hode)
    simpa [commonModel_couplings.finite_trajectory, controlledConsensusState_halfDifference,
      c1ControlledState] using h
  · intro d a h s
    rfl

/-- 共有条件とcontext同定を外部仮定なしに構成する。 -/
theorem commonModel_additionalConditions : AdditionalConditions commonModel := by
  refine {
    toCommonDataCouplings := commonModel_couplings
    common_layers := fun n => ⟨c6CommonLayerAdapter n,
      (c6CommonLayerAdapter n).c1_common_weight_agrees⟩
    history_centers := rfl
    history_flows := rfl
    original_stages := rfl
    original_stage_times := rfl
    original_self_representations := rfl
    stage_start := Tomabechi.Consistency.C3.hStageSequence_start
    stage_initial := by intros; rfl
    stage_endpoint := fun n => c3A7StitchedTrajectory_at_stageTime (n + 1)
    finite_c1_cost := c6LayeredFiniteRunningCost_eq_C1V0
    finite_optimal_selected := by intros; rfl
    finite_positive_baseline := ?_
    cost_policy_independent := ?_
    c1_evaluation := c1V0_eq_baseline_add_centeredPotential
    c4_evaluation := centeredQuadraticPotential_eq_C4
    top_field_binding := commonModel_topClosedField_binding }
  · intro k u x t
    change 1 ≤ 1 + 8 * (halfDifference x) ^ 2
    nlinarith [sq_nonneg (halfDifference x)]
  · intro a u v x t
    cases a <;> rfl

/-- 外部のモデル前提を残さない、指定共有モデルの存在。
原文と各受入fieldの対応を監査してから全体系の充足として認定する。 -/
theorem integrated_model_exists : ∃ M : ModelSignature,
    OriginalPremises M ∧ AdditionalConditions M ∧ Nondegenerate M :=
  ⟨commonModel, commonModel_originalPremises, commonModel_additionalConditions,
    commonModel_nondegenerate⟩

/-- 同じ受入済みモデルは、新共通束全点の情報lawを実SCM実験へ結ぶ。
これは元の共有存在結論に、証明済みのR1情報実験bridgeを付けた形である。 -/
theorem commonModel_commonConceptInformationExperimentBridge :
    Tomabechi.Consistency.R1.CommonConceptInformationExperimentBridge commonModel :=
  Tomabechi.Consistency.R1.commonConceptInformationExperimentBridge_of_couplings
    commonModel commonModel_couplings
    commonModel_originalPremises.relational_joint_invariant

/-- 共有モデルの存在と、共通束情報lawの同一SCM実験への接続を同時に保持する。 -/
theorem integrated_model_exists_with_common_concept_information_experiment :
    ∃ M : ModelSignature,
      OriginalPremises M ∧ AdditionalConditions M ∧ Nondegenerate M ∧
      Tomabechi.Consistency.R1.CommonConceptInformationExperimentBridge M :=
  ⟨commonModel, commonModel_originalPremises, commonModel_additionalConditions,
    commonModel_nondegenerate, commonModel_commonConceptInformationExperimentBridge⟩

/-- R1–R3間で同じC1評価・一点K・情報実験を参照する入口契約。
R2のadapterは各初期点の一点閉到達Kを保持し、R3は共通基礎評価を使う。 -/
def PointR2Theorem3Acceptance (x : AgentState) (hx : x ∈ box)
    (hmean : x 0 + x 1 = 0) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) : Prop :=
  (∀ t, (Tomabechi.Consistency.R2.pointTheorem3Target x t₀ t).Nonempty) ∧
  (∀ t, t₀ ≤ t →
    Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3StatePhi3
      (consensusOptimalFlow.flow t₀ x t) t =
    Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3StatePhi3 x t₀ *
      Real.exp (-6 * (t - t₀))) ∧
  (∀ t, t₀ ≤ t → Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (Tomabechi.Consistency.R2.pointTheorem3Target x t₀ t) ≤
    Real.sqrt (Tomabechi.Examples.Theorem2.DA.potential x t₀) *
      Real.exp (-3 * (t - t₀)))

/-- Quantitative point-K geometry and Theorem 1/4 target clauses. -/
structure PointR2QuantitativeTargets (x : AgentState) (hx : x ∈ box)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) : Prop where
  closure_exact : Tomabechi.Consistency.R2.pointReachableClosure x t₀ =
    Tomabechi.Consistency.R2.orbitSegment x
  closure_nonempty : (Tomabechi.Consistency.R2.pointReachableClosure x t₀).Nonempty
  forward_invariant : ∀ {y : AgentState},
    y ∈ Tomabechi.Consistency.R2.pointReachableClosure x t₀ →
    ∀ {s t : ℝ}, s ≤ t →
      consensusOptimalFlow.flow s y t ∈ Tomabechi.Consistency.R2.pointReachableClosure x t₀
  theorem1_target_nonempty :
    (Tomabechi.Consistency.R2.pointTheorem1Target x t₀ t₀).Nonempty
  theorem4_target_nonempty :
    (Tomabechi.Consistency.R2.pointTheorem4Target x t₀ t₀).Nonempty
  shared_target_nonempty :
    (Tomabechi.Consistency.R2.pointSharedTCZ x t₀ t₀).Nonempty
  o24_tcz_singleton : ∀ t,
    (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).TCZ t =
      {Tomabechi.Consistency.R2.agreementPoint x}
  o24_ego_feedback : ∀ y t,
    (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).Ego y t =
      (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).flow.feedback y t
  theorem1_distance_sq : ∀ t, t₀ ≤ t →
    (Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (Tomabechi.Consistency.R2.pointTheorem1Target x t₀ t)) ^ 2 ≤
        Tomabechi.Examples.Theorem2.DA.potential x t₀ * Real.exp (-6 * (t - t₀))
  theorem4_distance_sq : ∀ t, t₀ ≤ t →
    (Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (Tomabechi.Consistency.R2.pointTheorem4Target x t₀ t)) ^ 2 ≤
        Tomabechi.Examples.Theorem2.DA.potential x t₀ * Real.exp (-6 * (t - t₀))
  shared_distance : ∀ t, t₀ ≤ t →
    Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (Tomabechi.Consistency.R2.pointSharedTCZ x t₀ t) ≤
        Real.sqrt (Tomabechi.Examples.Theorem2.DA.potential x t₀) *
          Real.exp (-3 * (t - t₀))
  theorem20_distance : ∀ t, t₀ ≤ t →
    Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (Tomabechi.Consistency.R2.pointTheorem20Target x t₀ t) ≤
        Real.sqrt (Tomabechi.Examples.Theorem2.DA.potential x t₀) *
          Real.exp (-3 * (t - t₀))

structure R1R2R3EntryIntegration (M : ModelSignature) : Prop where
  information_experiment :
    Tomabechi.Consistency.R1.CommonConceptInformationExperimentBridge M
  common_concept_scm_source :
    Tomabechi.Consistency.R1.commonConceptMeasuredC3Model.model.scm.exogenousLaw =
        theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw ∧
      Tomabechi.Consistency.R1.commonConceptMeasuredC3Model.model.scm.globalHistory =
        theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistory
  common_concept_scm_candidate : ∀ d a,
    Tomabechi.Consistency.R1.commonConceptMeasuredC3Model.model.scm.candidateVariable d
        (Tomabechi.Consistency.R1.layerAddressEmbedding
          (Tomabechi.Consistency.C6.operationalLayerAddress a)) =
      theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d a
  common_concept_scm_noAtman : ∀ d a,
    ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      (Tomabechi.Consistency.R1.commonConceptMeasuredC3Model.model.scm.toIndexed.toProbabilityCausalModel)).hasAtman d a
  common_concept_candidate_positive : ∀ d s a,
    Theorem25GlobalHistorySCM.candidateHasPositiveMass
      Tomabechi.Consistency.R1.commonConceptMeasuredC3Model.model.scm.toIndexed d a s
  common_concept_typed_self_a2 : ∀ d a,
    (Tomabechi.Consistency.R1.commonConceptTypedSelfProcess d a).toLawModel.Condition25A2 ()
  common_concept_typed_self_representation : ∀ d h s a u,
    ((Tomabechi.Consistency.R1.commonConceptTypedSelfProcess d a).intervenedEquation h s u).1 =
      (Tomabechi.Consistency.R1.commonConceptPresence.relationalState d h a,
        Tomabechi.Consistency.C6.c6TypedSelfRepresentation h)
  common_concept_theorem24_proper : ∀ a (ha : a < (⊤ : Tomabechi.Consistency.R1.CommonConcept))
      (x : Tomabechi.Consistency.R1.fullCommonLayerState a) (T : ℝ), 0 ≤ T →
    0 < Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimalValue a x T ∧
      ¬ FeedbackPZS (Tomabechi.Consistency.R1.fullCommonTheorem24Data.admissible a)
        (fun _ => futureLebesgueMeasure T)
        (fun π y t s => Tomabechi.Consistency.R1.fullCommonTheorem24Data.runningCost a π
          (Tomabechi.Consistency.R1.fullCommonTheorem24Data.trajectory a π y t s) s) x T
  common_concept_full24_optimality : ∀ (a : Tomabechi.Consistency.R1.CommonConcept)
      (x : Tomabechi.Consistency.R1.fullCommonLayerState a) (T : ℝ), (hT : 0 ≤ T) →
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimalValue a x T =
        ∫ s, theorem26DiscountWeight
          Tomabechi.Consistency.R1.fullCommonTheorem24Data.rho T s *
          Tomabechi.Consistency.R1.fullCommonTheorem24Data.runningCost a
            (Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimalPolicy a x T)
            (Tomabechi.Consistency.R1.fullCommonTheorem24Data.trajectory a
              (Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimalPolicy a x T)
              x T s) s ∂(futureLebesgueMeasure T) ∧
      ∀ π, Tomabechi.Consistency.R1.fullCommonTheorem24Data.admissible a π x T →
        ENNReal.ofReal
            (Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimalValue a x T) ≤
          ∫⁻ s,
            ENNReal.ofReal
              (theorem26DiscountWeight
                Tomabechi.Consistency.R1.fullCommonTheorem24Data.rho T s *
                Tomabechi.Consistency.R1.fullCommonTheorem24Data.runningCost a π
                  (Tomabechi.Consistency.R1.fullCommonTheorem24Data.trajectory a π x T s) s)
            ∂(futureLebesgueMeasure T)
  common_concept_top27_kernel : ∀
      (x : Tomabechi.Consistency.R1.fullCommonLayerState
        (⊤ : Tomabechi.Consistency.R1.CommonConcept)) (T : ℝ) (hT : 0 ≤ T),
    c6LayeredTheorem27Conclusion
      (cast (congrArg C6LayeredState
        Tomabechi.Consistency.R1.fullCommonLayerIndex_top) x) T hT
  common_concept_top27_actuator : ∀
      (x : Tomabechi.Consistency.R1.fullCommonLayerState
        (⊤ : Tomabechi.Consistency.R1.CommonConcept)) (T : ℝ) (hT : 0 ≤ T),
    C6TopActuatorInputs
      (cast (congrArg C6LayeredState
        Tomabechi.Consistency.R1.fullCommonLayerIndex_top) x) T hT
  common_concept_top27_original_actuator : ∀
      (x : Tomabechi.Consistency.R1.fullCommonLayerState
        (⊤ : Tomabechi.Consistency.R1.CommonConcept)) (T : ℝ) (hT : 0 ≤ T),
    TopActuatorInputs commonModel
      (cast (congrArg C6LayeredState
        Tomabechi.Consistency.R1.fullCommonLayerIndex_top) x) T hT
  common_concept_full24_old_value : ∀ (a : WithTop ℕ) (x : C6LayeredState a) (T : ℝ),
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimalValue
      (Tomabechi.Consistency.R1.layerAddressEmbedding a)
      (cast (congrArg C6LayeredState
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress a).symm) x) T =
      c6LayeredNonnegativeTimeData.optimalValue a x T
  common_concept_full24_old_cost : ∀ (a : WithTop ℕ) (π : C6LayeredPolicy a)
      (x : C6LayeredState a) (t : ℝ),
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.runningCost
      (Tomabechi.Consistency.R1.layerAddressEmbedding a)
      (cast (congrArg C6LayeredPolicy
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress a).symm) π)
      (cast (congrArg C6LayeredState
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress a).symm) x) t =
      c6LayeredNonnegativeTimeData.runningCost a π x t
  common_concept_full24_old_admissibility : ∀ (a : WithTop ℕ) (π : C6LayeredPolicy a)
      (x : C6LayeredState a) (T : ℝ),
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.admissible
      (Tomabechi.Consistency.R1.layerAddressEmbedding a)
      (cast (congrArg C6LayeredPolicy
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress a).symm) π)
      (cast (congrArg C6LayeredState
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress a).symm) x) T ↔
      c6LayeredNonnegativeTimeData.admissible a π x T
  common_concept_full24_old_policy : ∀ (a : WithTop ℕ) (x : C6LayeredState a) (T : ℝ),
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimalPolicy
      (Tomabechi.Consistency.R1.layerAddressEmbedding a)
      (cast (congrArg C6LayeredState
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress a).symm) x) T =
      cast (congrArg C6LayeredPolicy
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress a).symm)
        (c6LayeredNonnegativeTimeData.optimalPolicy a x T)
  common_concept_full24_old_trajectory : ∀ (a : WithTop ℕ) (π : C6LayeredPolicy a)
      (x : C6LayeredState a) (T s : ℝ),
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.trajectory
      (Tomabechi.Consistency.R1.layerAddressEmbedding a)
      (cast (congrArg C6LayeredPolicy
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress a).symm) π)
      (cast (congrArg C6LayeredState
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress a).symm) x) T s =
      cast (congrArg C6LayeredState
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress a).symm)
        (c6LayeredNonnegativeTimeData.trajectory a π x T s)
  common_concept_scm_intervention : ∀ d a h s,
    ((Tomabechi.Consistency.R1.commonConceptMeasuredC3Model.model.scm.exogenousLaw.toMeasure).map
      (fun u =>
        (Tomabechi.Consistency.R1.commonConceptMeasuredC3Model.model.scm.stateEquation d
          (Tomabechi.Consistency.R1.layerAddressEmbedding
            (Tomabechi.Consistency.C6.operationalLayerAddress a)) h u,
         Tomabechi.Consistency.R1.commonConceptMeasuredC3Model.model.scm.outputEquation d
          (Tomabechi.Consistency.R1.layerAddressEmbedding
            (Tomabechi.Consistency.C6.operationalLayerAddress a)) h u s))).map
      (fun z => (Tomabechi.Consistency.R1.restrictCommonConceptGamma z.1, z.2)) =
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw.toMeasure).map
      (fun u =>
        (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
         theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u s))
  shared_base : M.c1.sharedBaseCandidate = Tomabechi.Consistency.R3.commonBaseContract
  point_o24 : ∀ (x : AgentState) (hx : x ∈ box) (t₀ : ℝ), 0 ≤ t₀ →
    (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).initialSet = {x} ∧
    (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).reachable =
      Tomabechi.Theorem1.closedLoopReachableSet (Tomabechi.Theorem1.policyFlowReachableAt
        (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).flow
        (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).initialSet t₀) ∧
    ∀ t, t₀ ≤ t → Metric.infDist
      ((Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).flow.flow t₀ x t)
      ((Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).TCZ t) ≤
        Real.sqrt (Tomabechi.Examples.Theorem2.DA.potential x t₀) * Real.exp (-3 * (t - t₀))
  point_theorem3 : ∀ (x : AgentState) (hx : x ∈ box)
      (hmean : x 0 + x 1 = 0) (t₀ : ℝ) (ht₀ : 0 ≤ t₀),
    PointR2Theorem3Acceptance x hx hmean t₀ ht₀
  point_quantitative_targets : ∀ (x : AgentState) (hx : x ∈ box)
      (t₀ : ℝ) (ht₀ : 0 ≤ t₀),
    PointR2QuantitativeTargets x hx t₀ ht₀
  /-- A complete CommonConcept-addressed H-stage input with the original scalar
  H-stage mean field recovered exactly on the diagonal subspace. -/
  common_concept_h_stage : ∀ n,
    ∃ s : Tomabechi.Theorem22.MeanFieldStageInput
        Tomabechi.Consistency.R1.LiftedStageState,
      s = Tomabechi.Consistency.R1.liftedHStageInput n ∧
      (∀ x : ℝ, s.meanField (Tomabechi.Consistency.R1.liftedStageCenter x) =
        (Tomabechi.Consistency.C3.hStageSequence n).meanField x) ∧
      (∀ x : ℝ,
        Tomabechi.Consistency.R1.liftedStageCenter x ∈ s.sublevel ↔
          x ∈ (Tomabechi.Consistency.C3.hStageSequence n).sublevel)
  common_concept_h_stage_family : ∀ x,
    Tomabechi.Consistency.R1.commonConceptHStageInput x =
      Tomabechi.Consistency.R1.liftedHStageDataOnOldAddress
        (Tomabechi.Consistency.R1.layerProjection x)
  common_concept_h_stage_family_at_proper_point : ∀ x
      (hx : x < (⊤ : Tomabechi.Consistency.R1.CommonConcept)),
    Tomabechi.Consistency.R1.commonConceptHStageInput x =
      Tomabechi.Consistency.R1.liftedHStageInput
        ((Tomabechi.Consistency.R1.layerProjection x).untopD 0)
  common_concept_h_stage_family_old_address : ∀ a : WithTop ℕ,
    Tomabechi.Consistency.R1.commonConceptHStageInput
        (Tomabechi.Consistency.R1.layerAddressEmbedding a) =
      Tomabechi.Consistency.R1.liftedHStageDataOnOldAddress a
  common_concept_h_stage_family_center : ∀ x,
    (Tomabechi.Consistency.R1.commonConceptHStageInput x).center =
      Tomabechi.Consistency.R1.liftedStageCenter
        (Tomabechi.Consistency.C3.representation
          ((((Tomabechi.Consistency.R1.layerProjection x).untopD 0 + 1 : ℕ) :
            Tomabechi.Consistency.C3.Atom)))
  common_concept_h_stage_family_top :
    Tomabechi.Consistency.R1.commonConceptHStageInput
        (⊤ : Tomabechi.Consistency.R1.CommonConcept) =
      Tomabechi.Consistency.R1.liftedHStageInput 0
  common_concept_h_stage_address : ∀ n,
    (Tomabechi.Consistency.R1.liftedHStageInput n).averagePresentation.supportLub =
        ((n + 1 : ℕ) : Tomabechi.Consistency.C3.Atom) ∧
      (Tomabechi.Consistency.R1.liftedHStageInput n).center =
        Tomabechi.Consistency.R1.liftedStageCenter
          (Tomabechi.Consistency.R1.layerAddressEmbedding
            (((n + 1 : ℕ) : Tomabechi.Consistency.C3.Atom)) 0)
  common_concept_h_stage_transition : ∀ n,
    (Tomabechi.Consistency.R1.liftedHStageInput (n + 1)).initial =
      (Tomabechi.Consistency.R1.liftedHStageValleyWitness n).orbit
        (Tomabechi.Consistency.C3.stageTime n +
          Tomabechi.Consistency.C3.stageDuration n)
  common_concept_h_stage_forward_invariant : ∀ n (x : Tomabechi.Consistency.R1.LiftedStageState),
    x ∈ (Tomabechi.Consistency.R1.liftedHStageInput n).sublevel →
    ∀ t, (Tomabechi.Consistency.R1.liftedHStageInput n).startTime ≤ t →
      Tomabechi.Consistency.R1.liftedStageOrbit
        (Tomabechi.Consistency.C3.representation (n + 1)) x
        (Tomabechi.Consistency.C3.stageTime n) t ∈
          (Tomabechi.Consistency.R1.liftedHStageInput n).sublevel
  common_concept_h_stage_decay : ∀ n t,
    (Tomabechi.Consistency.R1.liftedHStageInput n).startTime ≤ t →
    dist ((Tomabechi.Consistency.R1.liftedHStageValleyWitness n).orbit t)
        (Tomabechi.Consistency.R1.liftedStageCenter
          (Tomabechi.Consistency.C3.representation (n + 1))) =
      Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) *
        dist (Tomabechi.Consistency.R1.liftedHStageInput n).initial
          (Tomabechi.Consistency.R1.liftedStageCenter
            (Tomabechi.Consistency.C3.representation (n + 1)))
  common_concept_h_stage_flow_ode : ∀ (n : ℕ) (x : Tomabechi.Consistency.R1.LiftedStageState) t,
    HasDerivAt
      (Tomabechi.Consistency.R1.liftedStageOrbit
        (Tomabechi.Consistency.C3.representation (n + 1)) x
        (Tomabechi.Consistency.C3.stageTime n))
      (-(Tomabechi.Consistency.R1.liftedHStageInput n).mobility
          (Tomabechi.Consistency.R1.liftedStageOrbit
            (Tomabechi.Consistency.C3.representation (n + 1)) x
            (Tomabechi.Consistency.C3.stageTime n) t)
          ((Tomabechi.Consistency.R1.liftedHStageInput n).backgroundGradient
              (Tomabechi.Consistency.R1.liftedStageOrbit
                (Tomabechi.Consistency.C3.representation (n + 1)) x
                (Tomabechi.Consistency.C3.stageTime n) t) -
            ((Tomabechi.Consistency.R1.liftedHStageInput n).gain *
              (Tomabechi.Consistency.R1.liftedHStageInput n).presenceGain) •
              (Tomabechi.Consistency.R1.liftedHStageInput n).meanFieldGradient
                (Tomabechi.Consistency.R1.liftedStageOrbit
                  (Tomabechi.Consistency.C3.representation (n + 1)) x
                  (Tomabechi.Consistency.C3.stageTime n) t))) t
  /-- At every finite common-lattice address, the transported Theorem 24
  running cost is the same positive shared baseline used by the C1 model. -/
  common_concept_finite24_shared_base : ∀ (n : ℕ) (π : C1GainSignal)
      (x : AgentState) (hx : x ∈ box) (t : ℝ),
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.runningCost
      (Tomabechi.Consistency.R1.layerAddressEmbedding (some n))
      (cast (congrArg C6LayeredPolicy
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress (some n)).symm) π)
      (cast (congrArg C6LayeredState
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress (some n)).symm) x) t =
      Tomabechi.Consistency.R3.commonBaseV0 x t
  common_concept_finite24_value_shared_base : ∀ (n : ℕ) (x : AgentState)
      (hx : x ∈ box) (T : ℝ),
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimalValue
      (Tomabechi.Consistency.R1.layerAddressEmbedding (some n))
      (cast (congrArg C6LayeredState
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress (some n)).symm) x) T =
    ∫ s, theorem26DiscountWeight 1 T s *
      Tomabechi.Consistency.R3.commonBaseV0
        (controlledConsensusState x T c1MaxGainSignal s) s
      ∂(futureLebesgueMeasure T)
  /-- Preserve the complete quantitative C1 entry conclusions, including the
  shared-baseline Theorem 4/20 cost and target clauses, in the same witness. -/
  shared_base_entry_results : ∀ (x : AgentState) (hx : x ∈ box)
      (t₀ T : ℝ) (ht₀ : 0 ≤ t₀) (hT : 0 < T),
    Tomabechi.Consistency.ConsistencyC1CommonModel.C1EntryConclusions x t₀ T
  /-- At the embedded top address, Theorem 24 cost is exactly the preserved
  C5 source-layer cost after the explicit dependent-index cast. -/
  common_concept_top24_c5_cost : ∀
      (π : C6LayeredPolicy (⊤ : WithTop ℕ))
      (x : C6LayeredState (⊤ : WithTop ℕ)) (t : ℝ),
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.runningCost
      (Tomabechi.Consistency.R1.layerAddressEmbedding (⊤ : WithTop ℕ))
      (cast (congrArg C6LayeredPolicy
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress ⊤).symm) π)
      (cast (congrArg C6LayeredState
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress ⊤).symm) x) t =
      Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true
        π x t
  /-- The embedded top optimal value likewise recovers the C5 source value
  under the same type-index transport. -/
  common_concept_top24_c5_value : ∀
      (x : C6LayeredState (⊤ : WithTop ℕ)) (T : ℝ),
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimalValue
      (Tomabechi.Consistency.R1.layerAddressEmbedding (⊤ : WithTop ℕ))
      (cast (congrArg C6LayeredState
        (Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress ⊤).symm) x) T =
      Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        x T
  common_concept_top24_address :
    Tomabechi.Consistency.R1.layerAddressEmbedding (⊤ : WithTop ℕ) = ⊤
  common_concept_top26_dynamics :
    Tomabechi.Consistency.R1.FullCommonTopDynamicsExists
  common_concept_top27_path_transport : ∀
      (x : Tomabechi.Consistency.R1.fullCommonLayerState
        (⊤ : Tomabechi.Consistency.R1.CommonConcept)) (T s : ℝ),
    Tomabechi.Consistency.R1.fullCommonTheorem24Data.trajectory ⊤
      Tomabechi.Consistency.R1.fullCommonTopFeedback x T s =
      Tomabechi.Consistency.R1.fullCommonTopStateEquiv.symm
        (Tomabechi.Consistency.C6.c6TopPath
          (Tomabechi.Consistency.R1.fullCommonTopStateEquiv x) T s)
  common_concept_top27_feedback_transport : ∀
      (t : Set.Ici (0 : ℝ))
      (x : Tomabechi.Consistency.R1.fullCommonLayerState
        (⊤ : Tomabechi.Consistency.R1.CommonConcept)),
    (Tomabechi.Consistency.R1.fullCommonTopDynamics.policyEquiv
      Tomabechi.Consistency.R1.fullCommonTopDynamics.feedback).action (t, x) =
      (c6LayeredDynamics.policyEquiv c6LayeredDynamics.feedback).action
        (t, Tomabechi.Consistency.R1.fullCommonTopStateEquiv x)
  common_concept_top27_actuator_bridge : ∀
      (x : Tomabechi.Consistency.R1.fullCommonLayerState
      (⊤ : Tomabechi.Consistency.R1.CommonConcept)) (T : ℝ) (hT : 0 ≤ T),
    Tomabechi.Consistency.R1.CommonConceptTop27ActuatorBridge x T hT
  common_concept_top27_feedback_is_u0 : ∀
      (x : Tomabechi.Consistency.R1.fullCommonLayerState
        (⊤ : Tomabechi.Consistency.R1.CommonConcept)) (T s : ℝ)
      (hT : 0 ≤ T) (hs : T ≤ s),
    Tomabechi.Examples.Theorem27Op.u0E
        (Tomabechi.Consistency.R1.fullCommonTopStateEquiv x) T s =
      (Tomabechi.Consistency.R1.fullCommonTopDynamics.policyEquiv
        Tomabechi.Consistency.R1.fullCommonTopDynamics.feedback).action
        ⟨⟨s, hT.trans hs⟩,
          Tomabechi.Consistency.R1.fullCommonTheorem24Data.trajectory ⊤
            Tomabechi.Consistency.R1.fullCommonTopDynamics.feedback x T s⟩
  common_concept_top27_kernel_bridge : ∀
      (x : Tomabechi.Consistency.R1.fullCommonLayerState
        (⊤ : Tomabechi.Consistency.R1.CommonConcept)) (T : ℝ) (hT : 0 ≤ T),
    Tomabechi.Consistency.R1.CommonConceptTop27KernelBridge x T hT
  common_concept_top27_transported_conclusion : ∀
      (x : Tomabechi.Consistency.R1.fullCommonLayerState
        (⊤ : Tomabechi.Consistency.R1.CommonConcept)) (T : ℝ) (hT : 0 ≤ T),
    Tomabechi.Consistency.R1.fullCommonTopTheorem27Conclusion x T hT
  common_concept_top24_pzs_transport : ∀
      (x : Tomabechi.Consistency.R1.fullCommonLayerState
        (⊤ : Tomabechi.Consistency.R1.CommonConcept)) (t : ℝ),
    FeedbackPZS (Tomabechi.Consistency.R1.fullCommonTheorem24Data.admissible ⊤)
        futureLebesgueMeasure
        (fun π y a s => Tomabechi.Consistency.R1.fullCommonTheorem24Data.runningCost ⊤ π
          (Tomabechi.Consistency.R1.fullCommonTheorem24Data.trajectory ⊤ π y a s) s) x t ↔
      FeedbackPZS (Tomabechi.Consistency.C6.c6LayeredNonnegativeTimeData.admissible ⊤)
        futureLebesgueMeasure
        (fun π y a s => Tomabechi.Consistency.C6.c6LayeredNonnegativeTimeData.runningCost ⊤ π
          (Tomabechi.Consistency.C6.c6LayeredNonnegativeTimeData.trajectory ⊤ π y a s) s)
        (Tomabechi.Consistency.R1.fullCommonTopStateEquiv x) t
  common_concept_positive_entropy_address : ∀ p : Tomabechi.Consistency.C2.PositiveLayer,
    Tomabechi.Consistency.R1.commonConceptInformationLaw
        (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress p) =
      commonModel.informationLaw (p + 1) ∧
    Tomabechi.Consistency.C6.commonEntropyWeight
        (Tomabechi.Consistency.C6.entropyLayerAddress p) = commonModel.weight p ∧
    Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress p ≠ ⊥
  common_concept_positive_entropy_observation : ∀
      (p : Tomabechi.Consistency.C2.PositiveLayer)
      (z : Tomabechi.Consistency.C2.CompleteState),
    Tomabechi.Consistency.R1.commonConceptCompleteStateObservation commonModel
        (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress p) z =
      commonModel.layerObservation p z
  common_concept_physical_observation : ∀ z : Tomabechi.Consistency.C2.CompleteState,
    Tomabechi.Consistency.R1.commonConceptCompleteStateObservation commonModel ⊥ z =
      commonModel.physicalObservation z
  common_concept_entropy_balance_path : ∀ t : ℝ,
    commonModel.physicalObservation (commonModel.completePath t) +
      ∑' p : Tomabechi.Consistency.C2.PositiveLayer,
        commonEntropyWeight (entropyLayerAddress p) *
          Tomabechi.Consistency.R1.commonConceptCompleteStateObservation commonModel
            (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress p)
            (commonModel.completePath t) =
      1 + 3 * t
  common_concept_positive_entropy_path_ac : ∀
      (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
      (p : Tomabechi.Consistency.C2.PositiveLayer),
    AbsolutelyContinuousOnInterval
      (fun t => Tomabechi.Consistency.R1.commonConceptCompleteStateObservation commonModel
        (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress p)
        (commonModel.completePath t)) a b
  common_concept_physical_path_ac : ∀ (a b : ℝ), 0 ≤ a → a < b →
    AbsolutelyContinuousOnInterval
      (fun t => Tomabechi.Consistency.R1.commonConceptCompleteStateObservation commonModel ⊥
        (commonModel.completePath t)) a b
  common_concept_positive_entropy_endpoint_summable : ∀
      (a b : ℝ) (ha : 0 ≤ a) (hab : a < b),
    Summable (fun p : Tomabechi.Consistency.C2.PositiveLayer =>
      commonEntropyWeight (entropyLayerAddress p) *
        Tomabechi.Consistency.R1.commonConceptCompleteStateObservation commonModel
          (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress p)
          (commonModel.completePath a)) ∧
    Summable (fun p : Tomabechi.Consistency.C2.PositiveLayer =>
      commonEntropyWeight (entropyLayerAddress p) *
        Tomabechi.Consistency.R1.commonConceptCompleteStateObservation commonModel
          (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress p)
          (commonModel.completePath b))
  common_concept_positive_entropy_all_finite_ui : ∀
      (a b : ℝ) (ha : 0 ≤ a) (hab : a < b),
    UniformIntegrable
      (fun (s : Finset Tomabechi.Consistency.C2.PositiveLayer) t => ∑ p ∈ s,
        commonEntropyWeight (entropyLayerAddress p) *
          deriv (fun u => Tomabechi.Consistency.R1.commonConceptCompleteStateObservation
            commonModel (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress p)
            (commonModel.completePath u)) t)
      1 (volume.restrict (Set.uIoc a b))
  common_concept_positive_entropy_prefix_tendsto : ∀
      (a b : ℝ) (ha : 0 ≤ a) (hab : a < b),
    ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      Tendsto (fun k => ∑ i : Fin k,
        commonEntropyWeight
          (entropyLayerAddress
            (Tomabechi.Theorem15_23.countableLayerEnumeration
              Tomabechi.Consistency.C2.PositiveLayer i.val)) *
          deriv (fun u => Tomabechi.Consistency.R1.commonConceptCompleteStateObservation
            commonModel (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress
              (Tomabechi.Theorem15_23.countableLayerEnumeration
                Tomabechi.Consistency.C2.PositiveLayer i.val)) (commonModel.completePath u)) t)
        atTop
        (𝓝 (∑' p : Tomabechi.Consistency.C2.PositiveLayer,
          commonEntropyWeight (entropyLayerAddress p) *
            deriv (fun u => Tomabechi.Consistency.R1.commonConceptCompleteStateObservation
              commonModel (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress p)
              (commonModel.completePath u)) t))
  common_concept_A7_balance : ∀ (a b : ℝ), 0 ≤ a → a < b →
    ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      deriv (fun u => Tomabechi.Consistency.R1.commonConceptCompleteStateObservation
        commonModel ⊥ (commonModel.completePath u)) t =
      -(∑' p : Tomabechi.Consistency.C2.PositiveLayer,
        commonEntropyWeight (entropyLayerAddress p) *
          deriv (fun u => Tomabechi.Consistency.R1.commonConceptCompleteStateObservation
            commonModel (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress p)
            (commonModel.completePath u)) t) + 3
  common_concept_complete_path_nonrecurrence : ∀ (t₁ t₂ : ℝ),
    t₁ ∈ Set.Ici 0 → t₂ ∈ Set.Ici 0 → t₁ < t₂ →
      commonModel.completePath t₂ ≠ commonModel.completePath t₁
  /-- The minimizer selected for each lifted H-stage is its center in the
  shared CommonConcept representation. -/
  common_concept_h_stage_selected_minimizer : ∀ n,
    (Tomabechi.Consistency.R1.liftedHStageValleyWitness n).minimizer =
      Tomabechi.Consistency.R1.liftedStageCenter
        (Tomabechi.Consistency.C3.representation (n + 1))
  /-- Adjacent selected lifted valley minimizers remain positively separated. -/
  common_concept_h_stage_adjacent_minimizers_separated : ∀ n,
    0 < dist (Tomabechi.Consistency.R1.liftedHStageValleyWitness (n + 1)).minimizer
      (Tomabechi.Consistency.R1.liftedHStageValleyWitness n).minimizer
  /-- Full original 23-B switching conclusions, held alongside the lifted
  stage-center correspondence in this same acceptance witness. -/
  original_h_stage_switching_certificate :
    Tomabechi.Consistency.C3.HStageSwitchingCertificate
  /-- On each original 23-B dwell interval, the canonical stitched path
  lifted to the shared two-coordinate stage space follows that stage's
  selected lifted valley orbit exactly. -/
  common_concept_h_stage_stitched_dwell : ∀ n t,
    t ∈ Set.Icc (Tomabechi.Consistency.C3.stageTime n)
      (Tomabechi.Consistency.C3.stageTime n +
        Tomabechi.Consistency.C3.stageDuration n) →
    Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory t =
      (Tomabechi.Consistency.R1.liftedHStageValleyWitness n).orbit t
  /-- Every finite forward time belongs to a dwell interval, where the
  lifted stitched path is the selected lifted stage orbit. -/
  common_concept_h_stage_stitched_coverage : ∀ t,
    Tomabechi.Consistency.C3.stageTime 0 ≤ t →
    ∃ n, t ∈ Set.Ico (Tomabechi.Consistency.C3.stageTime n)
        (Tomabechi.Consistency.C3.stageTime n +
          Tomabechi.Consistency.C3.stageDuration n) ∧
      Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory t =
        (Tomabechi.Consistency.R1.liftedHStageValleyWitness n).orbit t
  /-- On the entire finite forward time domain, the lifted switched path is
  exactly the isometric image of the original canonical scalar path. -/
  common_concept_h_stage_stitched_path_transport : ∀ t,
    Tomabechi.Consistency.C3.stageTime 0 ≤ t →
      Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory t =
        Tomabechi.Consistency.R1.liftedStageCenter
          (Tomabechi.Consistency.C3.hStageSequenceStitchedTrajectory t)
  /-- The original endpoint error tolerance is unchanged by the lifted
  stage-center isometry. -/
  common_concept_h_stage_stitched_endpoint_error : ∀ n,
    dist
      (Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory
        (Tomabechi.Consistency.C3.stageTime n +
          Tomabechi.Consistency.C3.stageDuration n))
      (Tomabechi.Consistency.R1.liftedHStageValleyWitness n).minimizer ≤
      Tomabechi.Consistency.C3.errorTolerance n
  /-- The closure of each selected lifted stage orbit is exactly the
  isometric image of the original scalar stage's reachable closure. -/
  common_concept_h_stage_reachable_closure : ∀ n,
    closure ((Tomabechi.Consistency.R1.liftedHStageValleyWitness n).orbit ''
        Set.Ici (Tomabechi.Consistency.R1.liftedHStageInput n).startTime) =
      Tomabechi.Consistency.R1.liftedStageCenter '' closure
        ((Tomabechi.Consistency.C3.hStageSequenceValleys n).orbit ''
          Set.Ici (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).startTime)
  /-- The complete stage TCZ, including its region, reachable closure, and
  potential-gap condition, is exactly the image of the original scalar TCZ. -/
  common_concept_h_stage_tcz : ∀ n,
    Tomabechi.Consistency.R1.liftedHStageTCZ n =
      Tomabechi.Consistency.R1.liftedStageCenter ''
        Tomabechi.Consistency.C3.hStageSequenceTCZ n
  /-- The lifted 23-B stage TCZs are closed, nonempty, and still change
  between adjacent stages, as required by the switching conclusion. -/
  common_concept_h_stage_tcz_switching :
    (∀ n, IsClosed (Tomabechi.Consistency.R1.liftedHStageTCZ n)) ∧
    (∀ n, (Tomabechi.Consistency.R1.liftedHStageTCZ n).Nonempty) ∧
    (∀ n, Tomabechi.Consistency.R1.liftedHStageTCZ (n + 1) ≠
      Tomabechi.Consistency.R1.liftedHStageTCZ n)
  /-- At every embedded old address, the switched TCZ uses the same projected
  stage index as the CommonConcept H-stage family. -/
  common_concept_h_stage_tcz_old_address : ∀ a : WithTop ℕ,
    Tomabechi.Consistency.R1.commonConceptHStageTCZ
      (Tomabechi.Consistency.R1.layerAddressEmbedding a) =
      Tomabechi.Consistency.R1.liftedHStageTCZ (a.untopD 0)
  /-- The shared lattice top selects the initial H-stage switching TCZ. -/
  common_concept_h_stage_tcz_top :
    Tomabechi.Consistency.R1.commonConceptHStageTCZ
      (⊤ : Tomabechi.Consistency.R1.CommonConcept) =
      Tomabechi.Consistency.R1.liftedHStageTCZ 0
  /-- Every point of the CommonConcept lattice receives a closed, nonempty
  TCZ at its projected H-stage. -/
  common_concept_h_stage_tcz_all_points : ∀ x,
    IsClosed (Tomabechi.Consistency.R1.commonConceptHStageTCZ x) ∧
      (Tomabechi.Consistency.R1.commonConceptHStageTCZ x).Nonempty
  /-- Each lifted H-stage's atomic support, CommonConcept information law,
  and shared ModelSignature law refer to the same positive layer. -/
  common_concept_h_stage_information_address : ∀ n,
    Tomabechi.Consistency.R1.commonConceptInformationLaw
        (Tomabechi.Consistency.R1.layerAddressEmbedding
          (((n + 1 : ℕ) : WithTop ℕ))) = commonModel.informationLaw (n + 1) ∧
    commonModel.informationLaw (n + 1) = Tomabechi.Consistency.C3.upperJoint ∧
    (Tomabechi.Consistency.R1.liftedHStageInput n).averagePresentation.supportLub =
      ((n + 1 : ℕ) : Tomabechi.Consistency.C3.Atom)
  /-- The lifted H-stage uses the actual stage stored in this same
  ModelSignature: its diagonal mean field, sublevel, and effective potential
  recover that signature stage's scalar data. -/
  common_concept_h_stage_model_signature : ∀ n x,
    (Tomabechi.Consistency.R1.liftedHStageInput n).meanField
        (Tomabechi.Consistency.R1.liftedStageCenter x) =
      (commonModel.stages n).meanField x ∧
    (Tomabechi.Consistency.R1.liftedStageCenter x ∈
        (Tomabechi.Consistency.R1.liftedHStageInput n).sublevel ↔
      x ∈ (commonModel.stages n).sublevel) ∧
    Tomabechi.Theorem22.stageEffectivePotential
        ((Tomabechi.Consistency.R1.liftedHStageInput n).toStageValleySpec)
        (Tomabechi.Consistency.R1.liftedStageCenter x) =
      Tomabechi.Theorem22.stageEffectivePotential
        ((commonModel.stages n).toStageValleySpec) x
  /-- On the same complete state, the H-stage mean field is reconstructed
  from its CommonConcept positive-layer observation and cognitive coordinate.
  The latter is retained because the entropy observation stores its square. -/
  common_concept_h_stage_meanfield_from_complete_state : ∀ n
      (z : Tomabechi.Consistency.C2.CompleteState),
    2 * (commonModel.stages n).meanField
        (Tomabechi.Consistency.C2.cognitiveCoordinate z) =
      -(Tomabechi.Consistency.R1.commonConceptCompleteStateObservation commonModel
          (Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress n) z - 1) +
        2 * Tomabechi.Consistency.C3.representation (n + 1) *
          Tomabechi.Consistency.C2.cognitiveCoordinate z -
        (Tomabechi.Consistency.C3.representation (n + 1)) ^ 2

theorem commonModel_R1R2R3EntryIntegration : R1R2R3EntryIntegration commonModel := by
  refine ⟨commonModel_commonConceptInformationExperimentBridge,
    Tomabechi.Consistency.R1.commonConceptSCM_source_law_and_history,
    Tomabechi.Consistency.R1.commonConceptSCM_candidate_matches_old,
    Tomabechi.Consistency.R1.commonConceptMeasuredC3Model_noAtman,
    Tomabechi.Consistency.R1.commonConceptMeasuredC3Model_candidate_positive,
    Tomabechi.Consistency.R1.commonConceptTypedSelfProcess_satisfies25A2,
    Tomabechi.Consistency.R1.commonConceptTypedSelfProcess_representation,
    Tomabechi.Consistency.R1.fullCommonTheorem24_all_proper_points,
    (fun a x T hT =>
      ⟨Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimal_value_attained a x T hT,
        fun π hπ =>
          Tomabechi.Consistency.R1.fullCommonTheorem24Data.optimal_value_minimal
            a x T π hT hπ⟩),
    Tomabechi.Consistency.R1.fullCommon_top_theorem27_kernel,
    Tomabechi.Consistency.R1.fullCommon_top_actuatorInputs,
    Tomabechi.Consistency.R1.fullCommon_top_originalTopActuatorInputs,
    Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_optimalValue,
    Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_runningCost,
    Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_admissibility,
    Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_optimalPolicy,
    Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_trajectory,
    Tomabechi.Consistency.R1.commonConceptSCM_intervenedJoint_restricts_old,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (fun x t => Tomabechi.Consistency.R1.fullCommonTopPZS_transport x t),
    (fun p => ⟨
      Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress_law_eq
        commonModel commonModel_couplings p,
      Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress_weight_eq
        commonModel commonModel_couplings p,
      Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress_ne_bottom p⟩),
    (fun p z =>
      Tomabechi.Consistency.R1.commonConceptCompleteStateObservation_positive_address
        commonModel p z),
    (fun z =>
      Tomabechi.Consistency.R1.commonConceptCompleteStateObservation_bottom commonModel z),
    Tomabechi.Consistency.R1.commonConceptEntropyBalanceAlongPath,
    (fun a b ha hab p =>
      Tomabechi.Consistency.R1.commonConceptPositiveLayerPath_absolutelyContinuous
        commonModel commonModel_entropyInputs a b ha hab p),
    (fun a b ha hab =>
      Tomabechi.Consistency.R1.commonConceptPhysicalPath_absolutelyContinuous
        commonModel commonModel_entropyInputs a b ha hab),
    (fun a b ha hab =>
      Tomabechi.Consistency.R1.commonConceptPositiveLayerPath_endpoint_summable
        commonModel commonModel_couplings commonModel_entropyInputs a b ha hab),
    (fun a b ha hab =>
      Tomabechi.Consistency.R1.commonConceptPositiveLayerPath_all_finite_ui
        commonModel commonModel_couplings commonModel_entropyInputs a b ha hab),
    (fun a b ha hab =>
      Tomabechi.Consistency.R1.commonConceptPositiveLayerPath_prefix_tendsto
        commonModel commonModel_couplings commonModel_entropyInputs a b ha hab),
    (fun a b ha hab =>
      Tomabechi.Consistency.R1.commonConceptA7_balance
        commonModel commonModel_couplings commonModel_entropyInputs a b ha hab),
    commonModel_entropyInputs.nonrecurrence,
    Tomabechi.Consistency.R1.liftedHStageValleyWitness_minimizer_eq_center,
    Tomabechi.Consistency.R1.liftedHStageValleyWitness_adjacent_minimizers_separated,
    Tomabechi.Consistency.C3.hStageSequence_switching_certificate,
    Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory_eq_stageOrbit,
    Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory_covers_every_finite_time,
    Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory_eq_lifted_scalar,
    Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory_endpoint_error,
    Tomabechi.Consistency.R1.liftedHStageReachable_eq_liftedScalarImage,
    Tomabechi.Consistency.R1.liftedHStageTCZ_eq_lifted_scalar_image,
    ⟨Tomabechi.Consistency.R1.liftedHStageTCZ_closed,
      Tomabechi.Consistency.R1.liftedHStageTCZ_nonempty,
      Tomabechi.Consistency.R1.liftedHStageTCZ_adjacent_distinct⟩,
    Tomabechi.Consistency.R1.commonConceptHStageTCZ_at_oldAddress,
    Tomabechi.Consistency.R1.commonConceptHStageTCZ_at_top,
    Tomabechi.Consistency.R1.commonConceptHStageTCZ_closed_nonempty,
    (fun n => ⟨
      (Tomabechi.Consistency.R1.commonConceptInformationLaw_recovers_upper_address n).trans
        (commonModel_couplings.stage_information n).symm,
      commonModel_couplings.stage_information n,
      rfl⟩),
    (fun n x => by
      rw [commonModel_additionalConditions.original_stages]
      exact ⟨
        Tomabechi.Consistency.R1.liftedHStageInput_meanField_on_diagonal n x,
        Tomabechi.Consistency.R1.liftedHStageInput_diagonal_sublevel n x,
        Tomabechi.Consistency.R1.liftedHStageInput_effectivePotential_on_diagonal n x⟩),
    (fun n z => by
      rw [commonModel_additionalConditions.original_stages,
        Tomabechi.Consistency.R1.commonConceptCompleteStateObservation_positive_address,
        commonModel_couplings.layer_observation,
        Tomabechi.Consistency.R1.hStageSequence_meanField_matches_liftedPotential,
        Tomabechi.Consistency.C3.hStageSequence_center]
      simp [Tomabechi.Consistency.R1.liftedHStagePotential,
        Tomabechi.Consistency.R1.commonDiagonalAgentState,
        Tomabechi.Consistency.C2.layerEntropy,
        Tomabechi.Consistency.C2.cognitiveCoordinate]
      ring)⟩
  intro x hx t₀ ht₀
  refine ⟨Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter_initialSet x t₀,
    Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter_reachable x t₀, ?_⟩
  intro t ht
  exact Tomabechi.Consistency.R2.pointOptimalConsensusO24_distance x hx t₀ t ht₀ ht
  intro x hx hmean t₀ ht₀
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rw [Tomabechi.Consistency.R2.pointTheorem3Target_eq_singleton
      x hx hmean t₀ t ht₀]
    exact Set.singleton_nonempty _
  · intro t ht
    exact Tomabechi.Consistency.R2.consensusOptimalFlow_zeroMean_theorem3_residual_eq
      x hx hmean t₀ t ht
  · intro t ht
    exact Tomabechi.Consistency.R2.consensusOptimalFlow_pointTheorem3_distance
      x hx hmean t₀ t ht₀ ht
  intro x hx t₀ ht₀
  exact {
    closure_exact := Tomabechi.Consistency.R2.pointReachableClosure_eq_orbitSegment
      x t₀ ht₀
    closure_nonempty := Tomabechi.Consistency.R2.pointReachableClosure_nonempty
      x t₀ ht₀
    forward_invariant := by
      intro y hy s t hst
      exact Tomabechi.Consistency.R2.pointReachableClosure_forward_invariant
        x t₀ ht₀ hy hst
    theorem1_target_nonempty := Tomabechi.Consistency.R2.pointTheorem1Target_nonempty
      x hx t₀ t₀ ht₀
    theorem4_target_nonempty := Tomabechi.Consistency.R2.pointTheorem4Target_nonempty
      x hx t₀ t₀ ht₀
    shared_target_nonempty := by
      rw [Tomabechi.Consistency.R2.pointSharedTCZ_eq_singleton x hx t₀ t₀ ht₀]
      exact Set.singleton_nonempty _
    o24_tcz_singleton := by
      intro t
      exact Tomabechi.Consistency.R2.pointOptimalTCZ_eq_singleton x hx t₀ t ht₀
    o24_ego_feedback := by
      intro y t
      exact (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).ego_is_flow_feedback
        y t
    theorem1_distance_sq := by
      intro t ht
      exact Tomabechi.Consistency.R2.consensusOptimalFlow_pointTarget_distance_sq_le
        x hx t₀ t ht₀ ht
    theorem4_distance_sq := by
      intro t ht
      exact Tomabechi.Consistency.R2.consensusOptimalFlow_pointTheorem4_distance_sq_le
        x hx t₀ t ht₀ ht
    shared_distance := by
      intro t ht
      exact Tomabechi.Consistency.R2.consensusOptimalFlow_pointSharedTCZ_distance
        x hx t₀ t ht₀ ht
    theorem20_distance := by
      intro t ht
      exact Tomabechi.Consistency.R2.consensusOptimalFlow_pointTheorem20_distance
        x hx t₀ t ht₀ ht
  }
  intro n
  refine ⟨Tomabechi.Consistency.R1.liftedHStageInput n, rfl, ?_, ?_⟩
  · exact Tomabechi.Consistency.R1.liftedHStageInput_meanField_on_diagonal n
  · exact Tomabechi.Consistency.R1.liftedHStageInput_diagonal_sublevel n
  · exact Tomabechi.Consistency.R1.commonConceptHStageInput_eq_projected
  · exact Tomabechi.Consistency.R1.commonConceptHStageInput_at_properPoint
  · exact Tomabechi.Consistency.R1.commonConceptHStageInput_at_oldAddress
  · exact Tomabechi.Consistency.R1.commonConceptHStageInput_center
  · exact Tomabechi.Consistency.R1.commonConceptHStageInput_at_top
  · intro n
    constructor
    · rfl
    · change Tomabechi.Consistency.R1.liftedStageCenter
          (Tomabechi.Consistency.C3.representation (n + 1)) = _
      have hidx : (n : Tomabechi.Consistency.C3.Atom) + 1 =
          ((n + 1 : ℕ) : Tomabechi.Consistency.C3.Atom) := by simp
      rw [hidx, ← Tomabechi.Consistency.C3.hStageSequence_center n]
      exact congrArg Tomabechi.Consistency.R1.liftedStageCenter
        (Tomabechi.Consistency.R1.hStageSequence_center_matches_embedded_atomLayer n)
  · intro n
    exact Tomabechi.Consistency.R1.liftedHStageInput_selected_transition n
  · intro n x hx t ht
    exact Tomabechi.Consistency.R1.liftedHStageInput_orbit_forwardInvariant
      n x hx t ht
  · exact Tomabechi.Consistency.R1.liftedStageSelectedOrbit_distance
  · exact Tomabechi.Consistency.R1.liftedHStageInput_orbit_derivative
  · intro n π x hx t
    rw [Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_runningCost
      (some n) π x t]
    simp [c6LayeredNonnegativeTimeData, c6LayeredRunningCost,
      Tomabechi.Consistency.R3.commonBaseV0]
    rw [sharedPotential_eq_coupling x hx 0]
    norm_num [Tomabechi.Examples.Theorem2.γ]
    simp [halfDifference]
    ring
  · intro n x hx T
    rw [Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_optimalValue
      (some n) x T]
    simp [c6LayeredNonnegativeTimeData, c6LayeredOptimalValue]
    rw [← c1FiniteLayer_optimalValue_integral x T]
    have hpoint : ∀ s, T ≤ s →
        Tomabechi.Consistency.R3.commonBaseV0
            (controlledConsensusState x T c1MaxGainSignal s) s =
          1 + 8 * (halfDifference
            (controlledConsensusState x T c1MaxGainSignal s)) ^ 2 := by
      intro s hs
      have hsbox : controlledConsensusState x T c1MaxGainSignal s ∈ box :=
        controlledConsensusState_mem_box x hx T s c1MaxGainSignal hs
      rw [Tomabechi.Consistency.R3.commonBaseV0,
        sharedPotential_eq_coupling
          (controlledConsensusState x T c1MaxGainSignal s) hsbox 0]
      norm_num [Tomabechi.Examples.Theorem2.γ]
      dsimp [halfDifference]
      ring
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with s hs
    rw [hpoint s hs]
  · intro x hx t₀ T ht₀ hT
    exact Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness_entry_results
      x hx t₀ T ht₀ hT
  · intro π x t
    rw [Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_runningCost
      ⊤ π x t,
      Tomabechi.Consistency.C6.c6LayeredData_top_runningCost_fun]
  · intro x T
    rw [Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_optimalValue
      ⊤ x T,
      Tomabechi.Consistency.C6.c6LayeredData_top_optimalValue_fun]
  · change Tomabechi.Consistency.R1.layerAddress (⊤ : WithTop ℕ) = ⊤
    exact Tomabechi.Consistency.R1.layerAddress_top
  · exact Tomabechi.Consistency.R1.fullCommonTopDynamics_exists
  · exact Tomabechi.Consistency.R1.fullCommonTopTrajectory_eq_c6TopPath
  · exact Tomabechi.Consistency.R1.fullCommonTopFeedback_action_eq_old
  · exact Tomabechi.Consistency.R1.fullCommonTop27ActuatorBridge
  · exact Tomabechi.Consistency.R1.fullCommonTop27_u0_eq_transported_feedback
  · exact Tomabechi.Consistency.R1.fullCommonTop27KernelBridge
  · intro x T hT
    exact Tomabechi.Consistency.R1.fullCommonTopTheorem27Conclusion_of_kernelBridge
      x T hT (Tomabechi.Consistency.R1.fullCommonTop27KernelBridge x T hT)

/-- The point-initialized R2 consensus adapter in the integrated model also
retains its exact reachable geometry and its quantitative target estimates.
This packages the stronger R2 facts beside the O24 entry stored above. -/
theorem commonModel_point_R2_quantitative_acceptance
    (x : Tomabechi.Consistency.ConsistencyC1Consensus.AgentState)
    (hx : x ∈ Tomabechi.Consistency.ConsistencyC1Consensus.box) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (Tomabechi.Consistency.R2.pointReachableClosure x t₀ =
        Tomabechi.Consistency.R2.orbitSegment x) ∧
    (Tomabechi.Consistency.R2.pointReachableClosure x t₀).Nonempty ∧
    (∀ {y : Tomabechi.Consistency.ConsistencyC1Consensus.AgentState},
      y ∈ Tomabechi.Consistency.R2.pointReachableClosure x t₀ →
      ∀ {s t : ℝ}, s ≤ t →
        Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow.flow s y t ∈
          Tomabechi.Consistency.R2.pointReachableClosure x t₀) ∧
    (Tomabechi.Consistency.R2.pointTheorem1Target x t₀ t₀).Nonempty ∧
    (Tomabechi.Consistency.R2.pointTheorem4Target x t₀ t₀).Nonempty ∧
    (∀ t, t₀ ≤ t →
      (Metric.infDist
        (Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow.flow t₀ x t)
        (Tomabechi.Consistency.R2.pointTheorem1Target x t₀ t)) ^ 2 ≤
          Tomabechi.Examples.Theorem2.DA.potential x t₀ *
            Real.exp (-(6 : ℝ) * (t - t₀))) ∧
    (∀ t, t₀ ≤ t →
      (Metric.infDist
        (Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow.flow t₀ x t)
        (Tomabechi.Consistency.R2.pointTheorem4Target x t₀ t)) ^ 2 ≤
          Tomabechi.Examples.Theorem2.DA.potential x t₀ *
            Real.exp (-(6 : ℝ) * (t - t₀))) := by
  refine ⟨Tomabechi.Consistency.R2.pointReachableClosure_eq_orbitSegment x t₀ ht₀,
    Tomabechi.Consistency.R2.pointReachableClosure_nonempty x t₀ ht₀,
    ?_, Tomabechi.Consistency.R2.pointTheorem1Target_nonempty x hx t₀ t₀ ht₀,
    Tomabechi.Consistency.R2.pointTheorem4Target_nonempty x hx t₀ t₀ ht₀,
    ?_, ?_⟩
  · intro y hy s t hst
    exact Tomabechi.Consistency.R2.pointReachableClosure_forward_invariant
      x t₀ ht₀ hy hst
  · intro t ht
    exact Tomabechi.Consistency.R2.consensusOptimalFlow_pointTarget_distance_sq_le
      x hx t₀ t ht₀ ht
  · intro t ht
    exact Tomabechi.Consistency.R2.consensusOptimalFlow_pointTheorem4_distance_sq_le
      x hx t₀ t ht₀ ht

/-- The same point K also supports the shared-TCZ, Theorem 20, Theorem 3
zero-mean target, and typed O24 distance clauses. -/
theorem commonModel_point_R2_full_target_acceptance
    (x : Tomabechi.Consistency.ConsistencyC1Consensus.AgentState)
    (hx : x ∈ Tomabechi.Consistency.ConsistencyC1Consensus.box)
    (hmean : x 0 + x 1 = 0) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (Tomabechi.Consistency.R2.pointSharedTCZ x t₀ t₀).Nonempty ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist
        (Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow.flow t₀ x t)
        (Tomabechi.Consistency.R2.pointSharedTCZ x t₀ t) ≤
          Real.sqrt (Tomabechi.Examples.Theorem2.DA.potential x t₀) *
            Real.exp (-3 * (t - t₀))) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist
        (Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow.flow t₀ x t)
        (Tomabechi.Consistency.R2.pointTheorem20Target x t₀ t) ≤
          Real.sqrt (Tomabechi.Examples.Theorem2.DA.potential x t₀) *
            Real.exp (-3 * (t - t₀))) ∧
    (∀ t, ∃ z ∈ Tomabechi.Consistency.R2.pointReachableClosure x t₀,
      Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3StatePhi3 z t = 0) ∧
    (∀ t, (Tomabechi.Consistency.R2.pointTheorem3Target x t₀ t).Nonempty) ∧
    (∀ t, t₀ ≤ t →
      Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3StatePhi3
        (Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow.flow t₀ x t) t =
      Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3StatePhi3 x t₀ *
        Real.exp (-6 * (t - t₀))) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist
        (Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow.flow t₀ x t)
        (Tomabechi.Consistency.R2.pointTheorem3Target x t₀ t) ≤
          Real.sqrt (Tomabechi.Examples.Theorem2.DA.potential x t₀) *
            Real.exp (-3 * (t - t₀))) ∧
    (∀ t, (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).TCZ t =
      {Tomabechi.Consistency.R2.agreementPoint x}) ∧
    (∀ y t,
      (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).Ego y t =
        (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).flow.feedback y t) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist
        ((Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).flow.flow
          t₀ x t)
        ((Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).TCZ t) ≤
          Real.sqrt (Tomabechi.Examples.Theorem2.DA.potential x t₀) *
            Real.exp (-3 * (t - t₀))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Tomabechi.Consistency.R2.pointSharedTCZ_eq_singleton x hx t₀ t₀ ht₀]
    exact Set.singleton_nonempty _
  · intro t ht
    exact Tomabechi.Consistency.R2.consensusOptimalFlow_pointSharedTCZ_distance
      x hx t₀ t ht₀ ht
  · intro t ht
    exact Tomabechi.Consistency.R2.consensusOptimalFlow_pointTheorem20_distance
      x hx t₀ t ht₀ ht
  · intro t
    exact Tomabechi.Consistency.R2.pointReachableClosure_has_theorem3Target
      x hmean t₀ t ht₀
  · intro t
    rw [Tomabechi.Consistency.R2.pointTheorem3Target_eq_singleton
      x hx hmean t₀ t ht₀]
    exact Set.singleton_nonempty _
  · intro t ht
    exact Tomabechi.Consistency.R2.consensusOptimalFlow_zeroMean_theorem3_residual_eq
      x hx hmean t₀ t ht
  · intro t ht
    exact Tomabechi.Consistency.R2.consensusOptimalFlow_pointTheorem3_distance
      x hx hmean t₀ t ht₀ ht
  · intro t
    exact Tomabechi.Consistency.R2.pointOptimalTCZ_eq_singleton x hx t₀ t ht₀
  · intro y t
    exact (Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter x t₀).ego_is_flow_feedback
      y t
  · intro t ht
    exact Tomabechi.Consistency.R2.pointOptimalConsensusO24_distance
      x hx t₀ t ht₀ ht

/-- 存在宣言がR1情報実験・R2一点O24入口・R3共通基礎評価を同時に持つ。 -/
theorem integrated_model_exists_with_R1R2R3_entry_integration :
    ∃ M : ModelSignature,
      OriginalPremises M ∧ AdditionalConditions M ∧ Nondegenerate M ∧
      R1R2R3EntryIntegration M :=
  ⟨commonModel, commonModel_originalPremises, commonModel_additionalConditions,
    commonModel_nondegenerate, commonModel_R1R2R3EntryIntegration⟩

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.commonModel_originalPremises
#print axioms Tomabechi.Consistency.C6.commonModel_additionalConditions
#print axioms Tomabechi.Consistency.C6.integrated_model_exists
#print axioms Tomabechi.Consistency.C6.integrated_model_exists_with_common_concept_information_experiment
#print axioms Tomabechi.Consistency.C6.integrated_model_exists_with_R1R2R3_entry_integration
