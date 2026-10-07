import Tomabechi.Consistency.ConsistencyC6_Acceptance

/-!
# 共通概念束を添字とする共有データ署名

層別24データとその頂点26力学、SCM、情報law、完全状態pathと観測、
H-stage族、C1射影、一点到達adapter、基礎評価を実データとして保持する。
保存条件は引数Nのfield間で述べる。具体証人への代入だけで全原文条件の
監査を代替しない。ここでの受入はデータ共有の範囲であり、一般入口の
残る解析条件は別途この署名上で証明する必要がある。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.C2
open Tomabechi.Consistency.R1 Tomabechi.Consistency.C3
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1O24
open Tomabechi.Theorem24_26 Tomabechi.Theorem16_25
open Tomabechi.Examples.Theorem27

/-- 共通束全体の依存状態・方策族を持つ署名。
状態/方策carrierは輸送済みの型を固定し、実データは各Nのfieldから読む。 -/
structure SharedModelSignature where
  legacy : ModelSignature
  data : Theorem24NonnegativeTimeData fullCommonLayerState fullCommonLayerPolicy
  dynamics : Theorem26NonnegativeTimeDynamics data E2
  scm : Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool CommonConcept Bool
    (Bool × Bool) (fun _ => Unit) (fun _ => CommonConceptGamma)
    (fun _ => Bool) (fun _ => Bool)
  informationLaw : CommonConcept → Measure (Unit × Bool × Bool)
  completePath : ℝ → CompleteState
  observation : CommonConcept → CompleteState → ℝ
  weight : CommonConcept → ℝ
  stages : ℕ → Tomabechi.Theorem22.MeanFieldStageInput LiftedStageState
  stageFamily : CommonConcept → Tomabechi.Theorem22.MeanFieldStageInput LiftedStageState
  stageAddress : ℕ → CommonConcept
  scalarStitchedPath : ℝ → ℝ
  liftedStitchedPath : ℝ → LiftedStageState
  finiteProjection : ℝ → ℝ → CompleteState → AgentState
  topProjection : CompleteState → C6TopState
  pointAdapter : AgentState → (t₀ : ℝ) → C1OptimalConsensusAdapter t₀
  base : Tomabechi.Consistency.R3.C1CommonBaseContract

/-- 既存証人をデータとして代入する。保存条件の証明は次のrecordに分離する。 -/
def sharedModel : SharedModelSignature where
  legacy := commonModel
  data := fullCommonTheorem24Data
  dynamics := fullCommonTopDynamics
  scm := commonConceptMeasuredC3Model
  informationLaw := commonConceptInformationLaw
  completePath := commonModel.completePath
  observation := commonConceptCompleteStateObservation commonModel
  weight := fun a => commonEntropyWeight (layerProjection a)
  stages := liftedHStageInput
  stageFamily := commonConceptHStageInput
  stageAddress := commonConceptPositiveEntropyAddress
  scalarStitchedPath := hStageSequenceStitchedTrajectory
  liftedStitchedPath := liftedHStageStitchedTrajectory
  finiteProjection := commonModel.finiteProjection
  topProjection := commonModel.topProjection
  pointAdapter := Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter
  base := commonModel.c1.sharedBaseCandidate

/-- 同じ署名のデータ間で要求する共有保存式。
固定した別モデルの結論を並べるだけではこのrecordを構成できない。 -/
structure SharedDataPreservation (N : SharedModelSignature) : Prop where
  legacy_couplings : CommonDataCouplings N.legacy
  rho : N.data.rho = N.legacy.data.rho
  trajectory : ∀ a π x T t,
    N.data.trajectory a π x T t =
      N.legacy.data.trajectory (fullCommonLayerIndex a) π x T t
  runningCost : ∀ a π x t,
    N.data.runningCost a π x t =
      N.legacy.data.runningCost (fullCommonLayerIndex a) π x t
  admissible : ∀ a π x T, N.data.admissible a π x T ↔
    N.legacy.data.admissible (fullCommonLayerIndex a) π x T
  optimalValue : ∀ a x T,
    N.data.optimalValue a x T =
      N.legacy.data.optimalValue (fullCommonLayerIndex a) x T
  optimalPolicy : ∀ a x T,
    N.data.optimalPolicy a x T =
      N.legacy.data.optimalPolicy (fullCommonLayerIndex a) x T
  top_feedback : N.dynamics.feedback =
    fullCommonTopPolicyEquiv.symm N.legacy.dynamics.feedback
  top_feedback_action : ∀ t x,
    (N.dynamics.policyEquiv N.dynamics.feedback).action (t, x) =
      (N.legacy.dynamics.policyEquiv N.legacy.dynamics.feedback).action
        (t, fullCommonTopStateEquiv x)
  top_alive : ∀ x, x ∈ N.dynamics.alive ↔
    fullCommonTopStateEquiv x ∈ N.legacy.dynamics.alive
  top_lyapunov : ∀ x t, N.dynamics.W x t =
    N.legacy.dynamics.W (fullCommonTopStateEquiv x) t
  top_rate : N.dynamics.rate = N.legacy.dynamics.rate
  top_c₁ : N.dynamics.c₁ = N.legacy.dynamics.c₁
  top_c₂ : N.dynamics.c₂ = N.legacy.dynamics.c₂
  scm_law : N.scm.model.scm.exogenousLaw = N.legacy.scm.model.scm.exogenousLaw
  scm_history : N.scm.model.scm.globalHistory = N.legacy.scm.model.scm.globalHistory
  information : ∀ a, N.informationLaw a =
    N.legacy.informationLaw (commonConceptInformationIndex a)
  completePath : N.completePath = N.legacy.completePath
  physical : ∀ z, N.observation ⊥ z = N.legacy.physicalObservation z
  positive : ∀ p z, N.observation (commonConceptPositiveEntropyAddress p) z =
    N.legacy.layerObservation p z
  weight : ∀ p, N.weight (commonConceptPositiveEntropyAddress p) = N.legacy.weight p
  stageAddress : ∀ n, N.stageAddress n = commonConceptPositiveEntropyAddress n
  stageFamily : ∀ a, N.stageFamily a = N.stages ((layerProjection a).untopD 0)
  stage_meanField : ∀ n q,
    (N.stages n).meanField (liftedStageCenter q) = (N.legacy.stages n).meanField q
  stage_sublevel : ∀ n q,
    liftedStageCenter q ∈ (N.stages n).sublevel ↔ q ∈ (N.legacy.stages n).sublevel
  stage_potential : ∀ n q,
    Tomabechi.Theorem22.stageEffectivePotential (N.stages n).toStageValleySpec
        (liftedStageCenter q) =
      Tomabechi.Theorem22.stageEffectivePotential (N.legacy.stages n).toStageValleySpec q
  stage_information : ∀ n, N.informationLaw (N.stageAddress n) =
    N.legacy.informationLaw (n + 1)
  meanField_observation : ∀ n z,
    2 * (N.stages n).meanField (liftedStageCenter (cognitiveCoordinate z)) =
      -(N.observation (N.stageAddress n) z - 1) +
        2 * representation (n + 1) * cognitiveCoordinate z - (representation (n + 1)) ^ 2
  cognitive_path : ∀ t, stageTime 0 ≤ t →
    cognitiveCoordinate (N.completePath t) = N.scalarStitchedPath t
  physical_path : ∀ t, stageTime 0 ≤ t →
    physicalCoordinate (N.completePath t) = 3 * t - (N.scalarStitchedPath t) ^ 2
  lifted_path : ∀ t, stageTime 0 ≤ t →
    liftedStageCenter (cognitiveCoordinate (N.completePath t)) = N.liftedStitchedPath t
  finiteProjection : N.finiteProjection = N.legacy.finiteProjection
  topProjection : N.topProjection = N.legacy.topProjection
  point_initial : ∀ x t₀, (N.pointAdapter x t₀).initialSet = {x}
  point_flow : ∀ x t₀, (N.pointAdapter x t₀).flow = N.legacy.c1.selectedFlow
  point_reachable : ∀ x t₀, (N.pointAdapter x t₀).reachable =
    Tomabechi.Theorem1.closedLoopReachableSet
      (Tomabechi.Theorem1.policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀)
  base : N.base = N.legacy.c1.sharedBaseCandidate

/-- 署名引数を読む保存式を、既存の共有モデルと輸送補題から構成する。 -/
theorem sharedModel_preservation : SharedDataPreservation sharedModel := by
  refine {
    legacy_couplings := commonModel_couplings
    rho := rfl
    trajectory := by intros; rfl
    runningCost := by intros; rfl
    admissible := by intros; rfl
    optimalValue := by intros; rfl
    optimalPolicy := by intros; rfl
    top_feedback := rfl
    top_feedback_action := ?_
    top_alive := fullCommonTopAlive_mem_iff
    top_lyapunov := by intros; rfl
    top_rate := rfl
    top_c₁ := rfl
    top_c₂ := rfl
    scm_law := ?_
    scm_history := ?_
    information := ?_
    completePath := rfl
    physical := commonConceptCompleteStateObservation_bottom commonModel
    positive := commonConceptCompleteStateObservation_positive_address commonModel
    weight := ?_
    stageAddress := by intros; rfl
    stageFamily := ?_
    stage_meanField := ?_
    stage_sublevel := ?_
    stage_potential := ?_
    stage_information := ?_
    meanField_observation := ?_
    cognitive_path := commonModel_completePath_cognitive
    physical_path := commonModel_completePath_physical
    lifted_path := commonModel_completePath_cognitive_lift
    finiteProjection := rfl
    topProjection := rfl
    point_initial := Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter_initialSet
    point_flow := by intros; rfl
    point_reachable := ?_
    base := rfl }
  · exact fullCommonTopFeedback_action_eq_old
  · exact commonConceptSCM_source_law_and_history.1
  · exact commonConceptSCM_source_law_and_history.2
  · intro a
    exact (commonConceptInformationLaw_eq_modelLaw commonModel commonModel_couplings a).symm
  · intro p
    change commonEntropyWeight
      (layerProjection (layerAddress (entropyLayerAddress p))) = commonModel.weight p
    rw [layerProjection_layerAddress]
    exact commonConceptPositiveEntropyAddress_weight_eq commonModel commonModel_couplings p
  · intro a
    change commonConceptHStageInput a = liftedHStageInput ((layerProjection a).untopD 0)
    rw [commonConceptHStageInput_eq_projected]
    cases layerProjection a <;> rfl
  · intro n q
    exact (commonModel_R1R2R3EntryIntegration.common_concept_h_stage_model_signature n q).1
  · intro n q
    exact (commonModel_R1R2R3EntryIntegration.common_concept_h_stage_model_signature n q).2.1
  · intro n q
    exact (commonModel_R1R2R3EntryIntegration.common_concept_h_stage_model_signature n q).2.2
  · intro n
    exact (commonModel_R1R2R3EntryIntegration.common_concept_h_stage_information_address n).1
  · intro n z
    change 2 * (liftedHStageInput n).meanField (liftedStageCenter (cognitiveCoordinate z)) = _
    rw [(commonModel_R1R2R3EntryIntegration.common_concept_h_stage_model_signature
      n (cognitiveCoordinate z)).1]
    exact commonModel_R1R2R3EntryIntegration.common_concept_h_stage_meanfield_from_complete_state n z
  · intro x t₀
    rw [← Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter_initialSet x t₀]
    exact Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter_reachable x t₀

/-- 外部モデル前提なしの共有データ存在。全原文条件の最終存在宣言は別途必要。 -/
theorem shared_data_model_exists : ∃ N : SharedModelSignature,
    SharedDataPreservation N ∧ OriginalPremises N.legacy ∧
      AdditionalConditions N.legacy ∧ Nondegenerate N.legacy :=
  ⟨sharedModel, sharedModel_preservation, commonModel_originalPremises,
    commonModel_additionalConditions, commonModel_nondegenerate⟩

#print axioms shared_data_model_exists
end Tomabechi.Consistency.R123
