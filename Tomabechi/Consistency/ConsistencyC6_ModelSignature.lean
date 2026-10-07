import Tomabechi.Consistency.ConsistencyC6_TopActuator

/-!
# C6：実共有データ署名とデータから読む保存条件

独立証人のtupleではなく、制御核・層別費用・完全path・履歴固定点・SCMを保持し、
同じ署名のフィールドを参照する保存式を別の命題として課す。
このファイルの共通保存条件だけでは全原文入口と非退化性の最終監査を代替しない。
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

abbrev C6MeasuredSCM := Theorem25MeasuredSharedGlobalHistoryC3Model
  Bool Bool CommonLayer Bool (Bool × Bool) (fun _ => Unit)
  (fun _ => C6FullLayerGamma) (fun _ => Bool) (fun _ => Bool)

/-- 固定した共通層・主体・履歴・認知状態型を持つモデルの実データ。
proof-bearingデータD/E/C1/stage/SCMの値も、後の具体constructorで外部仮定なしに供給する。 -/
structure ModelSignature where
  data : Theorem24NonnegativeTimeData C6LayeredState C6LayeredPolicy
  dynamics : Theorem26NonnegativeTimeDynamics data C6TopState
  c1 : C1Witness
  step : ℝ → ℝ → ℝ → CompleteState → CompleteState
  potential : ℝ → CompleteState → ℝ
  finiteProjection : ℝ → ℝ → CompleteState → AgentState
  topProjection : CompleteState → C6TopState
  completePath : ℝ → CompleteState
  physicalObservation : CompleteState → ℝ
  layerObservation : PositiveLayer → CompleteState → ℝ
  weight : PositiveLayer → ℝ
  stages : ℕ → Tomabechi.Theorem22.MeanFieldStageInput ℝ
  stageTime : ℕ → ℝ
  stageInitial : ℕ → CompleteState
  historyCenter : Bool → ℝ
  historyFlow : Bool → ℝ → ℝ → ℝ
  fixedPoints : HistoryFixedPoints Bool (ℕ → ℝ)
  scm : C6MeasuredSCM
  selfRepresentation : Bool → C6TypedSelfRepresentation
  informationLaw : ℕ → Measure (Unit × Bool × Bool)
  informationPolicy : Bool → C1GainSignal

/-- SCMに同じ観測を施した型付き自己過程jointの構造式。
別のSCMや履歴lawを引数から注入しない。 -/
def ModelSignature.baselineSelfObservation (M : ModelSignature) (d h : Bool)
    (a : CommonLayer) (u : Bool × Bool) : (C6FullLayerGamma × C6TypedSelfRepresentation) × Bool :=
  let y := M.scm.model.scm.outputEquation d a h u (M.scm.model.scm.candidateVariable d a u)
  ((M.scm.model.scm.stateEquation d a h u, M.selfRepresentation y), y)

def ModelSignature.experimentInputLaw (M : ModelSignature) (k : ℕ) : Measure C6ExperimentInput :=
  M.scm.model.scm.exogenousLaw.toMeasure.prod (M.informationLaw k)

/-- 同じMの情報行為・実D状態・費用・自己過程を観測する。 -/
def ModelSignature.experimentObservation (M : ModelSignature) (d h : Bool) (k : ℕ)
    (x : AgentState) (T t : ℝ) (w : C6ExperimentInput) : C6ExperimentObservation :=
  let policy := M.informationPolicy w.2.2.2
  let state := M.data.trajectory (some k) policy x T t
  (w, (M.baselineSelfObservation d h (some k) w.1,
    (state, M.data.runningCost (some k) policy state t)))

def ModelSignature.experimentLaw (M : ModelSignature) (d h : Bool) (k : ℕ)
    (x : AgentState) (T t : ℝ) : Measure C6ExperimentObservation :=
  (M.experimentInputLaw k).map (M.experimentObservation d h k x T t)

/-- S1–S7の主要保存式。すべて同じMの実データから読む。
全O条件・全非退化性の最終受入は後続の条件recordで補う。 -/
structure CommonDataCouplings (M : ModelSignature) : Prop where
  core_cognitive : ∀ c A E z,
    cognitiveCoordinate (M.step c A E z) =
      c + (cognitiveCoordinate z - c) * Real.exp (-A)
  core_entropy : ∀ c A E z,
    M.physicalObservation (M.step c A E z) + (cognitiveCoordinate (M.step c A E z)) ^ 2 =
      M.physicalObservation z + (cognitiveCoordinate z) ^ 2 + E
  potential_formula : ∀ c z, M.potential c z = (cognitiveCoordinate z - c) ^ 2 / 2
  layer_weight : M.weight = layerWeight
  physical_observation : M.physicalObservation = physicalEntropy
  layer_observation : M.layerObservation = layerEntropy
  original_stage_data : M.stages = Tomabechi.Consistency.C3.hStageSequence
  finite_trajectory : ∀ k u x T t,
    M.data.trajectory (some k) u x T t = controlledConsensusState x T u t
  c1_selected_flow : ∀ k x T t,
    M.c1.selectedFlow.flow T x t = M.data.trajectory (some k) M.c1.selectedGain x T t
  core_all_finite_controls : ∀ k m c T t E z u,
    M.finiteProjection m c (M.step c (c1AccumulatedGain u T t) E z) =
      M.data.trajectory (some k) u (M.finiteProjection m c z) T t
  core_finite_cost : ∀ k u m c t z,
    M.data.runningCost (some k) u (M.finiteProjection m c z) t = 1 + 16 * M.potential c z
  stage_effective_potential : ∀ n z,
    Tomabechi.Theorem22.stageEffectivePotential (M.stages n).toStageValleySpec (cognitiveCoordinate z) =
      M.potential (Tomabechi.Consistency.C3.representation (n + 1 : ℕ)) z
  stage_path : ∀ n t, t ∈ Set.Ico (M.stageTime n) (M.stageTime (n + 1)) →
    M.completePath t = M.step (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
      (t - M.stageTime n) (3 * (t - M.stageTime n)) (M.stageInitial n)
  entropy_observation : ∀ t,
    M.physicalObservation (M.completePath t) +
      ∑' n, M.weight n * M.layerObservation n (M.completePath t) = 1 + 3 * t
  history_flow : ∀ h x y t E,
    cognitiveCoordinate (M.step (M.historyCenter h) t E (x, y)) = M.historyFlow h x t
  fixedPoint_gamma : ∀ d a h u,
    M.scm.model.scm.stateEquation d a h u =
      M.scm.model.presenceAndRelations.relationalState d
        (decide ((M.fixedPoints.fixedPoint h).1 0 = 1)) a
  scm_output_history : ∀ d a h u s, M.scm.model.scm.outputEquation d a h u s = h
  self_ego : ∀ h i x, (M.selfRepresentation h).Ego i x =
    theorem16_intervalGradientFlowFeedback h i x
  self_tcz : ∀ h i, (M.selfRepresentation h).TCZ i =
    Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4TCZ h
  top_cost : ∀ π z t,
    M.data.runningCost ⊤ π (M.topProjection z) t = 6 * M.potential 1 z
  top_value : ∀ z t,
    M.data.optimalValue ⊤ (M.topProjection z) t = 2 * M.potential 1 z
  core_all_top_controls : ∀ π x T t,
    M.topProjection (M.step 1
      ((1 / 2) * (t - T) +
        Tomabechi.Examples.Theorem26_27ControlClasses.measurableAccumulatedGain
          (Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain π) T t)
      (t - T) (vectorStateToCompleteState x)) = M.data.trajectory ⊤ π x T t
  physical_information : M.informationLaw 0 = Tomabechi.Consistency.C3.physicalLayerLaw.joint
  stage_information : ∀ n, M.informationLaw (n + 1) = Tomabechi.Consistency.C3.upperJoint
  information_input_code : ∀ g t,
    c6EncodeRate3AsSCMAction ((M.informationPolicy g).1 t) = g
  information_optimal : ∀ k x t, M.informationPolicy true = M.data.optimalPolicy (some k) x t
  experiment_information : ∀ d h k x T t,
    (M.experimentLaw d h k x T t).map (fun z => z.1.2) = M.informationLaw k
  experiment_self : ∀ d h k x T t,
    (M.experimentLaw d h k x T t).map (fun z => z.2.1) =
      (M.scm.model.scm.exogenousLaw.toMeasure).map (M.baselineSelfObservation d h (some k))

/-- 全共有データの具体値。各成分を局所証人へ戻す保存式は直後の定理で供給する。 -/
def commonModel : ModelSignature where
  data := c6CommonLayerData
  dynamics := c6CommonLayerDynamics
  c1 := c1Witness
  step := centeredGainEntropyStep
  potential := centeredQuadraticPotential
  finiteProjection := centeredC1Projection
  topProjection := disagreementStateTo27
  completePath := c3A7StitchedTrajectory
  physicalObservation := physicalEntropy
  layerObservation := layerEntropy
  weight := layerWeight
  stages := Tomabechi.Consistency.C3.hStageSequence
  stageTime := Tomabechi.Consistency.C3.stageTime
  stageInitial := c3A7StageInitial
  historyCenter := theorem16_intervalGradientCenter
  historyFlow := theorem16_intervalGradientFlow
  fixedPoints := theorem16_intervalGradientFlowFixedPoints
  scm := c6FullLayerMeasuredC3Model
  selfRepresentation := c6TypedSelfRepresentation
  informationLaw := c6LayerInformationLaw
  informationPolicy := c6InformationPolicy

/-- 同じ署名で制御・評価・完全path・固定点Γ・情報/自己過程lawを同時に保存する。 -/
theorem commonModel_couplings : CommonDataCouplings commonModel := by
  refine {
    core_cognitive := centeredGainEntropyStep_cognitive
    core_entropy := centeredGainEntropyStep_entropy
    potential_formula := by intros; rfl
    layer_weight := rfl
    physical_observation := rfl
    layer_observation := rfl
    original_stage_data := rfl
    finite_trajectory := by intros; rfl
    c1_selected_flow := by
      intro k x T t
      exact (c6FiniteData_positiveLayer_selectedFlow 0 x T t).symm
    core_all_finite_controls := ?_
    core_finite_cost := centeredC1Projection_runningCost
    stage_effective_potential := centeredQuadraticPotential_eq_C3_stage
    stage_path := c3A7StitchedTrajectory_eq_stage
    entropy_observation := ?_
    history_flow := centeredGainEntropyStep_projects_C4_history_flow
    fixedPoint_gamma := by intros; rfl
    scm_output_history := fun d a h u s => c6FullLayer_output_eq_history d h s a u
    self_ego := c6TypedSelfRepresentation_ego_feedback
    self_tcz := ?_
    top_cost := ?_
    top_value := ?_
    core_all_top_controls := centeredGainEntropyStep_projects_C5_data_trajectory
    physical_information := by rfl
    stage_information := c6LayerInformationLaw_stage
    information_input_code := c6InformationPolicy_code
    information_optimal := c6InformationPolicy_optimal
    experiment_information := c6ExperimentLaw_information
    experiment_self := c6ExperimentLaw_selfProcess }
  · intro k m c T t E z u
    exact centeredC1Projection_all_controls m c T t E z u
  · intro t
    exact c3A7StitchedTrajectory_generalizedEntropy t
  · intro h i
    exact Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4LayerCarrier_eq_TCZ h i
  · intro π z t
    exact c5RunningCost_eq_six_centeredPotential z π t
  · intro z t
    exact c5OptimalValue_eq_two_centeredPotential z t

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.commonModel_couplings
