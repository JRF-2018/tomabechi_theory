import Tomabechi.Consistency.ConsistencyR123_SharedSCM

/-!
# 同じ共有署名の情報・自己過程・制御状態・費用の実験

情報ラベルをNに格納された許容方策へ復号し、同じ有限層N.dataの軌道と
走行費を観測する。二値ラベルは許容制御族の部分族を指定する。
旧署名の実験joint全体との一致はΓ制限観測を通して証明する。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Theorem16_25
open Tomabechi.Consistency.R1 Tomabechi.Consistency.C6
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus

/-- 有限層の型同定。状態・方策のcastを同じ住所で行う。 -/
private theorem finiteIndex (k : ℕ) : fullCommonLayerIndex (layerAddressEmbedding (k : WithTop ℕ)) =
    (k : WithTop ℕ) := fullCommonLayerIndex_layerAddress k

/-- N.dataの実有限層軌道をAgentState座標で観測する。 -/
def SharedModelSignature.finiteExperimentState (N : SharedModelSignature) (k : ℕ)
    (u : C1GainSignal) (x : AgentState) (T t : ℝ) : AgentState :=
  cast (congrArg C6LayeredState (finiteIndex k))
    (N.data.trajectory (layerAddressEmbedding (k : WithTop ℕ))
      (cast (congrArg C6LayeredPolicy (finiteIndex k).symm) u)
      (cast (congrArg C6LayeredState (finiteIndex k).symm) x) T t)

/-- 同じ実有限層軌道の同じ走行費。定数費用へ置き換えない。 -/
def SharedModelSignature.finiteExperimentCost (N : SharedModelSignature) (k : ℕ)
    (u : C1GainSignal) (x : AgentState) (T t : ℝ) : ℝ :=
  N.data.runningCost (layerAddressEmbedding (k : WithTop ℕ))
    (cast (congrArg C6LayeredPolicy (finiteIndex k).symm) u)
    (N.data.trajectory (layerAddressEmbedding (k : WithTop ℕ))
      (cast (congrArg C6LayeredPolicy (finiteIndex k).symm) u)
      (cast (congrArg C6LayeredState (finiteIndex k).symm) x) T t) t

private theorem trajectory_cast {I : Type*} {S P : I → Type*}
    (f : ∀ i, P i → S i → ℝ → ℝ → S i) {i j : I} (h : j = i)
    (π : P i) (x : S i) (a t : ℝ) :
    cast (congrArg S h) (f j (cast (congrArg P h.symm) π)
      (cast (congrArg S h.symm) x) a t) = f i π x a t := by
  cases h
  rfl

private theorem cost_cast {I : Type*} {S P : I → Type*}
    (f : ∀ i, P i → S i → ℝ → ℝ → S i) (c : ∀ i, P i → S i → ℝ → ℝ)
    {i j : I} (h : j = i) (π : P i) (x : S i) (a t : ℝ) :
    c j (cast (congrArg P h.symm) π)
      (f j (cast (congrArg P h.symm) π) (cast (congrArg S h.symm) x) a t) t =
      c i π (f i π x a t) t := by
  cases h
  rfl

/-- Nの保存式により有限層の実状態を旧署名の同じ制御へ回収する。 -/
theorem SharedDataPreservation.finiteExperimentState {N : SharedModelSignature}
    (h : SharedDataPreservation N) (k u x T t) :
    N.finiteExperimentState k u x T t = N.legacy.data.trajectory (some k) u x T t := by
  unfold SharedModelSignature.finiteExperimentState
  rw [h.trajectory]
  exact trajectory_cast N.legacy.data.trajectory (finiteIndex k) u x T t

/-- 実費用も同じ署名の同じ実状態で一致する。 -/
theorem SharedDataPreservation.finiteExperimentCost {N : SharedModelSignature}
    (h : SharedDataPreservation N) (k u x T t) :
    N.finiteExperimentCost k u x T t =
      N.legacy.data.runningCost (some k) u (N.legacy.data.trajectory (some k) u x T t) t := by
  unfold SharedModelSignature.finiteExperimentCost
  rw [h.runningCost, h.trajectory]
  exact cost_cast N.legacy.data.trajectory N.legacy.data.runningCost (finiteIndex k) u x T t

/-- 全有限旧アドレスで情報lawの番号も保存される。 -/
theorem sharedInformationIndex_finite (k : ℕ) :
    commonConceptInformationIndex (layerAddressEmbedding (k : WithTop ℕ)) = k := by
  cases k with
  | zero => exact commonConceptInformationIndex_old_zero
  | succ n => exact commonConceptInformationIndex_old_positive n

/-- 同じN.scmの外生標本と同じN情報lawを使う実験入力。 -/
def SharedModelSignature.experimentInputLaw (N : SharedModelSignature) (k : ℕ) :
    Measure C6ExperimentInput :=
  N.scm.model.scm.exogenousLaw.toMeasure.prod
    (N.informationLaw (layerAddressEmbedding (k : WithTop ℕ)))

abbrev SharedExperimentObservation := C6ExperimentInput ×
  (((CommonConceptGamma × C6TypedSelfRepresentation) × Bool) × (AgentState × ℝ))

/-- N.scmの自己過程とN.dataの実制御状態/費用を同時に観測する。 -/
def SharedModelSignature.experimentObservation (N : SharedModelSignature) (d H : Bool)
    (k : ℕ) (x : AgentState) (T t : ℝ) (w : C6ExperimentInput) : SharedExperimentObservation :=
  let u := N.legacy.informationPolicy w.2.2.2
  (w, ((N.selfProcess d (layerAddressEmbedding (k : WithTop ℕ))).baselineEquation H w.1,
    (N.finiteExperimentState k u x T t, N.finiteExperimentCost k u x T t)))

def SharedModelSignature.experimentLaw (N : SharedModelSignature) (d H : Bool)
    (k : ℕ) (x : AgentState) (T t : ℝ) : Measure SharedExperimentObservation :=
  (N.experimentInputLaw k).map (N.experimentObservation d H k x T t)

/-- 全実験jointを旧署名へ戻す。標本・情報・自己表現・状態・費用を残す。 -/
def sharedExperimentRecovery (z : SharedExperimentObservation) : C6ExperimentObservation :=
  (z.1, (sharedRestrictTypedObservation z.2.1, z.2.2))

theorem sharedExperimentRecovery_measurable : Measurable sharedExperimentRecovery :=
  measurable_fst.prodMk
    ((sharedRestrictTypedObservation_measurable.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

/-- 共有保存条件から元の入力jointを厳密に回収する。 -/
theorem SharedDataPreservation.experimentInputLaw {N : SharedModelSignature}
    (h : SharedDataPreservation N) (k : ℕ) :
    N.experimentInputLaw k = N.legacy.experimentInputLaw k := by
  unfold SharedModelSignature.experimentInputLaw ModelSignature.experimentInputLaw
  rw [h.scm_law, h.information, sharedInformationIndex_finite]

/-- 旧住所の全SCM構造式と実制御状態/費用が同じ標本ごとに一致する。 -/
theorem SharedSCMCouplings.experimentObservation {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d H k x T t w) :
    sharedExperimentRecovery (N.experimentObservation d H k x T t w) =
      N.legacy.experimentObservation d H k x T t w := by
  dsimp [sharedExperimentRecovery, SharedModelSignature.experimentObservation,
    SharedModelSignature.selfProcess, SharedModelSignature.typedObservation,
    sharedRestrictTypedObservation, ModelSignature.experimentObservation,
    ModelSignature.baselineSelfObservation]
  rw [h.state, h.output, h.candidate,
    h.preservation.finiteExperimentState, h.preservation.finiteExperimentCost]
  rfl

/-- 実験joint全体が同じ旧署名のjointへ一致する。 -/
theorem SharedSCMCouplings.experimentLaw {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d H k x T t) :
    (N.experimentLaw d H k x T t).map sharedExperimentRecovery =
      N.legacy.experimentLaw d H k x T t := by
  rw [SharedModelSignature.experimentLaw,
    Measure.map_map sharedExperimentRecovery_measurable (measurable_of_finite _),
    h.preservation.experimentInputLaw]
  unfold ModelSignature.experimentLaw
  congr 1
  funext w
  exact h.experimentObservation d H k x T t w

/-- 同じNの実状態・実費用の周辺を、Nの入力lawから回収する。 -/
theorem SharedModelSignature.experiment_stateCost (N : SharedModelSignature) (d H k x T t) :
    (N.experimentLaw d H k x T t).map (fun z => z.2.2) =
      (N.experimentInputLaw k).map (fun w =>
        let u := N.legacy.informationPolicy w.2.2.2
        (N.finiteExperimentState k u x T t, N.finiteExperimentCost k u x T t)) := by
  rw [SharedModelSignature.experimentLaw,
    Measure.map_map
      (show Measurable (fun z : SharedExperimentObservation => z.2.2) from
        measurable_snd.comp measurable_snd) (measurable_of_finite _)]
  rfl

/-- 同じNの情報周辺は旧署名を経由しても変わらない。 -/
theorem SharedSCMCouplings.experiment_information {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d H k x T t) :
    (N.experimentLaw d H k x T t).map (fun z => z.1.2) =
      N.informationLaw (layerAddressEmbedding (k : WithTop ℕ)) := by
  have he := congrArg (fun μ : Measure C6ExperimentObservation => μ.map (fun z => z.1.2))
    (h.experimentLaw d H k x T t)
  rw [Measure.map_map
    (show Measurable (fun z : C6ExperimentObservation => z.1.2) from
      measurable_snd.comp measurable_fst) sharedExperimentRecovery_measurable,
    h.preservation.legacy_couplings.experiment_information] at he
  rw [h.preservation.information, sharedInformationIndex_finite]
  exact he

/-- 情報行為を実許容入力へ復号・再符号化したjointを保つ。 -/
theorem SharedSCMCouplings.experiment_actualPolicyInformation {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d H k x T t) :
    (N.experimentLaw d H k x T t).map
      (fun z => (z.1.2.1, z.1.2.2.1,
        c6EncodeRate3AsSCMAction ((N.legacy.informationPolicy z.1.2.2.2).1 t))) =
      N.informationLaw (layerAddressEmbedding (k : WithTop ℕ)) := by
  convert h.experiment_information d H k x T t using 1
  congr 1
  funext z
  rw [h.preservation.legacy_couplings.information_input_code]

/-- 有限層の実最適方策も同じ情報行為trueで指定される。 -/
theorem SharedSCMCouplings.information_optimal {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (k : ℕ) (x : AgentState) (t : ℝ) :
    cast (congrArg C6LayeredPolicy (finiteIndex k).symm) (N.legacy.informationPolicy true) =
      N.data.optimalPolicy (layerAddressEmbedding (k : WithTop ℕ))
        (cast (congrArg C6LayeredState (finiteIndex k).symm) x) t := by
  rw [h.preservation.optimalPolicy]
  have hf := h.preservation.legacy_couplings.information_optimal
  have hg : ∀ {i j : CommonLayer} (he : j = i) (x : C6LayeredState i),
      cast (congrArg C6LayeredPolicy he.symm) (N.legacy.data.optimalPolicy i x t) =
        N.legacy.data.optimalPolicy j (cast (congrArg C6LayeredState he.symm) x) t := by
    intro i j he x
    cases he
    rfl
  rw [hf k x t]
  exact hg (finiteIndex k) x

/-- 介入時も同じ標本・情報方策・状態・費用を観測する。 -/
def SharedModelSignature.intervenedExperimentObservation (N : SharedModelSignature)
    (d H s : Bool) (k : ℕ) (x : AgentState) (T t : ℝ) (w : C6ExperimentInput) :
    SharedExperimentObservation :=
  let u := N.legacy.informationPolicy w.2.2.2
  (w, ((N.selfProcess d (layerAddressEmbedding (k : WithTop ℕ))).intervenedEquation H s w.1,
    (N.finiteExperimentState k u x T t, N.finiteExperimentCost k u x T t)))

/-- 全有限旧層で候補介入は実験joint全体を変えない。 -/
theorem SharedSCMCouplings.experiment_intervention {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d H s k x T t) :
    (N.experimentInputLaw k).map (N.intervenedExperimentObservation d H s k x T t) =
      N.experimentLaw d H k x T t := by
  unfold SharedModelSignature.experimentLaw
  congr 1
  funext w
  dsimp [SharedModelSignature.intervenedExperimentObservation,
    SharedModelSignature.experimentObservation, SharedModelSignature.selfProcess,
    SharedModelSignature.typedObservation]
  rw [h.output, h.output, h.preservation.legacy_couplings.scm_output_history,
    h.preservation.legacy_couplings.scm_output_history]

/-- 同じ署名の物理層・正層の情報lawは全て確率法則である。 -/
theorem SharedSCMCouplings.information_probability {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (k : ℕ) :
    IsProbabilityMeasure (N.informationLaw (layerAddressEmbedding (k : WithTop ℕ))) := by
  rw [h.preservation.information, sharedInformationIndex_finite]
  cases k with
  | zero =>
    rw [h.preservation.legacy_couplings.physical_information]
    exact Tomabechi.Consistency.C3.physicalLayerLaw.joint_isProbabilityMeasure
  | succ n =>
    rw [h.preservation.legacy_couplings.stage_information]
    exact Tomabechi.Consistency.C3.upperJoint_isProbability

/-- 実標本lawと全観測jointの確率性。 -/
theorem SharedSCMCouplings.experiment_probability {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d H k x T t) :
    IsProbabilityMeasure (N.experimentInputLaw k) ∧
      IsProbabilityMeasure (N.experimentLaw d H k x T t) := by
  letI := h.information_probability k
  have hin : IsProbabilityMeasure (N.experimentInputLaw k) := by
    unfold SharedModelSignature.experimentInputLaw
    infer_instance
  letI := hin
  refine ⟨hin, ?_⟩
  exact (Measure.isProbabilityMeasure_map_iff (measurable_of_finite _).aemeasurable).mpr inferInstance

/-- 三表現・Γを付加した共通束の自己過程の周辺を、そのまま回収する。 -/
theorem SharedSCMCouplings.experiment_selfProcess {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d H k x T t) :
    (N.experimentLaw d H k x T t).map (fun z => z.2.1) =
      (N.selfProcess d (layerAddressEmbedding (k : WithTop ℕ))).exogenousLaw.toMeasure.map
        ((N.selfProcess d (layerAddressEmbedding (k : WithTop ℕ))).baselineEquation H) := by
  letI := h.information_probability k
  rw [SharedModelSignature.experimentLaw,
    Measure.map_map
      (show Measurable (fun z : SharedExperimentObservation => z.2.1) from
        measurable_fst.comp measurable_snd) (measurable_of_finite _)]
  change (N.experimentInputLaw k).map
    (((N.selfProcess d (layerAddressEmbedding (k : WithTop ℕ))).baselineEquation H) ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_of_finite _) measurable_fst,
    SharedModelSignature.experimentInputLaw, Measure.map_fst_prod]
  simp
  rfl

/-- R3・27に、同じSCMの全構造式と実験回収を接続する受入型。 -/
structure SharedSCMAndExperimentInputs (N : SharedModelSignature) : Prop
    extends SharedR3And27Inputs N where
  scm : SharedSCMCouplings N
  selfProcess25A2 : ∀ d a, (N.selfProcess d a).toLawModel.Condition25A2 ()
  experiment_joint : ∀ d H k x T t,
    (N.experimentLaw d H k x T t).map sharedExperimentRecovery =
      N.legacy.experimentLaw d H k x T t

/-- 同じ署名の全受入入力を外部モデル前提なしに同時構成する。 -/
theorem sharedModel_scmAndExperimentInputs : SharedSCMAndExperimentInputs sharedModel := by
  exact {
    toSharedR3And27Inputs := {
      toSharedR3Inputs := sharedModel_r3Inputs
      top27 := sharedModel_theorem27Inputs }
    scm := sharedModel_scmCouplings
    selfProcess25A2 := sharedModel_kernelInputs.selfProcess25A2
    experiment_joint := sharedModel_scmCouplings.experimentLaw }

/-- stage/R2/最終監査を残した、SCM・実験付き共有署名の同時存在。 -/
theorem shared_scm_and_experiment_model_exists :
    ∃ N : SharedModelSignature, SharedSCMAndExperimentInputs N :=
  ⟨sharedModel, sharedModel_scmAndExperimentInputs⟩

#print axioms SharedSCMCouplings.experiment_selfProcess
#print axioms SharedSCMCouplings.experiment_probability
#print axioms shared_scm_and_experiment_model_exists
#print axioms SharedSCMCouplings.experiment_intervention
#print axioms SharedSCMCouplings.experiment_actualPolicyInformation

#print axioms SharedSCMCouplings.experimentLaw
#print axioms SharedModelSignature.experiment_stateCost
end Tomabechi.Consistency.R123
