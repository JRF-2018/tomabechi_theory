import Tomabechi.Consistency.ConsistencyR123_SharedTheorem3

/-!
# 共通束全点の実情報・自己過程・状態費用joint

実験の層はCommonConcept全体を走る。非埋込み点でもN.dataの同じ層を使い、
頂点では頂点のベクトル状態・方策型を保つ。
情報の二値行為から実方策への復号族は引数で明示する。
全復号族に対する結果だけでは、復号族の存在・許容性を証明しない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1

/-- 各層の実数二座標/Euclidean状態の元の可測構造を使用する。 -/
def sharedLayerStateMeasurable : (a : CommonLayer) → MeasurableSpace (C6LayeredState a)
  | none => inferInstance
  | some _ => inferInstance

local instance (a : CommonConcept) : MeasurableSpace (fullCommonLayerState a) :=
  sharedLayerStateMeasurable (fullCommonLayerIndex a)

/-- 二値情報行為を、各層の全方策族の中の二方策へ復号する。 -/
abbrev SharedInformationDecoder := ∀ a : CommonConcept, Bool → fullCommonLayerPolicy a

abbrev FullExperimentObservation (a : CommonConcept) := C6ExperimentInput ×
  (((CommonConceptGamma × C6TypedSelfRepresentation) × Bool) × (fullCommonLayerState a × ℝ))

/-- 外生標本と情報lawは同じNと同じ共通束点を読む。 -/
def SharedModelSignature.fullExperimentInputLaw (N : SharedModelSignature) (a : CommonConcept) :
    Measure C6ExperimentInput :=
  N.scm.model.scm.exogenousLaw.toMeasure.prod (N.informationLaw a)

/-- 同じ層・同じ情報方策による実状態と実走行費を保持する。 -/
def SharedModelSignature.fullExperimentObservation (N : SharedModelSignature)
    (decode : SharedInformationDecoder) (d H : Bool) (a : CommonConcept)
    (x : fullCommonLayerState a) (T t : ℝ) (w : C6ExperimentInput) : FullExperimentObservation a :=
  let π := decode a w.2.2.2
  let y := N.data.trajectory a π x T t
  (w, ((N.selfProcess d a).baselineEquation H w.1, (y, N.data.runningCost a π y t)))

def SharedModelSignature.fullExperimentLaw (N : SharedModelSignature)
    (decode : SharedInformationDecoder) (d H : Bool) (a : CommonConcept)
    (x : fullCommonLayerState a) (T t : ℝ) : Measure (FullExperimentObservation a) :=
  (N.fullExperimentInputLaw a).map (N.fullExperimentObservation decode d H a x T t)

/-- 全共通束点で情報lawは確率法則。物理層のみ零情報の別lawを使う。 -/
theorem SharedDataPreservation.fullInformation_probability {N : SharedModelSignature}
    (h : SharedDataPreservation N) (a : CommonConcept) :
    IsProbabilityMeasure (N.informationLaw a) := by
  rw [h.information]
  cases hi : commonConceptInformationIndex a with
  | zero =>
    rw [h.legacy_couplings.physical_information]
    exact Tomabechi.Consistency.C3.physicalLayerLaw.joint_isProbabilityMeasure
  | succ k =>
    rw [h.legacy_couplings.stage_information]
    exact Tomabechi.Consistency.C3.upperJoint_isProbability

/-- 全点・全初期状態・全時刻・全復号族の実験は確率jointである。 -/
theorem SharedDataPreservation.fullExperiment_probability {N : SharedModelSignature}
    (h : SharedDataPreservation N) (decode d H a x T t) :
    IsProbabilityMeasure (N.fullExperimentInputLaw a) ∧
      IsProbabilityMeasure (N.fullExperimentLaw decode d H a x T t) := by
  letI := h.fullInformation_probability a
  have hin : IsProbabilityMeasure (N.fullExperimentInputLaw a) := by
    unfold SharedModelSignature.fullExperimentInputLaw
    infer_instance
  letI := hin
  refine ⟨hin, ?_⟩
  exact (Measure.isProbabilityMeasure_map_iff (measurable_of_finite _).aemeasurable).mpr inferInstance

/-- 実状態・走行費の周辺。評価値だけでなく同じ実軌道も残す。 -/
theorem SharedModelSignature.fullExperiment_stateCost (N : SharedModelSignature)
    (decode d H a x T t) :
    (N.fullExperimentLaw decode d H a x T t).map (fun z => z.2.2) =
      (N.fullExperimentInputLaw a).map (fun w =>
        let π := decode a w.2.2.2
        let y := N.data.trajectory a π x T t
        (y, N.data.runningCost a π y t)) := by
  rw [SharedModelSignature.fullExperimentLaw,
    Measure.map_map (show Measurable (fun z : FullExperimentObservation a => z.2.2) from
      measurable_snd.comp measurable_snd) (measurable_of_finite _)]
  rfl

/-- 元標本lawを回収する。標本保持により全周辺が同一jointに属する。 -/
theorem SharedModelSignature.fullExperiment_input (N : SharedModelSignature)
    (decode d H a x T t) :
    (N.fullExperimentLaw decode d H a x T t).map Prod.fst = N.fullExperimentInputLaw a := by
  rw [SharedModelSignature.fullExperimentLaw,
    Measure.map_map measurable_fst (measurable_of_finite _)]
  change (N.fullExperimentInputLaw a).map id = _
  exact Measure.map_id

/-- 全点の情報周辺は同じ住所のN.informationLawそのもの。 -/
theorem SharedDataPreservation.fullExperiment_information {N : SharedModelSignature}
    (h : SharedDataPreservation N) (decode d H a x T t) :
    (N.fullExperimentLaw decode d H a x T t).map (fun z => z.1.2) = N.informationLaw a := by
  rw [SharedModelSignature.fullExperimentLaw,
    Measure.map_map (show Measurable (fun z : FullExperimentObservation a => z.1.2) from
      measurable_snd.comp measurable_fst) (measurable_of_finite _)]
  change (N.fullExperimentInputLaw a).map Prod.snd = _
  unfold SharedModelSignature.fullExperimentInputLaw
  rw [Measure.map_snd_prod]
  simp

/-- 全点のnative Γ・三表現・出力の自己過程周辺を回収する。 -/
theorem SharedDataPreservation.fullExperiment_selfProcess {N : SharedModelSignature}
    (h : SharedDataPreservation N) (decode d H a x T t) :
    (N.fullExperimentLaw decode d H a x T t).map (fun z => z.2.1) =
      (N.selfProcess d a).exogenousLaw.toMeasure.map ((N.selfProcess d a).baselineEquation H) := by
  letI := h.fullInformation_probability a
  rw [SharedModelSignature.fullExperimentLaw,
    Measure.map_map (show Measurable (fun z : FullExperimentObservation a => z.2.1) from
      measurable_fst.comp measurable_snd) (measurable_of_finite _)]
  change (N.fullExperimentInputLaw a).map (((N.selfProcess d a).baselineEquation H) ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_of_finite _) measurable_fst,
    SharedModelSignature.fullExperimentInputLaw, Measure.map_fst_prod]
  simp
  rfl

def SharedModelSignature.fullIntervenedExperimentObservation (N : SharedModelSignature)
    (decode : SharedInformationDecoder) (d H s : Bool) (a : CommonConcept)
    (x : fullCommonLayerState a) (T t : ℝ) (w : C6ExperimentInput) : FullExperimentObservation a :=
  let π := decode a w.2.2.2
  let y := N.data.trajectory a π x T t
  (w, ((N.selfProcess d a).intervenedEquation H s w.1, (y, N.data.runningCost a π y t)))

/-- 全共通束点で候補介入は実験joint全体を保つ。
外生law上のa.e.非干渉を積lawの外生周辺から移す。 -/
theorem SharedKernelInputs.fullExperiment_intervention {N : SharedModelSignature}
    (h : SharedKernelInputs N) (decode d H s a x T t) :
    (N.fullExperimentInputLaw a).map
      (N.fullIntervenedExperimentObservation decode d H s a x T t) =
      N.fullExperimentLaw decode d H a x T t := by
  unfold SharedModelSignature.fullExperimentLaw
  apply Measure.map_congr
  letI := h.preservation.fullInformation_probability a
  have hmap : (N.fullExperimentInputLaw a).map Prod.fst =
      N.scm.model.scm.exogenousLaw.toMeasure := by
    unfold SharedModelSignature.fullExperimentInputLaw
    rw [Measure.map_fst_prod]
    simp
  have hae : ∀ᵐ u ∂(N.fullExperimentInputLaw a).map Prod.fst,
      N.scm.model.scm.outputEquation d a H u s =
        N.scm.model.scm.outputEquation d a H u
          (N.scm.model.scm.candidateVariable d a u) := by
    rw [hmap]
    exact h.scm_output_noninterference d a H s
  have hlift := ae_of_ae_map measurable_fst.aemeasurable hae
  filter_upwards [hlift] with w hw
  dsimp [SharedModelSignature.fullIntervenedExperimentObservation,
    SharedModelSignature.fullExperimentObservation, SharedModelSignature.selfProcess]
  rw [hw]

#print axioms SharedDataPreservation.fullExperiment_probability
#print axioms SharedDataPreservation.fullExperiment_selfProcess
#print axioms SharedKernelInputs.fullExperiment_intervention
end Tomabechi.Consistency.R123
