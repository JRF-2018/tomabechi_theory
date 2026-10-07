import Tomabechi.Consistency.ConsistencyR123_LayerControl

/-!
# 正典担体全体の型付き自己過程

これまでの `selfRepCanonical`は、旧 `C6TypedSelfRepresentation` の
`Ego : ℕ → Set.Icc 0 1 → Set.Icc 0 1` を**コピー**するだけで、担体 `ball16 h`（`h=false` で `[−1,1]`、
`h=true` で `[0,2]`）が `[0,1]` を超える部分 `[−1,0)`・`(1,2]` の方策が型に入らなかった。

ここでは担体全体を型に入れた新しい型付き自己表象 `CanonicalSelfRep` を作る：

* `TCZ i : Set ℝ`：層 `i` の正典 TCZ（担体 `ball16 h`、制御系 `velocityControlSystem` から生成されたものに等しい）。
* `Ego i : {x // x ∈ TCZ i} → {x // x ∈ TCZ i}`：方策 π_c ＝ 選択フィードバック `feedback16Canonical h i`
  （時刻1の勾配流）。**担体全体**を定義域・値域とする。
* `Self i : Set ℝ → Set ℝ`：評価による選別 `S ↦ ⋃_{τ≥0} (S ∩ Ω_θ(τ))`（Ω は N.data の層の実走行費の閾値集合）。
  一点の到達集合 `velReach onePointStart τ` の和に適用すると正典 TCZ になる。

三表現は同じ `(h, 層 i, 評価 Ω, 選択フィードバック)` から作る同一過程の型付き表現である。
旧 Icc 型の表象とは「包含による制限」でだけ結ぶ（`ego_restriction_legacy`）。旧/新 TCZ の等号は求めない。

その表象を 25 の型付き自己過程 `selfProcessFull`（baseline/intervenedEquation）、19 の実験
`fullExperimentLawFull` の自己過程成分へ渡し、条件25-A(2) と、19 の実験の自己過程周辺・情報周辺・
16 の固定点からの 25 の履歴表象（Γ）を同じ型で接続する。

**範囲：** `Self` は同じ評価 Ω による選別として新たに定義した（旧表象の Self の働きを担体全体へ拡げたもの）。
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1 Tomabechi.Consistency.C2
open Tomabechi.Theorem16_25

/-- 担体全体の型付き自己表象：Self（選別）・Ego（方策）・TCZ（集合）。 -/
structure CanonicalSelfRep where
  TCZ : ℕ → Set ℝ
  Ego : (i : ℕ) → {x : ℝ // x ∈ TCZ i} → {x : ℝ // x ∈ TCZ i}
  Self : ℕ → Set ℝ → Set ℝ

instance : MeasurableSpace CanonicalSelfRep := ⊤

/-- 履歴 h の表象：担体 `ball16 h`、Ego は選択フィードバック、Self は同じ評価による選別。 -/
def SharedModelSignature.selfRepFull (N : SharedModelSignature) (h : Bool) : CanonicalSelfRep where
  TCZ := fun _ => ball16 h
  Ego := fun i x => feedback16Canonical h i x
  Self := fun i S => {y | ∃ τ : ℝ, 0 ≤ τ ∧ y ∈ S ∧ y ∈ N.layerOmega h i τ}

def SharedModelSignature.typedObservationFull (N : SharedModelSignature)
    (z : CommonConceptGamma × Bool) : (CommonConceptGamma × CanonicalSelfRep) × Bool :=
  ((z.1, N.selfRepFull z.2), z.2)

theorem SharedModelSignature.typedObservationFull_measurable (N : SharedModelSignature) :
    Measurable N.typedObservationFull :=
  (measurable_fst.prodMk
    ((measurable_of_finite N.selfRepFull).comp measurable_snd)).prodMk measurable_snd

/-- 同じ N.scm から生成する、担体全体の型付き自己過程。 -/
def SharedModelSignature.selfProcessFull (N : SharedModelSignature) (d : Bool) (a : CommonConcept) :
    Theorem25SelfProcessSCM Bool (Bool × Bool)
      (CommonConceptGamma × CanonicalSelfRep) Bool Bool where
  exogenousLaw := N.scm.model.scm.exogenousLaw
  inputHistory := N.scm.model.scm.globalHistory
  candidateVariable := N.scm.model.scm.candidateVariable d a
  inputHistoryAEMeasurable := N.scm.model.scm.globalHistoryAEMeasurable
  candidateAEMeasurable := N.scm.model.scm.candidateVariableAEMeasurable d a
  baselineEquation := fun H u => N.typedObservationFull
    (N.scm.model.scm.stateEquation d a H u,
      N.scm.model.scm.outputEquation d a H u (N.scm.model.scm.candidateVariable d a u))
  intervenedEquation := fun H s u => N.typedObservationFull
    (N.scm.model.scm.stateEquation d a H u, N.scm.model.scm.outputEquation d a H u s)
  baselineAEMeasurable := fun H => N.typedObservationFull_measurable.comp_aemeasurable
    (N.scm.model.scm.baselineJointAEMeasurable d a H)
  intervenedAEMeasurable := fun H s => N.typedObservationFull_measurable.comp_aemeasurable
    (N.scm.model.scm.intervenedJointAEMeasurable d a H s)

/-- 担体全体の自己過程でも、条件25-A(2) は全主体・全共通束点で成り立つ。 -/
theorem SharedKernelInputs.selfProcessFull25A2 {N : SharedModelSignature}
    (h : SharedKernelInputs N) (d : Bool) (a : CommonConcept) :
    (N.selfProcessFull d a).toLawModel.Condition25A2 () := by
  apply (N.selfProcessFull d a).condition25A2
  · exact ((N.scm.model.scm.candidateIndependentOfGlobalContext d a).comp
      measurable_id measurable_fst).symm
  · intro H s
    apply ProbabilityMeasure.toMeasure_injective
    change (N.scm.model.scm.exogenousLaw.toMeasure).map _ =
      (N.scm.model.scm.exogenousLaw.toMeasure).map _
    apply Measure.map_congr
    filter_upwards [h.scm_output_noninterference d a H s] with u hu
    change N.typedObservationFull (_, _) = N.typedObservationFull (_, _)
    rw [hu]

local instance (a : CommonConcept) : MeasurableSpace (fullCommonLayerState a) :=
  sharedLayerStateMeasurable (fullCommonLayerIndex a)

/-- 19 の実験の観測型（表象は担体全体の型）。 -/
abbrev FullExperimentObservationFull (a : CommonConcept) := C6ExperimentInput ×
  (((CommonConceptGamma × CanonicalSelfRep) × Bool) × (fullCommonLayerState a × ℝ))

def SharedModelSignature.fullExperimentObservationFull (N : SharedModelSignature)
    (decode : SharedInformationDecoder) (d H : Bool) (a : CommonConcept)
    (x : fullCommonLayerState a) (T t : ℝ) (w : C6ExperimentInput) :
    FullExperimentObservationFull a :=
  let π := decode a w.2.2.2
  let y := N.data.trajectory a π x T t
  (w, ((N.selfProcessFull d a).baselineEquation H w.1, (y, N.data.runningCost a π y t)))

def SharedModelSignature.fullExperimentLawFull (N : SharedModelSignature)
    (decode : SharedInformationDecoder) (d H : Bool) (a : CommonConcept)
    (x : fullCommonLayerState a) (T t : ℝ) : Measure (FullExperimentObservationFull a) :=
  (N.fullExperimentInputLaw a).map (N.fullExperimentObservationFull decode d H a x T t)

/-- 実験の自己過程周辺は、同じ `(d,H)` の自己過程のベースライン joint。 -/
theorem SharedDataPreservation.fullExperimentFull_selfProcess {N : SharedModelSignature}
    (h : SharedDataPreservation N) (decode d H a x T t) :
    (N.fullExperimentLawFull decode d H a x T t).map (fun z => z.2.1) =
      (N.selfProcessFull d a).exogenousLaw.toMeasure.map
        ((N.selfProcessFull d a).baselineEquation H) := by
  letI := h.fullInformation_probability a
  rw [SharedModelSignature.fullExperimentLawFull,
    Measure.map_map (show Measurable (fun z : FullExperimentObservationFull a => z.2.1) from
      measurable_fst.comp measurable_snd) (measurable_of_finite _)]
  change (N.fullExperimentInputLaw a).map (((N.selfProcessFull d a).baselineEquation H) ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_of_finite _) measurable_fst,
    SharedModelSignature.fullExperimentInputLaw, Measure.map_fst_prod]
  simp
  rfl

/-- 実験の情報周辺（入力・ゴール・行為）は `N.informationLaw`。表象を担体全体の型にしても保たれる。 -/
theorem SharedDataPreservation.fullExperimentFull_information {N : SharedModelSignature}
    (h : SharedDataPreservation N) (d H a x T t) :
    (N.fullExperimentLawFull fullInformationDecoder d H a x T t).map
      (fun z => (z.1.2.1, z.1.2.2.1,
        fullActionEncode a (fullInformationDecoder a z.1.2.2.2))) = N.informationLaw a := by
  letI := h.fullInformation_probability a
  rw [SharedModelSignature.fullExperimentLawFull,
    Measure.map_map (show Measurable (fun z : FullExperimentObservationFull a =>
      (z.1.2.1, z.1.2.2.1, fullActionEncode a (fullInformationDecoder a z.1.2.2.2))) from
      (measurable_of_finite (fun w : C6ExperimentInput => (w.2.1, w.2.2.1,
        fullActionEncode a (fullInformationDecoder a w.2.2.2)))).comp measurable_fst)
      (measurable_of_finite _)]
  have hcomp : ((fun z : FullExperimentObservationFull a =>
      (z.1.2.1, z.1.2.2.1, fullActionEncode a (fullInformationDecoder a z.1.2.2.2))) ∘
        N.fullExperimentObservationFull fullInformationDecoder d H a x T t) =
      fun w : C6ExperimentInput =>
        (w.2.1, w.2.2.1, fullActionEncode a (fullInformationDecoder a w.2.2.2)) := rfl
  rw [hcomp]
  have := h.fullExperiment_actualActionInformation d H a x T t
  rw [SharedModelSignature.fullExperimentLaw,
    Measure.map_map (show Measurable (fun z : FullExperimentObservation a =>
      (z.1.2.1, z.1.2.2.1, fullActionEncode a (fullInformationDecoder a z.1.2.2.2))) from
      (measurable_of_finite (fun w : C6ExperimentInput => (w.2.1, w.2.2.1,
        fullActionEncode a (fullInformationDecoder a w.2.2.2)))).comp measurable_fst)
      (measurable_of_finite _)] at this
  exact this

/-- 担体全体の自己過程の受入型：三表現は同じ担体 `ball16 h` 上の同一過程。 -/
structure Shared25FullSelf (N : SharedModelSignature) : Prop where
  a2 : ∀ d a, (N.selfProcessFull d a).toLawModel.Condition25A2 ()
  tcz_ball : ∀ h i, (N.selfRepFull h).TCZ i = ball16 h
  tcz_canonical : ∀ h i, (N.selfRepFull h).TCZ i = N.canonicalLayerTCZ h i
  self_reach_eq_tcz : ∀ h i, (N.selfRepFull h).Self i
      {y | ∃ τ : ℝ, 0 ≤ τ ∧ y ∈ velReach onePointStart τ} ⊆ (N.selfRepFull h).TCZ i
  ego_is_feedback : ∀ (h : Bool) (i : ℕ) (x : {x : ℝ // x ∈ ball16 h}),
    ((N.selfRepFull h).Ego i x).1 = (feedback16Canonical h i x).1
  ego_outside_unit : ∃ (h : Bool) (i : ℕ) (x : {x : ℝ // x ∈ ball16 h}), x.1 ∉ Set.Icc (0 : ℝ) 1
  tcz_history_sensitive : (N.selfRepFull false).TCZ 0 ≠ (N.selfRepFull true).TCZ 0
  experiment_selfProcess : ∀ decode d H a x T t,
    (N.fullExperimentLawFull decode d H a x T t).map (fun z => z.2.1) =
      (N.selfProcessFull d a).exogenousLaw.toMeasure.map
        ((N.selfProcessFull d a).baselineEquation H)

theorem sharedModel_shared25FullSelf : Shared25FullSelf sharedModel := by
  have hp := sharedModel_preservation
  have hA := sharedModel_explicitAdditionalConditions.legacy
  have hk := sharedModel_kernelInputs
  have hball : ∀ h i, (sharedModel.selfRepFull h).TCZ i = ball16 h := fun _ _ => rfl
  refine ⟨fun d a => hk.selfProcessFull25A2 d a, hball, ?_, ?_, fun _ _ _ => rfl, ?_, ?_,
    fun decode d H a x T t => hp.fullExperimentFull_selfProcess decode d H a x T t⟩
  · intro h i
    rw [hball, SharedModelSignature.canonicalLayerTCZ_eq hp hA]
  · rintro h i y ⟨τ, hτ, _, hΩ⟩
    show y ∈ ball16 h
    rwa [SharedModelSignature.layerOmega_eq hp hA] at hΩ
  · refine ⟨false, 0, ⟨-1, ?_⟩, by norm_num⟩
    simp [ball16, theorem16_intervalGradientCenter]
  · exact sharedModel_shared16CanonicalInputs.carriers_differ

/-- 担体全体の型付き自己過程を、最終整合（層制御系つき）と同じ `N` で同時に主張する。 -/
theorem final_consistency_with_full_self :
    ∃ N sig, SharedFinalConsistency N ∧ LayerControlSound N sig ∧ Shared25FullSelf N := by
  exact ⟨sharedModel, velocityLayerControlSignature, sharedModel_finalConsistency,
    sharedModel_layerControlSound, sharedModel_shared25FullSelf⟩

#print axioms sharedModel_shared25FullSelf
#print axioms final_consistency_with_full_self

end Tomabechi.Consistency.R123
