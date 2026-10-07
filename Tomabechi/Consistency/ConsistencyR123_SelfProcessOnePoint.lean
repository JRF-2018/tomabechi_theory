import Tomabechi.Consistency.ConsistencyR123_Theorem21V0Instance

/-!
# 定理25の型付き自己過程を、一点初期状態の定理16担体で読む

`Shared16OnePointInputs`（一点 x₀ からの閉到達スライスを担体とする定理16の層系）は、
旧来の自己表象 `N.legacy.selfRepresentation`（TCZ は初期集合 `[0,1]` からの到達集合）とは
別に置かれていた。定理25の自己過程 `R_i[h]=(Self,Ego,TCZ)` は、定理16の主体の TCZ を
その成分にもつ（原文 §14 25.1、§2.4）。そこで、TCZ 成分だけを一点版の層別 TCZ
`N.layerTCZ1 h i` に取り替えた型付き自己過程を同じ `N.scm` から作り、条件25-A(2) が
同じ証明で成り立つことを示す。Self・Ego は旧表象のものを使い、Ego は一点版の
フィードバック（時刻1の勾配流）の拡張になっていることも述べる。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Theorem16_25
open Tomabechi.Consistency.R1 Tomabechi.Consistency.C6

/-- TCZ 成分を一点版の層別 TCZ に取り替えた三表現。 -/
def SharedModelSignature.selfRepOnePoint (N : SharedModelSignature) (h : Bool) :
    C6TypedSelfRepresentation where
  Self := (N.legacy.selfRepresentation h).Self
  Ego := (N.legacy.selfRepresentation h).Ego
  TCZ := fun i => N.layerTCZ1 h i

/-- 同じN.scmのΓと出力に、一点版の三表現を付加する観測。 -/
def SharedModelSignature.typedObservationOnePoint (N : SharedModelSignature)
    (z : CommonConceptGamma × Bool) :
    (CommonConceptGamma × C6TypedSelfRepresentation) × Bool :=
  ((z.1, N.selfRepOnePoint z.2), z.2)

theorem SharedModelSignature.typedObservationOnePoint_measurable (N : SharedModelSignature) :
    Measurable N.typedObservationOnePoint :=
  (measurable_fst.prodMk
    ((measurable_of_finite N.selfRepOnePoint).comp measurable_snd)).prodMk measurable_snd

/-- 同じN.scmから生成する、一点版の型付き自己過程。 -/
def SharedModelSignature.selfProcessOnePoint (N : SharedModelSignature) (d : Bool)
    (a : CommonConcept) :
    Theorem25SelfProcessSCM Bool (Bool × Bool)
      (CommonConceptGamma × C6TypedSelfRepresentation) Bool Bool where
  exogenousLaw := N.scm.model.scm.exogenousLaw
  inputHistory := N.scm.model.scm.globalHistory
  candidateVariable := N.scm.model.scm.candidateVariable d a
  inputHistoryAEMeasurable := N.scm.model.scm.globalHistoryAEMeasurable
  candidateAEMeasurable := N.scm.model.scm.candidateVariableAEMeasurable d a
  baselineEquation := fun H u => N.typedObservationOnePoint
    (N.scm.model.scm.stateEquation d a H u,
      N.scm.model.scm.outputEquation d a H u (N.scm.model.scm.candidateVariable d a u))
  intervenedEquation := fun H s u => N.typedObservationOnePoint
    (N.scm.model.scm.stateEquation d a H u, N.scm.model.scm.outputEquation d a H u s)
  baselineAEMeasurable := fun H => N.typedObservationOnePoint_measurable.comp_aemeasurable
    (N.scm.model.scm.baselineJointAEMeasurable d a H)
  intervenedAEMeasurable := fun H s => N.typedObservationOnePoint_measurable.comp_aemeasurable
    (N.scm.model.scm.intervenedJointAEMeasurable d a H s)

/-- 一点版の自己過程でも、条件25-A(2) は全主体・全共通束点で成り立つ。 -/
theorem SharedKernelInputs.selfProcessOnePoint25A2 {N : SharedModelSignature}
    (h : SharedKernelInputs N) (d : Bool) (a : CommonConcept) :
    (N.selfProcessOnePoint d a).toLawModel.Condition25A2 () := by
  apply (N.selfProcessOnePoint d a).condition25A2
  · exact ((N.scm.model.scm.candidateIndependentOfGlobalContext d a).comp
      measurable_id measurable_fst).symm
  · intro H s
    apply ProbabilityMeasure.toMeasure_injective
    change (N.scm.model.scm.exogenousLaw.toMeasure).map _ =
      (N.scm.model.scm.exogenousLaw.toMeasure).map _
    apply Measure.map_congr
    filter_upwards [h.scm_output_noninterference d a H s] with u hu
    change N.typedObservationOnePoint (_, _) = N.typedObservationOnePoint (_, _)
    rw [hu]

open Tomabechi.Consistency.C3 in
/-- 定理21の V₀ 実例を、段と同じ共通束 `CommonConcept` の枝（`sharedStageBranch 0`）で適用する。
旧 `v0Stage_theorem21` は `WithTop ℕ` の原子束の枝を使っていた。ここでは表象を順序埋込み
`layerAddressEmbedding` で共通束へ送り、𝕃_i⊊𝕃・⊤∉𝕃_i・b=∨supp μ を共通束で満たす。 -/
def v0Stage_theorem21_common :=
  Tomabechi.Theorem22.meanField_stage_theorem21_four_conclusions_directKL
    v0StageInput (sharedStageBranch 0)
    (Measure.dirac ()) inputMass inputAction (fun _ => sharedStageU 0)
    inputAction_measurable
    (by
      filter_upwards with x
      intro g hg
      change sharedStageU 0 ∈ ({sharedStageU 0} : Set CommonConcept)
      simp)
    (by
      filter_upwards with x
      intro g
      exact inputMass_nonneg x g)
    (by
      filter_upwards with x
      exact inputMass_sum x)
    (by
      filter_upwards with x
      intro g hg g' h
      exact inputAction_injective x g hg g' h)
    inputMass_measurable
    inputEntropy_pos
    (fun a : Atom => layerAddressEmbedding a) layerAddressEmbedding.injective
    (by intro a b hab; exact layerAddressEmbedding.monotone hab)
    (by
      change ({sharedStageU 0} : Set CommonConcept) =
        (fun a : Atom => layerAddressEmbedding a) '' {((0 + 1 : ℕ) : Atom)}
      simp [sharedStageU, layerU])
    (by
      change ({sharedStageU 0} : Set CommonConcept) =
        (fun a : Atom => layerAddressEmbedding a) '' {((0 + 1 : ℕ) : Atom)}
      simp [sharedStageU, layerU])
    (by
      change layerAddressEmbedding (⊤ : Atom) = ⊤
      exact layerAddress_top)
    (by
      change layerAddressEmbedding ((0 + 1 : ℕ) : Atom) = sSup ({sharedStageU 0} : Set CommonConcept)
      simp [sharedStageU, layerU])

/-- 共通束版の実例の結論（定理21の四結論）の命題。 -/
def V0StageConclusionCommon : Prop := type_of% v0Stage_theorem21_common

theorem v0Stage_theorem21_common_holds : V0StageConclusionCommon := v0Stage_theorem21_common

/-- 定理21の V₀ 実例を共通束の枝で述べた受入型。枝は段0と同じ共通束の住所。 -/
structure SharedTheorem21V0Common (N : SharedModelSignature) : Prop where
  base : SharedTheorem21V0 N
  branch_address : (sharedStageBranch 0).branch = {N.stageAddress 0}
  conclusion : V0StageConclusionCommon

theorem SharedModelSignature.sharedTheorem21V0Common {N : SharedModelSignature}
    (h21 : SharedTheorem21V0 N) (hsw : SharedStageSwitchInputs N) : SharedTheorem21V0Common N :=
  ⟨h21, by rw [hsw.address]; rfl, v0Stage_theorem21_common_holds⟩

/-- 定理25の自己過程の TCZ 成分が、一点版の定理16担体と同じ対象であることの受入型。 -/
structure Shared25OnePointSelf (N : SharedModelSignature) : Prop where
  /-- 条件25-A(2)：一点版の型付き自己過程で、候補追加自我への介入が法則を変えない。 -/
  a2 : ∀ d a, (N.selfProcessOnePoint d a).toLawModel.Condition25A2 ()
  /-- 自己過程の TCZ 成分は、一点版の定理16層系の担体そのもの。 -/
  tcz_is_carrier : ∀ h i, (N.selfRepOnePoint h).TCZ i = layerSystem16OnePoint.carrier h i
  /-- 自己過程の TCZ 成分は線分で、二履歴で異なる。 -/
  tcz_seg : ∀ h i, (N.selfRepOnePoint h).TCZ i = seg16 h
  tcz_history_sensitive : (N.selfRepOnePoint false).TCZ 0 ≠ (N.selfRepOnePoint true).TCZ 0
  /-- Ego は一点版のフィードバック（時刻1の勾配流）を担体上で拡張する。 -/
  ego_extends_feedback : ∀ h i (x : {x : ℝ // x ∈ seg16 h}),
    (((N.selfRepOnePoint h).Ego i ⟨x.1, seg16_subset_unit h x.2⟩ : Set.Icc (0 : ℝ) 1) : ℝ) =
      (feedback16OnePoint h i x : ℝ)

/-- 最終受入型の部品から、一点版の自己過程の受入型を任意のNで得る。 -/
theorem SharedModelSignature.shared25OnePointSelf {N : SharedModelSignature}
    (hk : SharedKernelInputs N) (h1 : Shared16OnePointInputs N) : Shared25OnePointSelf N := by
  refine ⟨hk.selfProcessOnePoint25A2, ?_, ?_, ?_, ?_⟩
  · intro h i
    exact (h1.carrier_eq h i).symm
  · intro h i
    exact h1.tcz_eq h i
  · change N.layerTCZ1 false 0 ≠ N.layerTCZ1 true 0
    rw [h1.tcz_eq, h1.tcz_eq]
    exact h1.carriers_differ
  · intro h i x
    change (((N.legacy.selfRepresentation h).Ego i _ : Set.Icc (0 : ℝ) 1) : ℝ) = _
    rw [hk.additional.toCommonDataCouplings.self_ego]
    rfl

theorem sharedModel_shared25OnePointSelf : Shared25OnePointSelf sharedModel :=
  SharedModelSignature.shared25OnePointSelf sharedModel_kernelInputs
    sharedModel_shared16OnePointInputs

/-- v4 の全受入型に、一点版の定理16担体を TCZ 成分にもつ定理25の自己過程を加えた存在宣言。 -/
theorem final_consistency_v5 :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N ∧
        GenealogyMortalityExtension N ∧ Shared16OnePointInputs N ∧ SharedTheorem21V0 N ∧
        Shared25OnePointSelf N ∧ SharedTheorem21V0Common N :=
  ⟨sharedModel,
    ⟨sharedModel_fullOriginalPremises, sharedModel_capacityInputs,
      sharedModel_shared16LayerTCZInputs, sharedModel_normUnification⟩,
    ⟨sharedModel_explicitAdditionalConditions,
      sharedModel_pointDomainInputs.explicitHConditions,
      sharedModel_shared16Indexing, sharedModel_baseDomain⟩,
    ⟨sharedModel_nondegenerate, sharedModel_nativeNondegenerate⟩,
    sharedModel_baseBackground21, sharedModel.sharedTopCompleteReading,
    sharedModel_normUnificationConclusions, sharedModel_theorem4Ranges,
    sharedModel_shared16Premises, sharedModel_subjectIdentity, sharedModel_noClockCoordinate,
    sharedModel_borelStructure, sharedModel_genealogyMortality, sharedModel_shared16OnePointInputs,
    sharedModel_theorem21V0, sharedModel_shared25OnePointSelf,
    SharedModelSignature.sharedTheorem21V0Common sharedModel_theorem21V0
      sharedModel_stageSwitchInputs⟩

#print axioms SharedModelSignature.shared25OnePointSelf
#print axioms v0Stage_theorem21_common_holds
#print axioms final_consistency_v5
end Tomabechi.Consistency.R123
