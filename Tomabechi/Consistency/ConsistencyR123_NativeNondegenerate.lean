import Tomabechi.Consistency.ConsistencyR123_SharedBaseDomain

/-!
# 非退化性を N 自身の field から読む

従来の非退化性 N3 は、正のゴールエントロピーを C3 の定数 `inputMass` から読んでいた
（`N.informationLaw` からではない）。また N6 の履歴固定点の分離は `N.legacy` に格納した
固定点を読んでいた。ここでは次を N の native な量で述べ直す。

* `N.informationLaw (N.stageAddress 0)` の条件付きゴールエントロピー
  `lawGoalEntropy`（事前核 `directPriorGoalKernel` の積分）が正。
  直接CMIが `log 2 > 0` で、`I(G;Y|X) ≤ H(G|X)` から出す（定数 `inputMass` を読まない）。
* `N.scm` 自身のΓ（`stateEquation`）が履歴 false/true で異なる主体・層・標本がある。
  `fixedPoint_gamma`（SCM 状態と固定点符号の保存式）の帰結で、定理16/25の固定点の
  履歴分離を SCM 側から読んだもの。

一般の N についての導出ではなく、`sharedModel` についての証明である（存在宣言に必要な範囲）。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1
open Tomabechi.Theorem19_22 Tomabechi.Theorem16_25

/-- 情報 law の条件付きゴールエントロピー `∫ H(G|X=x) dP_X`。確率測度でないときは 0。 -/
def lawGoalEntropy (J : Measure (Unit × Bool × Bool)) : ℝ :=
  open Classical in
  if h : IsProbabilityMeasure J then
    (haveI := h
    ∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel J) x ∂J.map Prod.fst)
  else 0

/-- 上位層の law では、条件付きゴールエントロピーは直接CMI（= log 2）以上で、特に正。 -/
theorem lawGoalEntropy_upper_pos :
    0 < lawGoalEntropy Tomabechi.Consistency.C3.upperJoint := by
  have hp := Tomabechi.Consistency.C3.upperJoint_isProbability
  unfold lawGoalEntropy
  rw [dif_pos hp]
  haveI := hp
  have hle := directCMI_le_inputGoalEntropy_of_finite
    Tomabechi.Consistency.C3.upperJoint capacityKL_upper_finite
  have hscore : (InformationTheory.klDiv
      (directActionGoalJoint Tomabechi.Consistency.C3.upperJoint)
      (directCMIReference Tomabechi.Consistency.C3.upperJoint)).toReal = Real.log 2 := by
    have := capacityScoreLaw_upper
    unfold capacityScoreLaw at this
    rwa [dif_pos hp] at this
  rw [hscore] at hle
  exact (Real.log_pos (by norm_num)).trans_le hle

/-- N 自身の量で読む非退化性。 -/
structure SharedNativeNondegenerate (N : SharedModelSignature) : Prop where
  /-- `N.informationLaw (N.stageAddress 0)` の直接CMI（定理19の評価）と
  条件付きゴールエントロピーがともに正。 -/
  information_positive :
    0 < capacityScoreLaw (N.informationLaw (N.stageAddress 0)) ∧
    0 < lawGoalEntropy (N.informationLaw (N.stageAddress 0))
  /-- `N.scm` 自身のΓが履歴 false/true で異なる主体・層・標本がある（定理16/25 の固定点の
  履歴分離を SCM から読む）。 -/
  scm_gamma_separates : ∃ (d : Bool) (a : CommonConcept) (u : Bool × Bool),
    N.scm.model.scm.stateEquation d a false u ≠ N.scm.model.scm.stateEquation d a true u

theorem SharedDataPreservation.informationPositive {N : SharedModelSignature}
    (h : SharedDataPreservation N) :
    0 < capacityScoreLaw (N.informationLaw (N.stageAddress 0)) ∧
    0 < lawGoalEntropy (N.informationLaw (N.stageAddress 0)) := by
  have hne : N.stageAddress 0 ≠ ⊥ := by
    rw [h.stageAddress]
    exact commonConceptPositiveEntropyAddress_ne_bottom 0
  rw [h.informationLaw_of_ne_bot hne, capacityScoreLaw_upper]
  exact ⟨Real.log_pos (by norm_num), lawGoalEntropy_upper_pos⟩

theorem sharedModel_scm_gamma_separates :
    ∃ (d : Bool) (a : CommonConcept) (u : Bool × Bool),
      sharedModel.scm.model.scm.stateEquation d a false u ≠
        sharedModel.scm.model.scm.stateEquation d a true u := by
  refine ⟨false, ⊥, (false, false), ?_⟩
  change commonConceptStateCode false ⊥
      (theorem16_intervalGradientFlowFixedPoints.fixedPoint false).1 ≠
    commonConceptStateCode false ⊥
      (theorem16_intervalGradientFlowFixedPoints.fixedPoint true).1
  rw [commonConceptStateCode_matches, commonConceptStateCode_matches]
  intro heq
  have hr := congrArg (fun γ => γ.incidentRelation false ⊥ true true ⊥) heq
  simp [Theorem25PresenceRelationModel.relationalState, commonConceptPresence] at hr

theorem sharedModel_nativeNondegenerate : SharedNativeNondegenerate sharedModel :=
  ⟨sharedModel_preservation.informationPositive, sharedModel_scm_gamma_separates⟩

/-- 先行する受入型に、N 自身の量で読む非退化性を加えた存在宣言。 -/
theorem final_consistency_with_native_nondegeneracy :
    ∃ N : SharedModelSignature,
      FullOriginalPremises N ∧ ExplicitAdditionalConditions N ∧ SharedNondegenerate N ∧
        SharedCapacityInputs N ∧ Shared16Indexing N ∧ Shared16LayerTCZInputs N ∧
        SharedBaseDomain N ∧ SharedNativeNondegenerate N :=
  ⟨sharedModel, sharedModel_fullOriginalPremises, sharedModel_explicitAdditionalConditions,
    sharedModel_nondegenerate, sharedModel_capacityInputs, sharedModel_shared16Indexing,
    sharedModel_shared16LayerTCZInputs, sharedModel_baseDomain, sharedModel_nativeNondegenerate⟩

#print axioms lawGoalEntropy_upper_pos
#print axioms sharedModel_nativeNondegenerate
#print axioms final_consistency_with_native_nondegeneracy
end Tomabechi.Consistency.R123
