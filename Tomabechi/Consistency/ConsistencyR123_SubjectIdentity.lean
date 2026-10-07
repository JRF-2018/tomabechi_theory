import Tomabechi.Consistency.ConsistencyR123_Shared16Premises

/-!
# 定理19の主体・履歴と定理16/25の主体・履歴の同一性（M8.1）

原文 §8 は、定理19の自由意思容量を **定理16 と同じ主体 i・履歴 h** について述べる。
従来は、主体を `Bool`、履歴を `Bool` で共通にしただけで、19 の実験の主体・履歴と
16/25 の自己過程の主体・履歴を等式で結ぶ field がなかった。ここでは次を述語にする。

1. **実験の自己過程＝25 の自己過程：** 19 の実験 `(d, H, a, x, T, t)` の自己過程成分の周辺は、
   N.scm の主体 `d`・層 `a`・履歴 `H` の自己過程 `N.selfProcess d a` のベースライン joint そのもの。
2. **三表現＝16 の自己表象：** その自己過程の表象成分は、N.legacy に格納した
   定理16の自己表象 `N.legacy.selfRepresentation`（SCM の出力の履歴に対するもの）。
3. **出力は履歴：** SCM の出力は候補・介入によらず履歴 `H` そのもの。したがって三表現は
   `N.legacy.selfRepresentation H`（16 の履歴 H の自己表象）。
4. **Γ は 16 の固定点から：** 全主体 `d`・層 `a` の Γ は、履歴 `h` の定理16の固定点
   （`theorem16_intervalGradientFlowFixedPoints`）の符号から作られる。16 の系は全主体で
   同じ（主体 `d` ごとに別の系を持たない）。

**範囲：** (3)(4) は `sharedModel` についての証明で、一般の N についての導出ではない。
定理16の系が主体に依らず一つであることを「同じ主体」と読む（主体ごとに別の16系を
置く拡張は扱わない）。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1 Tomabechi.Theorem16_25

local instance (a : CommonConcept) : MeasurableSpace (fullCommonLayerState a) :=
  sharedLayerStateMeasurable (fullCommonLayerIndex a)

structure SharedSubjectIdentity (N : SharedModelSignature) : Prop where
  experiment_self_process : ∀ (d H : Bool) (a : CommonConcept) (x : fullCommonLayerState a)
    (T t : ℝ),
    (N.fullExperimentLaw fullInformationDecoder d H a x T t).map (fun z => z.2.1) =
      (N.selfProcess d a).exogenousLaw.toMeasure.map
        ((N.selfProcess d a).baselineEquation H)
  representation_is_16 : ∀ (d : Bool) (a : CommonConcept) (H s : Bool) (u : Bool × Bool),
    ((N.selfProcess d a).intervenedEquation H s u).1.2 =
      N.legacy.selfRepresentation (N.scm.model.scm.outputEquation d a H u s)
  output_is_history : ∀ (d : Bool) (a : CommonConcept) (H s : Bool) (u : Bool × Bool),
    N.scm.model.scm.outputEquation d a H u s = H
  gamma_from_16_fixed_point : ∀ (d : Bool) (a : CommonConcept) (h : Bool) (u : Bool × Bool),
    N.scm.model.scm.stateEquation d a h u =
      commonConceptStateCode d a (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1

theorem sharedModel_subjectIdentity : SharedSubjectIdentity sharedModel where
  experiment_self_process := fun d H a x T t =>
    sharedModel_preservation.fullExperiment_selfProcess fullInformationDecoder d H a x T t
  representation_is_16 := fun d a H s u => rfl
  output_is_history := fun d a H s u => commonConceptSCM_output_eq_history d H s a u
  gamma_from_16_fixed_point := fun d a h u => rfl

/-- 三表現は、履歴 H の定理16の自己表象（19 の実験と 25 の自己過程が同じ 16 の系を読む）。 -/
theorem SharedSubjectIdentity.representation_eq_history {N : SharedModelSignature}
    (h : SharedSubjectIdentity N) (d : Bool) (a : CommonConcept) (H s : Bool) (u : Bool × Bool) :
    ((N.selfProcess d a).intervenedEquation H s u).1.2 = N.legacy.selfRepresentation H := by
  rw [h.representation_is_16, h.output_is_history]

theorem final_consistency_v2_with_subject_identity :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N := by
  refine ⟨sharedModel,
    ⟨sharedModel_fullOriginalPremises, sharedModel_capacityInputs,
      sharedModel_shared16LayerTCZInputs, sharedModel_normUnification⟩,
    ⟨sharedModel_explicitAdditionalConditions,
      sharedModel_pointDomainInputs.explicitHConditions,
      sharedModel_shared16Indexing, sharedModel_baseDomain⟩,
    ⟨sharedModel_nondegenerate, sharedModel_nativeNondegenerate⟩,
    sharedModel_baseBackground21, sharedModel.sharedTopCompleteReading,
    sharedModel_normUnificationConclusions, sharedModel_theorem4Ranges,
    sharedModel_shared16Premises, sharedModel_subjectIdentity⟩

#print axioms sharedModel_subjectIdentity
#print axioms final_consistency_v2_with_subject_identity
end Tomabechi.Consistency.R123
