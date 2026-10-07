import Tomabechi.Consistency.ConsistencyC6_ModelSignature

/-!
# C6：共有署名自身から生成する型付き自己過程

Mの同じSCM・外生法則・履歴・候補・Self/Ego/TCZから自己過程を構成する。
共有保存式から25-A2の同時法則不変性と全主体/共通層の25.2入口適用を得る。
局所SCMの結論を、データ同定なしにMへ移した結果ではない。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Theorem16_25
open MeasureTheory

/-- 同じモデルの三表現を付加し、Γと出力を保存する観測。 -/
def ModelSignature.typedObservation (M : ModelSignature) (z : C6FullLayerGamma × Bool) :
    (C6FullLayerGamma × C6TypedSelfRepresentation) × Bool :=
  ((z.1, M.selfRepresentation z.2), z.2)

theorem ModelSignature.typedObservation_measurable (M : ModelSignature) :
    Measurable M.typedObservation :=
  (measurable_fst.prodMk
    ((measurable_of_finite M.selfRepresentation).comp measurable_snd)).prodMk measurable_snd

/-- 介入時も同じMのΓ/出力に同じ三表現観測を施す。 -/
def ModelSignature.intervenedSelfObservation (M : ModelSignature) (d h s : Bool)
    (a : CommonLayer) (u : Bool × Bool) : (C6FullLayerGamma × C6TypedSelfRepresentation) × Bool :=
  M.typedObservation (M.scm.model.scm.stateEquation d a h u,
    M.scm.model.scm.outputEquation d a h u s)

/-- Mの同じ外生確率空間から生成する全主体・全共通層の自己過程。 -/
def ModelSignature.selfProcess (M : ModelSignature) (d : Bool) (a : CommonLayer) :
    Theorem25SelfProcessSCM Bool (Bool × Bool)
      (C6FullLayerGamma × C6TypedSelfRepresentation) Bool Bool where
  exogenousLaw := M.scm.model.scm.exogenousLaw
  inputHistory := M.scm.model.scm.globalHistory
  candidateVariable := M.scm.model.scm.candidateVariable d a
  inputHistoryAEMeasurable := M.scm.model.scm.globalHistoryAEMeasurable
  candidateAEMeasurable := M.scm.model.scm.candidateVariableAEMeasurable d a
  baselineEquation := fun h => M.baselineSelfObservation d h a
  intervenedEquation := fun h s => M.intervenedSelfObservation d h s a
  baselineAEMeasurable := fun h => M.typedObservation_measurable.comp_aemeasurable
    (M.scm.model.scm.baselineJointAEMeasurable d a h)
  intervenedAEMeasurable := fun h s => M.typedObservation_measurable.comp_aemeasurable
    (M.scm.model.scm.intervenedJointAEMeasurable d a h s)

/-- 共有保存式により、Mの型付き表象/Γ/出力の全介入観測は基準観測と一致する。 -/
theorem CommonDataCouplings.selfObservation_invariant {M : ModelSignature}
    (h : CommonDataCouplings M) (d H s : Bool) (a : CommonLayer) (u : Bool × Bool) :
    M.intervenedSelfObservation d H s a u = M.baselineSelfObservation d H a u := by
  unfold ModelSignature.intervenedSelfObservation ModelSignature.baselineSelfObservation
    ModelSignature.typedObservation
  rw [h.scm_output_history, h.scm_output_history]

/-- MのSCMが持つ独立性と全介入観測の保存から、同じ自己過程の25-A2を供給する。 -/
theorem CommonDataCouplings.selfProcess25A2 {M : ModelSignature}
    (h : CommonDataCouplings M) (d : Bool) (a : CommonLayer) :
    (M.selfProcess d a).toLawModel.Condition25A2 () := by
  apply (M.selfProcess d a).condition25A2
  · exact ((M.scm.model.scm.candidateIndependentOfGlobalContext d a).comp
      measurable_id measurable_fst).symm
  · intro H s
    congr 1
    funext u
    exact h.selfObservation_invariant d H s a u

/-- Mの実SCMを25.2一般入口へ渡す。全主体/全共通層でΓ全観測を保持する。 -/
theorem CommonDataCouplings.noAtman {M : ModelSignature} (h : CommonDataCouplings M) :
    ∀ d a, ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      M.scm.model.scm.toIndexed.toProbabilityCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference
    M.scm
  intro d a H s
  filter_upwards with u
  rw [h.scm_output_history, h.scm_output_history]

/-- 同じ署名の保存証拠に対する閉じた25-A2適用。 -/
theorem commonModel_selfProcess25A2 (d : Bool) (a : CommonLayer) :
    (commonModel.selfProcess d a).toLawModel.Condition25A2 () :=
  commonModel_couplings.selfProcess25A2 d a

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.CommonDataCouplings.selfProcess25A2
#print axioms Tomabechi.Consistency.C6.CommonDataCouplings.noAtman
#print axioms Tomabechi.Consistency.C6.commonModel_selfProcess25A2
