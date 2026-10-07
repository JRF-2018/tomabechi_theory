import Tomabechi.Consistency.ConsistencyR123_SharedTheorem27

/-!
# 同じ共有署名のSCM・介入joint・型付き自己過程

共通束のΓ全体を保持し、旧層アドレスの観測回収には全profile・近傍・
関係辺の制限を使う。全共通束点ではN.scm自身から自己過程を生成する。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Theorem16_25
open Tomabechi.Consistency.R1 Tomabechi.Consistency.C6

/-- 共通束のΓを全旧層アドレスへ制限する。 -/
def sharedRestrictGamma (γ : CommonConceptGamma) : C6FullLayerGamma where
  profile := fun b => γ.profile (layerAddressEmbedding b)
  verticalNeighborhood := layerAddressEmbedding ⁻¹' γ.verticalNeighborhood
  incidentRelation := fun e b r f c =>
    γ.incidentRelation e (layerAddressEmbedding b) r f (layerAddressEmbedding c)

/-- 旧アドレスではΓの全構成成分が旧共有束の同じ関係的状態に一致する。 -/
theorem sharedRestrictGamma_relationalState (d h : Bool) (a : CommonLayer) :
    sharedRestrictGamma (commonConceptPresence.relationalState d h (layerAddressEmbedding a)) =
      c6FullLayerPresence.relationalState d h a := by
  unfold sharedRestrictGamma Theorem25PresenceRelationModel.relationalState
  congr 1
  · ext b
    simp [commonConceptPresence, c6FullLayerPresence]
  · funext e b r f c
    simp [commonConceptPresence, c6FullLayerPresence]

/-- Nの旧層回収に必要な構造式。分布の各周辺だけの一致には弱めない。 -/
structure SharedSCMCouplings (N : SharedModelSignature) : Prop where
  preservation : SharedDataPreservation N
  state : ∀ d a h u,
    sharedRestrictGamma (N.scm.model.scm.stateEquation d (layerAddressEmbedding a) h u) =
      N.legacy.scm.model.scm.stateEquation d a h u
  candidate : ∀ d a u,
    N.scm.model.scm.candidateVariable d (layerAddressEmbedding a) u =
      N.legacy.scm.model.scm.candidateVariable d a u
  output : ∀ d a h u s,
    N.scm.model.scm.outputEquation d (layerAddressEmbedding a) h u s =
      N.legacy.scm.model.scm.outputEquation d a h u s

/-- 同じ具体共有署名に全旧層SCM保存式を供給する。 -/
theorem sharedModel_scmCouplings : SharedSCMCouplings sharedModel := by
  refine { preservation := sharedModel_preservation
           state := ?_
           candidate := by intros; rfl
           output := ?_ }
  · intro d a h u
    change sharedRestrictGamma (commonConceptStateCode d (layerAddressEmbedding a)
      (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1) =
      c6FullLayerStateCode d a (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1
    rw [commonConceptStateCode_matches, c6FullLayerStateCode_matches]
    exact sharedRestrictGamma_relationalState d h a
  · intro d a h u s
    change commonConceptMeasuredC3Model.model.scm.outputEquation d (layerAddressEmbedding a) h u s =
      c6FullLayerMeasuredC3Model.model.scm.outputEquation d a h u s
    rw [commonConceptSCM_output_eq_history, c6FullLayer_output_eq_history]

/-- 同じNの介入joint全体を旧署名の同じ層へ厳密に回収する。 -/
theorem SharedSCMCouplings.intervenedJoint {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d a H s) :
    ((N.scm.model.scm.exogenousLaw.toMeasure).map
      (fun u => (N.scm.model.scm.stateEquation d (layerAddressEmbedding a) H u,
        N.scm.model.scm.outputEquation d (layerAddressEmbedding a) H u s))).map
      (fun z => (sharedRestrictGamma z.1, z.2)) =
    (N.legacy.scm.model.scm.exogenousLaw.toMeasure).map
      (fun u => (N.legacy.scm.model.scm.stateEquation d a H u,
        N.legacy.scm.model.scm.outputEquation d a H u s)) := by
  rw [Measure.map_map
    (show Measurable (fun z : CommonConceptGamma × Bool => (sharedRestrictGamma z.1, z.2)) from
      ((measurable_from_top (f := sharedRestrictGamma)).comp measurable_fst).prodMk measurable_snd)
    (measurable_of_finite _), h.preservation.scm_law]
  congr 1
  funext u
  exact Prod.ext (h.state d a H u) (h.output d a H u s)

/-- 同じNの基準jointも同じ観測写像で全回収する。 -/
theorem SharedSCMCouplings.baselineJoint {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d a H) :
    ((N.scm.model.scm.exogenousLaw.toMeasure).map
      (fun u => (N.scm.model.scm.stateEquation d (layerAddressEmbedding a) H u,
        N.scm.model.scm.outputEquation d (layerAddressEmbedding a) H u
          (N.scm.model.scm.candidateVariable d (layerAddressEmbedding a) u)))).map
      (fun z => (sharedRestrictGamma z.1, z.2)) =
    (N.legacy.scm.model.scm.exogenousLaw.toMeasure).map
      (fun u => (N.legacy.scm.model.scm.stateEquation d a H u,
        N.legacy.scm.model.scm.outputEquation d a H u
          (N.legacy.scm.model.scm.candidateVariable d a u))) := by
  rw [Measure.map_map
    (show Measurable (fun z : CommonConceptGamma × Bool => (sharedRestrictGamma z.1, z.2)) from
      ((measurable_from_top (f := sharedRestrictGamma)).comp measurable_fst).prodMk measurable_snd)
    (measurable_of_finite _), h.preservation.scm_law]
  congr 1
  funext u
  dsimp only [Function.comp_apply]
  rw [h.state, h.output, h.candidate]

/-- Nに格納した三表現を、N.scmのΓと出力へ付加する。 -/
def SharedModelSignature.typedObservation (N : SharedModelSignature) (z : CommonConceptGamma × Bool) :
    (CommonConceptGamma × C6TypedSelfRepresentation) × Bool :=
  ((z.1, N.legacy.selfRepresentation z.2), z.2)

theorem SharedModelSignature.typedObservation_measurable (N : SharedModelSignature) :
    Measurable N.typedObservation :=
  (measurable_fst.prodMk
    ((measurable_of_finite N.legacy.selfRepresentation).comp measurable_snd)).prodMk measurable_snd

/-- 全主体・全共通束点で、同じN.scmから生成する型付き自己過程。 -/
def SharedModelSignature.selfProcess (N : SharedModelSignature) (d : Bool) (a : CommonConcept) :
    Theorem25SelfProcessSCM Bool (Bool × Bool)
      (CommonConceptGamma × C6TypedSelfRepresentation) Bool Bool where
  exogenousLaw := N.scm.model.scm.exogenousLaw
  inputHistory := N.scm.model.scm.globalHistory
  candidateVariable := N.scm.model.scm.candidateVariable d a
  inputHistoryAEMeasurable := N.scm.model.scm.globalHistoryAEMeasurable
  candidateAEMeasurable := N.scm.model.scm.candidateVariableAEMeasurable d a
  baselineEquation := fun H u => N.typedObservation
    (N.scm.model.scm.stateEquation d a H u,
      N.scm.model.scm.outputEquation d a H u (N.scm.model.scm.candidateVariable d a u))
  intervenedEquation := fun H s u => N.typedObservation
    (N.scm.model.scm.stateEquation d a H u, N.scm.model.scm.outputEquation d a H u s)
  baselineAEMeasurable := fun H => N.typedObservation_measurable.comp_aemeasurable
    (N.scm.model.scm.baselineJointAEMeasurable d a H)
  intervenedAEMeasurable := fun H s => N.typedObservation_measurable.comp_aemeasurable
    (N.scm.model.scm.intervenedJointAEMeasurable d a H s)

/-- 同じNの実非干渉入力から、型付き自己過程の25-A2を全共通束点で得る。 -/
theorem SharedKernelInputs.selfProcess25A2 {N : SharedModelSignature}
    (h : SharedKernelInputs N) (d : Bool) (a : CommonConcept) :
    (N.selfProcess d a).toLawModel.Condition25A2 () := by
  apply (N.selfProcess d a).condition25A2
  · exact ((N.scm.model.scm.candidateIndependentOfGlobalContext d a).comp
      measurable_id measurable_fst).symm
  · intro H s
    apply ProbabilityMeasure.toMeasure_injective
    change (N.scm.model.scm.exogenousLaw.toMeasure).map _ =
      (N.scm.model.scm.exogenousLaw.toMeasure).map _
    apply Measure.map_congr
    filter_upwards [h.scm_output_noninterference d a H s] with u hu
    change N.typedObservation (_, _) = N.typedObservation (_, _)
    rw [hu]

/-- 三表現を保ったままΓだけを旧層へ制限する。 -/
def sharedRestrictTypedObservation
    (z : (CommonConceptGamma × C6TypedSelfRepresentation) × Bool) :
    (C6FullLayerGamma × C6TypedSelfRepresentation) × Bool :=
  ((sharedRestrictGamma z.1.1, z.1.2), z.2)

theorem sharedRestrictTypedObservation_measurable : Measurable sharedRestrictTypedObservation :=
  (((measurable_from_top (f := sharedRestrictGamma)).comp
    (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd

/-- 同じNの型付き介入jointは旧層で全三表現・Γ・出力を保つ。 -/
theorem SharedSCMCouplings.selfProcess_intervenedJoint {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d a H s) :
    ((N.selfProcess d (layerAddressEmbedding a)).exogenousLaw.toMeasure.map
      ((N.selfProcess d (layerAddressEmbedding a)).intervenedEquation H s)).map
      sharedRestrictTypedObservation =
    (N.legacy.selfProcess d a).exogenousLaw.toMeasure.map
      ((N.legacy.selfProcess d a).intervenedEquation H s) := by
  rw [Measure.map_map sharedRestrictTypedObservation_measurable (measurable_of_finite _)]
  change (N.scm.model.scm.exogenousLaw.toMeasure).map _ =
    (N.legacy.scm.model.scm.exogenousLaw.toMeasure).map _
  rw [h.preservation.scm_law]
  congr 1
  funext u
  dsimp [SharedModelSignature.selfProcess, SharedModelSignature.typedObservation,
    sharedRestrictTypedObservation, ModelSignature.selfProcess,
    ModelSignature.intervenedSelfObservation, ModelSignature.typedObservation]
  rw [h.state, h.output]

/-- 同じNの型付き基準jointも介入と同じ制限観測で回収する。 -/
theorem SharedSCMCouplings.selfProcess_baselineJoint {N : SharedModelSignature}
    (h : SharedSCMCouplings N) (d a H) :
    ((N.selfProcess d (layerAddressEmbedding a)).exogenousLaw.toMeasure.map
      ((N.selfProcess d (layerAddressEmbedding a)).baselineEquation H)).map
      sharedRestrictTypedObservation =
    (N.legacy.selfProcess d a).exogenousLaw.toMeasure.map
      ((N.legacy.selfProcess d a).baselineEquation H) := by
  rw [Measure.map_map sharedRestrictTypedObservation_measurable (measurable_of_finite _)]
  change (N.scm.model.scm.exogenousLaw.toMeasure).map _ =
    (N.legacy.scm.model.scm.exogenousLaw.toMeasure).map _
  rw [h.preservation.scm_law]
  congr 1
  funext u
  dsimp [SharedModelSignature.selfProcess, SharedModelSignature.typedObservation,
    sharedRestrictTypedObservation, ModelSignature.selfProcess, ModelSignature.baselineSelfObservation]
  rw [h.state, h.output, h.candidate]

#print axioms SharedSCMCouplings.selfProcess_intervenedJoint
#print axioms SharedSCMCouplings.selfProcess_baselineJoint

#print axioms sharedModel_scmCouplings
#print axioms SharedSCMCouplings.intervenedJoint
#print axioms SharedKernelInputs.selfProcess25A2
end Tomabechi.Consistency.R123
