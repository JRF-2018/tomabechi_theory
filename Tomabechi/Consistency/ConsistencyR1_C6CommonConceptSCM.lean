import Tomabechi.Consistency.ConsistencyR1_CommonLattice
import Tomabechi.Consistency.ConsistencyC6_FullLayerSCM

/-!
# R1: CommonConcept 全体で定義した同一外生lawのC3/SCM

既存の全層SCMを新束上の層型へ単に読み替えるのではなく、
CommonConceptを層型とする測度付きC3モデルを直接構成する。
外生law・履歴・候補変数は元の定理25モデルと同じものを使う。
-/

noncomputable section
namespace Tomabechi.Consistency.R1

open MeasureTheory
open Tomabechi.Theorem16_25
open Tomabechi.Consistency.C6

abbrev CommonConceptGamma :=
  Theorem25RelationalState Bool CommonConcept Bool (fun _ => Unit)

instance : MeasurableSpace CommonConceptGamma := ⊤

/-- 全ての共通概念点で同じ非空profileと履歴依存の関係辺を持つ。 -/
def commonConceptPresence :
    Theorem25PresenceRelationModel Bool Bool CommonConcept Bool (fun _ => Unit) := by
  classical
  refine {
    profile := fun _ _ _ => some ()
    topMarker := ()
    topRepresentationIsSubsingleton := fun _ _ => Subsingleton.elim _ _
    supportNonempty := fun _ _ => ⟨⊤, by simp⟩
    supportUpwardClosed := fun _ _ _ _ _ _ => by simp
    topLayerHasCommonMarker := fun _ _ => rfl
    roleInverse := id
    roleInverseInvolutive := fun _ => rfl
    relationEdge := fun h d _ r e _ => d ≠ e ∧ r = h
    relationEdgeReverses := ?_
    everyExistenceIsRelated := ?_
    relationGraphConnected := ?_ }
  · intro h d a r e b
    simp [ne_comm]
  · intro h d
    cases d
    · exact ⟨true, ⊥, ⊥, h, by decide, by simp⟩
    · exact ⟨false, ⊥, ⊥, h, by decide, by simp⟩
  · intro h d e
    cases d <;> cases e
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by decide, ⊥, ⊥, h, by simp⟩
    · exact Relation.ReflTransGen.single ⟨by decide, ⊥, ⊥, h, by simp⟩
    · exact Relation.ReflTransGen.refl

def commonConceptStateCode (d : Bool) (a : CommonConcept) (x : ℕ → ℝ) :
    CommonConceptGamma :=
  commonConceptPresence.relationalState d (decide (x 0 = 1)) a

theorem commonConceptStateCode_matches (d h : Bool) (a : CommonConcept) :
    commonConceptStateCode d a
        (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 =
      commonConceptPresence.relationalState d h a := by
  have hx := theorem16_intervalGradientFlowFixedPoint_coordinate h 0
  cases h <;> simp [commonConceptStateCode, hx, theorem16_intervalGradientCenter]

theorem commonConceptGamma_event (p : CommonConceptGamma → Prop) :
    MeasurableSet {z : CommonConceptGamma × Bool | p z.1} :=
  measurable_fst (show MeasurableSet {γ | p γ} from trivial)

/-- CommonConcept全点で定理25の測度付きC3一般入口を満たすモデル。 -/
def commonConceptMeasuredC3Model :
    Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool CommonConcept Bool (Bool × Bool)
      (fun _ => Unit) (fun _ => CommonConceptGamma) (fun _ => Bool) (fun _ => Bool) := by
  apply Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
    (Output := fun _ : CommonConcept => Bool) (Candidate := fun _ : CommonConcept => Bool)
    theorem16_intervalGradientFlowFixedPoints commonConceptPresence
    commonConceptStateCode (fun d a h => commonConceptStateCode_matches d h a)
    (fun _ _ x => decide (x 0 = 1))
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistory
    (fun d _ => theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d false)
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistoryAEMeasurable
    (fun d _ => theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariableAEMeasurable d false)
  · intro d a
    change ProbabilityTheory.IndepFun Prod.fst
      (fun u : Bool × Bool => (u.2, commonConceptStateCode d a
        (theorem16_intervalGradientFlowFixedPoints.fixedPoint u.2).1))
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    exact ProbabilityTheory.indepFun_prod
      (X := fun b : Bool => b)
      (Y := fun h : Bool => (h, commonConceptStateCode d a
        (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1))
      measurable_id (measurable_of_finite _)
  · intro d a
    exact (measurable_of_finite _).aemeasurable
  · intro d a h
    exact commonConceptGamma_event
      (fun γ => γ.profile a = commonConceptPresence.profile d h a)
  · intro d a h e b r
    exact commonConceptGamma_event
      (fun γ => γ.incidentRelation d a r e b ↔ commonConceptPresence.relationEdge h d a r e b)
  · intro d a h
    exact commonConceptGamma_event (fun γ => γ = commonConceptPresence.relationalState d h a)

theorem commonConceptSCM_output_eq_history (d h s : Bool) (a : CommonConcept)
    (u : Bool × Bool) :
    commonConceptMeasuredC3Model.model.scm.outputEquation d a h u s = h := by
  change decide ((theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 0 = 1) = h
  have hx := theorem16_intervalGradientFlowFixedPoint_coordinate h 0
  cases h <;> simp [hx, theorem16_intervalGradientCenter]

/-- Theorem 25's no-self/Atman conclusion is applied at every point of the
new common lattice, using this model's own measured SCM. -/
theorem commonConceptMeasuredC3Model_noAtman : ∀ d a,
    ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      commonConceptMeasuredC3Model.model.scm.toIndexed.toProbabilityCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference
    commonConceptMeasuredC3Model
  intro d a h s
  filter_upwards with u
  rw [commonConceptSCM_output_eq_history, commonConceptSCM_output_eq_history]

/-- Each candidate value remains non-null under the original exogenous law,
uniformly over the common lattice. -/
theorem commonConceptMeasuredC3Model_candidate_positive (d s : Bool) (a : CommonConcept) :
    Theorem25GlobalHistorySCM.candidateHasPositiveMass
      commonConceptMeasuredC3Model.model.scm.toIndexed d a s :=
  theorem25_intervalGradientFlowRandomized_candidate_has_positive_mass s

/-- Attach the real C4 Self/Ego/TCZ representation to the CommonConcept Γ and
the same SCM output, without changing the exogenous source or candidate. -/
def commonConceptTypedObservation (z : CommonConceptGamma × Bool) :
    (CommonConceptGamma × C6TypedSelfRepresentation) × Bool :=
  ((z.1, c6TypedSelfRepresentation z.2), z.2)

theorem commonConceptTypedObservation_measurable :
    Measurable commonConceptTypedObservation :=
  (measurable_fst.prodMk
    ((measurable_of_finite c6TypedSelfRepresentation).comp measurable_snd)).prodMk
      measurable_snd

/-- Same-law typed self-process at each common-concept point. -/
def commonConceptTypedSelfProcess (d : Bool) (a : CommonConcept) :
    Theorem25SelfProcessSCM Bool (Bool × Bool)
      (CommonConceptGamma × C6TypedSelfRepresentation) Bool Bool where
  exogenousLaw := commonConceptMeasuredC3Model.model.scm.exogenousLaw
  inputHistory := commonConceptMeasuredC3Model.model.scm.globalHistory
  candidateVariable := commonConceptMeasuredC3Model.model.scm.candidateVariable d a
  inputHistoryAEMeasurable := commonConceptMeasuredC3Model.model.scm.globalHistoryAEMeasurable
  candidateAEMeasurable := commonConceptMeasuredC3Model.model.scm.candidateVariableAEMeasurable d a
  baselineEquation := fun h u => commonConceptTypedObservation
    (commonConceptMeasuredC3Model.model.scm.stateEquation d a h u,
      commonConceptMeasuredC3Model.model.scm.outputEquation d a h u
        (commonConceptMeasuredC3Model.model.scm.candidateVariable d a u))
  intervenedEquation := fun h s u => commonConceptTypedObservation
    (commonConceptMeasuredC3Model.model.scm.stateEquation d a h u,
      commonConceptMeasuredC3Model.model.scm.outputEquation d a h u s)
  baselineAEMeasurable := fun h => commonConceptTypedObservation_measurable.comp_aemeasurable
    (commonConceptMeasuredC3Model.model.scm.baselineJointAEMeasurable d a h)
  intervenedAEMeasurable := fun h s => commonConceptTypedObservation_measurable.comp_aemeasurable
    (commonConceptMeasuredC3Model.model.scm.intervenedJointAEMeasurable d a h s)

/-- 25-A2はCommonConcept全点で元と同じ外生law上の独立性を満たす。 -/
theorem commonConceptTypedSelfProcess_satisfies25A2 (d : Bool) (a : CommonConcept) :
    (commonConceptTypedSelfProcess d a).toLawModel.Condition25A2 () := by
  apply (commonConceptTypedSelfProcess d a).condition25A2
  · change ProbabilityTheory.IndepFun Prod.snd Prod.fst
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    exact (ProbabilityTheory.indepFun_prod (X := id) (Y := id)
      measurable_id measurable_id).symm
  · intro h s
    congr 1

theorem commonConceptTypedSelfProcess_representation (d h s : Bool) (a : CommonConcept)
    (u : Bool × Bool) :
    ((commonConceptTypedSelfProcess d a).intervenedEquation h s u).1 =
      (commonConceptPresence.relationalState d h a, c6TypedSelfRepresentation h) := by
  apply Prod.ext
  · exact commonConceptStateCode_matches d h a
  · change c6TypedSelfRepresentation
      (commonConceptMeasuredC3Model.model.scm.outputEquation d a h u s) = _
    rw [commonConceptSCM_output_eq_history]

/-- Γを元のBool二層観測へ制限する。 -/
def restrictCommonConceptGamma (γ : CommonConceptGamma) :
    Theorem25HistoryDependentGamma where
  profile := fun b => γ.profile (layerAddressEmbedding (operationalLayerAddress b))
  verticalNeighborhood :=
    (layerAddressEmbedding ∘ operationalLayerAddress) ⁻¹' γ.verticalNeighborhood
  incidentRelation := fun e b r f c => γ.incidentRelation e
    (layerAddressEmbedding (operationalLayerAddress b)) r f
    (layerAddressEmbedding (operationalLayerAddress c))

theorem commonConceptState_restricts_old (d a h : Bool) (u : Bool × Bool) :
    restrictCommonConceptGamma
      (commonConceptMeasuredC3Model.model.scm.stateEquation d
        (layerAddressEmbedding (operationalLayerAddress a)) h u) =
      theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u := by
  change restrictCommonConceptGamma
      (commonConceptStateCode d (layerAddressEmbedding (operationalLayerAddress a))
        (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1) =
    theorem25_intervalGradientFlowStateCode d a
      (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1
  rw [commonConceptStateCode_matches, theorem25_intervalGradientFlowStateCode_matches]
  unfold restrictCommonConceptGamma commonConceptPresence
    Theorem25PresenceRelationModel.relationalState
    theorem25_historyDependentPresenceRelations
  congr 1
  · ext b
    cases a <;> cases b <;> simp [operationalLayerAddress]
  · funext e b r f c
    cases a <;> cases b <;> cases c <;> simp [operationalLayerAddress]

theorem commonConceptSCM_source_law_and_history :
    commonConceptMeasuredC3Model.model.scm.exogenousLaw =
        theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw ∧
    commonConceptMeasuredC3Model.model.scm.globalHistory =
        theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistory :=
  ⟨rfl, rfl⟩

theorem commonConceptSCM_candidate_matches_old (d a : Bool) :
    commonConceptMeasuredC3Model.model.scm.candidateVariable d
        (layerAddressEmbedding (operationalLayerAddress a)) =
      theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d a := rfl

/-- Every old-address intervention joint is recovered after restricting Γ.
The equality includes both the state and output coordinates, under the same
original exogenous law. -/
theorem commonConceptSCM_intervenedJoint_restricts_old (d a h s : Bool) :
    ((commonConceptMeasuredC3Model.model.scm.exogenousLaw.toMeasure).map
      (fun u =>
        (commonConceptMeasuredC3Model.model.scm.stateEquation d
          (layerAddressEmbedding (operationalLayerAddress a)) h u,
         commonConceptMeasuredC3Model.model.scm.outputEquation d
          (layerAddressEmbedding (operationalLayerAddress a)) h u s))).map
      (fun z => (restrictCommonConceptGamma z.1, z.2)) =
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw.toMeasure).map
      (fun u =>
        (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
         theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u s)) := by
  rw [Measure.map_map
    (show Measurable
      (fun z : CommonConceptGamma × Bool => (restrictCommonConceptGamma z.1, z.2)) from
        ((measurable_from_top (f := restrictCommonConceptGamma)).comp measurable_fst).prodMk
          measurable_snd)
    (measurable_of_finite _)]
  congr 1
  funext u
  exact Prod.ext (commonConceptState_restricts_old d a h u)
    (commonConceptSCM_output_eq_history d h s
      (layerAddressEmbedding (operationalLayerAddress a)) u |>.trans
        (theorem25_intervalGradientFlowRandomized_output_eq_history d a h u s).symm)

end Tomabechi.Consistency.R1

end
