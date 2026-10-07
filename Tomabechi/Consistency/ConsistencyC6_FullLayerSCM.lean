import Tomabechi.Consistency.ConsistencyC6_TypedSelfProcess

/-!
# C6：共通束全層の25-B/C3と同一固定点由来SCM

共通WithTop ℕの全層profile・縦近傍・入出辺を持つΓを生成する。
主体・履歴・役割・候補は元のC4モデルと同じ型と外生法則を使う。
最高層の一元表象はprofileの型であり、C5の二次元認知状態ではない。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Theorem16_25
open MeasureTheory

/-- 元の全主体・履歴関係を共通束全層で保持する。
全層に現前する具体モデルなので支持は非空かつ上向き閉。 -/
def c6FullLayerPresence :
    Theorem25PresenceRelationModel Bool Bool CommonLayer Bool (fun _ => Unit) := by
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

/-- 共通全層のΓ。25のprofile表象はUnitだが、全関係的状態を保持する。 -/
abbrev C6FullLayerGamma :=
  Theorem25RelationalState Bool CommonLayer Bool (fun _ => Unit)

instance : MeasurableSpace C6FullLayerGamma := ⊤

def c6FullLayerStateCode (d : Bool) (a : CommonLayer) (x : ℕ → ℝ) : C6FullLayerGamma :=
  c6FullLayerPresence.relationalState d (decide (x 0 = 1)) a

/-- 同じC4履歴別固定点から、全共通層の真のΓを回収する。 -/
theorem c6FullLayerStateCode_matches (d h : Bool) (a : CommonLayer) :
    c6FullLayerStateCode d a (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 =
      c6FullLayerPresence.relationalState d h a := by
  have hx := theorem16_intervalGradientFlowFixedPoint_coordinate h 0
  cases h <;> simp [c6FullLayerStateCode, hx, theorem16_intervalGradientCenter]

/-- Γ観測について全一致事象が可測。測度値1だけで可測性を代替しない。 -/
theorem c6FullLayerGamma_event (p : C6FullLayerGamma → Prop) :
    MeasurableSet {z : C6FullLayerGamma × Bool | p z.1} :=
  measurable_fst (show MeasurableSet {γ | p γ} from trivial)

/-- 同じ履歴別固定点・外生law・履歴/候補から全層の測度付きC3モデルを作る。 -/
def c6FullLayerMeasuredC3Model :
    Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool CommonLayer Bool (Bool × Bool)
      (fun _ => Unit) (fun _ => C6FullLayerGamma) (fun _ => Bool) (fun _ => Bool) := by
  apply Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
    (Output := fun _ : CommonLayer => Bool) (Candidate := fun _ : CommonLayer => Bool)
    theorem16_intervalGradientFlowFixedPoints c6FullLayerPresence
    c6FullLayerStateCode (fun d a h => c6FullLayerStateCode_matches d h a)
    (fun _ _ x => decide (x 0 = 1))
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistory
    (fun d _ => theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d false)
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistoryAEMeasurable
    (fun d _ => theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariableAEMeasurable d false)
  · intro d a
    change ProbabilityTheory.IndepFun Prod.fst
      (fun u : Bool × Bool => (u.2, c6FullLayerStateCode d a
        (theorem16_intervalGradientFlowFixedPoints.fixedPoint u.2).1))
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    exact ProbabilityTheory.indepFun_prod
      (X := fun b : Bool => b)
      (Y := fun h : Bool => (h, c6FullLayerStateCode d a
        (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1))
      measurable_id (measurable_of_finite _)
  · intro d a
    exact (measurable_of_finite _).aemeasurable
  · intro d a h
    exact c6FullLayerGamma_event (fun γ => γ.profile a = c6FullLayerPresence.profile d h a)
  · intro d a h e b r
    exact c6FullLayerGamma_event (fun γ => γ.incidentRelation d a r e b ↔
      c6FullLayerPresence.relationEdge h d a r e b)
  · intro d a h
    exact c6FullLayerGamma_event (fun γ => γ = c6FullLayerPresence.relationalState d h a)

/-- 全層の出力は同じ履歴別固定点の履歴であり、候補介入に依存しない。 -/
theorem c6FullLayer_output_eq_history (d h s : Bool) (a : CommonLayer) (u : Bool × Bool) :
    c6FullLayerMeasuredC3Model.model.scm.outputEquation d a h u s = h := by
  change decide ((theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 0 = 1) = h
  have hx := theorem16_intervalGradientFlowFixedPoint_coordinate h 0
  cases h <;> simp [hx, theorem16_intervalGradientCenter]

/-- 全主体・全共通層で同じ測度付きC3一般入口を実適用する。 -/
theorem c6FullLayer_noAtman : ∀ d a,
    ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      c6FullLayerMeasuredC3Model.model.scm.toIndexed.toProbabilityCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference
    c6FullLayerMeasuredC3Model
  intro d a h s
  filter_upwards with u
  rw [c6FullLayer_output_eq_history, c6FullLayer_output_eq_history]

/-- 全Γを元の二層アドレスに制限する。全層Γ自体は保持し、旧観測の回収にだけ使う。 -/
def c6RestrictGamma (γ : C6FullLayerGamma) : Theorem25HistoryDependentGamma where
  profile := fun b => γ.profile (operationalLayerAddress b)
  verticalNeighborhood := operationalLayerAddress ⁻¹' γ.verticalNeighborhood
  incidentRelation := fun e b r f c => γ.incidentRelation e
    (operationalLayerAddress b) r f (operationalLayerAddress c)

/-- 元二層に対応するcontextで、全profile・縦近傍・入出辺の全観測を保存する。 -/
theorem c6RestrictGamma_relationalState (d h a : Bool) :
    c6RestrictGamma (c6FullLayerPresence.relationalState d h (operationalLayerAddress a)) =
      theorem25_historyDependentPresenceRelations.relationalState d h a := by
  unfold c6RestrictGamma Theorem25PresenceRelationModel.relationalState
  congr 1
  · ext b
    cases a <;> cases b <;>
      simp [c6FullLayerPresence, theorem25_historyDependentPresenceRelations,
        operationalLayerAddress]
  · funext e b r f c
    cases a <;> cases b <;> cases c <;>
      simp [c6FullLayerPresence, theorem25_historyDependentPresenceRelations,
        operationalLayerAddress]

/-- 全層SCMのΓを元二層へ戻すと、同じ固定点由来の元構造式そのもの。 -/
theorem c6FullLayer_state_restricts_to_source (d a h : Bool) (u : Bool × Bool) :
    c6RestrictGamma
      (c6FullLayerMeasuredC3Model.model.scm.stateEquation d (operationalLayerAddress a) h u) =
      theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u := by
  change c6RestrictGamma (c6FullLayerStateCode d (operationalLayerAddress a)
    (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1) =
      theorem25_intervalGradientFlowStateCode d a
        (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1
  rw [c6FullLayerStateCode_matches, c6RestrictGamma_relationalState,
    theorem25_intervalGradientFlowStateCode_matches]

/-- 拡張によって法則・履歴・候補の値は変わらない。 -/
theorem c6FullLayer_source_data (d a : Bool) :
    c6FullLayerMeasuredC3Model.model.scm.exogenousLaw =
        theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw ∧
    c6FullLayerMeasuredC3Model.model.scm.globalHistory =
        theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistory ∧
    c6FullLayerMeasuredC3Model.model.scm.candidateVariable d (operationalLayerAddress a) =
        theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d a := by
  exact ⟨rfl, rfl, rfl⟩

/-- 介入jointの完全な元二層観測回収。Γ周辺や出力周辺だけの一致ではない。 -/
theorem c6FullLayer_intervenedJoint_restricts_to_source (d a h s : Bool) :
    ((c6FullLayerMeasuredC3Model.model.scm.exogenousLaw.toMeasure).map
      (fun u =>
        (c6FullLayerMeasuredC3Model.model.scm.stateEquation d (operationalLayerAddress a) h u,
         c6FullLayerMeasuredC3Model.model.scm.outputEquation d (operationalLayerAddress a) h u s))).map
      (fun z => (c6RestrictGamma z.1, z.2)) =
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw.toMeasure).map
      (fun u =>
        (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
         theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u s)) := by
  rw [Measure.map_map
    (show Measurable (fun z : C6FullLayerGamma × Bool => (c6RestrictGamma z.1, z.2)) from
      ((measurable_from_top (f := c6RestrictGamma)).comp measurable_fst).prodMk measurable_snd)
    (measurable_of_finite _)]
  congr 1
  funext u
  exact Prod.ext (c6FullLayer_state_restricts_to_source d a h u)
    ((c6FullLayer_output_eq_history d h s (operationalLayerAddress a) u).trans
      (theorem25_intervalGradientFlowRandomized_output_eq_history d a h u s).symm)

/-- 全層SCMの同一観測を型付きR_iに拡張する。 -/
def c6FullLayerTypedObservation (z : C6FullLayerGamma × Bool) :
    (C6FullLayerGamma × C6TypedSelfRepresentation) × Bool :=
  ((z.1, c6TypedSelfRepresentation z.2), z.2)

theorem c6FullLayerTypedObservation_measurable : Measurable c6FullLayerTypedObservation :=
  (measurable_fst.prodMk
    ((measurable_of_finite c6TypedSelfRepresentation).comp measurable_snd)).prodMk measurable_snd

/-- 共通全層で、同じSCMと三表現を使う自己過程。 -/
def c6FullLayerTypedSelfProcess (d : Bool) (a : CommonLayer) :
    Theorem25SelfProcessSCM Bool (Bool × Bool)
      (C6FullLayerGamma × C6TypedSelfRepresentation) Bool Bool where
  exogenousLaw := c6FullLayerMeasuredC3Model.model.scm.exogenousLaw
  inputHistory := c6FullLayerMeasuredC3Model.model.scm.globalHistory
  candidateVariable := c6FullLayerMeasuredC3Model.model.scm.candidateVariable d a
  inputHistoryAEMeasurable := c6FullLayerMeasuredC3Model.model.scm.globalHistoryAEMeasurable
  candidateAEMeasurable := c6FullLayerMeasuredC3Model.model.scm.candidateVariableAEMeasurable d a
  baselineEquation := fun h u => c6FullLayerTypedObservation
    (c6FullLayerMeasuredC3Model.model.scm.stateEquation d a h u,
      c6FullLayerMeasuredC3Model.model.scm.outputEquation d a h u
        (c6FullLayerMeasuredC3Model.model.scm.candidateVariable d a u))
  intervenedEquation := fun h s u => c6FullLayerTypedObservation
    (c6FullLayerMeasuredC3Model.model.scm.stateEquation d a h u,
      c6FullLayerMeasuredC3Model.model.scm.outputEquation d a h u s)
  baselineAEMeasurable := fun h => c6FullLayerTypedObservation_measurable.comp_aemeasurable
    (c6FullLayerMeasuredC3Model.model.scm.baselineJointAEMeasurable d a h)
  intervenedAEMeasurable := fun h s => c6FullLayerTypedObservation_measurable.comp_aemeasurable
    (c6FullLayerMeasuredC3Model.model.scm.intervenedJointAEMeasurable d a h s)

/-- 25-A2を全共通層・全主体で証明する。 -/
theorem c6FullLayerTypedSelfProcess_satisfies25A2 (d : Bool) (a : CommonLayer) :
    (c6FullLayerTypedSelfProcess d a).toLawModel.Condition25A2 () := by
  apply (c6FullLayerTypedSelfProcess d a).condition25A2
  · change ProbabilityTheory.IndepFun Prod.snd Prod.fst
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    exact (ProbabilityTheory.indepFun_prod (X := id) (Y := id)
      measurable_id measurable_id).symm
  · intro h s
    congr 1

/-- 全層の同じ観測が真のΓと実Self/Ego/TCZを同時に保持する。 -/
theorem c6FullLayerTypedSelfProcess_representation (d h s : Bool) (a : CommonLayer)
    (u : Bool × Bool) :
    ((c6FullLayerTypedSelfProcess d a).intervenedEquation h s u).1 =
      (c6FullLayerPresence.relationalState d h a, c6TypedSelfRepresentation h) := by
  apply Prod.ext
  · exact c6FullLayerStateCode_matches d h a
  · change c6TypedSelfRepresentation
      (c6FullLayerMeasuredC3Model.model.scm.outputEquation d a h u s) = _
    rw [c6FullLayer_output_eq_history]

/-- 非定数候補の両値は同じ外生lawのもとで全主体・全層で正質量を持つ。 -/
theorem c6FullLayer_candidate_positive (d s : Bool) (a : CommonLayer) :
    Theorem25GlobalHistorySCM.candidateHasPositiveMass
      c6FullLayerMeasuredC3Model.model.scm.toIndexed d a s :=
  theorem25_intervalGradientFlowRandomized_candidate_has_positive_mass s

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.c6FullLayer_noAtman
#print axioms Tomabechi.Consistency.C6.c6FullLayerStateCode_matches
#print axioms Tomabechi.Consistency.C6.c6FullLayer_intervenedJoint_restricts_to_source
#print axioms Tomabechi.Consistency.C6.c6FullLayerTypedSelfProcess_satisfies25A2
#print axioms Tomabechi.Consistency.C6.c6FullLayerTypedSelfProcess_representation
#print axioms Tomabechi.Consistency.C6.c6FullLayer_candidate_positive
