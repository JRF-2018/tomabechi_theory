import Tomabechi.Consistency.ConsistencyC6_CenteredContexts

/-!
# C6：共有SCMの同一観測から得る型付き自己過程

Self作用素・Ego自己更新・TCZ集合を異なる型で保持し、元SCMの(Γ,Y⁺)から
履歴を復元して同時に観測する。候補や行為を履歴の代用にしない。
全主体・行為で同じ外生法則・入力履歴・候補変数を使う。
-/

noncomputable section
namespace Tomabechi.Consistency.C6

open Tomabechi.Theorem16_25
open Tomabechi.Consistency.C4
open MeasureTheory

/-- 実際のC4自己過程。Selfは集合選別作用素、Egoは自己更新写像、TCZは集合。
Nat全層を保持し、固定点codeのBoolだけで三表現を代替しない。 -/
structure C6TypedSelfRepresentation where
  Self : ℕ → Set ℝ → Set ℝ
  Ego : ℕ → Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1
  TCZ : ℕ → Set ℝ

instance : MeasurableSpace C6TypedSelfRepresentation := ⊤

/-- 元のC4型付きadapterの同じ履歴から三表現を取得する。 -/
def c6TypedSelfRepresentation (h : Bool) : C6TypedSelfRepresentation where
  Self := theorem16_intervalGradientFlowC4SelfEgoTCZ.Self h
  Ego := theorem16_intervalGradientFlowC4SelfEgoTCZ.Ego h
  TCZ := theorem16_intervalGradientFlowC4SelfEgoTCZ.TCZ h

/-- 共有SCMのΓを消さず、将来出力に符号化された履歴から三表現を回収する。
この観測をbaselineと介入の両方へ適用する。 -/
def c6TypedSelfObservation (z : Theorem25HistoryDependentGamma × Bool) :
    (Theorem25HistoryDependentGamma × C6TypedSelfRepresentation) × Bool :=
  ((z.1, c6TypedSelfRepresentation z.2), z.2)

theorem c6TypedSelfObservation_measurable : Measurable c6TypedSelfObservation := by
  exact (measurable_fst.prodMk
    ((measurable_of_finite c6TypedSelfRepresentation).comp measurable_snd)).prodMk
      measurable_snd

/-- 全主体・行為で元のSCMを同じ観測写像に通した自己過程。
原モデルの法則を別の独立法則で置き換えない。 -/
def c6TypedSelfProcessSCM (d a : Bool) :
    Theorem25SelfProcessSCM Bool (Bool × Bool)
      (Theorem25HistoryDependentGamma × C6TypedSelfRepresentation) Bool Bool where
  exogenousLaw := theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw
  inputHistory := theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistory
  candidateVariable := theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d a
  inputHistoryAEMeasurable :=
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistoryAEMeasurable
  candidateAEMeasurable :=
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariableAEMeasurable d a
  baselineEquation := fun h u => c6TypedSelfObservation
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
      theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u
        (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d a u))
  intervenedEquation := fun h s u => c6TypedSelfObservation
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
      theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u s)
  baselineAEMeasurable := fun h => c6TypedSelfObservation_measurable.comp_aemeasurable
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.baselineJointAEMeasurable d a h)
  intervenedAEMeasurable := fun h s => c6TypedSelfObservation_measurable.comp_aemeasurable
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.intervenedJointAEMeasurable d a h s)

/-- R_iの三表現は、元SCMの同じ履歴hに対応する実C4データである。 -/
theorem c6TypedSelfProcessSCM_representation (d a h s : Bool) (u : Bool × Bool) :
    ((c6TypedSelfProcessSCM d a).intervenedEquation h s u).1.2 =
      c6TypedSelfRepresentation h := by
  change c6TypedSelfRepresentation
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u s) = _
  rw [theorem25_intervalGradientFlowRandomized_output_eq_history]

/-- 全主体・行為・履歴・候補に対する25-A2。候補と履歴は元の独立座標である。 -/
theorem c6TypedSelfProcessSCM_satisfies25A2 (d a : Bool) :
    (c6TypedSelfProcessSCM d a).toLawModel.Condition25A2 () := by
  apply (c6TypedSelfProcessSCM d a).condition25A2
  · change ProbabilityTheory.IndepFun Prod.snd Prod.fst
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    exact (ProbabilityTheory.indepFun_prod (X := id) (Y := id)
      measurable_id measurable_id).symm
  · intro h s
    congr 1

/-- 元SCMの介入jointを同じ観測写像で押し出した法則に厳密に等しい。 -/
theorem c6TypedSelfProcessSCM_intervenedLaw (d a h s : Bool) :
    ((c6TypedSelfProcessSCM d a).exogenousLaw.toMeasure).map
        ((c6TypedSelfProcessSCM d a).intervenedEquation h s) =
      (((theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw.toMeasure).map
        (fun u =>
          (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
           theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u s)))).map
             c6TypedSelfObservation := by
  exact (Measure.map_map c6TypedSelfObservation_measurable
    (measurable_of_finite _)).symm

/-- 元SCMのbaseline jointにも、介入と同じ観測写像を用いる。 -/
theorem c6TypedSelfProcessSCM_baselineLaw (d a h : Bool) :
    ((c6TypedSelfProcessSCM d a).exogenousLaw.toMeasure).map
        ((c6TypedSelfProcessSCM d a).baselineEquation h) =
      (((theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw.toMeasure).map
        (fun u =>
          (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
           theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u
             (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d a u))))).map
             c6TypedSelfObservation := by
  exact (Measure.map_map c6TypedSelfObservation_measurable
    (measurable_of_finite _)).symm

/-- 三表現を付加した観測から元の(Γ,Y⁺)を完全に復元する。 -/
def c6TypedSelfObservationRecovery
    (z : (Theorem25HistoryDependentGamma × C6TypedSelfRepresentation) × Bool) :
    Theorem25HistoryDependentGamma × Bool := (z.1.1, z.2)

theorem c6TypedSelfObservationRecovery_leftInverse :
    Function.LeftInverse c6TypedSelfObservationRecovery c6TypedSelfObservation := by
  intro z
  rfl

/-- 三表現を付加した介入jointから、元SCMの同じ介入jointを厳密に回収する。
R_iの付加でΓや出力の結合情報を失っていない。 -/
theorem c6TypedSelfProcessSCM_recoverIntervenedLaw (d a h s : Bool) :
    (((c6TypedSelfProcessSCM d a).exogenousLaw.toMeasure).map
        ((c6TypedSelfProcessSCM d a).intervenedEquation h s)).map
          c6TypedSelfObservationRecovery =
      (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw.toMeasure).map
        (fun u =>
          (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
           theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u s)) := by
  rw [Measure.map_map
    (show Measurable c6TypedSelfObservationRecovery from
      (measurable_fst.comp measurable_fst).prodMk measurable_snd)
    (measurable_of_finite _)]
  rfl

/-- 介入観測のΓは同じ履歴別逆極限固定点のcodeである。 -/
theorem c6TypedSelfProcessSCM_fixedPointGamma (d a h s : Bool) (u : Bool × Bool) :
    ((c6TypedSelfProcessSCM d a).intervenedEquation h s u).1.1 =
      theorem25_intervalGradientFlowStateCode d a
        (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 := rfl

/-- 固定点codeは元の全profile・関係近傍・入出辺を持つΓそのものに復元される。 -/
theorem c6TypedSelfProcessSCM_relationalState (d a h s : Bool) (u : Bool × Bool) :
    ((c6TypedSelfProcessSCM d a).intervenedEquation h s u).1.1 =
      theorem25_historyDependentPresenceRelations.relationalState d h a := by
  rw [c6TypedSelfProcessSCM_fixedPointGamma]
  exact theorem25_intervalGradientFlowStateCode_matches d a h

/-- 同じ固定点の認知座標から、同じ履歴の三表現を復元する。 -/
theorem c6TypedSelfRepresentation_from_fixedPoint (h : Bool) :
    c6TypedSelfRepresentation
        (decide ((theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 0 = 1)) =
      c6TypedSelfRepresentation h := by
  have hx := theorem16_intervalGradientFlowFixedPoint_coordinate h 0
  cases h <;> simp [hx, theorem16_intervalGradientCenter]

/-- Selfを実到達集合に適用すると、このR_iが保持する同じTCZとなる。 -/
theorem c6TypedSelfRepresentation_self_tcz (h : Bool) (i : ℕ) :
    (c6TypedSelfRepresentation h).Self i
        (theorem16_intervalGradientFlowC4SelfEgoTCZ.reachable h i) =
      (c6TypedSelfRepresentation h).TCZ i :=
  theorem16_intervalGradientFlowC4SelfEgoTCZ.self_is_tcz h i

/-- Egoは同じ履歴流の時刻1自己更新である。 -/
theorem c6TypedSelfRepresentation_ego_feedback (h : Bool) (i : ℕ)
    (x : Set.Icc (0 : ℝ) 1) :
    (c6TypedSelfRepresentation h).Ego i x =
      theorem16_intervalGradientFlowFeedback h i x :=
  theorem16_intervalGradientFlowC4SelfEgoTCZ.ego_is_feedback h i x

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_satisfies25A2
#print axioms Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_intervenedLaw
#print axioms Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_relationalState
#print axioms Tomabechi.Consistency.C6.c6TypedSelfRepresentation_from_fixedPoint
#print axioms Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_recoverIntervenedLaw
