import Theorem16_25_Model

/-!
# C4: 定理16の区間逆極限から定理25への同時接続

履歴ごとの `[0,1]` 逆極限と強凸勾配流、逆極限固定点をコード化した25-C3共有SCMを、
同じ外生法則・大域履歴・候補変数を用いる25-A(2)自己過程へ射影する。
-/

namespace Tomabechi.Consistency.C4

open MeasureTheory ProbabilityTheory
open Tomabechi.Theorem16_25

abbrev C4InverseLimit (h : Bool) :=
  {x : ∀ i : Nat, ℝ // x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
    theorem16_intervalGradientFlowLayerSystem.carrier
    theorem16_intervalGradientFlowLayerSystem.project h}

/-- 第0座標距離を使う履歴別逆極限の完備計量。 -/
@[instance_reducible]
noncomputable def theorem16_intervalGradientFlowC4Metric (h : Bool) : MetricSpace (C4InverseLimit h) :=
  MetricSpace.induced (theorem16_intervalGradientFlowInverseLimitEquiv h)
    (theorem16_intervalGradientFlowInverseLimitEquiv h).injective inferInstance

/-- 積部分空間位相のhomeomorphと、引き戻しSC距離のisometryは同じ第0座標同値を使う。
従ってこの逆極限ではSC距離の位相は積部分空間位相に適合する。 -/
theorem theorem16_intervalGradientFlowC4_metric_product_coordinate_maps_agree (h : Bool) :
    letI : MetricSpace (C4InverseLimit h) := theorem16_intervalGradientFlowC4Metric h
    (theorem16_intervalGradientFlowInverseLimitIsometryEquiv h).toEquiv =
      (theorem16_intervalGradientFlowInverseLimitHomeomorph h).toEquiv := by
  rfl

/-- 第0座標で読む自己表象。関係は表象写像のグラフで閉である。 -/
def theorem16_intervalGradientFlowC4SelfRepresentation (h : Bool) :
    SelfRepresentation (C4InverseLimit h) (Set.Icc (0 : ℝ) 1) where
  relation := {p | p.1.1 = p.2.1 0}
  relation_closed := by
    exact isClosed_eq (continuous_subtype_val.comp continuous_fst)
      ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd))
  represent := fun x => ⟨x.1 0, x.2.1 0⟩
  represent_continuous := Continuous.subtype_mk
    ((continuous_apply 0).comp continuous_subtype_val) (fun x => x.2.1 0)
  represents := fun x => rfl

/-- 表象側の時刻1勾配流写像。 -/
noncomputable def theorem16_intervalGradientFlowC4RepresentedMap (h : Bool) :
    Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
  theorem16_intervalGradientFlowFeedback h 0

/-- 同じ強凸勾配流を方策として、初期値 `[0,1]` から時刻 `t` に到達する集合。 -/
def theorem16_intervalGradientFlowC4Reachable (h : Bool) (t : Set.Icc (0 : ℝ) 1) : Set ℝ :=
  {y | ∃ x : Set.Icc (0 : ℝ) 1,
    theorem16_intervalGradientFlow h x.1 t.1 = y}

/-- 勾配流とその二次評価 `V_h(x)`、閾値 `1/2` で定める正準到達TCZ。 -/
def theorem16_intervalGradientFlowC4TCZ (h : Bool) : Set ℝ :=
  {y | ∃ t : Set.Icc (0 : ℝ) 1, y ∈ theorem16_intervalGradientFlowC4Reachable h t ∧
    theorem16_intervalGradientPotential h y ≤ 1 / 2}

/-- C4の全層carrier `[0,1]` は、同じ勾配流方策・二次評価・閾値から得るTCZである。 -/
theorem theorem16_intervalGradientFlowC4TCZ_eq_carrier (h : Bool) :
    theorem16_intervalGradientFlowC4TCZ h = Set.Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨t, hreach, hv⟩
    rcases hreach with ⟨x, hxy⟩
    rw [← hxy]
    exact theorem16_intervalGradientFlow_stays h x.1 t.1 x.2 t.2
  · intro hy
    refine ⟨⟨0, by norm_num⟩, ⟨⟨y, hy⟩, ?_⟩, ?_⟩
    · simpa using theorem16_intervalGradientFlow_start h y
    · rw [theorem16_intervalGradientPotential]
      have hc : theorem16_intervalGradientCenter h ∈ Set.Icc (0 : ℝ) 1 := by
        cases h <;> norm_num [theorem16_intervalGradientCenter]
      have habs : |y - theorem16_intervalGradientCenter h| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hy.1, hc.2]
        · linarith [hy.2, hc.1]
      have habs' := abs_le.mp habs
      nlinarith [habs'.1, habs'.2,
        sq_nonneg (y - theorem16_intervalGradientCenter h)]

/-- 各履歴・各Nat層のcarrierが、同じ制御方策から得るTCZに等しい。 -/
theorem theorem16_intervalGradientFlowC4LayerCarrier_eq_TCZ (h : Bool) (i : Nat) :
    theorem16_intervalGradientFlowLayerSystem.carrier h i =
      theorem16_intervalGradientFlowC4TCZ h := by
  rw [theorem16_intervalGradientFlowC4TCZ_eq_carrier]
  rfl

/-- Self・Ego・TCZを別々の型で保持するC4の型付き表現。
Selfは到達集合を評価閾値で選別し、Egoは同じ勾配流の時刻1写像、TCZは層の目標集合である。 -/
structure Theorem16IntervalGradientFlowC4SelfEgoTCZ where
  Self : Bool → Nat → Set ℝ → Set ℝ
  Ego : Bool → Nat → Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1
  TCZ : Bool → Nat → Set ℝ
  reachable : Bool → Nat → Set ℝ
  self_is_tcz : ∀ h i, Self h i (reachable h i) = TCZ h i
  ego_is_feedback : ∀ h i x, Ego h i x = theorem16_intervalGradientFlowFeedback h i x
  tcz_is_layer_carrier : ∀ h i,
    TCZ h i = theorem16_intervalGradientFlowLayerSystem.carrier h i

/-- 同じ勾配流・ポテンシャル・閾値から、Self/Ego/TCZの型を保ってC4データを組む。 -/
noncomputable def theorem16_intervalGradientFlowC4SelfEgoTCZ :
    Theorem16IntervalGradientFlowC4SelfEgoTCZ where
  Self := fun h _ reachable =>
    {x | x ∈ reachable ∧ theorem16_intervalGradientPotential h x ≤ 1 / 2}
  Ego := theorem16_intervalGradientFlowFeedback
  TCZ := fun h i => theorem16_intervalGradientFlowLayerSystem.carrier h i
  reachable := fun h i => theorem16_intervalGradientFlowC4Reachable h ⟨0, by norm_num⟩
  self_is_tcz := by
    intro h i
    ext x
    constructor
    · rintro ⟨hreach, hv⟩
      change ∃ z : Set.Icc (0 : ℝ) 1,
        theorem16_intervalGradientFlow h z.1 0 = x at hreach
      rcases hreach with ⟨z, hz⟩
      have hstart := theorem16_intervalGradientFlow_start h z.1
      rw [hstart] at hz
      exact hz ▸ z.property
    · intro hx
      refine ⟨?_, ?_⟩
      · change ∃ z : Set.Icc (0 : ℝ) 1,
          theorem16_intervalGradientFlow h z.1 0 = x
        exact ⟨⟨x, hx⟩, theorem16_intervalGradientFlow_start h x⟩
      · rw [theorem16_intervalGradientPotential]
        have hc : theorem16_intervalGradientCenter h ∈ Set.Icc (0 : ℝ) 1 := by
          cases h <;> norm_num [theorem16_intervalGradientCenter]
        have habs : |x - theorem16_intervalGradientCenter h| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hx.1, hx.2, hc.1, hc.2]
        have habs' := abs_le.mp habs
        nlinarith [habs'.1, habs'.2, sq_nonneg (x - theorem16_intervalGradientCenter h)]
  ego_is_feedback := by intro h i x; rfl
  tcz_is_layer_carrier := by intro h i; rfl

/-- このC4 Presence/RelationモデルのRiは恒等な役割反転で、したがって対合である。 -/
theorem theorem16_intervalGradientFlowC4_Ri_is_involutive (r : Bool) :
    theorem25_historyDependentPresenceRelations.roleInverse
      (theorem25_historyDependentPresenceRelations.roleInverse r) = r := by
  rfl

/-- 定理16層系の縮小写像と第0座標表象は同変である。 -/
theorem theorem16_intervalGradientFlowC4_equivariant (h : Bool) (x : C4InverseLimit h) :
    (theorem16_intervalGradientFlowC4SelfRepresentation h).represent
        (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
          theorem16_intervalGradientFlowLayerSystem.carrier
          theorem16_intervalGradientFlowLayerSystem.project
          theorem16_intervalGradientFlowLayerSystem.projectMaps
          theorem16_intervalGradientFlowLayerSystem.feedback
          theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h x) =
      theorem16_intervalGradientFlowC4RepresentedMap h
        ((theorem16_intervalGradientFlowC4SelfRepresentation h).represent x) := by
  apply Subtype.ext
  rfl

/-- この具体系でSC計量から生成される定理16の履歴別固定点族。 -/
noncomputable def theorem16_intervalGradientFlowC4Points :
    HistoryFixedPoints Bool (∀ i : Nat, ℝ) := by
  let metric := theorem16_intervalGradientFlowC4Metric
  have hcomplete : ∀ h, @CompleteSpace (C4InverseLimit h)
      (metric h).toPseudoMetricSpace.toUniformSpace := by
    intro h
    letI : MetricSpace (C4InverseLimit h) := metric h
    exact (theorem16_intervalGradientFlowInverseLimitIsometryEquiv h).completeSpace
  have hcontract : ∀ h, letI := metric h; ContractingWith
      ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩
      (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
        theorem16_intervalGradientFlowLayerSystem.carrier
        theorem16_intervalGradientFlowLayerSystem.project
        theorem16_intervalGradientFlowLayerSystem.projectMaps
        theorem16_intervalGradientFlowLayerSystem.feedback
        theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h) := by
    intro h
    letI : MetricSpace (C4InverseLimit h) := metric h
    exact theorem16_intervalGradientFlowInverseLimit_contracting h
  exact historyFixedPointsOfTheorem16LayerSystemWithSCMetric
    theorem16_intervalGradientFlowLayerSystem metric hcomplete
    (fun _ => ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩)
    hcontract

/-- 一般接続定理に渡すSC距離上の固定点族は履歴に応じて異なる。 -/
theorem theorem16_intervalGradientFlowC4_generatedFixedPoints_separate :
    (theorem16_intervalGradientFlowC4Points.fixedPoint false).1 ≠
      (theorem16_intervalGradientFlowC4Points.fixedPoint true).1 := by
  classical
  intro heq
  have hfalse := theorem16_intervalGradientFlowC4Points.unique false
    (theorem16_intervalGradientFlowFixedPoints.fixedPoint false)
    (theorem16_intervalGradientFlowFixedPoints.isFixed false)
  have htrue := theorem16_intervalGradientFlowC4Points.unique true
    (theorem16_intervalGradientFlowFixedPoints.fixedPoint true)
    (theorem16_intervalGradientFlowFixedPoints.isFixed true)
  apply theorem16_intervalGradientFlowFixedPoints_separate
  exact funext fun i => by
    have h0 := congrFun (congrArg Subtype.val hfalse) i
    have h1 := congrFun (congrArg Subtype.val htrue) i
    exact h0.symm.trans ((congrFun heq i).trans h1)

/-- 共有履歴SCMのC3観測束縛を、一般接続定理が使う確率法則統合型へ移す。 -/
noncomputable def theorem25_sharedC3Model_to_integrated
    {D History Layer Role U : Type*} [CompleteLattice Layer]
    [MeasurableSpace U] [MeasurableSpace History]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25SharedGlobalHistoryC3Model D History Layer Role U
      Representation Gamma Output Candidate) :
    Theorem25C3IntegratedModel D History Layer Role
      Representation Gamma Output Candidate where
  integrated := {
    probability := Theorem25GlobalHistorySCM.toProbabilityCausalModel
      (M.scm.toIndexed)
    presenceAndRelations := M.presenceAndRelations
    profileObservation := M.profileObservation
    relationObservation := M.relationObservation
    baselineProfileCoherent := M.baselineProfileCoherent
    baselineRelationsCoherent := M.baselineRelationsCoherent }
  relationalStateObservation := M.relationalStateObservation
  encodeRelationalState := M.encodeRelationalState
  relationalStateObservation_encode := M.relationalStateObservation_encode
  baselineRelationalStateCoherent := M.baselineRelationalStateCoherent

/-- C4の一般入口証明書。定理16の原文層条件からの固定点存在・適合SC距離での幾何収束・
同変表象と、固定点符号化した同一の25-C3 SCM上の25-A(2)/B/C3/Dを一括して接続する。
対象は各履歴の `[0,1]` 対角逆系と固定二主体モデルである。 -/
theorem theorem16_intervalGradientFlowC4_generalEntryConnection :
    (∀ h, letI := theorem16_intervalGradientFlowC4Metric h; ∃! x : C4InverseLimit h,
      historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
        theorem16_intervalGradientFlowLayerSystem.carrier
        theorem16_intervalGradientFlowLayerSystem.project
        theorem16_intervalGradientFlowLayerSystem.projectMaps
        theorem16_intervalGradientFlowLayerSystem.feedback
        theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h x = x ∧
      theorem16_intervalGradientFlowC4RepresentedMap h
        ((theorem16_intervalGradientFlowC4SelfRepresentation h).represent x) =
          (theorem16_intervalGradientFlowC4SelfRepresentation h).represent x ∧
      ((theorem16_intervalGradientFlowC4SelfRepresentation h).represent x, x) ∈
        (theorem16_intervalGradientFlowC4SelfRepresentation h).relation ∧
      ∀ (x₀ : C4InverseLimit h) (n : ℕ),
        dist
          ((historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
            theorem16_intervalGradientFlowLayerSystem.carrier
            theorem16_intervalGradientFlowLayerSystem.project
            theorem16_intervalGradientFlowLayerSystem.projectMaps
            theorem16_intervalGradientFlowLayerSystem.feedback
            theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h)^[n] x₀) x ≤
          (Real.exp (-1)) ^ n * dist x₀ x) ∧
    theorem25_intervalGradientFlowRandomizedSelfProcessSCM.toLawModel.Condition25A2 () ∧
    (∀ s : Bool,
      Theorem25GlobalHistorySCM.candidateHasPositiveMass
        (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.toIndexed)
        false false s) ∧
    (theorem16_intervalGradientFlowC4Points.fixedPoint false).1 ≠
      (theorem16_intervalGradientFlowC4Points.fixedPoint true).1 ∧
    (∀ h i,
      theorem16_intervalGradientFlowLayerSystem.carrier h i =
        theorem16_intervalGradientFlowC4TCZ h) ∧
    (¬ ∃ x : ∀ i : Nat, ℝ,
      ∀ h, ∃ hx : x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
        theorem16_intervalGradientFlowLayerSystem.carrier
        theorem16_intervalGradientFlowLayerSystem.project h,
        historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
          theorem16_intervalGradientFlowLayerSystem.carrier
          theorem16_intervalGradientFlowLayerSystem.project
          theorem16_intervalGradientFlowLayerSystem.projectMaps
          theorem16_intervalGradientFlowLayerSystem.feedback
          theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h ⟨x, hx⟩ = ⟨x, hx⟩) ∧
    (∀ d a,
      ¬ ((Theorem25ProbabilityCausalModel.toCausalModel
        ((theorem25_sharedC3Model_to_integrated
          theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model).integrated.probability)).hasAtman
          d a)) ∧
    (∀ d a h s,
      (Theorem25GlobalHistorySCM.toProbabilityCausalModel
        (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.toIndexed)).intervenedJointLaw
        d a h s =
      (Theorem25GlobalHistorySCM.toProbabilityCausalModel
        (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.toIndexed)).baselineJointLaw
        d a h) ∧
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.ObservationEventsMeasurable := by
  let metric := theorem16_intervalGradientFlowC4Metric
  have hcomplete : ∀ h, @CompleteSpace (C4InverseLimit h)
      (metric h).toPseudoMetricSpace.toUniformSpace := by
    intro h
    letI : MetricSpace (C4InverseLimit h) := metric h
    exact (theorem16_intervalGradientFlowInverseLimitIsometryEquiv h).completeSpace
  let q : Bool → NNReal := fun _ => ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩
  have hcontract : ∀ h, letI := metric h; ContractingWith (q h)
      (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
        theorem16_intervalGradientFlowLayerSystem.carrier
        theorem16_intervalGradientFlowLayerSystem.project
        theorem16_intervalGradientFlowLayerSystem.projectMaps
        theorem16_intervalGradientFlowLayerSystem.feedback
        theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h) := by
    intro h
    letI : MetricSpace (C4InverseLimit h) := metric h
    exact theorem16_intervalGradientFlowInverseLimit_contracting h
  have hD : ∀ d a h s,
      (Theorem25GlobalHistorySCM.toProbabilityCausalModel
        (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.toIndexed)).intervenedJointLaw
        d a h s =
      (Theorem25GlobalHistorySCM.toProbabilityCausalModel
        (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.toIndexed)).baselineJointLaw
        d a h := by
    exact theorem25_globalHistorySCM_functionalCompleteness_of_candidateIrrelevance
      (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.toIndexed)
      (by
        intro d a h u s
        change theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation
            d a h u
            (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable
              d a u) =
          theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation
            d a h u s
        rw [theorem25_intervalGradientFlowRandomized_output_eq_history,
          theorem25_intervalGradientFlowRandomized_output_eq_history])
  have hconn := theorem16HistoryLayerSystem_to_theorem25_fullConnection
    theorem16_intervalGradientFlowLayerSystem metric hcomplete q hcontract
    (fun _ : Bool => Set.Icc (0 : ℝ) 1)
    theorem16_intervalGradientFlowC4SelfRepresentation
    theorem16_intervalGradientFlowC4RepresentedMap
    (by intro h; exact theorem16_intervalGradientFlowLayerSystem.feedbackContinuous h 0)
    theorem16_intervalGradientFlowC4_equivariant
    ⟨false, true, theorem16_intervalGradientFlowC4_generatedFixedPoints_separate⟩
    theorem25_intervalGradientFlowRandomizedSelfProcessSCM
    theorem25_intervalGradientFlowRandomizedSelfProcessSCM_satisfies25A2
    (theorem25_sharedC3Model_to_integrated
      theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model) hD
  exact ⟨hconn.1,
    theorem25_intervalGradientFlowRandomizedSelfProcessSCM_satisfies25A2,
    theorem25_intervalGradientFlowRandomized_candidate_has_positive_mass,
    theorem16_intervalGradientFlowC4_generatedFixedPoints_separate,
    theorem16_intervalGradientFlowC4LayerCarrier_eq_TCZ,
    hconn.2.1,
    hconn.2.2,
    hD,
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.observationEventsMeasurable⟩

end Tomabechi.Consistency.C4
