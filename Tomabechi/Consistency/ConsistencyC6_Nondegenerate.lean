import Tomabechi.Consistency.ConsistencyC6_ModelSignature

/-!
# C6：共有署名から読む非退化性

軌道、零目標、段時刻、固定点、候補の正質量はすべて同じモデルのフィールドを参照する。
N2の非終端添字は逆系のNatであり、共通束の最大元を否定する主張ではない。
ここでは非退化性を供給する。全原文条件の受入と統合存在宣言は別に必要である。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Theorem24_26
open Tomabechi.Theorem16_25
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1CommonModel
open Tomabechi.Consistency.ConsistencyC1Theorem3Bridge

/-- N1–N7の実データ証拠。N7は指定された適用領域の非空性を表し、
全原文入口の仮定をこのrecordだけで網羅したとは扱わない。 -/
structure Nondegenerate (M : ModelSignature) : Prop where
  /-- N1：正時間区間上のalive非定数軌道と、その初期点の零目標外性。 -/
  moving_alive : ∃ x : C6TopState,
    x ∉ theorem26ZeroValueTarget M.dynamics.alive (M.data.optimalValue ⊤) 0 ∧
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      M.data.trajectory ⊤ M.dynamics.feedback x 0 s ∈ M.dynamics.alive) ∧
    M.data.trajectory ⊤ M.dynamics.feedback x 0 0 ≠
      M.data.trajectory ⊤ M.dynamics.feedback x 0 1
  /-- N2：同じ自己表象のTCZに二点がある。 -/
  tcz_two_points : ∃ h : Bool, ∃ i : ℕ, ∃ x y : ℝ,
    x ≠ y ∧ x ∈ (M.selfRepresentation h).TCZ i ∧ y ∈ (M.selfRepresentation h).TCZ i
  /-- N2：逆系の有限添字は非空、有向、最大元なし。 -/
  inverse_indices : (∃ n : ℕ, commonStageAddress n ≠ (⊤ : CommonLayer)) ∧
    (∀ m n : ℕ, ∃ k : ℕ,
      commonStageAddress m ≤ commonStageAddress k ∧ commonStageAddress n ≤ commonStageAddress k) ∧
    (∀ n : ℕ, ∃ m : ℕ, commonStageAddress n < commonStageAddress m)
  /-- N3：二値goalの正情報問題を同じ情報lawに採用する。
  entropyの引数はこのlawを生成する入力測度とmassであり、SCM候補ではない。 -/
  positive_information :
    M.informationLaw 1 = Tomabechi.Consistency.C3.upperJoint ∧
    0 < Tomabechi.Theorem21.conditionalGoalEntropy
      (MeasureTheory.Measure.dirac ()) Tomabechi.Consistency.C3.inputMass
  goal_two_points : ∃ g₁ g₂ : Bool, g₁ ≠ g₂
  /-- N3/N7：全情報問題の方策族を空にしない。 -/
  information_problems_nonempty : ∀ a : CommonLayer, ∃ q : Bool,
    q ∈ Tomabechi.Consistency.C3.c3ProblemAdmissible a
  /-- N4：実段時刻の各dwellが正で、累積時刻が上に非有界。 -/
  stage_dwell_positive : ∀ n, 0 < M.stageTime (n + 1) - M.stageTime n
  stage_time_unbounded : ∀ B : ℝ, ∃ n : ℕ, B < M.stageTime n
  stage_endpoints_move : ∀ n, (M.stages n).initial < (M.stages (n + 1)).initial
  /-- N4：同じ段列の新情報は非終端層で起きる。 -/
  stage_new_information : ∀ n : ℕ,
    entropyLayerAddress n < (⊤ : CommonLayer) ∧
    ¬ Tomabechi.Consistency.C3.layerV (n + 1) ≤ Tomabechi.Consistency.C3.layerU n
  /-- N5：同じalive集合で、各開始時刻の零目標内外に状態がある。 -/
  target_inside_outside : ∀ T : ℝ, 0 ≤ T → ∃ x y : C6TopState,
    x ∈ M.dynamics.alive ∧ y ∈ M.dynamics.alive ∧
    x ∈ theorem26ZeroValueTarget M.dynamics.alive (M.data.optimalValue ⊤) T ∧
    y ∉ theorem26ZeroValueTarget M.dynamics.alive (M.data.optimalValue ⊤) T
  lower_layer_exists : ∃ a : CommonLayer, a < ⊤
  /-- N6：同じMの二履歴固定点とSCMの全主体/層の非定数候補。 -/
  history_fixed_points_separate :
    (M.fixedPoints.fixedPoint false).1 ≠ (M.fixedPoints.fixedPoint true).1
  candidate_positive : ∀ (d s : Bool) (a : CommonLayer),
    Theorem25GlobalHistorySCM.candidateHasPositiveMass M.scm.model.scm.toIndexed d a s
  /-- N7：C1箱内で抽象残差が正の初期状態を、同じC1証人から指定する。 -/
  c1_applicable : ∃ x : AgentState,
    x ∈ M.c1.initialRegion ∧ x 0 + x 1 = 0 ∧
    0 < c1Theorem3System.abstractResidual 0 (x 0)
  /-- N7：全層、全非負初期対の許容方策族が空でない。 -/
  policies_nonempty : ∀ a (x : C6LayeredState a) (T : ℝ), 0 ≤ T →
    ∃ π : C6LayeredPolicy a, M.data.admissible a π x T
  /-- N7：主体は二つあり、各主体は同じpresenceの実関係辺に参加する。 -/
  subjects_related : (∃ d e : Bool, d ≠ e) ∧ ∀ (h d : Bool),
    ∃ (e : Bool) (a b : CommonLayer) (r : Bool), d ≠ e ∧
      M.scm.model.presenceAndRelations.relationEdge h d a r e b

/-- 非退化性を外部のモデル仮定なしに、共有署名の具体値から供給する。 -/
theorem commonModel_nondegenerate : Nondegenerate commonModel := by
  refine {
    moving_alive := ?_
    tcz_two_points := ?_
    inverse_indices := ?_
    positive_information := ⟨commonModel_couplings.stage_information 0,
      Tomabechi.Consistency.C3.inputEntropy_pos⟩
    goal_two_points := ⟨false, true, Bool.false_ne_true⟩
    information_problems_nonempty := fun a =>
      ⟨false, Tomabechi.Consistency.C3.c3Problem_false_admissible a⟩
    stage_dwell_positive := ?_
    stage_time_unbounded := c6_N4_C3_sameSequence_nonZeno.2.1
    stage_endpoints_move := c6_N4_C3_sameSequence_nonZeno.2.2
    stage_new_information := fun n =>
      ⟨(c6_N4_C3_sameSequence_nonZeno.1 n).2.1,
        (c6_N4_C3_sameSequence_nonZeno.1 n).2.2.1⟩
    target_inside_outside := fun T hT => (c6_N5_C5LayerTarget_nonempty T hT).2
    lower_layer_exists := ⟨operationalLayerAddress false,
      (c6_N5_C5LayerTarget_nonempty 0 (by norm_num)).1⟩
    history_fixed_points_separate := c6C4FlowTCZAdapter.fixed_points_separate
    candidate_positive := c6FullLayer_candidate_positive
    c1_applicable := ⟨commonModel.c1.nontrivialInitial,
      commonModel.c1.nontrivialInitial_in_box,
      commonModel.c1.nontrivialInitial_zero_mean,
      commonModel.c1.nontrivialInitial_has_positive_abstract_residual⟩
    policies_nonempty := fun a x T hT =>
      ⟨commonModel.data.optimalPolicy a x T,
        commonModel.data.optimal_policy_admissible a x T hT⟩
    subjects_related := ?_ }
  · rcases c6_N1_C5Alive_nonconstantTrajectory with ⟨x, hx, ha, hm⟩
    refine ⟨x, ?_, ha, hm⟩
    change x ∉ theorem26ZeroValueTarget Set.univ
      (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue
        (⊤ : Tomabechi.Theorem24_26_Model.SourceAbstraction)) 0
    rw [Tomabechi.Examples.Theorem27.vectorSourceTargetTop_eq_ring]
    exact hx
  · rcases c6_N2_C4CommonLayer_nondegenerate.2.2.2 with
      ⟨h, i, x, y, _, hxy, hx, hy⟩
    refine ⟨h, i, x, y, hxy, ?_, ?_⟩
    · rw [commonModel_couplings.self_tcz,
        ← c6C4FlowTCZAdapter.every_layer_carrier_eq_tcz h i]
      exact hx
    · rw [commonModel_couplings.self_tcz,
        ← c6C4FlowTCZAdapter.every_layer_carrier_eq_tcz h i]
      exact hy
  · exact ⟨c6_N2_C4CommonLayer_nondegenerate.1,
      c6_N2_C4CommonLayer_nondegenerate.2.1,
      c6_N2_C4CommonLayer_nondegenerate.2.2.1⟩
  · intro n
    change 0 < Tomabechi.Consistency.C3.stageTime (n + 1) -
      Tomabechi.Consistency.C3.stageTime n
    rw [Tomabechi.Consistency.C3.stageTime_recurrence]
    simpa using Tomabechi.Consistency.C3.stageDuration_pos n
  · refine ⟨⟨false, true, Bool.false_ne_true⟩, ?_⟩
    intro h d
    rcases commonModel.scm.model.presenceAndRelations.everyExistenceIsRelated h d with
      ⟨e, a, b, r, hne, hedge⟩
    exact ⟨e, a, b, r, hne.symm, hedge⟩

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.commonModel_nondegenerate
