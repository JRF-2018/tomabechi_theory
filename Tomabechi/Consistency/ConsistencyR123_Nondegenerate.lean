import Tomabechi.Consistency.ConsistencyR123_PointDomain

/-!
# 共有署名Nを直接読む非退化性（N1–N7）

旧 `Nondegenerate N.legacy` は固定した旧署名の軌道・目標・情報law・段・候補を読む。
ここでは同じ条件を、軌道・目標・方策はN.data/N.dynamics、候補・関係はN.scm、
情報はN.informationLaw、段はN.stages/N.stageAddress、一点初期集合はN.pointAdapterから読む形で
述べ直し、受入型 `SharedPointDomainInputs N` から証明する。
N.legacyに実際に格納された固定点・自己表象は旧署名のfieldとして明示して使う
（`history_fixed_points_separate`・`tcz_two_points`）。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1 Tomabechi.Consistency.C3
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1Theorem3Bridge
open Tomabechi.Theorem24_26 Tomabechi.Theorem16_25

private theorem value_cast {I : Type*} {S : I → Type*} (f : ∀ i, S i → ℝ → ℝ)
    {i j : I} (h : j = i) (x : S j) (T : ℝ) :
    f j x T = f i (cast (congrArg S h) x) T := by
  cases h
  rfl

/-- 頂点の最適値を、同じ座標同値で旧署名の値へ移す。 -/
theorem SharedDataPreservation.topValue_chart {N : SharedModelSignature}
    (h : SharedDataPreservation N) (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) :
    N.data.optimalValue ⊤ x T =
      N.legacy.data.optimalValue ⊤ (fullCommonTopStateEquiv x) T :=
  (h.optimalValue ⊤ x T).trans
    (value_cast N.legacy.data.optimalValue fullCommonLayerIndex_top x T)

/-- 零評価目標への所属も、同じ座標同値で旧署名の目標へ移る。 -/
theorem SharedDataPreservation.topTarget_iff {N : SharedModelSignature}
    (h : SharedDataPreservation N) (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) :
    x ∈ theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) T ↔
      fullCommonTopStateEquiv x ∈ theorem26ZeroValueTarget N.legacy.dynamics.alive
        (N.legacy.data.optimalValue ⊤) T := by
  simp only [theorem26ZeroValueTarget, Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [h.top_alive, h.topValue_chart]

/-- N1–N7を、共有署名Nの実fieldから読む形で述べた非退化性。 -/
structure SharedNondegenerate (N : SharedModelSignature) : Prop where
  /-- N1：N.dataの頂点軌道が正時間区間でaliveかつ非定数で、初期点は零目標の外にある。 -/
  moving_alive : ∃ x : fullCommonLayerState (⊤ : CommonConcept),
    x ∉ theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) 0 ∧
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → N.topPath x 0 s ∈ N.dynamics.alive) ∧
    N.topPath x 0 0 ≠ N.topPath x 0 1
  /-- N2：N.legacyに格納した同じ自己表象のTCZに二点がある。 -/
  tcz_two_points : ∃ h : Bool, ∃ i : ℕ, ∃ x y : ℝ,
    x ≠ y ∧ x ∈ (N.legacy.selfRepresentation h).TCZ i ∧
      y ∈ (N.legacy.selfRepresentation h).TCZ i
  /-- N2：N.stageAddressは共通束で、頂より下・有向・最大元なし。 -/
  inverse_indices : (∃ n : ℕ, N.stageAddress n ≠ (⊤ : CommonConcept)) ∧
    (∀ m n : ℕ, ∃ k : ℕ,
      N.stageAddress m ≤ N.stageAddress k ∧ N.stageAddress n ≤ N.stageAddress k) ∧
    (∀ n : ℕ, ∃ m : ℕ, N.stageAddress n < N.stageAddress m)
  /-- N3：N.informationLawの正情報住所は同じ情報lawを持ち、goal entropyは正。 -/
  positive_information :
    N.informationLaw (N.stageAddress 0) = Tomabechi.Consistency.C3.upperJoint ∧
    0 < Tomabechi.Theorem21.conditionalGoalEntropy
      (MeasureTheory.Measure.dirac ()) Tomabechi.Consistency.C3.inputMass
  goal_two_points : ∃ g₁ g₂ : Bool, g₁ ≠ g₂
  /-- N3/N7：全CommonConcept点で、情報lawは確率測度、二つの異なる実許容方策がある。 -/
  information_problems_nonempty : ∀ a : CommonConcept,
    IsProbabilityMeasure (N.informationLaw a) ∧
    fullInformationDecoder a false ≠ fullInformationDecoder a true ∧
    ∀ (g : Bool) (x : fullCommonLayerState a) (T : ℝ), 0 ≤ T →
      N.data.admissible a (fullInformationDecoder a g) x T
  /-- N4：実段の開始時刻は狭義増加で上に非有界。 -/
  stage_dwell_positive : ∀ n, 0 < (N.stages (n + 1)).startTime - (N.stages n).startTime
  stage_time_unbounded : ∀ B : ℝ, ∃ n : ℕ, B < (N.stages n).startTime
  stage_endpoints_move : ∀ n, (N.stages n).initial ≠ (N.stages (n + 1)).initial
  /-- N4：同じ段列の新情報は頂より下の住所で起きる。 -/
  stage_new_information : ∀ n : ℕ,
    N.stageAddress n < (⊤ : CommonConcept) ∧
    ¬ Tomabechi.Consistency.C3.layerV (n + 1) ≤ Tomabechi.Consistency.C3.layerU n
  /-- N5：N.dynamicsのalive集合で、各開始時刻の零目標内外に状態がある。 -/
  target_inside_outside : ∀ T : ℝ, 0 ≤ T → ∃ x y : fullCommonLayerState (⊤ : CommonConcept),
    x ∈ N.dynamics.alive ∧ y ∈ N.dynamics.alive ∧
    x ∈ theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) T ∧
    y ∉ theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) T
  lower_layer_exists : ∃ a : CommonConcept, a < ⊤
  /-- N6：N.legacyの二履歴固定点は異なり、N.scmの全主体/層で候補は正質量を持つ。 -/
  history_fixed_points_separate :
    (N.legacy.fixedPoints.fixedPoint false).1 ≠ (N.legacy.fixedPoints.fixedPoint true).1
  candidate_positive : ∀ (d s : Bool) (a : CommonConcept),
    Theorem25GlobalHistorySCM.candidateHasPositiveMass N.scm.model.scm.toIndexed d a s
  /-- N7：N.pointAdapterの一点初期集合を持つ、箱内・零平均・正抽象残差の初期状態。 -/
  c1_applicable : ∃ x : AgentState,
    x ∈ N.legacy.c1.initialRegion ∧ x 0 + x 1 = 0 ∧
    0 < c1Theorem3System.abstractResidual 0 (x 0) ∧
    (N.pointAdapter x 0).initialSet = {x}
  /-- N7：全層・全非負初期対で、N.dataの許容方策族は空でない。 -/
  policies_nonempty : ∀ a (x : fullCommonLayerState a) (T : ℝ), 0 ≤ T →
    ∃ π : fullCommonLayerPolicy a, N.data.admissible a π x T
  /-- N7：主体は二つあり、各主体はN.scmの同じpresenceの実関係辺に参加する。 -/
  subjects_related : (∃ d e : Bool, d ≠ e) ∧ ∀ (h d : Bool),
    ∃ (e : Bool) (a b : CommonConcept) (r : Bool), d ≠ e ∧
      N.scm.model.presenceAndRelations.relationEdge h d a r e b

/-- 受入型から共有署名の非退化性を構成する。 -/
theorem SharedPointDomainInputs.sharedNondegenerate {N : SharedModelSignature}
    (hN : SharedPointDomainInputs N) : SharedNondegenerate N := by
  have hs : SharedStageInputs N := hN.toSharedFullExperimentInputs.toSharedPointInputs.toSharedStageInputs
  have hk : SharedKernelInputs N :=
    hs.toSharedSCMAndExperimentInputs.toSharedR3And27Inputs.toSharedR3Inputs.toSharedKernelInputs
  have hp := hk.preservation
  have hnd := hk.nondegenerate
  have hconc := hs.switching.fullConclusion
  have hstart := hs.switching.start
  have hrec := hs.switching.recurrence
  have htop : layerAddressEmbedding (⊤ : WithTop ℕ) = ⊤ := layerAddress_top
  have hlt : ∀ n : ℕ, N.stageAddress n < (⊤ : CommonConcept) := by
    intro n
    rw [hp.stageAddress, commonConceptPositiveEntropyAddress, ← htop]
    exact layerAddressEmbedding.lt_iff_lt.mpr (by simp [entropyLayerAddress_eq_succ])
  refine {
    moving_alive := ?_
    tcz_two_points := hnd.tcz_two_points
    inverse_indices := ?_
    positive_information := ?_
    goal_two_points := ⟨false, true, Bool.false_ne_true⟩
    information_problems_nonempty := ?_
    stage_dwell_positive := ?_
    stage_time_unbounded := ?_
    stage_endpoints_move := ?_
    stage_new_information := ?_
    target_inside_outside := ?_
    lower_layer_exists := ?_
    history_fixed_points_separate := hnd.history_fixed_points_separate
    candidate_positive := fun d s a => hk.scm_candidate_positive d s a
    c1_applicable := ?_
    policies_nonempty := fun a x T hT =>
      ⟨N.data.optimalPolicy a x T, N.data.optimal_policy_admissible a x T hT⟩
    subjects_related := ?_ }
  · -- N1
    obtain ⟨x, hx, ha, hm⟩ := hnd.moving_alive
    refine ⟨fullCommonTopStateEquiv.symm x, ?_, ?_, ?_⟩
    · rw [hp.topTarget_iff, Equiv.apply_symm_apply]
      exact hx
    · intro s hs'
      rw [hp.top_alive, hp.topPath_chart, Equiv.apply_symm_apply]
      exact ha s hs'
    · intro heq
      apply hm
      have := congrArg fullCommonTopStateEquiv heq
      rw [hp.topPath_chart, hp.topPath_chart, Equiv.apply_symm_apply] at this
      exact this
  · -- N2
    have hmono : ∀ m n : ℕ, m ≤ n → N.stageAddress m ≤ N.stageAddress n := by
      intro m n hmn
      rw [hp.stageAddress, hp.stageAddress, commonConceptPositiveEntropyAddress,
        commonConceptPositiveEntropyAddress]
      exact layerAddressEmbedding.le_iff_le.mpr (by
        simp only [entropyLayerAddress_eq_succ]; exact_mod_cast Nat.succ_le_succ hmn)
    refine ⟨⟨0, (hlt 0).ne⟩, fun m n => ⟨max m n, hmono _ _ (le_max_left _ _),
      hmono _ _ (le_max_right _ _)⟩, fun n => ⟨n + 1, ?_⟩⟩
    rw [hp.stageAddress, hp.stageAddress, commonConceptPositiveEntropyAddress,
      commonConceptPositiveEntropyAddress]
    exact layerAddressEmbedding.lt_iff_lt.mpr (by
      simp only [entropyLayerAddress_eq_succ]; exact_mod_cast Nat.succ_lt_succ (Nat.lt_succ_self n))
  · -- N3
    rw [hp.stage_information 0]
    exact ⟨hk.additional.stage_information 0, Tomabechi.Consistency.C3.inputEntropy_pos⟩
  · exact fun a => ⟨hp.fullInformation_probability a, hN.decoder_distinct a,
      fun g x T hT => hN.decoder_admissible a g x T hT⟩
  · intro n
    rw [hstart, hstart]
    have := hconc.layer_progress.2.2.2.2 n
    linarith
  · intro B
    obtain ⟨n, hn⟩ := hconc.layer_progress.2.2.2.1 B
    exact ⟨n, by rw [hstart]; exact hn⟩
  · intro n heq
    rw [hs.path.initial, hs.path.initial] at heq
    exact (hnd.stage_endpoints_move n).ne (liftedStageCenter_isometry.injective heq)
  · exact fun n => ⟨hlt n, (hnd.stage_new_information n).2⟩
  · intro T hT
    obtain ⟨x, y, hxa, hya, hxt, hyt⟩ := hnd.target_inside_outside T hT
    refine ⟨fullCommonTopStateEquiv.symm x, fullCommonTopStateEquiv.symm y, ?_, ?_, ?_, ?_⟩
    · rw [hp.top_alive, Equiv.apply_symm_apply]; exact hxa
    · rw [hp.top_alive, Equiv.apply_symm_apply]; exact hya
    · rw [hp.topTarget_iff, Equiv.apply_symm_apply]; exact hxt
    · rw [hp.topTarget_iff, Equiv.apply_symm_apply]; exact hyt
  · exact ⟨N.stageAddress 0, hlt 0⟩
  · exact ⟨N.legacy.c1.nontrivialInitial, N.legacy.c1.nontrivialInitial_in_box,
      N.legacy.c1.nontrivialInitial_zero_mean,
      N.legacy.c1.nontrivialInitial_has_positive_abstract_residual,
      hp.point_initial _ 0⟩
  · refine ⟨⟨false, true, Bool.false_ne_true⟩, ?_⟩
    intro h d
    rcases N.scm.model.presenceAndRelations.everyExistenceIsRelated h d with
      ⟨e, a, b, r, hne, hedge⟩
    exact ⟨e, a, b, r, hne.symm, hedge⟩

theorem sharedModel_nondegenerate : SharedNondegenerate sharedModel :=
  sharedModel_pointDomainInputs.sharedNondegenerate

#print axioms sharedModel_nondegenerate

end Tomabechi.Consistency.R123
