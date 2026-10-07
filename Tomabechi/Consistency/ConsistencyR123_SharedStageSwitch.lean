import Tomabechi.Consistency.ConsistencyR123_SharedExperiment

/-!
# 共有署名のH-stage全切替入力

段階の解析入力はN.stagesを読み、中心は共通概念束の忠実な二座標表現で
指定する。原23-Bのgap・線分・時間・遷移・対数待ち条件を全て要求する。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open scoped Topology
open Tomabechi.Consistency.R1 Tomabechi.Consistency.C3
open Tomabechi.Theorem22 Tomabechi.Theorem23

/-- 共通概念束の二座標を同じ二次元認知状態へ表す。 -/
def sharedStageRepresentation (a : CommonConcept) : LiftedStageState :=
  WithLp.toLp 2 (fun i => (a i : ℝ) / Real.sqrt 2)

theorem sharedStageRepresentation_injective : Function.Injective sharedStageRepresentation := by
  intro a b hab
  funext i
  apply Subtype.ext
  have hi := congrArg (fun z : LiftedStageState => z i) hab
  change (a i : ℝ) / Real.sqrt 2 = (b i : ℝ) / Real.sqrt 2 at hi
  exact (div_left_inj' (by positivity : Real.sqrt 2 ≠ 0)).mp hi

/-- 旧アドレスで元の共通表象の等長liftを回収する。 -/
theorem sharedStageRepresentation_oldAddress (a : Atom) :
    sharedStageRepresentation (layerAddressEmbedding a) = liftedStageCenter (representation a) := by
  cases a with
  | none =>
    change sharedStageRepresentation (layerAddress (⊤ : Atom)) = liftedStageCenter (representation ⊤)
    rw [layerAddress_top]
    ext i
    rfl
  | some n => ext i; rfl

/-- Nの段列に対応する共通束の更新列。 -/
def sharedStageU (n : ℕ) : CommonConcept := layerAddressEmbedding (layerU n)
def sharedStageV (n : ℕ) : CommonConcept := layerAddressEmbedding (layerV n)

theorem sharedStageU_update (n : ℕ) :
    sharedStageU (n + 1) = sharedStageU n ⊔ sharedStageV (n + 1) := by
  have hm : sharedStageU n ≤ sharedStageU (n + 1) :=
    layerAddressEmbedding.monotone (layerU_monotone (Nat.le_succ n))
  exact (sup_eq_right.mpr hm).symm

theorem sharedStageU_below_top (n : ℕ) : sharedStageU n < ⊤ := by
  have ht : layerAddressEmbedding (⊤ : Atom) = (⊤ : CommonConcept) := layerAddress_top
  rw [← ht]
  exact layerAddressEmbedding.strictMono (layerU_below_top n)

theorem sharedStageV_new (n : ℕ) : ¬ sharedStageV (n + 1) ≤ sharedStageU n := by
  exact fun hh => layerV_new n (layerAddressEmbedding.le_iff_le.mp hh)

/-- N自身の選択谷点・選択軌道。 -/
def SharedModelSignature.stageValleys (N : SharedModelSignature) :=
  chooseAllMeanFieldStageValleys N.stages

/-- 元H-stageの全切替前件をNの同じ段列・時刻で要求する。 -/
structure SharedStageSwitchInputs (N : SharedModelSignature) : Prop where
  preservation : SharedDataPreservation N
  center : ∀ n, (N.stages n).center = sharedStageRepresentation (sharedStageU n)
  address : ∀ n, N.stageAddress n = sharedStageU n
  gap : ∀ n, stageTheta (n + 1) <
    ((N.stages (n + 1)).gain * (N.stages (n + 1)).presenceGain *
      (N.stages (n + 1)).curvature - (N.stages (n + 1)).backgroundCurvature) / 2 *
      ‖(N.stageValleys (n + 1)).minimizer - (N.stageValleys n).minimizer‖ ^ 2
  segment : ∀ n, segment ℝ (N.stageValleys n).minimizer
    (N.stageValleys (n + 1)).minimizer ⊆
      Metric.closedBall (N.stages (n + 1)).center (N.stages (n + 1)).radius
  start : ∀ n, (N.stages n).startTime = N.legacy.stageTime n
  transition : ∀ n, (N.stages (n + 1)).initial =
    (N.stageValleys n).orbit (N.legacy.stageTime n + stageDuration n)
  recurrence : ∀ n, N.legacy.stageTime (n + 1) = N.legacy.stageTime n + stageDuration n
  diverges : ∀ B : ℝ, ∃ n, B < ∑ k ∈ Finset.range n, stageDuration k
  wait : ∀ n, max 0 (1 / (N.stageValleys n).decayRate *
    Real.log ((N.stageValleys n).decayAmplitude / errorTolerance n)) ≤ stageDuration n

/-- 全前件を同じNで読む23-B一般入口の適用。 -/
def SharedStageSwitchInputs.theorem23B {N : SharedModelSignature} (h : SharedStageSwitchInputs N) :=
  meanField_stage_specs_and_switches_give_condition23B_core
    sharedStageU sharedStageV sharedStageU_update sharedStageU_below_top sharedStageV_new
    N.stages sharedStageRepresentation sharedStageRepresentation_injective h.center
    stageTheta stageTheta_nonneg h.gap h.segment
    N.legacy.stageTime stageDuration errorTolerance h.start h.transition h.recurrence
    stageDuration_pos h.diverges errorTolerance_pos h.wait

/-- liftしても選択谷の減衰率を落とさない。 -/
theorem sharedLifted_decayRate (n : ℕ) : (liftedHStageValleyWitness n).decayRate =
    (hStageSequenceValleys n).decayRate := by
  norm_num [StageValleyWitness.decayRate, liftedHStageInput,
    MeanFieldStageInput.toStageValleySpec, hStageSequenceValleys, hStageSequenceStageSpecs,
    meanFieldStageSequence, hStageSequence, packageQuadraticStage,
    Tomabechi.Examples.Theorem23B.quadraticStage]

/-- 初期評価差と曲率余裕を保ち、距離評価係数も厳密一致する。 -/
theorem sharedLifted_decayAmplitude (n : ℕ) : (liftedHStageValleyWitness n).decayAmplitude =
    (hStageSequenceValleys n).decayAmplitude := by
  unfold StageValleyWitness.decayAmplitude
  rw [(liftedHStageValleyWitness n).initial_condition, (hStageSequenceValleys n).initial_condition,
    liftedHStageValleyWitness_minimizer_eq_lifted_scalar]
  change Real.sqrt _ = Real.sqrt _
  congr 1
  norm_num [liftedHStageInput, MeanFieldStageInput.toStageValleySpec,
    liftedStageMeanField, hStageSequenceStageSpecs, meanFieldStageSequence,
    hStageSequence, packageQuadraticStage, Tomabechi.Examples.Theorem23B.quadraticStage,
    liftedStageCenter_difference_norm]

set_option maxHeartbeats 1000000 in
/-- 具体共有署名は原H-stageの全切替前件を満たす。 -/
theorem sharedModel_stageSwitchInputs : SharedStageSwitchInputs sharedModel := by
  refine {
    preservation := sharedModel_preservation
    center := ?_
    address := ?_
    gap := ?_
    segment := ?_
    start := by intros; rfl
    transition := liftedHStageInput_selected_transition
    recurrence := stageTime_recurrence
    diverges := stageTime_unbounded
    wait := ?_ }
  · intro n
    rw [sharedStageU, sharedStageRepresentation_oldAddress]
    rfl
  · intro n
    rfl
  · intro n
    change stageTheta (n + 1) <
      ((liftedHStageInput (n + 1)).gain * (liftedHStageInput (n + 1)).presenceGain *
        (liftedHStageInput (n + 1)).curvature - (liftedHStageInput (n + 1)).backgroundCurvature) / 2 *
        ‖(liftedHStageValleyWitness (n + 1)).minimizer -
          (liftedHStageValleyWitness n).minimizer‖ ^ 2
    rw [liftedHStageValleyWitness_minimizer_eq_lifted_scalar,
      liftedHStageValleyWitness_minimizer_eq_lifted_scalar, liftedStageCenter_difference_norm]
    convert hStageSequence_gap_threshold n using 1 <;>
      norm_num [liftedHStageInput, hStageSequence, packageQuadraticStage,
        Tomabechi.Examples.Theorem23B.quadraticStage] <;> rfl
  · intro n
    change segment ℝ (liftedHStageValleyWitness n).minimizer
      (liftedHStageValleyWitness (n + 1)).minimizer ⊆
      Metric.closedBall (liftedHStageInput (n + 1)).center (liftedHStageInput (n + 1)).radius
    rw [liftedHStageValleyWitness_minimizer_eq_lifted_scalar,
      liftedHStageValleyWitness_minimizer_eq_lifted_scalar]
    apply (convex_closedBall (liftedHStageInput (n + 1)).center
      (liftedHStageInput (n + 1)).radius).segment_subset
    · change liftedStageCenter (hStageSequenceValleys n).minimizer ∈
        Metric.closedBall (liftedHStageInput (n + 1)).toStageValleySpec.center
          (liftedHStageInput (n + 1)).toStageValleySpec.radius
      rw [liftedHStageInput_center_eq_lifted_scalar, liftedHStageInput_radius_eq_scalar,
        liftedStageCenter_closedBall_mem_iff]
      exact hStageSequence_segment_in_next_ball n (left_mem_segment ℝ _ _)
    · change liftedStageCenter (hStageSequenceValleys (n + 1)).minimizer ∈
        Metric.closedBall (liftedHStageInput (n + 1)).toStageValleySpec.center
          (liftedHStageInput (n + 1)).toStageValleySpec.radius
      rw [liftedHStageInput_center_eq_lifted_scalar, liftedHStageInput_radius_eq_scalar,
        liftedStageCenter_closedBall_mem_iff]
      exact hStageSequence_segment_in_next_ball n (right_mem_segment ℝ _ _)
  · intro n
    change max 0 (1 / (liftedHStageValleyWitness n).decayRate *
      Real.log ((liftedHStageValleyWitness n).decayAmplitude / errorTolerance n)) ≤ stageDuration n
    rw [sharedLifted_decayRate, sharedLifted_decayAmplitude]
    exact hStageSequence_wait_bound n

#print axioms sharedModel_stageSwitchInputs

#print axioms SharedStageSwitchInputs.theorem23B
#print axioms sharedLifted_decayAmplitude
end Tomabechi.Consistency.R123
