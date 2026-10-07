import Tomabechi.Consistency.ConsistencyR123_SharedStageInformation

/-!
# 同じ共有署名の23-B全結論と完全状態path

原H-stage入口の全切替結論を名前付きrecordへ保持し、Nのstitched pathが
同じ段列から得られるcanonical trajectoryと一致することを要求する。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open scoped Topology
open Tomabechi.Consistency.R1 Tomabechi.Consistency.C3
open Tomabechi.Theorem22 Tomabechi.Theorem23

/-- Nの同じ段列から定義する23-B TCZ。 -/
def SharedModelSignature.stageTCZ (N : SharedModelSignature) (n : ℕ) : Set LiftedStageState :=
  Tomabechi.Theorem23.stageTCZ
    (fun k x => stageEffectivePotential (N.stages k).toStageValleySpec x)
    (fun k => (N.stageValleys k).minimizer) stageTheta
    (fun k => Metric.closedBall (N.stages k).center (N.stages k).radius)
    (fun k => closure ((N.stageValleys k).orbit '' Set.Ici (N.stages k).startTime)) n

/-- 同じNの切替時刻・段列が選ぶcanonical trajectory。 -/
def SharedStageSwitchInputs.canonicalPath {N : SharedModelSignature} (h : SharedStageSwitchInputs N) :=
  canonicalStageTrajectory (meanFieldStageSequence N.stages)
    N.legacy.stageTime stageDuration stageDuration_pos h.recurrence h.diverges

/-- 原23-Bの全9群の結論。TCZ・軌道・時刻は同じNを読む。 -/
structure SharedStageSwitchConclusion (N : SharedModelSignature) (h : SharedStageSwitchInputs N) : Prop where
  layer_progress : (∀ n, sharedStageU n < ⊤) ∧ Monotone sharedStageU ∧
    (∀ n, sharedStageU n < sharedStageU (n + 1)) ∧
    (∀ B : ℝ, ∃ n, B < N.legacy.stageTime n) ∧
    (∀ n, N.legacy.stageTime n < N.legacy.stageTime (n + 1))
  adjacent_centers : ∀ n, (N.stages n).center ≠ (N.stages (n + 1)).center
  adjacent_valleys : ∀ n, 0 < ‖(N.stageValleys (n + 1)).minimizer - (N.stageValleys n).minimizer‖
  tcz_closed : ∀ n, IsClosed (N.stageTCZ n)
  tcz_distinct : ∀ n, N.stageTCZ (n + 1) ≠ N.stageTCZ n
  tcz_nonempty : ∀ n, (N.stageTCZ n).Nonempty
  dwell : ∀ n, Set.EqOn h.canonicalPath (N.stageValleys n).orbit
    (Set.Icc (N.legacy.stageTime n) (N.legacy.stageTime n + stageDuration n)) ∧
    dist (h.canonicalPath (N.legacy.stageTime n + stageDuration n))
      (N.stageValleys n).minimizer ≤ errorTolerance n
  coverage : ∀ t, N.legacy.stageTime 0 ≤ t →
    ∃ n, t ∈ Set.Ico (N.legacy.stageTime n) (N.legacy.stageTime n + stageDuration n)
  infinitely_many : ∀ T K, ∃ n, K ≤ n ∧ T < N.legacy.stageTime n

/-- 全結論を同じNの一般入口から取り出す。 -/
theorem SharedStageSwitchInputs.fullConclusion {N : SharedModelSignature} (h : SharedStageSwitchInputs N) :
    SharedStageSwitchConclusion N h := by
  have hc := h.theorem23B
  exact {
    layer_progress := hc.1
    adjacent_centers := hc.2.1
    adjacent_valleys := hc.2.2.1
    tcz_closed := hc.2.2.2.1
    tcz_distinct := hc.2.2.2.2.1
    tcz_nonempty := hc.2.2.2.2.2.1
    dwell := hc.2.2.2.2.2.2.1
    coverage := hc.2.2.2.2.2.2.2.1
    infinitely_many := hc.2.2.2.2.2.2.2.2 }

/-- 一般23-Bが選ぶpathをNの実stitched pathへ結ぶ。 -/
structure SharedStagePathCouplings (N : SharedModelSignature) (h : SharedStageSwitchInputs N) : Prop where
  lifted_path : ∀ t, N.legacy.stageTime 0 ≤ t → N.liftedStitchedPath t = h.canonicalPath t
  initial : ∀ n, (N.stages n).initial = liftedStageCenter (N.legacy.stages n).initial

/-- 具体共有署名のlifted pathは同じ段列のcanonical trajectoryである。 -/
theorem sharedModel_stagePathCouplings :
    SharedStagePathCouplings sharedModel sharedModel_stageSwitchInputs := by
  refine { lifted_path := ?_
           initial := by intros; rfl }
  intro t ht
  obtain ⟨n, hn⟩ := sharedModel_stageSwitchInputs.fullConclusion.coverage t ht
  have hd := (sharedModel_stageSwitchInputs.fullConclusion.dwell n).1 (Set.Ico_subset_Icc_self hn)
  have hp := liftedHStageStitchedTrajectory_eq_stageOrbit n t (Set.Ico_subset_Icc_self hn)
  exact hp.trans hd.symm

/-- Nの実pathも全dwell区間で同じ選択谷を追い、端点誤差を満たす。 -/
theorem SharedStagePathCouplings.dwell {N : SharedModelSignature}
    {h : SharedStageSwitchInputs N} (hp : SharedStagePathCouplings N h) (n : ℕ) :
    Set.EqOn N.liftedStitchedPath (N.stageValleys n).orbit
      (Set.Icc (N.legacy.stageTime n) (N.legacy.stageTime n + stageDuration n)) ∧
    dist (N.liftedStitchedPath (N.legacy.stageTime n + stageDuration n))
      (N.stageValleys n).minimizer ≤ errorTolerance n := by
  have hs := h.fullConclusion
  have htime : Monotone N.legacy.stageTime := (strictMono_nat_of_lt_succ hs.layer_progress.2.2.2.2).monotone
  constructor
  · intro t ht
    rw [hp.lifted_path t ((htime (Nat.zero_le n)).trans ht.1)]
    exact (hs.dwell n).1 ht
  · rw [hp.lifted_path _ ((htime (Nat.zero_le n)).trans (le_add_of_nonneg_right (stageDuration_pos n).le))]
    exact (hs.dwell n).2

/-- 同じ共有署名に情報入力・全切替入力・実path接続を追加する。 -/
structure SharedStageInputs (N : SharedModelSignature) : Prop extends SharedSCMAndExperimentInputs N where
  information : Nonempty (SharedStageInformationInputs N)
  switching : SharedStageSwitchInputs N
  path : SharedStagePathCouplings N switching

/-- 全stage入力の同時存在。最終原文監査とR2は別途必要。 -/
theorem shared_stage_model_exists : ∃ N : SharedModelSignature, SharedStageInputs N := by
  refine ⟨sharedModel, ?_⟩
  exact {
    toSharedSCMAndExperimentInputs := sharedModel_scmAndExperimentInputs
    information := ⟨sharedModel_stageInformationInputs⟩
    switching := sharedModel_stageSwitchInputs
    path := sharedModel_stagePathCouplings }

/-- Nの完全状態pathの認知liftも同じcanonical pathである。 -/
theorem SharedStageInputs.completePath_lift {N : SharedModelSignature} (h : SharedStageInputs N)
    (t : ℝ) (ht : N.legacy.stageTime 0 ≤ t) :
    liftedStageCenter (Tomabechi.Consistency.C2.cognitiveCoordinate (N.completePath t)) =
      h.switching.canonicalPath t := by
  have ht' : stageTime 0 ≤ t := by
    simpa only [h.toSharedSCMAndExperimentInputs.toSharedR3And27Inputs.toSharedR3Inputs.toSharedKernelInputs.additional.original_stage_times] using ht
  exact (h.switching.preservation.lifted_path t ht').trans (h.path.lifted_path t ht)

/-- 段初期値は同じ完全状態の段初期値の認知座標に一致する。 -/
theorem SharedStageInputs.initial_cognitive {N : SharedModelSignature} (h : SharedStageInputs N) (n : ℕ) :
    (N.stages n).initial = liftedStageCenter
      (Tomabechi.Consistency.C2.cognitiveCoordinate (N.legacy.stageInitial n)) := by
  rw [h.path.initial]
  exact congrArg liftedStageCenter
    (h.toSharedSCMAndExperimentInputs.toSharedR3And27Inputs.toSharedR3Inputs.toSharedKernelInputs.additional.stage_initial n).symm

/-- 支持/LUBの段番号は住所n+1であり、旧stage族の住所nとは別に明示する。 -/
def SharedModelSignature.stageAtSupportAddress (N : SharedModelSignature) (a : CommonConcept) :=
  N.stages (commonConceptInformationIndex a - 1)

/-- 同じNの正情報住所は対応する同じ段の平均場を選ぶ。 -/
theorem SharedStageInputs.stageAtSupportAddress {N : SharedModelSignature}
    (h : SharedStageInputs N) (n : ℕ) : N.stageAtSupportAddress (N.stageAddress n) = N.stages n := by
  unfold SharedModelSignature.stageAtSupportAddress
  rw [h.switching.address]
  change N.stages (commonConceptInformationIndex (layerAddressEmbedding ((n + 1 : ℕ) : Atom)) - 1) = _
  rw [commonConceptInformationIndex_old_positive]
  simp

#print axioms SharedStageInputs.completePath_lift
#print axioms SharedStageInputs.initial_cognitive
#print axioms SharedStageInputs.stageAtSupportAddress

#print axioms shared_stage_model_exists
#print axioms SharedStageSwitchInputs.fullConclusion
#print axioms SharedStagePathCouplings.dwell
end Tomabechi.Consistency.R123
