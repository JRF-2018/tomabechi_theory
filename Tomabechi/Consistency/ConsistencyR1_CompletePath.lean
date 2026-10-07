import Tomabechi.Consistency.ConsistencyC6_ModelSignature
import Tomabechi.Consistency.ConsistencyR1_C3LiftedStage

/-!
# 完全状態pathと23-B切替pathの共有

同じ完全状態の認知射影は23-Bの正準切替軌道に一致する。
物理成分はA7の収支から回収し、認知状態の等長liftとは区別する。
対応の時間範囲は最初のstage以降の全有限時刻である。
-/

noncomputable section
namespace Tomabechi.Consistency.R1
open Tomabechi.Consistency.C6 Tomabechi.Consistency.C2 Tomabechi.Consistency.C3

/-- dwell閉区間では、選択谷軌道と正準切替軌道は一致する。 -/
theorem originalStageOrbit_eq_stitched (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (stageTime n) (stageTime n + stageDuration n)) :
    (hStageSequenceValleys n).orbit t = hStageSequenceStitchedTrajectory t := by
  exact ((hStageSequence_switching_certificate.stitched_dwell_and_endpoint_error n).1 ht).symm

/-- C2/A7完全状態pathの認知座標は、元23-Bの切替軌道そのものである。 -/
theorem commonModel_completePath_cognitive (t : ℝ) (ht : stageTime 0 ≤ t) :
    cognitiveCoordinate (commonModel.completePath t) = hStageSequenceStitchedTrajectory t := by
  obtain ⟨n, hmem⟩ := hStageSequence_switching_certificate.every_finite_time_in_a_dwell t ht
  have hstage : t ∈ Set.Ico (stageTime n) (stageTime (n + 1)) := by
    simpa only [stageTime_recurrence] using hmem
  change cognitiveCoordinate (c3A7StitchedTrajectory t) = _
  rw [c3A7StitchedTrajectory_eq_stage n t hstage, c3A7StageTrajectory_cognitive]
  have hstartEq : (valleySequence n).startTime = stageTime n := by
    change (hStageSequence n).startTime = _
    exact hStageSequence_start n
  have hspec : (hStageSequence n).toStageValleySpec =
      Tomabechi.Examples.Theorem23B.quadraticStage
        (representation (n + 1 : ℕ)) (valleySequence n).initial (stageTime n) := by
    calc
      _ = valleySequence n := hStageSequence_toStageValleySpec n
      _ = Tomabechi.Examples.Theorem23B.quadraticStage
          (representation (n + 1 : ℕ)) (valleySequence n).initial
          (valleySequence n).startTime := valleySequence_shape n
      _ = _ := by rw [hstartEq]
  have hsame : Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit
      (representation (n + 1 : ℕ)) (valleySequence n).initial (stageTime n) t =
      (hStageSequenceValleys n).orbit t := by
    change Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit
        (representation (n + 1 : ℕ)) (valleySequence n).initial (stageTime n) t =
      (Tomabechi.Theorem22.chooseStageValley ((hStageSequence n).toStageValleySpec)).orbit t
    rw [hspec]
    exact Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit_eq_witness_orbit
      _ _ _ _ hmem.1
  exact hsame.trans (originalStageOrbit_eq_stitched n t ⟨hmem.1, hmem.2.le⟩)

/-- 同じ完全状態の認知射影を等長に持ち上げると、lifted H-stage切替pathになる。 -/
theorem commonModel_completePath_cognitive_lift (t : ℝ) (ht : stageTime 0 ≤ t) :
    liftedStageCenter (cognitiveCoordinate (commonModel.completePath t)) =
      liftedHStageStitchedTrajectory t := by
  rw [commonModel_completePath_cognitive t ht]
  exact (liftedHStageStitchedTrajectory_eq_lifted_scalar t ht).symm

/-- A7収支は物理成分も固定する。独立時計を状態へ追加していない。 -/
theorem commonModel_completePath_physical (t : ℝ) (ht : stageTime 0 ≤ t) :
    physicalCoordinate (commonModel.completePath t) =
      3 * t - (hStageSequenceStitchedTrajectory t) ^ 2 := by
  have hbalance := c3A7StitchedTrajectory_entropyObserved t
  change physicalCoordinate (commonModel.completePath t) +
    (cognitiveCoordinate (commonModel.completePath t)) ^ 2 = 3 * t at hbalance
  rw [commonModel_completePath_cognitive t ht] at hbalance
  linarith

/-- 認知射影と収支を合わせると、完全状態の両成分を厳密に回収できる。 -/
theorem commonModel_completePath_recovered (t : ℝ) (ht : stageTime 0 ≤ t) :
    commonModel.completePath t =
      (hStageSequenceStitchedTrajectory t,
        3 * t - (hStageSequenceStitchedTrajectory t) ^ 2) := by
  apply Prod.ext
  · exact commonModel_completePath_cognitive t ht
  · exact commonModel_completePath_physical t ht

#print axioms commonModel_completePath_recovered
end Tomabechi.Consistency.R1
