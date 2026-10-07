import Tomabechi.Consistency.ConsistencyC6_FiniteDataAdapter

/-!
# C6：凍結中心を保持する状態・制御・評価の同時保存

元の認知座標qを変えず、contextの中心cを明示して二主体状態を読む。
半差はc-qであり、有限層費用は1+16P_cとなる。段切替での中心変更は
contextの変更であり、この射影の値を完全状態の不連続と解釈しない。
-/

noncomputable section
namespace Tomabechi.Consistency.C6

open Tomabechi.Consistency.C2
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus
open MeasureTheory

/-- 保存平均mと凍結中心cから二主体を復元する。全域で定義するが、
定理1の適用には別途box所属が必要である。 -/
def centeredC1Projection (m c : ℝ) (z : CompleteState) : AgentState :=
  ![m + (c - cognitiveCoordinate z), m - (c - cognitiveCoordinate z)]

theorem centeredC1Projection_mean (m c : ℝ) (z : CompleteState) :
    meanState (centeredC1Projection m c z) = m := by
  simp [meanState, centeredC1Projection]

theorem centeredC1Projection_halfDifference (m c : ℝ) (z : CompleteState) :
    halfDifference (centeredC1Projection m c z) = c - cognitiveCoordinate z := by
  simp [halfDifference, centeredC1Projection]

/-- 同じ元状態での費用保存。box外でもDの実走行費の等式は成立する。 -/
theorem centeredC1Projection_runningCost
    (n : ℕ) (u : C1GainSignal) (m c t : ℝ) (z : CompleteState) :
    c6LayeredRunningCost (some n) u (centeredC1Projection m c z) t =
      1 + 16 * centeredQuadraticPotential c z := by
  change 1 + 8 * (halfDifference (centeredC1Projection m c z)) ^ 2 = _
  rw [centeredC1Projection_halfDifference]
  unfold centeredQuadraticPotential
  ring

/-- 中心固定の共通更新核から、全許容ゲインの実二主体軌道を回収する。
費用保存と同じ射影を使うので、中心一致だけの接続ではない。 -/
theorem centeredC1Projection_all_controls
    (m c T t E : ℝ) (z : CompleteState) (u : C1GainSignal) :
    centeredC1Projection m c
        (centeredGainEntropyStep c (c1AccumulatedGain u T t) E z) =
      c6LayeredTrajectory (some 0) u (centeredC1Projection m c z) T t := by
  change _ = controlledConsensusState (centeredC1Projection m c z) T u t
  rw [controlledConsensusState, centeredC1Projection_mean,
    centeredC1Projection_halfDifference]
  ext i
  fin_cases i <;>
    simp [centeredC1Projection, centeredGainEntropyStep, cognitiveCoordinate,
      c1ControlledOrbit] <;> ring

/-- 元C3の凍結段はゲイン1であり、C1の全可測[0,3]族に属する。
最大ゲイン選択とは同一視しない。 -/
def c6UnitGainSignal : C1GainSignal :=
  ⟨fun _ => 1, measurable_const, fun _ => by constructor <;> norm_num⟩

theorem c6UnitGainSignal_accumulated (T t : ℝ) :
    c1AccumulatedGain c6UnitGainSignal T t = t - T := by
  simp [c1AccumulatedGain, c6UnitGainSignal]

/-- 元C3段の時刻・状態を保持して、有限層の実制御軌道へ射影する。 -/
theorem c3A7Stage_centeredC1_trajectory (n : ℕ) (m t : ℝ) :
    centeredC1Projection m (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
        (c3A7StageTrajectory n t) =
      c6LayeredTrajectory (some 0) c6UnitGainSignal
        (centeredC1Projection m (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
          (c3A7StageInitial n)) (Tomabechi.Consistency.C3.stageTime n) t := by
  unfold c3A7StageTrajectory
  rw [← c6UnitGainSignal_accumulated]
  exact centeredC1Projection_all_controls _ _ _ _ _ _ _

/-- 同じ元C3段の実効評価を、同じ射影上のD費用として読む。
baseline1と係数16を保ち、評価の無条件な同一視を避ける。 -/
theorem c3A7Stage_centeredC1_runningCost (n k : ℕ) (m t : ℝ) :
    c6LayeredRunningCost (some k) c6UnitGainSignal
        (centeredC1Projection m (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
          (c3A7StageTrajectory n t)) t =
      1 + 16 * Tomabechi.Theorem22.stageEffectivePotential
        (Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec
        (cognitiveCoordinate (c3A7StageTrajectory n t)) := by
  rw [centeredC1Projection_runningCost, centeredQuadraticPotential_eq_C3_stage]

/-- 箱内条件を中心からの距離と保存平均で判定する。
射影の全域定義から、定理1の適用域を無条件に推論しない。 -/
theorem centeredC1Projection_mem_box_iff (m c : ℝ) (z : CompleteState) :
    centeredC1Projection m c z ∈ box ↔
      |m + (c - cognitiveCoordinate z)| ≤ 1 / 4 ∧
      |m - (c - cognitiveCoordinate z)| ≤ 1 / 4 := by
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

/-- C4履歴contextの完全状態。物理観測は元のq,y上に保持する。 -/
def c4CenteredCompleteTrajectory (h : Bool) (x y T t : ℝ) : CompleteState :=
  centeredGainEntropyStep
    (Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h)
    (t - T) (t - T) (x, y)

/-- C4全履歴・全初期状態で、同じ凍結中心射影がゲイン1の実軌道を回収する。 -/
theorem c4CenteredC1_trajectory (h : Bool) (m x y T t : ℝ) :
    centeredC1Projection m
        (Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h)
        (c4CenteredCompleteTrajectory h x y T t) =
      c6LayeredTrajectory (some 0) c6UnitGainSignal
        (centeredC1Projection m
          (Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h) (x, y)) T t := by
  unfold c4CenteredCompleteTrajectory
  rw [← c6UnitGainSignal_accumulated]
  exact centeredC1Projection_all_controls _ _ _ _ _ _ _

/-- 同じC4完全軌道の認知座標は元の履歴勾配流そのもの。 -/
theorem c4CenteredCompleteTrajectory_cognitive (h : Bool) (x y T t : ℝ) :
    cognitiveCoordinate (c4CenteredCompleteTrajectory h x y T t) =
      Tomabechi.Theorem16_25.theorem16_intervalGradientFlow h x (t - T) := rfl

/-- 同じC4元状態で、有限層D費用と元の履歴potentialを換算する。 -/
theorem c4CenteredC1_runningCost (h : Bool) (k : ℕ) (m t : ℝ)
    (z : CompleteState) :
    c6LayeredRunningCost (some k) c6UnitGainSignal
        (centeredC1Projection m
          (Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h) z) t =
      1 + 16 * Tomabechi.Theorem16_25.theorem16_intervalGradientPotential h
        (cognitiveCoordinate z) := by
  rw [centeredC1Projection_runningCost, centeredQuadraticPotential_eq_C4]

/-- C4のpotential閾値1/2は有限層の基礎費用閾値9に対応する。
C1の閾値1とは異なるcontextであり、到達集合条件は別途保持する。 -/
theorem c4CenteredC1_threshold_iff (h : Bool) (k : ℕ) (m t : ℝ)
    (z : CompleteState) :
    c6LayeredRunningCost (some k) c6UnitGainSignal
        (centeredC1Projection m
          (Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h) z) t ≤ 9 ↔
      Tomabechi.Theorem16_25.theorem16_intervalGradientPotential h
        (cognitiveCoordinate z) ≤ 1 / 2 := by
  rw [c4CenteredC1_runningCost]
  constructor <;> intro hbound <;> linarith

/-- C4正準TCZの到達条件を保った閾値換算。評価だけの部分集合をTCZと呼ばない。 -/
theorem c4CenteredC1_canonicalTCZ_iff (h : Bool) (k : ℕ) (m t : ℝ)
    (z : CompleteState) :
    cognitiveCoordinate z ∈
        Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4TCZ h ↔
      ∃ τ : Set.Icc (0 : ℝ) 1,
        cognitiveCoordinate z ∈
          Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Reachable h τ ∧
        c6LayeredRunningCost (some k) c6UnitGainSignal
          (centeredC1Projection m
            (Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h) z) t ≤ 9 := by
  simp only [Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4TCZ,
    Set.mem_ofPred_eq, c4CenteredC1_threshold_iff]

/-- 同じ完全状態を次の中心contextへ渡すと、半差だけが中心差だけ変わる。
完全状態自体の跳躍を仮定する式ではない。 -/
theorem centeredC1Projection_context_change (m c d : ℝ) (z : CompleteState) :
    halfDifference (centeredC1Projection m d z) =
      halfDifference (centeredC1Projection m c z) + (d - c) := by
  rw [centeredC1Projection_halfDifference, centeredC1Projection_halfDifference]
  ring

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.c3A7Stage_centeredC1_trajectory
#print axioms Tomabechi.Consistency.C6.c3A7Stage_centeredC1_runningCost
#print axioms Tomabechi.Consistency.C6.c4CenteredC1_trajectory
#print axioms Tomabechi.Consistency.C6.c4CenteredC1_threshold_iff
#print axioms Tomabechi.Consistency.C6.c4CenteredC1_canonicalTCZ_iff
