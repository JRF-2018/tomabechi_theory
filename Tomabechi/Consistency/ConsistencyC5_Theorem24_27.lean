import Tomabechi.Examples.Theorem27_AvijjaSankhara

/-!
# C5: 定理24→26→27の同時充足

既存の二層ベクトル源モデルを、定理24の費用データ、定理26の同じ最適
feedbackとLyapunov力学、定理27の入力・軌道条件として一つの証人に束ねる。
適用層は `Bool` の下位/上位で、上位状態は `ℝ²`。許容族は例が明示する
有界可測ゲイン feedback であり、全Borel feedback一般ではない。
-/

noncomputable section

namespace Tomabechi.Consistency.C5

open Tomabechi.Examples.Theorem27
open Tomabechi.Examples.Theorem26_27ControlClasses
open Tomabechi.Examples.Theorem27Op
open Tomabechi.Theorem24_26
open Tomabechi.Theorem24_26_Model

abbrev E2 := Tomabechi.Examples.Theorem27Op.E2

private def referenceDrift (y : E2) : E2 := (-mu * y 0) • e0
private def referenceLaw (y : E2) : E2 := (mu * y 0) • e0 + omg • e1
private def referenceGradient (y : E2) : E2 := (2 * y 0) • e0

/-- 27-Aの基準相殺は選んだ軌道だけでなく、全二次元状態上で成り立つ。
したがって任意の適用点の近傍にも同じ一つのドリフト・入力則を使える。 -/
theorem reference_cancellation_on_neighborhood (y : E2) :
    inner ℝ (referenceGradient y) (referenceDrift y + referenceLaw y) = 0 := by
  have heq : referenceDrift y + referenceLaw y = (omg : ℝ) • e1 := by
    ext i
    fin_cases i <;> simp [referenceDrift, referenceLaw, e0, e1,
      EuclideanSpace.single]
  rw [heq]
  norm_num [referenceGradient, e0, e1, PiLp.inner_apply, Fin.sum_univ_two]

/-- Wは全時間・全状態で滑らかな二次関数なので、各軌道点の近傍でC¹。 -/
theorem W_is_contDiff : ContDiff ℝ 1 (fun p : ℝ × E2 => W3 p.2 p.1) := by
  have h : (fun p : ℝ × E2 => W3 p.2 p.1) = fun p => (p.2 0) ^ 2 := by
    funext p
    simp [W3, lyapunov]
  rw [h]
  fun_prop

/-- 全状態上で定義した基準入力則を軌道に制限すると、27の指定基準入力に
一致する。よって近傍相殺とカーネルの軌道相殺は同じ入力則を使う。 -/
theorem reference_law_on_flow (x : E2) (T t : ℝ) :
    referenceLaw (flowE x T t) = utrE x T t := by
  ext i
  fin_cases i <;> simp [referenceLaw, utrE, flowE, e0, e1, mu, omg,
    EuclideanSpace.single]

theorem natural_drift_on_flow (x : E2) (T t : ℝ) :
    referenceDrift (flowE x T t) = driftE x T t := by
  change (-mu * (flowE x T t) 0) • e0 =
    (-mu * flow (x 0) T t) • e0
  rw [flowE_0]

abbrev Layer := SourceAbstraction
abbrev State := VectorSourceState
abbrev Policy := VectorSourcePolicy

/-- C5の同時証人。費用データと力学は既存の同じ値を参照する。27の全初期値
適用は直後の全称定理で供給する。 -/
structure Witness where
  data : Theorem24NonnegativeTimeData State Policy
  dynamics : Theorem26NonnegativeTimeDynamics vectorSourceData
    Tomabechi.Examples.Theorem27Op.E2
  data_eq : data = vectorSourceData
  dynamics_eq : dynamics = vectorSourceDynamics

/-- 24/26/27が同じデータで同時に成立するC5証人。 -/
def witness : Witness where
  data := vectorSourceData
  dynamics := vectorSourceDynamics
  data_eq := rfl
  dynamics_eq := rfl

theorem witness_nonempty : Nonempty Witness := ⟨witness⟩

theorem all_initial_pzs_classification (x : Tomabechi.Examples.Theorem27Op.E2)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ t, T ≤ t →
      (¬ FeedbackPZS (vectorSourceData.admissible (⊤ : Layer))
        futureLebesgueMeasure
        (fun π y a s => vectorSourceData.runningCost (⊤ : Layer) π
          (vectorSourceData.trajectory (⊤ : Layer) π y a s) s)
        (vectorSourceData.trajectory (⊤ : Layer) vectorSourceDynamics.feedback x T t) t ↔
        0 < Tomabechi.Theorem27.residualDescentRateAlong
          (fun s y => vectorSourceDynamics.W y s)
          (fun s => vectorSourceData.trajectory (⊤ : Layer)
            vectorSourceDynamics.feedback x T s) t) := by
  exact (vectorSourceData_theorem27_kernel x T hT).1

/-- 同じ全初期対で27の入力差下界も得る。右辺の指定入力と基準入力は
ともに `E2` の入力で、半径だけでなく位相座標を含む。 -/
theorem all_initial_action_gap (x : Tomabechi.Examples.Theorem27Op.E2)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ t ∂futureLebesgueMeasure T,
      (¬ FeedbackPZS (vectorSourceData.admissible (⊤ : Layer))
        futureLebesgueMeasure
        (fun π y a s => vectorSourceData.runningCost (⊤ : Layer) π
          (vectorSourceData.trajectory (⊤ : Layer) π y a s) s)
        (vectorSourceData.trajectory (⊤ : Layer) vectorSourceDynamics.feedback x T t) t →
        vectorSourceDynamics.rate * vectorSourceDynamics.c₁ *
          Metric.infDist
            (vectorSourceData.trajectory (⊤ : Layer) vectorSourceDynamics.feedback x T t)
            (theorem26ZeroValueTarget vectorSourceDynamics.alive
              (vectorSourceData.optimalValue (⊤ : Layer)) t) ^ 2 /
            (2 * |x 0| + 1) ≤
          ‖u0E x T t - vectorSourceReferenceInput x T t‖ ∧
          0 < ‖u0E x T t - vectorSourceReferenceInput x T t‖) := by
  exact (vectorSourceData_theorem27_kernel x T hT).2.2

/-- 最大可測ゲインに加えて零ゲインも許容され、方策集合は単点でない。 -/
theorem two_distinct_allowed_feedbacks :
    boundedGainFeedback ⟨0, by norm_num⟩ ≠
      boundedGainFeedback ⟨1 / 2, by norm_num⟩ :=
  bounded_gain_family_nontrivial

/-- 上位の零価値目標は半径座標が0の状態からなり、(1,0)は目標外。
したがって最高層の適用状態は空虚ではない。 -/
theorem active_state_outside_target (T : ℝ) :
    vec 1 0 ∉ ringE T := by
  rw [ringE_eq]
  simp [vec]

/-- 輪の上でも角度方向は回転する。半径が0でも状態全体を静止させない。 -/
theorem ring_has_nontrivial_tangential_motion (φ T s : ℝ) (hTs : T < s) :
    flowE (vec 0 φ) T s 1 ≠ φ := by
  rw [flowE_1]
  have hω : (0 : ℝ) < omg := by norm_num [omg]
  have hmove : omg * (s - T) ≠ 0 := ne_of_gt (mul_pos hω (by linarith))
  simpa [vec] using hmove

end Tomabechi.Consistency.C5
