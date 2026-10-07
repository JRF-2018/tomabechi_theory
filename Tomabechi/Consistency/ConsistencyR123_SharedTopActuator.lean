import Tomabechi.Consistency.ConsistencyR123_SharedR3Inputs
import Tomabechi.Consistency.ConsistencyR123_TopGeometry

/-!
# 同じ共有署名の頂点27-A入力

軌道、評価、feedbackをN.data/N.dynamicsから読み、頂点の等長座標で
旧解析入力へ同定する。全初期状態・全非負開始時刻を保持する。
これは一般27入口へ渡す解析入力の保存段階である。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory Filter
open scoped Topology
open Tomabechi.Consistency.R1 Tomabechi.Consistency.C6
open Tomabechi.Examples.Theorem27Op
open Tomabechi.Theorem24_26

/-- 共有署名の実feedback軌道。 -/
def SharedModelSignature.topPath (N : SharedModelSignature)
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T t : ℝ) :=
  N.data.trajectory ⊤ N.dynamics.feedback x T t

private theorem trajectory_cast {I : Type*} {S P : I → Type*}
    (f : ∀ i, P i → S i → ℝ → ℝ → S i) {i j : I} (h : j = i)
    (π : P i) (x : S j) (a t : ℝ) :
    cast (congrArg S h) (f j (cast (congrArg P h.symm) π) x a t) =
      f i π (cast (congrArg S h) x) a t := by
  cases h
  rfl

/-- 任意Nの保存式から、実頂点軌道の座標が同じlegacyの軌道に一致する。 -/
theorem SharedDataPreservation.topPath_chart {N : SharedModelSignature}
    (h : SharedDataPreservation N) (x : fullCommonLayerState (⊤ : CommonConcept)) (T t : ℝ) :
    fullCommonTopStateEquiv (N.topPath x T t) =
      N.legacy.topPath (fullCommonTopStateEquiv x) T t := by
  unfold SharedModelSignature.topPath ModelSignature.topPath
  rw [h.trajectory, h.top_feedback]
  exact trajectory_cast N.legacy.data.trajectory fullCommonLayerIndex_top
    N.legacy.dynamics.feedback x T t

/-- 評価関数そのものを頂点座標へ移す。軌道上だけの等式に弱めない。 -/
theorem SharedDataPreservation.topW_chart {N : SharedModelSignature}
    (h : SharedDataPreservation N) (y : E2) (t : ℝ) :
    N.dynamics.W (fullCommonTopStateEquiv.symm y) t = N.legacy.dynamics.W y t := by
  rw [h.top_lyapunov, Equiv.apply_symm_apply]

/-- 実feedback入力の作用も同じ実軌道上で保存する。 -/
theorem SharedDataPreservation.topAction_chart {N : SharedModelSignature}
    (h : SharedDataPreservation N) (x : fullCommonLayerState (⊤ : CommonConcept))
    (T t : ℝ) (ht : 0 ≤ t) :
    (N.dynamics.policyEquiv N.dynamics.feedback).action (⟨t, ht⟩, N.topPath x T t) =
    (N.legacy.dynamics.policyEquiv N.legacy.dynamics.feedback).action
      (⟨t, ht⟩, N.legacy.topPath (fullCommonTopStateEquiv x) T t) := by
  rw [h.top_feedback_action, h.topPath_chart]

/-- Nの実データを頂点等長座標で読む27-A入力。
解析場は全状態で相殺し、実入力と基準入力の許容性も保持する。 -/
structure SharedTopActuatorInputs (N : SharedModelSignature)
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) : Prop where
  restart : ∀ y a s t, 0 ≤ a → a ≤ s → s ≤ t →
    N.topPath (N.topPath y a s) s t = N.topPath y a t
  ode : ∀ᵐ t ∂futureLebesgueMeasure T,
    HasDerivAt (fun s => fullCommonTopStateEquiv (N.topPath x T s))
      (driftE (fullCommonTopStateEquiv x) T t + GE (u0E (fullCommonTopStateEquiv x) T t)) t
  state_gradient : ∀ t z, dWE (fullCommonTopStateEquiv x) T t (0, z) =
    inner ℝ (gradWE (fullCommonTopStateEquiv x) T t) z
  reference_cancellation : ∀ t,
    dWE (fullCommonTopStateEquiv x) T t (1, 0) +
      inner ℝ (gradWE (fullCommonTopStateEquiv x) T t)
        (driftE (fullCommonTopStateEquiv x) T t + GE (utrE (fullCommonTopStateEquiv x) T t)) = 0
  residual_locally_lipschitz : LocallyLipschitzOn (Set.Ici T)
    (fun s => N.dynamics.W (N.topPath x T s) s)
  w_derivative : ∀ᵐ t ∂futureLebesgueMeasure T,
    HasFDerivAt (fun p : ℝ × E2 => N.dynamics.W (fullCommonTopStateEquiv.symm p.2) p.1)
      (dWE (fullCommonTopStateEquiv x) T t)
      (t, fullCommonTopStateEquiv (N.topPath x T t))
  w_contDiff : ContDiff ℝ 1
    (fun p : ℝ × E2 => N.dynamics.W (fullCommonTopStateEquiv.symm p.2) p.1)
  adjoint_bound : ∀ᵐ t ∂futureLebesgueMeasure T, ∀ v : E2,
    |inner ℝ (gradWE (fullCommonTopStateEquiv x) T t) (GE v)| ≤
      (2 * |(fullCommonTopStateEquiv x) 0| + 1) * ‖v‖
  feedback_input : ∀ t (ht : T ≤ t), u0E (fullCommonTopStateEquiv x) T t =
    (N.dynamics.policyEquiv N.dynamics.feedback).action
      (⟨t, hT.trans ht⟩, N.topPath x T t)
  drift_field : ∀ t, T ≤ t →
    c6TopNaturalDrift (fullCommonTopStateEquiv (N.topPath x T t)) =
      driftE (fullCommonTopStateEquiv x) T t
  reference_field : ∀ t, T ≤ t →
    c6TopReferenceField (fullCommonTopStateEquiv (N.topPath x T t)) =
      utrE (fullCommonTopStateEquiv x) T t
  neighborhood_cancellation : ∀ y, inner ℝ (c6TopGradientField y)
    (c6TopNaturalDrift y + GE (c6TopReferenceField y)) = 0
  actuator_difference_measurable : Measurable (fun t : Set.Ici T =>
    GE (u0E (fullCommonTopStateEquiv x) T t.1 -
      c6TopReferenceField (fullCommonTopStateEquiv (N.topPath x T t.1))))
  reference_allowed : ∀ y, c6TopReferenceField y ∈ c6TopAllowedInput
  actual_allowed : ∀ t, T ≤ t → u0E (fullCommonTopStateEquiv x) T t ∈ c6TopAllowedInput

/-- 旧27-A入力とNの保存式から、Nの実データを読む全入力を得る。 -/
theorem SharedKernelInputs.topActuatorInputs {N : SharedModelSignature}
    (h : SharedKernelInputs N) (x : fullCommonLayerState (⊤ : CommonConcept))
    (T : ℝ) (hT : 0 ≤ T) : SharedTopActuatorInputs N x T hT := by
  have hs := h.original.top_actuator (fullCommonTopStateEquiv x) T hT
  have hp := h.preservation.topPath_chart
  have hw := h.preservation.topW_chart
  have hwpath : ∀ y a s,
      N.dynamics.W (N.topPath y a s) s =
        N.legacy.dynamics.W (N.legacy.topPath (fullCommonTopStateEquiv y) a s) s := by
    intro y a s
    rw [h.preservation.top_lyapunov, hp]
  refine {
    restart := ?_
    ode := by simpa only [hp] using hs.ode
    state_gradient := hs.state_gradient
    reference_cancellation := hs.reference_cancellation
    residual_locally_lipschitz := by simpa only [hwpath] using hs.residual_locally_lipschitz
    w_derivative := by simpa only [hw, hp] using hs.w_derivative
    w_contDiff := by simpa only [hw] using hs.w_contDiff
    adjoint_bound := hs.adjoint_bound
    feedback_input := ?_
    drift_field := by simpa only [hp] using hs.drift_field
    reference_field := by simpa only [hp] using hs.reference_field
    neighborhood_cancellation := hs.neighborhood_cancellation
    actuator_difference_measurable := by simpa only [hp] using hs.actuator_difference_measurable
    reference_allowed := hs.reference_allowed
    actual_allowed := hs.actual_allowed }
  · intro y a s t ha has hst
    apply fullCommonTopStateEquiv.injective
    rw [hp, hp, hp]
    exact hs.restart (fullCommonTopStateEquiv y) a s t ha has hst
  · intro t ht
    rw [h.preservation.topAction_chart x T t (hT.trans ht)]
    exact hs.feedback_input t ht

#print axioms SharedKernelInputs.topActuatorInputs
end Tomabechi.Consistency.R123
