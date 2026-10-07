import Tomabechi.Consistency.ConsistencyC6_ModelSignature

/-!
# C6：モデルの実D/Eを読む27-A入力

実軌道、残差W、方策同値とfeedbackは同じMのフィールドから取る。
全状態上の自然ドリフト・基準入力の相殺を保持し、軌道上のa.e.相殺だけへ弱めない。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Examples.Theorem27Op
open Tomabechi.Theorem24_26
open MeasureTheory Filter
open scoped Topology

/-- MのDとEの実feedbackで得る頂点軌道。 -/
def ModelSignature.topPath (M : ModelSignature) (x : C6TopState) (T t : ℝ) : C6TopState :=
  M.data.trajectory ⊤ M.dynamics.feedback x T t

/-- O18/O19の27-A入力。場の具体化は固定し、全初期対に同じ場を使う。
これは全O条件の受入recordの頂点解析部分である。 -/
structure TopActuatorInputs (M : ModelSignature) (x : C6TopState) (T : ℝ)
    (hT : 0 ≤ T) : Prop where
  restart : ∀ (y : C6TopState) (a s t : ℝ), 0 ≤ a → a ≤ s → s ≤ t →
    M.topPath (M.topPath y a s) s t = M.topPath y a t
  ode : ∀ᵐ t ∂futureLebesgueMeasure T,
    HasDerivAt (M.topPath x T) (driftE x T t + GE (u0E x T t)) t
  state_gradient : ∀ t z, dWE x T t (0, z) = inner ℝ (gradWE x T t) z
  reference_cancellation : ∀ t,
    dWE x T t (1, 0) + inner ℝ (gradWE x T t) (driftE x T t + GE (utrE x T t)) = 0
  residual_locally_lipschitz : LocallyLipschitzOn (Set.Ici T)
    (fun s => M.dynamics.W (M.topPath x T s) s)
  w_derivative : ∀ᵐ t ∂futureLebesgueMeasure T,
    HasFDerivAt (fun p : ℝ × C6TopState => M.dynamics.W p.2 p.1)
      (dWE x T t) (t, M.topPath x T t)
  w_contDiff : ContDiff ℝ 1 (fun p : ℝ × C6TopState => M.dynamics.W p.2 p.1)
  adjoint_bound : ∀ᵐ t ∂futureLebesgueMeasure T, ∀ v : C6TopState,
    |inner ℝ (gradWE x T t) (GE v)| ≤ (2 * |x 0| + 1) * ‖v‖
  feedback_input : ∀ t (ht : T ≤ t), u0E x T t =
    (M.dynamics.policyEquiv M.dynamics.feedback).action
      ⟨⟨t, hT.trans ht⟩, M.topPath x T t⟩
  drift_field : ∀ t, T ≤ t → c6TopNaturalDrift (M.topPath x T t) = driftE x T t
  reference_field : ∀ t, T ≤ t → c6TopReferenceField (M.topPath x T t) = utrE x T t
  neighborhood_cancellation : ∀ y, inner ℝ (c6TopGradientField y)
    (c6TopNaturalDrift y + GE (c6TopReferenceField y)) = 0
  actuator_difference_measurable : Measurable (fun t : Set.Ici T =>
    GE (u0E x T t.1 - c6TopReferenceField (M.topPath x T t.1)))
  reference_allowed : ∀ y, c6TopReferenceField y ∈ c6TopAllowedInput
  actual_allowed : ∀ t, T ≤ t → u0E x T t ∈ c6TopAllowedInput

/-- commonModelの実D/Eフィールドが全初期対の27-A入力を満たす。
既存入力の実軌道との定義的一致を使い、解析証明を複製しない。 -/
theorem commonModel_topActuatorInputs (x : C6TopState) (T : ℝ) (hT : 0 ≤ T) :
    TopActuatorInputs commonModel x T hT := by
  have h := c6TopActuatorInputs x T hT
  exact {
    restart := h.restart
    ode := h.ode
    state_gradient := h.state_gradient
    reference_cancellation := h.reference_cancellation
    residual_locally_lipschitz := h.residual_locally_lipschitz
    w_derivative := h.w_derivative
    w_contDiff := h.w_contDiff
    adjoint_bound := h.adjoint_bound
    feedback_input := h.feedback_input
    drift_field := h.drift_field
    reference_field := h.reference_field
    neighborhood_cancellation := h.neighborhood_cancellation
    actuator_difference_measurable := h.actuator_difference_measurable
    reference_allowed := h.reference_allowed
    actual_allowed := h.actual_allowed }

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.commonModel_topActuatorInputs
