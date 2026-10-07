import Tomabechi.Consistency.ConsistencyR123_SharedKernelInputs
import Tomabechi.Consistency.ConsistencyR3_Theorem20Entry

/-!
# 共有署名の定理20原文条件

基礎評価をN.baseから読む。Euclidean拡張は箱内でこの値に一致し、
箱外では同じbaselineをもつ二次式を使う。勾配・移動度・場の一致、
PL・距離誤差・一点Kのコンパクト性/不変性を原文条件入口へ供給する。
原文の象徴零集合は全域合意超平面。初期集合の一点Kとは区別する。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory Filter
open scoped Topology Gradient
open Tomabechi.Theorem1
open Tomabechi.Examples.Theorem2
open Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1Consensus

/-- Nに一度だけ格納したbaselineを保つEuclidean二次拡張。 -/
def SharedModelSignature.theorem20BaseExtension (N : SharedModelSignature)
    (x : C1EuclideanAgentState) : ℝ :=
  N.base.V0 0 0 + 8 * c1EuclideanSymbolDistance x

theorem theorem20BaseExtension_eq (N : SharedModelSignature) :
    N.theorem20BaseExtension = sharedT20V0 := by
  have hz : N.base.V0 0 0 = 1 := by
    rw [N.base.V0_eq_shared]
    dsimp [commonBaseV0]
    rw [potential_eq]
    norm_num [θ, γ]
  funext x
  exact congrArg (fun c => c + 8 * c1EuclideanSymbolDistance x) hz

/-- 共有署名を読む定理20の全解析入力。
flow自体は既存のEuclidean表現を使い、Nの一点adapterとの一致を必須化する。 -/
structure SharedTheorem20Inputs (N : SharedModelSignature) : Prop where
  base_on_box : ∀ x ∈ c1EuclideanBox,
    N.theorem20BaseExtension x = N.base.V0 (c1EuclideanCoordinates x) 0
  flow_projection : ∀ (x : C1EuclideanAgentState) (t₀ t : ℝ),
    c1EuclideanCoordinates (euclideanConsensusOptimalFlow.flow t₀ x t) =
      (N.pointAdapter (c1EuclideanCoordinates x) t₀).flow.flow t₀ (c1EuclideanCoordinates x) t
  field : ∀ y r,
    differentiableEuclideanConsensusOptimalFlow.vectorField y
      (differentiableEuclideanConsensusOptimalFlow.feedback y r) r =
      -(sharedT20Mobility r)
        (∇ (fun z => N.theorem20BaseExtension z - 1 * 1 * (1 * (-sharedT20D z))) y)
  gradientV : ∀ y, HasGradientAt N.theorem20BaseExtension
    ((8 : ℝ) • c1EuclideanSymbolDistanceGradient y) y
  gradientP : ∀ y : C1EuclideanAgentState, HasGradientAt (fun _ => (1 : ℝ)) 0 y
  gradientD : ∀ y, HasGradientAt sharedT20D (sharedT20GradD y) y
  distance_nonnegative : ∀ y, 0 ≤ sharedT20D y
  distance_zero : ∀ y, sharedT20D y = 0 ↔ y ∈ c1EuclideanSymbolTarget
  target_nonempty : c1EuclideanSymbolTarget.Nonempty
  target_closed : IsClosed c1EuclideanSymbolTarget
  slope : ∀ d : ℝ, HasDerivAt (fun z => -z) (-1) d
  inverse : ∀ r y, sharedT20InverseMobility r (sharedT20Mobility r y) = y
  symmetric : ∀ r y z, inner ℝ y (sharedT20Mobility r z) = inner ℝ (sharedT20Mobility r y) z
  coercive : ∀ r y, (1 / 4 : ℝ) * ‖y‖ ^ 2 ≤ inner ℝ y (sharedT20Mobility r y)
  couplingA : ∀ r y,
    -inner ℝ (sharedT20GradD y)
      (sharedT20Mobility r ((8 : ℝ) • c1EuclideanSymbolDistanceGradient y)) ≤
        (1 / 2 : ℝ) * inner ℝ (sharedT20GradD y) (sharedT20Mobility r (sharedT20GradD y))
  amplifiedB : (1 : ℝ) * 1 * 1 * (-(-1)) ≥ 1 / 2 + 1 / 2
  pl_identity : ∀ r y, 2 * sharedT20D y =
    inner ℝ (sharedT20GradD y) (sharedT20Mobility r (sharedT20GradD y))
  error : ∀ y, Metric.infDist y c1EuclideanSymbolTarget ≤ 2 * Real.sqrt (sharedT20D y)
  pointK_compact : ∀ x t₀, 0 ≤ t₀ → IsCompact (closedLoopReachableSet
    (policyFlowReachableAt euclideanConsensusOptimalFlow {x} t₀))
  pointK_invariant : ∀ x t₀, 0 ≤ t₀ →
    ∀ y ∈ closedLoopReachableSet (policyFlowReachableAt euclideanConsensusOptimalFlow {x} t₀),
      ∀ t, t₀ ≤ t → euclideanConsensusOptimalFlow.flow t₀ y t ∈
        closedLoopReachableSet (policyFlowReachableAt euclideanConsensusOptimalFlow {x} t₀)

/-- 共有基礎評価・一点flowを保存するNから、原文条件の全入力を構成する。 -/
theorem SharedKernelInputs.theorem20Inputs {N : SharedModelSignature}
    (h : SharedKernelInputs N) : SharedTheorem20Inputs N := by
  refine {
    base_on_box := ?_
    flow_projection := ?_
    field := ?_
    gradientV := ?_
    gradientP := fun y => hasGradientAt_const y 1
    gradientD := sharedT20D_hasGradientAt
    distance_nonnegative := fun y => mul_nonneg (by norm_num) (c1EuclideanSymbolDistance_nonneg y)
    distance_zero := ?_
    target_nonempty := c1EuclideanSymbolTarget_nonempty
    target_closed := c1EuclideanSymbolTarget_closed
    slope := hasDerivAt_neg
    inverse := ?_
    symmetric := ?_
    coercive := ?_
    couplingA := ?_
    amplifiedB := by norm_num
    pl_identity := ?_
    error := ?_
    pointK_compact := sharedT20_pointK_compact
    pointK_invariant := sharedT20_pointK_invariant }
  · intro x hx
    rw [theorem20BaseExtension_eq, N.base.V0_eq_shared]
    exact sharedT20V0_eq_common x hx
  · intro x t₀ t
    rw [h.preservation.point_flow, N.legacy.c1.selectedFlow_eq_rate3]
    simp [euclideanConsensusOptimalFlow, c1EuclideanCoordinates_toLp]
  · rw [theorem20BaseExtension_eq]
    exact sharedT20_field
  · rw [theorem20BaseExtension_eq]
    exact sharedT20V0_hasGradientAt
  · intro y
    rw [sharedT20D, mul_eq_zero]
    norm_num
    exact c1EuclideanSymbolDistance_zero_iff y
  · intro r y
    simp [sharedT20InverseMobility, sharedT20Mobility, smul_smul]
  · intro r y z
    simp [sharedT20Mobility, real_inner_smul_left, real_inner_smul_right, real_inner_comm]
  · intro r y
    simp [sharedT20Mobility, real_inner_smul_right, real_inner_self_eq_norm_sq]
  · intro r y
    change -inner ℝ ((4 : ℝ) • c1EuclideanSymbolDistanceGradient y)
        ((1 / 4 : ℝ) • ((8 : ℝ) • c1EuclideanSymbolDistanceGradient y)) ≤
      (1 / 2 : ℝ) * inner ℝ ((4 : ℝ) • c1EuclideanSymbolDistanceGradient y)
        ((1 / 4 : ℝ) • ((4 : ℝ) • c1EuclideanSymbolDistanceGradient y))
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      c1EuclideanSymbolGradient_inner_self]
    nlinarith [c1EuclideanSymbolDistance_nonneg y]
  · intro r y
    change 2 * (4 * c1EuclideanSymbolDistance y) =
      inner ℝ ((4 : ℝ) • c1EuclideanSymbolDistanceGradient y)
        ((1 / 4 : ℝ) • ((4 : ℝ) • c1EuclideanSymbolDistanceGradient y))
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      c1EuclideanSymbolGradient_inner_self]
    ring
  · intro y
    apply (c1EuclideanSymbolDistance_error_bound y).trans
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
    dsimp [sharedT20D]
    nlinarith [c1EuclideanSymbolDistance_nonneg y]

/-- このNの基礎評価を一般原文条件入口へ渡し、全一点初期対に適用する。
指数距離、距離残差、strict下降、逆計量恒等式は元の全結論に含まれる。
この射影では距離残差・距離評価・極限を読み出す。 -/
theorem SharedTheorem20Inputs.full_conclusion {N : SharedModelSignature}
    (h : SharedTheorem20Inputs N) (x : C1EuclideanAgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    SharedT20OriginalConclusions x t₀ := by
  let F := differentiableEuclideanConsensusOptimalFlow
  let gradD := fun r => sharedT20GradD (F.flow t₀ x r)
  let gradV := fun r => (8 : ℝ) • c1EuclideanSymbolDistanceGradient (F.flow t₀ x r)
  let g2 := fun r => 2 * sharedT20D (F.flow t₀ x r)
  have hr := Tomabechi.Theorem20.theorem20_policy_flow_original_condition_conclusion
    F sharedT20Mobility sharedT20InverseMobility N.theorem20BaseExtension (fun _ => 1)
    sharedT20D (fun d => -d) 1 1 (1 / 2) (1 / 2) 1 2 (1 / 4) t₀ ht₀ {x} x
    (Set.mem_singleton _) c1EuclideanSymbolTarget g2 (fun _ => -1)
    gradV (fun _ => 0) gradD h.field (h.pointK_compact x t₀ ht₀) (h.pointK_invariant x t₀ ht₀)
    (fun r _ => h.gradientV _) (fun r _ => h.gradientP _) (fun r _ => h.gradientD _)
    h.distance_nonnegative h.distance_zero h.target_nonempty h.target_closed
    (fun r _ => h.slope _) (fun r _ => h.inverse r) (fun r _ => h.symmetric r)
    (fun r _ => h.coercive r)
    (by
      intro r hr hreach hnot
      simpa [gradD, gradV] using h.couplingA r (F.flow t₀ x r))
    (by intros; exact h.amplifiedB)
    (by intro r hr; dsimp [g2]; norm_num)
    (fun r _ => h.pl_identity r _) (fun r _ => h.error _)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa only [SharedT20OriginalConclusions, one_mul, mul_one, neg_one_mul,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    F, g2, gradD, differentiableEuclideanConsensusOptimalFlow] using hr

/-- 全原文条件結論から距離残差・距離評価・極限を読み出す。 -/
theorem SharedTheorem20Inputs.point_conclusion {N : SharedModelSignature}
    (h : SharedTheorem20Inputs N) (x : C1EuclideanAgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t →
      sharedT20D (euclideanConsensusOptimalFlow.flow t₀ x t) ≤
        sharedT20D (euclideanConsensusOptimalFlow.flow t₀ x t₀) * Real.exp (-(t - t₀)) ∧
      Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x t) c1EuclideanSymbolTarget ≤
        2 * Real.sqrt (sharedT20D (euclideanConsensusOptimalFlow.flow t₀ x t₀)) *
          Real.exp (-(1 / 2 : ℝ) * (t - t₀))) ∧
      Tendsto (fun t => Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x t)
        c1EuclideanSymbolTarget) atTop (𝓝 0) := by
  have hr := h.full_conclusion x t₀ ht₀
  exact ⟨fun t ht => ⟨(hr.1 t ht).1, (hr.1 t ht).2.1⟩, hr.2⟩

#print axioms SharedKernelInputs.theorem20Inputs
#print axioms SharedTheorem20Inputs.full_conclusion
#print axioms SharedTheorem20Inputs.point_conclusion
end Tomabechi.Consistency.R123
