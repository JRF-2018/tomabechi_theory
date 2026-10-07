import Tomabechi.Consistency.ConsistencyR123_SharedTheorem4
import Tomabechi.Consistency.ConsistencyR123_SharedTheorem20

/-!
# 同じ共有署名の4/20解析入力と費用最適性

費用はN.baseとN.legacy.dataの同じ正有限層軌道から構成する。
この軌道はSharedDataPreservationで新束のN.dataにも同定される。
全可測許容ゲインとの比較を保ち、解析入口の入力と同時に存在量化する。
全stage/SCM/27等を含む最終受入は別途必要である。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.R3 Tomabechi.Consistency.C6
open Tomabechi.Consistency.R1 Tomabechi.Consistency.R2
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus

/-- Nの一点到達adapterが定めるK内で象徴目標を選ぶ。 -/
def SharedModelSignature.theorem20PointTarget (N : SharedModelSignature)
    (x : C1EuclideanAgentState) (t₀ : ℝ) : Set C1EuclideanAgentState :=
  (c1EuclideanCoordinates.symm '' (N.pointAdapter (c1EuclideanCoordinates x) t₀).reachable) ∩
    c1EuclideanSymbolTarget

theorem SharedKernelInputs.theorem20PointTarget_eq {N : SharedModelSignature}
    (h : SharedKernelInputs N) (x : C1EuclideanAgentState) (t₀ : ℝ) :
    N.theorem20PointTarget x t₀ = sharedT20PointTarget x t₀ := by
  unfold SharedModelSignature.theorem20PointTarget
  rw [h.preservation.point_reachable, h.preservation.point_flow,
    N.legacy.c1.selectedFlow_eq_rate3]
  rw [sharedT20PointTarget, sharedT20_pointK_eq_image]
  rfl

/-- 原文条件の一般入口に加え、同じ具体軌道の率3距離評価も保存する。 -/
theorem SharedKernelInputs.theorem20_point_rate3 {N : SharedModelSignature}
    (h : SharedKernelInputs N) (x : C1EuclideanAgentState) (hx : x ∈ c1EuclideanBox)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (t : ℝ) :
    Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x t) (N.theorem20PointTarget x t₀) ≤
      2 * Real.sqrt (sharedT20D x) * Real.exp (-3 * (t - t₀)) := by
  rw [h.theorem20PointTarget_eq, sharedT20PointTarget_infDist_eq x hx t₀ ht₀ t]
  have hroot : Real.sqrt (c1EuclideanSymbolDistance (euclideanConsensusOptimalFlow.flow t₀ x t)) =
      Real.sqrt (c1EuclideanSymbolDistance x) * Real.exp (-3 * (t - t₀)) := by
    rw [c1EuclideanSymbolDistance_optimalFlow_decay,
      Real.sqrt_mul (c1EuclideanSymbolDistance_nonneg x)]
    have hexp : Real.exp (-6 * (t - t₀)) = (Real.exp (-3 * (t - t₀))) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [hexp, Real.sqrt_sq (Real.exp_pos _).le]
  have hbound := c1EuclideanSymbolDistance_error_bound (euclideanConsensusOptimalFlow.flow t₀ x t)
  rw [hroot, ← mul_assoc] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
  dsimp [sharedT20D]
  nlinarith [c1EuclideanSymbolDistance_nonneg x]

/-- 同じ正有限層の実制御軌道で積分する、共有評価の定理4費用。 -/
def SharedModelSignature.theorem4FiniteCost (N : SharedModelSignature)
    (x : AgentState) (t₀ T : ℝ) (u : C1GainSignal) : ENNReal :=
  ∫⁻ s, ENNReal.ofReal
    (let y := N.legacy.data.trajectory (some 1) u x t₀ s
     Tomabechi.Theorem4.effectivePotential (N.base.V0 y s)
       (commonBasePresenceP y s) (commonBasePresenceQ y s) 1)
    ∂volume.restrict (Set.Icc t₀ (t₀ + T))

/-- 定理20の同じbaselineと勾配を保った実効評価を費用へ使う。 -/
def SharedModelSignature.theorem20FiniteCost (N : SharedModelSignature)
    (x : AgentState) (t₀ T : ℝ) (u : C1GainSignal) : ENNReal :=
  ∫⁻ s, ENNReal.ofReal
    (let y := N.legacy.data.trajectory (some 1) u x t₀ s
     N.base.V0 y 0 - 1 * 1 * commonBaseSlope y)
    ∂volume.restrict (Set.Icc t₀ (t₀ + T))

/-- Nの実軌道・実評価費用は証明済みの共有評価費用へ厳密に戻る。 -/
theorem SharedKernelInputs.theorem4FiniteCost_eq {N : SharedModelSignature}
    (h : SharedKernelInputs N) (x : AgentState) (t₀ T : ℝ) (u : C1GainSignal) :
    N.theorem4FiniteCost x t₀ T u = commonBaseTheorem4FiniteHorizonCost x t₀ T u := by
  unfold SharedModelSignature.theorem4FiniteCost commonBaseTheorem4FiniteHorizonCost
  apply lintegral_congr_ae
  filter_upwards with s
  rw [h.original.finite_control_solution]
  dsimp
  rw [N.base.V0_eq_shared]
  rfl

theorem SharedKernelInputs.theorem20FiniteCost_eq {N : SharedModelSignature}
    (h : SharedKernelInputs N) (x : AgentState) (t₀ T : ℝ) (u : C1GainSignal) :
    N.theorem20FiniteCost x t₀ T u = commonBaseTheorem20FiniteHorizonCost x t₀ T u := by
  unfold SharedModelSignature.theorem20FiniteCost commonBaseTheorem20FiniteHorizonCost
  apply lintegral_congr_ae
  filter_upwards with s
  rw [h.original.finite_control_solution]
  dsimp
  rw [N.base.V0_eq_shared]
  rfl

/-- R3の共有評価一般入口と全競合費用最適性を同じN上で受け入れる。 -/
structure SharedR3Inputs (N : SharedModelSignature) : Prop extends SharedKernelInputs N where
  theorem4 : ∀ x ∈ box, ∀ t₀, 0 ≤ t₀ → SharedTheorem4PointInputs N x t₀
  theorem4_rate3 : ∀ x ∈ box, ∀ t₀, 0 ≤ t₀ → ∀ t, t₀ ≤ t →
    Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t) (N.theorem4PointTarget x t₀ t) ≤
      Real.sqrt (N.theorem4PointResidual x t₀ t₀) * Real.exp (-3 * (t - t₀))
  theorem20 : SharedTheorem20Inputs N
  theorem20_point_target : ∀ x ∈ c1EuclideanBox, ∀ t₀, 0 ≤ t₀ →
    N.theorem20PointTarget x t₀ = {sharedT20Agreement x}
  theorem20_point_distance_transport : ∀ x ∈ c1EuclideanBox, ∀ t₀, 0 ≤ t₀ → ∀ t,
    Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x t) (N.theorem20PointTarget x t₀) =
      Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x t) c1EuclideanSymbolTarget
  theorem20_rate3 : ∀ x ∈ c1EuclideanBox, ∀ t₀, 0 ≤ t₀ → ∀ t,
    Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x t) (N.theorem20PointTarget x t₀) ≤
      2 * Real.sqrt (sharedT20D x) * Real.exp (-3 * (t - t₀))
  theorem4_argmin : ∀ x ∈ box, ∀ t₀, 0 ≤ t₀ → ∀ T, 0 < T → ∀ u : C1GainSignal,
    N.theorem4FiniteCost x t₀ T N.legacy.c1.selectedGain ≤ N.theorem4FiniteCost x t₀ T u
  theorem20_argmin : ∀ x ∈ box, ∀ t₀, 0 ≤ t₀ → ∀ T, 0 < T → ∀ u : C1GainSignal,
    N.theorem20FiniteCost x t₀ T N.legacy.c1.selectedGain ≤ N.theorem20FiniteCost x t₀ T u

/-- 新しい外部モデル前提を加えず、共有kernel証拠からR3入力を構成する。 -/
theorem SharedKernelInputs.r3Inputs {N : SharedModelSignature} (h : SharedKernelInputs N) :
    SharedR3Inputs N := by
  refine {
    toSharedKernelInputs := h
    theorem4 := h.theorem4Inputs
    theorem4_rate3 := h.theorem4_point_rate3
    theorem20 := h.theorem20Inputs
    theorem20_point_target := ?_
    theorem20_point_distance_transport := ?_
    theorem20_rate3 := h.theorem20_point_rate3
    theorem4_argmin := ?_
    theorem20_argmin := ?_ }
  · intro x hx t₀ ht₀
    rw [h.theorem20PointTarget_eq]
    exact sharedT20PointTarget_eq_singleton x hx t₀ ht₀
  · intro x hx t₀ ht₀ t
    rw [h.theorem20PointTarget_eq]
    exact sharedT20PointTarget_infDist_eq x hx t₀ ht₀ t
  · intro x hx t₀ ht₀ T hT u
    rw [h.theorem4FiniteCost_eq, h.theorem4FiniteCost_eq, N.legacy.c1.selectedGain_eq_maximum]
    exact commonBaseTheorem4_maxGain_argmin x hx t₀ T hT u
  · intro x hx t₀ ht₀ T hT u
    rw [h.theorem20FiniteCost_eq, h.theorem20FiniteCost_eq, N.legacy.c1.selectedGain_eq_maximum]
    exact commonBaseTheorem20_maxGain_argmin x hx t₀ T hT u

/-- 同じ具体共有署名がR3一般入口と実費用argminを同時に満たす。 -/
theorem sharedModel_r3Inputs : SharedR3Inputs sharedModel := sharedModel_kernelInputs.r3Inputs

/-- 原文全共有条件の最終存在認定とは区別した、R3付き共有入力の存在。 -/
theorem shared_r3_model_exists : ∃ N : SharedModelSignature, SharedR3Inputs N :=
  ⟨sharedModel, sharedModel_r3Inputs⟩

#print axioms shared_r3_model_exists
#print axioms SharedKernelInputs.r3Inputs
end Tomabechi.Consistency.R123
