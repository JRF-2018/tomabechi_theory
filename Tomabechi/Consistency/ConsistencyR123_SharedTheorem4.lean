import Tomabechi.Consistency.ConsistencyR123_SharedKernelInputs
import Tomabechi.Consistency.ConsistencyR3_Theorem4Entry

/-!
# 署名Nの基礎評価と一点Kによる定理4入力

目標・残差はN.baseとN.pointAdapterを読む。
共通評価・flow・到達閉包の保存式から全入力を構成し、一般入口へ直接渡す。
箱内全初期点・非負開始時刻を量化する。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory Filter
open scoped Topology
open Tomabechi.Theorem1 Tomabechi.Theorem4
open Tomabechi.Examples.Theorem2
open Tomabechi.Consistency.R3 Tomabechi.Consistency.R2
open Tomabechi.Consistency.ConsistencyC1Consensus

def SharedModelSignature.theorem4PointTarget (N : SharedModelSignature)
    (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  weightedTCZ (N.pointAdapter x t₀).reachable N.base.V0
    commonBasePresenceP commonBasePresenceQ 1 0 t

def SharedModelSignature.theorem4PointResidual (N : SharedModelSignature)
    (x : AgentState) (t₀ t : ℝ) : ℝ :=
  let y := (N.pointAdapter x t₀).flow.flow t₀ x t
  residual4 (N.base.V0 y t) (commonBasePresenceP y t) (commonBasePresenceQ y t) 1 0

/-- 同じNの一点K、共有基礎評価を使う定理4一般入口の全前件。 -/
structure SharedTheorem4PointInputs (N : SharedModelSignature)
    (x : AgentState) (t₀ : ℝ) : Prop where
  reachable : (N.pointAdapter x t₀).reachable =
    closedLoopReachableSet (policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀)
  target_nonempty : ∀ t, (N.theorem4PointTarget x t₀ t).Nonempty
  residual_ac : ∀ T, t₀ ≤ T →
    AbsolutelyContinuousOnInterval (N.theorem4PointResidual x t₀) t₀ T
  decay_ae : ∀ T, t₀ ≤ T →
    ∀ᵐ t ∂volume.restrict (Set.Icc t₀ T),
      deriv (N.theorem4PointResidual x t₀) t ≤
        -2 * (3 / 2 : ℝ) * N.theorem4PointResidual x t₀ t
  error : ∀ t, t₀ ≤ t →
    Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t)
        (N.theorem4PointTarget x t₀ t) ^ 2 ≤ 1 * N.theorem4PointResidual x t₀ t

/-- Nの保存式から、全箱初期点の共有評価によるAC/散逸/誤差を供給する。 -/
theorem SharedKernelInputs.theorem4Inputs {N : SharedModelSignature}
    (h : SharedKernelInputs N) (x : AgentState) (hx : x ∈ box)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) : SharedTheorem4PointInputs N x t₀ := by
  have hV : N.base.V0 = commonBaseV0 := by
    funext y t
    exact N.base.V0_eq_shared y t
  have hF : (N.pointAdapter x t₀).flow = consensusOptimalFlow :=
    (h.preservation.point_flow x t₀).trans N.legacy.c1.selectedFlow_eq_rate3
  have hK : (N.pointAdapter x t₀).reachable = pointReachableClosure x t₀ := by
    rw [h.preservation.point_reachable, hF]
    rfl
  have hZ : N.theorem4PointTarget x t₀ = sharedT4PointTarget x t₀ := by
    funext t
    dsimp [SharedModelSignature.theorem4PointTarget]
    rw [hK, hV]
    rfl
  have hR : N.theorem4PointResidual x t₀ = sharedT4Residual x t₀ := by
    funext t
    dsimp [SharedModelSignature.theorem4PointResidual]
    rw [hF, hV]
    rfl
  refine {
    reachable := h.preservation.point_reachable x t₀
    target_nonempty := ?_
    residual_ac := ?_
    decay_ae := ?_
    error := ?_ }
  · intro t
    rw [hZ, sharedT4PointTarget_eq x hx, pointSharedTCZ_eq_singleton x hx t₀ t ht₀]
    exact Set.singleton_nonempty _
  · rw [hR]
    exact sharedT4Residual_ac x hx t₀
  · intro T hT
    rw [hR]
    convert sharedT4Residual_decay_ae x hx t₀ T using 1 <;> norm_num
  · intro t ht
    rw [hF, hZ, hR]
    exact sharedT4PointTarget_error x hx t₀ t ht₀ ht

/-- Nの実評価と一点到達集合を、そのまま一般定理4へ渡す。 -/
theorem SharedTheorem4PointInputs.conclusion {N : SharedModelSignature}
    {x : AgentState} {t₀ : ℝ} (h : SharedTheorem4PointInputs N x t₀) (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t → (N.pointAdapter x t₀).flow.flow t₀ x t ∈ (N.pointAdapter x t₀).reachable) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t) (N.theorem4PointTarget x t₀ t) ≤
        Real.sqrt (N.theorem4PointResidual x t₀ t₀) *
          Real.exp (-(3 / 2 : ℝ) * (t - t₀))) ∧
    Tendsto (fun t => Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t)
      (N.theorem4PointTarget x t₀ t)) atTop (𝓝 0) := by
  have htarget : ∀ t,
      weightedTCZ (closedLoopReachableSet
        (policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀))
        N.base.V0 commonBasePresenceP commonBasePresenceQ 1 0 t =
          N.theorem4PointTarget x t₀ t := by
    intro t
    rw [← h.reachable]
    rfl
  have hcore := weighted_reachable_tcz_distance_tendsto_zero
    ((N.pointAdapter x t₀).flow.flow t₀ x)
    (policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀)
    N.base.V0 commonBasePresenceP commonBasePresenceQ 1 0 (3 / 2) 1 t₀
    (fun t ht => mem_policyFlowReachableAt_of_flow (N.pointAdapter x t₀).flow {x}
      t₀ t x (Set.mem_singleton _) ht)
    (fun T hT t ht => by rw [htarget]; exact h.target_nonempty t)
    h.residual_ac h.decay_ae
    (fun T hT t ht => by rw [htarget]; exact h.error t ht.1)
    ht₀ (by norm_num) (by norm_num)
  simpa only [← h.reachable, one_mul, SharedModelSignature.theorem4PointResidual,
    SharedModelSignature.theorem4PointTarget] using hcore

#print axioms SharedKernelInputs.theorem4Inputs
#print axioms SharedTheorem4PointInputs.conclusion

/-- この具体flowでは、一点目標の幾何から率3の距離評価も保つ。
一般入口から得た率3/2の結論に加える強いモデル内評価である。 -/
theorem SharedKernelInputs.theorem4_point_rate3 {N : SharedModelSignature}
    (h : SharedKernelInputs N) (x : AgentState) (hx : x ∈ box)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (t : ℝ) (ht : t₀ ≤ t) :
    Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t) (N.theorem4PointTarget x t₀ t) ≤
      Real.sqrt (N.theorem4PointResidual x t₀ t₀) * Real.exp (-3 * (t - t₀)) := by
  have hF : (N.pointAdapter x t₀).flow = consensusOptimalFlow :=
    (h.preservation.point_flow x t₀).trans N.legacy.c1.selectedFlow_eq_rate3
  have hK : (N.pointAdapter x t₀).reachable = pointReachableClosure x t₀ := by
    rw [h.preservation.point_reachable, hF]
    rfl
  have hV : N.base.V0 = commonBaseV0 := by
    funext y s
    exact N.base.V0_eq_shared y s
  have hZ : N.theorem4PointTarget x t₀ t = pointSharedTCZ x t₀ t := by
    dsimp [SharedModelSignature.theorem4PointTarget]
    rw [hK, hV]
    exact sharedT4PointTarget_eq x hx t₀ t
  have hR : N.theorem4PointResidual x t₀ t₀ = commonBaseTheorem4Effective x t₀ := by
    dsimp [SharedModelSignature.theorem4PointResidual]
    rw [hF, hV]
    change sharedT4Residual x t₀ t₀ = _
    rw [sharedT4Residual_eq_effective, consensusOptimalFlow.initial]
  rw [hF, hZ, hR]
  exact (consensusOptimalFlow_pointSharedTCZ_distance x hx t₀ t ht₀ ht).trans
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (by
        have htime : DA.potential x t₀ = DA.potential x 0 := by
          rw [potential_eq ![0, 0] x t₀, potential_eq ![0, 0] x 0]
        rw [htime]
        exact (commonBaseTheorem4_bounds x t₀).1))
      (Real.exp_pos _).le)

#print axioms SharedKernelInputs.theorem4_point_rate3
end Tomabechi.Consistency.R123
