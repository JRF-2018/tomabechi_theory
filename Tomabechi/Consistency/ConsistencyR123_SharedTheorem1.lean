import Tomabechi.Consistency.ConsistencyR123_SharedTheorem2

/-!
# 同じNの基礎評価・一点Kによる定理1

閾値1の残差はDAの共有残差と一致する。
定理2と同じ実flow・一点K・AC・散逸・誤差境界を一般定理1へ渡す。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory Filter
open scoped Topology
open Tomabechi.Theorem1 Tomabechi.Examples.Theorem2
open Tomabechi.Consistency.ConsistencyC1Consensus

def SharedModelSignature.theorem1PointTarget (N : SharedModelSignature)
    (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  {y | y ∈ (N.pointAdapter x t₀).reachable ∧ N.base.V0 y t ≤ 1}

/-- 共有基礎評価の閾値1残差を、時間依存の共有残差へ同定する。 -/
theorem sharedBase_residual {N : SharedModelSignature} (y : AgentState) (t : ℝ) :
    residual1 (N.base.V0 y t) 1 = DA.potential y t := by
  rw [N.base.V0_eq_shared]
  have htime : DA.potential y t = DA.potential y 0 := by
    rw [potential_eq ![0, 0] y t, potential_eq ![0, 0] y 0]
  have hn := consensusPresence_potential_nonneg y 0
  simp [Tomabechi.Consistency.R3.commonBaseV0, residual1, htime,
    max_eq_left hn]

/-- Nの基礎評価のTCZと定理2の共有TCZは、同じ一点K上で一致する。 -/
theorem sharedBase_pointTargets {N : SharedModelSignature}
    (x : AgentState) (t₀ t : ℝ) :
    N.theorem1PointTarget x t₀ t = N.theorem2PointTarget x t₀ t := by
  ext y
  have hr := sharedBase_residual (N := N) y t
  have hn := consensusPresence_potential_nonneg y t
  change (y ∈ (N.pointAdapter x t₀).reachable ∧ N.base.V0 y t ≤ 1) ↔
    y ∈ (N.pointAdapter x t₀).reachable ∧ DA.potential y t = 0
  constructor
  · rintro ⟨hy, hv⟩
    refine ⟨hy, ?_⟩
    rw [← hr, residual1]
    exact max_eq_right (by linarith)
  · rintro ⟨hy, hp⟩
    refine ⟨hy, ?_⟩
    rw [hp] at hr
    have hle := le_max_left (N.base.V0 y t - 1) 0
    change max (N.base.V0 y t - 1) 0 = 0 at hr
    rw [hr] at hle
    linarith

/-- 定理2の解析入力を共有し、一般定理1の到達性・率3距離・極限を得る。
評価はN.baseそのもの、目標はNの実一点到達閉包上の閾値集合である。 -/
theorem SharedTheorem2PointInputs.theorem1 {N : SharedModelSignature}
    {x : AgentState} {t₀ : ℝ} (h : SharedTheorem2PointInputs N x t₀)
    (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t → (N.pointAdapter x t₀).flow.flow t₀ x t ∈
      (N.pointAdapter x t₀).reachable) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t)
        (N.theorem1PointTarget x t₀ t) ≤
      Real.sqrt (residual1 (N.base.V0 x t₀) 1) * Real.exp (-3 * (t - t₀))) ∧
    Tendsto (fun t => Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t)
      (N.theorem1PointTarget x t₀ t)) atTop (𝓝 0) := by
  have hR : (fun t => residual1
      (N.base.V0 ((N.pointAdapter x t₀).flow.flow t₀ x t) t) 1) =
      N.theorem2PointPotential x t₀ := by
    funext t
    exact sharedBase_residual _ t
  have hZ : ∀ t, {y | y ∈ closedLoopReachableSet
      (policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀) ∧ N.base.V0 y t ≤ 1} =
      N.theorem2PointTarget x t₀ t := by
    intro t
    rw [← h.reachable, ← sharedBase_pointTargets]
    rfl
  have hcore := theorem1_reachable_tcz_distance_tendsto_zero
    ((N.pointAdapter x t₀).flow.flow t₀ x)
    (policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀)
    N.base.V0 1 3 1 t₀
    (fun t ht => mem_policyFlowReachableAt_of_flow (N.pointAdapter x t₀).flow {x}
      t₀ t x (Set.mem_singleton _) ht)
    (fun T hT t ht => by rw [hZ]; exact h.target_nonempty t)
    (by rw [hR]; exact h.potential_ac)
    (by
      rw [hR]
      simp only [sharedBase_residual]
      exact h.decay_ae)
    (fun T hT t ht => by
      rw [hZ, one_mul]
      exact (h.error t ht.1).trans_eq (sharedBase_residual _ t).symm)
    ht₀ (by norm_num) (by norm_num)
  simpa only [← h.reachable, SharedModelSignature.theorem1PointTarget,
    (N.pointAdapter x t₀).flow.initial, one_mul] using hcore

#print axioms sharedBase_residual
#print axioms SharedTheorem2PointInputs.theorem1
end Tomabechi.Consistency.R123
