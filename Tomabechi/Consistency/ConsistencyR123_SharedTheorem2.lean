import Tomabechi.Consistency.ConsistencyR123_SharedStageConclusion

/-!
# 同じ署名Nの一点到達集合に対する定理2

箱内全初期点・非負開始時刻について、Nの実flowからAC・散逸・誤差境界を作る。
定理2の一般状態対入口から、全主体・全辺の残差と距離の定量評価および極限を保つ。
状態対残差系DAは二主体の具体モデルである。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory Filter
open scoped Topology
open Tomabechi.Theorem1 Tomabechi.Theorem2
open Tomabechi.Examples.Theorem2
open Tomabechi.Consistency.R2
open Tomabechi.Consistency.ConsistencyC1Consensus

/-- 二主体・二向き辺の接続性。主体・辺の量化を省略しない。 -/
theorem sharedResidual_connected : ∀ i j : Fin 2, Relation.ReflTransGen
    (fun a b => ∃ e, ((DA.endpoint e).1 = a ∧ (DA.endpoint e).2 = b) ∨
      ((DA.endpoint e).1 = b ∧ (DA.endpoint e).2 = a)) i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.single ⟨0, Or.inr ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.refl

def SharedModelSignature.theorem2PointTarget (N : SharedModelSignature)
    (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  DA.sharedTCZ (N.pointAdapter x t₀).reachable t

def SharedModelSignature.theorem2PointPotential (N : SharedModelSignature)
    (x : AgentState) (t₀ t : ℝ) : ℝ :=
  DA.potential ((N.pointAdapter x t₀).flow.flow t₀ x t) t

/-- 一点初期状態の実到達集合と、同じ実flowの解析前件。 -/
structure SharedTheorem2PointInputs (N : SharedModelSignature)
    (x : AgentState) (t₀ : ℝ) : Prop where
  reachable : (N.pointAdapter x t₀).reachable = closedLoopReachableSet
    (policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀)
  target_nonempty : ∀ t, (N.theorem2PointTarget x t₀ t).Nonempty
  potential_ac : ∀ T, t₀ ≤ T → AbsolutelyContinuousOnInterval
    (N.theorem2PointPotential x t₀) t₀ T
  decay_ae : ∀ T, t₀ ≤ T → ∀ᵐ t ∂volume.restrict (Set.Icc t₀ T),
    deriv (N.theorem2PointPotential x t₀) t ≤
      -2 * 3 * N.theorem2PointPotential x t₀ t
  error : ∀ t, t₀ ≤ t →
    Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t)
      (N.theorem2PointTarget x t₀ t) ^ 2 ≤ N.theorem2PointPotential x t₀ t

/-- 一点Kの目標は平均保存の合意点。実残差との誤差境界を各時刻で証明する。 -/
theorem SharedKernelInputs.theorem2Inputs {N : SharedModelSignature}
    (h : SharedKernelInputs N) (x : AgentState) (hx : x ∈ box)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) : SharedTheorem2PointInputs N x t₀ := by
  have hF : (N.pointAdapter x t₀).flow = consensusOptimalFlow :=
    (h.preservation.point_flow x t₀).trans N.legacy.c1.selectedFlow_eq_rate3
  have hK : (N.pointAdapter x t₀).reachable = pointReachableClosure x t₀ := by
    rw [h.preservation.point_reachable, hF]
    rfl
  have hZ : ∀ t, N.theorem2PointTarget x t₀ t = {agreementPoint x} := by
    intro t
    dsimp [SharedModelSignature.theorem2PointTarget]
    rw [hK]
    have hbox := pointReachableClosure_subset_box x hx t₀
    have heq : DA.sharedTCZ (pointReachableClosure x t₀) t = pointSharedTCZ x t₀ t := by
      ext y
      constructor
      · rintro ⟨hy, hp⟩
        exact ⟨hy, hbox hy, hp⟩
      · rintro ⟨hy, _, hp⟩
        exact ⟨hy, hp⟩
    rw [heq, pointSharedTCZ_eq_singleton x hx t₀ t ht₀]
  have hP : N.theorem2PointPotential x t₀ = consensusOptimalPotentialAlong x t₀ := by
    funext t
    dsimp [SharedModelSignature.theorem2PointPotential, consensusOptimalPotentialAlong]
    rw [hF]
  refine ⟨h.preservation.point_reachable x t₀, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hZ]
    exact Set.singleton_nonempty _
  · rw [hP]
    exact consensusOptimalPotentialAlong_ac x hx t₀
  · intro T hT
    rw [hP]
    by_cases heq : T = t₀
    · subst T
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (by simp : volume (Set.Icc t₀ t₀) = 0)] with t ht hmem
      exact False.elim (ht hmem)
    · exact consensusOptimalPotentialAlong_decay_ae x hx t₀ T
        (lt_of_le_of_ne hT (Ne.symm heq))
  · intro t ht
    rw [hZ, Metric.infDist_singleton, hP]
    rw [hF]
    have hd := consensusOptimalFlow_dist_agreementPoint_le x t₀ t
    have hs := (sq_le_sq₀ dist_nonneg (by positivity)).2 hd
    have hy := consensusOptimalFlow_forward_invariant x hx t₀ t ht
    rw [consensusOptimalPotentialAlong, sharedPotential_eq_coupling _ hy t,
      consensusOptimalFlow_gap]
    rw [mul_pow, sq_abs] at hs
    dsimp [halfDifference, γ] at *
    nlinarith [sq_nonneg ((x 0 - x 1) * Real.exp (-3 * (t - t₀)))]

/-- 一般定理2をNのflowと一点初期到達集合へ直接適用する。
距離率3、全主体・全辺の残差率6、表象一致、三種類の極限を返す。 -/
theorem SharedTheorem2PointInputs.conclusion {N : SharedModelSignature}
    {x : AgentState} {t₀ : ℝ} (h : SharedTheorem2PointInputs N x t₀)
    (ht₀ : 0 ≤ t₀) :
    StatePairResidualSystem.ReachableStatePairConclusion DA
      (policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀)
      ((N.pointAdapter x t₀).flow.flow t₀ x) sharedResidual_connected 3 1 t₀ := by
  apply DA.theorem2_reachable_state_pair_quantitative_conclusion
    _ _ sharedResidual_connected 3 1 t₀ (by norm_num) (by norm_num) ht₀
  · intro t ht
    exact mem_policyFlowReachableAt_of_flow (N.pointAdapter x t₀).flow {x}
      t₀ t x (Set.mem_singleton _) ht
  · intro t ht
    rw [← h.reachable]
    exact h.target_nonempty t
  · exact h.potential_ac
  · exact h.decay_ae
  · intro t ht
    rw [← h.reachable, one_mul]
    exact h.error t ht

#print axioms SharedKernelInputs.theorem2Inputs
#print axioms SharedTheorem2PointInputs.conclusion
end Tomabechi.Consistency.R123
