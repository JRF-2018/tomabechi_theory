import Tomabechi.Consistency.ConsistencyR123_TopCompleteState

/-!
# 定理1・3・4の距離の結論を Euclid 距離で（H-flow″）

以前は 1–4 の**誤差境界**（二乗誤差の前件）を Euclid 距離で述べ直した（`SharedNormUnification`）。
ここでは、1・3・4 の**結論**（状態の TCZ への距離の指数評価と極限）も、定理20と同じ
Euclid 距離（`c1EuclideanCoordinates`）で述べる。`‖·‖∞ ≤ ‖·‖₂ ≤ √2‖·‖∞` から、
集合への距離は `infDist_E ≤ √2 · infDist_sup` なので、指数評価の定数は `√2` 倍になり、
極限は 0 のまま保たれる。

**範囲：** 定理2の結論は一般定理側の抽象記録（`ReachableStatePairConclusion`）で返るため
ここでは Euclid 版を作らない（定理1の結論が定理2の解析入力から導かれる形で含む）。
距離の比較は ℝ² の二つのノルムの同値性による。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Filter
open scoped Topology
open Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Theorem1

/-- 距離の評価の Euclid 版（定数 `√2` 倍）。 -/
theorem euclid_infDist_le_of_sup (A : Set AgentState) (y : AgentState) (b : ℝ)
    (h : Metric.infDist y A ≤ b) :
    Metric.infDist (c1EuclideanCoordinates.symm y) (c1EuclideanCoordinates.symm '' A) ≤
      Real.sqrt 2 * b := by
  have himg : c1EuclideanCoordinates.symm '' A =
      (fun a : AgentState => (WithLp.toLp 2 a : C1EuclideanAgentState)) '' A := by
    ext z; simp [c1EuclideanCoordinates_symm_eq]
  rw [himg, c1EuclideanCoordinates_symm_eq]
  exact (infDist_euclid_le A y).trans (by gcongr)

/-- 距離の極限 0 は Euclid 距離でも保たれる。 -/
theorem euclid_tendsto_of_sup (y : ℝ → AgentState) (A : ℝ → Set AgentState)
    (h : Tendsto (fun t => Metric.infDist (y t) (A t)) atTop (𝓝 0)) :
    Tendsto (fun t => Metric.infDist (c1EuclideanCoordinates.symm (y t))
      (c1EuclideanCoordinates.symm '' A t)) atTop (𝓝 0) := by
  refine squeeze_zero (fun t => Metric.infDist_nonneg) (fun t => ?_)
    (by simpa using h.const_mul (Real.sqrt 2))
  exact euclid_infDist_le_of_sup (A t) (y t) _ le_rfl

/-- 定理1・3・4 の距離の結論（指数評価と極限）を、定理20と同じ Euclid 距離で述べた版。 -/
structure SharedNormUnificationConclusions (N : SharedModelSignature) : Prop where
  theorem1 : ∀ x ∈ box, ∀ t₀ : ℝ, 0 ≤ t₀ →
    (∀ t, t₀ ≤ t →
      Metric.infDist
          (c1EuclideanCoordinates.symm ((N.pointAdapter x t₀).flow.flow t₀ x t))
          (c1EuclideanCoordinates.symm '' N.theorem1PointTarget x t₀ t) ≤
        Real.sqrt 2 * (Real.sqrt (residual1 (N.base.V0 x t₀) 1) * Real.exp (-3 * (t - t₀)))) ∧
    Tendsto (fun t => Metric.infDist
        (c1EuclideanCoordinates.symm ((N.pointAdapter x t₀).flow.flow t₀ x t))
        (c1EuclideanCoordinates.symm '' N.theorem1PointTarget x t₀ t)) atTop (𝓝 0)
  theorem3 : ∀ x ∈ box, x 0 + x 1 = 0 → ∀ t₀ : ℝ, 0 ≤ t₀ →
    (∀ t, t₀ ≤ t →
      Metric.infDist
          (c1EuclideanCoordinates.symm ((N.pointAdapter x t₀).flow.flow t₀ x t))
          (c1EuclideanCoordinates.symm '' N.theorem3PointTarget x t₀ t) ≤
        Real.sqrt 2 * (Real.sqrt (N.theorem3PointPotential x t₀ t₀) *
          Real.exp (-3 * (t - t₀)))) ∧
    Tendsto (fun t => Metric.infDist
        (c1EuclideanCoordinates.symm ((N.pointAdapter x t₀).flow.flow t₀ x t))
        (c1EuclideanCoordinates.symm '' N.theorem3PointTarget x t₀ t)) atTop (𝓝 0)
  theorem4 : ∀ x ∈ box, ∀ t₀ : ℝ, 0 ≤ t₀ →
    (∀ t, t₀ ≤ t →
      Metric.infDist
          (c1EuclideanCoordinates.symm ((N.pointAdapter x t₀).flow.flow t₀ x t))
          (c1EuclideanCoordinates.symm '' N.theorem4PointTarget x t₀ t) ≤
        Real.sqrt 2 * (Real.sqrt (N.theorem4PointResidual x t₀ t₀) *
          Real.exp (-(3 / 2 : ℝ) * (t - t₀)))) ∧
    Tendsto (fun t => Metric.infDist
        (c1EuclideanCoordinates.symm ((N.pointAdapter x t₀).flow.flow t₀ x t))
        (c1EuclideanCoordinates.symm '' N.theorem4PointTarget x t₀ t)) atTop (𝓝 0)

theorem SharedKernelInputs.normUnificationConclusions {N : SharedModelSignature}
    (h : SharedKernelInputs N) : SharedNormUnificationConclusions N where
  theorem1 := fun x hx t₀ ht₀ => by
    obtain ⟨_, hb, hl⟩ := (h.theorem2Inputs x hx t₀ ht₀).theorem1 ht₀
    exact ⟨fun t ht => euclid_infDist_le_of_sup _ _ _ (hb t ht),
      euclid_tendsto_of_sup _ _ hl⟩
  theorem3 := fun x hx hm t₀ ht₀ => by
    have hc := (h.theorem3Inputs x hx hm t₀ ht₀).conclusion ht₀
    exact ⟨fun t ht => euclid_infDist_le_of_sup _ _ _ (hc.state_bound t ht),
      euclid_tendsto_of_sup _ _ hc.state_limit⟩
  theorem4 := fun x hx t₀ ht₀ => by
    obtain ⟨_, hb, hl⟩ := (h.theorem4Inputs x hx t₀ ht₀).conclusion ht₀
    exact ⟨fun t ht => euclid_infDist_le_of_sup _ _ _ (hb t ht),
      euclid_tendsto_of_sup _ _ hl⟩

theorem sharedModel_normUnificationConclusions : SharedNormUnificationConclusions sharedModel :=
  sharedModel_kernelInputs.normUnificationConclusions

theorem final_consistency_v2_with_norm_conclusions :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N := by
  obtain ⟨N, h1, h2, h3, h4, h5⟩ := final_consistency_v2_with_top_complete_state
  exact ⟨N, h1, h2, h3, h4, h5,
    SharedKernelInputs.normUnificationConclusions h1.base.inputs.toSharedFullExperimentInputs.toSharedPointInputs.toSharedStageInputs.toSharedSCMAndExperimentInputs.toSharedR3And27Inputs.toSharedR3Inputs.toSharedKernelInputs⟩

#print axioms SharedKernelInputs.normUnificationConclusions
#print axioms final_consistency_v2_with_norm_conclusions
end Tomabechi.Consistency.R123
