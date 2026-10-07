import Tomabechi.Consistency.ConsistencyR123_NormUnificationConclusions

/-!
# 定理4の値域条件 (M6.1) を N の述語に入れる

原文 §6 は定理4に `V₀ ≥ 0`、`P ∈ [0,1]`、`Q ∈ [−1,1]`、`κ > 0` を課し、
`Ṽ = V₀ − κPQ ≥ −κ` を述べる。以前は `P = exp(−F) ∈ (0,1]`、`Q = 1`
の値域補題を共有基礎評価の側に置いた（`commonBasePresenceP_mem` など）が、
N の述語には入っていなかった。ここでは N 自身の基礎評価 `N.base.V0` について、
定理4の一般補題 `effectivePotential_lower_bound`（原文の下限 `Ṽ ≥ −κ`）を適用して、
値域条件を一つの受入型 `SharedTheorem4Ranges N` にまとめる。

**範囲：** `P = exp(−DA.potential)`、`Q = 1`、`κ = 1` の具体的な選択についての値域である。
`P` を別の関数に取り替えた場合の値域は主張しない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Theorem4

structure SharedTheorem4Ranges (N : SharedModelSignature) : Prop where
  V0_nonneg : ∀ (y : AgentState) (t : ℝ), 0 ≤ N.base.V0 y t
  P_range : ∀ (y : AgentState) (t : ℝ), 0 ≤ commonBasePresenceP y t ∧ commonBasePresenceP y t ≤ 1
  Q_range : ∀ (y : AgentState) (t : ℝ), -1 ≤ commonBasePresenceQ y t ∧ commonBasePresenceQ y t ≤ 1
  kappa_pos : (0 : ℝ) < 1
  effective_lower : ∀ (y : AgentState) (t : ℝ),
    -(1 : ℝ) ≤ effectivePotential (N.base.V0 y t) (commonBasePresenceP y t)
      (commonBasePresenceQ y t) 1

theorem SharedModelSignature.sharedTheorem4Ranges (N : SharedModelSignature) :
    SharedTheorem4Ranges N := by
  have hV : ∀ y t, 0 ≤ N.base.V0 y t := fun y t => by
    rw [N.base.V0_eq_shared]; exact (commonBaseV0_positive y t).le
  have hP : ∀ y t, 0 ≤ commonBasePresenceP y t ∧ commonBasePresenceP y t ≤ 1 :=
    fun y t => ⟨(commonBasePresenceP_mem y t).1.le, (commonBasePresenceP_mem y t).2⟩
  have hQ : ∀ y t, -1 ≤ commonBasePresenceQ y t ∧ commonBasePresenceQ y t ≤ 1 :=
    fun y t => (commonBasePresenceQ_mem y t)
  exact ⟨hV, hP, hQ, one_pos, fun y t =>
    effectivePotential_lower_bound _ _ _ 1 (hV y t) (hP y t).1 (hP y t).2 (hQ y t).1 (hQ y t).2
      one_pos⟩

theorem sharedModel_theorem4Ranges : SharedTheorem4Ranges sharedModel :=
  sharedModel.sharedTheorem4Ranges

theorem final_consistency_v2_with_theorem4_ranges :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N := by
  obtain ⟨N, h1, h2, h3, h4, h5, h6⟩ := final_consistency_v2_with_norm_conclusions
  exact ⟨N, h1, h2, h3, h4, h5, h6, N.sharedTheorem4Ranges⟩

#print axioms SharedModelSignature.sharedTheorem4Ranges
#print axioms final_consistency_v2_with_theorem4_ranges
end Tomabechi.Consistency.R123
