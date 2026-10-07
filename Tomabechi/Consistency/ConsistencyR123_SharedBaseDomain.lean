import Tomabechi.Consistency.ConsistencyR123_Shared16LayerTCZ
import Tomabechi.Consistency.ConsistencyR123_SharedTheorem20

/-!
# 基礎評価の領域 X := box を明示

原文は 1・4・20・24 で同じ基礎評価 V₀ を状態領域 X 全体で使う。共有基礎評価
`N.base.V0 = 1 + DA.potential` は個人の閾値残差 `max((xᵢ)²−θ,0)` を含むので、
箱 `box = {x | ∀ i, |xᵢ| ≤ 1/4}` の外では、定理20のEuclid二次式拡張
`1 + 8·symbolDistance`（箱内で `1+2D` に一致）とは一致しない。

そこで **状態領域を X := box と明示する**。`SharedBaseDomain N` は次を課す。

* 箱は全方策のもとで前向き不変（有限層の実軌道）。
* 箱内で `N.base.V0` は定理1の評価、有限層の実走行費、定理20の箱内値 `1+2D` と一致する。
* 定理20のEuclid拡張は箱内で `N.base.V0` と一致し、箱の内部の各点の近傍で一致する
  （微分条件は内部の開集合で比較できる）。
* 箱の外では一致しない点が存在する（X を箱より広げると別の評価になることの記録）。

箱の外の評価の統一（案2）は行っていない。1/4/20/24 の量化は箱上のものとして読む。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Filter
open scoped Topology
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Examples.Theorem2

structure SharedBaseDomain (N : SharedModelSignature) : Prop where
  /-- 箱は有限層の任意のゲイン方策のもとで前向き不変。 -/
  forward_invariant : ∀ (k : ℕ) (u : C1GainSignal) (x : AgentState), x ∈ box →
    ∀ T t : ℝ, T ≤ t → N.legacy.data.trajectory (some k) u x T t ∈ box
  /-- 箱内で共有基礎評価は定理1の評価。 -/
  base_eq_theorem1 : ∀ x ∈ box, ∀ t, N.base.V0 x t = consensusV0 x t
  /-- 箱内で有限層の実走行費は共有基礎評価（全方策）。 -/
  layer_cost_eq_base : ∀ (k : ℕ) (u : C1GainSignal) (x : AgentState), x ∈ box → ∀ t,
    N.legacy.data.runningCost (some k) u x t = N.base.V0 x t
  /-- 箱内で定理20の値 `1 + 2D`。 -/
  theorem20_value : ∀ x ∈ box, N.base.V0 x 0 = 1 + 2 * commonBaseD x
  /-- Euclid拡張は箱内で共有基礎評価に一致し、箱の内部の各点の近傍で一致する。 -/
  extension_eq_on_box : ∀ z ∈ c1EuclideanBox,
    N.theorem20BaseExtension z = N.base.V0 (c1EuclideanCoordinates z) 0
  extension_eq_near_interior : ∀ z ∈ interior c1EuclideanBox,
    N.theorem20BaseExtension =ᶠ[𝓝 z] fun w => N.base.V0 (c1EuclideanCoordinates w) 0
  /-- 箱の外では一致しない点がある（領域を X := box と限る理由）。 -/
  outside_differs : ∃ z : C1EuclideanAgentState, z ∉ c1EuclideanBox ∧
    N.theorem20BaseExtension z ≠ N.base.V0 (c1EuclideanCoordinates z) 0

/-- 箱外の不一致の具体例：座標 (1,1)。拡張は `1`、共有基礎評価は `1+2·(1−1/10)`。 -/
theorem baseDomain_outside_example (N : SharedModelSignature) :
    ∃ z : C1EuclideanAgentState, z ∉ c1EuclideanBox ∧
      N.theorem20BaseExtension z ≠ N.base.V0 (c1EuclideanCoordinates z) 0 := by
  refine ⟨WithLp.toLp 2 ![1, 1], ?_, ?_⟩
  · intro hz
    have := hz 0
    norm_num [c1EuclideanCoordinates_toLp] at this
  · rw [theorem20BaseExtension_eq, N.base.V0_eq_shared]
    simp only [c1EuclideanCoordinates_toLp]
    dsimp [sharedT20V0, commonBaseV0]
    rw [potential_eq, c1EuclideanSymbolDistance_eq_coordinates]
    simp only [c1EuclideanCoordinates_toLp]
    norm_num [c1SymbolDistance, θ, γ]

theorem SharedModelSignature.sharedBaseDomain {N : SharedModelSignature}
    (hA : AdditionalConditions N.legacy) : SharedBaseDomain N where
  forward_invariant := fun k u x hx T t hT => by
    rw [hA.toCommonDataCouplings.finite_trajectory]
    exact controlledConsensusState_mem_box x hx T t u hT
  base_eq_theorem1 := fun x hx t => N.base.theorem1_matches x hx t
  layer_cost_eq_base := fun k u x hx t =>
    (hA.finite_c1_cost k u x hx t).trans (N.base.theorem1_matches x hx t).symm
  theorem20_value := fun x hx => N.base.theorem20_box_value x hx
  extension_eq_on_box := fun z hz => by
    rw [theorem20BaseExtension_eq, N.base.V0_eq_shared]
    exact sharedT20V0_eq_common z hz
  extension_eq_near_interior := fun z hz => by
    have hn : c1EuclideanBox ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
    filter_upwards [hn] with w hw
    rw [theorem20BaseExtension_eq, N.base.V0_eq_shared]
    exact sharedT20V0_eq_common w hw
  outside_differs := baseDomain_outside_example N

theorem sharedModel_baseDomain : SharedBaseDomain sharedModel :=
  SharedModelSignature.sharedBaseDomain sharedModel_explicitAdditionalConditions.legacy

/-- 先行する受入型に、基礎評価の領域（X := box）を加えた存在宣言。 -/
theorem final_consistency_with_base_domain :
    ∃ N : SharedModelSignature,
      FullOriginalPremises N ∧ ExplicitAdditionalConditions N ∧ SharedNondegenerate N ∧
        SharedCapacityInputs N ∧ Shared16Indexing N ∧ Shared16LayerTCZInputs N ∧
        SharedBaseDomain N :=
  ⟨sharedModel, sharedModel_fullOriginalPremises, sharedModel_explicitAdditionalConditions,
    sharedModel_nondegenerate, sharedModel_capacityInputs, sharedModel_shared16Indexing,
    sharedModel_shared16LayerTCZInputs, sharedModel_baseDomain⟩

#print axioms SharedModelSignature.sharedBaseDomain
#print axioms final_consistency_with_base_domain
end Tomabechi.Consistency.R123
