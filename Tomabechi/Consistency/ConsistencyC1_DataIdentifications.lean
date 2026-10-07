import Tomabechi.Consistency.ConsistencyC1_O24

/-!
# C1 の既存データ間の同定

定理20の象徴データとEuclideanSpace上の入口、および定理1/2/4の
目標集合と型付きO24表現を、既存の具体定義のまま接続する。
同じ流れを持つことから評価関数の一致を推測せず、必要な等式を明示する。
これらの同定はC1全前提の充足証明ではない。
-/

noncomputable section

namespace Tomabechi.Consistency.ConsistencyC1DataIdentifications

open Tomabechi.Theorem1
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1O24
open Tomabechi.Examples.Theorem2

/-- Precisely the cross-context identities required by the C1 entries.
This record does not identify the Theorem 3 full-potential target with the
Theorem 1/4 diagonal target; those targets are different in this model. -/
structure C1Connections (t₀ : ℝ) (ht₀ : 0 ≤ t₀) : Prop where
  euclidean_flow_coordinates : ∀ (x : AgentState) (t : ℝ),
    c1EuclideanCoordinates
        (euclideanConsensusOptimalFlow.flow t₀ (WithLp.toLp 2 x) t) =
      consensusOptimalFlow.flow t₀ x t
  symbol_base_euclidean : ∀ (x : C1EuclideanAgentState) (t : ℝ),
    c1SymbolV0 (c1EuclideanCoordinates x) t =
      2 * c1EuclideanSymbolDistance x
  symbol_effective_euclidean : ∀ (x : C1EuclideanAgentState),
    c1SymbolEffectivePotential (c1EuclideanCoordinates x) =
      2 * c1EuclideanSymbolDistance x -
        1 * 1 * (1 * c1SymbolSlope (c1EuclideanSymbolDistance x))
  symbol_target_euclidean : ∀ (x : C1EuclideanAgentState),
    x ∈ c1EuclideanSymbolTarget ↔
      c1EuclideanCoordinates x ∈ c1SymbolTarget c1SymbolAddress
  o24_target_theorem1 : ∀ (t : ℝ),
    (optimalConsensusSelfEgoTCZAdapter t₀).TCZ t =
      consensusOptimalTheorem1Target t₀ t
  o24_target_theorem4 : ∀ (t : ℝ),
    (optimalConsensusSelfEgoTCZAdapter t₀).TCZ t =
      Tomabechi.Theorem4.weightedTCZ
        (closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀))
        consensusPresenceV0 consensusPresenceP consensusPresenceQ 1 1 t
  o24_target_symbol_restriction : ∀ (t : ℝ),
    (optimalConsensusSelfEgoTCZAdapter t₀).TCZ t =
      {x : AgentState | x ∈ box ∧ x ∈ c1SymbolTarget c1SymbolAddress}

/-- 象徴側の基礎評価 `2D` は座標移送後も定理20入口の基礎評価と一致する。 -/
theorem symbol_base_transport (x : C1EuclideanAgentState) (t : ℝ) :
    c1SymbolV0 (c1EuclideanCoordinates x) t =
      2 * c1EuclideanSymbolDistance x := by
  rw [c1SymbolV0, c1EuclideanSymbolDistance_eq_coordinates]

/-- 象徴側の実効評価と、定理20入口の `V₀=2D, P=q=κ=1, s=-D` は一致する。
ここで入口のPは増幅後の `Pσ=1` であり、増幅前の `P=0` と区別する。 -/
theorem symbol_effective_transport (x : C1EuclideanAgentState) :
    c1SymbolEffectivePotential (c1EuclideanCoordinates x) =
      2 * c1EuclideanSymbolDistance x -
        1 * 1 * (1 * c1SymbolSlope (c1EuclideanSymbolDistance x)) := by
  rw [c1SymbolEffectivePotential_selected _ 0,
    c1EuclideanSymbolDistance_eq_coordinates]
  unfold c1SymbolSlope
  ring

/-- 定理20の象徴目標は、座標移送によって同じ距離の零集合に対応する。 -/
theorem symbol_target_transport (x : C1EuclideanAgentState) :
    x ∈ c1EuclideanSymbolTarget ↔
      c1EuclideanCoordinates x ∈ c1SymbolTarget c1SymbolAddress := by
  rw [← c1EuclideanSymbolDistance_zero_iff,
    c1EuclideanSymbolDistance_eq_coordinates, c1SymbolDistance_zero_iff]

/-- O24のTCZと定理1の閉到達可能TCZは同じ集合である。 -/
theorem o24_target_eq_theorem1 (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    (optimalConsensusSelfEgoTCZAdapter t₀).TCZ t =
      consensusOptimalTheorem1Target t₀ t := by
  rw [c1OptimalConsensusTCZ_eq_shared t₀ t ht₀,
    consensusOptimalTheorem1Target_eq_shared t₀ t ht₀]

/-- O24のTCZと定理4の加重TCZは、同じ到達閉包上で一致する。 -/
theorem o24_target_eq_theorem4 (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    (optimalConsensusSelfEgoTCZAdapter t₀).TCZ t =
      Tomabechi.Theorem4.weightedTCZ
        (closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀))
        consensusPresenceV0 consensusPresenceP consensusPresenceQ 1 1 t := by
  rw [consensusOptimalFlow_reachable_closure_eq_box t₀ ht₀,
    consensusPresence_weightedTCZ_eq_shared,
    c1OptimalConsensusTCZ_eq_shared t₀ t ht₀]

/-- O24のTCZは象徴目標を箱へ制限した集合とも一致する。
定理20のambient目標そのものを箱内TCZと同一視することはしない。 -/
theorem o24_target_eq_restricted_symbol_target (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    (optimalConsensusSelfEgoTCZAdapter t₀).TCZ t =
      {x : AgentState | x ∈ box ∧ x ∈ c1SymbolTarget c1SymbolAddress} := by
  rw [c1SymbolTarget_box_eq_sharedTCZ,
    c1OptimalConsensusTCZ_eq_shared t₀ t ht₀]

/-- The concrete two-agent model satisfies the required C1 cross-context
identifications at every nonnegative start time. -/
theorem c1Connections_nonempty (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    Nonempty (C1Connections t₀ ht₀) := by
  refine ⟨{
    euclidean_flow_coordinates := ?_
    symbol_base_euclidean := symbol_base_transport
    symbol_effective_euclidean := symbol_effective_transport
    symbol_target_euclidean := symbol_target_transport
    o24_target_theorem1 := fun t => o24_target_eq_theorem1 t₀ t ht₀
    o24_target_theorem4 := fun t => o24_target_eq_theorem4 t₀ t ht₀
    o24_target_symbol_restriction := fun t =>
      o24_target_eq_restricted_symbol_target t₀ t ht₀
  }⟩
  intro x t
  simpa using euclideanConsensusOptimalFlow_coordinates
    (WithLp.toLp 2 x) t₀ t

end Tomabechi.Consistency.ConsistencyC1DataIdentifications
