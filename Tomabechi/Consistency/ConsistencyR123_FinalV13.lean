import Tomabechi.Consistency.ConsistencyR123_PolicyCapacity

/-!
# 最終存在宣言 v13：四つの追加を同じ `N` で束ねる

v11（`SharedFinalConsistency`）と v12（定理3の `Φ₂ = DX`）に、次の四つの追加を同じ `sharedModel` で束ねる。

* 層制御系：16 の層の TCZ を生成する制御系（速度制御 `ẋ=u`、`LayerControlSound`）。**層別の独立した生成系を認める読み**で、
  N.data の有界ゲイン力学（中心に到達しない）から導いたものではない。
* 担体全体の自己過程：担体 `ball16` 全体を型にした自己表象・自己過程（`Shared25FullSelf`）。
* 現行評価の原文前件：現行評価 `commonV0X` の原文前件（有限地平 argmin、補題0の K 全点・再始動、`FullOriginalPremisesCurrent`）。
* 容量：問題×方策の容量（一元方策族、`SharedPolicyCapacityInputs`）。

あわせて、新しい生成族・表象・方策を導入した後も、24 の最適方策・実走行費、19 の joint、25 の介入不変性が
保たれることを `SharedFinalCrossChecksV13` で再照合する。

**範囲（報告基準）：** 「限定つきの同時充足」。層別の独立生成系、定理3は `X1` の零平均点、25-C4/C5 はモデル例、
容量の方策族は一元、距離は sup 距離（Euclid 版は別途）。原文を一つの共有制御系として読む強い認定ではない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.R1 Tomabechi.Consistency.R2
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.C6

/-- 新しい生成族・表象・方策を入れた後の再照合。 -/
structure SharedFinalCrossChecksV13 (N : SharedModelSignature) : Prop where
  /-- 24・13：有限層の実走行費は全域で `commonV0X`（制御系の導入で N.data は不変）。 -/
  layer_cost_current : ∀ (k : ℕ) (π : C1GainSignal) (y : AgentState) (t : ℝ),
    N.legacy.data.runningCost (some k) π y t = commonV0X y
  /-- 最適方策：`decode c true` は N.data の最適方策で、`false` と別の実制御方策。 -/
  optimal_policy_true : ∀ (c : CommonConcept) (x : fullCommonLayerState c) (T : ℝ),
    fullInformationDecoder c true = N.data.optimalPolicy c x T
  policies_distinct : ∀ c : CommonConcept,
    fullInformationDecoder c false ≠ fullInformationDecoder c true
  /-- 19：問題×方策の joint は情報法則で、固定 decoder の `capacityJoint` に一致。 -/
  joint_information : ∀ (d H : Bool) {a : CommonConcept} (q : CapProblemPolicy a),
    N.policyJoint d H q.2.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 = N.informationLaw q.1.1.1
  /-- 25：担体全体の自己過程でも介入不変性（条件25-A(2)）が全主体・全共通束点で成り立つ。 -/
  intervention_invariance : ∀ d a, (N.selfProcessFull d a).toLawModel.Condition25A2 ()
  /-- 25・16：自己表象の TCZ は正典 TCZ で、Ego は担体全体上の選択フィードバック。 -/
  tcz_canonical : ∀ h i, (N.selfRepFull h).TCZ i = N.canonicalLayerTCZ h i
  /-- 原文の目標非空条件を満たす定理3の初期点は零平均点に限る（モデル内の帰結）。 -/
  theorem3_zero_mean : ∀ x ∈ domainX1, ∀ t₀, 0 ≤ t₀ → ∀ t,
    ((target3X x t₀ t).Nonempty ↔ x 0 + x 1 = 0)

structure SharedFinalConsistencyV13 (N : SharedModelSignature) (sig : LayerControlSignature) :
    Prop where
  final : SharedFinalConsistency N
  theorem3 : SharedDomainTheorem3 N
  layer_control : LayerControlSound N sig
  full_self : Shared25FullSelf N
  current_premises : FullOriginalPremisesCurrent N
  policy_capacity : SharedPolicyCapacityInputs N
  cross_checks : SharedFinalCrossChecksV13 N

theorem sharedModel_finalCrossChecksV13 : SharedFinalCrossChecksV13 sharedModel where
  layer_cost_current := sharedModel_fullOriginalPremisesCurrent.v0_is_layer_cost
  optimal_policy_true := sharedModel_fixedCapacityInputs.policy_true_optimal
  policies_distinct := sharedModel_policyCapacityInputs.policy_values_distinct
  joint_information := sharedModel_policyCapacityInputs.joint_information
  intervention_invariance := sharedModel_shared25FullSelf.a2
  tcz_canonical := sharedModel_shared25FullSelf.tcz_canonical
  theorem3_zero_mean := sharedModel_fullOriginalPremisesCurrent.theorem3_target_nonempty

theorem sharedModel_finalConsistencyV13 :
    SharedFinalConsistencyV13 sharedModel velocityLayerControlSignature where
  final := sharedModel_finalConsistency
  theorem3 := sharedModel_domainTheorem3
  layer_control := sharedModel_layerControlSound
  full_self := sharedModel_shared25FullSelf
  current_premises := sharedModel_fullOriginalPremisesCurrent
  policy_capacity := sharedModel_policyCapacityInputs
  cross_checks := sharedModel_finalCrossChecksV13

/-- v13：限定つきの同時充足（層別の独立生成系、定理3は `X1` 零平均、容量の方策族は一元）。 -/
theorem final_consistency_v13 : ∃ (N : SharedModelSignature) (sig : LayerControlSignature),
    SharedFinalConsistencyV13 N sig :=
  ⟨sharedModel, velocityLayerControlSignature, sharedModel_finalConsistencyV13⟩

#print axioms sharedModel_finalCrossChecksV13
#print axioms final_consistency_v13

end Tomabechi.Consistency.R123
