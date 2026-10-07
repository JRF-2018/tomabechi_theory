import Tomabechi.Consistency.ConsistencyR123_DomainTheorems

/-!
# 統合ゲート：最終存在宣言 v11

正典 TCZ・共通状態領域・固定主体・履歴の容量の各版を、
**同じ一つの証人 `sharedModel`** で、互いの関係を証明したうえで束ねる。

**版の整理（同じ共有記号に複数の読みが併置されていた点の処理）：**

| 共有記号 | 現行版（置換後の読み） | 旧版（置換される読み・関係を証明して併置） |
|---|---|---|
| 定理16の担体 TCZ | 正典 TCZ `ball16`（一点 x₀、閉包なし、全許容制御） | 初期集合 `[0,1]` 版 `layerTCZ`、一点閉包版 `seg16` |
| 25 の三表現 | `selfRepCanonical`（`selfProcessCanonical`） | `legacy.selfRepresentation`、`selfRepOnePoint` |
| 19 の容量 | 固定主体・履歴 `fixedCapacity` | 主体・履歴を動かす `sharedCapacity` |
| 基礎評価 V₀ | 全域の `commonV0X`（1・2・4・20・24） | 箱の `N.base.V0 = 1+DA.potential`（θ=1/10） |
| 定理2の残差 | `DX`（θX=10、X3） | `DA`（θ=1/10、箱） |

`SharedVersionCoherence` は、旧版と現行版が**独立した局所証人の併置ではなく**、次の関係で結ばれていることを
同じ N で証明する：担体の包含鎖 `seg16 ⊆ [0,1] ⊆ ball16`、三つの層系の時刻1フィードバックと固定点の一致、
`N.base.V0 = commonV0X` と `DA.potential = DX.potential`（箱の上）、`P` の一致、容量の一致。

`SharedFinalCrossChecks` は再照合：型付き Self/Ego/TCZ、19/24/25 の主体・履歴、21/22/23-B の
枝・表象・実 path、26/27 の完全状態 chart、定理1・4 の Euclid 距離版と定理4の値域（`commonV0X` 版）。

**範囲：** 旧版の述語（`FullOriginalPremisesV2` 内の旧 TCZ・旧基礎評価に結んだ入口など）は削除せず、
`SharedFinalConsistency` の中で旧版として残す（既存の宣言は保持する方針）。置換とは、現行版が原文の読みの
代表で、旧版は現行版と証明済みの関係にある、という整理である。定理3は共通状態領域の対象外のまま。
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Theorem16_25 Tomabechi.Theorem2
open Tomabechi.Consistency.R1 Tomabechi.Consistency.R2 Tomabechi.Consistency.R3
open Tomabechi.Consistency.C6 Tomabechi.Consistency.C2
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Examples.Theorem2

/-- 箱の上で `DA.potential = DX.potential`（個人閾値の項が両方で消える）。 -/
theorem DA_potential_eq_DX_on_box {x : AgentState} (hx : x ∈ box) (t : ℝ) :
    DA.potential x t = DX.potential x t := by
  rw [potential_eq ![0, 0] x t, DX_potential_eq]
  have e0 : (![0, 0] : Fin 2 → ℝ) 0 = 0 := rfl
  have e1 : (![0, 0] : Fin 2 → ℝ) 1 = 0 := rfl
  have h0 : (x 0 - (![0, 0] : Fin 2 → ℝ) 0) ^ 2 - Tomabechi.Examples.Theorem2.θ ≤ 0 := by
    have := abs_le.mp (hx 0); rw [e0]; simp only [sub_zero, Tomabechi.Examples.Theorem2.θ]
    nlinarith [this.1, this.2]
  have h1 : (x 1 - (![0, 0] : Fin 2 → ℝ) 1) ^ 2 - Tomabechi.Examples.Theorem2.θ ≤ 0 := by
    have := abs_le.mp (hx 1); rw [e1]; simp only [sub_zero, Tomabechi.Examples.Theorem2.θ]
    nlinarith [this.1, this.2]
  have g0 : x 0 ^ 2 - θX ≤ 0 := by
    have := abs_le.mp (hx 0); unfold θX; nlinarith [this.1, this.2]
  have g1 : x 1 ^ 2 - θX ≤ 0 := by
    have := abs_le.mp (hx 1); unfold θX; nlinarith [this.1, this.2]
  rw [max_eq_right h0, max_eq_right h1, max_eq_right g0, max_eq_right g1]

/-- 箱の上で、旧 `P = exp(−DA.potential)` と新 `P = exp(−F)` は一致。 -/
theorem commonBasePresenceP_eq_on_box {x : AgentState} (hx : x ∈ box) (t : ℝ) :
    commonBasePresenceP x t = Real.exp (-(Fg x)) := by
  have h := DA_potential_eq_DX_on_box hx 0
  have h2 := DX_potential_eq_on_X3 (x := x) (fun i => (hx i).trans (by norm_num)) 0
  unfold commonBasePresenceP Fg
  rw [h, h2]

theorem Icc_zero_one_subset_ball16 (h : Bool) : Set.Icc (0 : ℝ) 1 ⊆ ball16 h := by
  intro y hy
  cases h <;> simp only [ball16, theorem16_intervalGradientCenter, Bool.false_eq_true, if_false,
    if_true] <;> constructor <;> linarith [hy.1, hy.2]

/-- 版の関係：旧版と現行版は独立な局所証人の併置ではなく、証明済みの関係で結ばれる。 -/
structure SharedVersionCoherence (N : SharedModelSignature) : Prop where
  /-- TCZ の包含鎖：一点閉包版 ⊆ 初期集合版 ⊆ 正典版。 -/
  tcz_chain : ∀ (h : Bool) (i : ℕ),
    N.layerTCZ1 h i ⊆ N.layerTCZ h i ∧ N.layerTCZ h i ⊆ N.canonicalLayerTCZ h i
  /-- 旧自己表象の TCZ は初期集合版。 -/
  legacy_tcz_is_initial_set_version : ∀ (h : Bool) (i : ℕ),
    (N.legacy.selfRepresentation h).TCZ i = N.layerTCZ h i
  /-- 三つの層系の時刻1フィードバックは、重なる点で同じ勾配流。 -/
  feedback_agree : ∀ (h : Bool) (i : ℕ) (x : ℝ) (hx : x ∈ seg16 h),
    (feedback16OnePoint h i ⟨x, hx⟩ : ℝ) = feedback16Canonical h i ⟨x, Icc_zero_one_subset_ball16 h
      (seg16_subset_unit h hx)⟩ ∧
    (theorem16_intervalGradientFlowFeedback h i ⟨x, seg16_subset_unit h hx⟩ : ℝ) =
      feedback16Canonical h i ⟨x, Icc_zero_one_subset_ball16 h (seg16_subset_unit h hx)⟩
  /-- 三つの層系の不動点は同じ（全座標が履歴の中心）。 -/
  fixed_points_same : ∀ (h : Bool) (x : IL1 h) (y : ILc h),
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes h x = x →
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes h y = y →
    x.1 = y.1
  /-- 基礎評価：旧 `N.base.V0` は箱の上で `commonV0X`、旧 `P` も箱の上で新 `P`、
  `DA.potential = DX.potential`。 -/
  base_eq_on_box : ∀ x ∈ box, ∀ t, N.base.V0 x t = commonV0X x
  presence_eq_on_box : ∀ x ∈ box, ∀ t, commonBasePresenceP x t = Real.exp (-(Fg x))
  residual_eq_on_box : ∀ x ∈ box, ∀ t, DA.potential x t = DX.potential x t
  /-- 21 の実例の背景は、球の上で `commonV0X`。 -/
  v0_instance_eq : ∀ z : C1EuclideanAgentState, ‖z‖ ≤ 1 / 8 → v0Background z = commonV0XE z
  /-- 容量：固定した `(d,H)` の容量は、主体・履歴を動かす容量と一致。 -/
  capacity_same : ∀ (d H : Bool) (a : CommonConcept), N.fixedCapacity d H a = N.sharedCapacity a

theorem sharedModel_versionCoherence : SharedVersionCoherence sharedModel where
  tcz_chain := fun h i => by
    have hp := sharedModel_preservation
    have hA := sharedModel_explicitAdditionalConditions.legacy
    rw [sharedModel.layerTCZ1_eq_seg16 hp hA, SharedModelSignature.layerTCZ_eq_carrier hp hA,
      SharedModelSignature.canonicalLayerTCZ_eq hp hA]
    exact ⟨seg16_subset_unit h, Icc_zero_one_subset_ball16 h⟩
  legacy_tcz_is_initial_set_version := sharedModel_shared16LayerTCZInputs.tcz_eq
  feedback_agree := fun h i x hx => ⟨rfl, rfl⟩
  fixed_points_same := fun h x y hx hy => by
    funext i
    rw [fixedPoint1_coordinate h x hx i, fixedPointC_coordinate h y hy i]
  base_eq_on_box := fun x hx t => sharedModel.base_eq_commonV0X_on_box hx t
  presence_eq_on_box := fun x hx t => commonBasePresenceP_eq_on_box hx t
  residual_eq_on_box := fun x hx t => DA_potential_eq_DX_on_box hx t
  v0_instance_eq := fun z hz => by
    rw [v0Background_eq hz, commonV0XE_eq_theorem20_extension]
    rfl
  capacity_same := fun d H a => sharedModel_preservation.fixedCapacity_eq_shared d H a

/-! ## 再照合 -/

/-- 定理1・4 の Euclid 距離版（`commonV0X`、全初期点）と、定理4の値域（`commonV0X` 版）。 -/
structure SharedFinalCrossChecks (N : SharedModelSignature) : Prop where
  /-- 型付き Self・Ego は旧表象のもの、TCZ は正典 TCZ。 -/
  typed_Self_Ego : ∀ h : Bool, (N.selfRepCanonical h).Self = (N.legacy.selfRepresentation h).Self ∧
    (N.selfRepCanonical h).Ego = (N.legacy.selfRepresentation h).Ego
  typed_TCZ : ∀ (h : Bool) (i : ℕ), (N.selfRepCanonical h).TCZ i = N.canonicalLayerTCZ h i
  /-- 21/22/23-B：枝・表象（中心・住所）・実 path・段の接続。 -/
  stage_switch : SharedStageSwitchInputs N
  stage_address_16 : ∀ n : ℕ, N.stageAddress n = index16 (n + 1)
  stage_information : ∀ n : ℕ, N.informationLaw (N.stageAddress n) = N.legacy.informationLaw (n + 1)
  real_path_cognitive : ∀ t, Tomabechi.Consistency.C3.stageTime 0 ≤ t →
    cognitiveCoordinate (N.completePath t) = N.scalarStitchedPath t
  real_path_physical : ∀ t, Tomabechi.Consistency.C3.stageTime 0 ≤ t →
    physicalCoordinate (N.completePath t) = 3 * t - (N.scalarStitchedPath t) ^ 2
  real_path_lifted : ∀ t, Tomabechi.Consistency.C3.stageTime 0 ≤ t →
    liftedStageCenter (cognitiveCoordinate (N.completePath t)) = N.liftedStitchedPath t
  /-- 26/27：完全状態の chart はモデルの射影そのもの。 -/
  top_chart : ∀ z : CompleteState, fullCommonTopStateEquiv (completeTopChart z) = N.topProjection z
  /-- 定理1・4 の Euclid 距離版（定数 √2 倍、`commonV0X`、全初期点）。 -/
  theorem1_euclid : ∀ (x : AgentState) (t₀ : ℝ), 0 ≤ t₀ →
    (∀ t, t₀ ≤ t → Metric.infDist (c1EuclideanCoordinates.symm (consensusOptimalFlow.flow t₀ x t))
        (c1EuclideanCoordinates.symm '' point1TargetX x t₀) ≤
      Real.sqrt 2 * (Real.sqrt (Fg x) * Real.exp (-3 * (t - t₀)))) ∧
    Tendsto (fun t => Metric.infDist (c1EuclideanCoordinates.symm (consensusOptimalFlow.flow t₀ x t))
      (c1EuclideanCoordinates.symm '' point1TargetX x t₀)) atTop (𝓝 0)
  theorem4_euclid : ∀ (x : AgentState) (t₀ : ℝ), 0 ≤ t₀ →
    (∀ t, t₀ ≤ t → Metric.infDist (c1EuclideanCoordinates.symm (consensusOptimalFlow.flow t₀ x t))
        (c1EuclideanCoordinates.symm '' point4TargetX x t₀) ≤
      Real.sqrt 2 * (Real.sqrt (effX x) * Real.exp (-(3 / 2 : ℝ) * (t - t₀)))) ∧
    Tendsto (fun t => Metric.infDist (c1EuclideanCoordinates.symm (consensusOptimalFlow.flow t₀ x t))
      (c1EuclideanCoordinates.symm '' point4TargetX x t₀)) atTop (𝓝 0)
  /-- 定理4の値域（`commonV0X` 版）：`P∈(0,1]`、`Q=1`、`κ=1`、`Ṽ ≥ F ≥ 0 ≥ −κ`。 -/
  theorem4_ranges_X : ∀ y : AgentState, (0 < Real.exp (-(Fg y)) ∧ Real.exp (-(Fg y)) ≤ 1) ∧
    Fg y ≤ effX y ∧ -(1 : ℝ) ≤ effX y

theorem sharedModel_finalCrossChecks : SharedFinalCrossChecks sharedModel where
  typed_Self_Ego := fun h => ⟨rfl, rfl⟩
  typed_TCZ := fun h i => rfl
  stage_switch := sharedModel_stageSwitchInputs
  stage_address_16 := fun n => sharedModel_shared16Indexing.stage_shift n
  stage_information := fun n => sharedModel_preservation.stage_information n
  real_path_cognitive := sharedModel_preservation.cognitive_path
  real_path_physical := sharedModel_preservation.physical_path
  real_path_lifted := sharedModel_preservation.lifted_path
  top_chart := fun z => completeTopChart_eq_topProjection z
  theorem1_euclid := fun x t₀ ht₀ => by
    obtain ⟨_, hb, hl⟩ := theorem1_commonDomainX x t₀ ht₀
    exact ⟨fun t ht => euclid_infDist_le_of_sup _ _ _ (hb t ht), euclid_tendsto_of_sup _ _ hl⟩
  theorem4_euclid := fun x t₀ ht₀ => by
    obtain ⟨_, hb, hl⟩ := theorem4_commonDomainX x t₀ ht₀
    exact ⟨fun t ht => euclid_infDist_le_of_sup _ _ _ (hb t ht), euclid_tendsto_of_sup _ _ hl⟩
  theorem4_ranges_X := fun y => by
    have hF := Fg_nonneg y
    have hb := effX_bounds y
    refine ⟨⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩, hb.1, by linarith [hb.1]⟩

/-! ## 最終存在宣言 v11 -/

/-- 統合した最終受入型。現行版・旧版・その関係・再照合を、同じ N で束ねる。 -/
structure SharedFinalConsistency (N : SharedModelSignature) : Prop where
  /-- 原文由来の C6 入力・明示追加条件・非退化性（旧署名のデータ。旧 TCZ・旧基礎評価に結んだ入口を含む）。 -/
  original : FullOriginalPremisesV2 N
  additional : ExplicitAdditionalConditionsV2 N
  nondegenerate : SharedNondegenerateV2 N
  native_nondegenerate : SharedNativeNondegenerate N
  /-- 現行版：正典 TCZ・25 の三表現・19 の主体/履歴/固定容量・共通領域と共有評価・21 の V₀ 実例・
  26/27 の完全状態・Borel・時計座標なし・25-C4/C5。 -/
  canonical16 : Shared16CanonicalInputs N
  canonical25 : Shared25CanonicalSelf N
  subject_identity : SharedSubjectIdentityCanonical N
  fixed_capacity : SharedFixedCapacityInputs N
  common_domain : SharedCommonDomainX N
  domain_theorems : SharedDomainTheorems N
  theorem21 : SharedTheorem21V0Common N
  top_complete : SharedTopCompleteReading N
  borel : SharedBorelStructure N
  no_clock : SharedNoClockCoordinate N
  mortality : MortalityOnN N
  genealogy : GenealogyMortalityExtension N
  presence25B : MortalityPresence25B
  /-- 旧版（置換される読み）：一点閉包版・旧自己表象・旧主体同一性・旧基礎評価に結んだ補助。 -/
  one_point16 : Shared16OnePointInputs N
  one_point25 : Shared25OnePointSelf N
  old_subject_identity : SharedSubjectIdentity N
  old_premises16 : Shared16Premises N
  old_base_ranges : SharedTheorem4Ranges N
  old_norm : SharedNormUnificationConclusions N
  old_base_background : SharedBaseBackground21 N
  old_theorem21 : SharedTheorem21V0 N
  /-- 旧版と現行版の関係、および再照合。 -/
  coherence : SharedVersionCoherence N
  cross_checks : SharedFinalCrossChecks N

theorem sharedModel_finalConsistency : SharedFinalConsistency sharedModel where
  original := ⟨sharedModel_fullOriginalPremises, sharedModel_capacityInputs,
    sharedModel_shared16LayerTCZInputs, sharedModel_normUnification⟩
  additional := ⟨sharedModel_explicitAdditionalConditions,
    sharedModel_pointDomainInputs.explicitHConditions, sharedModel_shared16Indexing,
    sharedModel_baseDomain⟩
  nondegenerate := ⟨sharedModel_nondegenerate, sharedModel_nativeNondegenerate⟩
  native_nondegenerate := sharedModel_nativeNondegenerate
  canonical16 := sharedModel_shared16CanonicalInputs
  canonical25 := sharedModel_shared25CanonicalSelf
  subject_identity := sharedModel_subjectIdentityCanonical
  fixed_capacity := sharedModel_fixedCapacityInputs
  common_domain := sharedModel_commonDomainX
  domain_theorems := sharedModel_domainTheorems
  theorem21 := SharedModelSignature.sharedTheorem21V0Common sharedModel_theorem21V0
    sharedModel_stageSwitchInputs
  top_complete := sharedModel.sharedTopCompleteReading
  borel := sharedModel_borelStructure
  no_clock := sharedModel_noClockCoordinate
  mortality := sharedModel_mortalityOnN
  genealogy := sharedModel_genealogyMortality
  presence25B := mortalityPresence25B
  one_point16 := sharedModel_shared16OnePointInputs
  one_point25 := sharedModel_shared25OnePointSelf
  old_subject_identity := sharedModel_subjectIdentity
  old_premises16 := sharedModel_shared16Premises
  old_base_ranges := sharedModel_theorem4Ranges
  old_norm := sharedModel_normUnificationConclusions
  old_base_background := sharedModel_baseBackground21
  old_theorem21 := sharedModel_theorem21V0
  coherence := sharedModel_versionCoherence
  cross_checks := sharedModel_finalCrossChecks

/-- 最終存在宣言 v11：現行版・旧版・その関係・再照合を同じ `sharedModel` で。 -/
theorem final_consistency_v11 : ∃ N : SharedModelSignature, SharedFinalConsistency N :=
  ⟨sharedModel, sharedModel_finalConsistency⟩

#print axioms sharedModel_versionCoherence
#print axioms sharedModel_finalCrossChecks
#print axioms sharedModel_finalConsistency
#print axioms final_consistency_v11

end Tomabechi.Consistency.R123
