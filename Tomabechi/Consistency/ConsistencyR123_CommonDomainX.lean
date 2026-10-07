import Tomabechi.Consistency.ConsistencyR123_CanonicalTCZ

/-!
# 共通状態領域 X の部分的な統合

**問題：** `SharedBaseDomain` は X := box（各座標の絶対値 ≤ 1/4）を採るが、`sharedModel.stages 0` の
中心は座標 `1/(2√2) > 1/4` で箱の外にあり、§11 の `U_n ⊂ X` が共通箱では成り立たない。

**観察：** 有限層の実走行費（定理24）は `1 + 8(halfDifference x)² = 1 + 2(x₀−x₁)²` で、**全域で**この二次式であり、
定理20の拡張 `1 + 8·symbolDistance` も全域で同じ二次式である。箱でだけ一致が要るのは、定理1・2・4の
`N.base.V0 = 1 + DA.potential`（定理2の個人閾値残差 `[(x_i)²−θ]₊`, `θ = 1/10` を含む）だけである。

**ここで証明すること：** 明示的な共通領域 `X := ℝ²`（Euclid 平面全体）と全域の共有評価
`commonV0X x := 1 + 2(x₀−x₁)²` を置き、

1. `commonV0X` は定理20の拡張・有限層 24 の実走行費（`sharedModel.legacy`、共通束の層 α を通しても）と**全域で一致**する。
2. `commonV0X` は全域で C^∞ で、勾配場 `G z = baseHessian21 z`（`‖G z‖ ≤ 8‖z‖`）、`∇² ≽ 0`（β=0）。
3. すべての実際の段 `sharedModel.stages n` の閉球 `U_n` は `closedBall 0 3` に含まれ、したがって `X` に含まれる。
   各 `U_n` 上で `commonV0X` は (21.3) の型の条件（C²・`‖∇V₀‖ ≤ 24`・`∇²V₀ ≽ 0`）を満たす。
4. `N.base.V0` は箱上で `commonV0X` に一致し、定理1・2・4 の一点到達集合は箱の中に留まる。
5. 箱の外では `N.base.V0` と `commonV0X` が異なる（記録）。

**証明していないこと：** 定理1・2・4 を、箱の外の初期点を含む `X` 全体で
`commonV0X` について述べ直すこと。これらは定理2の個人閾値残差を含む `DA`（`θ=1/10` 固定）に結んで
構成されており、箱の外では `Φ₂ ≠ commonV0X − 1` である。`θ` を大きく取り直した並列の `DA`、
共有基礎契約・入口・受入型の再構成が要り、既存の宣言を変えない方針では本ファイルの範囲を超える。
したがって「同じ V₀ が 1/4/20/24 で `X` 全体で一致する」とは主張しない（20 と 24 については全域で一致、
1・2・4 は箱の上でだけ）。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Filter
open scoped Topology Gradient
open Tomabechi.Consistency.R1 Tomabechi.Consistency.R2 Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.C6

/-- 共通状態領域 `X`：Euclid 平面全体（座標写像は `c1EuclideanCoordinates`）。 -/
def commonDomainX : Set C1EuclideanAgentState := Set.univ

/-- 段の閉球をすべて含む有界な部分領域。 -/
def stageHull : Set C1EuclideanAgentState := Metric.closedBall 0 3

/-- 全域の共有評価。 -/
def commonV0X (x : AgentState) : ℝ := 1 + 2 * (x 0 - x 1) ^ 2

def commonV0XE (z : C1EuclideanAgentState) : ℝ := commonV0X (c1EuclideanCoordinates z)

theorem commonV0X_eq_halfDifference (x : AgentState) :
    commonV0X x = 1 + 8 * (halfDifference x) ^ 2 := by
  simp only [commonV0X, halfDifference]; ring

/-- 定理20の拡張と全域で一致。 -/
theorem commonV0XE_eq_theorem20_extension : commonV0XE = sharedT20V0 := by
  funext z
  rw [commonV0XE, sharedT20V0, c1EuclideanSymbolDistance_eq_coordinates]
  simp only [commonV0X, c1SymbolDistance]
  ring

/-- 有限層の実走行費（定理24）は全域で `commonV0X`。 -/
theorem sharedModel_finiteCost_eq_commonV0X (k : ℕ) (π : C1GainSignal) (x : AgentState) (t : ℝ) :
    sharedModel.legacy.data.runningCost (some k) π x t = commonV0X x := by
  change c6LayeredRunningCost (some k) π x t = commonV0X x
  simp only [c6LayeredRunningCost]
  rw [commonV0X_eq_halfDifference]

/-- 共通束の層 `index16 i` を通しても、実走行費は全域で `commonV0X`。 -/
theorem sharedModel_commonLayerCost_eq_commonV0X (i : ℕ) (u : C1GainSignal) (x : AgentState)
    (t : ℝ) :
    sharedModel.data.runningCost (index16 i) (layerPolicyCast i u) (layerStateCast i x) t =
      commonV0X x := by
  rw [sharedModel_preservation.layerCost_eq]
  exact sharedModel_finiteCost_eq_commonV0X i u x t

theorem commonV0X_ge_one (x : AgentState) : 1 ≤ commonV0X x := by
  simp only [commonV0X]; nlinarith [sq_nonneg (x 0 - x 1)]

/-- 全域で C^∞、勾配場 `baseHessian21`。 -/
theorem commonV0XE_contDiff : ContDiff ℝ 2 commonV0XE := by
  rw [commonV0XE_eq_theorem20_extension]
  have hin : ContDiff ℝ 2 (fun x : C1EuclideanAgentState =>
      inner ℝ c1EuclideanDisagreementDirection x) :=
    (innerSL ℝ c1EuclideanDisagreementDirection).contDiff
  unfold sharedT20V0 c1EuclideanSymbolDistance
  exact contDiff_const.add (contDiff_const.mul (contDiff_const.mul (hin.pow 2)))

theorem commonV0XE_hasGradientAt (z : C1EuclideanAgentState) :
    HasGradientAt commonV0XE (baseHessian21 z) z := by
  rw [commonV0XE_eq_theorem20_extension, ← baseGradient21_eq]
  exact sharedT20V0_hasGradientAt z

theorem liftedStageCenter_norm (c : ℝ) : ‖liftedStageCenter c‖ = |c| := by
  have h := liftedStageCenter_difference_norm c 0
  have h0 : liftedStageCenter 0 = 0 := by
    ext i; simp [liftedStageCenter]
  rw [h0, sub_zero, sub_zero] at h
  exact h

theorem stage_center_eq (n : ℕ) :
    (sharedModel.stages n).center =
      liftedStageCenter (Tomabechi.Consistency.C3.representation ((n + 1 : ℕ) : WithTop ℕ)) := by
  have h := liftedHStageInput_center_eq_lifted_scalar n
  change ((liftedHStageInput n).toStageValleySpec).center = _
  rw [h]
  have hc := Tomabechi.Consistency.C3.hStageSequence_center n
  simp only [Tomabechi.Consistency.C3.hStageSequenceStageSpecs,
    Tomabechi.Theorem22.meanFieldStageSequence]
  congr 1

/-- 球 `U_n` ⊂ `closedBall 0 3` の評価。 -/
theorem stage_center_norm_lt_one (n : ℕ) : ‖(sharedModel.stages n).center‖ < 1 := by
  rw [stage_center_eq, liftedStageCenter_norm]
  have h0 : 0 ≤ Tomabechi.Consistency.C3.representation ((n + 1 : ℕ) : WithTop ℕ) := by
    simp only [Tomabechi.Consistency.C3.representation]; positivity
  rw [abs_of_nonneg h0]
  exact Tomabechi.Consistency.C3.representation_lt_top (n + 1)

theorem stage_radius_le_two (n : ℕ) : (sharedModel.stages n).radius ≤ 2 := by
  have h := liftedHStageInput_radius_eq_scalar n
  change ((liftedHStageInput n).toStageValleySpec).radius ≤ 2
  rw [h]
  simp only [Tomabechi.Consistency.C3.hStageSequenceStageSpecs,
    Tomabechi.Theorem22.meanFieldStageSequence]
  rw [Tomabechi.Consistency.C3.hStageSequence_toStageValleySpec n,
    Tomabechi.Consistency.C3.valleySequence_shape n]
  simp only [Tomabechi.Examples.Theorem23B.quadraticStage]
  have hi : (Tomabechi.Consistency.C3.valleySequence n).initial =
      (Tomabechi.Consistency.C3.hStageSequence n).initial := rfl
  rw [hi]
  have hb := Tomabechi.Consistency.C3.hStageSequence_initial_between_centers n
  have hl := Tomabechi.Consistency.C3.representation_lt_top (n + 1)
  have hcast : ((n + 1 : ℕ) : WithTop ℕ) = (n : WithTop ℕ) + 1 := by push_cast; rfl
  rw [hcast] at hb hl
  have : |(Tomabechi.Consistency.C3.hStageSequence n).initial -
      Tomabechi.Consistency.C3.representation ((n : WithTop ℕ) + 1)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
  rw [hcast]
  linarith

/-- 実際の段の閉球は `closedBall 0 3`（したがって `X`）に含まれる。 -/
theorem stage_ball_subset_hull (n : ℕ) :
    Metric.closedBall (sharedModel.stages n).center (sharedModel.stages n).radius ⊆ stageHull := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  show z ∈ Metric.closedBall (0 : C1EuclideanAgentState) 3
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 := stage_center_norm_lt_one n
  have h2 := stage_radius_le_two n
  have : ‖z‖ ≤ ‖z - (sharedModel.stages n).center‖ + ‖(sharedModel.stages n).center‖ := by
    simpa using norm_add_le (z - (sharedModel.stages n).center) (sharedModel.stages n).center
  linarith

/-- 全域の共有評価 `commonV0X` の、各段の球上での (21.3) 型の条件：C²・`‖∇V₀‖ ≤ 24`・`∇²V₀ ≽ 0`（β=0）。 -/
theorem commonV0X_regular_on_stage_balls (n : ℕ) :
    ContDiff ℝ 2 commonV0XE ∧
    (∀ z ∈ Metric.closedBall (sharedModel.stages n).center (sharedModel.stages n).radius,
      HasGradientAt commonV0XE (baseHessian21 z) z ∧ ‖baseHessian21 z‖ ≤ 24) ∧
    (∀ w : C1EuclideanAgentState, 0 ≤ inner ℝ (baseHessian21 w) w) := by
  refine ⟨commonV0XE_contDiff, fun z hz => ⟨commonV0XE_hasGradientAt z, ?_⟩, baseHessian21_psd⟩
  have hz' : z ∈ stageHull := stage_ball_subset_hull n hz
  have hn : ‖z‖ ≤ 3 := by
    have := hz'
    simpa [stageHull, Metric.mem_closedBall, dist_zero_right] using this
  have := baseHessian21_bound z
  linarith

/-- 箱の上で `N.base.V0` は `commonV0X`。 -/
theorem SharedModelSignature.base_eq_commonV0X_on_box (N : SharedModelSignature) {x : AgentState}
    (hx : x ∈ box) (t : ℝ) : N.base.V0 x t = commonV0X x := by
  rw [N.base.V0_eq_shared]
  unfold commonBaseV0 commonV0X
  rw [Tomabechi.Examples.Theorem2.potential_eq]
  have h0 : (x 0 - (![0, 0] : Fin 2 → ℝ) 0) ^ 2 - Tomabechi.Examples.Theorem2.θ ≤ 0 := by
    have := hx 0
    have habs := abs_le.mp this
    have e0 : (![0, 0] : Fin 2 → ℝ) 0 = 0 := rfl
    rw [e0]
    simp only [sub_zero, Tomabechi.Examples.Theorem2.θ]
    nlinarith [habs.1, habs.2]
  have h1 : (x 1 - (![0, 0] : Fin 2 → ℝ) 1) ^ 2 - Tomabechi.Examples.Theorem2.θ ≤ 0 := by
    have := hx 1
    have habs := abs_le.mp this
    have e1 : (![0, 0] : Fin 2 → ℝ) 1 = 0 := rfl
    rw [e1]
    simp only [sub_zero, Tomabechi.Examples.Theorem2.θ]
    nlinarith [habs.1, habs.2]
  rw [max_eq_right h0, max_eq_right h1]
  simp only [Tomabechi.Examples.Theorem2.γ]
  ring

/-- 共通状態領域の統合（部分）：X := ℝ²、全域の共有評価 `commonV0X`。 -/
structure SharedCommonDomainX (N : SharedModelSignature) : Prop where
  /-- 領域は Euclid 平面全体、段の球は有界部分 `closedBall 0 3` に入る。 -/
  stage_balls_in_X : ∀ n, Metric.closedBall (N.stages n).center (N.stages n).radius ⊆ stageHull ∧
    stageHull ⊆ commonDomainX
  /-- 定理20の拡張は全域で `commonV0X`。 -/
  theorem20_global : N.theorem20BaseExtension = commonV0XE
  /-- 有限層の実走行費（定理24）は全域で `commonV0X`（共通束の層を通しても）。 -/
  layer_cost_global : ∀ (i : ℕ) (u : C1GainSignal) (x : AgentState) (t : ℝ),
    N.data.runningCost (index16 i) (layerPolicyCast i u) (layerStateCast i x) t = commonV0X x
  finite_cost_global : ∀ (k : ℕ) (π : C1GainSignal) (x : AgentState) (t : ℝ),
    N.legacy.data.runningCost (some k) π x t = commonV0X x
  /-- 有限層の軌道は全域で明示解。 -/
  finite_trajectory_global : ∀ (k : ℕ) (u : C1GainSignal) (x : AgentState) (T t : ℝ),
    N.legacy.data.trajectory (some k) u x T t = controlledConsensusState x T u t
  /-- 全域で C^∞・勾配・Hessian・各段の球上の勾配上界。 -/
  regular_global : ContDiff ℝ 2 commonV0XE ∧ (∀ z, HasGradientAt commonV0XE (baseHessian21 z) z) ∧
    (∀ w, 0 ≤ inner ℝ (baseHessian21 w) w)
  regular_on_stage_balls : ∀ n, ∀ z ∈ Metric.closedBall (N.stages n).center (N.stages n).radius,
    ‖baseHessian21 z‖ ≤ 24
  baseline_ge_one : ∀ x, 1 ≤ commonV0X x
  /-- 定理1・2・4 が使う `N.base.V0` は、箱の上で `commonV0X` に一致し、一点到達集合は箱の中に留まる。 -/
  base_eq_on_box : ∀ x ∈ box, ∀ t, N.base.V0 x t = commonV0X x
  point_reach_in_box : ∀ x ∈ box, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ y ∈ (N.pointAdapter x t₀).reachable, y ∈ box
  /-- 箱の外では `N.base.V0` と `commonV0X` は異なる（1・2・4 は箱の上でだけ `commonV0X` に結ばれる）。 -/
  base_ne_outside_box : ∃ x : AgentState, x ∉ box ∧ N.base.V0 x 0 ≠ commonV0X x

theorem sharedModel_commonDomainX : SharedCommonDomainX sharedModel where
  stage_balls_in_X := fun n => ⟨stage_ball_subset_hull n, fun _ _ => Set.mem_univ _⟩
  theorem20_global := by rw [theorem20BaseExtension_eq, commonV0XE_eq_theorem20_extension]
  layer_cost_global := sharedModel_commonLayerCost_eq_commonV0X
  finite_cost_global := sharedModel_finiteCost_eq_commonV0X
  finite_trajectory_global := fun k u x T t => by
    rw [sharedModel_explicitAdditionalConditions.legacy.toCommonDataCouplings.finite_trajectory]
  regular_global := ⟨commonV0XE_contDiff, commonV0XE_hasGradientAt, baseHessian21_psd⟩
  regular_on_stage_balls := fun n z hz => (commonV0X_regular_on_stage_balls n).2.1 z hz |>.2 |>.trans (by norm_num)
  baseline_ge_one := commonV0X_ge_one
  base_eq_on_box := fun x hx t => sharedModel.base_eq_commonV0X_on_box hx t
  point_reach_in_box := fun x hx t₀ ht₀ y hy => by
    rw [sharedModel_kernelInputs.pointK] at hy
    exact pointReachableClosure_subset_box x hx t₀ hy
  base_ne_outside_box := by
    obtain ⟨z, hz, hne⟩ := sharedModel_baseDomain.outside_differs
    refine ⟨c1EuclideanCoordinates z, fun hb => hz hb, ?_⟩
    rw [theorem20BaseExtension_eq] at hne
    intro heq
    apply hne
    have := commonV0XE_eq_theorem20_extension
    have h2 : sharedT20V0 z = commonV0X (c1EuclideanCoordinates z) := by
      rw [← this]; rfl
    rw [h2, heq]

/-- v8：v7 に共通状態領域の部分的な統合を加えた存在宣言。 -/
theorem final_consistency_v8 :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N ∧
        GenealogyMortalityExtension N ∧ Shared16OnePointInputs N ∧ SharedTheorem21V0 N ∧
        Shared25OnePointSelf N ∧ SharedTheorem21V0Common N ∧ MortalityOnN N ∧
        MortalityPresence25B ∧ Shared16CanonicalInputs N ∧ Shared25CanonicalSelf N ∧
        SharedSubjectIdentityCanonical N ∧ SharedCommonDomainX N :=
  ⟨sharedModel,
    ⟨sharedModel_fullOriginalPremises, sharedModel_capacityInputs,
      sharedModel_shared16LayerTCZInputs, sharedModel_normUnification⟩,
    ⟨sharedModel_explicitAdditionalConditions,
      sharedModel_pointDomainInputs.explicitHConditions,
      sharedModel_shared16Indexing, sharedModel_baseDomain⟩,
    ⟨sharedModel_nondegenerate, sharedModel_nativeNondegenerate⟩,
    sharedModel_baseBackground21, sharedModel.sharedTopCompleteReading,
    sharedModel_normUnificationConclusions, sharedModel_theorem4Ranges,
    sharedModel_shared16Premises, sharedModel_subjectIdentity, sharedModel_noClockCoordinate,
    sharedModel_borelStructure, sharedModel_genealogyMortality, sharedModel_shared16OnePointInputs,
    sharedModel_theorem21V0, sharedModel_shared25OnePointSelf,
    SharedModelSignature.sharedTheorem21V0Common sharedModel_theorem21V0
      sharedModel_stageSwitchInputs,
    sharedModel_mortalityOnN, mortalityPresence25B,
    sharedModel_shared16CanonicalInputs, sharedModel_shared25CanonicalSelf,
    sharedModel_subjectIdentityCanonical, sharedModel_commonDomainX⟩

#print axioms commonV0XE_eq_theorem20_extension
#print axioms sharedModel_finiteCost_eq_commonV0X
#print axioms stage_ball_subset_hull
#print axioms sharedModel_commonDomainX
#print axioms final_consistency_v8

end Tomabechi.Consistency.R123
