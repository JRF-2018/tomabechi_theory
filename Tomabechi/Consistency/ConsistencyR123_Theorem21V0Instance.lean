import Tomabechi.Consistency.ConsistencyR123_Shared16OnePoint

/-!
# 定理21を V₀ = 共有基礎評価で適用した実例

以前は (21.3) の V₀ の条件（C²・`‖∇V₀‖≤B`・`∇²V₀≽−βI`）だけを `V₀ = N.base.V0` について示した。
ここでは **定理21の単独の実例**を作る：背景 `V₀ = N.base.V0∘coords`、偏り `S(x) = −‖x‖²/2`（`m=1`）、
`κ=1`、中心 `x_b = 0`（合意点）、球 `B̄_{1/8}(0)`（箱の内部）、移動度は恒等、
`B = 8r = 1`、`β = 0`、臨場感利得 `p = 9 > p_crit = max{β, B/r}/(κm) = 8`。
初期点は `‖x₀‖ = 1/16` で、部分準位は原文どおり `{x ∈ U_b | Ṽ(x) ≤ Ṽ(x₀)}`。
`MeanFieldStageInput` を構成して、定理21の四結論（一意最小点・距離・指数収束・直接KL CMI）の
一般入口 `meanField_stage_theorem21_four_conclusions_directKL` を適用する。

**範囲：** 中心 `0`・球の大きさ・初期点・利得は具体値の一つ（存在の実例）。段の背景地形 `R_n`（22/23-B）
とは別の入力で、`R_n ＝ N.base.V0` とは主張しない。情報の部分（ゴール分布・行為）は C3 の上位層の law を使う。
-/

open MeasureTheory

noncomputable section
namespace Tomabechi.Consistency.R123
open Filter
open scoped Topology Gradient
open Tomabechi.Consistency.R1 Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Theorem22

/-- 背景 `V₀ = N.base.V0` の認知座標（Euclid）表示（`sharedModel`）。 -/
def v0Background (z : C1EuclideanAgentState) : ℝ :=
  sharedModel.base.V0 (c1EuclideanCoordinates z) 0

/-- 偏りの平均場 `S(x) = −‖x‖²/2` を上位層の Dirac 平均で表す平均化表現（中心は全原子で 0）。 -/
def v0AveragePresentation : MeanFieldAveragePresentation LiftedStageState :=
  { liftedStageAveragePresentation 0 with
    centerRepresentation := fun _ => 0
    reconstructionKernel := fun x _ => (-(1 / 2 : ℝ)) * ‖x‖ ^ 2
    reconstructionKernel_integrable := fun x => by
      letI := (liftedStageAveragePresentation 0).atomMeasurableSpace
      haveI := (liftedStageAveragePresentation 0).atomMeasure_probability
      exact integrable_const _ }


def v0Radius : ℝ := 1 / 8

/-- 初期点 `x₀ = (1/16) e₀`、`‖x₀‖ = 1/16 = r/2`。 -/
def v0Initial : LiftedStageState := (1 / 16 : ℝ) • EuclideanSpace.single 0 1

theorem v0Initial_norm : ‖v0Initial‖ = 1 / 16 := by
  simp [v0Initial, norm_smul]

def v0MeanField (x : LiftedStageState) : ℝ := (-(1 / 2 : ℝ)) * ‖x‖ ^ 2

theorem v0AveragePresentation_integral (x : LiftedStageState) :
    v0AveragePresentation.integralValue x = v0MeanField x := by
  classical
  letI : MeasurableSpace LiftedStageAtom := ⊤
  unfold MeanFieldAveragePresentation.integralValue v0AveragePresentation
    liftedStageAveragePresentation
  dsimp
  rw [integral_dirac]
  rfl

/-- 球 `‖x‖ ≤ 1/8` 上で `V₀ = 1 + 8·symbolDistance`（箱内の二次式）。 -/
theorem v0Background_eq {x : LiftedStageState} (hx : ‖x‖ ≤ 1 / 8) :
    v0Background x = 1 + 8 * c1EuclideanSymbolDistance x := by
  have hint : x ∈ interior c1EuclideanBox :=
    closedBall_subset_interior_box (r := 1 / 8) (by norm_num)
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
  have hbox : x ∈ c1EuclideanBox := interior_subset hint
  have := sharedModel_baseDomain.extension_eq_on_box x hbox
  rw [theorem20BaseExtension_eq] at this
  unfold v0Background
  rw [← this]
  rfl

theorem symbolDistance_nonneg' (x : LiftedStageState) : 0 ≤ c1EuclideanSymbolDistance x :=
  c1EuclideanSymbolDistance_nonneg x

theorem symbolDistance_le (x : LiftedStageState) : c1EuclideanSymbolDistance x ≤ ‖x‖ ^ 2 / 2 := by
  unfold c1EuclideanSymbolDistance
  have h1 : |inner ℝ c1EuclideanDisagreementDirection x| ≤
      ‖c1EuclideanDisagreementDirection‖ * ‖x‖ := abs_real_inner_le_norm _ _
  have hd : ‖c1EuclideanDisagreementDirection‖ ^ 2 = 2 := c1EuclideanDisagreementDirection_norm_sq
  have h2 : (inner ℝ c1EuclideanDisagreementDirection x) ^ 2 ≤
      (‖c1EuclideanDisagreementDirection‖ * ‖x‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [mul_pow, hd] at h2
  nlinarith


/-- 部分準位：球内で `Ṽ(x) ≤ Ṽ(x₀)`（`κ=1`、`p=9`）。 -/
def v0Sublevel : Set LiftedStageState :=
  {x | x ∈ Metric.closedBall (0 : LiftedStageState) v0Radius ∧
    v0Background x - 1 * 9 * v0MeanField x ≤
      v0Background v0Initial - 1 * 9 * v0MeanField v0Initial}

theorem v0Sublevel_norm_le {x : LiftedStageState} (hx : x ∈ v0Sublevel) : ‖x‖ ≤ 1 / 10 := by
  obtain ⟨hball, hle⟩ := hx
  have hx8 : ‖x‖ ≤ 1 / 8 := by simpa [Metric.mem_closedBall, dist_zero_right, v0Radius] using hball
  have hx0 : ‖v0Initial‖ ≤ 1 / 8 := by rw [v0Initial_norm]; norm_num
  rw [v0Background_eq hx8, v0Background_eq hx0] at hle
  have h1 := symbolDistance_nonneg' x
  have h2 := symbolDistance_le v0Initial
  have h0 : ‖v0Initial‖ ^ 2 = 1 / 256 := by rw [v0Initial_norm]; norm_num
  simp only [v0MeanField] at hle
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg x]

/-- 定理21の `MeanFieldStageInput`：`V₀ = N.base.V0`、偏り `−‖x‖²/2`、中心 0、球 `B̄_{1/8}(0)`。 -/
noncomputable def v0StageInput : MeanFieldStageInput LiftedStageState := by
  refine
    { center := 0
      radius := v0Radius
      gain := 1
      presenceGain := 9
      curvature := 1
      backgroundCurvature := 0
      gradientBound := 8 * v0Radius
      gamma := 1
      startTime := 0
      background := v0Background
      meanField := v0MeanField
      averagePresentation := v0AveragePresentation
      center_eq_supportLub_representation := rfl
      meanField_eq_integral := fun x => (v0AveragePresentation_integral x).symm
      backgroundGradient := fun x => gradient v0Background x
      meanFieldGradient := fun x => (-1 : ℝ) • x
      backgroundHessian := fun _ => baseHessian21
      meanFieldHessian := fun _ => (-1 : ℝ) • ContinuousLinearMap.id ℝ LiftedStageState
      mobility := liftedStageMobility
      sublevel := v0Sublevel
      initial := v0Initial
      radius_pos := by norm_num [v0Radius]
      gain_pos := by norm_num
      curvature_pos := by norm_num
      backgroundCurvature_nonneg := by norm_num
      gradientBound_nonneg := by norm_num [v0Radius]
      gain_threshold := by norm_num [v0Radius]
      background_c2_at := ?_
      meanField_c2_at := ?_
      background_gradient_representation := ?_
      meanField_gradient_representation := ?_
      background_gradient_deriv := ?_
      meanField_gradient_deriv := ?_
      mobility_c1 := by intro y hy; fun_prop [liftedStageMobility]
      mobility_symmetric := ?_
      background_hessian_lower := ?_
      meanField_hessian_upper := ?_
      meanField_center_stationary := by simp
      background_gradient_bound := ?_
      initial_mem := ?_
      sublevel_barrier := ?_
      gamma_pos := by norm_num
      mobility_coercive := ?_
      sublevel_eq := rfl }
  · -- background_c2_at
    intro y hy
    have hy' : ‖y‖ ≤ 1 / 8 := by simpa [Metric.mem_closedBall, dist_zero_right, v0Radius] using hy
    exact sharedModel_baseBackground21.c2 (1 / 8) (by norm_num) y
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hy')
  · -- meanField_c2_at
    intro y hy
    have h : ContDiffAt ℝ 2 (fun z : LiftedStageState => ‖z‖ ^ 2) y :=
      ContDiffAt.norm_sq (𝕜 := ℝ) contDiffAt_id
    exact h.const_smul (-(1 / 2 : ℝ)) |>.congr_of_eventuallyEq (by
      filter_upwards with z; simp [v0MeanField, smul_eq_mul])
  · -- background_gradient_representation
    intro y
    ext w
    simp [gradient, InnerProductSpace.toDual_symm_apply, innerSL_apply_apply]
  · -- meanField_gradient_representation
    intro y
    have hfd : HasFDerivAt (fun z : LiftedStageState => ‖z‖ ^ 2)
        (2 • (innerSL ℝ y)) y := by
      simpa using hasStrictFDerivAt_norm_sq y |>.hasFDerivAt
    have := hfd.const_smul (-(1 / 2 : ℝ))
    change innerSL ℝ ((-1 : ℝ) • y) = fderiv ℝ (fun z : LiftedStageState => v0MeanField z) y
    have hmf : (fun z : LiftedStageState => v0MeanField z) =
        fun z => (-(1 / 2 : ℝ)) • ‖z‖ ^ 2 := by funext z; simp [v0MeanField, smul_eq_mul]
    have hfd2 : HasFDerivAt (fun z : LiftedStageState => (-(1 / 2 : ℝ)) • ‖z‖ ^ 2)
        (-(1 / 2 : ℝ) • 2 • (innerSL ℝ y)) y := this
    rw [hmf, hfd2.fderiv]
    ext w
    simp [innerSL_apply_apply]
  · -- background_gradient_deriv
    intro y hy
    have hy' : ‖y‖ ≤ 1 / 8 := by simpa [Metric.mem_closedBall, dist_zero_right, v0Radius] using hy
    have hev : (fun x => gradient v0Background x) =ᶠ[𝓝 y] fun x => baseHessian21 x := by
      have hn : Metric.ball (0 : LiftedStageState) (3 / 16) ∈ 𝓝 y :=
        Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball, dist_zero_right]; linarith)
      filter_upwards [hn] with z hz
      have hz' : z ∈ Metric.closedBall (0 : LiftedStageState) (3 / 16) := Metric.ball_subset_closedBall hz
      exact (sharedModel_baseBackground21.gradient (3 / 16) (by norm_num) z hz').gradient
    exact (baseHessian21.hasFDerivAt (x := y)).congr_of_eventuallyEq hev
  · -- meanField_gradient_deriv
    intro y hy
    exact (hasFDerivAt_id y).const_smul (-1 : ℝ)
  · -- mobility_symmetric
    intro y hy v w
    simp [liftedStageMobility, real_inner_smul_left, real_inner_smul_right]
  · -- background_hessian_lower
    intro y hy w
    simpa using sharedModel_baseBackground21.hessian_lower w
  · -- meanField_hessian_upper
    intro y hy w
    simp [real_inner_self_eq_norm_sq, real_inner_smul_left]
  · -- background_gradient_bound
    intro y hy
    have hy' : ‖y‖ ≤ 1 / 8 := by simpa [Metric.mem_closedBall, dist_zero_right, v0Radius] using hy
    have hg : gradient v0Background y = baseHessian21 y :=
      (sharedModel_baseBackground21.gradient (3 / 16) (by norm_num) y
        (by simp [Metric.mem_closedBall, dist_zero_right]; linarith)).gradient
    rw [hg]
    have := baseHessian21_bound y
    simp only [v0Radius] at *
    linarith
  · -- initial_mem
    refine ⟨?_, le_rfl⟩
    simp [Metric.mem_closedBall, dist_zero_right, v0Initial_norm, v0Radius]
    norm_num
  · -- sublevel_barrier
    have hsub : v0Sublevel ⊆ Metric.closedBall (0 : LiftedStageState) (1 / 10) := by
      intro x hx
      simpa [Metric.mem_closedBall, dist_zero_right] using v0Sublevel_norm_le hx
    refine (closure_minimal hsub Metric.isClosed_closedBall).trans ?_
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right] at hx
    simp only [Metric.mem_ball, dist_zero_right, v0Radius]
    linarith
  · -- mobility_coercive
    intro y hy w
    simp [liftedStageMobility, real_inner_self_eq_norm_sq, real_inner_smul_left]


open Tomabechi.Consistency.C3 in
/-- 定理21の四結論（一意最小点・距離・指数収束・直接KL CMI）を、`V₀ = N.base.V0` の段へ適用。 -/
def v0Stage_theorem21 :=
  meanField_stage_theorem21_four_conclusions_directKL
    v0StageInput (branchContext 0)
    (Measure.dirac ()) inputMass inputAction (fun _ => ((0 + 1 : ℕ) : Atom))
    inputAction_measurable
    (by
      filter_upwards with x
      intro g hg
      change ((0 + 1 : ℕ) : Atom) ∈ {((0 + 1 : ℕ) : Atom)}
      simp)
    (by
      filter_upwards with x
      intro g
      exact inputMass_nonneg x g)
    (by
      filter_upwards with x
      exact inputMass_sum x)
    (by
      filter_upwards with x
      intro g hg g' h
      exact inputAction_injective x g hg g' h)
    inputMass_measurable
    inputEntropy_pos
    (fun a : Atom => a) (by intro a b h; exact h)
    (by intro a b hab; exact hab)
    (by
      change {((0 + 1 : ℕ) : Atom)} = (fun a : Atom => a) '' {((0 + 1 : ℕ) : Atom)}
      simp)
    (by
      change {((0 + 1 : ℕ) : Atom)} = (fun a : Atom => a) '' {((0 + 1 : ℕ) : Atom)}
      simp)
    (by
      change (⊤ : Atom) = ⊤
      rfl)
    (by
      change ((0 + 1 : ℕ) : Atom) = sSup {((0 + 1 : ℕ) : Atom)}
      simp)

/-- 実例の結論（定理21の四結論）の命題。 -/
def V0StageConclusion : Prop := type_of% v0Stage_theorem21

theorem v0Stage_theorem21_holds : V0StageConclusion := v0Stage_theorem21

/-- 定理21を V₀ = 共有基礎評価で適用した実例の受入型。 -/
structure SharedTheorem21V0 (N : SharedModelSignature) : Prop where
  background_is_base : v0StageInput.background = fun z => N.base.V0 (c1EuclideanCoordinates z) 0
  center_zero : v0StageInput.center = 0
  gain_above_critical :
    max v0StageInput.backgroundCurvature (v0StageInput.gradientBound / v0StageInput.radius) /
        (v0StageInput.gain * v0StageInput.curvature) <
      v0StageInput.presenceGain
  initial_off_center : v0StageInput.initial ≠ v0StageInput.center
  conclusion : V0StageConclusion

theorem sharedModel_theorem21V0 : SharedTheorem21V0 sharedModel where
  background_is_base := rfl
  center_zero := rfl
  gain_above_critical := by norm_num [v0StageInput, v0Radius]
  initial_off_center := by
    intro h
    have : ‖v0Initial‖ = 0 := by
      have h' : v0Initial = 0 := h
      rw [h']; simp
    rw [v0Initial_norm] at this
    norm_num at this
  conclusion := v0Stage_theorem21_holds

/-- v4：v3 の全受入型に、V₀ = 共有基礎評価での定理21の実例を加えた存在宣言。 -/
theorem final_consistency_v4 :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N ∧
        GenealogyMortalityExtension N ∧ Shared16OnePointInputs N ∧ SharedTheorem21V0 N :=
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
    sharedModel_theorem21V0⟩

#print axioms sharedModel_theorem21V0
#print axioms v0Stage_theorem21_holds
#print axioms final_consistency_v4

end Tomabechi.Consistency.R123
