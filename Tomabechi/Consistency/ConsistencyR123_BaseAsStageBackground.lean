import Tomabechi.Consistency.ConsistencyR123_ModelExamples

/-!
# 定理21の V₀ としての共有基礎評価

定理21 の (21.3) は、局所球 `U_b = B̄_r(x_b)` 上で `V₀, S_μ ∈ C²(U_b)`、
`‖∇V₀‖ ≤ B`、`∇²V₀ ≽ −βI` を課す。原文は §2.1 の基礎評価と同じ記号 `V₀` を使う。
モデルの段 n では背景地形 `R_n` を別の関数として置いていた（`R_n` の読み、§11 が許す）が、
ここでは **`V₀ = 共有基礎評価 N.base.V0`**（認知座標の Euclid 表示）と読んだ場合に、
(21.3) が実際に成り立つことを示す。

箱 `box = {|xᵢ| ≤ 1/4}` の内部では `N.base.V0 = 1 + 8·symbolDistance`（箱内で `1+2(x₀−x₁)²`）で
二次式である。原点中心の Euclid 球 `B̄_r(0)`（`0 < r < 1/4`）は箱の内部に入るので、

* `V₀` は球上の各点で `C²`、
* 勾配は `G(z) = 8 • ∇symbolDistance(z) = 4⟨d,z⟩ d`（`d = e₀ − e₁`）、`‖G(z)‖ ≤ 8r`（`B = 8r`）、
* ヘシアンは `4 ⟨d,·⟩ d`（半正定値）で `∇²V₀ ≽ −βI`（`β = 0`）。

**範囲：** これは (21.3) の V₀ についての条件の充足であり、完全な `MeanFieldStageInput`（臨場感 S、
中心、勾配条件 `p > p_crit`、部分準位、障壁など）を `V₀ = N.base.V0` で組み直したものではない。
箱の内部の球に限る（箱の境界・外部では V₀ は二次式でない）。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Filter
open scoped Topology Gradient
open Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus

/-- 原点中心の球 `r < 1/4` は箱の内部に入る。 -/
theorem closedBall_subset_interior_box {r : ℝ} (hr : r < 1 / 4) :
    Metric.closedBall (0 : C1EuclideanAgentState) r ⊆ interior c1EuclideanBox := by
  intro z hz
  have hz' : z ∈ Metric.ball (0 : C1EuclideanAgentState) (1 / 4) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_zero_right] using hz) hr
  refine interior_maximal ?_ Metric.isOpen_ball hz'
  intro w hw i
  have hn : ‖w‖ < 1 / 4 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  have := PiLp.norm_apply_le w i
  change |c1EuclideanCoordinates w i| ≤ 1 / 4
  have hc : c1EuclideanCoordinates w i = w i := rfl
  rw [hc]
  simpa [Real.norm_eq_abs] using this.trans hn.le

/-- 勾配場 `G(z) = 8 • ∇symbolDistance(z)` は線形写像 `4⟨d,·⟩d` で、ヘシアンは半正定値。 -/
def baseHessian21 : C1EuclideanAgentState →L[ℝ] C1EuclideanAgentState :=
  (4 : ℝ) • (innerSL ℝ c1EuclideanDisagreementDirection).smulRight c1EuclideanDisagreementDirection

theorem baseGradient21_eq (z : C1EuclideanAgentState) :
    (8 : ℝ) • c1EuclideanSymbolDistanceGradient z = baseHessian21 z := by
  simp only [c1EuclideanSymbolDistanceGradient, baseHessian21, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
  congr 1
  ring

theorem baseHessian21_psd (w : C1EuclideanAgentState) :
    0 ≤ inner ℝ (baseHessian21 w) w := by
  simp only [baseHessian21, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left]
  have : inner ℝ c1EuclideanDisagreementDirection w * inner ℝ c1EuclideanDisagreementDirection w
      ≥ 0 := mul_self_nonneg _
  simp only [conj_trivial]
  nlinarith [mul_self_nonneg (inner ℝ c1EuclideanDisagreementDirection w)]

theorem baseHessian21_bound (z : C1EuclideanAgentState) :
    ‖baseHessian21 z‖ ≤ 8 * ‖z‖ := by
  simp only [baseHessian21, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, norm_smul]
  have h1 : |inner ℝ c1EuclideanDisagreementDirection z| ≤
      ‖c1EuclideanDisagreementDirection‖ * ‖z‖ := abs_real_inner_le_norm _ _
  have hd : ‖c1EuclideanDisagreementDirection‖ ^ 2 = 2 := c1EuclideanDisagreementDirection_norm_sq
  have hd0 := norm_nonneg c1EuclideanDisagreementDirection
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have : |inner ℝ c1EuclideanDisagreementDirection z| * ‖c1EuclideanDisagreementDirection‖ ≤
      2 * ‖z‖ := by
    calc _ ≤ (‖c1EuclideanDisagreementDirection‖ * ‖z‖) * ‖c1EuclideanDisagreementDirection‖ :=
          mul_le_mul_of_nonneg_right h1 hd0
      _ = ‖c1EuclideanDisagreementDirection‖ ^ 2 * ‖z‖ := by ring
      _ = 2 * ‖z‖ := by rw [hd]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  nlinarith

/-- 定理21 (21.3) の V₀ を共有基礎評価で読んだときの条件。球 `B̄_r(0)`、`0<r<1/4`。 -/
structure SharedBaseBackground21 (N : SharedModelSignature) : Prop where
  c2 : ∀ r : ℝ, r < 1 / 4 → ∀ z ∈ Metric.closedBall (0 : C1EuclideanAgentState) r,
    ContDiffAt ℝ 2 (fun w => N.base.V0 (c1EuclideanCoordinates w) 0) z
  gradient : ∀ r : ℝ, r < 1 / 4 → ∀ z ∈ Metric.closedBall (0 : C1EuclideanAgentState) r,
    HasGradientAt (fun w => N.base.V0 (c1EuclideanCoordinates w) 0) (baseHessian21 z) z
  gradient_deriv : ∀ z, HasFDerivAt (fun w => baseHessian21 w) baseHessian21 z
  gradient_bound : ∀ r : ℝ, r < 1 / 4 → ∀ z ∈ Metric.closedBall (0 : C1EuclideanAgentState) r,
    ‖baseHessian21 z‖ ≤ 8 * r
  hessian_lower : ∀ w : C1EuclideanAgentState, -(0 : ℝ) * ‖w‖ ^ 2 ≤ inner ℝ (baseHessian21 w) w

theorem SharedModelSignature.sharedBaseBackground21 (N : SharedModelSignature)
    (hd : SharedBaseDomain N) : SharedBaseBackground21 N where
  c2 := fun r hr z hz => by
    have hint := closedBall_subset_interior_box hr hz
    have hev := hd.extension_eq_near_interior z hint
    have hsm : ContDiff ℝ 2 sharedT20V0 := by
      have hin : ContDiff ℝ 2 (fun x : C1EuclideanAgentState =>
          inner ℝ c1EuclideanDisagreementDirection x) :=
        (innerSL ℝ c1EuclideanDisagreementDirection).contDiff
      unfold sharedT20V0 c1EuclideanSymbolDistance
      exact contDiff_const.add (contDiff_const.mul (contDiff_const.mul (hin.pow 2)))
    refine (hsm.contDiffAt).congr_of_eventuallyEq ?_
    rw [theorem20BaseExtension_eq] at hev
    exact hev.symm
  gradient := fun r hr z hz => by
    have hint := closedBall_subset_interior_box hr hz
    have hev := hd.extension_eq_near_interior z hint
    rw [theorem20BaseExtension_eq] at hev
    rw [← baseGradient21_eq]
    exact (sharedT20V0_hasGradientAt z).congr_of_eventuallyEq hev.symm
  gradient_deriv := fun z => baseHessian21.hasFDerivAt
  gradient_bound := fun r hr z hz => by
    have hz' : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    exact (baseHessian21_bound z).trans (by linarith)
  hessian_lower := fun w => by
    have := baseHessian21_psd w
    simpa using this

theorem sharedModel_baseBackground21 : SharedBaseBackground21 sharedModel :=
  sharedModel.sharedBaseBackground21 sharedModel_baseDomain

/-- 21/22 の状態空間 `LiftedStageState` は定理20と同じ Euclid 空間 `EuclideanSpace ℝ (Fin 2)`。 -/
example : Tomabechi.Consistency.R1.LiftedStageState = C1EuclideanAgentState := rfl

/-- 最終存在宣言 v2 に、V₀ を共有基礎評価と読んだ (21.3) の充足を加えた存在宣言。 -/
theorem final_consistency_v2_with_base_background21 :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N := by
  obtain ⟨N, h1, h2, h3⟩ := final_consistency_model_exists_v2
  exact ⟨N, h1, h2, h3, N.sharedBaseBackground21 h2.baseDomain⟩

#print axioms SharedModelSignature.sharedBaseBackground21
#print axioms final_consistency_v2_with_base_background21
end Tomabechi.Consistency.R123
