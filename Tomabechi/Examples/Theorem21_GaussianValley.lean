import Tomabechi.Dynamics.Theorem21GlobalResults
import Tomabechi.Examples.Gaussian

/-!
# 定理21の Python 例 (`examples/theorem21_local_well.py`) の Lean 根拠

目標 `x_t=4` への浅い引力 `V0(x)=0.05 (x-4)²` と、偏った中心 `x_b=6` のガウス臨場感
`S(x)=exp(-(x-6)²/2)`（円環の局所チャート。`U_b=[5.5,6.5]` は対蹠点 `0 (mod 8)` から遠く、
`wrap` の特異点を踏まない）。`Ṽ=V0-κ p S`、`κ=1`。

**監査の結果（Python の旧パラメータは前提を満たさない）:** 旧 Python は `m=1`, `r=1.5`, `β=0.1`,
`B=0.3` を使い `p_crit≈0.2` としたが、ガウス核の `-S''=(1-d²)e^{-d²/2}` は `|d|<1` でしか正でなく、
(21.2) `-∇²S≽mI`（m=1）は `d=0` 以外で破れる。Lean が認める定数は
`r=1/2`, `m=1/2`（`-S''≥(3/4)e^{-1/8}≥21/32≥1/2`）、`β=0`（`V0''=0.1>0`）、`B=1/4`
（`|V0'|=|x-4|/10≤1/4`）、したがって `p_crit=max(β,B/r)/(κm)=1`。
Python 側を `r=0.5`, `m=0.5`, `B=0.25`, `p_crit=1` に直した。

結論: `p>1` で `U_b` 内部に唯一の最小点 `x*` があり、勾配流は `x*` へ指数収束
（一般定理 `theorem21_identity_mobility_global_exponential_case`）。
-/

namespace Tomabechi.Examples.Theorem21

open Tomabechi.Examples.Gaussian

/-- `V0(x)=0.05(x-4)²`。 -/
noncomputable def V (x : ℝ) : ℝ := 1 / 20 * (x - 4) ^ 2
noncomputable def gradV (x : ℝ) : ℝ := 1 / 10 * (x - 4)
/-- ガウス臨場感 `S(x)=exp(-(x-6)²/2)`。 -/
noncomputable def S (x : ℝ) : ℝ := -well 1 1 6 x
noncomputable def gradS (x : ℝ) : ℝ := -dwell 1 1 6 x
noncomputable def HS (x : ℝ) : ℝ →L[ℝ] ℝ := innerSL ℝ (-ddwell 1 1 6 x)
noncomputable def HV (_x : ℝ) : ℝ →L[ℝ] ℝ := innerSL ℝ (1 / 10 : ℝ)

theorem S_eq (x : ℝ) : S x = Real.exp (-(x - 6) ^ 2 / 2) := by
  simp [S, well]

theorem hasDerivAt_V (x : ℝ) : HasDerivAt V (gradV x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y - 4) 1 x := (hasDerivAt_id x).sub_const 4
  have h2 : HasDerivAt (fun y : ℝ => (y - 4) ^ 2) (2 * (x - 4)) x := by
    have := (hasDerivAt_pow 2 (x - 4)).comp x h1
    rw [show (2 * (x - 4) : ℝ) = (↑(2 : ℕ) * (x - 4) ^ (2 - 1) * 1) by norm_num]
    exact this
  have h := h2.const_mul (1 / 20)
  exact h.congr_deriv (by simp [gradV]; ring)

theorem hasDerivAt_gradV (x : ℝ) : HasDerivAt gradV (1 / 10) x := by
  have h := ((hasDerivAt_id x).sub_const 4).const_mul (1 / 10)
  exact h.congr_deriv (by simp)

theorem hasDerivAt_S (x : ℝ) : HasDerivAt S (gradS x) x :=
  (hasDerivAt_well 1 1 6 x one_ne_zero).neg

theorem hasDerivAt_gradS (x : ℝ) : HasDerivAt gradS (-ddwell 1 1 6 x) x :=
  (hasDerivAt_dwell 1 1 6 x one_ne_zero).neg

/-- `|x-6|≤1/2` で `ddwell ≥ 1/2`（`-S''≤-1/2`）。 -/
theorem ddwell_ge (x : ℝ) (hx : |x - 6| ≤ 1 / 2) : 1 / 2 ≤ ddwell 1 1 6 x := by
  unfold ddwell
  have hd : (x - 6) ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hx
    nlinarith
  have h1 : (3 : ℝ) / 4 ≤ 1 - (x - 6) ^ 2 / 1 ^ 2 := by norm_num; linarith
  have h2 : (7 : ℝ) / 8 ≤ Real.exp (-(x - 6) ^ 2 / (2 * 1 ^ 2)) := by
    have := Real.add_one_le_exp (-(x - 6) ^ 2 / (2 * 1 ^ 2))
    norm_num at this ⊢; linarith
  norm_num at h1 ⊢
  nlinarith [mul_le_mul h1 h2 (by norm_num) (by linarith)]

/-- Python のパラメータ（r=1/2, m=1/2, β=0, B=1/4, κ=1）の下で、`p>1=p_crit` なら
`U_b=[5.5,6.5]` 内部に唯一…（一般定理の結論）: 最小点の存在と、勾配流の指数収束。 -/
theorem python_valley (p : ℝ) (hp : 1 < p) (a x₀ : ℝ)
    (hx₀ : x₀ ∈ Metric.closedBall (6 : ℝ) (1 / 2)) :
    ∃ xstar ∈ interior (Metric.closedBall (6 : ℝ) (1 / 2)),
      IsMinOn (fun x => V x - 1 * p * S x) (Metric.closedBall (6 : ℝ) (1 / 2)) xstar ∧
      ∃ trajectory : ℝ → ℝ, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
        (∀ t ∈ Set.Ici a, trajectory t ∈ Metric.closedBall (6 : ℝ) (1 / 2)) ∧
        (∀ t ∈ Set.Ici a,
          0 ≤ (V (trajectory a) - 1 * p * S (trajectory a)) - (V xstar - 1 * p * S xstar) ∧
          (V (trajectory t) - 1 * p * S (trajectory t)) - (V xstar - 1 * p * S xstar) ≤
            ((V (trajectory a) - 1 * p * S (trajectory a)) - (V xstar - 1 * p * S xstar)) *
              Real.exp (-2 * (1 * p * (1 / 2) - 0) * (t - a)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((V (trajectory a) - 1 * p * S (trajectory a)) -
              (V xstar - 1 * p * S xstar)) / (1 * p * (1 / 2) - 0)) *
              Real.exp (-(1 * p * (1 / 2) - 0) * (t - a))) := by
  have hVsmooth : ContDiff ℝ 1 V := by unfold V; fun_prop
  have hSsmooth : ContDiff ℝ 1 S := by
    unfold S well; fun_prop
  have hgradS_smooth : ContDiff ℝ 1 gradS := by
    unfold gradS dwell; fun_prop
  have hgradV_smooth : ContDiff ℝ 1 gradV := by unfold gradV; fun_prop
  refine Tomabechi.Theorem21.theorem21_identity_mobility_global_exponential_case (E := ℝ) (6 : ℝ) (1 / 2) 1 p (1 / 2) 0 (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; linarith) V S gradV gradS HV HS hVsmooth.contDiffOn hSsmooth.contDiffOn
    (fun x _ => ?_) (fun x _ => ?_) (fun x _ => ?_) (fun x _ => ?_) (fun x _ v => ?_)
    (fun x hx v => ?_) ?_ (fun x hx => ?_) ?_ (fun x _ => ?_) a x₀ hx₀
  · convert (hasDerivAt_V x).hasFDerivAt using 1
    ext y; simp [gradV, innerSL_apply_apply]
  · convert (hasDerivAt_S x).hasFDerivAt using 1
    ext y; simp [gradS, innerSL_apply_apply]
  · convert (hasDerivAt_gradV x).hasFDerivAt using 1
    ext y; simp [HV, innerSL_apply_apply]
  · convert (hasDerivAt_gradS x).hasFDerivAt using 1
    ext y; simp [HS, innerSL_apply_apply]
  · simp [HV, innerSL_apply_apply, real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg v]
  · have hx' : |x - 6| ≤ 1 / 2 := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hx
    have := ddwell_ge x hx'
    simp only [HS, innerSL_apply_apply, real_inner_eq_re_inner]
    simp [real_inner_comm]
    nlinarith [sq_nonneg v]
  · simp [gradS, dwell]
  · have hx' : |x - 6| ≤ 1 / 2 := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hx
    have h := abs_le.mp hx'
    simp only [gradV, Real.norm_eq_abs]
    rw [abs_le]; constructor <;> nlinarith
  · have hfield : ContDiff ℝ 1 (fun y : ℝ => -(gradV y - (1 * p) • gradS y)) := by
      unfold gradV gradS dwell; fun_prop
    exact hfield.continuous
  · have hfield : ContDiff ℝ 1 (fun y : ℝ => -(gradV y - (1 * p) • gradS y)) := by
      unfold gradV gradS dwell; fun_prop
    exact hfield.contDiffAt

end Tomabechi.Examples.Theorem21
