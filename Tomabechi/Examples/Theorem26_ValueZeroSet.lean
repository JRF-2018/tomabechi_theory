import Theorem24_26_Model

/-!
# 定理26の Python 例 (`examples/theorem26_value_zero_set.py`) の Lean 根拠

Python 例は `ẋ = -λx` (λ=1)、最高抽象度の走行コスト `3x²`、割引率 ρ=1、空未満の走行コスト 1 の
スカラーモデルを使う。これは `Theorem24_26_Model` のモデルと**同一パラメータ**なので、
ここでは新しい証明をせず、Python の各数値・主張が既存モデルの宣言から出ることを対応づける。

* L0 定義対応: `Theorem24_26_Model.flow/runningCost/value/lowerValue` が Python の
  `x(t)=x0 e^{-λt}`、`V⊤=3x²`、`J*`、`J*_a` に対応する。
* L1/L2: `J*⊤(x0)=x0²`（x0 ∈ {0, ½, 1, 2}）、空未満 `J*_a=1/ρ=1`、零苦集合 `{0}`、
  (26.2) の指数評価。
* L3: θ=¾ の劣位集合 `{3x²≤θ}` の境界 x=½ でも `J*>0`（有界化であって滅尽ではない）。

証明対象は Python の数値出力ではなく、モデルが定理26の条件を満たし結論が従うことである。
-/

namespace Tomabechi.Examples.Theorem26

open Tomabechi.Theorem24_26_Model

/-- Python の `J_top = [J(x0) for x0 in [0, 0.5, 1, 2]]` の厳密値 `x0²`（T=0）。 -/
theorem J_top_values :
    value 0 0 = 0 ∧ value (1 / 2) 0 = 1 / 4 ∧ value 1 0 = 1 ∧ value 2 0 = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [value_eq_sq]; norm_num)

/-- Python の `J_sub`（空未満の層、走行コスト1、ρ=1）は常に `1 = 1/ρ > 0`。 -/
theorem J_sub_value (T : ℝ) : lowerValue T = 1 ∧ 0 < lowerValue T := by
  have h := lowerValue_eq_one T
  exact ⟨h, by rw [h]; norm_num⟩

/-- Python の零苦集合 `N⊤={0}`（最高抽象度）。 -/
theorem top_zero_target (T : ℝ) : zeroTarget T = ({0} : Set ℝ) :=
  zeroTarget_eq_singleton T

/-- 条件26-Aが各 (x,T,s) で成立する（Python の W=x²、c1=c2=1、λ_W=2）。 -/
alias condition26A := concrete_condition26A

/-- (26.2) の指数評価。Python の `bound=W0 e^{-λ_W t}`、`dist_bound=√W0 e^{-λ_W t/2}`（T=0）。 -/
theorem exponential_bounds (x s : ℝ) (hs : 0 ≤ s) :
    WAlong x 0 s ≤ x ^ 2 * Real.exp (-2 * s) ∧
      Metric.infDist (flow x 0 s) (zeroTarget s) ≤ |x| * Real.exp (-s) := by
  have h := model_theorem26_exponential_convergence x 0 s hs
  have hW0 : WAlong x 0 0 = x ^ 2 := by simp [WAlong, lyapunov, flow]
  rw [hW0] at h
  refine ⟨by simpa using h.1, ?_⟩
  have h2 := h.2
  rw [Real.sqrt_sq_eq_abs] at h2
  convert h2 using 2 <;> ring_nf

/-- 有界化と滅尽の違い: θ=¾ の劣位集合 `{3x²≤θ}` の境界 x=½ は、走行コストが θ 以下
だが `J*=¼>0`。零苦集合 `{0}` には入っていない。 -/
theorem bounded_but_not_extinguished :
    3 * (1 / 2 : ℝ) ^ 2 = 3 / 4 ∧ value (1 / 2) 0 = 1 / 4 ∧ 0 < value (1 / 2) 0 ∧
      (1 / 2 : ℝ) ∉ zeroTarget 0 := by
  refine ⟨by norm_num, (J_top_values).2.1, by rw [(J_top_values).2.1]; norm_num, ?_⟩
  rw [zeroTarget_eq_singleton]
  norm_num

end Tomabechi.Examples.Theorem26
