import Theorem22_InvariantRegion_Model

/-!
# 定理22/H-stage 不変領域の Python 例 (`examples/theorem22_h_stage_invariant_region.py`) の Lean 根拠

Python 例は `Ṽ(x)=x/2+x²/2`、局所球 `U=[-1,1]`、閉ループ `ẋ=-(x+½)`、初期点 `x0=½` の1次元モデルで、
`Theorem22_InvariantRegion_Model.lean` の `toy*` と**同一**である。ここでは Python が確認する各項目を
既存宣言へ対応づけ、Python の厳密解 `x(t)=x*+(x0-x*)e^{-t}` が閉ループ方程式を解くこと、
およびその上での `Ṽ(x(t))-Ṽ(x*)=e^{-2t}(Ṽ(x0)-Ṽ(x*))` を追加する。

これは範囲拡張の例（旧入力は不成立・緩和入力は成立）であり、原文定理22の反例ではない。
-/

namespace Tomabechi.Examples.Theorem22HStage

open Tomabechi.Theorem22InvariantRegionModel

/-- Python の `sub=(x*-s, x*+s)=(-3/2, 1/2)`: 端点で `Ṽ` が等しく、左端は球 `[-1,1]` の外。 -/
theorem old_sublevel_endpoints :
    toyPotential (-(3 / 2 : ℝ)) = toyPotential (1 / 2) ∧
      (-(3 / 2 : ℝ)) ∉ Metric.closedBall (0 : ℝ) 1 := by
  refine ⟨by norm_num [toyPotential, toyBackground, toyMeanField], ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  norm_num

/-- 旧入力（初期の全部分準位が球内部障壁を満たす）は不成立。 -/
alias old_input_fails := toy_old_sublevel_barrier_fails

/-- Python の `invariant`: 端点で閉ループ場が内向き（`field(-½)=0≥0`, `field(½)=-1≤0`）。 -/
theorem invariant_interval_inward :
    0 ≤ toyClosedLoopField (-(1 / 2 : ℝ)) ∧ toyClosedLoopField (1 / 2 : ℝ) ≤ 0 := by
  norm_num [toyClosedLoopField]

/-- Python の `I_inside_ball`: 新しい不変区間の閉包は球の内部。 -/
alias new_interval_inside_ball := toy_invariant_region_closure_inside_ball

/-- 前向き不変性（一般の解に対して）。 -/
alias new_interval_forward_invariant := toy_closed_loop_interval_invariant

/-- Python の厳密解 `x(t)=x*+(x0-x*)e^{-t}`（x*=-½, x0=½）は `ẋ=-(x+½)` を解き、初期値 `½`。 -/
theorem exact_solution (t : ℝ) :
    HasDerivAt (fun s : ℝ => -(1 / 2 : ℝ) + Real.exp (-s))
      (toyClosedLoopField (-(1 / 2 : ℝ) + Real.exp (-t))) t ∧
      (-(1 / 2 : ℝ) + Real.exp (-0)) = 1 / 2 := by
  refine ⟨?_, by norm_num⟩
  have h : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    exact (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) |>.congr_deriv (by ring)
  have h2 := h.const_add (-(1 / 2 : ℝ))
  convert h2 using 1
  simp [toyClosedLoopField]

/-- Python の `gap = V(x(t))-V(x*) = e^{-2t}(V(x0)-V(x*))` の厳密式。 -/
theorem potential_gap_decay (t : ℝ) :
    toyPotential (-(1 / 2 : ℝ) + Real.exp (-t)) - toyPotential (-(1 / 2 : ℝ)) =
      Real.exp (-2 * t) * (toyPotential (1 / 2) - toyPotential (-(1 / 2 : ℝ))) := by
  rw [toy_potential_square_completion, toy_potential_square_completion,
    toy_potential_square_completion]
  have h : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h]
  ring

/-- 一般定理（緩和 H-stage 入力→定量軌道）がこのモデルで成立する。 -/
alias general_quantitative_orbit := toy_model_has_general_quantitative_orbit

end Tomabechi.Examples.Theorem22HStage
