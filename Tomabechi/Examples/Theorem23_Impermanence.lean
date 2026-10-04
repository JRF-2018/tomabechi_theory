import Theorem15_23

/-!
# 定理23の Python 例 (`examples/theorem23_impermanence.py`) の Lean 根拠

(A) 非再帰: 完全状態 `z=(θ,e)∈ 円周×ℝ`、一般化総エントロピー `S(z)=e`、`z(t)=(t mod 2π, Π t)`。
    条件23-A（`Π>0` で任意の `t₁<t₂` に `∫Π>0`）のもとで `z(t₂)≠z(t₁)`（一般定理
    `Tomabechi.Theorem23.complete_state_never_repeats_of_strict_entropy_balance`）。
    `Π=0`（23-A なし）では `z(2π)=z(0)` で再帰する（反例側）。
(B) 段階TCZ: 二次谷 `Ṽ_n=(c/2)(x-x_n*)²` で、`x_n*∈TCZ_{n+1}(θ) ⇔ cδ²/2≤θ`。
    したがって `θ<cδ²/2`（原文の閾値条件）なら `TCZ_n≠TCZ_{n+1}`、`θ` が大きいと前段の中心が
    次段TCZに入る（Python の `in_TCZ_next`）。※段階入力全体（H-stage）を使う 23-B 一般核の
    適用は本ファイルの範囲外。
(C) 非Zeno: `T_n=1` なら `ΣT_n=∞`、`T_n=2^{-n}`（n≥1）なら `ΣT_n=1`（有限時刻に集積）。
-/

namespace Tomabechi.Examples.Theorem23

open scoped Topology

/-! ## (A) 非再帰 -/

abbrev Circle : Type := AddCircle (2 * Real.pi)

/-- Python の軌道 `z(t)=(t mod 2π, Π t)`（Π は散逸率）。 -/
noncomputable def orbit (Pi : ℝ) (t : ℝ) : Circle × ℝ := ((t : Circle), Pi * t)

/-- 一般化総エントロピー `S(z)=e`（第2成分）。 -/
def entropy (z : Circle × ℝ) : ℝ := z.2

/-- 条件23-A（`Π=c>0`）のもとで、どの `t₁<t₂` でも状態は元に戻らない。 -/
theorem nonrecurrence (c : ℝ) (hc : 0 < c) (t₁ t₂ : ℝ) (h : t₁ < t₂) :
    orbit c t₂ ≠ orbit c t₁ := by
  refine Tomabechi.Theorem23.complete_state_never_repeats_of_strict_entropy_balance
    entropy (orbit c) (fun _ => c) Set.univ ?_ ?_ t₁ t₂ (Set.mem_univ _) (Set.mem_univ _) h
  · intro a b _ _ hab
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    nlinarith
  · intro a b _ _ _
    simp only [entropy, orbit, intervalIntegral.integral_const, smul_eq_mul]
    ring

/-- `Π=0`（23-A なし）: 周期 `2π` で完全状態が戻る。 -/
theorem recurrence_without_dissipation : orbit 0 (2 * Real.pi) = orbit 0 0 := by
  have : ((2 * Real.pi : ℝ) : Circle) = ((0 : ℝ) : Circle) := by
    simpa using AddCircle.coe_period (2 * Real.pi)
  simp [orbit, this]

/-! ## (B) 段階TCZの不固定 -/

/-- 二次谷 `Ṽ(x)-Ṽ(x*) = (c/2)(x-x*)²` の部分準位集合 `{≤θ}`（Python では K を全空間とした簡約）。 -/
def tcz (c center θ : ℝ) : Set ℝ := {x | c / 2 * (x - center) ^ 2 ≤ θ}

/-- 前段の最小点 `x_n*` が次段TCZに入る ⇔ `cδ²/2 ≤ θ`（δ=段間距離）。 -/
theorem prev_center_mem_next_iff (c xn xn1 θ : ℝ) :
    xn ∈ tcz c xn1 θ ↔ c * (xn1 - xn) ^ 2 / 2 ≤ θ := by
  simp only [tcz, Set.mem_setOf_eq]
  constructor <;> intro h <;> nlinarith

/-- 原文の閾値 `θ<cδ²/2` なら `x_n*∉TCZ_{n+1}`、したがって `TCZ_n≠TCZ_{n+1}`（θ≥0 のとき）。 -/
theorem tcz_changes (c xn xn1 θ θ' : ℝ) (hθ : 0 ≤ θ') (hlt : θ < c * (xn1 - xn) ^ 2 / 2) :
    tcz c xn θ' ≠ tcz c xn1 θ := by
  intro heq
  have hmem : xn ∈ tcz c xn θ' := by simp [tcz]; exact hθ
  rw [heq, prev_center_mem_next_iff] at hmem
  linarith

/-- Python の数値（c=1, δ=1）: しきい値は `θ=½`。 -/
theorem python_threshold :
    ¬ ((0 : ℝ) ∈ tcz 1 1 (49 / 100)) ∧ (0 : ℝ) ∈ tcz 1 1 (1 / 2) := by
  constructor <;> simp [tcz] <;> norm_num

/-! ## (C) 非Zeno -/

/-- `T_n=2^{-n}` (n≥1) の切替時刻の和は 1（有限時刻に集積＝Zeno）。 -/
theorem zeno_total : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
  have h := hasSum_geometric_two' (1 : ℝ)
  convert h using 1
  funext n
  simp [pow_succ, div_eq_mul_inv, mul_comm]

/-- `T_n=1` の和は発散（非Zeno: 切替は有限時刻に集積しない）。 -/
theorem nonzeno_total : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro h
  have := h.tendsto_atTop_zero
  have h1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1) := tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique h1 this)

end Tomabechi.Examples.Theorem23
