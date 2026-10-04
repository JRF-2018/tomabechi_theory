import Theorem22
import Tomabechi.Examples.Gaussian

/-!
# 定理22の Python 例 (`examples/theorem22_lub_staircase.py`) の Lean 根拠（前提充足の範囲）

束 `𝕃 = Finset (Fin 8)`（Python のビット集合）、`u_{n+1}=u_n ∨ v_{n+1}` (22.1)、段 `n` の谷の
中心 `x_n=|u_n|`、ガウス谷 `Ṽ_n(x)=-A exp(-(x-x_n)²/(2σ²))`（A=2, σ=3/2）、局所球半径 `r=1`。

* (22.1)(22.3): 一般補題 `lub_update_is_strict` / `lub_update_strict_iff` を、Python の3列
  A（1要素ずつ）, B（6要素→2要素）, C（`v≤u_n` の入力が混じる）に適用し、各 `|u_n|` を確認。
* 局所強凸性: ガウス谷は `|x-x_n|<σ` で `Ṽ_n''>0`。`r=1<σ=3/2` の球上で `Ṽ_n''>0` を証明。
* 到達可能性: A（δ=1）では前段の終点が次段の局所球 `B(x_{n+1},r)` 内、B（δ=6）では球外。
  後者は、定理22の「切替状態が次段の吸引域に入る」前提が成り立たないことの例である。

範囲外: 段階列の ODE 解、時間尺度分離、一般の段階定理 (22.4)(22.5)、定理23-B 核の適用
（H-stage 入力の構成が必要）。Python の挙動の数値は証明しない。
-/

namespace Tomabechi.Examples.Theorem22Staircase

open Tomabechi.Theorem22 Tomabechi.Examples.Gaussian

/-! ## 束側: (22.1)(22.3) -/

abbrev L8 := Finset (Fin 8)

/-- A: 1要素ずつ。`u₀=∅`。 -/
def uA : ℕ → L8
  | 0 => ∅
  | 1 => {0}
  | 2 => {0, 1}
  | 3 => {0, 1, 2}
  | _ => {0, 1, 2, 3}

theorem A_cards : (List.range 5).map (fun n => (uA n).card) = [0, 1, 2, 3, 4] := by decide

theorem A_updates_strict :
    uA 0 < uA 0 ⊔ {0} ∧ uA 1 < uA 1 ⊔ {1} ∧ uA 2 < uA 2 ⊔ {2} ∧ uA 3 < uA 3 ⊔ {3} := by
  refine ⟨lub_update_is_strict _ _ ?_, lub_update_is_strict _ _ ?_,
    lub_update_is_strict _ _ ?_, lub_update_is_strict _ _ ?_⟩ <;> decide

/-- B: 6要素 `{0..5}` を一度に、次に `{6,7}`。 -/
def uB : ℕ → L8
  | 0 => ∅
  | 1 => {0, 1, 2, 3, 4, 5}
  | _ => Finset.univ

theorem B_cards : (List.range 3).map (fun n => (uB n).card) = [0, 6, 8] := by decide

/-- C: `v≤u_n` の入力（2回目の `{0}`）では `u_n` は増えない（`lub_update_strict_iff`）。 -/
def uC : ℕ → L8
  | 0 => ∅
  | 1 => {0}
  | 2 => {0}
  | _ => {0, 1}

theorem C_cards : (List.range 4).map (fun n => (uC n).card) = [0, 1, 1, 2] := by decide

theorem C_second_input_not_strict : ¬ (uC 1 < uC 1 ⊔ {0}) := by
  have hle : ({0} : L8) ≤ uC 1 := by decide
  have := lub_update_strict_iff (uC 1) ({0} : L8)
  intro h
  exact (this.1 h) hle

theorem C_first_and_third_strict :
    uC 0 < uC 0 ⊔ {0} ∧ uC 2 < uC 2 ⊔ {0, 1} := by
  refine ⟨lub_update_is_strict _ _ ?_, lub_update_is_strict _ _ ?_⟩ <;> decide

/-! ## Python のパラメータ A=2, σ=3/2, r=1 -/

/-- Python の谷の中心 `x_n=|u_n|`（A 列）。 -/
def centerA (n : ℕ) : ℝ := ((uA n).card : ℝ)
/-- B 列。 -/
def centerB (n : ℕ) : ℝ := ((uB n).card : ℝ)

/-- 各段の谷は `r=1<σ=3/2` の球で強凸。 -/
theorem python_well_strongly_convex (c x : ℝ) (hx : |x - c| ≤ 1) :
    0 < ddwell 2 (3 / 2) c x :=
  ddwell_pos (r := 1) (by norm_num) (by norm_num) (by norm_num) hx

/-- A（δ=1）: 前段の終点（中心 `x_n`）は次段の局所球 `B(x_{n+1},1)` の中。 -/
theorem A_switch_state_in_next_ball :
    ∀ n ∈ Finset.range 4, |centerA n - centerA (n + 1)| ≤ 1 := by
  intro n hn
  simp only [Finset.mem_range] at hn
  interval_cases n <;> norm_num [centerA, uA]

/-- B（δ=6）: 前段の終点（中心 0）は次段の局所球 `B(6,1)` の外。
定理22の「切替状態が次段の吸引域に入る」前提が成り立たない。 -/
theorem B_switch_state_outside_next_ball : ¬ |centerB 0 - centerB 1| ≤ 1 := by
  norm_num [centerB, uB]

end Tomabechi.Examples.Theorem22Staircase
