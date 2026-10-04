import Theorem15

/-!
# 定理15の Python 例 (`examples/theorem15_entropy_exchange.py`) の Lean 根拠

有限6層（`Fin 6`）、換算重み `w_k=2^{-k}`、意味エントロピー `H_k(t)=2+sin(0.7(k+1)t)`、
散逸 `Π` は (a) `Π≡0`（理想閉鎖可逆系）、(b) `Π(t)=½(1+sin t)≥0`。物理エントロピーは
A7 の交換式をそのまま積分して定義: `S_phys(z)=5+∫₀^z (-Σ w_k H_k' + Π)`。

一般定理 `Tomabechi.Theorem15.theorem15_finite_layer_integral_balance`（A2/A5/A6′(有限層は自明)/A7 →
積分収支）の前提を全て証明して適用する。
* (I) `S_gen(b)-S_gen(a)=∫_a^b Π ≥ 0`（一般化第二法則）
* (II) `Π≡0` なら `S_gen` は定数、ただし `S_phys` 単独は定数でない（`S_phys'(0)=-21/8`）
* (III) 秩序化量の上界 `Σ w[H(a)-H(b)] ≤ S_phys(b)-S_phys(a)`

注意: Python 例の位相は `+k` から `0` に変更した（`t=0` での微分が有理数で、非保存性が示せるため）。
可算無限層での A6′(ii) の欠如（高木型反例）は本ファイルの対象外（未着手、対応表に記載）。
-/

namespace Tomabechi.Examples.Theorem15

open MeasureTheory intervalIntegral

/-- 連続な導関数をもつ関数は（任意の区間で）絶対連続。 -/
theorem ac_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hc : Continuous f') (a b : ℝ) : AbsolutelyContinuousOnInterval f a b := by
  have hint : IntervalIntegrable f' volume a b := hc.intervalIntegrable a b
  have hrep : ∀ t, f t = f a + ∫ v in a..t, f' v := by
    intro t
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hc.intervalIntegrable a t)]
    ring
  have h1 := hint.absolutelyContinuousOnInterval_intervalIntegral (Set.left_mem_uIcc (a := a) (b := b))
  have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  have h3 := h2.add h1
  exact h3.congr (fun t _ => by simp [hrep t])

/-- Python の層周波数 `0.7(k+1)`。 -/
noncomputable def freq (k : Fin 6) : ℝ := 7 / 10 * ((k : ℕ) + 1)
/-- 意味エントロピー `H_k(t)=2+sin(freq_k t)`。 -/
noncomputable def H (k : Fin 6) (t : ℝ) : ℝ := 2 + Real.sin (freq k * t)
/-- `dH_k/dt`。 -/
noncomputable def dH (k : Fin 6) (t : ℝ) : ℝ := freq k * Real.cos (freq k * t)
/-- 換算重み `w_k=2^{-k}`。 -/
noncomputable def w (k : Fin 6) : ℝ := (1 / 2 : ℝ) ^ (k : ℕ)

theorem w_pos (k : Fin 6) : 0 < w k := by unfold w; positivity

theorem H_nonneg (k : Fin 6) (t : ℝ) : 0 ≤ H k t := by
  unfold H; linarith [Real.neg_one_le_sin (freq k * t)]

theorem hasDerivAt_H (k : Fin 6) (t : ℝ) : HasDerivAt (H k) (dH k t) t := by
  unfold H dH
  have h := ((hasDerivAt_id t).const_mul (freq k)).sin.const_add 2
  simpa [mul_comm] using h

theorem continuous_dH (k : Fin 6) : Continuous (dH k) := by
  unfold dH; fun_prop

/-- 認知側の総レート `Σ w_k H_k'`。 -/
noncomputable def cogRate (t : ℝ) : ℝ := ∑ k, w k * dH k t

theorem continuous_cogRate : Continuous cogRate := by
  unfold cogRate
  exact continuous_finset_sum _ fun k _ => continuous_const.mul (continuous_dH k)

/-- A7 の交換式から定まる物理エントロピーの変化率 `-Σ w_k H_k' + Π`。 -/
noncomputable def dSphys (Pr : ℝ → ℝ) (t : ℝ) : ℝ := -cogRate t + Pr t

/-- `S_phys(z)=5+∫₀^z dSphys`。 -/
noncomputable def Sphys (Pr : ℝ → ℝ) (z : ℝ) : ℝ := 5 + ∫ s in (0 : ℝ)..z, dSphys Pr s

theorem hasDerivAt_Sphys {Pr : ℝ → ℝ} (hPr : Continuous Pr) (t : ℝ) :
    HasDerivAt (Sphys Pr) (dSphys Pr t) t := by
  have hc : Continuous (dSphys Pr) := (continuous_cogRate.neg).add hPr
  have := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  exact this.const_add 5

/-- 一般化総エントロピー。 -/
noncomputable def Sgen (Pr : ℝ → ℝ) (z : ℝ) : ℝ := Sphys Pr z + ∑ k, w k * H k z

/-- 定理15 (I)(III): 任意の連続な `Π≥0` について交換収支が成り立つ。 -/
theorem balance {Pr : ℝ → ℝ} (hPr : Continuous Pr) (hnn : ∀ t, 0 ≤ Pr t) (a b : ℝ) (hab : a ≤ b) :
    Sgen Pr b - Sgen Pr a = ∫ t in a..b, Pr t ∧ 0 ≤ ∫ t in a..b, Pr t := by
  have hPr' : ∀ t, deriv (fun u => Sphys Pr u) t = -(∑ k, w k * deriv (fun u => H k u) t) + Pr t := by
    intro t
    rw [(hasDerivAt_Sphys hPr t).deriv]
    simp only [dSphys, cogRate, (hasDerivAt_H _ t).deriv]
  have := Tomabechi.Theorem15.theorem15_finite_layer_integral_balance
    (Layer := Fin 6) (State := ℝ) (Sphys Pr) H w w_pos (fun k z => H_nonneg k z) id a b hab
    (fun k => ac_of_hasDerivAt (hasDerivAt_H k) (continuous_dH k) a b)
    (ac_of_hasDerivAt (hasDerivAt_Sphys hPr) ((continuous_cogRate.neg).add hPr) a b)
    Pr
    (Filter.Eventually.of_forall fun t => by simpa using hPr' t)
    (Filter.Eventually.of_forall fun t => hnn t)
  simpa [Sgen] using this

/-- Python の `Π≡0`（理想閉鎖可逆系）: `S_gen` は厳密に一定。 -/
theorem closed_system_conserved (a b : ℝ) (hab : a ≤ b) :
    Sgen (fun _ => 0) b = Sgen (fun _ => 0) a := by
  have := (balance (Pr := fun _ => 0) continuous_const (fun _ => le_refl _) a b hab).1
  simp at this
  linarith

/-- 物理層単独は保存しない: `Π≡0` でも `S_phys'(0)=-Σ w_k freq_k = -21/8`、したがって定数でない。 -/
theorem sphys_not_conserved : ¬ ∀ t, Sphys (fun _ => 0) t = Sphys (fun _ => 0) 0 := by
  intro h
  have hd := hasDerivAt_Sphys (Pr := fun _ => 0) continuous_const 0
  have hconst : HasDerivAt (Sphys (fun _ => 0)) 0 0 := by
    have : Sphys (fun _ => 0) = fun _ => Sphys (fun _ => 0) 0 := funext h
    rw [this]; exact hasDerivAt_const 0 _
  have := hd.unique hconst
  have hval : dSphys (fun _ => 0) 0 = -(21 / 8 : ℝ) := by
    simp only [dSphys, cogRate, dH, freq, w, mul_zero, Real.cos_zero, mul_one]
    simp [Fin.sum_univ_succ]
    norm_num
  rw [hval] at this
  norm_num at this

/-- Python の `Π(t)=½(1+sin t)≥0`。 -/
noncomputable def Pi1 (t : ℝ) : ℝ := 1 / 2 * (1 + Real.sin t)

theorem Pi1_nonneg (t : ℝ) : 0 ≤ Pi1 t := by
  unfold Pi1; linarith [Real.neg_one_le_sin t]

theorem Pi1_continuous : Continuous Pi1 := by unfold Pi1; fun_prop

/-- 一般化第二法則 (3.7): `S_gen` は単調非減少。 -/
theorem Sgen_monotone (a b : ℝ) (hab : a ≤ b) : Sgen Pi1 a ≤ Sgen Pi1 b := by
  have := balance Pi1_continuous Pi1_nonneg a b hab
  linarith [this.1, this.2]

/-- 秩序化量の上界 (3.8): `Σ w[H(a)-H(b)] ≤ S_phys(b)-S_phys(a)`。 -/
theorem ordering_bound (a b : ℝ) (hab : a ≤ b) :
    ∑ k, w k * (H k a - H k b) ≤ Sphys Pi1 b - Sphys Pi1 a := by
  have := balance Pi1_continuous Pi1_nonneg a b hab
  have h2 : ∑ k, w k * (H k a - H k b) =
      ∑ k, w k * H k a - ∑ k, w k * H k b := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  simp only [Sgen] at this
  linarith [this.1, this.2]

end Tomabechi.Examples.Theorem15
