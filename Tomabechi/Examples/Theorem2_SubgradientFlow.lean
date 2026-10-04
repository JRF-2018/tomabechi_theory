import Tomabechi.Examples.Theorem2_SharedTCZ
import Mathlib.Analysis.Calculus.MeanValue

/-!
# 定理2の共有残差に対する実際の劣勾配流

Python例のケースAで使う初期値 `(2,-2)` とゲイン20を保ち、共有残差 `Φ₂` の選択劣勾配流を
解析式で定義する。選んだ劣勾配とのa.e.流れ方程式、軌道上の指数減衰、既存定理2の定量結論への接続を証明する。
-/

noncomputable section

set_option maxHeartbeats 2000000

namespace Tomabechi.Examples.Theorem2SubgradientFlow

open Tomabechi.Examples.Theorem2
open Tomabechi.Theorem2
open MeasureTheory
open Filter

/-- hinge項の閾値での正の平方根。 -/
def r : ℝ := Real.sqrt θ

/-- 閾値を横切る時刻。 -/
def τ : ℝ := Real.log (2 / r) / 200

/-- 対称軌道の一成分。閾値の前は率200、後は率160で指数減衰する。 -/
def y (t : ℝ) : ℝ := 2 * Real.exp (-(160 * t + 40 * min t τ))

/-- Python例の連続時間劣勾配流の候補軌道。 -/
def traj (t : ℝ) : ∀ i, (DA).State i := ![y t, -y t]

/-- 軌道上の共有残差。 -/
def Phi (t : ℝ) : ℝ := 2 * max (y t ^ 2 - θ) 0 + 8 * y t ^ 2

/-- hinge `max (x²-θ) 0` に対する、閾値上だけ勾配を取る選択劣勾配。 -/
def hingeGrad (x : ℝ) : ℝ := if θ < x ^ 2 then 2 * x else 0

/-- 共有残差の選択劣勾配。 -/
def residualGrad (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![hingeGrad (x 0) + 4 * (x 0 - x 1), hingeGrad (x 1) - 4 * (x 0 - x 1)]

/-- `y` の指数部を表す、切替後に傾きが変わる関数。 -/
def q (t : ℝ) : ℝ := 160 * t + 40 * min t τ

theorem r_sq : r ^ 2 = θ := by
  rw [r]
  exact Real.sq_sqrt (by unfold θ; norm_num)

theorem r_pos : 0 < r := by
  rw [r]
  exact Real.sqrt_pos.2 (by unfold θ; norm_num)

theorem tau_pos : 0 < τ := by
  have hratio : 1 < 2 / r := by
    have hs : r ^ 2 = 1 / 10 := by simpa [θ] using r_sq
    rw [lt_div_iff₀ r_pos]
    nlinarith [hs]
  unfold τ
  exact div_pos (Real.log_pos hratio) (by norm_num)

theorem min_eq_left_of_le {t : ℝ} (h : t ≤ τ) : min t τ = t := min_eq_left h
theorem min_eq_right_of_le {t : ℝ} (h : τ ≤ t) : min t τ = τ := min_eq_right h

theorem y_before (t : ℝ) (ht : t ≤ τ) : y t = 2 * Real.exp (-200 * t) := by
  rw [y, min_eq_left_of_le ht]
  congr 1
  ring_nf

theorem y_after (t : ℝ) (ht : τ ≤ t) : y t = r * Real.exp (-160 * (t - τ)) := by
  rw [y, min_eq_right_of_le ht]
  rw [show -(160 * t + 40 * τ) = -160 * (t - τ) + (-200 * τ) by ring, Real.exp_add]
  have he : Real.exp (-200 * τ) = r / 2 := by
    rw [τ]
    have hr : 0 < r := r_pos
    rw [show -200 * (Real.log (2 / r) / 200) = -Real.log (2 / r) by field_simp,
      Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [he]
  ring_nf

theorem y_zero : y 0 = 2 := by
  rw [y, min_eq_left (le_of_lt tau_pos)]
  simp

theorem traj_zero : traj 0 = x0 := by
  funext i
  fin_cases i <;> simp [traj, x0, y_zero]

theorem y_nonneg (t : ℝ) : 0 ≤ y t := by
  rw [y]
  positivity

theorem y_sq_le_four (t : ℝ) (ht0 : 0 ≤ t) : y t ^ 2 ≤ 4 := by
  rw [y]
  have hq : 0 ≤ 160 * t + 40 * min t τ := by
    by_cases ht : t ≤ τ
    · rw [min_eq_left ht]
      positivity
    · rw [min_eq_right (le_of_not_ge ht)]
      have htτ : τ ≤ t := le_of_not_ge ht
      have hτ := le_of_lt tau_pos
      nlinarith
  have he : Real.exp (-(160 * t + 40 * min t τ)) ≤ 1 :=
    (Real.exp_le_one_iff.mpr (by linarith)).trans (by norm_num)
  nlinarith [Real.exp_pos (-(160 * t + 40 * min t τ))]

theorem q_lipschitz : LipschitzWith 200 q := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hm := (LipschitzWith.id.min_const τ).dist_le_mul s t
  have hdiff : q s - q t = 160 * (s - t) + 40 * (min s τ - min t τ) := by
    simp [q]; ring
  rw [Real.dist_eq, Real.dist_eq] at hm ⊢
  rw [hdiff]
  calc |160 * (s - t) + 40 * (min s τ - min t τ)|
      ≤ |160 * (s - t)| + |40 * (min s τ - min t τ)| := abs_add_le _ _
    _ = 160 * |s - t| + 40 * |min s τ - min t τ| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 160), abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 40)]
    _ ≤ 160 * |s - t| + 40 * |s - t| := by
      have hm' : |min s τ - min t τ| ≤ |s - t| := by simpa using hm
      nlinarith [hm']
    _ = 200 * |s - t| := by ring

theorem exp_lipschitzOn_Iic : LipschitzOnWith 1 Real.exp (Set.Iic (0:ℝ)) := by
  refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (s := Set.Iic (0:ℝ)) (f := Real.exp) (C := 1)
    ?_ ?_ (convex_Iic 0)
  · intro x hx
    exact Real.differentiableAt_exp
  · intro x hx
    rw [Real.deriv_exp, Real.nnnorm_of_nonneg (Real.exp_pos x).le]
    have he : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
    exact_mod_cast he

theorem q_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ q t := by
  unfold q
  by_cases h : t ≤ τ
  · rw [min_eq_left h]
    positivity
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith [tau_pos]

theorem y_ac (T : ℝ) (hT : 0 ≤ T) : AbsolutelyContinuousOnInterval y 0 T := by
  apply (LipschitzOnWith.of_dist_le_mul (K := 400) (f := y) (s := Set.uIcc 0 T) ?_).absolutelyContinuousOnInterval
  intro s hs t ht
  have hs0 : 0 ≤ s := by
    rcases Set.mem_uIcc.mp hs with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · linarith [hT]
  have ht0 : 0 ≤ t := by
    rcases Set.mem_uIcc.mp ht with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · linarith [hT]
  have hmaps : -q s ∈ Set.Iic (0:ℝ) ∧ -q t ∈ Set.Iic (0:ℝ) := by
    constructor <;> apply Set.mem_Iic.mpr <;> linarith [q_nonneg s hs0, q_nonneg t ht0]
  have hex := exp_lipschitzOn_Iic.dist_le_mul (-q s) hmaps.1 (-q t) hmaps.2
  have hq := q_lipschitz.dist_le_mul s t
  rw [Real.dist_eq, Real.dist_eq, y, y]
  calc |2 * Real.exp (-q s) - 2 * Real.exp (-q t)|
      = 2 * |Real.exp (-q s) - Real.exp (-q t)| := by rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num)]
    _ ≤ 2 * |(-q s) - (-q t)| := by
      have hneg : |(-q s) - (-q t)| = |q s - q t| := by rw [show (-q s) - (-q t) = -(q s-q t) by ring, abs_neg]
      have hex' : |Real.exp (-q s) - Real.exp (-q t)| ≤ |q s - q t| := by simpa [Real.dist_eq] using hex
      nlinarith [hex']
    _ ≤ 400 * |s - t| := by
      have hneg : |(-q s) - (-q t)| = |q s - q t| := by rw [show (-q s) - (-q t) = -(q s-q t) by ring, abs_neg]
      have hq' : |q s - q t| ≤ 200 * |s-t| := by simpa [Real.dist_eq] using hq
      rw [hneg]
      nlinarith [hq']

theorem Phi_ac (T : ℝ) (hT : 0 ≤ T) : AbsolutelyContinuousOnInterval Phi 0 T := by
  have hy := y_ac T hT
  have hsq := hy.mul hy
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => θ) 0 T :=
    (by fun_prop : ContDiff ℝ 1 (fun _ : ℝ => θ)).contDiffOn.absolutelyContinuousOnInterval
  have harg := hsq.sub hconst
  have hmax : LipschitzWith 1 (fun u : ℝ => max u 0) := by
    simpa using LipschitzWith.id.max_const (0:ℝ)
  have hhinge := hmax.comp_absolutelyContinuousOnInterval harg
  have h1 := hhinge.const_mul 2
  have h2 := hsq.const_mul 8
  convert h1.add h2 using 1 <;> ext t <;> simp [Phi, pow_two]

/-- 閾値の手前では、軌道の一成分は率200の微分方程式に従う。 -/
theorem y_hasDeriv_before (t : ℝ) (ht : t < τ) : HasDerivAt y (-200 * y t) t := by
  have hev : ∀ᶠ u in nhds t, u < τ := isOpen_Iio.mem_nhds (Set.mem_Iio.mpr ht)
  have heq : y =ᶠ[nhds t] fun u => 2 * Real.exp (-200 * u) := by
    filter_upwards [hev] with u hu
    exact y_before u hu.le
  have hid : HasDerivAt (fun u : ℝ => -200 * u) (-200) t := by
    simpa using (hasDerivAt_id t).const_mul (-200)
  have hexp := (Real.hasDerivAt_exp (-200 * t)).comp t hid
  have hder : HasDerivAt (fun u : ℝ => 2 * Real.exp (-200 * u))
      (2 * (Real.exp (-200 * t) * -200)) t := by
    have h := hexp.const_mul 2
    simpa only [Function.comp_apply] using h
  have h := hder.congr_of_eventuallyEq heq
  convert h using 1
  rw [y_before t ht.le]
  ring

theorem y_deriv_before (t : ℝ) (ht : t < τ) : deriv y t = -200 * y t :=
  (y_hasDeriv_before t ht).deriv

/-- 閾値の後では、軌道の一成分は率160の微分方程式に従う。 -/
theorem y_hasDeriv_after (t : ℝ) (ht : τ < t) : HasDerivAt y (-160 * y t) t := by
  have hev : ∀ᶠ u in nhds t, τ < u := isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ht)
  have heq : y =ᶠ[nhds t] fun u => r * Real.exp (-160 * (u - τ)) := by
    filter_upwards [hev] with u hu
    exact y_after u hu.le
  have hid : HasDerivAt (fun u : ℝ => -160 * (u - τ)) (-160) t := by
    simpa using (hasDerivAt_id t).sub_const τ |>.const_mul (-160)
  have hexp := (Real.hasDerivAt_exp (-160 * (t - τ))).comp t hid
  have hder : HasDerivAt (fun u : ℝ => r * Real.exp (-160 * (u - τ)))
      (r * (Real.exp (-160 * (t - τ)) * -160)) t := by
    have h := hexp.const_mul r
    simpa only [Function.comp_apply] using h
  have h := hder.congr_of_eventuallyEq heq
  convert h using 1
  rw [y_after t ht.le]
  ring

theorem y_deriv_after (t : ℝ) (ht : τ < t) : deriv y t = -160 * y t :=
  (y_hasDeriv_after t ht).deriv

theorem exp_neg200tau : Real.exp (-200 * τ) = r / 2 := by
  rw [τ]
  have hr : 0 < r := r_pos
  rw [show -200 * (Real.log (2 / r) / 200) = -Real.log (2 / r) by field_simp,
    Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

theorem y_gt_r_before (t : ℝ) (ht : t < τ) : r < y t := by
  rw [y_before t ht.le]
  have hex : Real.exp (-200 * τ) < Real.exp (-200 * t) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  rw [exp_neg200tau] at hex
  nlinarith [r_pos]

theorem y_le_r_after (t : ℝ) (ht : τ ≤ t) : y t ≤ r := by
  rw [y_after t ht]
  have he : Real.exp (-160 * (t - τ)) ≤ 1 :=
    (Real.exp_le_one_iff.mpr (by nlinarith)).trans (by norm_num)
  nlinarith [r_pos]

theorem y_lt_r_after (t : ℝ) (ht : τ < t) : y t < r := by
  rw [y_after t ht.le]
  have he : Real.exp (-160 * (t - τ)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hm := mul_lt_mul_of_pos_left he r_pos
  nlinarith [hm]

theorem Phi_eq_before (t : ℝ) (ht : t < τ) : Phi t = 10 * y t ^ 2 - 2 * θ := by
  have h := y_gt_r_before t ht
  have hr := r_sq
  have hnonneg := mul_nonneg (sub_nonneg.mpr h.le) (add_nonneg (y_nonneg t) r_pos.le)
  unfold Phi
  rw [max_eq_left (by nlinarith : 0 ≤ y t ^ 2 - θ)]
  ring

theorem Phi_eq_after (t : ℝ) (ht : τ ≤ t) : Phi t = 8 * y t ^ 2 := by
  have h := y_le_r_after t ht
  have hr := r_sq
  have hnonneg := mul_nonneg (sub_nonneg.mpr h) (add_nonneg (y_nonneg t) r_pos.le)
  unfold Phi
  rw [max_eq_right (by nlinarith : y t ^ 2 - θ ≤ 0)]
  ring

theorem Phi_deriv_before (t : ℝ) (ht : t < τ) : deriv Phi t = -4000 * y t ^ 2 := by
  have hy := y_hasDeriv_before t ht
  have hypos := y_gt_r_before t ht
  have hp : 0 < y t ^ 2 - θ := by nlinarith [mul_pos (sub_pos.mpr hypos) (add_pos r_pos (lt_trans r_pos hypos)), r_sq]
  have hcont : Continuous (fun u : ℝ => y u ^ 2 - θ) := by fun_prop [y, q]
  have hev := hcont.continuousAt.eventually (lt_mem_nhds hp)
  have heq : Phi =ᶠ[nhds t] fun u => 10 * y u ^ 2 - 2 * θ := by
    filter_upwards [hev] with u hu
    unfold Phi
    rw [max_eq_left (le_of_lt hu)]
    ring
  have hpow := hy.pow 2
  have hder : HasDerivAt (fun u : ℝ => 10 * y u ^ 2 - 2 * θ)
      (10 * (2 * y t * (-200 * y t))) t := by
    have h := (hpow.const_mul 10).sub_const (2 * θ)
    convert h using 1 <;> ring
  have h := hder.congr_of_eventuallyEq heq
  rw [h.deriv]
  ring

theorem Phi_deriv_after (t : ℝ) (ht : τ < t) : deriv Phi t = -2560 * y t ^ 2 := by
  have hy := y_hasDeriv_after t ht
  have hylt := y_lt_r_after t ht
  have hp : y t ^ 2 - θ < 0 := by
    have hsq : y t ^ 2 < r ^ 2 := by
      have hprod : 0 < (r - y t) * (r + y t) :=
        mul_pos (sub_pos.mpr hylt) (add_pos_of_pos_of_nonneg r_pos (y_nonneg t))
      nlinarith [hprod]
    rw [r_sq] at hsq
    linarith
  have hcont : Continuous (fun u : ℝ => y u ^ 2 - θ) := by fun_prop [y, q]
  have hev := hcont.continuousAt.eventually (gt_mem_nhds hp)
  have heq : Phi =ᶠ[nhds t] fun u => 8 * y u ^ 2 := by
    filter_upwards [hev] with u hu
    unfold Phi
    rw [max_eq_right (le_of_lt hu)]
    ring
  have hpow := hy.pow 2
  have hder : HasDerivAt (fun u : ℝ => 8 * y u ^ 2)
      (8 * (2 * y t * (-160 * y t))) t := by
    convert hpow.const_mul 8 using 1 <;> ring
  have h := hder.congr_of_eventuallyEq heq
  rw [h.deriv]
  ring

/-- 軌道上の残差は、切替時刻を除き `Φ' ≤ -2Φ` を満たす。 -/
theorem Phi_deriv_decay_ae (T : ℝ) :
    ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) T), deriv Phi s ≤ -2 * Phi s := by
  have hnull : volume ({τ} : Set ℝ) = 0 := measure_singleton τ
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hnull] with s hs _
  have hne : s ≠ τ := by simpa using hs
  rcases lt_or_gt_of_ne hne with hleft | hright
  · rw [Phi_deriv_before s hleft, Phi_eq_before s hleft]
    have hθ : 0 ≤ θ := by unfold θ; norm_num
    nlinarith
  · rw [Phi_deriv_after s hright, Phi_eq_after s hright.le]
    nlinarith [sq_nonneg (y s)]

theorem potential_traj (t : ℝ) : DA.potential (traj t) t = Phi t := by
  rw [potential_eq ![0, 0] (traj t) t]
  simp [traj, Phi, γ]
  ring

/-- hinge項について、選んだ値は凸劣勾配の支持不等式を満たす。 -/
theorem hingeGrad_support (x z : ℝ) :
    max (z ^ 2 - θ) 0 ≥ max (x ^ 2 - θ) 0 + hingeGrad x * (z - x) := by
  by_cases h : θ < x ^ 2
  · have hx : 0 ≤ x ^ 2 - θ := by linarith
    rw [show hingeGrad x = 2 * x by simp [hingeGrad, h], max_eq_left hx]
    have hz : z ^ 2 - θ ≤ max (z ^ 2 - θ) 0 := le_max_left _ _
    nlinarith [sq_nonneg (z - x)]
  · have hx : x ^ 2 - θ ≤ 0 := by push Not at h; linarith
    rw [show hingeGrad x = 0 by simp [hingeGrad, h], max_eq_right hx]
    have hz : 0 ≤ max (z ^ 2 - θ) 0 := le_max_right _ _
    nlinarith

/-- `residualGrad x` は具体共有残差の凸劣勾配である（支持不等式の形）。 -/
theorem residualGrad_support (x z : Fin 2 → ℝ) :
    (max (z 0 ^ 2 - θ) 0 + max (z 1 ^ 2 - θ) 0 + γ * (z 0 - z 1) ^ 2) ≥
      (max (x 0 ^ 2 - θ) 0 + max (x 1 ^ 2 - θ) 0 + γ * (x 0 - x 1) ^ 2) +
        ∑ i : Fin 2, residualGrad x i * (z i - x i) := by
  have h0 := hingeGrad_support (x 0) (z 0)
  have h1 := hingeGrad_support (x 1) (z 1)
  have hquad : (x 0 - x 1) ^ 2 * 2 +
      (4 * (x 0 - x 1)) * (z 0 - x 0) + (-4 * (x 0 - x 1)) * (z 1 - x 1) ≤
      2 * (z 0 - z 1) ^ 2 := by
    have := sq_nonneg ((z 0 - z 1) - (x 0 - x 1))
    nlinarith
  simp [residualGrad, γ, Fin.sum_univ_two]
  nlinarith

/-- 選択したベクトルは、定理2の共有ポテンシャルの凸劣勾配である。 -/
theorem residualGrad_is_subgradient (x : Fin 2 → ℝ) :
    ∀ z : Fin 2 → ℝ, DA.potential z 0 ≥ DA.potential x 0 +
      ∑ i : Fin 2, residualGrad x i * (z i - x i) := by
  intro z
  rw [potential_eq ![0, 0] z 0, potential_eq ![0, 0] x 0]
  simpa [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using
    residualGrad_support x z

/-- 切替前は、選択劣勾配流の両成分が活性ヒンジを含む勾配方程式に従う。 -/
theorem traj_flow_before (t : ℝ) (ht : t < τ) :
    ∀ i : Fin 2, deriv (fun s => traj s i) t = -20 * residualGrad (traj t) i := by
  have hy := y_deriv_before t ht
  have hypos := y_gt_r_before t ht
  have hact : θ < y t ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hypos) (add_pos r_pos (lt_trans r_pos hypos))
    nlinarith [hp, r_sq]
  intro i
  fin_cases i
  · change deriv y t = -20 * (hingeGrad (y t) + 4 * (y t - -y t))
    rw [hy]
    simp [hingeGrad, hact]
    ring
  · change deriv (fun s => -y s) t = -20 * (hingeGrad (-y t) - 4 * (y t - -y t))
    have hneg : HasDerivAt (fun s : ℝ => -y s) (200 * y t) t := by
      have hEq : (fun s : ℝ => -y s) =ᶠ[nhds t] (-y) := by filter_upwards with s; rfl
      have h := ((y_hasDeriv_before t ht).neg).congr_of_eventuallyEq hEq
      exact h.congr_deriv (by ring)
    rw [hneg.deriv]
    simp [hingeGrad, hact]
    ring

/-- 切替後はヒンジが非活性となり、二次の不整合項だけが流れを決める。 -/
theorem traj_flow_after (t : ℝ) (ht : τ < t) :
    ∀ i : Fin 2, deriv (fun s => traj s i) t = -20 * residualGrad (traj t) i := by
  have hy := y_deriv_after t ht
  have hylt := y_lt_r_after t ht
  have hnot : ¬ θ < y t ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hylt) (add_pos_of_pos_of_nonneg r_pos (y_nonneg t))
    nlinarith [hp, r_sq]
  intro i
  fin_cases i
  · change deriv y t = -20 * (hingeGrad (y t) + 4 * (y t - -y t))
    rw [hy]
    simp [hingeGrad, hnot]
    ring
  · change deriv (fun s => -y s) t = -20 * (hingeGrad (-y t) - 4 * (y t - -y t))
    have hneg : HasDerivAt (fun s : ℝ => -y s) (160 * y t) t := by
      have hEq : (fun s : ℝ => -y s) =ᶠ[nhds t] (-y) := by filter_upwards with s; rfl
      have h := ((y_hasDeriv_after t ht).neg).congr_of_eventuallyEq hEq
      exact h.congr_deriv (by ring)
    rw [hneg.deriv]
    simp [hingeGrad, hnot]
    ring

/-- 閾値の一点を除けば、全区間で軌道は選択劣勾配方程式を満たす。 -/
theorem traj_flow_ae (T : ℝ) :
    ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) T),
      ∀ i : Fin 2, deriv (fun s => traj s i) t = -20 * residualGrad (traj t) i := by
  have hnull : volume ({τ} : Set ℝ) = 0 := measure_singleton τ
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hnull] with t ht _
  have hne : t ≠ τ := by simpa using ht
  rcases lt_or_gt_of_ne hne with hbefore | hafter
  · exact traj_flow_before t hbefore
  · exact traj_flow_after t hafter

/-- 実際の劣勾配流から定理2の条件付き定量結論を得る。 -/
theorem subgradient_flow_conclusion (t : ℝ) (ht : 0 ≤ t) :
    (traj t ∈ (Set.univ : Set (∀ i, (DA).State i)) ∧
      Metric.infDist (traj t) (DA.sharedTCZ Set.univ t) ≤
        Real.sqrt (2 * DA.potential (traj 0) 0) * Real.exp (-1 * (t - 0))) ∧
    (∀ i, DA.individual i (traj t i) t ≤
      (DA.potential (traj 0) 0 / DA.individualWeight i) * Real.exp (-2 * 1 * (t - 0))) ∧
    (∀ e, DA.mismatch e (traj t (DA.endpoint e).1) (traj t (DA.endpoint e).2) t ≤
      (DA.potential (traj 0) 0 / DA.edgeWeight e) * Real.exp (-2 * 1 * (t - 0))) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) t, ∀ x ∈ DA.sharedTCZ Set.univ s, ∀ i j,
      DA.repr i (x i) = DA.repr j (x j)) := by
  refine DA.theorem2_state_pair_conditional_conclusion Set.univ traj connectedA 1 2 0 t
    one_pos two_pos ht (fun _ _ => trivial) (fun s _ => sharedTCZ_nonempty s) ?_ ?_
    (fun s _ => caseA_error_bound (traj s) s)
  · have hpot : (fun s => DA.potential (traj s) s) = Phi := funext potential_traj
    rw [hpot]
    exact Phi_ac t ht
  · have hpot : (fun s => DA.potential (traj s) s) = Phi := funext potential_traj
    rw [hpot]
    simpa only [potential_traj, mul_one] using Phi_deriv_decay_ae t

end Tomabechi.Examples.Theorem2SubgradientFlow

end
