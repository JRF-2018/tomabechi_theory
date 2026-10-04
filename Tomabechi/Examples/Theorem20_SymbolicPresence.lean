import Theorem20

/-!
# 定理20の Python 例 (`examples/theorem20_symbolic_presence.py`) の Lean 根拠

一般の実内積空間 `E`（Python は `E=ℝ²`）で、目標集合 `Z=closedBall u R`、基礎評価
`V0(y)=½‖y-v‖²`、`P≡1`、距離型関数 `D(y)=¼[(‖y-u‖²-R²)₊]²`、`s(D)=-D`（`s'=-1`）、
`ẋ=-∇(V0 - κq P s(D))=-∇(V0 + K D)`（`M=id`、`κ=K`、`q=1`）。

* ケースA（`v∈Z`、すなわち `‖u-v‖≤R`）: 一般定理
  `theorem20_full_trajectory_conclusion_of_original_conditions` の全前提を示す。
  (20.A) は `b` 任意（`b>0`）で成立し、(20.B) は `b+c≤K`、PL は `μ=2R²`、誤差境界は `C=1/R`。
* ケースB（`v∉Z`）: 具体的な `E=ℝ²`、`u=(2,0)`、`v=0`、`R=½`、`K=4/3` で、停留点 `x*=(1,0)`
  （`x*∉Z`）を厳密に与え、同じ ODE の定常解が結論 (20.1)/(20.2) を満たさないこと、および
  (20.A)(20.B) を同時に満たす `b,c>0` が存在しないことを証明する。

注意: Python の旧 D（`½dist²`）は境界での勾配構成が重いので、`C¹` で多項式勾配をもつ
距離型関数 `¼[(‖·-u‖²-R²)₊]²` に置き換えた（原文は `D=0⇔x∈Z` の距離型関数を要求するだけ）。
-/

namespace Tomabechi.Examples.Theorem20

open scoped Gradient RealInnerProductSpace
open Tomabechi.Theorem20
open Filter Topology

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `t ↦ (max t 0)²` は `C¹`、導関数 `2 max t 0`。 -/
theorem hasDerivAt_sqPos (t : ℝ) :
    HasDerivAt (fun x : ℝ => (max x 0) ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have h : (fun x : ℝ => (max x 0) ^ 2) =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with x hx
      simp [max_eq_right (Set.mem_Iio.mp hx).le]
    have := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq h
    simpa [max_eq_right ht.le] using this
  · subst ht
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hbound : ∀ h : ℝ, ‖(max (0 + h) 0) ^ 2 - (max (0 : ℝ) 0) ^ 2 - h • (2 * max (0 : ℝ) 0)‖ ≤ ‖h ^ 2‖ := by
      intro h
      simp only [zero_add, max_self, smul_eq_mul, mul_zero, sub_zero, norm_pow, Real.norm_eq_abs]
      rcases le_total h 0 with hh | hh
      · simp [max_eq_right hh]
        positivity
      · simp [max_eq_left hh]
    have h2 : (fun h : ℝ => h ^ 2) =o[nhds 0] fun h => h := by
      simpa using Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)
    exact (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun h => by
      simpa using hbound h)).trans_isLittleO h2
  · have h : (fun x : ℝ => (max x 0) ^ 2) =ᶠ[nhds t] fun x => x ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      simp [max_eq_left (Set.mem_Ioi.mp hx).le]
    have := (hasDerivAt_pow 2 t).congr_of_eventuallyEq h
    simpa [max_eq_left ht.le] using this

/-- `y ↦ ½‖y-v‖²` の勾配は `y-v`。 -/
theorem hasGradientAt_halfNormSq [CompleteSpace E] (v y : E) :
    HasGradientAt (fun z : E => 1 / 2 * ‖z - v‖ ^ 2) (y - v) y := by
  have h := ((hasStrictFDerivAt_norm_sq (y - v)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).sub_const v)).const_mul (1 / 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine h.congr_fderiv ?_
  ext w
  simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]

variable [CompleteSpace E]

/-- 距離型関数 `D(y)=¼[(‖y-u‖²-R²)₊]²`（`D=0 ⇔ ‖y-u‖≤R`）。 -/
noncomputable def Dfun (u : E) (R : ℝ) (y : E) : ℝ := 1 / 4 * (max (‖y - u‖ ^ 2 - R ^ 2) 0) ^ 2

/-- `D` の勾配 `(‖y-u‖²-R²)₊ • (y-u)`。 -/
noncomputable def gradD (u : E) (R : ℝ) (y : E) : E := (max (‖y - u‖ ^ 2 - R ^ 2) 0) • (y - u)

theorem hasGradientAt_D (u : E) (R : ℝ) (y : E) :
    HasGradientAt (Dfun u R) (gradD u R y) y := by
  have hf : HasFDerivAt (fun z : E => ‖z - u‖ ^ 2 - R ^ 2) ((2 : ℝ) • innerSL ℝ (y - u)) y := by
    have h := ((hasStrictFDerivAt_norm_sq (y - u)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const u)).sub_const (R ^ 2)
    refine h.congr_fderiv ?_
    ext w; simp
  have hg := ((hasDerivAt_sqPos (‖y - u‖ ^ 2 - R ^ 2)).comp_hasFDerivAt y hf).const_mul (1 / 4)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hg.congr_fderiv ?_
  ext w
  simp [gradD, InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  ring

/-- `D ≥ 0`、かつ `D y = 0 ↔ y ∈ closedBall u R`（R>0）。 -/
theorem Dfun_nonneg (u : E) (R : ℝ) (y : E) : 0 ≤ Dfun u R y := by
  unfold Dfun; positivity

theorem Dfun_eq_zero_iff (u : E) {R : ℝ} (hR : 0 < R) (y : E) :
    Dfun u R y = 0 ↔ y ∈ Metric.closedBall u R := by
  unfold Dfun
  rw [Metric.mem_closedBall, dist_eq_norm]
  constructor
  · intro h
    have h1 : (max (‖y - u‖ ^ 2 - R ^ 2) 0) ^ 2 = 0 := by linarith
    have h2 : max (‖y - u‖ ^ 2 - R ^ 2) 0 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
    have h3 : ‖y - u‖ ^ 2 - R ^ 2 ≤ 0 := le_of_max_le_left h2.le
    nlinarith [norm_nonneg (y - u)]
  · intro h
    have : ‖y - u‖ ^ 2 - R ^ 2 ≤ 0 := by nlinarith [norm_nonneg (y - u)]
    simp [max_eq_right this]

/-- `‖∇D‖² = 4 D ‖y-u‖²`、ゆえに目標外（‖y-u‖≥R）で PL: `4R² D ≤ ‖∇D‖²`。 -/
theorem gradD_inner_self (u : E) (R : ℝ) (y : E) :
    inner ℝ (gradD u R y) (gradD u R y) = 4 * Dfun u R y * ‖y - u‖ ^ 2 := by
  unfold gradD Dfun
  rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
  simp
  ring

theorem PL_bound (u : E) {R : ℝ} (hR : 0 < R) (y : E) :
    2 * (2 * R ^ 2) * Dfun u R y ≤ inner ℝ (gradD u R y) (gradD u R y) := by
  rw [gradD_inner_self]
  by_cases h : ‖y - u‖ ^ 2 - R ^ 2 ≤ 0
  · have : Dfun u R y = 0 := by
      unfold Dfun; simp [max_eq_right h]
    simp [this]
  · have h := not_le.mp h
    have hD := Dfun_nonneg u R y
    have : R ^ 2 ≤ ‖y - u‖ ^ 2 := by linarith
    nlinarith

/-- 誤差境界: `infDist y Z ≤ (1/R) √D`。 -/
theorem error_bound (u : E) {R : ℝ} (hR : 0 < R) (y : E) :
    Metric.infDist y (Metric.closedBall u R) ≤ (1 / R) * Real.sqrt (Dfun u R y) := by
  by_cases h : ‖y - u‖ ≤ R
  · have hy : y ∈ Metric.closedBall u R := by rwa [Metric.mem_closedBall, dist_eq_norm]
    rw [Metric.infDist_zero_of_mem hy]
    positivity
  · have h' : R < ‖y - u‖ := not_le.mp h
    obtain ⟨r, hr⟩ : ∃ r, ‖y - u‖ = r := ⟨_, rfl⟩
    rw [hr] at h'
    have hrpos : 0 < r := hR.trans h'
    have hp : u + (R / r) • (y - u) ∈ Metric.closedBall u R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hrpos), hr]
      field_simp
      exact le_refl _
    have hdist : dist y (u + (R / r) • (y - u)) = r - R := by
      rw [dist_eq_norm]
      have : y - (u + (R / r) • (y - u)) = (1 - R / r) • (y - u) := by
        simp only [sub_smul, one_smul]; abel
      rw [this, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by rw [sub_nonneg, div_le_one hrpos]; exact h'.le), hr]
      field_simp
    have h1 := Metric.infDist_le_dist_of_mem (x := y) hp
    rw [hdist] at h1
    have hsq : Real.sqrt (Dfun u R y) = (r ^ 2 - R ^ 2) / 2 := by
      have : Dfun u R y = ((r ^ 2 - R ^ 2) / 2) ^ 2 := by
        unfold Dfun
        rw [hr, max_eq_left (by nlinarith)]
        ring
      rw [this, Real.sqrt_sq (by nlinarith)]
    rw [hsq]
    refine h1.trans ?_
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hR]
    nlinarith

/-- 実効ポテンシャル `V0 + K D` の勾配は `(y-v) + K • ∇D`。 -/
theorem hasGradientAt_effective (u v : E) (R K : ℝ) (y : E) :
    HasGradientAt (fun z : E => 1 / 2 * ‖z - v‖ ^ 2 - K * 1 * (1 * (-(Dfun u R z))))
      ((y - v) + K • gradD u R y) y := by
  have h1 := hasGradientAt_iff_hasFDerivAt.1 (hasGradientAt_halfNormSq v y)
  have h2 := hasGradientAt_iff_hasFDerivAt.1 (hasGradientAt_D u R y)
  have h := h1.add (h2.const_mul K)
  rw [hasGradientAt_iff_hasFDerivAt]
  have hfun : (fun z : E => 1 / 2 * ‖z - v‖ ^ 2 - K * 1 * (1 * (-(Dfun u R z)))) =
      (fun z : E => 1 / 2 * ‖z - v‖ ^ 2 + K * Dfun u R z) := by
    funext z; ring
  rw [hfun]
  refine h.congr_fderiv ?_
  ext w
  simp [InnerProductSpace.toDual_apply_apply, inner_add_left, inner_smul_left]

/-- ケースA の一般結論: 閉ループ `ẋ=-∇(V0 + K D)`（`P≡1`, `s(D)=-D`, `κq=K`）の任意の解について、
`v∈Z`（`‖u-v‖≤R`）、`b+c≤K`、`b,c>0` のもとで `D` と `dist(x,Z)` が指数減衰する。
一般定理 `theorem20_full_trajectory_conclusion_of_original_conditions` の全前提を示して得る。 -/
theorem caseA (u v : E) {R K b c : ℝ} (hR : 0 < R) (hv : ‖u - v‖ ≤ R)
    (hb : 0 < b) (hc : 0 < c) (hbc : b + c ≤ K) (t₀ : ℝ) (x : ℝ → E)
    (hode : ∀ r, t₀ ≤ r → HasDerivAt x
      (-(∇ (fun y => 1 / 2 * ‖y - v‖ ^ 2 - K * 1 * (1 * (-(Dfun u R y)))) (x r))) r) :
    (∀ t, t₀ ≤ t →
      Dfun u R (x t) ≤ Dfun u R (x t₀) * Real.exp (-(2 * (2 * R ^ 2) * c) * (t - t₀)) ∧
      Metric.infDist (x t) (Metric.closedBall u R) ≤
        (1 / R) * Real.sqrt (Dfun u R (x t₀)) * Real.exp (-(2 * R ^ 2) * c * (t - t₀)) ∧
      (x t ∉ Metric.closedBall u R → deriv (fun r => Dfun u R (x r)) t < 0)) ∧
    Filter.Tendsto (fun r => Metric.infDist (x r) (Metric.closedBall u R))
      Filter.atTop (nhds 0) := by
  have h := theorem20_full_trajectory_conclusion_of_original_conditions
    (fun _ => ContinuousLinearMap.id ℝ E) (fun _ => ContinuousLinearMap.id ℝ E)
    (fun y => 1 / 2 * ‖y - v‖ ^ 2) (fun _ => (1 : ℝ)) (Dfun u R) (fun d => -d)
    x (fun r => -(∇ (fun y => 1 / 2 * ‖y - v‖ ^ 2 - K * 1 * (1 * (-(Dfun u R y)))) (x r)))
    Set.univ (Metric.closedBall u R)
    (fun r => inner ℝ (gradD u R (x r)) (gradD u R (x r))) (fun _ => -1)
    K 1 b c (2 * R ^ 2) (1 / R) 1 t₀
    (fun r => x r - v) (fun _ => 0) (fun r => gradD u R (x r))
    (fun r _ => Set.mem_univ _)
    (fun r _ => hasGradientAt_halfNormSq v (x r))
    (fun r _ => hasGradientAt_const (x r) (1 : ℝ))
    (fun r _ => hasGradientAt_D u R (x r))
    (Dfun_nonneg u R) (Dfun_eq_zero_iff u hR)
    ⟨u, Metric.mem_closedBall_self hR.le⟩ Metric.isClosed_closedBall
    (fun r _ => by simpa using hasDerivAt_neg (Dfun u R (x r)))
    hode
    (fun r _ => by simp)
    (fun r _ y => by simp)
    (fun r _ y z => rfl)
    (fun r _ y => by simp [real_inner_self_eq_norm_sq])
    (fun r _ _ hnot => by
      have hw : R < ‖x r - u‖ := by
        simpa [Metric.mem_closedBall, dist_eq_norm, not_le] using hnot
      have hm : 0 < ‖x r - u‖ ^ 2 - R ^ 2 := by nlinarith
      have hin : 0 ≤ inner ℝ (x r - u) (x r - v) := by
        have hsplit : x r - v = (x r - u) + (u - v) := by abel
        rw [hsplit, inner_add_right, real_inner_self_eq_norm_sq]
        have := abs_real_inner_le_norm (x r - u) (u - v)
        have := neg_abs_le (inner ℝ (x r - u) (u - v))
        nlinarith [norm_nonneg (x r - u), norm_nonneg (u - v)]
      have hgrad : gradD u R (x r) = (‖x r - u‖ ^ 2 - R ^ 2) • (x r - u) := by
        simp [gradD, max_eq_left hm.le]
      simp only [ContinuousLinearMap.id_apply, inner_zero_right, mul_zero, add_zero, hgrad,
        inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      have h2 : 0 ≤ b * ((‖x r - u‖ ^ 2 - R ^ 2) * ((‖x r - u‖ ^ 2 - R ^ 2) *
          inner ℝ (x r - u) (x r - u))) := by
        rw [real_inner_self_eq_norm_sq]; positivity
      nlinarith [mul_nonneg hm.le hin])
    (fun r _ _ _ => by simp; linarith)
    (fun r _ => by simpa using PL_bound u hR (x r))
    (fun r _ => by simp)
    (fun r _ => by simpa using error_bound u hR (x r))
    (by positivity) (by positivity) one_pos hb hc one_pos
  refine ⟨fun t ht => ⟨(h.1 t ht).1, ?_, (h.1 t ht).2.2.2.1⟩, h.2⟩
  have := (h.1 t ht).2.1
  convert this using 2 <;> ring_nf

end General

/-! ## ケースB（反例）: `v∉Z` で `x*=(1,0)` が停留点 -/

section CaseB

abbrev E2 := EuclideanSpace ℝ (Fin 2)

noncomputable def vec (a b : ℝ) : E2 := !₂[a, b]

theorem inner_vec (a b c d : ℝ) : inner ℝ (vec a b) (vec c d) = a * c + b * d := by
  simp [vec, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem normSq_vec (a b : ℝ) : ‖vec a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_vec]; ring

theorem vec_sub (a b c d : ℝ) : vec a b - vec c d = vec (a - c) (b - d) := by
  ext i; fin_cases i <;> simp [vec]

theorem vec_smul (k a b : ℝ) : k • vec a b = vec (k * a) (k * b) := by
  ext i; fin_cases i <;> simp [vec]

/-- Python のケースB: `u=(2,0)`, `v=0`, `R=½`, `K=4/3`。 -/
noncomputable def uB : E2 := vec 2 0
noncomputable def vB : E2 := vec 0 0
noncomputable def xstar : E2 := vec 1 0
noncomputable def RB : ℝ := 1 / 2
noncomputable def KB : ℝ := 4 / 3

theorem xstar_not_in_Z : xstar ∉ Metric.closedBall uB RB := by
  rw [Metric.mem_closedBall, dist_eq_norm, not_le]
  have h : ‖xstar - uB‖ ^ 2 = 1 := by
    simp only [xstar, uB, vec_sub, normSq_vec]; norm_num
  have h0 : 0 ≤ ‖xstar - uB‖ := norm_nonneg _
  simp only [RB]
  nlinarith

theorem D_xstar : Dfun uB RB xstar = 9 / 64 := by
  have h : ‖xstar - uB‖ ^ 2 = 1 := by
    simp only [xstar, uB, vec_sub, normSq_vec]; norm_num
  unfold Dfun; rw [h]; norm_num [RB]

theorem gradD_xstar : gradD uB RB xstar = vec (-(3 / 4)) 0 := by
  have h : ‖xstar - uB‖ ^ 2 = 1 := by
    simp only [xstar, uB, vec_sub, normSq_vec]; norm_num
  unfold gradD; rw [h]
  simp only [xstar, uB, vec_sub, vec_smul, RB]
  norm_num

/-- 停留点: `∇(V0 + K D)(x*) = (x*-v) + K ∇D(x*) = (1,0) + (4/3)(-3/4,0) = 0`。 -/
theorem effective_gradient_xstar :
    (xstar - vB) + KB • gradD uB RB xstar = 0 := by
  rw [gradD_xstar]
  simp only [xstar, vB, KB, vec_sub, vec_smul]
  have : (vec 1 0 - vec 0 0 : E2) = vec 1 0 := by simp [vec_sub]
  ext i; fin_cases i <;> simp [vec]

/-- 反例（B）: 定数軌道 `x(t)≡x*` は同じ閉ループ ODE の解で、`x*∉Z`、`dist(x*,Z)>0` が一定。
したがって (20.1) の厳密下降 `x∉Z ⇒ Ḋ<0` も、(20.2) の距離収束も成り立たない。 -/
theorem caseB_constant_solution :
    (∀ r : ℝ, HasDerivAt (fun _ : ℝ => xstar)
      (-(∇ (fun y : E2 => 1 / 2 * ‖y - vB‖ ^ 2 - KB * 1 * (1 * (-(Dfun uB RB y)))) xstar)) r) ∧
    xstar ∉ Metric.closedBall uB RB ∧
    deriv (fun _ : ℝ => Dfun uB RB xstar) 0 = 0 ∧
    0 < Metric.infDist xstar (Metric.closedBall uB RB) ∧
    ¬ Filter.Tendsto (fun _ : ℝ => Metric.infDist xstar (Metric.closedBall uB RB))
      Filter.atTop (nhds 0) := by
  have hgrad := (hasGradientAt_effective uB vB RB KB xstar).gradient
  rw [effective_gradient_xstar] at hgrad
  have hpos : 0 < Metric.infDist xstar (Metric.closedBall uB RB) :=
    (Metric.isClosed_closedBall.notMem_iff_infDist_pos
      ⟨uB, Metric.mem_closedBall_self (by norm_num [RB])⟩).1 xstar_not_in_Z
  refine ⟨fun r => ?_, xstar_not_in_Z, by simp, hpos, ?_⟩
  · rw [hgrad]; simpa using hasDerivAt_const r xstar
  · intro hT
    have := tendsto_nhds_unique tendsto_const_nhds hT
    exact hpos.ne' this

/-- (20.A)(20.B) を同時に満たす `b,c>0` は存在しない（`x*` で (20.A) は `b≥4/3`、(20.B) は `b+c≤4/3`）。 -/
theorem caseB_no_valid_constants (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hA : -inner ℝ (gradD uB RB xstar) (xstar - vB) ≤
      b * inner ℝ (gradD uB RB xstar) (gradD uB RB xstar)) :
    ¬ (b + c ≤ KB) := by
  rw [gradD_xstar] at hA
  have hx : xstar - vB = vec 1 0 := by simp [xstar, vB, vec_sub]
  rw [hx, inner_vec, inner_vec] at hA
  simp only [KB]
  intro h
  nlinarith

/-- Python のケースA: `u=(2,0)`, `v=0`, `R=5/2`, `K=4/3`（一般定理の定数は `b=1/3`, `c=1`）。 -/
noncomputable def uA : E2 := vec 2 0

theorem caseA_python_instance (t₀ : ℝ) (x : ℝ → E2)
    (hode : ∀ r, t₀ ≤ r → HasDerivAt x
      (-(∇ (fun y : E2 => 1 / 2 * ‖y - vB‖ ^ 2 - (4 / 3 : ℝ) * 1 * (1 * (-(Dfun uA (5 / 2) y)))) (x r))) r) :
    (∀ t, t₀ ≤ t →
      Dfun uA (5 / 2) (x t) ≤ Dfun uA (5 / 2) (x t₀) *
        Real.exp (-(2 * (2 * (5 / 2 : ℝ) ^ 2) * 1) * (t - t₀)) ∧
      Metric.infDist (x t) (Metric.closedBall uA (5 / 2)) ≤
        (1 / (5 / 2)) * Real.sqrt (Dfun uA (5 / 2) (x t₀)) *
          Real.exp (-(2 * (5 / 2 : ℝ) ^ 2) * 1 * (t - t₀)) ∧
      (x t ∉ Metric.closedBall uA (5 / 2) → deriv (fun r => Dfun uA (5 / 2) (x r)) t < 0)) ∧
    Filter.Tendsto (fun r => Metric.infDist (x r) (Metric.closedBall uA (5 / 2)))
      Filter.atTop (nhds 0) := by
  have hv : ‖uA - vB‖ ≤ 5 / 2 := by
    have h : ‖uA - vB‖ ^ 2 = 4 := by
      simp only [uA, vB, vec_sub, normSq_vec]; norm_num
    nlinarith [norm_nonneg (uA - vB)]
  exact caseA uA vB (R := 5 / 2) (K := 4 / 3) (b := 1 / 3) (c := 1)
    (by norm_num) hv (by norm_num) one_pos (by norm_num) t₀ x hode

end CaseB

end Tomabechi.Examples.Theorem20
