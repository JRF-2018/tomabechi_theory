import Mathlib

/-!
# 定理15の反例 (`examples/theorem15_entropy_exchange.py` の (B)) の Lean 根拠

可算無限層 `k∈ℕ`、`H_k(t)=2^{-k}(1+sin(4^k t))`、`w_k=1`。

* A2（各 `H_k` は滑らか＝絶対連続）と A6′(i)（`ΣH_k(t)` は各点で有限: `0≤H_k≤2·2^{-k}`）は成り立つ。
* しかし A6′(ii) は破れる: 有限部分和の族 `{Σ_{k∈s} w_k h_k : s⊂ℕ 有限}`（`h_k=dH_k/dt=2^k cos(4^k t)`）は
  `L¹[0,1]` で一様可積分でない。実際 `s={N}` の単独層だけで `‖h_N‖_{L¹}≥2^N/4→∞`、
  `UniformIntegrable` の必須成分 `L¹` 有界性が成り立たない。
  （原文 §3.7.5: このとき補題15.1の項別微分が保証されず、交換式A7の打ち消しが意味を失う。）

注意: A6′(ii) の不成立、有限部分和の変動発散、極限の非有界変動・非絶対連続は別々に証明する。
有限部分和の変動発散だけから極限の非有界変動は推論せず、極限 `F=ΣH_k` が `[0,1]` で有界変動でも
絶対連続でもないこと（`not_boundedVariation_infiniteSum`、`not_absolutelyContinuous_infiniteSum`）は、
高周波の正弦係数の評価で直接証明する。Python と同じ `k=1` 始まりの級数についても同じ結論を示す。
-/

namespace Tomabechi.Examples.Theorem15A6

open MeasureTheory
open Filter
open scoped Topology

set_option maxHeartbeats 4000000

/-- `H_k(t)=2^{-k}(1+sin(4^k t))`。 -/
noncomputable def H (k : ℕ) (t : ℝ) : ℝ := (1 / 2 : ℝ) ^ k * (1 + Real.sin (4 ^ k * t))
/-- `h_k=dH_k/dt=2^k cos(4^k t)`。 -/
noncomputable def h (k : ℕ) (t : ℝ) : ℝ := 2 ^ k * Real.cos (4 ^ k * t)

theorem hasDerivAt_H (k : ℕ) (t : ℝ) : HasDerivAt (H k) (h k t) t := by
  unfold H h
  have h1 := ((hasDerivAt_id t).const_mul ((4 : ℝ) ^ k)).sin.const_add 1
  have h2 := h1.const_mul ((1 / 2 : ℝ) ^ k)
  refine h2.congr_deriv ?_
  simp only [id, mul_one]
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, one_div, inv_pow]
  field_simp

/-- A6′(i): `0≤H_k≤2·2^{-k}` なので `ΣH_k(t)` は各点で有限。 -/
theorem H_bound (k : ℕ) (t : ℝ) : 0 ≤ H k t ∧ H k t ≤ 2 * (1 / 2 : ℝ) ^ k := by
  unfold H
  have hp : 0 < (1 / 2 : ℝ) ^ k := by positivity
  have h1 := Real.neg_one_le_sin (4 ^ k * t)
  have h2 := Real.sin_le_one (4 ^ k * t)
  constructor <;> nlinarith

theorem H_summable (t : ℝ) : Summable fun k => H k t :=
  Summable.of_nonneg_of_le (fun k => (H_bound k t).1) (fun k => (H_bound k t).2)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)

/-- 一様極限として定めた無限和 `F(t)=Σ H_k(t)`。 -/
noncomputable def infiniteSum (t : ℝ) : ℝ := ∑' k, H k t

/-- 各項の絶対値は幾何級数 `2·2^{-k}` で一様に抑えられる。 -/
theorem H_norm_bound (k : ℕ) (t : ℝ) : ‖H k t‖ ≤ 2 * (1 / 2 : ℝ) ^ k := by
  rw [Real.norm_eq_abs, abs_of_nonneg (H_bound k t).1]
  exact H_bound k t |>.2

/-- 無限和は連続関数の一様極限なので連続である。 -/
theorem continuous_infiniteSum : Continuous infiniteSum := by
  exact continuous_tsum (fun k => by
    unfold H
    fun_prop)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)
    (fun k t => H_norm_bound k t)

/-- `N` 項目以降の尾は、`4·2^{-N}` 以下。一様収束の定量的な尾評価である。 -/
theorem infiniteSum_tail_norm_bound (N : ℕ) (t : ℝ) :
    ‖∑' k : ℕ, H (k + N) t‖ ≤ 4 * (1 / 2 : ℝ) ^ N := by
  let g : ℕ → ℝ := fun k => 2 * (1 / 2 : ℝ) ^ (k + N)
  have hg : Summable g := by
    have hgeom : Summable fun k : ℕ => (1 / 2 : ℝ) ^ k :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    rw [show g = (fun k => ((1 / 2 : ℝ) ^ N * 2) * (1 / 2 : ℝ) ^ k) by
      funext k
      dsimp [g]
      rw [pow_add]
      ring]
    exact hgeom.mul_left _
  have htail : Summable fun k : ℕ => ‖H (k + N) t‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => (H_norm_bound (k + N) t)) hg
  calc
    ‖∑' k : ℕ, H (k + N) t‖ ≤ ∑' k : ℕ, ‖H (k + N) t‖ :=
      norm_tsum_le_tsum_norm htail
    _ ≤ ∑' k : ℕ, g k := by
      exact Summable.tsum_le_tsum (fun k => H_norm_bound (k + N) t) htail hg
    _ = 4 * (1 / 2 : ℝ) ^ N := by
      dsimp [g]
      rw [show (fun k : ℕ => 2 * (1 / 2 : ℝ) ^ (k + N)) =
        (fun k => (1 / 2 : ℝ) ^ N * (2 * (1 / 2 : ℝ) ^ k)) by
          funext k
          rw [pow_add]
          ring]
      rw [tsum_mul_left, tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
          (by norm_num : (1 / 2 : ℝ) < 1)]
      norm_num
      ring

/-- 絶対連続関数の高周波正弦係数は、部分積分により `1/ω` の速さで抑えられる。 -/
theorem ac_sine_coefficient_bound (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f 0 1) (ω : ℝ) (hω : 0 < ω) :
    |∫ t in (0 : ℝ)..1, f t * Real.sin (ω * t)| ≤
      (|f 0| + |f 1| + ∫ t in (0 : ℝ)..1, |deriv f t|) / ω := by
  let g : ℝ → ℝ := fun t => Real.cos (ω * t) / ω
  have hg : AbsolutelyContinuousOnInterval g 0 1 := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hgD (t : ℝ) : HasDerivAt g (-Real.sin (ω * t)) t := by
    dsimp [g]
    have harg : HasDerivAt (fun x : ℝ => ω * x) ω t := by
      simpa using (hasDerivAt_id t).const_mul ω
    have hcos := (Real.hasDerivAt_cos (ω * t)).comp t harg
    have hh : HasDerivAt (fun x : ℝ => Real.cos (ω * x) / ω)
        ((-Real.sin (ω * t) * ω) / ω) t := hcos.div_const ω
    convert hh using 1 <;> simp [g, hω.ne', div_eq_mul_inv, mul_comm]
  have hparts := hf.integral_mul_deriv_eq_deriv_mul hg
  have hformula :
      (∫ t in (0 : ℝ)..1, f t * Real.sin (ω * t)) =
        -(f 1 * g 1 - f 0 * g 0) + ∫ t in (0 : ℝ)..1, deriv f t * g t := by
    have hderiv (t : ℝ) : deriv g t = -Real.sin (ω * t) := (hgD t).deriv
    have hparts' :
        -(∫ t in (0 : ℝ)..1, f t * Real.sin (ω * t)) =
          f 1 * g 1 - f 0 * g 0 - ∫ t in (0 : ℝ)..1, deriv f t * g t := by
      simpa [hderiv, neg_mul] using hparts
    linarith
  have hfd : IntervalIntegrable (deriv f) volume 0 1 := hf.intervalIntegrable_deriv
  have hfg : IntervalIntegrable (fun t => deriv f t * g t) volume 0 1 :=
    hfd.mul_continuousOn (by
      intro t ht
      dsimp [g]
      fun_prop)
  have hbound_g (t : ℝ) : |g t| ≤ 1 / ω := by
    dsimp [g]
    rw [abs_div, abs_of_pos hω]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (le_of_lt hω)
  have hproduct :
      |∫ t in (0 : ℝ)..1, deriv f t * g t| ≤
        (∫ t in (0 : ℝ)..1, |deriv f t|) / ω := by
    have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (by norm_num : (0 : ℝ) ≤ 1)
      (f := fun t => deriv f t * g t)
    have hcmp :
        (∫ t in (0 : ℝ)..1, |deriv f t * g t|) ≤
          ∫ t in (0 : ℝ)..1, (1 / ω) * |deriv f t| := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        hfg.abs (hfd.abs.const_mul (1 / ω))
      intro t ht
      rw [abs_mul]
      calc
        |deriv f t| * |g t| ≤ |deriv f t| * (1 / ω) :=
          mul_le_mul_of_nonneg_left (hbound_g t) (abs_nonneg _)
        _ = (1 / ω) * |deriv f t| := by ring
    have hconst := intervalIntegral.integral_const_mul (1 / ω)
      (fun t : ℝ => |deriv f t|) (μ := volume) (a := 0) (b := 1)
    rw [hconst] at hcmp
    simpa [Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using hnorm.trans hcmp
  have hbdry : |f 1 * g 1 - f 0 * g 0| ≤ (|f 0| + |f 1|) / ω := by
    have hg0 : g 0 = 1 / ω := by simp [g]
    have hg1 : |g 1| ≤ 1 / ω := hbound_g 1
    rw [hg0]
    calc
      |f 1 * g 1 - f 0 * (1 / ω)| ≤
          |f 1| * (1 / ω) + |f 0| * (1 / ω) := by
        calc
          |f 1 * g 1 - f 0 * (1 / ω)| ≤ |f 1 * g 1| + |f 0 * (1 / ω)| := by
            simpa [Real.norm_eq_abs] using norm_sub_le (f 1 * g 1) (f 0 * (1 / ω))
          _ ≤ |f 1| * (1 / ω) + |f 0| * (1 / ω) := by
            apply add_le_add
            · rw [abs_mul]
              exact mul_le_mul_of_nonneg_left hg1 (abs_nonneg (f 1))
            · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / ω)]
      _ = (|f 0| + |f 1|) / ω := by field_simp [hω.ne']; ring
  calc
    |∫ t in (0 : ℝ)..1, f t * Real.sin (ω * t)| ≤
        |f 1 * g 1 - f 0 * g 0| +
          |∫ t in (0 : ℝ)..1, deriv f t * g t| := by
      rw [hformula]
      calc
        |-(f 1 * g 1 - f 0 * g 0) + ∫ t in (0 : ℝ)..1, deriv f t * g t| ≤
            |f 1 * g 1 - f 0 * g 0| +
              |∫ t in (0 : ℝ)..1, deriv f t * g t| := by
          calc
            |-(f 1 * g 1 - f 0 * g 0) + ∫ t in (0 : ℝ)..1, deriv f t * g t| ≤
                |-(f 1 * g 1 - f 0 * g 0)| +
                  |∫ t in (0 : ℝ)..1, deriv f t * g t| := by
              simpa [Real.norm_eq_abs] using
                (norm_add_le (-(f 1 * g 1 - f 0 * g 0))
                  (∫ t in (0 : ℝ)..1, deriv f t * g t))
            _ = |f 1 * g 1 - f 0 * g 0| +
                |∫ t in (0 : ℝ)..1, deriv f t * g t| := by rw [abs_neg]
            _ = _ := by rw [abs_sub_comm]
        _ = _ := rfl
    _ ≤ (|f 0| + |f 1|) / ω +
        (∫ t in (0 : ℝ)..1, |deriv f t|) / ω := add_le_add hbdry hproduct
    _ = (|f 0| + |f 1| + ∫ t in (0 : ℝ)..1, |deriv f t|) / ω := by ring

/-- 無限和と正弦の積分を、各層の積分の級数へ交換できる。 -/
theorem integral_infiniteSum_sin_eq_tsum (ω : ℝ) :
    ∫ t in (0 : ℝ)..1, infiniteSum t * Real.sin (ω * t) =
      ∑' k : ℕ, ∫ t in (0 : ℝ)..1, H k t * Real.sin (ω * t) := by
  let term (k : ℕ) : C(ℝ, ℝ) := ⟨fun t => H k t * Real.sin (ω * t), by
    unfold H
    fun_prop⟩
  let interval : Set ℝ := Set.uIcc (0 : ℝ) 1
  have hcompact : IsCompact interval := by
    change IsCompact (Set.uIcc (0 : ℝ) 1)
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact isCompact_Icc
  letI : CompactSpace interval := isCompact_iff_compactSpace.mp hcompact
  have hterm_bound (k : ℕ) :
      ‖ContinuousMap.restrict interval (term k)‖ ≤ 2 * (1 / 2 : ℝ) ^ k := by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro t
    change ‖H k (t : ℝ) * Real.sin (ω * (t : ℝ))‖ ≤ _
    have h := H_norm_bound k (t : ℝ)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |H k t| * |Real.sin (ω * t)| ≤ |H k t| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = |H k t| := by ring
      _ ≤ 2 * (1 / 2 : ℝ) ^ k := by simpa [Real.norm_eq_abs] using h
  have hseries : Summable fun k : ℕ => ‖ContinuousMap.restrict interval (term k)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      hterm_bound ((summable_geometric_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2)
  have hhas := intervalIntegral.hasSum_intervalIntegral_of_summable_norm
    (a := 0) (b := 1) hseries
  have hsum := hhas.tsum_eq
  have hpoint (t : ℝ) : (∑' k : ℕ, term k t) = infiniteSum t * Real.sin (ω * t) := by
    dsimp [term, infiniteSum]
    exact (H_summable t).tsum_mul_right (Real.sin (ω * t))
  calc
    ∫ t in (0 : ℝ)..1, infiniteSum t * Real.sin (ω * t) =
        ∫ t in (0 : ℝ)..1, ∑' k : ℕ, term k t := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact (hpoint t).symm
    _ = ∑' k : ℕ, ∫ t in (0 : ℝ)..1, term k t := hsum.symm
    _ = ∑' k : ℕ, ∫ t in (0 : ℝ)..1, H k t * Real.sin (ω * t) := by
      congr 1

/-- 各層の試験積分も絶対収束する。これにより後で対角項を級数から分離できる。 -/
theorem summable_layer_sine_integrals (ω : ℝ) :
    Summable fun k : ℕ => ∫ t in (0 : ℝ)..1, H k t * Real.sin (ω * t) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2)
  intro k
  have hcont : IntervalIntegrable (fun t : ℝ => H k t * Real.sin (ω * t)) volume 0 1 := by
    apply (by
      unfold H
      fun_prop : Continuous fun t : ℝ => H k t * Real.sin (ω * t)).intervalIntegrable
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (f := fun t : ℝ => H k t * Real.sin (ω * t))
  have hpoint (t : ℝ) : ‖H k t * Real.sin (ω * t)‖ ≤ 2 * (1 / 2 : ℝ) ^ k := by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |H k t| * |Real.sin (ω * t)| ≤ |H k t| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = |H k t| := by ring
      _ ≤ 2 * (1 / 2 : ℝ) ^ k := by
        rw [← Real.norm_eq_abs]
        exact H_norm_bound k t
  have hpoint_integral :
      (∫ t in (0 : ℝ)..1, ‖H k t * Real.sin (ω * t)‖) ≤
        ∫ t in (0 : ℝ)..1, (2 * (1 / 2 : ℝ) ^ k) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hcont.norm
      (by
        have hc : Continuous fun _ : ℝ => 2 * (1 / 2 : ℝ) ^ k := continuous_const
        exact hc.intervalIntegrable 0 1)
    intro t _
    exact hpoint t
  rw [intervalIntegral.integral_const] at hpoint_integral
  have hnorm' : ‖∫ t in (0 : ℝ)..1, H k t * Real.sin (ω * t)‖ ≤
      2 * (1 / 2 : ℝ) ^ k := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, ‖H k t * Real.sin (ω * t)‖ := hnorm
      _ ≤ 2 * (1 / 2 : ℝ) ^ k := by simpa using hpoint_integral
  exact hnorm'

/-- 有限部分集合 `s` の部分和 `Σ_{k∈s} w_k h_k`（`w_k=1`）。 -/
noncomputable def finiteRate (s : Finset ℕ) (t : ℝ) : ℝ := ∑ k ∈ s, h k t

/-- `H₀`から`H_N`までの有限部分和の導関数。 -/
noncomputable def partialDerivative (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), h k t

/-- 有限部分和の関数。Python側の級数と同じ形で、ここでは`k=0`から始める。 -/
noncomputable def partialSum (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), H k t

/-- 有限部分和は滑らかで、導関数は層ごとの導関数の有限和である。 -/
theorem hasDerivAt_partialSum (N : ℕ) (t : ℝ) :
    HasDerivAt (partialSum N) (partialDerivative N t) t := by
  change HasDerivAt (fun y => ∑ k ∈ Finset.range (N + 1), H k y)
    (∑ k ∈ Finset.range (N + 1), h k t) t
  exact HasDerivAt.fun_sum (fun k hk => hasDerivAt_H k t)

/-- `partialDerivative`は有限部分和の通常の導関数そのものである。 -/
theorem deriv_partialSum (N : ℕ) (t : ℝ) :
    deriv (partialSum N) t = partialDerivative N t :=
  (hasDerivAt_partialSum N t).deriv

/-- 有限部分和の導関数を周波数`4^N`の余弦で試験すると、層ごとの積分へ分解できる。 -/
theorem partialDerivative_cos_integral_eq_sum (N : ℕ) :
    ∫ t in (0 : ℝ)..1, partialDerivative N t * Real.cos ((4 : ℝ) ^ N * t) =
      ∑ k ∈ Finset.range (N + 1),
        ∫ t in (0 : ℝ)..1, h k t * Real.cos ((4 : ℝ) ^ N * t) := by
  unfold partialDerivative
  rw [intervalIntegral.integral_congr (fun t _ => by
    rw [Finset.sum_mul])]
  rw [intervalIntegral.integral_finsetSum (μ := volume) (a := (0 : ℝ)) (b := 1)]
  intro k hk
  have hc : Continuous fun x : ℝ => h k x * Real.cos ((4 : ℝ) ^ N * x) := by
    unfold h
    fun_prop
  exact hc.intervalIntegrable (μ := volume) 0 1

/-- `∫₀¹ cos²(Mt) ≥ 1/2 - 1/(4M)`（`M>0`）。 -/
theorem integral_cos_sq_lower (M : ℝ) (hM : 0 < M) :
    1 / 2 - 1 / (4 * M) ≤ ∫ t in (0 : ℝ)..1, Real.cos (M * t) ^ 2 := by
  have h := intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x ^ 2) (a := 0) (b := 1) hM.ne'
  rw [integral_cos_sq] at h
  simp at h
  rw [h]
  have hsc : -(1 / 2 : ℝ) ≤ Real.cos M * Real.sin M := by
    nlinarith [sq_nonneg (Real.cos M + Real.sin M), Real.sin_sq_add_cos_sq M]
  have : (1 / 2 - 1 / (4 * M) : ℝ) = M⁻¹ * ((-(1 / 2) + M) / 2) := by field_simp; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- 周波数を `c` 倍した余弦の区間積分。 -/
theorem integral_cos_scaled (c : ℝ) (hc : c ≠ 0) :
    ∫ t in (0 : ℝ)..1, Real.cos (c * t) = Real.sin c / c := by
  have h := intervalIntegral.integral_comp_mul_left Real.cos (a := 0) (b := 1) hc
  rw [integral_cos] at h
  rw [show c * (1 : ℝ) = c by ring, show c * (0 : ℝ) = 0 by ring,
    Real.sin_zero, sub_zero] at h
  convert h using 1 <;> simp only [smul_eq_mul] <;> field_simp [hc]

/-- 周波数を `c` 倍した正弦の区間積分。定数項との交差に用いる。 -/
theorem integral_sin_scaled (c : ℝ) (hc : c ≠ 0) :
    ∫ t in (0 : ℝ)..1, Real.sin (c * t) = (1 - Real.cos c) / c := by
  have h := intervalIntegral.integral_comp_mul_left Real.sin (a := 0) (b := 1) hc
  rw [integral_sin] at h
  rw [show c * (0 : ℝ) = 0 by ring, Real.cos_zero] at h
  convert h using 1 <;> simp only [smul_eq_mul] <;> field_simp [hc]

/-- 上の積分の絶対値は `2/|c|` 以下。 -/
theorem abs_integral_sin_scaled_le (c : ℝ) (hc : c ≠ 0) :
    |∫ t in (0 : ℝ)..1, Real.sin (c * t)| ≤ 2 / |c| := by
  rw [integral_sin_scaled c hc, abs_div]
  have hnum : |1 - Real.cos c| ≤ 2 := by
    calc
      |1 - Real.cos c| ≤ |(1 : ℝ)| + |Real.cos c| := abs_sub _ _
      _ ≤ 2 := by
        have hc' := Real.abs_cos_le_one c
        norm_num at * <;> nlinarith
  exact div_le_div_of_nonneg_right hnum (abs_nonneg c)

/-- 異なる2周波数の正弦積は、和差周波数の端点値で厳密に積分できる。 -/
theorem integral_sin_mul_sin (a b : ℝ) (hab : a ≠ b) (hsum : a + b ≠ 0) :
    ∫ t in (0 : ℝ)..1, Real.sin (a * t) * Real.sin (b * t) =
      ((Real.sin (a - b) / (a - b)) - (Real.sin (a + b) / (a + b))) / 2 := by
  have hdiff : a - b ≠ 0 := sub_ne_zero.mpr hab
  have htrig (t : ℝ) :
      Real.sin (a * t) * Real.sin (b * t) =
        (Real.cos ((a - b) * t) - Real.cos ((a + b) * t)) / 2 := by
    have h3 : (a - b) * t = a * t - b * t := by ring
    have h4 : (a + b) * t = a * t + b * t := by ring
    rw [h3, h4, Real.cos_sub, Real.cos_add]
    ring
  have hint :
      (∫ t in (0 : ℝ)..1, Real.sin (a * t) * Real.sin (b * t)) =
      (∫ t in (0 : ℝ)..1, (Real.cos ((a - b) * t) - Real.cos ((a + b) * t)) / 2) := by
    exact intervalIntegral.integral_congr (fun t _ => htrig t)
  have hcos1 (c : ℝ) : IntervalIntegrable (fun t : ℝ => Real.cos (c * t)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => Real.cos (c * t)).intervalIntegrable _ _
  rw [hint, intervalIntegral.integral_div,
    intervalIntegral.integral_sub (hcos1 (a - b)) (hcos1 (a + b)),
    integral_cos_scaled (a - b) hdiff, integral_cos_scaled (a + b) hsum]

/-- 高周波の対角項 `sin²(Mt)` は約 `1/2` の積分を持つ。 -/
theorem integral_sin_sq_lower (M : ℝ) (hM : 0 < M) :
    1 / 2 - 1 / (4 * M) ≤ ∫ t in (0 : ℝ)..1, Real.sin (M * t) ^ 2 := by
  have h := intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 2)
    (a := 0) (b := 1) hM.ne'
  rw [integral_sin_sq] at h
  simp only [Real.sin_zero, zero_mul, sub_zero, Real.cos_zero,
    one_mul, mul_one, mul_zero] at h
  have hsc : Real.sin M * Real.cos M ≤ 1 / 2 := by
    nlinarith [sq_nonneg (Real.sin M - Real.cos M), Real.sin_sq_add_cos_sq M]
  have hrepr : (1 / 2 - 1 / (4 * M) : ℝ) = M⁻¹ * ((M - 1 / 2) / 2) := by
    field_simp
    ring
  rw [hrepr, h]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- 上の積分公式から得る、交差周波数項の絶対値上界。 -/
theorem abs_integral_sin_mul_sin_le (a b : ℝ) (hab : a ≠ b) (hsum : a + b ≠ 0) :
    |∫ t in (0 : ℝ)..1, Real.sin (a * t) * Real.sin (b * t)| ≤
      (1 / |a - b| + 1 / |a + b|) / 2 := by
  rw [integral_sin_mul_sin a b hab hsum]
  have hdiv (x : ℝ) (hx : x ≠ 0) : |Real.sin x / x| ≤ 1 / |x| := by
    rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hx)).2
    calc
      |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
      _ = 1 / |x| * |x| := by field_simp [abs_ne_zero.mpr hx]
  calc
    |(Real.sin (a - b) / (a - b) - Real.sin (a + b) / (a + b)) / 2| ≤
        (|Real.sin (a - b) / (a - b)| + |Real.sin (a + b) / (a + b)|) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)
    _ ≤ (1 / |a - b| + 1 / |a + b|) / 2 := by
      apply div_le_div_of_nonneg_right (add_le_add _ _) (by norm_num)
      · exact hdiv _ (sub_ne_zero.mpr hab)
      · exact hdiv _ hsum

/-- 4冪の異なる2周波数の正弦交差積分は、高い方の周波数の逆数で抑えられる。 -/
theorem abs_integral_sin_pow_mul_sin_pow_le (k n : ℕ) (hkn : k < n) :
    |∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ k * t) *
      Real.sin ((4 : ℝ) ^ n * t)| ≤ 2 / (4 : ℝ) ^ n := by
  have hpow : (4 : ℝ) ^ (k + 1) ≤ (4 : ℝ) ^ n := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
      (Nat.succ_le_of_lt hkn)
  have hscale : (4 : ℝ) ^ k * 4 ≤ (4 : ℝ) ^ n := by
    simpa [pow_succ] using hpow
  have hkpos : 0 < (4 : ℝ) ^ k := by positivity
  have hnpos : 0 < (4 : ℝ) ^ n := by positivity
  have hfreq : (4 : ℝ) ^ k ≤ (4 : ℝ) ^ n / 4 := by
    calc
      (4 : ℝ) ^ k = ((4 : ℝ) ^ k * 4) / 4 := by field_simp
      _ ≤ (4 : ℝ) ^ n / 4 := div_le_div_of_nonneg_right hscale (by norm_num)
  have hdiff : (4 : ℝ) ^ k ≠ (4 : ℝ) ^ n := by
    intro heq
    have : (4 : ℝ) ^ n / 4 < (4 : ℝ) ^ n := by nlinarith
    linarith
  have hsum : (4 : ℝ) ^ k + (4 : ℝ) ^ n ≠ 0 := by positivity
  have hgap : (3 / 4 : ℝ) * (4 : ℝ) ^ n ≤ (4 : ℝ) ^ n - (4 : ℝ) ^ k := by
    linarith
  have hgap' : (3 / 4 : ℝ) * (4 : ℝ) ^ n ≤
      |(4 : ℝ) ^ k - (4 : ℝ) ^ n| := by
    rw [abs_of_neg (sub_neg.mpr (by linarith : (4 : ℝ) ^ k < (4 : ℝ) ^ n))]
    linarith
  have hdiff_inv : 1 / |(4 : ℝ) ^ k - (4 : ℝ) ^ n| ≤
      1 / ((3 / 4 : ℝ) * (4 : ℝ) ^ n) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact hgap'
  have hsum_inv : 1 / ((4 : ℝ) ^ k + (4 : ℝ) ^ n) ≤
      1 / (4 : ℝ) ^ n := by
    apply one_div_le_one_div_of_le hnpos
    linarith
  have hcore := abs_integral_sin_mul_sin_le ((4 : ℝ) ^ k) ((4 : ℝ) ^ n) hdiff hsum
  have hplus : |(4 : ℝ) ^ k + (4 : ℝ) ^ n| = (4 : ℝ) ^ k + (4 : ℝ) ^ n :=
    abs_of_pos (by positivity)
  rw [hplus] at hcore
  calc
    |∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ k * t) *
        Real.sin ((4 : ℝ) ^ n * t)| ≤
        (1 / |(4 : ℝ) ^ k - (4 : ℝ) ^ n| +
          1 / ((4 : ℝ) ^ k + (4 : ℝ) ^ n)) / 2 := hcore
    _ ≤ (1 / ((3 / 4 : ℝ) * (4 : ℝ) ^ n) +
          1 / (4 : ℝ) ^ n) / 2 := by
        apply div_le_div_of_nonneg_right (add_le_add hdiff_inv hsum_inv) (by norm_num)
    _ ≤ 2 / (4 : ℝ) ^ n := by
      have hM : 0 < (4 : ℝ) ^ n := hnpos
      have heq : (1 / ((3 / 4 : ℝ) * (4 : ℝ) ^ n) +
          1 / (4 : ℝ) ^ n) / 2 = (7 / 6 : ℝ) / (4 : ℝ) ^ n := by
        field_simp
        ring
      rw [heq]
      exact div_le_div_of_nonneg_right (by norm_num : (7 / 6 : ℝ) ≤ 2) (le_of_lt hM)

/-- 異なる層と試験正弦との積分は、試験周波数の逆数で一様に抑えられる。 -/
theorem abs_integral_sin_pow_mul_sin_pow_of_ne (k n : ℕ) (hkn : k ≠ n) :
    |∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ k * t) *
      Real.sin ((4 : ℝ) ^ n * t)| ≤ 2 / (4 : ℝ) ^ n := by
  rcases lt_or_gt_of_ne hkn with hlt | hgt
  · exact abs_integral_sin_pow_mul_sin_pow_le k n hlt
  · have hswap :
        (∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ k * t) *
          Real.sin ((4 : ℝ) ^ n * t)) =
        ∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t) *
          Real.sin ((4 : ℝ) ^ k * t) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    have hfreq : (4 : ℝ) ^ n ≤ (4 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hgt.le
    calc
      |∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ k * t) *
          Real.sin ((4 : ℝ) ^ n * t)| =
        |∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t) *
          Real.sin ((4 : ℝ) ^ k * t)| := congrArg abs hswap
      _ ≤ 2 / (4 : ℝ) ^ k := abs_integral_sin_pow_mul_sin_pow_le n k hgt
      _ ≤ 2 / (4 : ℝ) ^ n :=
        div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
          (by positivity) hfreq

/-- 異なる周波数の余弦積も、和差周波数の端点値で積分できる。 -/
theorem integral_cos_mul_cos (a b : ℝ) (hab : a ≠ b) (hsum : a + b ≠ 0) :
    ∫ t in (0 : ℝ)..1, Real.cos (a * t) * Real.cos (b * t) =
      ((Real.sin (a - b) / (a - b)) + (Real.sin (a + b) / (a + b))) / 2 := by
  have hdiff : a - b ≠ 0 := sub_ne_zero.mpr hab
  have htrig (t : ℝ) :
      Real.cos (a * t) * Real.cos (b * t) =
        (Real.cos ((a - b) * t) + Real.cos ((a + b) * t)) / 2 := by
    have h3 : (a - b) * t = a * t - b * t := by ring
    have h4 : (a + b) * t = a * t + b * t := by ring
    rw [h3, h4, Real.cos_sub, Real.cos_add]
    ring
  have hint :
      (∫ t in (0 : ℝ)..1, Real.cos (a * t) * Real.cos (b * t)) =
      (∫ t in (0 : ℝ)..1, (Real.cos ((a - b) * t) + Real.cos ((a + b) * t)) / 2) :=
    intervalIntegral.integral_congr (fun t _ => htrig t)
  have hcos1 (c : ℝ) : IntervalIntegrable (fun t : ℝ => Real.cos (c * t)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => Real.cos (c * t)).intervalIntegrable _ _
  rw [hint, intervalIntegral.integral_div,
    intervalIntegral.integral_add (hcos1 (a - b)) (hcos1 (a + b)),
    integral_cos_scaled (a - b) hdiff, integral_cos_scaled (a + b) hsum]

/-- 周波数が異なる余弦の積分は、和差の逆数で上から抑えられる。 -/
theorem abs_integral_cos_mul_cos_le (a b : ℝ) (hab : a ≠ b) (hsum : a + b ≠ 0) :
    |∫ t in (0 : ℝ)..1, Real.cos (a * t) * Real.cos (b * t)| ≤
      (1 / |a - b| + 1 / |a + b|) / 2 := by
  rw [integral_cos_mul_cos a b hab hsum]
  have hdiv (x : ℝ) (hx : x ≠ 0) : |Real.sin x / x| ≤ 1 / |x| := by
    rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hx)).2
    calc
      |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
      _ = 1 / |x| * |x| := by field_simp [abs_ne_zero.mpr hx]
  calc
    |(Real.sin (a - b) / (a - b) + Real.sin (a + b) / (a + b)) / 2| ≤
        (|Real.sin (a - b) / (a - b)| +
          |Real.sin (a + b) / (a + b)|) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right
        (show |Real.sin (a - b) / (a - b) + Real.sin (a + b) / (a + b)| ≤
          |Real.sin (a - b) / (a - b)| + |Real.sin (a + b) / (a + b)| by
            exact abs_add_le _ _) (by norm_num)
    _ ≤ (1 / |a - b| + 1 / |a + b|) / 2 := by
      apply div_le_div_of_nonneg_right (add_le_add _ _) (by norm_num)
      · exact hdiv _ (sub_ne_zero.mpr hab)
      · exact hdiv _ hsum

/-- 4の冪で周波数を離すと、低周波との交差積分は高周波の逆数で抑えられる。 -/
theorem abs_integral_cos_pow_mul_cos_pow_le (k n : ℕ) (hkn : k < n) :
    |∫ t in (0 : ℝ)..1, Real.cos ((4 : ℝ) ^ k * t) *
      Real.cos ((4 : ℝ) ^ n * t)| ≤ 2 / (4 : ℝ) ^ n := by
  have hpow : (4 : ℝ) ^ (k + 1) ≤ (4 : ℝ) ^ n := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
      (Nat.succ_le_of_lt hkn)
  have hscale : (4 : ℝ) ^ k * 4 ≤ (4 : ℝ) ^ n := by
    simpa [pow_succ] using hpow
  have hkpos : 0 < (4 : ℝ) ^ k := by positivity
  have hnpos : 0 < (4 : ℝ) ^ n := by positivity
  have hfreq : (4 : ℝ) ^ k ≤ (4 : ℝ) ^ n / 4 := by
    calc
      (4 : ℝ) ^ k = ((4 : ℝ) ^ k * 4) / 4 := by field_simp
      _ ≤ (4 : ℝ) ^ n / 4 := div_le_div_of_nonneg_right hscale (by norm_num)
  have hdiff : (4 : ℝ) ^ k ≠ (4 : ℝ) ^ n := by
    intro heq
    have : (4 : ℝ) ^ n / 4 < (4 : ℝ) ^ n := by nlinarith
    linarith
  have hsum : (4 : ℝ) ^ k + (4 : ℝ) ^ n ≠ 0 := by positivity
  have hgap : (3 / 4 : ℝ) * (4 : ℝ) ^ n ≤ (4 : ℝ) ^ n - (4 : ℝ) ^ k := by
    linarith
  have hgap' : (3 / 4 : ℝ) * (4 : ℝ) ^ n ≤
      |(4 : ℝ) ^ k - (4 : ℝ) ^ n| := by
    rw [abs_of_neg (sub_neg.mpr (by linarith : (4 : ℝ) ^ k < (4 : ℝ) ^ n))]
    linarith
  have hdiff_inv : 1 / |(4 : ℝ) ^ k - (4 : ℝ) ^ n| ≤
      1 / ((3 / 4 : ℝ) * (4 : ℝ) ^ n) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact hgap'
  have hsum_inv : 1 / ((4 : ℝ) ^ k + (4 : ℝ) ^ n) ≤
      1 / (4 : ℝ) ^ n := by
    apply one_div_le_one_div_of_le hnpos
    linarith
  have hcore := abs_integral_cos_mul_cos_le ((4 : ℝ) ^ k) ((4 : ℝ) ^ n) hdiff hsum
  have hplus : |(4 : ℝ) ^ k + (4 : ℝ) ^ n| = (4 : ℝ) ^ k + (4 : ℝ) ^ n :=
    abs_of_pos (by positivity)
  rw [hplus] at hcore
  calc
    |∫ t in (0 : ℝ)..1, Real.cos ((4 : ℝ) ^ k * t) *
        Real.cos ((4 : ℝ) ^ n * t)| ≤
        (1 / |(4 : ℝ) ^ k - (4 : ℝ) ^ n| +
          1 / ((4 : ℝ) ^ k + (4 : ℝ) ^ n)) / 2 := hcore
    _ ≤ (1 / ((3 / 4 : ℝ) * (4 : ℝ) ^ n) +
          1 / (4 : ℝ) ^ n) / 2 := by
        apply div_le_div_of_nonneg_right (add_le_add hdiff_inv hsum_inv) (by norm_num)
    _ ≤ 2 / (4 : ℝ) ^ n := by
      have hM : 0 < (4 : ℝ) ^ n := hnpos
      have : (1 / ((3 / 4 : ℝ) * (4 : ℝ) ^ n) +
          1 / (4 : ℝ) ^ n) / 2 = (7 / 6 : ℝ) / (4 : ℝ) ^ n := by
        field_simp
        ring
      rw [this]
      apply div_le_div_of_nonneg_right (by norm_num : (7 / 6 : ℝ) ≤ 2) (le_of_lt hM)

/-- 高周波成分以外の一層が、試験余弦に与える寄与の上界。 -/
theorem layer_cos_coefficient_bound (k n : ℕ) (hkn : k < n) :
    |∫ t in (0 : ℝ)..1, h k t * Real.cos ((4 : ℝ) ^ n * t)| ≤
      (2 : ℝ) ^ k * (2 / (4 : ℝ) ^ n) := by
  have hrewrite :
      (∫ t in (0 : ℝ)..1, h k t * Real.cos ((4 : ℝ) ^ n * t)) =
        (2 : ℝ) ^ k * (∫ t in (0 : ℝ)..1,
          Real.cos ((4 : ℝ) ^ k * t) * Real.cos ((4 : ℝ) ^ n * t)) := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          (2 : ℝ) ^ k * (Real.cos ((4 : ℝ) ^ k * t) *
            Real.cos ((4 : ℝ) ^ n * t)) := by
          apply intervalIntegral.integral_congr
          intro t _
          simp [h]
          ring_nf
      _ = _ := intervalIntegral.integral_const_mul ((2 : ℝ) ^ k)
        (fun t : ℝ => Real.cos ((4 : ℝ) ^ k * t) * Real.cos ((4 : ℝ) ^ n * t))
  rw [hrewrite, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_cos_pow_mul_cos_pow_le k n hkn) (by positivity)

/-- 対角層の余弦係数は周波数の大きさに比例して下から評価できる。 -/
theorem diagonal_cos_coefficient_lower (n : ℕ) :
    (2 : ℝ) ^ n * (1 / 2 - 1 / (4 * (4 : ℝ) ^ n)) ≤
      ∫ t in (0 : ℝ)..1, h n t * Real.cos ((4 : ℝ) ^ n * t) := by
  have heq :
      (∫ t in (0 : ℝ)..1, h n t * Real.cos ((4 : ℝ) ^ n * t)) =
        (2 : ℝ) ^ n * (∫ t in (0 : ℝ)..1, Real.cos ((4 : ℝ) ^ n * t) ^ 2) := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          (2 : ℝ) ^ n * Real.cos ((4 : ℝ) ^ n * t) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t _
          simp [h]
          ring
      _ = _ := intervalIntegral.integral_const_mul ((2 : ℝ) ^ n)
        (fun t : ℝ => Real.cos ((4 : ℝ) ^ n * t) ^ 2)
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (integral_cos_sq_lower ((4 : ℝ) ^ n) (by positivity)) (by positivity)

/-- 低周波層の振幅和は`2^n`以下である。 -/
theorem sum_two_pow_range_le (n : ℕ) :
    (∑ k ∈ Finset.range n, (2 : ℝ) ^ k) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [ih]

/-- 有限導関数和の`4^N`係数は対角項が支配し、L¹ノルムは指数的に大きくなる。 -/
theorem partialDerivative_cos_integral_lower (N : ℕ) (hN : 3 ≤ N) :
    (2 : ℝ) ^ N / 4 ≤
      ∫ t in (0 : ℝ)..1, partialDerivative N t * Real.cos ((4 : ℝ) ^ N * t) := by
  let q : ℕ → ℝ := fun k =>
    ∫ t in (0 : ℝ)..1, h k t * Real.cos ((4 : ℝ) ^ N * t)
  have hdecomp :
      (∫ t in (0 : ℝ)..1, partialDerivative N t * Real.cos ((4 : ℝ) ^ N * t)) =
        (∑ k ∈ Finset.range N, q k) + q N := by
    rw [partialDerivative_cos_integral_eq_sum]
    dsimp [q]
    rw [Finset.sum_range_succ]
  have hdiag :
      (2 : ℝ) ^ N * (1 / 2 - 1 / (4 * (4 : ℝ) ^ N)) ≤ q N := by
    exact diagonal_cos_coefficient_lower N
  have hc : 0 ≤ (2 : ℝ) / (4 : ℝ) ^ N := by positivity
  have herror :
      -(2 : ℝ) ^ N * ((2 : ℝ) / (4 : ℝ) ^ N) ≤
        ∑ k ∈ Finset.range N, q k := by
    calc
      -(2 : ℝ) ^ N * ((2 : ℝ) / (4 : ℝ) ^ N) ≤
          -((∑ k ∈ Finset.range N, (2 : ℝ) ^ k) *
            ((2 : ℝ) / (4 : ℝ) ^ N)) := by
              calc
                _ = -((2 : ℝ) ^ N * ((2 : ℝ) / (4 : ℝ) ^ N)) := by ring
                _ ≤ _ := neg_le_neg
                  (mul_le_mul_of_nonneg_right (sum_two_pow_range_le N) hc)
      _ = ∑ k ∈ Finset.range N, -((2 : ℝ) ^ k *
            ((2 : ℝ) / (4 : ℝ) ^ N)) := by
              rw [Finset.sum_mul, Finset.sum_neg_distrib]
      _ ≤ ∑ k ∈ Finset.range N, q k := by
              apply Finset.sum_le_sum
              intro k hk
              exact neg_le_of_abs_le (layer_cos_coefficient_bound k N
                (Finset.mem_range.mp hk))
  have hy : (64 : ℝ) ≤ (4 : ℝ) ^ N := by
    calc
      (64 : ℝ) = (4 : ℝ) ^ 3 := by norm_num
      _ ≤ (4 : ℝ) ^ N := by
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hN
  have hx : (8 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc
      (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ N := by
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN
  have hdiagFactor : (1 / 2 - 1 / (4 * (4 : ℝ) ^ N)) ≥ 1 / 2 - 1 / 256 := by
    have hinv : 1 / (4 * (4 : ℝ) ^ N) ≤ (1 / 256 : ℝ) := by
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 256)
      nlinarith
    linarith
  have herrorAbs :
      (2 : ℝ) ^ N * ((2 : ℝ) / (4 : ℝ) ^ N) ≤ 1 / 4 := by
    have hrel : (4 : ℝ) ^ N = (2 : ℝ) ^ N * (2 : ℝ) ^ N := by
      rw [← mul_pow]
      norm_num
    rw [hrel]
    have hxpos : 0 < (2 : ℝ) ^ N := by positivity
    field_simp
    nlinarith [hx]
  rw [hdecomp]
  have hlower := add_le_add herror hdiag
  have hfinal :
      (2 : ℝ) ^ N / 4 ≤
        (-(2 : ℝ) ^ N * ((2 : ℝ) / (4 : ℝ) ^ N)) +
          (2 : ℝ) ^ N * (1 / 2 - 1 / (4 * (4 : ℝ) ^ N)) := by
    nlinarith [hdiagFactor, herrorAbs, hx]
  linarith

/-- 試験余弦の積分係数は、導関数の`L¹`ノルム以下である。 -/
theorem partialDerivative_cos_integral_le_l1 (N : ℕ) :
    |∫ t in (0 : ℝ)..1, partialDerivative N t * Real.cos ((4 : ℝ) ^ N * t)| ≤
      ∫ t in (0 : ℝ)..1, |partialDerivative N t| := by
  have hcont : Continuous fun t : ℝ =>
      partialDerivative N t * Real.cos ((4 : ℝ) ^ N * t) := by
    unfold partialDerivative h
    fun_prop
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun t : ℝ => partialDerivative N t * Real.cos ((4 : ℝ) ^ N * t))
  have hmono :
      (∫ t in (0 : ℝ)..1,
        |partialDerivative N t * Real.cos ((4 : ℝ) ^ N * t)|) ≤
      ∫ t in (0 : ℝ)..1, |partialDerivative N t| := by
    have hD : Continuous fun t : ℝ => partialDerivative N t := by
      unfold partialDerivative h
      fun_prop
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hcont.abs.intervalIntegrable (μ := volume) 0 1)
      (hD.abs.intervalIntegrable (μ := volume) 0 1)
    intro t _
    rw [abs_mul]
    calc
      |partialDerivative N t| * |Real.cos ((4 : ℝ) ^ N * t)| ≤
          |partialDerivative N t| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |partialDerivative N t| := by ring
  simpa only [Real.norm_eq_abs] using hnorm.trans hmono

/-- 有限部分和の導関数の`L¹`ノルムは少なくとも`2^N/4`となる。 -/
theorem partialDerivative_l1_lower (N : ℕ) (hN : 3 ≤ N) :
    (2 : ℝ) ^ N / 4 ≤ ∫ t in (0 : ℝ)..1, |partialDerivative N t| := by
  have hc := partialDerivative_cos_integral_lower N hN
  have hl1 := partialDerivative_cos_integral_le_l1 N
  have htarget : 0 ≤ (2 : ℝ) ^ N / 4 := by positivity
  have hpos : 0 ≤ ∫ t in (0 : ℝ)..1,
      partialDerivative N t * Real.cos ((4 : ℝ) ^ N * t) := htarget.trans hc
  rw [abs_of_nonneg hpos] at hl1
  linarith

/-- 滑らかな関数が有界変動なら、導関数のL¹積分はその全変動以下である。 -/
theorem integral_abs_deriv_le_variation (f : ℝ → ℝ)
    (hfc : Continuous (deriv f))
    (hBV : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) :
    ∫ t in (0 : ℝ)..1, |deriv f t| ≤
      variationOnFromTo f (Set.Icc (0 : ℝ) 1) 0 1 := by
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  have hloc : LocallyBoundedVariationOn f s := by
    simpa [s] using hBV.locallyBoundedVariationOn
  obtain ⟨p, q, hp, hq, hf, hvar⟩ := hloc.exists_monotoneOn_sub_monotoneOn'
  have hpIcc : MonotoneOn p (Set.uIcc (0 : ℝ) 1) := by
    simpa [s, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hp
  have hqIcc : MonotoneOn q (Set.uIcc (0 : ℝ) 1) := by
    simpa [s, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hq
  have hpder : IntervalIntegrable (deriv p) volume 0 1 := by
    exact hpIcc.intervalIntegrable_deriv
  have hqder : IntervalIntegrable (deriv q) volume 0 1 := by
    exact hqIcc.intervalIntegrable_deriv
  have hleft : IntervalIntegrable (fun t : ℝ => |deriv f t|) volume 0 1 :=
    hfc.abs.intervalIntegrable 0 1
  have hright : IntervalIntegrable (fun t : ℝ => deriv p t + deriv q t) volume 0 1 :=
    hpder.add hqder
  have hinterior : ∀ᵐ t ∂(volume.restrict s), t ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
    have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff, measure_singleton]
    filter_upwards [hne0, hne1] with t ht0 ht1 hts
    exact ⟨lt_of_le_of_ne hts.1 ht0.symm, lt_of_le_of_ne hts.2 ht1⟩
  have hpae : ∀ᵐ t ∂(volume.restrict s), DifferentiableWithinAt ℝ p s t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    simpa [s] using hp.ae_differentiableWithinAt_of_mem
  have hqae : ∀ᵐ t ∂(volume.restrict s), DifferentiableWithinAt ℝ q s t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    simpa [s] using hq.ae_differentiableWithinAt_of_mem
  have hpoint :
      (fun t : ℝ => |deriv f t|) ≤ᵐ[volume.restrict s]
        (fun t => deriv p t + deriv q t) := by
    filter_upwards [hpae, hqae, hinterior] with t hpt hqt ht
    have hts : t ∈ s := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hpd : DifferentiableAt ℝ p t :=
      hpt.differentiableAt (Icc_mem_nhds ht.1 ht.2)
    have hqd : DifferentiableAt ℝ q t :=
      hqt.differentiableAt (Icc_mem_nhds ht.1 ht.2)
    have hpnonneg : 0 ≤ deriv p t := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      exact hp.derivWithin_nonneg
    have hqnonneg : 0 ≤ deriv q t := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      exact hq.derivWithin_nonneg
    have hderiv : deriv f t = deriv p t - deriv q t := by
      rw [hf, deriv_sub hpd hqd]
    calc
      |deriv f t| = |deriv p t - deriv q t| := by rw [hderiv]
      _ ≤ |deriv p t| + |deriv q t| := abs_sub _ _
      _ = deriv p t + deriv q t := by
        rw [abs_of_nonneg hpnonneg, abs_of_nonneg hqnonneg]
  have hmono := intervalIntegral.integral_mono_ae_restrict (by norm_num)
    hleft hright hpoint
  have hpint := hpIcc.intervalIntegral_deriv_mem_uIcc (a := (0 : ℝ)) (b := 1)
  have hqint := hqIcc.intervalIntegral_deriv_mem_uIcc (a := (0 : ℝ)) (b := 1)
  have hple : p 0 ≤ p 1 := hp (by simp [s]) (by simp [s]) (by norm_num)
  have hqle : q 0 ≤ q 1 := hq (by simp [s]) (by simp [s]) (by norm_num)
  rw [Set.uIcc_of_le (sub_nonneg.mpr hple), Set.mem_Icc] at hpint
  rw [Set.uIcc_of_le (sub_nonneg.mpr hqle), Set.mem_Icc] at hqint
  have hvar01 := hvar 0 (by simp [s]) 1 (by simp [s])
  calc
    ∫ t in (0 : ℝ)..1, |deriv f t| ≤
        (∫ t in (0 : ℝ)..1, deriv p t) + ∫ t in (0 : ℝ)..1, deriv q t := by
          simpa [intervalIntegral.integral_add hpder hqder] using hmono
    _ ≤ (p 1 - p 0) + (q 1 - q 0) := add_le_add hpint.2 hqint.2
    _ = variationOnFromTo f s 0 1 := hvar01

/-- 有限部分和の全変動は`2^N/4`以上となり、したがって一様に有界ではない。 -/
theorem partialSum_variation_lower (N : ℕ) (hN : 3 ≤ N) :
    ENNReal.ofReal ((2 : ℝ) ^ N / 4) ≤
      eVariationOn (partialSum N) (Set.Icc (0 : ℝ) 1) := by
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let v : ENNReal := eVariationOn (partialSum N) s
  change ENNReal.ofReal ((2 : ℝ) ^ N / 4) ≤ v
  by_cases htop : v = ⊤
  · simp [htop]
  · have hBV : BoundedVariationOn (partialSum N) s := htop
    have hcont : Continuous (deriv (partialSum N)) := by
      rw [show deriv (partialSum N) = partialDerivative N from funext (deriv_partialSum N)]
      unfold partialDerivative h
      fun_prop
    have hvar := integral_abs_deriv_le_variation (partialSum N) hcont hBV
    have hlower :
        (2 : ℝ) ^ N / 4 ≤ ∫ t in (0 : ℝ)..1, |deriv (partialSum N) t| := by
      calc
        (2 : ℝ) ^ N / 4 ≤ ∫ t in (0 : ℝ)..1, |partialDerivative N t| :=
          partialDerivative_l1_lower N hN
        _ = ∫ t in (0 : ℝ)..1, |deriv (partialSum N) t| := by
          apply intervalIntegral.integral_congr
          intro t _
          exact congrArg abs (deriv_partialSum N t).symm
    have hreal : (2 : ℝ) ^ N / 4 ≤ v.toReal := by
      have hvar_eq : variationOnFromTo (partialSum N) s 0 1 = v.toReal := by
        rw [variationOnFromTo.eq_of_le (partialSum N) s (by norm_num)]
        simp [v, s]
      rw [hvar_eq] at hvar
      exact hlower.trans hvar
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal hreal

/-- 各層と試験正弦との積分は、定数項と周波数交差項に分かれる。 -/
theorem H_sin_integral_decomp (k n : ℕ) :
    ∫ t in (0 : ℝ)..1, H k t * Real.sin ((4 : ℝ) ^ n * t) =
      (1 / 2 : ℝ) ^ k *
        ((∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t)) +
          (∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ k * t) *
            Real.sin ((4 : ℝ) ^ n * t))) := by
  have hfun (t : ℝ) : H k t * Real.sin ((4 : ℝ) ^ n * t) =
      (1 / 2 : ℝ) ^ k * Real.sin ((4 : ℝ) ^ n * t) +
        (1 / 2 : ℝ) ^ k *
          (Real.sin ((4 : ℝ) ^ k * t) * Real.sin ((4 : ℝ) ^ n * t)) := by
    unfold H
    ring
  have hi1 : IntervalIntegrable
      (fun t : ℝ => (1 / 2 : ℝ) ^ k * Real.sin ((4 : ℝ) ^ n * t)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => (1 / 2 : ℝ) ^ k * Real.sin ((4 : ℝ) ^ n * t))
      |>.intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun t : ℝ => (1 / 2 : ℝ) ^ k *
        (Real.sin ((4 : ℝ) ^ k * t) * Real.sin ((4 : ℝ) ^ n * t))) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => (1 / 2 : ℝ) ^ k *
      (Real.sin ((4 : ℝ) ^ k * t) * Real.sin ((4 : ℝ) ^ n * t)))
      |>.intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun t _ => hfun t),
    intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring_nf

/-- 対角層以外の`H_k`の試験積分は、重み付きで周波数の逆数以下。 -/
theorem layer_H_sine_coefficient_bound (k n : ℕ) (hkn : k ≠ n) :
    |∫ t in (0 : ℝ)..1, H k t * Real.sin ((4 : ℝ) ^ n * t)| ≤
      (1 / 2 : ℝ) ^ k * (4 / (4 : ℝ) ^ n) := by
  rw [H_sin_integral_decomp]
  have hfreq : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hconst := abs_integral_sin_scaled_le ((4 : ℝ) ^ n) (ne_of_gt hfreq)
  have hcross := abs_integral_sin_pow_mul_sin_pow_of_ne k n hkn
  have hconst' :
      |∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t)| ≤
        2 / (4 : ℝ) ^ n := by
    have habs : |(4 : ℝ) ^ n| = (4 : ℝ) ^ n := abs_of_pos hfreq
    simpa [habs] using hconst
  rw [abs_mul]
  rw [abs_of_pos (by positivity : 0 < (1 / 2 : ℝ) ^ k)]
  calc
    (1 / 2 : ℝ) ^ k *
        |(∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t)) +
          (∫ t in (0 : ℝ)..1,
            Real.sin ((4 : ℝ) ^ k * t) * Real.sin ((4 : ℝ) ^ n * t))| ≤
      (1 / 2 : ℝ) ^ k *
        (|(∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t))| +
          |(∫ t in (0 : ℝ)..1,
            Real.sin ((4 : ℝ) ^ k * t) * Real.sin ((4 : ℝ) ^ n * t))|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
    _ ≤ (1 / 2 : ℝ) ^ k * (2 / (4 : ℝ) ^ n + 2 / (4 : ℝ) ^ n) := by
      gcongr
    _ = (1 / 2 : ℝ) ^ k * (4 / (4 : ℝ) ^ n) := by ring

/-- 無限和の`4^n`正弦係数は対角層が支配し、`2^{-n}/8`以上となる。 -/
theorem infiniteSum_sine_coefficient_lower (n : ℕ) (hn : 6 ≤ n) :
    (1 / 2 : ℝ) ^ n / 8 ≤
      ∫ t in (0 : ℝ)..1, infiniteSum t * Real.sin ((4 : ℝ) ^ n * t) := by
  let term (k : ℕ) : ℝ :=
    ∫ t in (0 : ℝ)..1, H k t * Real.sin ((4 : ℝ) ^ n * t)
  let remainder (k : ℕ) : ℝ := if k = n then 0 else term k
  have hterms : Summable term := by
    simpa [term] using summable_layer_sine_integrals ((4 : ℝ) ^ n)
  have hremBound (k : ℕ) : ‖remainder k‖ ≤ (1 / 2 : ℝ) ^ k * (4 / (4 : ℝ) ^ n) := by
    by_cases hkn : k = n
    · simp [remainder, hkn]
      positivity
    · simp only [Real.norm_eq_abs, remainder, if_neg hkn]
      exact layer_H_sine_coefficient_bound k n hkn
  have hgeom : Summable fun k : ℕ => (1 / 2 : ℝ) ^ k * (4 / (4 : ℝ) ^ n) := by
    exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_right _
  have hrem : Summable remainder :=
    Summable.of_norm_bounded hgeom hremBound
  have hremNorm := norm_tsum_le_tsum_norm hrem.norm
  have hremSum :
      ‖∑' k : ℕ, remainder k‖ ≤ 8 / (4 : ℝ) ^ n := by
    calc
      _ ≤ ∑' k : ℕ, ‖remainder k‖ := hremNorm
      _ ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k * (4 / (4 : ℝ) ^ n) :=
        Summable.tsum_le_tsum hremBound hrem.norm hgeom
      _ = 8 / (4 : ℝ) ^ n := by
        rw [show (fun k : ℕ => (1 / 2 : ℝ) ^ k * (4 / (4 : ℝ) ^ n)) =
          (fun k => (4 / (4 : ℝ) ^ n) * (1 / 2 : ℝ) ^ k) by
            funext k
            ring,
          tsum_mul_left,
          tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
            (by norm_num : (1 / 2 : ℝ) < 1)]
        norm_num
        ring
  have hdiag :
      (1 / 2 : ℝ) ^ n * (1 / 2 - 9 / (4 * (4 : ℝ) ^ n)) ≤ term n := by
    change (1 / 2 : ℝ) ^ n * (1 / 2 - 9 / (4 * (4 : ℝ) ^ n)) ≤
      ∫ t in (0 : ℝ)..1, H n t * Real.sin ((4 : ℝ) ^ n * t)
    have hdiagprod :
        (∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t) *
          Real.sin ((4 : ℝ) ^ n * t)) =
        ∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    have hconst :
        -(2 / (4 : ℝ) ^ n) ≤ ∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t) := by
      have h := abs_integral_sin_scaled_le ((4 : ℝ) ^ n) (ne_of_gt (by positivity))
      have hpos : |(4 : ℝ) ^ n| = (4 : ℝ) ^ n := abs_of_pos (by positivity)
      have h' : |∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t)| ≤
          2 / (4 : ℝ) ^ n := by simpa [hpos] using h
      exact neg_le_of_abs_le h'
    have hsq := integral_sin_sq_lower ((4 : ℝ) ^ n) (by positivity)
    have hw : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    calc
      (1 / 2 : ℝ) ^ n * (1 / 2 - 9 / (4 * (4 : ℝ) ^ n)) ≤
          (1 / 2 : ℝ) ^ n *
            (-(2 / (4 : ℝ) ^ n) + (1 / 2 - 1 / (4 * (4 : ℝ) ^ n))) := by
              ring_nf
              nlinarith
      _ ≤ (1 / 2 : ℝ) ^ n *
            ((∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t)) +
              (∫ t in (0 : ℝ)..1, Real.sin ((4 : ℝ) ^ n * t) ^ 2)) := by
              gcongr
      _ = ∫ t in (0 : ℝ)..1, H n t * Real.sin ((4 : ℝ) ^ n * t) := by
        rw [H_sin_integral_decomp n n, hdiagprod]
  have hsplit :
      (∑' k : ℕ, term k) = term n + ∑' k : ℕ, remainder k := by
    calc
      (∑' k : ℕ, term k) = term n +
          ∑' k : ℕ, ite (k = n) 0 (term k) := hterms.tsum_eq_add_tsum_ite n
      _ = term n + ∑' k : ℕ, remainder k := by
        exact congrArg (fun x : ℝ => term n + x) (tsum_congr fun k => by
          by_cases hkn : k = n <;> simp [remainder, hkn]
        )
  have hintegral := integral_infiniteSum_sin_eq_tsum ((4 : ℝ) ^ n)
  have hdiagLower : (1 / 2 : ℝ) ^ n / 8 ≤ term n - 8 / (4 : ℝ) ^ n := by
    have h4pow : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      calc
        (4 : ℝ) ^ n = (2 * 2 : ℝ) ^ n := by norm_num
        _ = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by rw [mul_pow]
        _ = ((2 : ℝ) ^ n) ^ 2 := by ring
    have hx : (64 : ℝ) ≤ (2 : ℝ) ^ n := by
      calc
        (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
        _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    have hM : (1024 : ℝ) ≤ (4 : ℝ) ^ n := by
      rw [h4pow]
      nlinarith [hx]
    have hdiagFactor :
        (1 / 2 - 9 / (4 * (4 : ℝ) ^ n)) ≥ 1 / 4 := by
      have hinv : 9 / (4 * (4 : ℝ) ^ n) ≤ (1 / 4 : ℝ) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (4 : ℝ) ^ n)]
        nlinarith
      linarith
    have hremRel : 8 / (4 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ n / 8 := by
      rw [h4pow]
      have hxpos : 0 < (2 : ℝ) ^ n := by positivity
      have hxy : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      field_simp
      nlinarith [hx, hxy]
    have hpos : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    have hdiagQuarter : (1 / 2 : ℝ) ^ n / 4 ≤ term n := by
      calc
      (1 / 2 : ℝ) ^ n / 4 = (1 / 2 : ℝ) ^ n * (1 / 4 : ℝ) := by ring
        _ ≤ (1 / 2 : ℝ) ^ n *
            (1 / 2 - 9 / (4 * (4 : ℝ) ^ n)) := by
              exact mul_le_mul_of_nonneg_left (show (1 / 4 : ℝ) ≤
                1 / 2 - 9 / (4 * (4 : ℝ) ^ n) from hdiagFactor) hpos
        _ ≤ term n := hdiag
    calc
      (1 / 2 : ℝ) ^ n / 8 ≤ (1 / 2 : ℝ) ^ n / 4 -
          (1 / 2 : ℝ) ^ n / 8 := by
        exact le_of_eq (by ring)
      _ ≤ term n - 8 / (4 : ℝ) ^ n := by linarith [hdiagQuarter, hremRel]
  have htotal :
      (1 / 2 : ℝ) ^ n / 8 ≤ term n + ∑' k : ℕ, remainder k := by
    have hremLower : -(8 / (4 : ℝ) ^ n) ≤ ∑' k : ℕ, remainder k := by
      have := hremSum
      rw [Real.norm_eq_abs] at this
      exact neg_le_of_abs_le this
    linarith
  rw [hintegral, hsplit]
  exact htotal

/-- 区間上の単調関数を、端点値で定数延長できるよう実数全体へ単調に延長するための切詰め。 -/
def bvIntervalClamp (x : ℝ) : ℝ := max 0 (min x 1)

theorem bvIntervalClamp_monotone : Monotone bvIntervalClamp := by
  intro x y hxy
  exact max_le_max_left 0 (min_le_min_right 1 hxy)

theorem bvIntervalClamp_mem (x : ℝ) : bvIntervalClamp x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

/-- `[0,1]` 上の単調関数を切詰め写像と合成した単調延長。 -/
noncomputable def bvMonotoneExtension (p : ℝ → ℝ) : ℝ → ℝ :=
  fun x => p (bvIntervalClamp x)

theorem bvMonotoneExtension_monotone (p : ℝ → ℝ)
    (hp : MonotoneOn p (Set.Icc (0 : ℝ) 1)) :
    Monotone (bvMonotoneExtension p) := by
  intro x y hxy
  exact hp (bvIntervalClamp_mem x) (bvIntervalClamp_mem y)
    (bvIntervalClamp_monotone hxy)

theorem bvIntervalClamp_continuous : Continuous bvIntervalClamp := by
  unfold bvIntervalClamp
  fun_prop

theorem bvMonotoneExtension_rightLim_one (p : ℝ → ℝ)
    (hp : MonotoneOn p (Set.Icc (0 : ℝ) 1)) :
    Function.rightLim (bvMonotoneExtension p) 1 = p 1 := by
  have hevent : (fun x => bvMonotoneExtension p x) =ᶠ[𝓝[>] (1 : ℝ)] fun _ => p 1 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (1 : ℝ) < x := hx
    simp [bvMonotoneExtension, bvIntervalClamp, hx'.le]
  exact rightLim_eq_of_tendsto (tendsto_const_nhds.congr' hevent.symm)

theorem bvMonotoneExtension_le_rightLim_zero (p : ℝ → ℝ)
    (hp : MonotoneOn p (Set.Icc (0 : ℝ) 1)) :
    p 0 ≤ Function.rightLim (bvMonotoneExtension p) 0 := by
  have h := (bvMonotoneExtension_monotone p hp).le_rightLim (le_refl (0 : ℝ))
  simpa [bvMonotoneExtension, bvIntervalClamp] using h

theorem bvMonotoneExtension_stieltjes_mass (p : ℝ → ℝ)
    (hp : MonotoneOn p (Set.Icc (0 : ℝ) 1)) :
    ((((bvMonotoneExtension_monotone p hp).stieltjesFunction).measure.restrict
        (Set.Ioc (0 : ℝ) 1)) Set.univ).toReal =
      p 1 - Function.rightLim (bvMonotoneExtension p) 0 := by
  have hmeasure :
      (((bvMonotoneExtension_monotone p hp).stieltjesFunction).measure.restrict
        (Set.Ioc (0 : ℝ) 1)) Set.univ =
      ENNReal.ofReal (p 1 - Function.rightLim (bvMonotoneExtension p) 0) := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      StieltjesFunction.measure_Ioc]
    change ENNReal.ofReal (Function.rightLim (bvMonotoneExtension p) 1 -
      Function.rightLim (bvMonotoneExtension p) 0) = _
    rw [bvMonotoneExtension_rightLim_one p hp]
  have hinc : Function.rightLim (bvMonotoneExtension p) 0 ≤ p 1 := by
    have h := (bvMonotoneExtension_monotone p hp).rightLim
      (show (0 : ℝ) ≤ 1 by norm_num)
    simpa [bvMonotoneExtension_rightLim_one p hp] using h
  rw [hmeasure]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr hinc)

theorem bvMonotoneExtension_rightLim_sub_eq (f p q : ℝ → ℝ)
    (hf : Continuous f)
    (hp : MonotoneOn p (Set.Icc (0 : ℝ) 1))
    (hq : MonotoneOn q (Set.Icc (0 : ℝ) 1))
    (hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = p x - q x)
    (x : ℝ) :
    Function.rightLim (bvMonotoneExtension p) x -
        Function.rightLim (bvMonotoneExtension q) x =
      f (bvIntervalClamp x) := by
  have hpoint (y : ℝ) : bvMonotoneExtension p y - bvMonotoneExtension q y =
      f (bvIntervalClamp y) := by
    have hy := hsub (bvIntervalClamp y) (bvIntervalClamp_mem y)
    simpa [bvMonotoneExtension] using hy.symm
  have hpconv := (bvMonotoneExtension_monotone p hp).tendsto_rightLim x
  have hqconv := (bvMonotoneExtension_monotone q hq).tendsto_rightLim x
  have hdiff := hpconv.sub hqconv
  have hcont : Continuous (fun y => f (bvIntervalClamp y)) := hf.comp bvIntervalClamp_continuous
  have hcontAt : ContinuousAt (fun y => f (bvIntervalClamp y)) x := hcont.continuousAt
  have htarget : Tendsto (fun y => f (bvIntervalClamp y)) (𝓝[>] x)
      (𝓝 (f (bvIntervalClamp x))) :=
    hcontAt.tendsto.mono_left (nhdsWithin_le_nhds (a := x) (s := Set.Ioi x))
  have htarget' : Tendsto (fun y => bvMonotoneExtension p y - bvMonotoneExtension q y)
      (𝓝[>] x) (𝓝 (f (bvIntervalClamp x))) := by
    exact htarget.congr' (Eventually.of_forall fun y => (hpoint y).symm)
  exact tendsto_nhds_unique hdiff htarget'

/-- 単調延長に対応するStieltjes測度は、区間 `(0,t]` 上で右極限の増分を持つ。 -/
theorem bvMonotoneExtension_stieltjes_increment (p : ℝ → ℝ)
    (hp : MonotoneOn p (Set.Icc (0 : ℝ) 1)) (t : ℝ) :
    ((bvMonotoneExtension_monotone p hp).stieltjesFunction).measure (Set.Ioc 0 t) =
      ENNReal.ofReal
        (Function.rightLim (bvMonotoneExtension p) t -
      Function.rightLim (bvMonotoneExtension p) 0) := by
  exact StieltjesFunction.measure_Ioc _ _ _

theorem bvMonotoneExtension_stieltjes_locallyFinite (p : ℝ → ℝ)
    (hp : MonotoneOn p (Set.Icc (0 : ℝ) 1)) :
    IsFiniteMeasure
      (((bvMonotoneExtension_monotone p hp).stieltjesFunction).measure.restrict
        (Set.Ioc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter]
  rw [StieltjesFunction.measure_Ioc]
  exact ENNReal.ofReal_lt_top

/-- 制限Stieltjes測度の累積量は、単調延長の右極限の増分そのものである。 -/
theorem bvMonotoneExtension_stieltjes_cumulative (p : ℝ → ℝ)
    (hp : MonotoneOn p (Set.Icc (0 : ℝ) 1)) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((((bvMonotoneExtension_monotone p hp).stieltjesFunction).measure.restrict
        (Set.Ioc (0 : ℝ) 1)) (Set.Iic t)).toReal =
      Function.rightLim (bvMonotoneExtension p) t -
        Function.rightLim (bvMonotoneExtension p) 0 := by
  have hset : Set.Iic t ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨hxt, hx0, hx1⟩
      exact ⟨hx0, hxt⟩
    · rintro ⟨hx0, hxt⟩
      exact ⟨hxt, hx0, hxt.trans ht1⟩
  have hmeasure :
      (((bvMonotoneExtension_monotone p hp).stieltjesFunction).measure.restrict
        (Set.Ioc (0 : ℝ) 1)) (Set.Iic t) =
      ENNReal.ofReal (Function.rightLim (bvMonotoneExtension p) t -
        Function.rightLim (bvMonotoneExtension p) 0) := by
    rw [Measure.restrict_apply measurableSet_Iic, hset]
    exact bvMonotoneExtension_stieltjes_increment p hp t
  have hinc : Function.rightLim (bvMonotoneExtension p) 0 ≤
      Function.rightLim (bvMonotoneExtension p) t := by
    exact (bvMonotoneExtension_monotone p hp).rightLim ht0
  rw [hmeasure]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr hinc)

noncomputable def intervalVolume01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

theorem intervalVolume01_finite : IsFiniteMeasure intervalVolume01 := by
  dsimp [intervalVolume01]
  infer_instance

/-- 有限測度について、累積量 `μ((-∞,t])` と正弦の積分を積の測度上の核へ移すFubini公式。 -/
theorem cumulative_sine_integral_fubini (μ : Measure ℝ) [IsFiniteMeasure μ] (ω : ℝ) :
    ∫ t, (μ (Set.Iic t)).toReal * Real.sin (ω * t) ∂intervalVolume01 =
      ∫ s, ∫ t, (if s ≤ t then Real.sin (ω * t) else 0) ∂intervalVolume01 ∂μ := by
  letI : IsFiniteMeasure intervalVolume01 := intervalVolume01_finite
  let K : ℝ × ℝ → ℝ := fun z => if z.1 ≤ z.2 then Real.sin (ω * z.2) else 0
  have hKmeas : Measurable K := by
    exact Measurable.ite measurableSet_le'
      (Real.measurable_sin.comp (measurable_const.mul measurable_snd)) measurable_const
  have hKbound (z : ℝ × ℝ) : ‖K z‖ ≤ 1 := by
    dsimp [K]
    split_ifs
    · simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (ω * z.2)
    · simp
  have hKint : Integrable K (μ.prod intervalVolume01) := by
    have hfinite : (μ.prod intervalVolume01) Set.univ ≠ ⊤ := by simp
    simpa using (Measure.integrableOn_of_bounded hfinite hKmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hKbound)).integrable
  have hleft (t : ℝ) :
      ∫ s, K (s, t) ∂μ = (μ (Set.Iic t)).toReal * Real.sin (ω * t) := by
    have hset : MeasurableSet (Set.Iic t) := measurableSet_Iic
    calc
      ∫ s, K (s, t) ∂μ = ∫ s in Set.Iic t, Real.sin (ω * t) ∂μ := by
        rw [← integral_indicator hset]
        apply integral_congr_ae
        filter_upwards [] with s
        simp [K, Set.indicator]
      _ = (μ (Set.Iic t)).toReal * Real.sin (ω * t) := by
        rw [setIntegral_const]
        simp [measureReal_def, smul_eq_mul, mul_comm]
  calc
    ∫ t, (μ (Set.Iic t)).toReal * Real.sin (ω * t) ∂intervalVolume01
        = ∫ t, ∫ s, K (s, t) ∂μ ∂intervalVolume01 := by
          apply integral_congr_ae
          filter_upwards [] with t
          rw [hleft]
    _ = ∫ z, K z ∂(μ.prod intervalVolume01) :=
      (integral_prod_symm K hKint).symm
    _ = ∫ s, ∫ t, K (s, t) ∂intervalVolume01 ∂μ := integral_prod K hKint
    _ = ∫ s, ∫ t, (if s ≤ t then Real.sin (ω * t) else 0)
          ∂intervalVolume01 ∂μ := by rfl

/-- Fubini交換後の内側積分は、区間 `[s,1]` の正弦積分である。 -/
theorem interval_tail_sine_integral (s ω : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hω : ω ≠ 0) :
    ∫ t, (if s ≤ t then Real.sin (ω * t) else 0) ∂intervalVolume01 =
      (Real.cos (ω * s) - Real.cos ω) / ω := by
  letI : IsFiniteMeasure intervalVolume01 := intervalVolume01_finite
  have hkernel : (fun t : ℝ => if s ≤ t then Real.sin (ω * t) else 0) =
      (Set.Ici s).indicator (fun t => Real.sin (ω * t)) := by
    funext t
    simp [Set.indicator]
  change ∫ t in Set.Icc (0 : ℝ) 1,
    (if s ≤ t then Real.sin (ω * t) else 0) ∂volume = _
  rw [hkernel, setIntegral_indicator measurableSet_Ici]
  have hset : Set.Icc (0 : ℝ) 1 ∩ Set.Ici s = Set.Icc s 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨⟨ht0, ht1⟩, hst⟩
      exact ⟨hst, ht1⟩
    · rintro ⟨hst, ht1⟩
      exact ⟨⟨hs0.trans hst, ht1⟩, hst⟩
  rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs1]
  have hcomp := intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x)
    (a := s) (b := 1) hω
  rw [integral_sin] at hcomp
  simpa [smul_eq_mul, one_div, div_eq_mul_inv, mul_comm] using hcomp

/-- 有限測度の累積正弦係数は、全質量に比例して `1/ω` で減衰する。 -/
theorem finite_cumulative_sine_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ s ∂μ, s ∈ Set.Ioc (0 : ℝ) 1) (ω : ℝ) (hω : 0 < ω) :
    |∫ t, (μ (Set.Iic t)).toReal * Real.sin (ω * t) ∂intervalVolume01| ≤
      (2 / ω) * (μ Set.univ).toReal := by
  letI : IsFiniteMeasure intervalVolume01 := intervalVolume01_finite
  let K : ℝ × ℝ → ℝ := fun z => if z.1 ≤ z.2 then Real.sin (ω * z.2) else 0
  have hKmeas : Measurable K := by
    exact Measurable.ite measurableSet_le'
      (Real.measurable_sin.comp (measurable_const.mul measurable_snd)) measurable_const
  have hKbound (z : ℝ × ℝ) : ‖K z‖ ≤ 1 := by
    dsimp [K]
    split_ifs
    · simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (ω * z.2)
    · simp
  have hKint : Integrable K (μ.prod intervalVolume01) := by
    have hfinite : (μ.prod intervalVolume01) Set.univ ≠ ⊤ := by simp
    simpa using (Measure.integrableOn_of_bounded hfinite hKmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hKbound)).integrable
  let G : ℝ → ℝ := fun s => ∫ t, K (s, t) ∂intervalVolume01
  have hGint : Integrable G μ := by
    simpa [G, K] using hKint.integral_prod_left
  have hGbound (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
      ‖G s‖ ≤ 2 / ω := by
    have htail := interval_tail_sine_integral s ω (le_of_lt hs.1) hs.2 hω.ne'
    rw [show G s = ∫ t, (if s ≤ t then Real.sin (ω * t) else 0)
      ∂intervalVolume01 by rfl, htail]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hω]
    have hnum : |Real.cos (ω * s) - Real.cos ω| ≤ 2 := by
      calc
        |Real.cos (ω * s) - Real.cos ω| ≤ |Real.cos (ω * s)| + |Real.cos ω| := abs_sub _ _
        _ ≤ 2 := by nlinarith [Real.abs_cos_le_one (ω * s), Real.abs_cos_le_one ω]
    exact div_le_div_of_nonneg_right hnum hω.le
  have hGae : (fun s => ‖G s‖) ≤ᵐ[μ] fun _ => 2 / ω := by
    filter_upwards [hsupp] with s hs
    exact hGbound s hs
  have hconst : Integrable (fun _ : ℝ => (2 / ω : ℝ)) μ := integrable_const _
  have hnorm : ‖∫ s, G s ∂μ‖ ≤ ∫ s, ‖G s‖ ∂μ :=
    norm_integral_le_integral_norm (μ := μ) G
  have hnormBound : (∫ s, ‖G s‖ ∂μ) ≤ ∫ s, (2 / ω : ℝ) ∂μ :=
    integral_mono_ae hGint.norm hconst hGae
  have hbound : ‖∫ s, G s ∂μ‖ ≤ (2 / ω) * μ.real Set.univ := by
    calc
      _ ≤ ∫ s, ‖G s‖ ∂μ := hnorm
      _ ≤ ∫ s, (2 / ω : ℝ) ∂μ := hnormBound
      _ = (2 / ω) * μ.real Set.univ := by
        rw [integral_const]
        simp [smul_eq_mul, mul_comm, measureReal_def]
  rw [cumulative_sine_integral_fubini μ ω]
  rw [← Real.norm_eq_abs]
  change ‖∫ s, G s ∂μ‖ ≤ (2 / ω) * (μ Set.univ).toReal
  simpa [measureReal_def] using hbound

/-- 単調関数の右連続代表を、初期値とStieltjes累積項に分けて積分する。 -/
theorem bvMonotoneExtension_sine_integral_decomp (p : ℝ → ℝ)
    (hp : MonotoneOn p (Set.Icc (0 : ℝ) 1)) (ω : ℝ) :
    ∫ t in (0 : ℝ)..1,
        Function.rightLim (bvMonotoneExtension p) t * Real.sin (ω * t) =
      Function.rightLim (bvMonotoneExtension p) 0 *
          (∫ t in (0 : ℝ)..1, Real.sin (ω * t)) +
        ∫ t in (0 : ℝ)..1,
          ((((bvMonotoneExtension_monotone p hp).stieltjesFunction).measure.restrict
            (Set.Ioc (0 : ℝ) 1)) (Set.Iic t)).toReal * Real.sin (ω * t) := by
  let P : ℝ → ℝ := Function.rightLim (bvMonotoneExtension p)
  let μp : Measure ℝ := ((bvMonotoneExtension_monotone p hp).stieltjesFunction).measure.restrict
    (Set.Ioc (0 : ℝ) 1)
  have hPmono : Monotone P := (bvMonotoneExtension_monotone p hp).rightLim
  have hPint : IntervalIntegrable P volume 0 1 := hPmono.intervalIntegrable
  have hsinInt : IntervalIntegrable (fun t : ℝ => Real.sin (ω * t)) volume 0 1 := by
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable
      (μ := volume) 0 1
  have hPsinInt : IntervalIntegrable (fun t => P t * Real.sin (ω * t)) volume 0 1 :=
    hPint.mul_continuousOn (by intro t ht; fun_prop)
  have hconstSinInt : IntervalIntegrable
      (fun t : ℝ => P 0 * Real.sin (ω * t)) volume 0 1 := by
    exact hsinInt.const_mul _
  have hdiffSinInt : IntervalIntegrable
      (fun t : ℝ => P t * Real.sin (ω * t) - P 0 * Real.sin (ω * t)) volume 0 1 :=
    hPsinInt.sub hconstSinInt
  have hcumEq : Set.EqOn
      (fun t : ℝ => (μp (Set.Iic t)).toReal * Real.sin (ω * t))
      (fun t => P t * Real.sin (ω * t) - P 0 * Real.sin (ω * t))
      (Set.uIoc (0 : ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      rcases (show 0 < t ∧ t ≤ 1 by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht) with ⟨hlt, hle⟩
      exact ⟨hlt.le, hle⟩
    have hcum := bvMonotoneExtension_stieltjes_cumulative p hp t ht'.1 ht'.2
    change (μp (Set.Iic t)).toReal = P t - P 0 at hcum
    change (μp (Set.Iic t)).toReal * Real.sin (ω * t) =
      P t * Real.sin (ω * t) - P 0 * Real.sin (ω * t)
    rw [hcum]
    ring
  have hcumSinInt : IntervalIntegrable
      (fun t : ℝ => (μp (Set.Iic t)).toReal * Real.sin (ω * t)) volume 0 1 :=
    (intervalIntegrable_congr hcumEq).2 hdiffSinInt
  calc
    ∫ t in (0 : ℝ)..1, P t * Real.sin (ω * t) =
        ∫ t in (0 : ℝ)..1,
          (P 0 * Real.sin (ω * t) +
            (μp (Set.Iic t)).toReal * Real.sin (ω * t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have hcum := bvMonotoneExtension_stieltjes_cumulative p hp t ht'.1 ht'.2
      change (μp (Set.Iic t)).toReal = P t - P 0 at hcum
      change P t * Real.sin (ω * t) = P 0 * Real.sin (ω * t) +
        (μp (Set.Iic t)).toReal * Real.sin (ω * t)
      rw [hcum]
      ring
    _ = (∫ t in (0 : ℝ)..1, P 0 * Real.sin (ω * t)) +
          ∫ t in (0 : ℝ)..1, (μp (Set.Iic t)).toReal * Real.sin (ω * t) := by
      rw [← intervalIntegral.integral_add hconstSinInt hcumSinInt]
    _ = P 0 * (∫ t in (0 : ℝ)..1, Real.sin (ω * t)) +
          ∫ t in (0 : ℝ)..1, (μp (Set.Iic t)).toReal * Real.sin (ω * t) := by
      rw [intervalIntegral.integral_const_mul]

/-- 区間積分を `[0,1]` 上の制限体積測度の積分として読み替える。 -/
theorem intervalIntegral_eq_intervalVolume01 (g : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..1, g t = ∫ t, g t ∂intervalVolume01 := by
  rw [intervalIntegral.integral_of_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [restrict_Ioc_eq_restrict_Icc]
  rfl

/-- BV関数の高周波正弦係数は、端点値と全変動で定まる `1/ω` 型に抑えられる。 -/
theorem bv_sine_coefficient_bound (f : ℝ → ℝ)
    (hfcont : Continuous f) (hBV : BoundedVariationOn f (Set.Icc (0 : ℝ) 1))
    (ω : ℝ) (hω : 0 < ω) :
    |∫ t in (0 : ℝ)..1, f t * Real.sin (ω * t)| ≤
      (2 * |f 0| + 2 * variationOnFromTo f (Set.Icc (0 : ℝ) 1) 0 1) / ω := by
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  have hloc : LocallyBoundedVariationOn f s := by
    simpa [s] using hBV.locallyBoundedVariationOn
  obtain ⟨p, q, hp, hq, hf, hvar⟩ := hloc.exists_monotoneOn_sub_monotoneOn'
  have hpIcc : MonotoneOn p (Set.Icc (0 : ℝ) 1) := by simpa [s] using hp
  have hqIcc : MonotoneOn q (Set.Icc (0 : ℝ) 1) := by simpa [s] using hq
  let P : ℝ → ℝ := Function.rightLim (bvMonotoneExtension p)
  let Q : ℝ → ℝ := Function.rightLim (bvMonotoneExtension q)
  let μp : Measure ℝ := ((bvMonotoneExtension_monotone p hpIcc).stieltjesFunction).measure.restrict
    (Set.Ioc (0 : ℝ) 1)
  let μq : Measure ℝ := ((bvMonotoneExtension_monotone q hqIcc).stieltjesFunction).measure.restrict
    (Set.Ioc (0 : ℝ) 1)
  have hμpFinite : IsFiniteMeasure μp := by
    dsimp [μp]
    exact bvMonotoneExtension_stieltjes_locallyFinite p hpIcc
  have hμqFinite : IsFiniteMeasure μq := by
    dsimp [μq]
    exact bvMonotoneExtension_stieltjes_locallyFinite q hqIcc
  have hμpSupp : ∀ᵐ x ∂μp, x ∈ Set.Ioc (0 : ℝ) 1 := by
    exact ae_restrict_mem measurableSet_Ioc
  have hμqSupp : ∀ᵐ x ∂μq, x ∈ Set.Ioc (0 : ℝ) 1 := by
    exact ae_restrict_mem measurableSet_Ioc
  have hmassP : (μp Set.univ).toReal = p 1 - P 0 := by
    simpa [μp, P] using bvMonotoneExtension_stieltjes_mass p hpIcc
  have hmassQ : (μq Set.univ).toReal = q 1 - Q 0 := by
    simpa [μq, Q] using bvMonotoneExtension_stieltjes_mass q hqIcc
  have hPsub : P 0 - Q 0 = f 0 := by
    have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = p x - q x := by
      intro x hx
      change f x = (p - q) x
      exact congrFun hf x
    have h := bvMonotoneExtension_rightLim_sub_eq f p q hfcont hpIcc hqIcc hsub 0
    simpa [P, Q, bvIntervalClamp] using h
  have hPdec := bvMonotoneExtension_sine_integral_decomp p hpIcc ω
  have hQdec := bvMonotoneExtension_sine_integral_decomp q hqIcc ω
  have hcoeffEq :
      (∫ t in (0 : ℝ)..1, f t * Real.sin (ω * t)) =
        (P 0 - Q 0) * (∫ t in (0 : ℝ)..1, Real.sin (ω * t)) +
          (∫ t in (0 : ℝ)..1,
            (μp (Set.Iic t)).toReal * Real.sin (ω * t)) -
          (∫ t in (0 : ℝ)..1,
            (μq (Set.Iic t)).toReal * Real.sin (ω * t)) := by
    have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : f t = P t - Q t := by
      have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = p x - q x := by
        intro x hx
        change f x = (p - q) x
        exact congrFun hf x
      have h := bvMonotoneExtension_rightLim_sub_eq f p q hfcont hpIcc hqIcc hsub t
      have hclamp : bvIntervalClamp t = t := by
        simp [bvIntervalClamp, ht.1, ht.2]
      simpa [P, Q, hclamp] using h.symm
    have hint : ∫ t in (0 : ℝ)..1, f t * Real.sin (ω * t) =
        ∫ t in (0 : ℝ)..1, (P t - Q t) * Real.sin (ω * t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      change f t * Real.sin (ω * t) = (P t - Q t) * Real.sin (ω * t)
      rw [hpoint t ht']
    have hPmono : Monotone P := (bvMonotoneExtension_monotone p hpIcc).rightLim
    have hQmono : Monotone Q := (bvMonotoneExtension_monotone q hqIcc).rightLim
    have hPsinInt : IntervalIntegrable (fun t => P t * Real.sin (ω * t)) volume 0 1 :=
      hPmono.intervalIntegrable.mul_continuousOn (by intro t ht; fun_prop)
    have hQsinInt : IntervalIntegrable (fun t => Q t * Real.sin (ω * t)) volume 0 1 :=
      hQmono.intervalIntegrable.mul_continuousOn (by intro t ht; fun_prop)
    rw [hint]
    have hsplit : (fun t : ℝ => (P t - Q t) * Real.sin (ω * t)) =
        (fun t => P t * Real.sin (ω * t) - Q t * Real.sin (ω * t)) := by
      funext t
      ring
    rw [hsplit, intervalIntegral.integral_sub hPsinInt hQsinInt]
    rw [hPdec, hQdec]
    ring
  have hcumP : |∫ t in (0 : ℝ)..1,
      (μp (Set.Iic t)).toReal * Real.sin (ω * t)| ≤ (2 / ω) * (p 1 - P 0) := by
    rw [intervalIntegral_eq_intervalVolume01]
    calc
      _ ≤ (2 / ω) * (μp Set.univ).toReal := finite_cumulative_sine_bound μp hμpSupp ω hω
      _ = (2 / ω) * (p 1 - P 0) := by rw [hmassP]
  have hcumQ : |∫ t in (0 : ℝ)..1,
      (μq (Set.Iic t)).toReal * Real.sin (ω * t)| ≤ (2 / ω) * (q 1 - Q 0) := by
    rw [intervalIntegral_eq_intervalVolume01]
    calc
      _ ≤ (2 / ω) * (μq Set.univ).toReal := finite_cumulative_sine_bound μq hμqSupp ω hω
      _ = (2 / ω) * (q 1 - Q 0) := by rw [hmassQ]
  have hsin : |∫ t in (0 : ℝ)..1, Real.sin (ω * t)| ≤ 2 / ω := by
    simpa [abs_of_pos hω] using abs_integral_sin_scaled_le ω hω.ne'
  have hvar01 := hvar 0 (by simp [s]) 1 (by simp [s])
  have hple : p 0 ≤ P 0 := by
    simpa [P] using bvMonotoneExtension_le_rightLim_zero p hpIcc
  have hqle : q 0 ≤ Q 0 := by
    simpa [Q] using bvMonotoneExtension_le_rightLim_zero q hqIcc
  have hpartsNonneg : 0 ≤ (p 1 - P 0) + (q 1 - Q 0) := by
    have hPmono : P 0 ≤ p 1 := by
      simpa [P, bvMonotoneExtension_rightLim_one p hpIcc] using
        (bvMonotoneExtension_monotone p hpIcc).rightLim (by norm_num : (0 : ℝ) ≤ 1)
    have hQmono : Q 0 ≤ q 1 := by
      simpa [Q, bvMonotoneExtension_rightLim_one q hqIcc] using
        (bvMonotoneExtension_monotone q hqIcc).rightLim (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hpartsLe : (p 1 - P 0) + (q 1 - Q 0) ≤
      variationOnFromTo f s 0 1 := by
    have hpmono : p 0 ≤ p 1 := hpIcc (by norm_num) (by norm_num) (by norm_num)
    have hqmono : q 0 ≤ q 1 := hqIcc (by norm_num) (by norm_num) (by norm_num)
    rw [← hvar01]
    nlinarith [hple, hqle]
  let A := f 0 * (∫ t in (0 : ℝ)..1, Real.sin (ω * t))
  let B := ∫ t in (0 : ℝ)..1, (μp (Set.Iic t)).toReal * Real.sin (ω * t)
  let C := ∫ t in (0 : ℝ)..1, (μq (Set.Iic t)).toReal * Real.sin (ω * t)
  have htriangle : |A + B - C| ≤ |A| + |B| + |C| := by
    calc
      |(A + B) - C| ≤ |A + B| + |C| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (A + B) (-C)
      _ ≤ |A| + |B| + |C| := by linarith [abs_add_le A B]
  rw [hcoeffEq, hPsub]
  calc
    |f 0 * (∫ t in (0 : ℝ)..1, Real.sin (ω * t)) +
        (∫ t in (0 : ℝ)..1, (μp (Set.Iic t)).toReal * Real.sin (ω * t)) -
        (∫ t in (0 : ℝ)..1, (μq (Set.Iic t)).toReal * Real.sin (ω * t))| ≤
      |f 0| * |∫ t in (0 : ℝ)..1, Real.sin (ω * t)| +
        |∫ t in (0 : ℝ)..1, (μp (Set.Iic t)).toReal * Real.sin (ω * t)| +
        |∫ t in (0 : ℝ)..1, (μq (Set.Iic t)).toReal * Real.sin (ω * t)| := by
          simpa [A, B, C, abs_mul] using htriangle
    _ ≤ |f 0| * (2 / ω) + (2 / ω) *
        ((p 1 - P 0) + (q 1 - Q 0)) := by
      have hs := mul_le_mul_of_nonneg_left hsin (abs_nonneg (f 0))
      have hpq := add_le_add hcumP hcumQ
      nlinarith
    _ ≤ |f 0| * (2 / ω) + (2 / ω) * variationOnFromTo f s 0 1 := by
      have hfactor : 0 ≤ (2 : ℝ) / ω := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hpartsLe hfactor]
    _ = (2 * |f 0| + 2 * variationOnFromTo f s 0 1) / ω := by ring

/-- 無限和の係数下界とBV係数上界は両立しないため、無限和は有界変動でない。 -/
theorem not_boundedVariation_infiniteSum :
    ¬ BoundedVariationOn infiniteSum (Set.Icc (0 : ℝ) 1) := by
  intro hBV
  let V := variationOnFromTo infiniteSum (Set.Icc (0 : ℝ) 1) 0 1
  let C := 2 * |infiniteSum 0| + 2 * V
  have hCnonneg : 0 ≤ C := by
    have hV : 0 ≤ variationOnFromTo infiniteSum (Set.Icc (0 : ℝ) 1) 0 1 :=
      variationOnFromTo.nonneg_of_le _ _ (by norm_num)
    dsimp [C, V]
    positivity
  obtain ⟨n, hnPow⟩ := pow_unbounded_of_one_lt (64 + 8 * C)
    (by norm_num : (1 : ℝ) < 2)
  have hn : 6 ≤ n := by
    by_contra hn'
    have hnle : n ≤ 5 := by omega
    have hnupper : (2 : ℝ) ^ n ≤ 32 := by
      calc
        (2 : ℝ) ^ n ≤ (2 : ℝ) ^ 5 := pow_le_pow_right₀ (by norm_num) hnle
        _ = 32 := by norm_num
    nlinarith
  have h4pow : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    calc
      (4 : ℝ) ^ n = (2 * 2 : ℝ) ^ n := by norm_num
      _ = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by rw [mul_pow]
      _ = ((2 : ℝ) ^ n) ^ 2 := by ring
  have hcoeffLower := infiniteSum_sine_coefficient_lower n hn
  have hcoeffUpper := bv_sine_coefficient_bound infiniteSum continuous_infiniteSum hBV
    ((4 : ℝ) ^ n) (by positivity)
  have hstrict : C / (4 : ℝ) ^ n < (1 / 2 : ℝ) ^ n / 8 := by
    rw [h4pow]
    have hpositive : 0 < (2 : ℝ) ^ n := by positivity
    have hbig : 8 * C < (2 : ℝ) ^ n := by linarith
    have hxy : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    field_simp
    nlinarith [hxy]
  have hupper :
      |∫ t in (0 : ℝ)..1, infiniteSum t * Real.sin ((4 : ℝ) ^ n * t)| ≤
        C / (4 : ℝ) ^ n := by
    dsimp [C, V] at hcoeffUpper ⊢
    exact hcoeffUpper
  have hpositiveCoeff : 0 < ∫ t in (0 : ℝ)..1,
      infiniteSum t * Real.sin ((4 : ℝ) ^ n * t) := by
    have hpos : 0 < (1 / 2 : ℝ) ^ n / 8 := by positivity
    linarith
  have habsLower :
      (1 / 2 : ℝ) ^ n / 8 ≤
        |∫ t in (0 : ℝ)..1, infiniteSum t * Real.sin ((4 : ℝ) ^ n * t)| := by
    rw [abs_of_pos hpositiveCoeff]
    exact hcoeffLower
  linarith

/-- 無限和は絶対連続ではない。高周波係数の下界が、絶対連続関数に許される
`1/ω` 型の部分積分上界より遅く減衰するためである。 -/
theorem not_absolutelyContinuous_infiniteSum :
    ¬ AbsolutelyContinuousOnInterval infiniteSum 0 1 := by
  intro hac
  let C : ℝ := |infiniteSum 0| + |infiniteSum 1| +
    ∫ t in (0 : ℝ)..1, |deriv infiniteSum t|
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    refine add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
    exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)
  obtain ⟨n, hnPow⟩ := pow_unbounded_of_one_lt (64 + 8 * C)
    (by norm_num : (1 : ℝ) < 2)
  have hn : 6 ≤ n := by
    by_contra hn'
    have hnle : n ≤ 5 := by omega
    have hnupper : (2 : ℝ) ^ n ≤ 32 := by
      calc
        (2 : ℝ) ^ n ≤ (2 : ℝ) ^ 5 := by
          exact pow_le_pow_right₀ (by norm_num) hnle
        _ = 32 := by norm_num
    have hlarge := hnPow
    dsimp [C] at hlarge
    nlinarith
  have h4pow : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    calc
      (4 : ℝ) ^ n = (2 * 2 : ℝ) ^ n := by norm_num
      _ = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by rw [mul_pow]
      _ = ((2 : ℝ) ^ n) ^ 2 := by ring
  have hcoeffLower := infiniteSum_sine_coefficient_lower n hn
  have hcoeffUpper := ac_sine_coefficient_bound infiniteSum hac
    ((4 : ℝ) ^ n) (by positivity)
  have hstrict : C / (4 : ℝ) ^ n < (1 / 2 : ℝ) ^ n / 8 := by
    rw [h4pow]
    have hpositive : 0 < (2 : ℝ) ^ n := by positivity
    have hbig : 8 * C < (2 : ℝ) ^ n := by linarith
    have hmul : C * 8 < (2 : ℝ) ^ n := by nlinarith
    have hxy : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    field_simp
    nlinarith [hxy]
  have hupper :
      |∫ t in (0 : ℝ)..1, infiniteSum t * Real.sin ((4 : ℝ) ^ n * t)| ≤
        C / (4 : ℝ) ^ n := by
    dsimp [C] at hcoeffUpper ⊢
    exact hcoeffUpper
  have hpositiveCoeff : 0 < ∫ t in (0 : ℝ)..1,
      infiniteSum t * Real.sin ((4 : ℝ) ^ n * t) := by
    have hpos : 0 < (1 / 2 : ℝ) ^ n / 8 := by positivity
    linarith
  have habsLower :
      (1 / 2 : ℝ) ^ n / 8 ≤
        |∫ t in (0 : ℝ)..1, infiniteSum t * Real.sin ((4 : ℝ) ^ n * t)| := by
    rw [abs_of_pos hpositiveCoeff]
    exact hcoeffLower
  linarith

theorem l1_lower (N : ℕ) : 2 ^ N / 4 ≤ ∫ t in (0 : ℝ)..1, |h N t| := by
  have hM : (0 : ℝ) < 4 ^ N := by positivity
  have hcos := integral_cos_sq_lower (4 ^ N) hM
  have hmono : ∫ t in (0 : ℝ)..1, (2 : ℝ) ^ N * Real.cos (4 ^ N * t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, |h N t| := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
    · exact (by fun_prop : Continuous fun t : ℝ => (2 : ℝ) ^ N * Real.cos (4 ^ N * t) ^ 2).intervalIntegrable _ _
    · exact (by unfold h; fun_prop : Continuous fun t : ℝ => |h N t|).intervalIntegrable _ _
    · intro t _
      unfold h
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ N)]
      have := Real.abs_cos_le_one (4 ^ N * t)
      have h2 : Real.cos (4 ^ N * t) ^ 2 ≤ |Real.cos (4 ^ N * t)| := by
        rw [← sq_abs]; nlinarith [abs_nonneg (Real.cos (4 ^ N * t))]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hlow : (2 : ℝ) ^ N * (1 / 2 - 1 / (4 * 4 ^ N)) ≤ ∫ t in (0 : ℝ)..1, (2 : ℝ) ^ N * Real.cos (4 ^ N * t) ^ 2 := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hcos (by positivity)
  have h4 : (2 : ℝ) ^ N / 4 ≤ (2 : ℝ) ^ N * (1 / 2 - 1 / (4 * 4 ^ N)) := by
    have h1 : (1 : ℝ) ≤ 4 ^ N := one_le_pow₀ (by norm_num)
    have h2 : 1 / (4 * (4 : ℝ) ^ N) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hp : (0 : ℝ) < 2 ^ N := by positivity
    nlinarith
  linarith

/-- A6′(ii) の破れ: 有限部分和の族は `L¹[0,1]` で一様可積分でない（`L¹` 有界性が崩れる）。 -/
theorem not_uniformIntegrable :
    ¬ UniformIntegrable finiteRate 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rintro ⟨_, C, hC⟩
  -- 単独層 s={N}: ‖h_N‖_{L¹} ≤ C
  have hbound : ∀ N : ℕ, 2 ^ N / 4 ≤ (C : ℝ) := by
    intro N
    have h1 := hC {N}
    have hcont : Continuous fun t : ℝ => finiteRate {N} t := by
      unfold finiteRate h; simp; fun_prop
    rw [eLpNorm_one_eq_lintegral_enorm hcont.aestronglyMeasurable] at h1
    have hint : Integrable (fun t => finiteRate {N} t) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      hcont.integrableOn_Icc
    have h2 := ofReal_integral_norm_eq_lintegral_enorm hint
    have h3 : ENNReal.ofReal (∫ t, ‖finiteRate {N} t‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) ≤ C := by
      rw [h2]; exact h1
    have h4 : (∫ t, ‖finiteRate {N} t‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) ≤ C := by
      have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).1 h3
      simpa using this
    have h5 : (∫ t in (0 : ℝ)..1, |h N t|) = ∫ t, ‖finiteRate {N} t‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
      simp [finiteRate, Real.norm_eq_abs]
    linarith [l1_lower N, h5]
  -- N → ∞ で 2^N/4 は非有界
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((C : ℝ) * 4 + 1) (by norm_num : (1 : ℝ) < 2)
  have := hbound N
  linarith

/-! ## Pythonの1始まり級数との接続 -/

/-- Pythonで使う `k=1` 始まりの無限級数。数値部分和の丸め誤差は対象外。 -/
noncomputable def pythonInfiniteSum (t : ℝ) : ℝ := ∑' k : ℕ, H (k + 1) t

/-- 0始まりの級数との差は、滑らかな有限項 `H 0 = 1 + sin` だけである。 -/
theorem infiniteSum_eq_pythonInfiniteSum_add (t : ℝ) :
    infiniteSum t = pythonInfiniteSum t + H 0 t := by
  have h := (H_summable t).sum_add_tsum_nat_add 1
  simpa [infiniteSum, pythonInfiniteSum, add_comm] using h.symm

/-- 除く最初の項は滑らかなので絶対連続であり、有界変動でもある。 -/
theorem H_zero_absolutelyContinuous : AbsolutelyContinuousOnInterval (H 0) 0 1 := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  unfold H
  fun_prop

/-- 1始まりの級数も非BVである。BVに滑らかな有限項を足してもBVなので、
もし1始まりの級数がBVなら既証明の0始まりの非BVと矛盾する。 -/
theorem not_boundedVariation_pythonInfiniteSum :
    ¬ BoundedVariationOn pythonInfiniteSum (Set.Icc (0 : ℝ) 1) := by
  intro h
  have hzero : BoundedVariationOn (H 0) (Set.Icc (0 : ℝ) 1) := by
    simpa using H_zero_absolutelyContinuous.boundedVariationOn
  apply not_boundedVariation_infiniteSum
  have heq : infiniteSum = pythonInfiniteSum + H 0 := by
    funext t
    exact infiniteSum_eq_pythonInfiniteSum_add t
  rw [heq]
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨h, hzero⟩)
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    ∑ i ∈ Finset.range n, edist ((pythonInfiniteSum + H 0) (u (i + 1)))
        ((pythonInfiniteSum + H 0) (u i)) ≤
        ∑ i ∈ Finset.range n, (edist (pythonInfiniteSum (u (i + 1)))
          (pythonInfiniteSum (u i)) + edist (H 0 (u (i + 1))) (H 0 (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (pythonInfiniteSum (u (i + 1)))
        (pythonInfiniteSum (u i))) +
        ∑ i ∈ Finset.range n, edist (H 0 (u (i + 1))) (H 0 (u i)) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- Pythonと同じ1始まりの級数の非絶対連続性。数値出力や至る所微分不能は主張しない。 -/
theorem not_absolutelyContinuous_pythonInfiniteSum :
    ¬ AbsolutelyContinuousOnInterval pythonInfiniteSum 0 1 := by
  intro h
  apply not_boundedVariation_pythonInfiniteSum
  simpa using h.boundedVariationOn

end Tomabechi.Examples.Theorem15A6
