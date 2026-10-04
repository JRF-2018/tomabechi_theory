import Theorem24_26
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# 定理24の Python 例 (`examples/theorem24_all_is_suffering.py`) の Lean 根拠（条件24-Aの検証）

追従問題: `x∈ℝ`、速度制限 `|ẋ|≤1`（許容方策＝初期値 `π T=x` をもつ1-リプシッツ軌道）、基準
`d(t)=A sin(ωt)`（`ω=2π/6.4=5π/16`）、走行コスト `V(y,s)=[(|y-d(s)|-1/40)₊]²`（帯の中なら苦ゼロ）、
割引 `ρ=1`。

* A=3（追従不能）: `|d'|` の最大は `3ω≈2.95>1`。**条件24-A（空未満で `V=0` をほとんど至る所永久に
  保つ許容方策が存在しない）が全ての `(x,T)` で成り立つ**ことを証明する。さらに1-Lipschitz許容軌道の
  コンパクト性から最適軌道の存在を証明し、一般定理 `theorem24_positive_optimal_value_of_condition24A`
  に接続して最適値 `J*>0` を得る。
* A=1/2（追従可能）: `x=d(T)` から `π=d` が許容で `V=0` を永久に保つ（24-A は成立しない）。
  最適値は 0。

注意: 割引費用の可積分性と最適方策の存在はこのモデルで証明する（Python の動的計画法の
数値 `J*` は証明しない）。許容方策クラスは1-リプシッツ軌道の開ループ方策に限定している。
-/

namespace Tomabechi.Examples.Theorem24

open Tomabechi.Theorem24_26 MeasureTheory Asymptotics

/-- `ω=2π/6.4=5π/16`。 -/
noncomputable def ω : ℝ := 5 * Real.pi / 16

/-- 基準 `d(s)=A sin(ωs)`。 -/
noncomputable def d (A s : ℝ) : ℝ := A * Real.sin (ω * s)

/-- 走行コスト `V=[(|y-d(s)|-1/40)₊]²`。 -/
noncomputable def Vtrack (A y s : ℝ) : ℝ := (max (|y - d A s| - 1 / 40) 0) ^ 2

/-- 許容方策: 1-リプシッツ軌道で `π T = x`。 -/
def admissible (π : ℝ → ℝ) (x T : ℝ) : Prop := LipschitzWith 1 π ∧ π T = x

/-- 軌道上の走行コスト（Python の `cost`）。 -/
noncomputable def running (A : ℝ) (π : ℝ → ℝ) (_x _T : ℝ) (s : ℝ) : ℝ := Vtrack A (π s) s

theorem Vtrack_nonneg (A y s : ℝ) : 0 ≤ Vtrack A y s := by unfold Vtrack; positivity

theorem Vtrack_eq_zero_iff (A y s : ℝ) : Vtrack A y s = 0 ↔ |y - d A s| ≤ 1 / 40 := by
  unfold Vtrack
  constructor
  · intro h
    have h1 : max (|y - d A s| - 1 / 40) 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h
    linarith [le_max_left (|y - d A s| - 1 / 40) 0]
  · intro h
    have : |y - d A s| - 1 / 40 ≤ 0 := by linarith
    rw [max_eq_right this]; norm_num

theorem continuous_d (A : ℝ) : Continuous (d A) := by unfold d ω; fun_prop

/-- 許容軌道は初期値からの距離で一様に抑えられる。これは後で割引費用を
多項式×指数関数で支配するときに使う、全ての方策に共通の評価である。 -/
theorem admissible_state_bound {π : ℝ → ℝ} {x T s : ℝ}
    (hπ : admissible π x T) : |π s| ≤ |x| + |s - T| := by
  rcases hπ with ⟨hlip, hinit⟩
  have hdist := hlip.dist_le_mul s T
  rw [Real.dist_eq, hinit, Real.dist_eq] at hdist
  norm_num at hdist
  calc |π s| = |(π s - x) + x| := by rw [sub_add_cancel]
    _ ≤ |π s - x| + |x| := abs_add_le _ _
    _ ≤ |s - T| + |x| := by nlinarith [hdist]
    _ = |x| + |s - T| := by ring

/-- 追従コストは軌道の線形成長から二次式で一様に抑えられる。
割引積分の可積分性と最小化列の有限費用性を示すための解析的な核。 -/
theorem Vtrack_growth_bound (A y s : ℝ) :
    Vtrack A y s ≤ (|y| + |A|) ^ 2 := by
  unfold Vtrack d
  have hs : |Real.sin (ω * s)| ≤ 1 := abs_le.mpr ⟨by linarith [Real.neg_one_le_sin (ω * s)], Real.sin_le_one _⟩
  have hdist : |y - A * Real.sin (ω * s)| ≤ |y| + |A| := by
    calc |y - A * Real.sin (ω * s)|
        ≤ |y| + |A * Real.sin (ω * s)| := abs_sub _ _
      _ = |y| + |A| * |Real.sin (ω * s)| := by rw [abs_mul]
      _ ≤ |y| + |A| := by nlinarith [abs_nonneg A]
  have hpos : 0 ≤ |y| + |A| := by positivity
  have hmax : max (|y - A * Real.sin (ω * s)| - 1 / 40) 0 ≤ |y| + |A| :=
    max_le (by linarith) hpos
  have hmnonneg : 0 ≤ max (|y - A * Real.sin (ω * s)| - 1 / 40) 0 := le_max_right _ _
  nlinarith [sq_nonneg (|y| + |A| - max (|y - A * Real.sin (ω * s)| - 1 / 40) 0)]

/-- 許容方策での被積分費用は、初期値・経過時間だけの二次式で抑えられる。 -/
theorem running_growth_bound {π : ℝ → ℝ} {x T s : ℝ} (A : ℝ)
    (hπ : admissible π x T) :
    running A π x T s ≤ (|x| + |s - T| + |A|) ^ 2 := by
  unfold running
  calc Vtrack A (π s) s ≤ (|π s| + |A|) ^ 2 := Vtrack_growth_bound A (π s) s
    _ ≤ (|x| + |s - T| + |A|) ^ 2 := by
      gcongr
      exact admissible_state_bound hπ

/-- 初期値と割引開始時刻を固定すると、軌道の二次成長包絡は任意の正の
指数成長より遅い。この漸近評価が指数割引積分の有限性を与える。 -/
theorem running_envelope_isBigO_exp (A x T : ℝ) :
    (fun s : ℝ => (|x| + |s - T| + |A|) ^ 2) =O[Filter.atTop]
      (fun s => Real.exp ((1 / 2 : ℝ) * s)) := by
  let C : ℝ := |x| + |T| + |A|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq : (fun s : ℝ => (|x| + |s - T| + |A|) ^ 2) =O[Filter.atTop]
      (fun s => s ^ 2) := by
    rw [isBigO_iff]
    refine ⟨(C + 1) ^ 2, ?_⟩
    filter_upwards [show ∀ᶠ s : ℝ in Filter.atTop, max T 1 ≤ s from
      Filter.eventually_atTop.2 ⟨max T 1, fun s hs => hs⟩] with s hs
    have hsT : T ≤ s := le_trans (le_max_left _ _) hs
    have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
    have hst : 0 ≤ s - T := sub_nonneg.mpr hsT
    have habs : |s - T| = s - T := abs_of_nonneg hst
    have hlinear : |x| + |s - T| + |A| ≤ C + s := by
      dsimp [C]
      rw [habs]
      nlinarith [neg_le_abs T]
    have hmul : C + s ≤ (C + 1) * s := by
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hs1)]
    have hnonneg : 0 ≤ |x| + |s - T| + |A| := by positivity
    have hsnonneg : 0 ≤ s := by linarith
    have hqnonneg : 0 ≤ (|x| + |s - T| + |A|) ^ 2 := sq_nonneg _
    have hmulnonneg : 0 ≤ (C + 1) * s := mul_nonneg (by linarith) hsnonneg
    calc ‖(|x| + |s - T| + |A|) ^ 2‖
        = (|x| + |s - T| + |A|) ^ 2 := abs_of_nonneg hqnonneg
      _ ≤ ((C + 1) * s) ^ 2 := by nlinarith [hlinear.trans hmul]
      _ = (C + 1) ^ 2 * ‖s ^ 2‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]; ring
  have hpoly : (fun s : ℝ => s ^ 2) =o[Filter.atTop]
      (fun s => Real.exp ((1 / 2 : ℝ) * s)) :=
    by
      convert isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2) using 1
  exact hq.trans_isLittleO hpoly |>.isBigO

/-- 指数割引は許容軌道の二次成長を上回るので、全ての許容方策の追従費用は
未来半直線上で可積分となる。これにより最適化問題の有限費用性を仮定せずに済む。 -/
theorem discounted_running_integrable (A x T : ℝ) {π : ℝ → ℝ}
    (hπ : admissible π x T) :
    Integrable (fun s => theorem26DiscountWeight 1 T s * running A π x T s)
      (futureLebesgueMeasure T) := by
  let q : ℝ → ℝ := fun s => (|x| + |s - T| + |A|) ^ 2
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hloc : LocallyIntegrableOn q (Set.Ici T) :=
    hqcont.continuousOn.locallyIntegrableOn measurableSet_Ici
  have hbig : q =O[Filter.atTop] (fun s : ℝ => Real.exp ((1 / 2 : ℝ) * s)) := by
    simpa only [q] using running_envelope_isBigO_exp A x T
  have hdec : IntegrableOn (fun s : ℝ => Real.exp (-s) * q s) (Set.Ici T) :=
    by
      simpa [neg_one_mul] using
        (integrableOn_exp_neg_mul_of_isBigO_exp hloc hbig (by norm_num : (1 / 2 : ℝ) < 1))
  have hbase : Integrable (fun s : ℝ => Real.exp T * (Real.exp (-s) * q s))
      (volume.restrict (Set.Ici T)) := by
    change IntegrableOn (fun s : ℝ => Real.exp T * (Real.exp (-s) * q s)) (Set.Ici T)
    exact hdec.const_mul (Real.exp T)
  have htarget : AEStronglyMeasurable
      (fun s : ℝ => theorem26DiscountWeight 1 T s * running A π x T s)
      (volume.restrict (Set.Ici T)) := by
    have hc : Continuous (fun s : ℝ =>
        theorem26DiscountWeight 1 T s * running A π x T s) := by
      have hrun : Continuous (running A π x T) := by
        unfold running Vtrack d
        have hπc : Continuous π := hπ.1.continuous
        fun_prop
      unfold theorem26DiscountWeight
      fun_prop
    exact hc.aestronglyMeasurable
  apply hbase.mono' htarget
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  have hrun : 0 ≤ running A π x T s := Vtrack_nonneg A (π s) s
  have hq : 0 ≤ q s := by dsimp [q]; positivity
  have hbound : running A π x T s ≤ q s := by
    simpa [q] using running_growth_bound A hπ
  have hexp : theorem26DiscountWeight 1 T s = Real.exp T * Real.exp (-s) := by
    rw [theorem26DiscountWeight, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hleft : 0 ≤ Real.exp T * Real.exp (-s) * running A π x T s := by positivity
  have hright : 0 ≤ Real.exp T * (Real.exp (-s) * q s) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleft]
  calc Real.exp T * Real.exp (-s) * running A π x T s
      = Real.exp T * (Real.exp (-s) * running A π x T s) := by ring
    _ ≤ Real.exp T * (Real.exp (-s) * q s) := by gcongr

/-- 全ての許容方策に共通する割引済み二次包絡の可積分性。 -/
theorem discounted_tracking_envelope_integrable (A x T : ℝ) :
    Integrable (fun s => theorem26DiscountWeight 1 T s *
      (|x| + |s - T| + |A|) ^ 2) (futureLebesgueMeasure T) := by
  let q : ℝ → ℝ := fun s => (|x| + |s - T| + |A|) ^ 2
  have hqcont : Continuous q := by dsimp [q]; fun_prop
  have hloc : LocallyIntegrableOn q (Set.Ici T) :=
    hqcont.continuousOn.locallyIntegrableOn measurableSet_Ici
  have hbig : q =O[Filter.atTop] (fun s : ℝ => Real.exp ((1 / 2 : ℝ) * s)) := by
    simpa only [q] using running_envelope_isBigO_exp A x T
  have hdec : IntegrableOn (fun s : ℝ => Real.exp (-s) * q s) (Set.Ici T) := by
    simpa [neg_one_mul] using
      (integrableOn_exp_neg_mul_of_isBigO_exp hloc hbig (by norm_num : (1 / 2 : ℝ) < 1))
  have hbase : Integrable (fun s : ℝ => Real.exp T * (Real.exp (-s) * q s))
      (volume.restrict (Set.Ici T)) := by
    change IntegrableOn (fun s : ℝ => Real.exp T * (Real.exp (-s) * q s)) (Set.Ici T)
    exact hdec.const_mul (Real.exp T)
  have heq : (fun s : ℝ => theorem26DiscountWeight 1 T s * q s) =
      (fun s => Real.exp T * (Real.exp (-s) * q s)) := by
    funext s
    rw [show theorem26DiscountWeight 1 T s = Real.exp T * Real.exp (-s) by
      rw [theorem26DiscountWeight, ← Real.exp_add]
      congr 1
      ring]
    ring
  rw [futureLebesgueMeasure]
  change Integrable (fun s : ℝ => theorem26DiscountWeight 1 T s * q s)
    (volume.restrict (Set.Ici T))
  rw [heq]
  exact hbase

/-- Lipschitz許容方策の費用関数は連続である。有限区間上の一様収束から
極限費用の下半連続性を得る際に使う。 -/
theorem continuous_running (A x T : ℝ) {π : ℝ → ℝ} (hπ : admissible π x T) :
    Continuous (running A π x T) := by
  unfold running Vtrack d
  have hπc : Continuous π := hπ.1.continuous
  have hsin : Continuous (fun s : ℝ => Real.sin (ω * s)) := by fun_prop
  fun_prop

/-- 指数割引を掛けた被積分関数も連続であり、特に任意の有限区間で可積分である。
無限区間での可積分性は、この局所結果に指数減衰評価を加えて示す。 -/
theorem continuous_discounted_running (A x T : ℝ) {π : ℝ → ℝ}
    (hπ : admissible π x T) :
    Continuous (fun s => theorem26DiscountWeight 1 T s * running A π x T s) := by
  have hc := continuous_running A x T hπ
  unfold theorem26DiscountWeight
  fun_prop

/-- 連続な割引費用は有限区間上で可積分である。無限半直線上の可積分性では、
この局所可積分性に加えて割引が軌道の二次成長を支配することを示す必要がある。 -/
theorem discounted_running_integrableOn_Icc (A x T a b : ℝ) {π : ℝ → ℝ}
    (hπ : admissible π x T) :
    IntegrableOn (fun s => theorem26DiscountWeight 1 T s * running A π x T s)
      (Set.Icc a b) := by
  exact (continuous_discounted_running A x T hπ).continuousOn.integrableOn_compact
    isCompact_Icc

/-- 任意の初期対に対し、定数軌道が許容方策を与える。最小化列の集合が空でない
ことを示すときの基準方策である。 -/
theorem constant_admissible (x T : ℝ) : admissible (fun _ : ℝ => x) x T := by
  constructor
  · exact (LipschitzWith.const x).weaken (by norm_num)
  · rfl

/-- 固定した初期対に対する割引総費用。全ての許容方策で実数値の有限積分となる。 -/
noncomputable def trackingCost (A x T : ℝ) (π : ℝ → ℝ) : ℝ :=
  discountedFeedbackValue (fun t => futureLebesgueMeasure t) (theorem26DiscountWeight 1)
    (fun (π : ℝ → ℝ) (x : ℝ) (T s : ℝ) => running A π x T s) π x T

/-- 許容方策列が各時刻で収束すれば、優収束定理により総費用も収束する。 -/
theorem trackingCost_tendsto_of_pointwise {ps : ℕ → ℝ → ℝ} {π : ℝ → ℝ}
    (A x T : ℝ) (hps : ∀ n, admissible (ps n) x T)
    (hlim : ∀ s, Filter.Tendsto (fun n => ps n s) Filter.atTop (nhds (π s))) :
    Filter.Tendsto (fun n => trackingCost A x T (ps n)) Filter.atTop
      (nhds (trackingCost A x T π)) := by
  let μ := futureLebesgueMeasure T
  let F : ℕ → ℝ → ℝ := fun n s =>
    theorem26DiscountWeight 1 T s * running A (ps n) x T s
  let f : ℝ → ℝ := fun s => theorem26DiscountWeight 1 T s * running A π x T s
  let bound : ℝ → ℝ := fun s => theorem26DiscountWeight 1 T s *
    (|x| + |s - T| + |A|) ^ 2
  have hmeas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    dsimp [F, μ]
    exact (continuous_discounted_running A x T (hps n)).aestronglyMeasurable
  have hboundInt : Integrable bound μ := by
    dsimp [bound, μ]
    exact discounted_tracking_envelope_integrable A x T
  have hdom : ∀ n, ∀ᵐ s ∂μ, ‖F n s‖ ≤ bound s := by
    intro n
    filter_upwards with s
    have hrun : 0 ≤ running A (ps n) x T s := Vtrack_nonneg A (ps n s) s
    have hrunBound := running_growth_bound (s := s) A (hps n)
    have hexp : 0 < theorem26DiscountWeight 1 T s := Real.exp_pos _
    dsimp [F, bound]
    rw [abs_of_nonneg (mul_nonneg hexp.le hrun)]
    exact mul_le_mul_of_nonneg_left hrunBound hexp.le
  have hpoint : ∀ᵐ s ∂μ, Filter.Tendsto (fun n => F n s) Filter.atTop (nhds (f s)) := by
    filter_upwards with s
    have hc : Continuous (fun y : ℝ =>
        theorem26DiscountWeight 1 T s * Vtrack A y s) := by
      unfold Vtrack d
      fun_prop
    have ht := hc.continuousAt.tendsto.comp (hlim s)
    change Filter.Tendsto
      (fun n => theorem26DiscountWeight 1 T s * Vtrack A (ps n s) s)
      Filter.atTop (nhds (theorem26DiscountWeight 1 T s * Vtrack A (π s) s)) at ht
    simpa [F, f, running] using ht
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
    bound hmeas hboundInt hdom hpoint
  simpa [trackingCost, discountedFeedbackValue, F, f, μ] using hconv

/-- 許容方策が与える全ての費用の集合。 -/
def trackingCosts (A x T : ℝ) : Set ℝ :=
  {j | ∃ π, admissible π x T ∧ trackingCost A x T π = j}

/-- 非負走行費用から、全ての許容方策の割引総費用は非負。 -/
theorem trackingCost_nonneg (A x T : ℝ) {π : ℝ → ℝ}
    (hπ : admissible π x T) : 0 ≤ trackingCost A x T π := by
  have _hfinite := discounted_running_integrable A x T hπ
  unfold trackingCost discountedFeedbackValue
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards with s
  exact mul_nonneg (Real.exp_pos _).le (Vtrack_nonneg A (π s) s)

/-- 定数方策により許容費用集合は空でない。 -/
theorem trackingCosts_nonempty (A x T : ℝ) : (trackingCosts A x T).Nonempty := by
  refine ⟨trackingCost A x T (fun _ => x), ?_⟩
  exact ⟨fun _ => x, constant_admissible x T, rfl⟩

/-- 費用集合は0で下に有界。 -/
theorem trackingCosts_bddBelow (A x T : ℝ) : BddBelow (trackingCosts A x T) := by
  refine ⟨0, ?_⟩
  rintro j ⟨π, hπ, rfl⟩
  exact trackingCost_nonneg A x T hπ

/-- 追従問題の最適値候補を許容費用の下限として定義する。 -/
noncomputable def trackingValue (A x T : ℝ) : ℝ := sInf (trackingCosts A x T)

/-- 下限は0以上であり、どの許容方策の費用以下でもある。従って実数値の
最適値候補が上下から有限に定まる。 -/
theorem trackingValue_bounds (A x T : ℝ) :
    0 ≤ trackingValue A x T ∧
      ∀ π, admissible π x T → trackingValue A x T ≤ trackingCost A x T π := by
  have hglb : IsGLB (trackingCosts A x T) (trackingValue A x T) :=
    isGLB_csInf (trackingCosts_nonempty A x T) (trackingCosts_bddBelow A x T)
  constructor
  · apply hglb.2
    intro j hj
    rcases hj with ⟨π, hπ, rfl⟩
    exact trackingCost_nonneg A x T hπ
  · intro π hπ
    exact hglb.1 ⟨π, hπ, rfl⟩

/-- 任意の精度で下限に近い許容方策を選ぶ最小化列が存在する。
ここではまだ極限方策や下限の達成は主張しない。 -/
theorem exists_tracking_minimizing_sequence (A x T : ℝ) :
    ∃ ps : ℕ → ℝ → ℝ,
      (∀ n, admissible (ps n) x T) ∧
      (∀ n, trackingCost A x T (ps n) < trackingValue A x T + 1 / (n + 1)) := by
  have hnonempty := trackingCosts_nonempty A x T
  have hbounded := trackingCosts_bddBelow A x T
  have hexists : ∀ n : ℕ, ∃ π : ℝ → ℝ,
      admissible π x T ∧
        trackingCost A x T π < trackingValue A x T + 1 / (n + 1) := by
    intro n
    have hε : 0 < (1 : ℝ) / (n + 1) := by positivity
    obtain ⟨j, hj, hjlt⟩ := exists_lt_of_csInf_lt hnonempty
      (show trackingValue A x T < trackingValue A x T + 1 / (n + 1) by linarith)
    rcases hj with ⟨π, hπ, rfl⟩
    exact ⟨π, hπ, by simpa [trackingValue] using hjlt⟩
  let ps : ℕ → ℝ → ℝ := fun n => Classical.choose (hexists n)
  refine ⟨ps, ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (hexists n)).1
  · intro n
    exact (Classical.choose_spec (hexists n)).2

/-- 構成した最小化列の費用は下限へ収束する。 -/
theorem tracking_minimizing_sequence_cost_tendsto {ps : ℕ → ℝ → ℝ}
    (A x T : ℝ) (hps : ∀ n, admissible (ps n) x T)
    (hnear : ∀ n, trackingCost A x T (ps n) < trackingValue A x T + 1 / (n + 1)) :
    Filter.Tendsto (fun n => trackingCost A x T (ps n)) Filter.atTop
      (nhds (trackingValue A x T)) := by
  have hrecip : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hup : Filter.Tendsto (fun n : ℕ => trackingValue A x T + 1 / (n + 1))
      Filter.atTop (nhds (trackingValue A x T)) := by
    simpa using (tendsto_const_nhds.add hrecip)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hup (fun n => ?_) (fun n => ?_)
  · exact (trackingValue_bounds A x T).2 (ps n) (hps n)
  · exact le_of_lt (hnear n)

/-- 最小化列から各時刻収束する部分列が得られれば、その極限方策が下限を
実際に達成する。収束部分列の構成は `exists_admissible_pointwise_convergent_subsequence`
（Arzelà–Ascoli）が与える。 -/
theorem pointwise_limit_attains_trackingValue {ps : ℕ → ℝ → ℝ} {π : ℝ → ℝ}
    {φ : ℕ → ℕ} (A x T : ℝ)
    (hps : ∀ n, admissible (ps n) x T)
    (hnear : ∀ n, trackingCost A x T (ps n) < trackingValue A x T + 1 / (n + 1))
    (hφ : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (hlim : ∀ s, Filter.Tendsto (fun n => ps (φ n) s) Filter.atTop (nhds (π s))) :
    trackingCost A x T π = trackingValue A x T := by
  have hsub : ∀ n, admissible (ps (φ n)) x T := fun n => hps (φ n)
  have hcostLimit := trackingCost_tendsto_of_pointwise A x T hsub hlim
  have hminLimit := (tracking_minimizing_sequence_cost_tendsto A x T hps hnear).comp hφ
  exact tendsto_nhds_unique hcostLimit hminLimit

/-- 許容方策列の各時刻での極限も1-Lipschitz制約と初期条件を保つ。
コンパクト性から抽出する極限曲線が実際に許容方策であることを保証する。 -/
theorem admissible_of_pointwise_limit {ps : ℕ → ℝ → ℝ} {x T : ℝ}
    (hps : ∀ n, admissible (ps n) x T) (π : ℝ → ℝ)
    (hlim : ∀ s, Filter.Tendsto (fun n => ps n s) Filter.atTop (nhds (π s))) :
    admissible π x T := by
  constructor
  · refine LipschitzWith.of_dist_le_mul fun s t => ?_
    have hdist : Filter.Tendsto (fun n => dist (ps n s) (ps n t)) Filter.atTop
        (nhds (dist (π s) (π t))) := (hlim s).dist (hlim t)
    apply le_of_tendsto hdist
    filter_upwards with n
    exact (hps n).1.dist_le_mul s t
  · have hfun : (fun n : ℕ => ps n T) = fun _ => x := funext fun n => (hps n).2
    have hseq : Filter.Tendsto (fun n : ℕ => ps n T) Filter.atTop (nhds x) := by
      rw [hfun]
      exact tendsto_const_nhds
    exact (tendsto_nhds_unique hseq (hlim T)).symm

/-- 固定した初期値を通る1-Lipschitz軌道全体は、局所一様収束の位相でコンパクト。
各時刻での値は初期値からの距離で有界で、共通Lipschitz定数が等連続性を与える。 -/
theorem admissible_maps_compact (x T : ℝ) :
    IsCompact {f : C(ℝ, ℝ) | LipschitzWith 1 f ∧ f T = x} := by
  let S : Set C(ℝ, ℝ) := {f | LipschitzWith 1 f ∧ f T = x}
  let R : ℝ → ℝ := fun s => |x| + |s - T|
  have himage : ContinuousMap.toFun '' S =
      {f : ℝ → ℝ | LipschitzWith (1 : NNReal) f ∧ f T = x} := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · rintro ⟨hLip, hT⟩
      exact ⟨⟨f, hLip.continuous⟩, ⟨hLip, hT⟩, rfl⟩
  have hLipClosed : IsClosed {f : ℝ → ℝ | LipschitzWith (1 : NNReal) f} :=
    isClosed_setOfPred_lipschitzWith (1 : NNReal)
  have hAnchorClosed : IsClosed {f : ℝ → ℝ | f T = x} :=
    isClosed_eq (continuous_apply T) continuous_const
  have hclosed : IsClosed (ContinuousMap.toFun '' S) := by
    rw [himage]
    exact hLipClosed.inter hAnchorClosed
  have hprod : IsCompact (Set.pi Set.univ (fun s : ℝ => Set.Icc (-R s) (R s))) :=
    isCompact_univ_pi fun s => isCompact_Icc
  have hsubset : ContinuousMap.toFun '' S ⊆
      Set.pi Set.univ (fun s : ℝ => Set.Icc (-R s) (R s)) := by
    rintro f ⟨g, hg, rfl⟩
    intro s _
    have hstate : |g s| ≤ R s := by
      simpa [R] using admissible_state_bound ⟨hg.1, hg.2⟩
    exact abs_le.mp hstate
  have himageCompact : IsCompact (ContinuousMap.toFun '' S) :=
    hprod.of_isClosed_subset hclosed hsubset
  have hEqui : Equicontinuous ((↑) : S → ℝ → ℝ) := by
    exact (LipschitzWith.uniformEquicontinuous
      (fun f : S => (f : C(ℝ, ℝ))) (1 : NNReal) (fun f => f.2.1)).equicontinuous
  exact ArzelaAscoli.isCompact_of_equicontinuous S himageCompact hEqui

/-- 任意の許容方策列には各時刻で収束する部分列があり、その極限も許容方策である。 -/
theorem exists_admissible_pointwise_convergent_subsequence {ps : ℕ → ℝ → ℝ} {x T : ℝ}
    (hps : ∀ n, admissible (ps n) x T) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ π : ℝ → ℝ,
      admissible π x T ∧
      ∀ s, Filter.Tendsto (fun n => ps (φ n) s) Filter.atTop (nhds (π s)) := by
  let S : Set C(ℝ, ℝ) := {f | LipschitzWith 1 f ∧ f T = x}
  let q : ℕ → C(ℝ, ℝ) := fun n => ⟨ps n, (hps n).1.continuous⟩
  have hq : ∀ n, q n ∈ S := fun n => hps n
  obtain ⟨g, hgS, φ, hφ, hconv⟩ :=
    (admissible_maps_compact x T).tendsto_subseq (x := q) hq
  refine ⟨φ, hφ, g, hgS, ?_⟩
  intro s
  have heval : Continuous (fun f : C(ℝ, ℝ) => f s) := by fun_prop
  have h := heval.continuousAt.tendsto.comp hconv
  change Filter.Tendsto (fun n => ps (φ n) s) Filter.atTop (nhds (g s)) at h
  exact h

/-- この追従問題は任意の初期値・開始時刻・振幅について最適許容軌道を持つ。
最小化列の局所一様収束部分列と優収束による費用収束を組み合わせる。 -/
theorem exists_tracking_optimal_policy (A x T : ℝ) :
    ∃ π : ℝ → ℝ, admissible π x T ∧
      trackingCost A x T π = trackingValue A x T ∧
      ∀ π', admissible π' x T → trackingCost A x T π ≤ trackingCost A x T π' := by
  obtain ⟨ps, hps, hnear⟩ := exists_tracking_minimizing_sequence A x T
  obtain ⟨φ, hφ, π, hπ, hlim⟩ := exists_admissible_pointwise_convergent_subsequence hps
  have hvalue : trackingCost A x T π = trackingValue A x T :=
    pointwise_limit_attains_trackingValue A x T hps hnear hφ.tendsto_atTop hlim
  refine ⟨π, hπ, hvalue, ?_⟩
  intro π' hπ'
  rw [hvalue]
  exact (trackingValue_bounds A x T).2 π' hπ'

/-- A=3: 追従不能。条件24-A が全ての `(x,T)` で成り立つ。 -/
theorem condition24A_hard (x T : ℝ) :
    ∀ π, admissible π x T → ¬ (fun s => running 3 π x T s) =ᵐ[futureLebesgueMeasure T] 0 := by
  rintro π ⟨hπ, _⟩ hae
  -- 連続性と a.e. 零から Ioi T 上で恒等的に零
  have hcont : Continuous (fun s => running 3 π x T s) := by
    unfold running Vtrack
    have := hπ.continuous
    have := continuous_d 3
    fun_prop
  have hae' : (fun s => running 3 π x T s) =ᵐ[volume.restrict (Set.Ioi T)] 0 :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioi_subset_Ici_self hae
  have hzero := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioi hcont.continuousOn
    continuousOn_const (g := fun _ => (0 : ℝ))
  have hband : ∀ s, T < s → |π s - d 3 s| ≤ 1 / 40 := by
    intro s hs
    exact (Vtrack_eq_zero_iff 3 (π s) s).1 (hzero hs)
  -- 窓 [s₀, s₀+1/2], s₀ = 16k/5 - 1/4 > T
  obtain ⟨k, hk⟩ := exists_nat_gt ((T + 1 / 4) * (5 / 16))
  set s₀ : ℝ := 16 * k / 5 - 1 / 4 with hs₀
  have hTs₀ : T < s₀ := by rw [hs₀]; nlinarith
  have hTs₁ : T < s₀ + 1 / 2 := by linarith
  have b0 := hband s₀ hTs₀
  have b1 := hband (s₀ + 1 / 2) hTs₁
  have hlip : |π (s₀ + 1 / 2) - π s₀| ≤ 1 / 2 := by
    have := hπ.dist_le_mul (s₀ + 1 / 2) s₀
    simpa [Real.dist_eq] using this
  -- 基準の増分 |d(s₁)-d(s₀)| = 6 sin a ≥ 15/16
  set a : ℝ := 5 * Real.pi / 64 with ha
  have hsin : 0 < Real.sin a := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [ha]; linarith [Real.pi_pos]
  have hjordan : 2 / Real.pi * a ≤ Real.sin a :=
    Real.mul_le_sin (by positivity) (by rw [ha]; linarith [Real.pi_pos])
  have hjord' : 5 / 32 ≤ Real.sin a := by
    have : 2 / Real.pi * a = 5 / 32 := by rw [ha]; field_simp; ring
    linarith
  have hω0 : ω * s₀ = k * Real.pi - a := by
    rw [hs₀, ha]; unfold ω; ring
  have hω1 : ω * (s₀ + 1 / 2) = k * Real.pi + a := by
    rw [hs₀, ha]; unfold ω; ring
  have hdiff : |d 3 (s₀ + 1 / 2) - d 3 s₀| = 6 * Real.sin a := by
    unfold d
    rw [hω0, hω1]
    have e1 : Real.sin (k * Real.pi + a) = (-1) ^ k * Real.sin a := by
      rw [add_comm, Real.sin_add_nat_mul_pi]
    have e2 : Real.sin (k * Real.pi - a) = (-1) ^ k * (-Real.sin a) := by
      rw [sub_eq_neg_add, Real.sin_add_nat_mul_pi, Real.sin_neg]
    rw [e1, e2]
    have : (3 : ℝ) * ((-1) ^ k * Real.sin a) - 3 * ((-1) ^ k * -Real.sin a) =
        6 * ((-1) ^ k * Real.sin a) := by ring
    rw [this, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hsin]
    norm_num
  have htri : |d 3 (s₀ + 1 / 2) - d 3 s₀| ≤ 1 / 40 + 1 / 2 + 1 / 40 := by
    calc |d 3 (s₀ + 1 / 2) - d 3 s₀|
        = |(d 3 (s₀ + 1 / 2) - π (s₀ + 1 / 2)) + (π (s₀ + 1 / 2) - π s₀) + (π s₀ - d 3 s₀)| := by
          ring_nf
      _ ≤ |d 3 (s₀ + 1 / 2) - π (s₀ + 1 / 2)| + |π (s₀ + 1 / 2) - π s₀| + |π s₀ - d 3 s₀| := by
          refine (abs_add_three _ _ _)
      _ ≤ 1 / 40 + 1 / 2 + 1 / 40 := by
          rw [abs_sub_comm (d 3 (s₀ + 1 / 2))]
          linarith
  rw [hdiff] at htri
  linarith

/-- A=1/2: `d` は 1-リプシッツで、`x=d(T)` から `V=0` を永久に保つ（24-A は成立しない）。 -/
theorem trackable_zero_cost (T : ℝ) :
    admissible (d (1 / 2)) (d (1 / 2) T) T ∧
      (fun s => running (1 / 2) (d (1 / 2)) (d (1 / 2) T) T s) =ᵐ[futureLebesgueMeasure T] 0 := by
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun s t => ?_
    have h := Real.abs_sin_sub_sin_le (ω * s) (ω * t)
    have hω : ω ≤ 2 := by unfold ω; linarith [Real.pi_lt_four]
    have : dist (d (1 / 2) s) (d (1 / 2) t) = 1 / 2 * |Real.sin (ω * s) - Real.sin (ω * t)| := by
      unfold d
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [this, Real.dist_eq]
    have hω0 : 0 ≤ ω := by unfold ω; positivity
    calc 1 / 2 * |Real.sin (ω * s) - Real.sin (ω * t)|
        ≤ 1 / 2 * |ω * s - ω * t| := by gcongr
      _ = 1 / 2 * ω * |s - t| := by rw [← mul_sub, abs_mul, abs_of_nonneg hω0]; ring
      _ ≤ (1 : NNReal) * |s - t| := by
          simp only [NNReal.coe_one, one_mul]
          nlinarith [abs_nonneg (s - t)]
  · filter_upwards with s
    simp only [running, Vtrack, Pi.zero_apply]
    simp

/-- 追従可能なら最適値は 0（零コスト方策で達成）。 -/
theorem trackable_value_zero (T : ℝ) :
    discountedFeedbackValue (fun t => futureLebesgueMeasure t) (theorem26DiscountWeight 1)
      (fun (π : ℝ → ℝ) (x : ℝ) (T s : ℝ) => running (1 / 2) π x T s) (d (1 / 2)) (d (1 / 2) T) T = 0 := by
  unfold discountedFeedbackValue
  have h := (trackable_zero_cost T).2
  have : (fun s => theorem26DiscountWeight 1 T s * running (1 / 2) (d (1 / 2)) (d (1 / 2) T) T s)
      =ᵐ[futureLebesgueMeasure T] 0 := by
    filter_upwards [h] with s hs
    have hs' : running (1 / 2) (d (1 / 2)) (d (1 / 2) T) T s = 0 := hs
    simp only [Pi.zero_apply]
    rw [hs', mul_zero]
  rw [integral_congr_ae this]
  simp

/-- A=3: 一般定理の呼び出し。有限コスト方策・最適方策の存在・可積分性を仮定して `J*>0`。 -/
theorem hard_optimal_value_positive (x T optimalValue : ℝ) (π₀ : ℝ → ℝ)
    (hint : ∀ π, admissible π x T →
      Integrable (fun s => theorem26DiscountWeight 1 T s * running 3 π x T s)
        (futureLebesgueMeasure T))
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue = discountedFeedbackValue (fun t => futureLebesgueMeasure t)
      (theorem26DiscountWeight 1) (fun (π : ℝ → ℝ) (x : ℝ) (T s : ℝ) => running 3 π x T s) π₀ x T)
    (hminimal : ∀ π, admissible π x T → optimalValue ≤ discountedFeedbackValue
      (fun t => futureLebesgueMeasure t) (theorem26DiscountWeight 1)
      (fun (π : ℝ → ℝ) (x : ℝ) (T s : ℝ) => running 3 π x T s) π x T) :
    0 < optimalValue := by
  refine theorem24_positive_optimal_value_of_condition24A
    (State := ℝ) (Feedback := ℝ → ℝ) (fun t => futureLebesgueMeasure t)
    (theorem26DiscountWeight 1) (fun (π : ℝ → ℝ) (x : ℝ) (T s : ℝ) => running 3 π x T s)
    admissible π₀ x T optimalValue ?_ ?_ hint hπ₀ hattains hminimal (condition24A_hard x T)
  · exact theorem26DiscountWeight_pos_ae 1 T
  · intro π _
    exact Filter.Eventually.of_forall fun s => Vtrack_nonneg 3 (π s) s

/-- 可積分性をモデル自身から供給した定理24の適用形。残る仮定は最適方策の
存在・達成と最小性だけであり、それらは `exists_tracking_optimal_policy`（直接法）で
構成され、`hard_tracking_value_positive` で使われる。 -/
theorem hard_optimal_value_positive_of_optimal (x T optimalValue : ℝ) (π₀ : ℝ → ℝ)
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue = discountedFeedbackValue (fun t => futureLebesgueMeasure t)
      (theorem26DiscountWeight 1) (fun (π : ℝ → ℝ) (x : ℝ) (T s : ℝ) => running 3 π x T s) π₀ x T)
    (hminimal : ∀ π, admissible π x T → optimalValue ≤ discountedFeedbackValue
      (fun t => futureLebesgueMeasure t) (theorem26DiscountWeight 1)
      (fun (π : ℝ → ℝ) (x : ℝ) (T s : ℝ) => running 3 π x T s) π x T) :
    0 < optimalValue := by
  exact hard_optimal_value_positive x T optimalValue π₀
    (fun π hπ => discounted_running_integrable 3 x T hπ) hπ₀ hattains hminimal

/-- A=3 の追従問題は任意の初期対で最適軌道を持ち、その最適費用は正である。 -/
theorem hard_tracking_value_positive (x T : ℝ) : 0 < trackingValue 3 x T := by
  obtain ⟨π, hπ, hattains, hminimal⟩ := exists_tracking_optimal_policy 3 x T
  have hvalue : trackingValue 3 x T =
      discountedFeedbackValue (fun t => futureLebesgueMeasure t) (theorem26DiscountWeight 1)
        (fun (π : ℝ → ℝ) (x : ℝ) (T s : ℝ) => running 3 π x T s) π x T := by
    simpa [trackingCost] using hattains.symm
  have hmin : ∀ π', admissible π' x T → trackingValue 3 x T ≤
      discountedFeedbackValue (fun t => futureLebesgueMeasure t) (theorem26DiscountWeight 1)
        (fun (π : ℝ → ℝ) (x : ℝ) (T s : ℝ) => running 3 π x T s) π' x T := by
    intro π' hπ'
    rw [← hattains]
    simpa [trackingCost] using hminimal π' hπ'
  exact hard_optimal_value_positive_of_optimal x T (trackingValue 3 x T) π hπ hvalue hmin

end Tomabechi.Examples.Theorem24
