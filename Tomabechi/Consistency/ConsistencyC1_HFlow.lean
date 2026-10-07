import Theorem1_4_HFlow
import Theorem20
import Tomabechi.Examples.Theorem20_SymbolicPresence
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# C1: 全実数上で定義した指数収縮H-flow

ここでは状態と制御を実数とし、正の率 `a` で目標 `r` に近づく流を構成する。
流の式は開始時刻より前も含む全実数で定義する。したがって開始時刻での微分も通常の
二側微分として扱える。有限ホライズンでは任意の許容可測ゲイン入力のODE解の一意性と
最大ゲインの費用最小性まで示す。原文の方策クラスとの厳密な同定、定理1–4・20の全入力は
別途必要であり、C1完了を主張しない。
-/

noncomputable section

namespace Tomabechi.Consistency.ConsistencyC1

open Tomabechi.Theorem1
open Filter
open MeasureTheory
open scoped Gradient RealInnerProductSpace
open scoped Topology

/-! ## 有限ホライズン制御の最適性 -/

/-- 有限ホライズンで許す制御。制御信号は可測で、全時刻で `[0,3]` に入る。 -/
abbrev C1GainSignal := {u : ℝ → ℝ // Measurable u ∧ ∀ t, 0 ≤ u t ∧ u t ≤ 3}

/-- 制御 `u` の開始時刻 `t₀` からの累積量。 -/
noncomputable def c1AccumulatedGain (u : C1GainSignal) (t₀ t : ℝ) : ℝ :=
  ∫ s in t₀..t, u.1 s

/-- 可測かつ有界な制御は任意の有限区間で積分可能。 -/
theorem c1Gain_intervalIntegrable (u : C1GainSignal) (t₀ t : ℝ) :
    IntervalIntegrable u.1 volume t₀ t := by
  rw [intervalIntegrable_iff]
  let μ := volume.restrict (Set.uIoc t₀ t)
  have hfinite : volume (Set.uIoc t₀ t) < ⊤ := by
    apply lt_of_le_of_lt (MeasureTheory.measure_mono Set.uIoc_subset_uIcc)
    exact isCompact_uIcc.measure_lt_top
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ] using hfinite
  have hconst : Integrable (fun _ : ℝ => (3 : ℝ)) μ := integrable_const _
  refine hconst.mono' u.2.1.stronglyMeasurable.aestronglyMeasurable ?_
  filter_upwards with s
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [(u.2.2 s).1], (u.2.2 s).2⟩

/-- 累積ゲインは中間時刻で加法的に分割できる。 -/
theorem c1AccumulatedGain_add (u : C1GainSignal) (t₀ s t : ℝ) :
    c1AccumulatedGain u t₀ t =
      c1AccumulatedGain u t₀ s + c1AccumulatedGain u s t := by
  unfold c1AccumulatedGain
  symm
  exact intervalIntegral.integral_add_adjacent_intervals
    (c1Gain_intervalIntegrable u t₀ s) (c1Gain_intervalIntegrable u s t)

/-- 各時点までの累積ゲインは、0と最大制御の累積量の間にある。 -/
theorem c1AccumulatedGain_bounds (u : C1GainSignal) (t₀ t : ℝ) (ht : t₀ ≤ t) :
    0 ≤ c1AccumulatedGain u t₀ t ∧
      c1AccumulatedGain u t₀ t ≤ 3 * (t - t₀) := by
  have hu := c1Gain_intervalIntegrable u t₀ t
  have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume t₀ t :=
    continuous_const.intervalIntegrable t₀ t
  have hthree : IntervalIntegrable (fun _ : ℝ => (3 : ℝ)) volume t₀ t :=
    continuous_const.intervalIntegrable t₀ t
  have hlo := intervalIntegral.integral_mono_on ht hz hu (fun s _ => (u.2.2 s).1)
  have hhi := intervalIntegral.integral_mono_on ht hu hthree (fun s _ => (u.2.2 s).2)
  constructor
  · simpa [c1AccumulatedGain] using hlo
  · calc
      c1AccumulatedGain u t₀ t ≤ (t - t₀) * 3 := by
        simpa [c1AccumulatedGain, intervalIntegral.integral_const] using hhi
      _ = 3 * (t - t₀) := by ring

/-- 許容入力 `u` による明示軌道。最大ゲイン3の軌道も同じ式で得られる。 -/
noncomputable def c1ControlledOrbit (x t₀ : ℝ) (u : C1GainSignal) (t : ℝ) : ℝ :=
  x * Real.exp (-(c1AccumulatedGain u t₀ t))

/-- すべての制御信号について、積分軌道は開始状態を保つ。 -/
theorem c1ControlledOrbit_initial (x t₀ : ℝ) (u : C1GainSignal) :
    c1ControlledOrbit x t₀ u t₀ = x := by
  simp [c1ControlledOrbit, c1AccumulatedGain]

/-- 積分軌道は任意の中間時刻から同じ制御信号で再始動する。 -/
theorem c1ControlledOrbit_restart (x t₀ s t : ℝ) (u : C1GainSignal) :
    c1ControlledOrbit x t₀ u t =
      c1ControlledOrbit (c1ControlledOrbit x t₀ u s) s u t := by
  rw [c1ControlledOrbit, c1ControlledOrbit, c1AccumulatedGain_add]
  rw [show -(c1AccumulatedGain u t₀ s + c1AccumulatedGain u s t) =
      (-c1AccumulatedGain u t₀ s) + (-c1AccumulatedGain u s t) by ring,
    Real.exp_add]
  simp only [c1ControlledOrbit]
  ring

/-- 最大ゲイン軌道は任意の許容可測制御より各時点で二乗状態が小さい。 -/
theorem c1MaxGain_orbit_sq_le (x t₀ t : ℝ) (u : C1GainSignal) (ht : t₀ ≤ t) :
    (x * Real.exp (-(3 * (t - t₀)))) ^ 2 ≤
      (c1ControlledOrbit x t₀ u t) ^ 2 := by
  have hacc := c1AccumulatedGain_bounds u t₀ t ht
  have hexp : -(3 * (t - t₀)) ≤ -(c1AccumulatedGain u t₀ t) := by linarith [hacc.2]
  have hmono := Real.exp_le_exp.mpr hexp
  have hsq := (sq_le_sq₀ (Real.exp_nonneg _) (Real.exp_nonneg _)).2 hmono
  have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg x)
  simpa [c1ControlledOrbit, c1AccumulatedGain, mul_pow] using hmul

/-- 任意の許容可測ゲインが定める積分軌道は、有限地平上でa.e.にODEを満たす。 -/
theorem c1ControlledOrbit_ae_ode (x t₀ T : ℝ) (hT : 0 < T) (u : C1GainSignal) :
    ∀ᵐ t ∂volume.restrict (Set.Icc t₀ (t₀ + T)),
      HasDerivAt (fun s => c1ControlledOrbit x t₀ u s)
        (-(u.1 t) * c1ControlledOrbit x t₀ u t) t := by
  have hu := c1Gain_intervalIntegrable u t₀ (t₀ + T)
  have hderiv := hu.ae_hasDerivAt_integral
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards [hderiv] with t htd
  intro htIcc
  have htmem : t ∈ Set.uIcc t₀ (t₀ + T) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact htIcc
  have ht₀mem : t₀ ∈ Set.uIcc t₀ (t₀ + T) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact ⟨le_rfl, by linarith⟩
  have hA := htd htmem t₀ ht₀mem
  have hneg : HasDerivAt (fun s => -(c1AccumulatedGain u t₀ s)) (-(u.1 t)) t := by
    convert hA.neg using 1 <;> rfl
  have hexp := (Real.hasDerivAt_exp (-(c1AccumulatedGain u t₀ t))).comp t hneg
  have hpath := hexp.const_mul x
  convert hpath using 1
  · rfl
  · dsimp [c1ControlledOrbit]
    ring

/-- 許容可測入力の積分軌道は任意の有限前向き区間で絶対連続である。 -/
theorem c1ControlledOrbit_absolutelyContinuousOnInterval
    (x t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (u : C1GainSignal) :
    AbsolutelyContinuousOnInterval (fun s => c1ControlledOrbit x t₀ u s) t₀ t₁ := by
  have hprim : AbsolutelyContinuousOnInterval
      (fun s => c1AccumulatedGain u t₀ s) t₀ t₁ :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      (c1Gain_intervalIntegrable u t₀ t₁) (c := t₀) (by
        rw [Set.uIcc_of_le ht]
        exact ⟨le_rfl, ht⟩)
  have harg : AbsolutelyContinuousOnInterval
      (fun s => -(c1AccumulatedGain u t₀ s)) t₀ t₁ := hprim.neg
  have hexpLip : LipschitzOnWith 1 Real.exp (Set.Iic (0 : ℝ)) := by
    refine (convex_Iic (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f := Real.exp) (s := Set.Iic (0 : ℝ))
      (f' := fun z : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (Real.exp z))
      (C := 1) ?_ ?_
    · intro z hz
      simpa only [Function.comp_def, id_eq, mul_one] using
        ((HasDerivAt.exp (hasDerivAt_id z)).hasDerivWithinAt).hasFDerivWithinAt
    · intro z hz
      rw [ContinuousLinearMap.nnnorm_toSpanSingleton]
      have hreal : (‖Real.exp z‖₊ : ℝ) ≤ 1 := by
        rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg z)]
        exact Real.exp_le_one_iff.mpr hz
      exact_mod_cast hreal
  have hexpMaps : Set.MapsTo
      (fun s => -(c1AccumulatedGain u t₀ s)) (Set.uIcc t₀ t₁) (Set.Iic 0) := by
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    have hacc := c1AccumulatedGain_bounds u t₀ s hs.1
    change -(c1AccumulatedGain u t₀ s) ≤ 0
    linarith [hacc.1]
  have hexpAC := hexpLip.comp_absolutelyContinuousOnInterval hexpMaps harg
  simpa [Function.comp_def, c1ControlledOrbit] using hexpAC.const_mul x

/-- 目標 `r` のまわりに置いた任意制御の状態軌道。 -/
noncomputable def c1ControlledState (r x t₀ : ℝ) (u : C1GainSignal) (t : ℝ) : ℝ :=
  r + c1ControlledOrbit (x - r) t₀ u t

theorem c1ControlledState_initial (r x t₀ : ℝ) (u : C1GainSignal) :
    c1ControlledState r x t₀ u t₀ = x := by
  simp [c1ControlledState, c1ControlledOrbit_initial]

theorem c1ControlledState_restart (r x t₀ s t : ℝ) (u : C1GainSignal) :
    c1ControlledState r x t₀ u t =
      c1ControlledState r (c1ControlledState r x t₀ u s) s u t := by
  simp only [c1ControlledState]
  have hcenter : r + c1ControlledOrbit (x - r) t₀ u s - r =
      c1ControlledOrbit (x - r) t₀ u s := by ring
  rw [hcenter]
  exact congrArg (fun z : ℝ => r + z)
    (c1ControlledOrbit_restart (x - r) t₀ s t u)

/-- 中心化した積分状態軌道は、元の制御ベクトル場を有限区間a.e.満たす。 -/
theorem c1ControlledState_ae_ode (r x t₀ T : ℝ) (hT : 0 < T) (u : C1GainSignal) :
    ∀ᵐ t ∂volume.restrict (Set.Icc t₀ (t₀ + T)),
      HasDerivAt (fun s => c1ControlledState r x t₀ u s)
        (-(u.1 t) * (c1ControlledState r x t₀ u t - r)) t := by
  filter_upwards [c1ControlledOrbit_ae_ode (x - r) t₀ T hT u] with t h
  have h' := h.add_const r
  convert h' using 1 <;> simp [c1ControlledState] <;> ring

theorem c1ControlledState_absolutelyContinuousOnInterval
    (r x t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (u : C1GainSignal) :
    AbsolutelyContinuousOnInterval (fun s => c1ControlledState r x t₀ u s) t₀ t₁ := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => r) t₀ t₁ := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  change AbsolutelyContinuousOnInterval
    ((fun _ : ℝ => r) + fun s => c1ControlledOrbit (x - r) t₀ u s) t₀ t₁
  exact hconst.add (c1ControlledOrbit_absolutelyContinuousOnInterval (x - r) t₀ t₁ ht u)

/-- 任意のCarathéodory解は積分表示の候補軌道と一致する。
差の二乗のa.e.導関数が非正で、初期値が0であることから一意性を得る。 -/
theorem c1ControlledState_unique_on_interval
    (r x t₀ t₁ : ℝ) (u : C1GainSignal) (y : ℝ → ℝ)
    (ht : t₀ ≤ t₁) (hyAC : AbsolutelyContinuousOnInterval y t₀ t₁)
    (hyInitial : y t₀ = x)
    (hyODE : ∀ᵐ t ∂volume.restrict (Set.Icc t₀ t₁),
      HasDerivAt y (-(u.1 t) * (y t - r)) t) :
    y t₁ = c1ControlledState r x t₀ u t₁ := by
  by_cases hEq : t₀ = t₁
  · subst t₁
    rw [c1ControlledState_initial]
    exact hyInitial
  · have hlt : t₀ < t₁ := lt_of_le_of_ne ht hEq
    let candidate : ℝ → ℝ := fun t => c1ControlledState r x t₀ u t
    let delta : ℝ → ℝ := fun t => y t - candidate t
    let q : ℝ → ℝ := fun t => delta t * delta t
    have hcAC : AbsolutelyContinuousOnInterval candidate t₀ t₁ := by
      exact c1ControlledState_absolutelyContinuousOnInterval r x t₀ t₁ ht u
    have hdeltaAC : AbsolutelyContinuousOnInterval delta t₀ t₁ := by
      exact hyAC.sub hcAC
    have hqAC : AbsolutelyContinuousOnInterval q t₀ t₁ := by
      change AbsolutelyContinuousOnInterval (fun t => delta t * delta t) t₀ t₁
      exact hdeltaAC.mul hdeltaAC
    have hcODE : ∀ᵐ t ∂volume.restrict (Set.Icc t₀ t₁),
        HasDerivAt candidate (-(u.1 t) * (candidate t - r)) t := by
      have h := c1ControlledState_ae_ode r x t₀ (t₁ - t₀) (sub_pos.mpr hlt) u
      simpa [candidate, add_sub_cancel_left] using h
    have hqDeriv : ∀ᵐ t ∂volume.restrict (Set.Icc t₀ t₁),
        HasDerivAt q (-(2 * u.1 t) * (delta t) ^ 2) t := by
      filter_upwards [hyODE, hcODE] with t hy hc
      have hdelta : HasDerivAt delta (-(u.1 t) * delta t) t := by
        convert hy.sub hc using 1 <;> simp [delta, candidate] <;> ring
      have hq : HasDerivAt q (-(2 * u.1 t) * (delta t) ^ 2) t := by
        convert hdelta.mul hdelta using 1 <;> simp [q] <;> ring
      exact hq
    have hqDerivNonpos : deriv q ≤ᵐ[volume.restrict (Set.Icc t₀ t₁)] 0 := by
      filter_upwards [hqDeriv] with t hq
      have hu : 0 ≤ u.1 t := (u.2.2 t).1
      have hnonneg : 0 ≤ 2 * u.1 t * (delta t) ^ 2 := by positivity
      have heq : deriv q t = -(2 * u.1 t * (delta t) ^ 2) := by
        rw [hq.deriv]
        ring
      rw [heq]
      exact neg_nonpos.mpr hnonneg
    have hzero : q t₀ = 0 := by
      simp [q, delta, candidate, hyInitial, c1ControlledState_initial]
    have hint := intervalIntegral.integral_mono_ae_restrict ht
      hqAC.intervalIntegrable_deriv (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume t₀ t₁) hqDerivNonpos
    have hFTC := hqAC.integral_deriv_eq_sub
    have hdrop : q t₁ ≤ q t₀ := by
      have hInt : (∫ t in t₀..t₁, deriv q t) ≤ 0 := by simpa using hint
      rw [hFTC] at hInt
      linarith
    have hq_nonneg : 0 ≤ q t₁ := by
      change 0 ≤ delta t₁ * delta t₁
      nlinarith [sq_nonneg (delta t₁)]
    have hq_eq : q t₁ = 0 := by rw [hzero] at hdrop; linarith
    have hdelta_sq : delta t₁ * delta t₁ = 0 := hq_eq
    have hdelta_zero : delta t₁ = 0 := mul_self_eq_zero.mp hdelta_sq
    dsimp [delta, candidate] at hdelta_zero
    exact sub_eq_zero.mp hdelta_zero

/-- 区間内の各時刻で同じ解が一致する。終点一意性をその時刻までの部分区間へ適用する。 -/
theorem c1ControlledState_unique_on_interval_all
    (r x t₀ t₁ : ℝ) (u : C1GainSignal) (y : ℝ → ℝ)
    (ht : t₀ ≤ t₁) (hyAC : AbsolutelyContinuousOnInterval y t₀ t₁)
    (hyInitial : y t₀ = x)
    (hyODE : ∀ᵐ t ∂volume.restrict (Set.Icc t₀ t₁),
      HasDerivAt y (-(u.1 t) * (y t - r)) t) :
    ∀ t ∈ Set.Icc t₀ t₁, y t = c1ControlledState r x t₀ u t := by
  intro s hs
  have hACs : AbsolutelyContinuousOnInterval y t₀ s := by
    apply hyAC.mono
    rw [Set.uIcc_of_le hs.1, Set.uIcc_of_le ht]
    exact Set.Icc_subset_Icc le_rfl hs.2
  have hODEvol := (ae_restrict_iff' measurableSet_Icc).1 hyODE
  have hODEs : ∀ᵐ t ∂volume.restrict (Set.Icc t₀ s),
      HasDerivAt y (-(u.1 t) * (y t - r)) t := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hODEvol] with t hvalid
    intro hts
    apply hvalid
    exact ⟨hts.1, le_trans hts.2 hs.2⟩
  exact c1ControlledState_unique_on_interval r x t₀ s u y hs.1 hACs hyInitial hODEs

/-- 正の基準値を加えた二次走行費用を有限時間区間上で積分した拡張実数値。 -/
noncomputable def c1FiniteHorizonCost (x t₀ T : ℝ) (u : C1GainSignal) : ENNReal :=
  ∫⁻ t, ENNReal.ofReal
    (1 + (c1ControlledOrbit x t₀ u t) ^ 2)
    ∂volume.restrict (Set.Icc t₀ (t₀ + T))

/-- Cost of an arbitrary state trajectory on the same finite horizon. -/
noncomputable def c1TrajectoryFiniteHorizonCost
    (r t₀ T : ℝ) (y : ℝ → ℝ) : ENNReal :=
  ∫⁻ t, ENNReal.ofReal (1 + (y t - r) ^ 2)
    ∂volume.restrict (Set.Icc t₀ (t₀ + T))

/-- 有限ホライズンで選ぶ最大ゲイン信号。 -/
def c1MaxGainSignal : C1GainSignal :=
  ⟨fun _ => 3, measurable_const, fun _ => ⟨by norm_num, le_rfl⟩⟩

/-- 最大ゲインとは異なる許容信号。 -/
def c1ZeroGainSignal : C1GainSignal :=
  ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, by norm_num⟩⟩

/-- この最適化問題には少なくとも二つの異なる許容制御がある。 -/
theorem c1_two_distinct_admissible_gains : c1ZeroGainSignal ≠ c1MaxGainSignal := by
  intro h
  have hval := congrArg Subtype.val h
  have := congrFun hval 0
  norm_num [c1ZeroGainSignal, c1MaxGainSignal] at this

/-- 最大ゲイン信号の累積量は `3(t-t₀)` である。 -/
theorem c1MaxGain_accumulation (t₀ t : ℝ) :
    c1AccumulatedGain c1MaxGainSignal t₀ t = 3 * (t - t₀) := by
  simp [c1AccumulatedGain, c1MaxGainSignal, intervalIntegral.integral_const,
    mul_comm]

/-- 選択する状態時刻feedbackは最大ゲインで、連続かつ右連続である。 -/
def c1OptimalFeedback : ℝ → ℝ → ℝ := fun _ _ => 3

theorem c1OptimalFeedback_continuous : Continuous (Function.uncurry c1OptimalFeedback) :=
  continuous_const

theorem c1OptimalFeedback_rightContinuous (x : ℝ) :
    Continuous fun t : ℝ => c1OptimalFeedback x t := continuous_const

theorem c1OptimalFeedback_rightLimit (x t₀ : ℝ) :
    Tendsto (fun t : ℝ => c1OptimalFeedback x t) (𝓝[>] t₀) (𝓝 3) := by
  simpa [c1OptimalFeedback] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (3 : ℝ)) (𝓝[>] t₀) (𝓝 3))

/-- 各開始状態と開始時刻に対して選ぶ有限ホライズン制御列。
このモデルでは、どの組に対しても最大ゲイン3の定数列を選ぶ。 -/
def c1SelectedHorizonControl (p : ℝ × ℝ) : ℝ → ℝ := fun _ => 3

/-- 最適制御列の選択は、開始時刻と初期状態についてBorel可測である。 -/
theorem c1SelectedHorizonControl_measurable :
    Measurable c1SelectedHorizonControl := measurable_const

/-- 選ばれた制御列は、すべての実数時刻で許容最大ゲイン信号である。 -/
theorem c1SelectedHorizonControl_is_admissible (p : ℝ × ℝ) :
    (⟨c1SelectedHorizonControl p, measurable_const,
      fun s => ⟨by simp [c1SelectedHorizonControl], by norm_num [c1SelectedHorizonControl]⟩⟩
      : C1GainSignal) = c1MaxGainSignal := by
  apply Subtype.ext
  rfl

/-- 選択した最適制御列の右連続代表の開始点右極限は、閉ループfeedbackと一致する。 -/
theorem c1SelectedHorizonControl_rightLimit (x t₀ : ℝ) :
    Tendsto (fun s : ℝ => c1SelectedHorizonControl (t₀, x) s)
      (𝓝[>] t₀) (𝓝 (c1OptimalFeedback x t₀)) := by
  simpa [c1SelectedHorizonControl, c1OptimalFeedback] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (3 : ℝ)) (𝓝[>] t₀) (𝓝 3))

/-- 正の有限ホライズンで最大ゲインが全可測ゲイン制御の費用を最小化する。
可測性・有界性から定義された費用は存在し、点ごとの軌道比較からargminが従う。 -/
theorem c1_maximum_gain_attains_finite_horizon_argmin
    (x t₀ T : ℝ) (_hT : 0 < T) :
    ∀ u : C1GainSignal,
      c1FiniteHorizonCost x t₀ T c1MaxGainSignal ≤
        c1FiniteHorizonCost x t₀ T u := by
  intro u
  unfold c1FiniteHorizonCost
  apply MeasureTheory.lintegral_mono_ae
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards with t ht
  have htime : t₀ ≤ t := ht.1
  have hsq := c1MaxGain_orbit_sq_le x t₀ t u htime
  have hmax : c1ControlledOrbit x t₀ c1MaxGainSignal t =
      x * Real.exp (-(3 * (t - t₀))) := by
    simp [c1ControlledOrbit, c1MaxGain_accumulation]
  have hsq' : (c1ControlledOrbit x t₀ c1MaxGainSignal t) ^ 2 ≤
      (c1ControlledOrbit x t₀ u t) ^ 2 := by
    rw [hmax]
    exact hsq
  have hsq'' := add_le_add_right hsq' 1
  have hreal : 1 + (c1ControlledOrbit x t₀ c1MaxGainSignal t) ^ 2 ≤
      1 + (c1ControlledOrbit x t₀ u t) ^ 2 := by
    simpa [add_comm] using hsq''
  apply ENNReal.ofReal_le_ofReal
  simpa using hreal

/-- 選択した最大ゲインの有限ホライズン費用は有限である。 -/
theorem c1_maximum_gain_finite_cost (x t₀ T : ℝ) :
    c1FiniteHorizonCost x t₀ T c1MaxGainSignal < ⊤ := by
  unfold c1FiniteHorizonCost
  let f : ℝ → ℝ := fun t =>
    1 + (x * Real.exp (-3 * (t - t₀))) ^ 2
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hint : Integrable f (volume.restrict (Set.Icc t₀ (t₀ + T))) := by
    exact hfcont.continuousOn.integrableOn_compact isCompact_Icc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc t₀ (t₀ + T))] f := by
    filter_upwards with t
    positivity
  have heq :
      (∫⁻ t, ENNReal.ofReal
        (1 + (c1ControlledOrbit x t₀ c1MaxGainSignal t) ^ 2)
        ∂volume.restrict (Set.Icc t₀ (t₀ + T))) = ENNReal.ofReal (∫ t, f t ∂volume.restrict (Set.Icc t₀ (t₀ + T))) := by
    calc
      (∫⁻ t, ENNReal.ofReal
          (1 + (c1ControlledOrbit x t₀ c1MaxGainSignal t) ^ 2)
          ∂volume.restrict (Set.Icc t₀ (t₀ + T))) =
          ∫⁻ t, ENNReal.ofReal (f t) ∂volume.restrict (Set.Icc t₀ (t₀ + T)) := by
        apply lintegral_congr_ae
        filter_upwards with t
        simp [f, c1ControlledOrbit, c1AccumulatedGain, c1MaxGainSignal,
          intervalIntegral.integral_const]
        congr 1
        ring
      _ = ENNReal.ofReal (∫ t, f t ∂volume.restrict (Set.Icc t₀ (t₀ + T))) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
  rw [heq]
  exact ENNReal.ofReal_lt_top

/-- 絶対連続でODEを満たす軌道は積分表示の軌道と一致し、その費用も等しい。 -/
theorem c1TrajectoryFiniteHorizonCost_eq_controlCost
    (r x t₀ T : ℝ) (hT : 0 < T) (u : C1GainSignal) (y : ℝ → ℝ)
    (hyAC : AbsolutelyContinuousOnInterval y t₀ (t₀ + T))
    (hyInitial : y t₀ = x)
    (hyODE : ∀ᵐ t ∂volume.restrict (Set.Icc t₀ (t₀ + T)),
      HasDerivAt y (-(u.1 t) * (y t - r)) t) :
    c1TrajectoryFiniteHorizonCost r t₀ T y =
      c1FiniteHorizonCost (x - r) t₀ T u := by
  have hpath := c1ControlledState_unique_on_interval_all
    r x t₀ (t₀ + T) u y (by linarith) hyAC hyInitial hyODE
  unfold c1TrajectoryFiniteHorizonCost c1FiniteHorizonCost
  apply lintegral_congr_ae
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards with t ht
  have hyt := hpath t ht
  congr 1
  rw [hyt]
  simp [c1ControlledState]

/-- 有界可測ゲインで動く任意のCarathéodory軌道に対し、最大ゲインfeedbackの費用が最小である。 -/
theorem c1_maximum_gain_minimizes_all_ode_trajectories
    (r x t₀ T : ℝ) (hT : 0 < T) (u : C1GainSignal) (y : ℝ → ℝ)
    (hyAC : AbsolutelyContinuousOnInterval y t₀ (t₀ + T))
    (hyInitial : y t₀ = x)
    (hyODE : ∀ᵐ t ∂volume.restrict (Set.Icc t₀ (t₀ + T)),
      HasDerivAt y (-(u.1 t) * (y t - r)) t) :
    c1TrajectoryFiniteHorizonCost r t₀ T
        (fun t => c1ControlledState r x t₀ c1MaxGainSignal t) ≤
      c1TrajectoryFiniteHorizonCost r t₀ T y := by
  rw [c1TrajectoryFiniteHorizonCost_eq_controlCost r x t₀ T hT
      c1MaxGainSignal (fun t => c1ControlledState r x t₀ c1MaxGainSignal t)
      (c1ControlledState_absolutelyContinuousOnInterval r x t₀ (t₀ + T) (by linarith) c1MaxGainSignal)
      (c1ControlledState_initial r x t₀ c1MaxGainSignal)
      (c1ControlledState_ae_ode r x t₀ T hT c1MaxGainSignal)]
  rw [c1TrajectoryFiniteHorizonCost_eq_controlCost r x t₀ T hT u y hyAC hyInitial hyODE]
  exact c1_maximum_gain_attains_finite_horizon_argmin (x - r) t₀ T hT u

/-- 選択feedbackで実現するCarathéodory軌道は、各正の有限ホライズンで有限費用を持つ。 -/
theorem c1_selected_trajectory_finite_cost
    (r x t₀ T : ℝ) (hT : 0 < T) :
    c1TrajectoryFiniteHorizonCost r t₀ T
      (fun t => c1ControlledState r x t₀ c1MaxGainSignal t) < ⊤ := by
  rw [c1TrajectoryFiniteHorizonCost_eq_controlCost r x t₀ T hT
    c1MaxGainSignal
    (fun t => c1ControlledState r x t₀ c1MaxGainSignal t)
    (c1ControlledState_absolutelyContinuousOnInterval r x t₀ (t₀ + T)
      (by linarith) c1MaxGainSignal)
    (c1ControlledState_initial r x t₀ c1MaxGainSignal)
    (c1ControlledState_ae_ode r x t₀ T hT c1MaxGainSignal)]
  exact c1_maximum_gain_finite_cost (x - r) t₀ T


/-- 制御値は実数で、正の率モデルでは許容制御を `[0,a]` にする。
選択feedbackは最大ゲイン `a`。指数式はそのfeedbackの閉ループ解である。 -/
def linearFlow (a r : ℝ) : ClosedLoopPolicyFlow ℝ ℝ where
  admissible := fun u => a ≤ 0 ∨ (0 ≤ u ∧ u ≤ a)
  feedback := fun _ _ => a
  vectorField := fun x u _ => -u * (x - r)
  flow := fun t₀ x t => r + (x - r) * Real.exp (-a * (t - t₀))
  feedback_admissible := by
    intro x t
    by_cases ha : a ≤ 0
    · exact Or.inl ha
    · exact Or.inr ⟨le_of_lt (lt_of_not_ge ha), le_rfl⟩
  initial := by
    intro t₀ x
    change r + (x - r) * Real.exp (-a * (t₀ - t₀)) = x
    simp
  restart := by
    intro t₀ x s t h₀s hst
    change r + (x - r) * Real.exp (-a * (t - t₀)) =
      r + (r + (x - r) * Real.exp (-a * (s - t₀)) - r) *
        Real.exp (-a * (t - s))
    rw [show r + (x - r) * Real.exp (-a * (s - t₀)) - r =
      (x - r) * Real.exp (-a * (s - t₀)) by ring]
    rw [show t - t₀ = (s - t₀) + (t - s) by ring]
    rw [show -a * ((s - t₀) + (t - s)) =
      (-a * (s - t₀)) + (-a * (t - s)) by ring, Real.exp_add]
    ring

/-- 反復ホライズン最適選択と閉ループflowで使うfeedbackは同じ定数ゲイン。 -/
theorem c1OptimalFeedback_is_hflow_feedback (r : ℝ) :
    (linearFlow 3 r).feedback = c1OptimalFeedback := rfl

/-- 最大ゲインの積分軌道は、構成したH-flowの軌道そのもの（目標からの偏差）である。 -/
theorem c1MaxGain_orbit_eq_hflow (r x t₀ t : ℝ) :
    c1ControlledOrbit (x - r) t₀ c1MaxGainSignal t =
      (linearFlow 3 r).flow t₀ x t - r := by
  change (x - r) * Real.exp (-(∫ s in t₀..t, (3 : ℝ))) =
    r + (x - r) * Real.exp (-3 * (t - t₀)) - r
  rw [intervalIntegral.integral_const]
  congr 1
  ring

/-- 同じ線形流は全実数の開始時刻・状態に対して通常微分可能で、その導関数は
feedbackが指定するベクトル場に一致する。 -/
def differentiableLinearFlow (a r : ℝ) : DifferentiableClosedLoopPolicyFlow ℝ ℝ where
  toClosedLoopPolicyFlow := linearFlow a r
  solves := by
    intro t₀ x t ht
    have hlin : HasDerivAt (fun s : ℝ => -a * (s - t₀)) (-a) t := by
      simpa using (hasDerivAt_id t).sub_const t₀ |>.const_mul (-a)
    have hexp := (Real.hasDerivAt_exp (-a * (t - t₀))).comp t hlin
    have hflow : HasDerivAt
        (fun s : ℝ => r + (x - r) * Real.exp (-a * (s - t₀)))
        ((x - r) * (Real.exp (-a * (t - t₀)) * (-a))) t := by
      have h := hexp.const_mul (x - r) |>.add_const r
      simpa [add_comm] using h
    convert hflow using 1
    · funext s
      rfl
    · simp [linearFlow]
      ring

/-- The closed-loop vector field is globally Lipschitz in the state, with
constant `|a|`, uniformly in time. -/
theorem linearFlow_vectorField_lipschitz (a r t : ℝ) :
    LipschitzWith ‖a‖₊ (fun x : ℝ =>
      (linearFlow a r).vectorField x ((linearFlow a r).feedback x t) t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq]
  rw [linearFlow]
  simp only
  rw [show (-a * (x - r)) - (-a * (y - r)) = -a * (x - y) by ring,
    abs_mul]
  simp [Real.norm_eq_abs]

/-- 任意の許容可測ゲイン信号に対し、制御ベクトル場は状態について一様な定数3で大域Lipschitzとなる。 -/
theorem c1_controlled_vectorField_lipschitz (u : C1GainSignal) (r t : ℝ) :
    LipschitzWith 3 (fun x : ℝ =>
      (linearFlow 3 r).vectorField x (u.1 t) t) := by
  have hbase : LipschitzWith ‖u.1 t‖₊ (fun x : ℝ => -(u.1 t) * (x - r)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq]
    rw [show (-(u.1 t) * (x - r)) - (-(u.1 t) * (y - r)) =
      -(u.1 t) * (x - y) by ring, abs_mul]
    simp [Real.norm_eq_abs]
  have hbound : ‖u.1 t‖₊ ≤ (3 : NNReal) := by
    have hreal : (‖u.1 t‖₊ : ℝ) ≤ 3 := by
      rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (u.2.2 t).1]
      exact (u.2.2 t).2
    exact_mod_cast hreal
  have h := hbase.weaken hbound
  simpa [linearFlow] using h

/-- 選択したfeedbackは定数であり、状態と時刻についてBorel可測である。 -/
theorem linearFlow_feedback_measurable (a r : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      (linearFlow a r).feedback p.1 p.2) := by
  exact measurable_const

/-- Every positive-rate instance has at least two distinct admissible controls,
so its control set is not a singleton. -/
theorem linearFlow_has_multiple_controls (a r : ℝ) (ha : 0 < a) :
    (linearFlow a r).admissible 0 ∧ (linearFlow a r).admissible a ∧ 0 ≠ a := by
  constructor
  · simp [linearFlow, ha.le]
  constructor
  · simp [linearFlow, ha.le]
  · exact (ne_of_gt ha).symm

/-- The selected feedback has a continuous (hence right-continuous) time
representative at every state and every starting time. -/
theorem linearFlow_feedback_continuous (a r x : ℝ) :
    Continuous (fun t : ℝ => (linearFlow a r).feedback x t) := by
  exact continuous_const

/-- Among all admissible controls in `[0,a]`, the selected maximum gain gives
the smallest instantaneous derivative of the quadratic distance residual. -/
theorem maximum_gain_minimizes_quadratic_derivative
    (a r x u : ℝ) (ha : 0 < a) (hu : (linearFlow a r).admissible u) :
    -2 * a * (x - r) ^ 2 ≤ -2 * u * (x - r) ^ 2 := by
  rcases hu with hneg | ⟨hu0, hua⟩
  · linarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hua) (sq_nonneg (x - r))]

/-- 任意の時刻で目標からの誤差は初期誤差に指数因子を掛けたもの。 -/
theorem linearFlow_error (a r t₀ x t : ℝ) :
    (linearFlow a r).flow t₀ x t - r =
      (x - r) * Real.exp (-a * (t - t₀)) := by
  simp [linearFlow]

/-- 正の率なら、開始後の流は目標との距離を拡大しない。 -/
theorem linearFlow_distance_nonincreasing (a r t₀ x t : ℝ)
    (ha : 0 ≤ a) (ht : t₀ ≤ t) :
    |(linearFlow a r).flow t₀ x t - r| ≤ |x - r| := by
  rw [linearFlow_error]
  rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  have he : Real.exp (-a * (t - t₀)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  exact mul_le_of_le_one_right (abs_nonneg _) he

/-- Lyapunov residual along the same flow, with a strictly positive threshold. -/
def positiveResidualPath (a r t₀ x s : ℝ) : ℝ :=
  ((x - r) * Real.exp (-a * (s - t₀))) ^ 2

/-- A non-target initial state has strictly positive residual at every finite time. -/
theorem positiveResidualPath_pos (a r t₀ x s : ℝ) (hx : x ≠ r) :
    0 < positiveResidualPath a r t₀ x s := by
  apply sq_pos_of_ne_zero
  apply mul_ne_zero
  · exact sub_ne_zero.mpr hx
  · exact (Real.exp_ne_zero _)

/-- The model's closed reachable set is all of `ℝ`: every real point is already
reachable at the nonnegative absolute start time `t₀`. -/
theorem linearFlow_closedReachable_univ (a r t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    closedLoopReachableSet
      (policyFlowReachableAt (linearFlow a r) Set.univ t₀) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  apply mem_closedLoopReachableSet_of_mem_reachableAt
    (policyFlowReachableAt (linearFlow a r) Set.univ t₀) ht₀
  simpa [linearFlow] using
    (mem_policyFlowReachableAt_of_flow (linearFlow a r) Set.univ t₀ t₀ y
      (by simp) le_rfl)

/-- On the entire closed reachable set and at every time, squared distance to
the positive-threshold TCZ is exactly the quadratic residual (`C=1`). -/
theorem linearFlow_global_error_bound (a r t₀ z s : ℝ) (ht₀ : 0 ≤ t₀) :
    (Metric.infDist z
      {y | y ∈ closedLoopReachableSet
          (policyFlowReachableAt (linearFlow a r) Set.univ t₀) ∧
        (1 + (y - r) ^ 2 : ℝ) ≤ 1}) ^ 2 ≤
      residual1 (1 + (z - r) ^ 2) 1 := by
  have hK := linearFlow_closedReachable_univ a r t₀ ht₀
  have hTCZ : {y | y ∈ closedLoopReachableSet
      (policyFlowReachableAt (linearFlow a r) Set.univ t₀) ∧
    (1 + (y - r) ^ 2 : ℝ) ≤ 1} = {r} := by
    ext y
    simp [hK]
    constructor <;> intro h <;> nlinarith
  rw [hTCZ, Metric.infDist_singleton, Real.dist_eq, sq_abs]
  simp [residual1, max_eq_left (sq_nonneg (z - r))]

private theorem positiveResidualPath_hasDerivAt
    (a r t₀ x s : ℝ) :
    HasDerivAt (positiveResidualPath a r t₀ x)
      (-2 * a * positiveResidualPath a r t₀ x s) s := by
  have hlin : HasDerivAt (fun u : ℝ => -a * (u - t₀)) (-a) s := by
    simpa using (hasDerivAt_id s).sub_const t₀ |>.const_mul (-a)
  have hexp := (Real.hasDerivAt_exp (-a * (s - t₀))).comp s hlin
  have hbase := hexp.const_mul (x - r)
  have hsq := hbase.pow 2
  convert hsq using 1
  · funext u
    simp [positiveResidualPath, mul_sub, mul_add]
  · simp [positiveResidualPath]
    ring

/-- The trajectory residual is absolutely continuous on every bounded interval. -/
private theorem positiveResidualPath_ac (a r t₀ x T : ℝ) (hT : t₀ ≤ T) :
    AbsolutelyContinuousOnInterval (positiveResidualPath a r t₀ x) t₀ T := by
  unfold positiveResidualPath
  apply ((by fun_prop : ContDiff ℝ 1
    (fun s : ℝ => ((x - r) * Real.exp (-a * (s - t₀))) ^ 2)).contDiffOn).absolutelyContinuousOnInterval

/-- Theorem 1's reachable TCZ estimate for this whole scalar affine system.
The reachable closure comes from the selected flow with `initialSet = univ`; the
TCZ itself is derived from the positive quadratic threshold sublevel, whose
only point is the target `r`. -/
theorem linearFlow_theorem1 (a r t₀ x : ℝ) (ha : 0 < a) (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t →
      (linearFlow a r).flow t₀ x t ∈ closedLoopReachableSet
        (policyFlowReachableAt (linearFlow a r) Set.univ t₀)) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist ((linearFlow a r).flow t₀ x t)
        {y | y ∈ closedLoopReachableSet
            (policyFlowReachableAt (linearFlow a r) Set.univ t₀) ∧
          (1 + (y - r) ^ 2 : ℝ) ≤ 1} ≤
        |x - r| * Real.exp (-a * (t - t₀))) ∧
    Filter.Tendsto (fun t => Metric.infDist ((linearFlow a r).flow t₀ x t)
      {y | y ∈ closedLoopReachableSet
          (policyFlowReachableAt (linearFlow a r) Set.univ t₀) ∧
        (1 + (y - r) ^ 2 : ℝ) ≤ 1}) atTop (𝓝 0) := by
  have hK : closedLoopReachableSet
      (policyFlowReachableAt (linearFlow a r) Set.univ t₀) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    apply mem_closedLoopReachableSet_of_mem_reachableAt
      (policyFlowReachableAt (linearFlow a r) Set.univ t₀) (by linarith [ht₀])
    simpa [linearFlow] using
      (mem_policyFlowReachableAt_of_flow (linearFlow a r) Set.univ t₀ t₀ y
        (by simp) le_rfl)
  have hTCZ : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      {y | y ∈ closedLoopReachableSet
          (policyFlowReachableAt (linearFlow a r) Set.univ t₀) ∧
        (1 + (y - r) ^ 2 : ℝ) ≤ 1}.Nonempty := by
    intro T hT s hs
    refine ⟨r, ?_, ?_⟩
    · simp [hK]
    · norm_num
  have hAC : ∀ T, t₀ ≤ T → AbsolutelyContinuousOnInterval
      (fun s => residual1
        ((1 + (((linearFlow a r).flow t₀ x s) - r) ^ 2 : ℝ)) 1) t₀ T := by
    intro T hT
    have hac := positiveResidualPath_ac a r t₀ x T hT
    have heq : (fun s => residual1
        (1 + (((linearFlow a r).flow t₀ x s) - r) ^ 2) 1) =
        positiveResidualPath a r t₀ x := by
      funext s
      simp [residual1, positiveResidualPath, linearFlow,
        max_eq_left (sq_nonneg ((x - r) * Real.exp (-a * (s - t₀))))]
      positivity
    rw [heq]
    exact hac
  have hDecay : ∀ T, t₀ ≤ T → ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc t₀ T),
      deriv (fun u => residual1
        ((1 + (((linearFlow a r).flow t₀ x u) - r) ^ 2 : ℝ)) 1) s ≤
        -2 * a * residual1
          ((1 + (((linearFlow a r).flow t₀ x s) - r) ^ 2 : ℝ)) 1 := by
    intro T hT
    filter_upwards with s
    have hderiv := positiveResidualPath_hasDerivAt a r t₀ x s
    have hfun : (fun u => residual1
        ((1 + (((linearFlow a r).flow t₀ x u) - r) ^ 2 : ℝ)) 1) =
        positiveResidualPath a r t₀ x := by
      funext u
      simp [residual1, positiveResidualPath, linearFlow,
        max_eq_left (sq_nonneg ((x - r) * Real.exp (-a * (u - t₀))))]
      <;> positivity
    have hAt := congrFun hfun s
    rw [hfun]
    rw [hderiv.deriv]
    rw [← hAt]
  have hError : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (Metric.infDist ((linearFlow a r).flow t₀ x s)
        {y | y ∈ closedLoopReachableSet
            (policyFlowReachableAt (linearFlow a r) Set.univ t₀) ∧
          (1 + (y - r) ^ 2 : ℝ) ≤ 1}) ^ 2 ≤
        1 * residual1 (1 + (((linearFlow a r).flow t₀ x s) - r) ^ 2) 1 := by
    intro T hT s hs
    have hset : {y | y ∈ closedLoopReachableSet
        (policyFlowReachableAt (linearFlow a r) Set.univ t₀) ∧
      (1 + (y - r) ^ 2 : ℝ) ≤ 1} = {r} := by
      ext y
      simp [hK]
      constructor <;> intro h <;> nlinarith
    rw [hset, Metric.infDist_singleton, Real.dist_eq]
    rw [linearFlow_error]
    rw [sq_abs]
    simp [residual1, max_eq_left (sq_nonneg _)]
  have hresult := theorem1_policy_flow_reachable_tcz_distance_tendsto_zero
    (linearFlow a r) Set.univ x (Set.mem_univ x)
    (fun _ _ => 1 + (_ - r) ^ 2) 1 a 1 t₀
    hTCZ hAC hDecay hError
    (by intro y hy t ht; simp [hK])
    ht₀ ha (by norm_num)
  refine ⟨hresult.1, ?_, hresult.2.2⟩
  intro t ht
  have hbound := hresult.2.1 t ht
  have hinitial : residual1
      ((1 + (((linearFlow a r).flow t₀ x t₀) - r) ^ 2 : ℝ)) 1 = (x - r) ^ 2 := by
    simp [residual1, linearFlow, max_eq_left (sq_nonneg (x - r))]
  rw [hinitial] at hbound
  simpa [Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le] using hbound

#check differentiableLinearFlow
#print axioms differentiableLinearFlow
#print axioms linearFlow_theorem1

/-! ## 同じflowに対する定理20の一次元原文条件モデル -/

/-- 二次距離残差に対する定理20用の全時刻誤差評価。 -/
theorem quadraticDistance_error_bound (r z : ℝ) :
    Metric.infDist z ({r} : Set ℝ) ≤
      2 * Real.sqrt (1 / 2 * (z - r) ^ 2) := by
  rw [Metric.infDist_singleton, Real.dist_eq]
  have hsq : (|z - r| / 2) ^ 2 ≤ 1 / 2 * (z - r) ^ 2 := by
    rw [div_pow, sq_abs]
    nlinarith [sq_nonneg (z - r)]
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  have hnonneg : 0 ≤ |z - r| := abs_nonneg _
  nlinarith

/-- For a closed unit interval of initial conditions, the flow-generated closed
reachable set is exactly that same compact interval. -/
theorem linearFlow_intervalReachable_eq (r t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    closedLoopReachableSet
      (policyFlowReachableAt (linearFlow 3 r) (Metric.closedBall r 1) t₀) =
      Metric.closedBall r 1 := by
  apply Set.Subset.antisymm
  · unfold closedLoopReachableSet
    apply closure_minimal ?_ Metric.isClosed_closedBall
    rintro y ⟨t, htime, hy⟩
    rcases hy with ⟨ht, x₀, hx₀, rfl⟩
    rw [Metric.mem_closedBall, Real.dist_eq]
    rw [linearFlow]
    have hx : |x₀ - r| ≤ 1 := by
      simpa [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using hx₀
    have he : 0 ≤ Real.exp (-3 * (t - t₀)) := (Real.exp_pos _).le
    have he1 : Real.exp (-3 * (t - t₀)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    rw [show r + (x₀ - r) * Real.exp (-3 * (t - t₀)) - r =
      (x₀ - r) * Real.exp (-3 * (t - t₀)) by ring, abs_mul,
      abs_of_nonneg he]
    calc
      |x₀ - r| * Real.exp (-3 * (t - t₀)) ≤ 1 * Real.exp (-3 * (t - t₀)) :=
        mul_le_mul_of_nonneg_right hx he
      _ ≤ 1 * 1 := by nlinarith [he, he1]
      _ = 1 := by ring
  · intro y hy
    apply subset_closure
    refine ⟨t₀, ht₀, ?_⟩
    refine ⟨le_rfl, y, hy, ?_⟩
    simp [linearFlow]

/-- Theorem-20 conclusion for the nonconstant scalar model
`D(x)=‖x-r‖²/2`, `P=1`, `s(D)=-D`, and unit mobility. A compact invariant
initial interval supplies the exact flow-generated closed reachable set. -/
def linearFlow_theorem20 (r t₀ x₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (hx₀ : x₀ ∈ Metric.closedBall r 1) := by
  let F := differentiableLinearFlow 3 r
  let initialSet : Set ℝ := Metric.closedBall r 1
  let K := closedLoopReachableSet
    (policyFlowReachableAt F.toClosedLoopPolicyFlow initialSet t₀)
  let V₀ : ℝ → ℝ := fun y => 1 / 2 * ‖y - r‖ ^ 2
  let P : ℝ → ℝ := fun _ => 1
  let D : ℝ → ℝ := V₀
  let s : ℝ → ℝ := fun d => -d
  let Z : Set ℝ := {r}
  let grad : ℝ → ℝ := fun t => F.flow t₀ x₀ t - r
  let gradP : ℝ → ℝ := fun _ => 0
  let g2 : ℝ → ℝ := fun t => (F.flow t₀ x₀ t - r) ^ 2
  have hKeq : K = Metric.closedBall r 1 := by
    simpa [K, F, differentiableLinearFlow, initialSet] using
      linearFlow_intervalReachable_eq r t₀ ht₀
  have hKcompact : IsCompact K := by
    rw [hKeq]
    exact isCompact_closedBall r 1
  have hKforward : ∀ y ∈ K, ∀ t, t₀ ≤ t → F.flow t₀ y t ∈ K := by
    intro y hy t ht
    rw [hKeq] at hy ⊢
    rw [Metric.mem_closedBall, Real.dist_eq] at hy ⊢
    have hdist := linearFlow_distance_nonincreasing 3 r t₀ y t (by norm_num) ht
    simpa [F, differentiableLinearFlow, linearFlow] using hdist.trans hy
  have hVgrad : ∀ t, t₀ ≤ t → HasGradientAt V₀ (grad t) (F.flow t₀ x₀ t) := by
    intro t ht
    simpa [V₀, grad, F, Real.norm_eq_abs, sq_abs] using
      (Tomabechi.Examples.Theorem20.hasGradientAt_halfNormSq r
        (F.flow t₀ x₀ t))
  have hPgrad : ∀ t, t₀ ≤ t → HasGradientAt P (gradP t) (F.flow t₀ x₀ t) := by
    intro t ht
    exact hasGradientAt_const (F.flow t₀ x₀ t) (1 : ℝ)
  have hDgrad : ∀ t, t₀ ≤ t → HasGradientAt D (grad t) (F.flow t₀ x₀ t) := by
    simpa [D] using hVgrad
  have hDnonneg : ∀ y, 0 ≤ D y := by
    intro y
    positivity
  have hDzero : ∀ y, D y = 0 ↔ y ∈ Z := by
    intro y
    constructor
    · intro hz
      have hsquare : |y - r| ^ 2 = 0 := by
        dsimp [D, V₀] at hz
        nlinarith
      have habs : |y - r| = 0 := (sq_eq_zero_iff).mp hsquare
      have hsub : y - r = 0 := abs_eq_zero.mp habs
      simp [Z, sub_eq_zero.mp hsub]
    · intro hz
      have hy : y = r := by simpa [Z] using hz
      simp [D, V₀, hy]
  have hZnonempty : Z.Nonempty := ⟨r, by simp [Z]⟩
  have hZclosed : IsClosed Z := isClosed_singleton
  have hsderiv : ∀ t, t₀ ≤ t → HasDerivAt s (-1) (D (F.flow t₀ x₀ t)) := by
    intro t ht
    simpa [s] using hasDerivAt_neg (D (F.flow t₀ x₀ t))
  have hField : ∀ y t,
      F.vectorField y (F.feedback y t) t =
        -(ContinuousLinearMap.id ℝ ℝ)
          (∇ (fun z => V₀ z - 2 * 1 * (P z * s (D z))) y) := by
    intro y t
    have hV : HasGradientAt V₀ (y - r) y := by
      simpa [V₀, Real.norm_eq_abs, sq_abs] using
        (Tomabechi.Examples.Theorem20.hasGradientAt_halfNormSq r y)
    have hP : HasGradientAt P 0 y := hasGradientAt_const y (1 : ℝ)
    have hD : HasGradientAt D (y - r) y := by simpa [D] using hV
    have hs : HasDerivAt s (-1) (D y) := by simpa [s] using hasDerivAt_neg (D y)
    have heff := Tomabechi.Theorem20.effective_potential_hasGradientAt
      V₀ P D s y (y - r) 0 (y - r) (-1) 2 hV hP hD hs
    have hgradEff : ∇ (fun z => V₀ z - 2 * 1 * (P z * s (D z))) y =
        3 * (y - r) := by
      calc
        ∇ (fun z => V₀ z - 2 * 1 * (P z * s (D z))) y =
            y - r - 2 * (r - y) := by
          simpa [P, s, D, V₀] using heff.gradient
        _ = 3 * (y - r) := by ring
    simpa [F, differentiableLinearFlow, linearFlow] using hgradEff.symm
  exact Tomabechi.Theorem20.theorem20_policy_flow_original_condition_conclusion
    F (fun _ => ContinuousLinearMap.id ℝ ℝ)
      (fun _ => ContinuousLinearMap.id ℝ ℝ) V₀ P D s
      2 1 (1 / 2) 1 1 2 1 t₀ ht₀ initialSet x₀ hx₀ Z g2
      (fun _ => -1) grad gradP grad
      (by intro y t; simpa using hField y t)
      hKcompact hKforward hVgrad hPgrad hDgrad hDnonneg hDzero
      hZnonempty hZclosed hsderiv
      (by intro t ht y; simp)
      (by intro t ht y z; simp [real_inner_comm])
      (by intro t ht y; simp [real_inner_self_eq_norm_sq])
      (by intro t ht hK hnot
          simp [gradP, grad, D, V₀, P, s]
          nlinarith [sq_nonneg (F.flow t₀ x₀ t - r)])
      (by intro t ht hK hnot; norm_num [P, s])
      (by intro t ht; simp [g2, D, V₀, Real.norm_eq_abs, sq_abs])
      (by intro t ht; simp [g2, grad, real_inner_self_eq_norm_sq])
      (by intro t ht
          simpa [Z, D, V₀, Real.norm_eq_abs, sq_abs] using
            quadraticDistance_error_bound r (F.flow t₀ x₀ t))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Tomabechi.Consistency.ConsistencyC1
