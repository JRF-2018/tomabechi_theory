import Mathlib.Order.FixedPoints
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Data.Set.Operations
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Theorem21
import Econlib.Math.Topology.FanGlicksberg
import Theorem16_25_Core

namespace Tomabechi.Theorem16_25

open Function
open scoped Convex
open scoped RealInnerProductSpace

def variableMobilityGradient (x : ℝ) : ℝ := x
noncomputable def metricMobilityCoordinate (x : ℝ) : ℝ := x + x ^ 2
noncomputable def metricMobilityVectorField (x : ℝ) : ℝ :=
  -(x / (1 + 2 * x) ^ 2)
noncomputable def metricMobilityTransformedDrift (x : ℝ) : ℝ :=
  x / (1 + 2 * x)
/-- `φ(x)=x+x²` の微分。 -/
theorem metricMobilityCoordinate_hasDerivAt (x : ℝ) :
    HasDerivAt metricMobilityCoordinate (1 + 2 * x) x := by
  unfold metricMobilityCoordinate
  convert (hasDerivAt_id x).add ((hasDerivAt_id x).pow 2) using 1
  · funext y
    simp [pow_two]
  · simp only [id_eq]
    ring
/-- 適合座標は状態依存流のベクトル場を `-x/(1+2x)` に送る。 -/
theorem metricMobilityCoordinate_chainRule {x : ℝ} (hx : 0 ≤ x) :
    (1 + 2 * x) * metricMobilityVectorField x =
      -metricMobilityTransformedDrift x := by
  unfold metricMobilityVectorField metricMobilityTransformedDrift
  have hden : 1 + 2 * x ≠ 0 := ne_of_gt (by linarith)
  field_simp [hden]
/-- 実際の状態依存移動度ODEを適合座標へ移す連鎖律。 -/
theorem metricMobility_coordinateFlow_hasDerivAt
    (f : ℝ → ℝ) (t : ℝ)
    (hf : HasDerivAt f (metricMobilityVectorField (f t)) t)
    (hfx : 0 ≤ f t) :
    HasDerivAt (fun s => metricMobilityCoordinate (f s))
      (-metricMobilityTransformedDrift (f t)) t := by
  have hcomp := (metricMobilityCoordinate_hasDerivAt (f t)).comp t hf
  convert hcomp using 1
  · rfl
  · rw [metricMobilityCoordinate_chainRule hfx]
/-- 適合座標における変換後ドリフトは区間 `[0,1]` 上で `1/27` 強単調。
この評価は状態依存流の縮小計量を構成する局所条件である。 -/
theorem metricMobilityTransformedDrift_strongMonotone
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1 / 27 : ℝ) *
        (metricMobilityCoordinate x - metricMobilityCoordinate y) ^ 2 ≤
      (metricMobilityTransformedDrift x - metricMobilityTransformedDrift y) *
        (metricMobilityCoordinate x - metricMobilityCoordinate y) := by
  have hA : 0 < 1 + 2 * x := by positivity
  have hB : 0 < 1 + 2 * y := by positivity
  have hC : 0 < 1 + x + y := by linarith
  have hA3 : 1 + 2 * x ≤ 3 := by linarith
  have hB3 : 1 + 2 * y ≤ 3 := by linarith
  have hC3 : 1 + x + y ≤ 3 := by linarith
  have hAB : (1 + 2 * x) * (1 + 2 * y) ≤ 9 := by
    calc
      (1 + 2 * x) * (1 + 2 * y) ≤ 3 * (1 + 2 * y) :=
        mul_le_mul_of_nonneg_right hA3 hB.le
      _ ≤ 3 * 3 := mul_le_mul_of_nonneg_left hB3 (by norm_num)
      _ = 9 := by norm_num
  have hABC : (1 + 2 * x) * (1 + 2 * y) * (1 + x + y) ≤ 27 := by
    calc
      (1 + 2 * x) * (1 + 2 * y) * (1 + x + y) ≤ 9 * (1 + x + y) :=
        mul_le_mul_of_nonneg_right hAB hC.le
      _ ≤ 9 * 3 := mul_le_mul_of_nonneg_left hC3 (by norm_num)
      _ = 27 := by norm_num
  have hratio : (1 + x + y) / 27 ≤ 1 / ((1 + 2 * x) * (1 + 2 * y)) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 27) (mul_pos hA hB)]
    calc
      (1 + x + y) * ((1 + 2 * x) * (1 + 2 * y)) =
          (1 + 2 * x) * (1 + 2 * y) * (1 + x + y) := by ring
      _ ≤ 27 := hABC
      _ = 1 * 27 := by norm_num
  have hcoord : metricMobilityCoordinate x - metricMobilityCoordinate y =
      (x - y) * (1 + x + y) := by
    unfold metricMobilityCoordinate
    ring
  have hdrift : metricMobilityTransformedDrift x -
      metricMobilityTransformedDrift y =
      (x - y) / ((1 + 2 * x) * (1 + 2 * y)) := by
    unfold metricMobilityTransformedDrift
    field_simp [ne_of_gt hA, ne_of_gt hB]
    ring
  rw [hcoord, hdrift]
  have hscale := mul_le_mul_of_nonneg_left hratio (sq_nonneg (x - y))
  have hCnonneg : 0 ≤ 1 + x + y := le_of_lt hC
  have hscaled := mul_le_mul_of_nonneg_right hscale hCnonneg
  calc
    (1 / 27 : ℝ) * ((x - y) * (1 + x + y)) ^ 2 =
        (x - y) ^ 2 * ((1 + x + y) / 27) * (1 + x + y) := by ring
    _ ≤ (x - y) ^ 2 * (1 / ((1 + 2 * x) * (1 + 2 * y))) *
        (1 + x + y) := hscaled
    _ = ((x - y) / ((1 + 2 * x) * (1 + 2 * y))) *
        ((x - y) * (1 + x + y)) := by
      field_simp [ne_of_gt (mul_pos hA hB)]
/-- 適合座標は `[0,1]` 上で単射なので、その押し戻し距離は真正の距離になる。 -/
structure MetricMobilityState where
  value : ℝ
  property : value ∈ Set.Icc 0 1
instance : Nonempty MetricMobilityState :=
  ⟨⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩⟩
theorem metricMobilityCoordinate_injective_on_state :
    Function.Injective (fun x : MetricMobilityState =>
      metricMobilityCoordinate x.value) := by
  intro x y hxy
  cases x with
  | mk xv xprop =>
    cases y with
    | mk yv yprop =>
      simp only [MetricMobilityState.mk.injEq]
      have hfactor : 0 < 1 + xv + yv := by linarith [xprop.1, yprop.1]
      have hprod : (xv - yv) * (1 + xv + yv) = 0 := by
        have hdiff : metricMobilityCoordinate xv -
            metricMobilityCoordinate yv =
            (xv - yv) * (1 + xv + yv) := by
          unfold metricMobilityCoordinate
          ring
        rw [← hdiff]
        have hxy' : metricMobilityCoordinate xv = metricMobilityCoordinate yv := by
          simpa only using hxy
        rw [hxy']
        ring
      rcases mul_eq_zero.mp hprod with hxy' | hfactor'
      · exact sub_eq_zero.mp hxy'
      · linarith
/-- `[0,1]` 上の状態型に、適合座標が誘導する距離を入れる。 -/
noncomputable instance metricMobilityStateMetric : MetricSpace MetricMobilityState :=
  MetricSpace.induced (fun x => metricMobilityCoordinate x.value)
    metricMobilityCoordinate_injective_on_state inferInstance
/-- 適合距離は通常の実数距離を下から抑える。 -/
theorem metricMobilityState_value_dist_le_dist
    (x y : MetricMobilityState) :
    dist x.value y.value ≤ dist x y := by
  have hfactor : 1 ≤ 1 + x.value + y.value := by
    linarith [x.property.1, y.property.1]
  have hcoord : metricMobilityCoordinate x.value -
      metricMobilityCoordinate y.value =
      (x.value - y.value) * (1 + x.value + y.value) := by
    unfold metricMobilityCoordinate
    ring
  change |x.value - y.value| ≤
    |metricMobilityCoordinate x.value - metricMobilityCoordinate y.value|
  rw [hcoord, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + x.value + y.value)]
  nlinarith [abs_nonneg (x.value - y.value)]
/-- 適合距離で見た状態空間 `[0,1]` は完備。
座標距離が通常距離を支配するため、Cauchy列は実数座標で収束し、閉区間内に極限をもつ。 -/
noncomputable instance metricMobilityState_complete : CompleteSpace MetricMobilityState := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have huValue : CauchySeq (fun n => (u n).value) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    exact lt_of_le_of_lt
      (metricMobilityState_value_dist_le_dist (u m) (u n)) (hN m hm n hn)
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete huValue
  have hvMem : v ∈ Set.Icc 0 1 :=
    isClosed_Icc.mem_of_tendsto hv (Filter.Eventually.of_forall fun n => (u n).property)
  let x : MetricMobilityState := ⟨v, hvMem⟩
  have hcoordTendsto :
      Filter.Tendsto (fun n => metricMobilityCoordinate (u n).value)
        Filter.atTop (nhds (metricMobilityCoordinate v)) := by
    exact (metricMobilityCoordinate_hasDerivAt v).continuousAt.tendsto.comp hv
  refine ⟨x, ?_⟩
  rw [Metric.tendsto_atTop]
  change ∀ ε > 0, ∃ N, ∀ n ≥ N,
    dist (metricMobilityCoordinate (u n).value)
      (metricMobilityCoordinate v) < ε
  exact Metric.tendsto_atTop.mp hcoordTendsto
/-- 線形化された系の解を、適合座標内の指数流を逆変換して明示的に定義する。 -/
noncomputable def metricMobilityExactTrajectory
    (x : MetricMobilityState) (t : ℝ) : ℝ :=
  (Real.sqrt (1 + 4 * Real.exp (-t) * metricMobilityCoordinate x.value) - 1) / 2
/-- 適合座標 `x+x²` の逆写像。 -/
noncomputable def metricMobilityCoordinateInverse (z : ℝ) : ℝ :=
  (Real.sqrt (1 + 4 * z) - 1) / 2
/-- `[0,2]` では逆座標が再び `[0,1]` に入り、座標写像との合成は恒等写像。 -/
theorem metricMobilityCoordinateInverse_mem {z : ℝ} (hz : z ∈ Set.Icc 0 2) :
    metricMobilityCoordinateInverse z ∈ Set.Icc 0 1 := by
  have hzlo : 1 ≤ 1 + 4 * z := by linarith [hz.1]
  have hzhi : 1 + 4 * z ≤ 9 := by linarith [hz.2]
  have hrootlo : 1 ≤ Real.sqrt (1 + 4 * z) := by
    apply (Real.le_sqrt (by norm_num) (by linarith [hzlo])).2
    nlinarith [hzlo]
  have hroothi : Real.sqrt (1 + 4 * z) ≤ 3 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [hzhi]⟩
  unfold metricMobilityCoordinateInverse
  constructor <;> nlinarith
theorem metricMobilityCoordinate_inverse_right {z : ℝ} (hz : z ∈ Set.Icc 0 2) :
    metricMobilityCoordinate (metricMobilityCoordinateInverse z) = z := by
  have hsqrt := Real.sq_sqrt (show 0 ≤ 1 + 4 * z by linarith [hz.1])
  unfold metricMobilityCoordinate metricMobilityCoordinateInverse
  nlinarith [hsqrt]
/-- `[0,1]` の任意の状態の適合座標は `[0,2]` にある。 -/
theorem metricMobilityCoordinate_mem (x : MetricMobilityState) :
    metricMobilityCoordinate x.value ∈ Set.Icc 0 2 := by
  have hx := x.property
  constructor
  · unfold metricMobilityCoordinate
    nlinarith [sq_nonneg x.value, hx.1]
  · unfold metricMobilityCoordinate
    have hxSq : x.value ^ 2 ≤ x.value := by
      have hmul := mul_le_mul_of_nonneg_left hx.2 hx.1
      nlinarith
    nlinarith [hxSq, hx.2]
/-- 明示解の適合座標は初期座標の `exp(-t)` 倍。 -/
theorem metricMobilityExactTrajectory_coordinate
    (x : MetricMobilityState) (t : ℝ) :
    metricMobilityCoordinate (metricMobilityExactTrajectory x t) =
      Real.exp (-t) * metricMobilityCoordinate x.value := by
  have hxcoord : 0 ≤ x.value + x.value ^ 2 := by
    nlinarith [x.property.1, sq_nonneg x.value]
  have hz : 0 ≤ Real.exp (-t) * metricMobilityCoordinate x.value :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hxcoord
  have hsqrt := Real.sq_sqrt (show 0 ≤
    1 + 4 * Real.exp (-t) * metricMobilityCoordinate x.value by positivity)
  unfold metricMobilityExactTrajectory metricMobilityCoordinate
  unfold metricMobilityCoordinate at hsqrt
  nlinarith [hsqrt]
/-- 明示解は時刻0に初期状態を取る。 -/
theorem metricMobilityExactTrajectory_start (x : MetricMobilityState) :
    metricMobilityExactTrajectory x 0 = x.value := by
  have hx := x.property
  simp only [metricMobilityExactTrajectory, neg_zero, Real.exp_zero]
  unfold metricMobilityCoordinate
  rw [show 1 + 4 * 1 * (x.value + x.value ^ 2) =
    (1 + 2 * x.value) ^ 2 by ring]
  rw [Real.sqrt_sq (by linarith [hx.1])]
  ring
/-- 非負時刻では明示解は初期値と0の間に留まり、したがって `[0,1]` 内にある。 -/
theorem metricMobilityExactTrajectory_stays
    (x : MetricMobilityState) {t : ℝ} (ht : 0 ≤ t) :
    metricMobilityExactTrajectory x t ∈ Set.Icc 0 1 := by
  have hx := x.property
  have hcoordx : 0 ≤ metricMobilityCoordinate x.value := by
    unfold metricMobilityCoordinate
    nlinarith [sq_nonneg x.value, hx.1]
  have hexp0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hexp1 : Real.exp (-t) ≤ 1 := (Real.exp_le_one_iff).2 (by linarith)
  have hcoordle : metricMobilityCoordinate x.value ≤ 2 := by
    have hxSq : x.value ^ 2 ≤ x.value := by
      nlinarith [mul_le_mul_of_nonneg_left hx.2 hx.1]
    unfold metricMobilityCoordinate
    nlinarith [hxSq, hx.2]
  have hradge : 1 ≤ 1 + 4 * Real.exp (-t) * metricMobilityCoordinate x.value := by
    have hmul : 0 ≤ Real.exp (-t) * metricMobilityCoordinate x.value :=
      mul_nonneg hexp0.le hcoordx
    nlinarith [hmul]
  have hradle : 1 + 4 * Real.exp (-t) * metricMobilityCoordinate x.value ≤ 9 := by
    calc
      1 + 4 * Real.exp (-t) * metricMobilityCoordinate x.value ≤
          1 + 4 * metricMobilityCoordinate x.value := by
            nlinarith [mul_le_mul_of_nonneg_right hexp1 hcoordx]
      _ ≤ 9 := by nlinarith
  have hrootlo : 1 ≤ Real.sqrt
      (1 + 4 * Real.exp (-t) * metricMobilityCoordinate x.value) := by
    apply (Real.le_sqrt (by norm_num) (by linarith [hradge])).2
    nlinarith [hradge]
  have hroothi : Real.sqrt
      (1 + 4 * Real.exp (-t) * metricMobilityCoordinate x.value) ≤ 3 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [hradle]⟩
  unfold metricMobilityExactTrajectory
  constructor <;> nlinarith
/-- 明示解の適合座標は単位率の線形安定系に従う。 -/
theorem metricMobilityExactTrajectory_coordinate_hasDerivAt
    (x : MetricMobilityState) (t : ℝ) :
    HasDerivAt (fun s => metricMobilityCoordinate
      (metricMobilityExactTrajectory x s))
      (-metricMobilityCoordinate (metricMobilityExactTrajectory x t)) t := by
  let c : ℝ := metricMobilityCoordinate x.value
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t (by
      convert (hasDerivAt_id t).neg using 1
      funext s
      rfl) using 1
    · funext s
      rfl
    · ring
  have heq : (fun s => metricMobilityCoordinate
      (metricMobilityExactTrajectory x s)) =
      (fun s => Real.exp (-s) * c) := by
    funext s
    simpa [c] using metricMobilityExactTrajectory_coordinate x s
  rw [heq]
  convert hexp.const_mul c using 1
  · funext s
    ring
  · rw [metricMobilityExactTrajectory_coordinate]
    dsimp [c]
    ring
/-- 履歴 r をポテンシャルの谷の中心とした適合座標上の明示流。
座標では `z' = -(z - φ(r))` であり、逆座標に戻した状態依存勾配流である。 -/
noncomputable def metricMobilityHistoryFlow
    (r x : MetricMobilityState) (t : ℝ) : ℝ :=
  metricMobilityCoordinateInverse
    (metricMobilityCoordinate r.value + Real.exp (-t) *
      (metricMobilityCoordinate x.value - metricMobilityCoordinate r.value))
theorem metricMobilityHistoryFlow_coordinate_mem
    (r x : MetricMobilityState) {t : ℝ} (ht : 0 ≤ t) :
    metricMobilityCoordinate r.value + Real.exp (-t) *
      (metricMobilityCoordinate x.value - metricMobilityCoordinate r.value) ∈
        Set.Icc 0 2 := by
  have hr := metricMobilityCoordinate_mem r
  have hx := metricMobilityCoordinate_mem x
  have he0 : 0 ≤ Real.exp (-t) := le_of_lt (Real.exp_pos _)
  have he1 : Real.exp (-t) ≤ 1 := (Real.exp_le_one_iff).2 (by linarith)
  have hrew : metricMobilityCoordinate r.value + Real.exp (-t) *
      (metricMobilityCoordinate x.value - metricMobilityCoordinate r.value) =
      (1 - Real.exp (-t)) * metricMobilityCoordinate r.value +
        Real.exp (-t) * metricMobilityCoordinate x.value := by ring
  constructor
  · calc
      0 ≤ (1 - Real.exp (-t)) * metricMobilityCoordinate r.value +
          Real.exp (-t) * metricMobilityCoordinate x.value :=
        add_nonneg (mul_nonneg (by linarith) hr.1) (mul_nonneg he0 hx.1)
      _ = _ := hrew.symm
  · calc
      metricMobilityCoordinate r.value + Real.exp (-t) *
          (metricMobilityCoordinate x.value - metricMobilityCoordinate r.value) =
          (1 - Real.exp (-t)) * metricMobilityCoordinate r.value +
            Real.exp (-t) * metricMobilityCoordinate x.value := hrew
      _ ≤ (1 - Real.exp (-t)) * 2 + Real.exp (-t) * 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hr.2 (by linarith))
          (mul_le_mul_of_nonneg_left hx.2 he0)
      _ = 2 := by ring
/-- 各履歴の中心点を固定する明示的な勾配流時間写像。 -/
noncomputable def metricMobilityHistoryStep
    (r : MetricMobilityState) (T : ℝ) (hT : 0 ≤ T)
    (x : MetricMobilityState) : MetricMobilityState :=
  ⟨metricMobilityHistoryFlow r x T,
    metricMobilityCoordinateInverse_mem (metricMobilityHistoryFlow_coordinate_mem r x hT)⟩
theorem metricMobilityHistoryStep_coordinate
    (r x : MetricMobilityState) (T : ℝ) (hT : 0 ≤ T) :
    metricMobilityCoordinate (metricMobilityHistoryStep r T hT x).value =
      metricMobilityCoordinate r.value + Real.exp (-T) *
        (metricMobilityCoordinate x.value - metricMobilityCoordinate r.value) := by
  exact metricMobilityCoordinate_inverse_right
    (metricMobilityHistoryFlow_coordinate_mem r x hT)
theorem metricMobilityHistoryStep_fixes_center
    (r : MetricMobilityState) (T : ℝ) (hT : 0 ≤ T) :
    metricMobilityHistoryStep r T hT r = r := by
  apply metricMobilityCoordinate_injective_on_state
  change metricMobilityCoordinate (metricMobilityHistoryStep r T hT r).value =
    metricMobilityCoordinate r.value
  rw [metricMobilityHistoryStep_coordinate]
  ring
/-- 履歴中心が固定された座標アフィン写像なので、各履歴の更新は適合距離で
縮小率 `exp(-T)` の `ContractingWith` になる。 -/
theorem metricMobilityHistoryStep_contracting
    (r : MetricMobilityState) (T : ℝ) (hT : 0 < T) :
    ContractingWith ⟨Real.exp (-T), le_of_lt (Real.exp_pos _)⟩
      (metricMobilityHistoryStep r T (le_of_lt hT)) := by
  letI : MetricSpace MetricMobilityState := metricMobilityStateMetric
  have hK : (⟨Real.exp (-T), le_of_lt (Real.exp_pos _)⟩ : NNReal) < 1 := by
    change Real.exp (-T) < 1
    rw [Real.exp_lt_one_iff]
    linarith
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  change dist (metricMobilityCoordinate
      (metricMobilityHistoryStep r T (le_of_lt hT) x).value)
      (metricMobilityCoordinate
        (metricMobilityHistoryStep r T (le_of_lt hT) y).value) ≤
    Real.exp (-T) * dist (metricMobilityCoordinate x.value)
      (metricMobilityCoordinate y.value)
  rw [metricMobilityHistoryStep_coordinate, metricMobilityHistoryStep_coordinate]
  change |metricMobilityCoordinate r.value + Real.exp (-T) *
      (metricMobilityCoordinate x.value - metricMobilityCoordinate r.value) -
      (metricMobilityCoordinate r.value + Real.exp (-T) *
        (metricMobilityCoordinate y.value - metricMobilityCoordinate r.value))| ≤
    Real.exp (-T) * |metricMobilityCoordinate x.value - metricMobilityCoordinate y.value|
  have hdiff : metricMobilityCoordinate r.value + Real.exp (-T) *
        (metricMobilityCoordinate x.value - metricMobilityCoordinate r.value) -
      (metricMobilityCoordinate r.value + Real.exp (-T) *
        (metricMobilityCoordinate y.value - metricMobilityCoordinate r.value)) =
      Real.exp (-T) * (metricMobilityCoordinate x.value -
        metricMobilityCoordinate y.value) := by ring
  rw [hdiff, abs_mul, abs_of_pos (Real.exp_pos _)]
/-- 明示軌道は適合距離で任意の二初期値間を `exp(-t)` で縮める。 -/
theorem metricMobilityExactTrajectory_pairwise_contraction
    (x y : MetricMobilityState) (T : ℝ) :
    ∀ t ∈ Set.Icc 0 T,
      dist (metricMobilityCoordinate (metricMobilityExactTrajectory x t))
        (metricMobilityCoordinate (metricMobilityExactTrajectory y t)) ≤
        Real.exp (-t) * dist (metricMobilityCoordinate x.value)
          (metricMobilityCoordinate y.value) := by
  have hflow := coordinateFlow_dist_contracting (Set.Icc 0 1)
    metricMobilityCoordinate metricMobilityCoordinate (1 : ℝ) 0 T (by norm_num)
    (by
      intro u hu v hv
      nlinarith)
    (metricMobilityExactTrajectory x) (metricMobilityExactTrajectory y)
    (fun t _ => metricMobilityExactTrajectory_coordinate_hasDerivAt x t)
    (fun t _ => metricMobilityExactTrajectory_coordinate_hasDerivAt y t)
    (fun t ht => metricMobilityExactTrajectory_stays x (by linarith [ht.1]))
    (fun t ht => metricMobilityExactTrajectory_stays y (by linarith [ht.1]))
  intro t ht
  have hstartDist :
      dist (metricMobilityCoordinate (metricMobilityExactTrajectory x 0))
        (metricMobilityCoordinate (metricMobilityExactTrajectory y 0)) =
      dist (metricMobilityCoordinate x.value) (metricMobilityCoordinate y.value) := by
    rw [metricMobilityExactTrajectory_start, metricMobilityExactTrajectory_start]
  have hexp : Real.exp (-1 * (t - 0)) = Real.exp (-t) := by
    congr 1 <;> ring
  calc
    dist (metricMobilityCoordinate (metricMobilityExactTrajectory x t))
        (metricMobilityCoordinate (metricMobilityExactTrajectory y t)) ≤
      Real.exp (-1 * (t - 0)) *
        dist (metricMobilityCoordinate (metricMobilityExactTrajectory x 0))
          (metricMobilityCoordinate (metricMobilityExactTrajectory y 0)) := hflow t ht
    _ = Real.exp (-t) * dist (metricMobilityCoordinate x.value)
        (metricMobilityCoordinate y.value) := by rw [hexp, hstartDist]
/-- この具体的な状態依存流の時間写像は適合距離のもとで縮小写像である。 -/
theorem metricMobilityExact_flow_timeMap_contracting
    (T : ℝ) (hT : 0 < T) :
    ContractingWith ⟨Real.exp (-T), le_of_lt (Real.exp_pos _)⟩
      (fun x : MetricMobilityState =>
        (⟨metricMobilityExactTrajectory x T,
          metricMobilityExactTrajectory_stays x (le_of_lt hT)⟩ :
            MetricMobilityState)) := by
  letI : MetricSpace MetricMobilityState := metricMobilityStateMetric
  have hK : (⟨Real.exp (-T), le_of_lt (Real.exp_pos _)⟩ : NNReal) < 1 := by
    change Real.exp (-T) < 1
    rw [Real.exp_lt_one_iff]
    linarith
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hdistT :
      dist (⟨metricMobilityExactTrajectory x T,
        metricMobilityExactTrajectory_stays x (le_of_lt hT)⟩ : MetricMobilityState)
        (⟨metricMobilityExactTrajectory y T,
          metricMobilityExactTrajectory_stays y (le_of_lt hT)⟩ : MetricMobilityState) =
      dist (metricMobilityCoordinate (metricMobilityExactTrajectory x T))
        (metricMobilityCoordinate (metricMobilityExactTrajectory y T)) := rfl
  have hdist0 : dist x y =
      dist (metricMobilityCoordinate x.value) (metricMobilityCoordinate y.value) := rfl
  rw [hdistT, hdist0]
  have hflow := metricMobilityExactTrajectory_pairwise_contraction x y T T
    ⟨le_of_lt hT, le_rfl⟩
  calc
    dist (metricMobilityCoordinate (metricMobilityExactTrajectory x T))
        (metricMobilityCoordinate (metricMobilityExactTrajectory y T)) ≤
      Real.exp (-T) * dist (metricMobilityCoordinate x.value)
        (metricMobilityCoordinate y.value) := hflow
    _ = (↑(⟨Real.exp (-T), le_of_lt (Real.exp_pos _)⟩ : NNReal) : ℝ) *
        dist (metricMobilityCoordinate x.value) (metricMobilityCoordinate y.value) := by
          exact congrArg (fun r : ℝ => r *
            dist (metricMobilityCoordinate x.value) (metricMobilityCoordinate y.value))
            (NNReal.coe_mk _ _).symm
/-- 状態依存移動度 `A(x)=(1+2x)⁻²` の流れは、区間 `[0,1]` に留まる軌道同士で
適合座標 `φ(x)=x+x²` の距離を率 `1/27` で縮める。原座標の距離縮小は主張しない。 -/
theorem metricMobility_flow_coordinate_dist_contracting
    (f g : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ t ∈ Set.Icc a b,
      HasDerivAt f (metricMobilityVectorField (f t)) t)
    (hg : ∀ t ∈ Set.Icc a b,
      HasDerivAt g (metricMobilityVectorField (g t)) t)
    (hfU : ∀ t ∈ Set.Icc a b, f t ∈ Set.Icc 0 1)
    (hgU : ∀ t ∈ Set.Icc a b, g t ∈ Set.Icc 0 1) :
    ∀ t ∈ Set.Icc a b,
      dist (metricMobilityCoordinate (f t)) (metricMobilityCoordinate (g t)) ≤
        Real.exp (-(1 / 27 : ℝ) * (t - a)) *
          dist (metricMobilityCoordinate (f a)) (metricMobilityCoordinate (g a)) := by
  apply coordinateFlow_dist_contracting (Set.Icc 0 1)
    metricMobilityCoordinate metricMobilityTransformedDrift (1 / 27) a b
    (by norm_num) ?_ f g ?_ ?_ hfU hgU
  · intro x hx y hy
    exact metricMobilityTransformedDrift_strongMonotone hx.1 hx.2 hy.1 hy.2
  · intro t ht
    exact metricMobility_coordinateFlow_hasDerivAt f t (hf t ht) (hfU t ht).1
  · intro t ht
    exact metricMobility_coordinateFlow_hasDerivAt g t (hg t ht) (hgU t ht).1
/-- 状態依存移動度のこの一次元モデルでは、座標誘導距離を使えば時間 `T>0` の
流れ写像が `ContractingWith` になる。定理21の勾配流からBanach条件へ接続する
具体例だが、[0,1] 不変性、全初期値の軌道存在、そして定理16の層別更新則との
同定はいずれも追加仮定である。 -/
theorem metricMobility_flow_timeMap_contracting
    (T : ℝ) (hT : 0 < T)
    (trajectory : MetricMobilityState → ℝ → ℝ)
    (hderiv : ∀ x t, t ∈ Set.Icc 0 T →
      HasDerivAt (trajectory x) (metricMobilityVectorField (trajectory x t)) t)
    (hstay : ∀ x t, t ∈ Set.Icc 0 T → trajectory x t ∈ Set.Icc 0 1)
    (hstart : ∀ x, trajectory x 0 = x.value) :
    ContractingWith ⟨Real.exp (-(1 / 27 : ℝ) * T),
      le_of_lt (Real.exp_pos _)⟩
      (fun x : MetricMobilityState =>
        (⟨trajectory x T, hstay x T ⟨le_of_lt hT, le_rfl⟩⟩ :
          MetricMobilityState)) := by
  letI : MetricSpace MetricMobilityState := metricMobilityStateMetric
  have hK : (⟨Real.exp (-(1 / 27 : ℝ) * T),
      le_of_lt (Real.exp_pos _)⟩ : NNReal) < 1 := by
    change Real.exp (-(1 / 27 : ℝ) * T) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hflow := metricMobility_flow_coordinate_dist_contracting
    (trajectory x) (trajectory y) 0 T
    (fun t ht => hderiv x t ht) (fun t ht => hderiv y t ht)
    (fun t ht => hstay x t ht) (fun t ht => hstay y t ht)
    T ⟨le_of_lt hT, le_rfl⟩
  have hdistT :
      dist (⟨trajectory x T, hstay x T ⟨le_of_lt hT, le_rfl⟩⟩ :
        MetricMobilityState)
        (⟨trajectory y T, hstay y T ⟨le_of_lt hT, le_rfl⟩⟩ :
        MetricMobilityState) =
      dist (metricMobilityCoordinate (trajectory x T))
        (metricMobilityCoordinate (trajectory y T)) := rfl
  have hdist0 : dist x y =
      dist (metricMobilityCoordinate x.value) (metricMobilityCoordinate y.value) := rfl
  rw [hdistT, hdist0]
  calc
    dist (metricMobilityCoordinate (trajectory x T))
        (metricMobilityCoordinate (trajectory y T)) ≤
      Real.exp (-(1 / 27 : ℝ) * T) *
        dist (metricMobilityCoordinate x.value) (metricMobilityCoordinate y.value) := by
          simpa only [hstart x, hstart y, sub_zero] using hflow
    _ = (↑(⟨Real.exp (-(1 / 27 : ℝ) * T),
        le_of_lt (Real.exp_pos _)⟩ : NNReal) : ℝ) *
        dist (metricMobilityCoordinate x.value) (metricMobilityCoordinate y.value) := by
          exact congrArg (fun r : ℝ => r *
            dist (metricMobilityCoordinate x.value) (metricMobilityCoordinate y.value))
            (NNReal.coe_mk _ _).symm
/-- 線形化状態依存流の時間写像は平衡点0を固定する。 -/
theorem metricMobilityExact_flow_timeMap_fixes_zero (T : ℝ) (hT : 0 ≤ T) :
    (fun x : MetricMobilityState =>
      (⟨metricMobilityExactTrajectory x T,
        metricMobilityExactTrajectory_stays x hT⟩ : MetricMobilityState))
      ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ =
    ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ := by
  simp [metricMobilityExactTrajectory, metricMobilityCoordinate]
/-- 明示的ODEモデルのBanach固定点は、ポテンシャルの平衡点0に一致する。 -/
theorem metricMobilityExact_flow_fixedPoint_eq_zero (T : ℝ) (hT : 0 < T) :
    ContractingWith.fixedPoint
      (fun x : MetricMobilityState =>
        (⟨metricMobilityExactTrajectory x T,
          metricMobilityExactTrajectory_stays x (le_of_lt hT)⟩ :
            MetricMobilityState))
      (metricMobilityExact_flow_timeMap_contracting T hT) =
        ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ := by
  let f : MetricMobilityState → MetricMobilityState := fun x =>
    ⟨metricMobilityExactTrajectory x T,
      metricMobilityExactTrajectory_stays x (le_of_lt hT)⟩
  have hc : ContractingWith ⟨Real.exp (-T), le_of_lt (Real.exp_pos _)⟩ f := by
    exact metricMobilityExact_flow_timeMap_contracting T hT
  let zero : MetricMobilityState :=
    ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩
  change ContractingWith.fixedPoint f hc = zero
  have hzero : IsFixedPt f zero := by
    change f zero = zero
    exact metricMobilityExact_flow_timeMap_fixes_zero T (le_of_lt hT)
  exact hc.fixedPoint_unique' hc.fixedPoint_isFixedPt hzero
/-- 完備な適合距離のもとで、この状態依存流の時間写像にはBanach固定点が一意に存在する。
大域軌道の存在・区間不変性は仮定し、定理16の層別作用素との同定は行っていない。 -/
theorem metricMobility_flow_timeMap_hasUniqueFixedPoint
    (T : ℝ) (hT : 0 < T)
    (trajectory : MetricMobilityState → ℝ → ℝ)
    (hderiv : ∀ x t, t ∈ Set.Icc 0 T →
      HasDerivAt (trajectory x) (metricMobilityVectorField (trajectory x t)) t)
    (hstay : ∀ x t, t ∈ Set.Icc 0 T → trajectory x t ∈ Set.Icc 0 1)
    (hstart : ∀ x, trajectory x 0 = x.value) :
    HasUniqueFixedPoint
      (fun x : MetricMobilityState =>
        (⟨trajectory x T, hstay x T ⟨le_of_lt hT, le_rfl⟩⟩ :
          MetricMobilityState)) := by
  exact hasUniqueFixedPoint_of_contraction
    (metricMobility_flow_timeMap_contracting T hT trajectory hderiv hstay hstart)
/-- 履歴別時間写像を一般のBanach固定点族構成へ入れ、25-A(1)に対応する
中心分離から定理25第1結論を得る。 -/
theorem metricMobilityHistoryFamily_theorem25_firstConclusion
    (T : ℝ) (hT : 0 < T) {r₁ r₂ : MetricMobilityState} (hcenters : r₁ ≠ r₂) :
    ¬ ∃ x : MetricMobilityState,
      metricMobilityHistoryStep r₁ T (le_of_lt hT) x = x ∧
      metricMobilityHistoryStep r₂ T (le_of_lt hT) x = x := by
  let carrier : MetricMobilityState → Set MetricMobilityState := fun _ => Set.univ
  let feedback : ∀ r, {x : MetricMobilityState // x ∈ carrier r} →
      {x : MetricMobilityState // x ∈ carrier r} := fun r x =>
    ⟨metricMobilityHistoryStep r T (le_of_lt hT) x.1, Set.mem_univ _⟩
  let K : MetricMobilityState → NNReal := fun _ =>
    ⟨Real.exp (-T), le_of_lt (Real.exp_pos _)⟩
  have hnonempty : ∀ r, (carrier r).Nonempty := fun _ => Set.univ_nonempty
  have hcomplete : ∀ r, IsComplete (carrier r) := fun _ => isComplete_univ
  have hcontract : ∀ r, ContractingWith (K r) (feedback r) := by
    intro r
    have hbase := metricMobilityHistoryStep_contracting r T hT
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · simpa [K] using hbase.1
    · change dist (metricMobilityHistoryStep r T (le_of_lt hT) x.1)
        (metricMobilityHistoryStep r T (le_of_lt hT) y.1) ≤
        (K r : ℝ) * dist x.1 y.1
      simpa [K, Subtype.dist_eq] using hbase.2.dist_le_mul x.1 y.1
  let F := historyFixedPointsOfContractions carrier feedback K hnonempty hcomplete hcontract
  have hcenter (r : MetricMobilityState) : (F.fixedPoint r).1 = r := by
    let cr : {x : MetricMobilityState // x ∈ carrier r} := ⟨r, by simp [carrier]⟩
    have hfix : feedback r cr = cr := by
      apply Subtype.ext
      exact metricMobilityHistoryStep_fixes_center r T (le_of_lt hT)
    have heq := F.unique r cr hfix
    exact (congrArg Subtype.val heq).symm
  have hsep : (F.fixedPoint r₁).1 ≠ (F.fixedPoint r₂).1 := by
    intro h
    apply hcenters
    calc
      r₁ = (F.fixedPoint r₁).1 := (hcenter r₁).symm
      _ = (F.fixedPoint r₂).1 := h
      _ = r₂ := hcenter r₂
  have hno := theorem25_firstConclusion_of_historyContractions
    carrier feedback K hnonempty hcomplete hcontract hsep
  intro ⟨x, hx₁, hx₂⟩
  let sx₁ : {y : MetricMobilityState // y ∈ carrier r₁} := ⟨x, by simp [carrier]⟩
  let sx₂ : {y : MetricMobilityState // y ∈ carrier r₂} := ⟨x, by simp [carrier]⟩
  have hfix₁ : feedback r₁ sx₁ = sx₁ := by
    apply Subtype.ext
    exact hx₁
  have hfix₂ : feedback r₂ sx₂ = sx₂ := by
    apply Subtype.ext
    exact hx₂
  exact hno ⟨x, sx₁.property, sx₂.property, hfix₁, hfix₂⟩


/-- 状態依存移動度が強凸性だけから縮小性を与えないことを示す一次元監査例。
`V(x)=x²/2` と `A(x)=1/(1+100x²)` に対するベクトル場 `-A(x)V'(x)`。 -/
noncomputable def variableMobilityWitness (x : ℝ) : ℝ := 1 / (1 + 100 * x ^ 2)

noncomputable def variableMobilityVectorField (x : ℝ) : ℝ :=
  -(x / (1 + 100 * x ^ 2))

noncomputable def variableMobilityPotential (x : ℝ) : ℝ := x ^ 2 / 2

/-- 二次ポテンシャルは任意の領域上で強凸定数1をもつ。 -/
theorem variableMobilityPotential_stronglyConvex (U : Set ℝ) :
    Tomabechi.Theorem21.StronglyConvexOn U variableMobilityPotential
      variableMobilityGradient 1 := by
  intro x hx y hy
  have hnorm : ‖y - x‖ ^ 2 = (y - x) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm, Real.inner_apply]
  dsimp [variableMobilityPotential, variableMobilityGradient]
  nlinarith

/-- この状態依存移動度のベクトル場の導関数。 -/
theorem variableMobilityVectorField_hasDerivAt (x : ℝ) :
    HasDerivAt variableMobilityVectorField
      ((100 * x ^ 2 - 1) / (1 + 100 * x ^ 2) ^ 2) x := by
  have hden : 1 + 100 * x ^ 2 ≠ 0 := by positivity
  have hdenDeriv : HasDerivAt (fun y : ℝ => 1 + 100 * y ^ 2)
      (200 * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul 100).add_const 1 using 1
    · funext y
      simp [pow_two]
      ring
    · simp only [id_eq]
      ring
  have hquot := (hasDerivAt_id x).div hdenDeriv hden
  change HasDerivAt (fun y : ℝ => -(y / (1 + 100 * y ^ 2)))
    ((100 * x ^ 2 - 1) / (1 + 100 * x ^ 2) ^ 2) x
  convert hquot.neg using 1
  · funext y
    simp [div_eq_mul_inv]
  · simp only [id_eq]
    field_simp
    ring

/-- 不変区間の右側では、強凸二次ポテンシャルでも状態依存移動度の
閉ループベクトル場は局所的に距離を拡大する方向を持つ。 -/
theorem variableMobilityVectorField_deriv_pos
    {x : ℝ} (hx : (1 / 10 : ℝ) < x) :
    0 < deriv variableMobilityVectorField x := by
  rw [(variableMobilityVectorField_hasDerivAt x).deriv]
  have hnum : 0 < 100 * x ^ 2 - 1 := by
    nlinarith [sq_nonneg (x - 1 / 10)]
  positivity

/-- `[-3/10,3/10]` 上で移動度は一様に10分の1以上。 -/
theorem variableMobilityWitness_lower_bound
    {x : ℝ} (hlo : -(3 / 10 : ℝ) ≤ x) (hhi : x ≤ 3 / 10) :
    (1 / 10 : ℝ) ≤ variableMobilityWitness x := by
  have hxSq : x ^ 2 ≤ (3 / 10 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (x - 3 / 10), sq_nonneg (x + 3 / 10)]
  have hden : 0 < 1 + 100 * x ^ 2 := by positivity
  unfold variableMobilityWitness
  rw [le_div_iff₀ hden]
  nlinarith [hxSq]

/-- 閉区間の両端でベクトル場は内向きであり、符号は全域で原点方向。 -/
theorem variableMobilityVectorField_mul_self_nonpos (x : ℝ) :
    x * variableMobilityVectorField x ≤ 0 := by
  unfold variableMobilityVectorField
  have hden : 0 < 1 + 100 * x ^ 2 := by positivity
  calc
    x * -(x / (1 + 100 * x ^ 2)) =
        -(x ^ 2 / (1 + 100 * x ^ 2)) := by
      field_simp [ne_of_gt hden]
    _ ≤ 0 := neg_nonpos.mpr
      (div_nonneg (sq_nonneg x) hden.le)


/-- 有限離散外生空間からの写像は可測であり、その確率法則pushforwardは通常の像測度になる。-/
private theorem theorem25_finiteDomain_aemeasurable
    {U V : Type*} [MeasurableSpace U] [MeasurableSingletonClass U]
    [Finite U] [MeasurableSpace V]
    (μ : MeasureTheory.Measure U) (f : U → V) : AEMeasurable f μ :=
  (measurable_of_finite f).aemeasurable

/-- 生成意味論の型検査用の退化例。外生状態・履歴・候補を定数にし、
実際の `IndepFun` と介入不変なpushforward法則から25-A(2)を満たす。 -/
noncomputable def theorem25_selfProcessSCM_degenerateWitness :
    Theorem25SelfProcessSCM Unit Unit Unit Bool Bool where
  exogenousLaw := ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
  inputHistory := fun _ => ()
  candidateVariable := fun _ => false
  inputHistoryAEMeasurable := measurable_const.aemeasurable
  candidateAEMeasurable := measurable_const.aemeasurable
  baselineEquation := fun _ _ => ((), false)
  intervenedEquation := fun _ _ _ => ((), false)
  baselineAEMeasurable := fun _ => theorem25_finiteDomain_aemeasurable _ _
  intervenedAEMeasurable := fun _ _ => theorem25_finiteDomain_aemeasurable _ _

theorem theorem25_selfProcessSCM_degenerateWitness_satisfies25A2 :
    theorem25_selfProcessSCM_degenerateWitness.toLawModel.Condition25A2 () := by
  apply theorem25_selfProcessSCM_degenerateWitness.condition25A2
  · exact ProbabilityTheory.indepFun_const_left
      (μ := MeasureTheory.Measure.dirac ()) () _
  · intro h s
    apply Subtype.ext
    rfl

/-- 候補変数と出力がともに非定数な有限SCM。候補は外生Boolそのもの、履歴は定数で
独立性は自明だが、観測された自己過程・出力は外生Boolに依存して非定数となる。
介入後の構造式が候補値を無視するため25-A(2)を満たす。これは生成意味論の例であり、
原文の一般認知状態方程式から候補非干渉を導いた結果ではない。 -/
noncomputable def theorem25_selfProcessSCM_nonconstantWitness :
    Theorem25SelfProcessSCM Unit Bool (Unit × Bool) Bool Bool where
  exogenousLaw := ⟨ProbabilityTheory.uniformOn (Set.univ : Set Bool), inferInstance⟩
  inputHistory := fun _ => ()
  candidateVariable := id
  inputHistoryAEMeasurable := measurable_const.aemeasurable
  candidateAEMeasurable := measurable_id.aemeasurable
  baselineEquation := fun _ u => (((), u), u)
  intervenedEquation := fun _ _ u => (((), u), u)
  baselineAEMeasurable := fun _ => theorem25_finiteDomain_aemeasurable _ _
  intervenedAEMeasurable := fun _ _ => theorem25_finiteDomain_aemeasurable _ _

/-- この有限SCMの構造式は、候補の両値を外生空間上に実現し、出力も非定数にする。 -/
theorem theorem25_selfProcessSCM_nonconstantWitness_candidate_surjective :
    Function.Surjective theorem25_selfProcessSCM_nonconstantWitness.candidateVariable := by
  intro s
  exact ⟨s, rfl⟩

theorem theorem25_selfProcessSCM_nonconstantWitness_candidate_true_positive :
    0 < (MeasureTheory.ProbabilityMeasure.toMeasure
      theorem25_selfProcessSCM_nonconstantWitness.exogenousLaw) {true} := by
  change 0 < ProbabilityTheory.uniformOn (Set.univ : Set Bool) ({true} : Set Bool)
  rw [show (Set.univ : Set Bool) = (Finset.univ : Finset Bool) by ext b; simp,
    show ({true} : Set Bool) = ({true} : Finset Bool) by ext b; simp]
  rw [ProbabilityTheory.uniformOn_apply_finset (s := Finset.univ) (t := {true})]
  norm_num

theorem theorem25_selfProcessSCM_nonconstantWitness_output_nonconstant :
    ∃ u v, (theorem25_selfProcessSCM_nonconstantWitness.baselineEquation () u).2 ≠
      (theorem25_selfProcessSCM_nonconstantWitness.baselineEquation () v).2 := by
  exact ⟨false, true, by decide⟩

/-- 候補が実際に変動する有限外生ノイズのもとで、25-A(2)の確率版を満たすSCM例。 -/
theorem theorem25_selfProcessSCM_nonconstantWitness_satisfies25A2 :
    theorem25_selfProcessSCM_nonconstantWitness.toLawModel.Condition25A2 () := by
  apply theorem25_selfProcessSCM_nonconstantWitness.condition25A2
  · exact ProbabilityTheory.indepFun_const_left
      (μ := MeasureTheory.ProbabilityMeasure.toMeasure
        theorem25_selfProcessSCM_nonconstantWitness.exogenousLaw) () _
  · intro h s
    rfl

/-- 自己過程を一つの型付き表現とした有限法則例。Subject=false では
25-A(2)の法則等式が成立し、別subject=true では介入で法則が変わる。
候補独立性フィールドは `True` であり、確率変数の独立性は示していない。 -/
noncomputable def theorem25_selfProcessA2LawToyModel :
    Theorem25SelfProcessLawModel Bool Unit
      (fun _ : Bool => Unit) (fun _ : Bool => Bool) (fun _ : Bool => Bool) :=
  { baselineJointLaw := fun _ _ =>
      ⟨MeasureTheory.Measure.dirac ((), false), inferInstance⟩
    intervenedJointLaw := fun i _ s =>
      ⟨MeasureTheory.Measure.dirac ((), if i then s else false), inferInstance⟩
    candidateIndependentOfInputHistory := fun _ => True }

theorem theorem25_selfProcessA2LawToyModel_satisfies_condition25A2 :
    theorem25_selfProcessA2LawToyModel.Condition25A2 false := by
  constructor
  · trivial
  · intro h s
    cases s <;> rfl

theorem theorem25_selfProcessA2LawToyModel_otherSubjectLawChanges :
    ∃ h s,
      theorem25_selfProcessA2LawToyModel.intervenedJointLaw true h s ≠
        theorem25_selfProcessA2LawToyModel.baselineJointLaw true h := by
  refine ⟨(), true, ?_⟩
  intro heq
  have hmeasure := congrArg MeasureTheory.ProbabilityMeasure.toMeasure heq
  change MeasureTheory.Measure.dirac ((), true) =
    MeasureTheory.Measure.dirac ((), false) at hmeasure
  exact (MeasureTheory.dirac_ne_dirac (by decide)) hmeasure


/-!
## 適合座標・勾配流の具体モデル

以下の例はCoreの一般固定点論証から独立している。後続Coreが使う縮小補題とその依存はCore側に残す。
-/

/-- 適合座標をもつ別の状態依存移動度例。`φ'(x)=1/√A(x)=1+2x` を
満たす `A(x)=(1+2x)⁻²` を使う。 -/
noncomputable def metricMobilityWitness (x : ℝ) : ℝ := 1 / (1 + 2 * x) ^ 2

/-- `[0,1]` 上の適合移動度は一様正定値であり、下界は `1/9`。 -/
theorem metricMobilityWitness_lower_bound
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 / 9 : ℝ) ≤ metricMobilityWitness x := by
  have hden : 0 < 1 + 2 * x := by positivity
  have hden_le : 1 + 2 * x ≤ 3 := by linarith
  unfold metricMobilityWitness
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 9) (sq_pos_of_pos hden)]
  nlinarith [sq_nonneg x]

/-- 二次ポテンシャルの勾配にこの移動度を掛けたものが、モデルのベクトル場である。 -/
theorem metricMobilityVectorField_eq_negative_mobility_gradient (x : ℝ) :
    metricMobilityVectorField x =
      -(metricMobilityWitness x * variableMobilityGradient x) := by
  unfold metricMobilityVectorField metricMobilityWitness variableMobilityGradient
  field_simp

/-- 二次適合座標の二乗をポテンシャルに選ぶと、変換後の流れは厳密に線形化する。 -/
noncomputable def metricMobilityExactPotential (x : ℝ) : ℝ :=
  (metricMobilityCoordinate x) ^ 2 / 2

noncomputable def metricMobilityExactGradient (x : ℝ) : ℝ :=
  metricMobilityCoordinate x * (1 + 2 * x)

noncomputable def metricMobilityExactVectorField (x : ℝ) : ℝ :=
  -(metricMobilityCoordinate x / (1 + 2 * x))

/-- 線形化ポテンシャルの勾配に移動度を掛けた閉ループ場。 -/
theorem metricMobilityExactVectorField_eq_negative_mobility_gradient (x : ℝ) :
    metricMobilityExactVectorField x =
      -(metricMobilityWitness x * metricMobilityExactGradient x) := by
  unfold metricMobilityExactVectorField metricMobilityWitness
    metricMobilityExactGradient
  field_simp

/-- 適合距離に合わせたポテンシャルも `[0,1]` 上で1-強凸である。 -/
theorem metricMobilityExactPotential_stronglyConvex :
    Tomabechi.Theorem21.StronglyConvexOn (Set.Icc (0 : ℝ) 1)
      metricMobilityExactPotential metricMobilityExactGradient 1 := by
  intro x hx y hy
  have hnorm : ‖y - x‖ ^ 2 = (y - x) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm, Real.inner_apply]
  have hrem : metricMobilityExactPotential y - metricMobilityExactPotential x -
      metricMobilityExactGradient x * (y - x) =
      (y - x) ^ 2 *
        (1 / 2 + 2 * x + x ^ 2 + (1 + 2 * x) * y + (y - x) ^ 2 / 2) := by
    unfold metricMobilityExactPotential metricMobilityExactGradient metricMobilityCoordinate
    ring
  have hcoef : 1 / 2 ≤
      1 / 2 + 2 * x + x ^ 2 + (1 + 2 * x) * y + (y - x) ^ 2 / 2 := by
    have hxy : 0 ≤ (1 + 2 * x) * y :=
      mul_nonneg (by linarith [hx.1]) hy.1
    nlinarith [sq_nonneg x, sq_nonneg (y - x), hx.1, hy.1, hxy]
  rw [hrem]
  have hdSq : 0 ≤ (y - x) ^ 2 := sq_nonneg _
  calc
    1 / 2 * (y - x) ^ 2 = (y - x) ^ 2 * (1 / 2) := by ring
    _ ≤ (y - x) ^ 2 *
        (1 / 2 + 2 * x + x ^ 2 + (1 + 2 * x) * y + (y - x) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hcoef hdSq

/-- 上で定義した明示軌道は、線形化ポテンシャルの状態依存勾配流を満たす。 -/
theorem metricMobilityExactTrajectory_hasDerivAt
    (x : MetricMobilityState) (t : ℝ) :
    HasDerivAt (metricMobilityExactTrajectory x)
      (metricMobilityExactVectorField (metricMobilityExactTrajectory x t)) t := by
  let c : ℝ := metricMobilityCoordinate x.value
  have hc : 0 ≤ c := by
    dsimp [c, metricMobilityCoordinate]
    nlinarith [x.property.1, sq_nonneg x.value]
  have harg : 0 < 1 + 4 * Real.exp (-t) * c := by positivity
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := by
    convert (hasDerivAt_id t).neg using 1
    · funext s
      rfl
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t hneg using 1
    · funext s
      rfl
    · ring
  have hrad : HasDerivAt (fun s : ℝ => 1 + 4 * Real.exp (-s) * c)
      (-4 * Real.exp (-t) * c) t := by
    convert ((hexp.const_mul (4 * c)).add_const 1) using 1
    · funext s
      ring
    · ring
  have hsqrt := hrad.sqrt (ne_of_gt harg)
  have hraw : HasDerivAt
      (fun s : ℝ => (Real.sqrt (1 + 4 * Real.exp (-s) * c) - 1) / 2)
      ((-4 * Real.exp (-t) * c) / (2 * Real.sqrt
        (1 + 4 * Real.exp (-t) * c)) / 2) t := by
    exact (hsqrt.sub_const 1).div_const 2
  have hcoord := metricMobilityExactTrajectory_coordinate x t
  have hroot : 1 + 2 * metricMobilityExactTrajectory x t =
      Real.sqrt (1 + 4 * Real.exp (-t) * c) := by
    dsimp [metricMobilityExactTrajectory, c]
    ring
  have hden : 1 + 2 * metricMobilityExactTrajectory x t ≠ 0 := by
    rw [hroot]
    positivity
  change HasDerivAt
    (fun s : ℝ => (Real.sqrt (1 + 4 * Real.exp (-s) * c) - 1) / 2)
    (metricMobilityExactVectorField (metricMobilityExactTrajectory x t)) t
  convert hraw using 1
  unfold metricMobilityExactVectorField
  rw [hroot, hcoord]
  dsimp [c]
  field_simp [hden]
  ring

noncomputable def metricMobilityHistoryPotential
    (r : MetricMobilityState) (y : ℝ) : ℝ :=
  (metricMobilityCoordinate y - metricMobilityCoordinate r.value) ^ 2 / 2

noncomputable def metricMobilityHistoryGradient
    (r : MetricMobilityState) (y : ℝ) : ℝ :=
  (metricMobilityCoordinate y - metricMobilityCoordinate r.value) * (1 + 2 * y)

noncomputable def metricMobilityHistoryVectorField
    (r : MetricMobilityState) (y : ℝ) : ℝ :=
  -((metricMobilityCoordinate y - metricMobilityCoordinate r.value) / (1 + 2 * y))

/-- 中心移動ポテンシャルの導関数は、定義した履歴別勾配に一致する。 -/
theorem metricMobilityHistoryPotential_hasDerivAt
    (r : MetricMobilityState) (y : ℝ) :
    HasDerivAt (metricMobilityHistoryPotential r)
      (metricMobilityHistoryGradient r y) y := by
  have hcoord := metricMobilityCoordinate_hasDerivAt y
  have hshift := hcoord.sub_const (metricMobilityCoordinate r.value)
  have hsq := hshift.pow 2
  have hpot := hsq.div_const 2
  change HasDerivAt (fun z =>
    (metricMobilityCoordinate z - metricMobilityCoordinate r.value) ^ 2 / 2)
      (metricMobilityHistoryGradient r y) y
  convert hpot using 1
  · simp [metricMobilityHistoryGradient]
    ring

/-- 中心を移したポテンシャルの状態依存移動度勾配ベクトル場。 -/
theorem metricMobilityHistoryVectorField_eq_negative_mobility_gradient
    (r : MetricMobilityState) (y : ℝ) :
    metricMobilityHistoryVectorField r y =
      -(metricMobilityWitness y * metricMobilityHistoryGradient r y) := by
  unfold metricMobilityHistoryVectorField metricMobilityWitness metricMobilityHistoryGradient
  field_simp

/-- 履歴中心 `r` の適合座標時間写像を逆座標へ戻した軌道は、
中心移動ポテンシャルの元座標での状態依存勾配流ODEを満たす。 -/
theorem metricMobilityHistoryFlow_hasDerivAt
    (r x : MetricMobilityState) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (metricMobilityHistoryFlow r x)
      (metricMobilityHistoryVectorField r (metricMobilityHistoryFlow r x t)) t := by
  let a : ℝ := metricMobilityCoordinate r.value
  let d : ℝ := metricMobilityCoordinate x.value - a
  have harg : 0 < 1 + 4 * (a + Real.exp (-t) * d) := by
    have hz := metricMobilityHistoryFlow_coordinate_mem r x ht
    dsimp [a, d] at hz ⊢
    nlinarith [hz.1]
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := by
    convert (hasDerivAt_id t).neg using 1
    · funext s
      rfl
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t hneg using 1
    · funext s
      rfl
    · ring
  have hrad : HasDerivAt (fun s : ℝ => 1 + 4 * (a + Real.exp (-s) * d))
      (-4 * Real.exp (-t) * d) t := by
    convert (((hexp.const_mul d).add_const a).const_mul 4).add_const 1 using 1
    · funext s
      ring
    · ring
  have hsqrt := hrad.sqrt (ne_of_gt harg)
  have hraw : HasDerivAt
      (fun s : ℝ => (Real.sqrt (1 + 4 * (a + Real.exp (-s) * d)) - 1) / 2)
      ((-4 * Real.exp (-t) * d) /
        (2 * Real.sqrt (1 + 4 * (a + Real.exp (-t) * d))) / 2) t := by
    exact (hsqrt.sub_const 1).div_const 2
  have hcoord : metricMobilityCoordinate (metricMobilityHistoryFlow r x t) =
      a + Real.exp (-t) * d := by
    exact metricMobilityCoordinate_inverse_right
      (metricMobilityHistoryFlow_coordinate_mem r x ht)
  have hroot : 1 + 2 * metricMobilityHistoryFlow r x t =
      Real.sqrt (1 + 4 * (a + Real.exp (-t) * d)) := by
    dsimp [metricMobilityHistoryFlow, metricMobilityCoordinateInverse]
    ring
  have hden : 1 + 2 * metricMobilityHistoryFlow r x t ≠ 0 := by
    rw [hroot]
    positivity
  change HasDerivAt
    (fun s : ℝ => (Real.sqrt (1 + 4 * (a + Real.exp (-s) * d)) - 1) / 2)
    (metricMobilityHistoryVectorField r (metricMobilityHistoryFlow r x t)) t
  convert hraw using 1
  unfold metricMobilityHistoryVectorField
  rw [hroot, hcoord]
  dsimp [a, d]
  field_simp [hden]
  ring

/-- 履歴中心 `r` はその履歴の縮小写像の唯一固定点である。 -/
theorem metricMobilityHistoryStep_unique_fixedPoint
    (r x : MetricMobilityState) (T : ℝ) (hT : 0 < T)
    (hx : metricMobilityHistoryStep r T (le_of_lt hT) x = x) : x = r := by
  have hcoord := congrArg (fun y : MetricMobilityState =>
    metricMobilityCoordinate y.value) hx
  rw [metricMobilityHistoryStep_coordinate] at hcoord
  have hcontractFactor : Real.exp (-T) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hcoordEq : metricMobilityCoordinate x.value = metricMobilityCoordinate r.value := by
    nlinarith [hcoord]
  exact metricMobilityCoordinate_injective_on_state hcoordEq

/-- 履歴中心の異なる二つの線形化勾配流時間写像は、中心を別々の唯一固定点とする。
これは定理25 (25.1) の「履歴に依存する谷・縮小流」モデル接続で、
原文の一般的な自己意識更新則への同定は追加仮定として残る。 -/
theorem metricMobilityHistoryStep_fixedPoints_separate
    (r₁ r₂ : MetricMobilityState) (T : ℝ) (hT : 0 < T)
    (hcenters : r₁ ≠ r₂) :
    metricMobilityHistoryStep r₁ T (le_of_lt hT) r₁ ≠
      metricMobilityHistoryStep r₂ T (le_of_lt hT) r₂ := by
  simpa [metricMobilityHistoryStep_fixes_center] using hcenters

theorem metricMobilityHistoryStep_has_no_common_fixedPoint
    (r₁ r₂ : MetricMobilityState) (T : ℝ) (hT : 0 < T)
    (hcenters : r₁ ≠ r₂) :
    ¬ ∃ x : MetricMobilityState,
      metricMobilityHistoryStep r₁ T (le_of_lt hT) x = x ∧
      metricMobilityHistoryStep r₂ T (le_of_lt hT) x = x := by
  rintro ⟨x, hx₁, hx₂⟩
  have hcoord₁ := congrArg (fun y : MetricMobilityState =>
    metricMobilityCoordinate y.value) hx₁
  have hcoord₂ := congrArg (fun y : MetricMobilityState =>
    metricMobilityCoordinate y.value) hx₂
  rw [metricMobilityHistoryStep_coordinate] at hcoord₁ hcoord₂
  have hcontractFactor : Real.exp (-T) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hprod : (1 - Real.exp (-T)) *
      (metricMobilityCoordinate r₁.value - metricMobilityCoordinate r₂.value) = 0 := by
    nlinarith [hcoord₁, hcoord₂]
  have hcentersCoord : metricMobilityCoordinate r₁.value =
      metricMobilityCoordinate r₂.value := by
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · linarith
    · linarith
  exact hcenters (metricMobilityCoordinate_injective_on_state hcentersCoord)

/-- A positive constant scalar mobility `A=aI` only rescales time in a strongly
convex gradient flow. Consequently its time map contracts at rate `exp(-a*c*T)`.
This is a general Hilbert-space sufficient condition within Theorem 21's
state-dependent-mobility family; it does not cover arbitrary varying `A(x)`. -/
theorem stronglyConvexScalarMobilityGradientFlow_dist_contracting
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (potential : E → ℝ) (gradient : E → E)
    (c a T : ℝ) (ha : 0 < a) (hT : 0 ≤ T)
    (hconvex : Tomabechi.Theorem21.StronglyConvexOn U potential gradient c)
    (trajectory : {x : E // x ∈ U} → ℝ → E)
    (hderiv : ∀ x t, HasDerivAt (trajectory x)
      (-(a • gradient (trajectory x t))) t)
    (hstay : ∀ x t, t ∈ Set.Icc 0 T → trajectory x t ∈ U)
    (hstart : ∀ x, trajectory x 0 = x.1) :
    ∀ x y, dist (trajectory x T) (trajectory y T) ≤
      Real.exp (-a * c * T) * dist (x : E) (y : E) := by
  intro x y
  let scaled (z : {x : E // x ∈ U}) (s : ℝ) := trajectory z (s / a)
  have hscaled_deriv (z : {x : E // x ∈ U}) (s : ℝ) :
      HasDerivAt (scaled z) (-gradient (scaled z s)) s := by
    have harg : HasDerivAt (fun r : ℝ => r / a) (1 / a) s := by
      simpa [div_eq_mul_inv, mul_comm] using
        (hasDerivAt_id s).const_mul (a⁻¹)
    have hcomp := (hderiv z (s / a)).hasFDerivAt.comp_hasDerivAt s harg
    have hderivEq :
        ((ContinuousLinearMap.toSpanSingleton ℝ
          (-(a • gradient (trajectory z (s / a))))) (1 / a)) =
            -gradient (trajectory z (s / a)) := by
      simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_neg, smul_smul]
      have hmul : (1 / a) * a = 1 := by field_simp [ha.ne']
      rw [hmul, one_smul]
    have hcomp' := hcomp.congr_deriv hderivEq
    simpa [scaled, Function.comp_def] using hcomp'
  have hscaled_stay (z : {x : E // x ∈ U}) (s : ℝ)
      (hs : s ∈ Set.Icc 0 (a * T)) : scaled z s ∈ U := by
    apply hstay z (s / a)
    constructor
    · exact div_nonneg hs.1 (le_of_lt ha)
    · rw [div_le_iff₀ ha]
      nlinarith [hs.2]
  have haT : 0 ≤ a * T := mul_nonneg (le_of_lt ha) hT
  have hbase := stronglyConvexGradientFlow_dist_contracting U potential gradient c
    0 (a * T) hconvex (scaled x) (scaled y) (hscaled_deriv x) (hscaled_deriv y)
    (hscaled_stay x) (hscaled_stay y) (a * T) ⟨haT, le_rfl⟩
  have htime : a * T / a = T := by field_simp [ha.ne']
  simpa [scaled, htime, hstart, mul_comm, mul_left_comm, mul_assoc] using hbase

/-- このモデルでは、平衡点0への距離減衰は二軌道収縮の特殊化として従う。
定理1型の一軌道安定性評価に相当するが、ここではより強い増分収縮を先に証明している。 -/
theorem metricMobility_flow_distance_to_equilibrium
    (f : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ t ∈ Set.Icc a b,
      HasDerivAt f (metricMobilityVectorField (f t)) t)
    (hfU : ∀ t ∈ Set.Icc a b, f t ∈ Set.Icc 0 1) :
    ∀ t ∈ Set.Icc a b,
      dist (metricMobilityCoordinate (f t)) 0 ≤
        Real.exp (-(1 / 27 : ℝ) * (t - a)) *
          dist (metricMobilityCoordinate (f a)) 0 := by
  have hcontract := metricMobility_flow_coordinate_dist_contracting
    f (fun _ => 0) a b hf
    (fun t ht => by
      simpa [metricMobilityVectorField] using (hasDerivAt_const t (0 : ℝ)))
    hfU (fun _ _ => Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  intro t ht
  simpa [metricMobilityCoordinate] using hcontract t ht

/-- 定理21の強凸条件に定数スカラー移動度 `A(x)=aI` を置いた連続時間写像は、
全初期点からの軌道が区間内に留まるなら率 `exp(-a*c*T)` で縮小する。
この条件を満たす層別写像は定理16の追加縮小条件へ接続できる。 -/
theorem stronglyConvexScalarMobilityGradientFlow_timeMap_contracting
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (potential : E → ℝ) (gradient : E → E)
    (c a T : ℝ) (hc : 0 < c) (ha : 0 < a) (hT : 0 < T)
    (hconvex : Tomabechi.Theorem21.StronglyConvexOn U potential gradient c)
    (trajectory : {x : E // x ∈ U} → ℝ → E)
    (hderiv : ∀ x t, HasDerivAt (trajectory x)
      (-(a • gradient (trajectory x t))) t)
    (hstay : ∀ x t, t ∈ Set.Icc 0 T → trajectory x t ∈ U)
    (hstart : ∀ x, trajectory x 0 = x.1) :
    ContractingWith ⟨Real.exp (-a * c * T), le_of_lt (Real.exp_pos _)⟩
      (fun x : {x : E // x ∈ U} =>
        (⟨trajectory x T, hstay x T ⟨le_of_lt hT, le_rfl⟩⟩ : {x : E // x ∈ U})) := by
  have hK : (⟨Real.exp (-a * c * T), le_of_lt (Real.exp_pos _)⟩ : NNReal) < 1 := by
    change Real.exp (-a * c * T) < 1
    rw [Real.exp_lt_one_iff]
    have hprod : 0 < a * c * T := mul_pos (mul_pos ha hc) hT
    nlinarith
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Subtype.dist_eq, Subtype.dist_eq]
  have hdist := stronglyConvexScalarMobilityGradientFlow_dist_contracting
    U potential gradient c a T ha (le_of_lt hT) hconvex trajectory hderiv hstay hstart x y
  change dist (trajectory x T) (trajectory y T) ≤
    Real.exp (-a * c * T) * dist (x : E) (y : E)
  exact hdist



/-!
## 定常流・区間TCZの具体モデル

制御なしの定常例と、定数制御から区間TCZを構成する一次元モデル。
-/

/-- 無制御の定常軌道 `x(t)=x₀`。 -/
def theorem16_stationaryFlow (x₀ t : ℝ) : ℝ := x₀

theorem theorem16_stationaryFlow_hasDerivAt (x₀ t : ℝ) :
    HasDerivAt (theorem16_stationaryFlow x₀) 0 t := by
  change HasDerivAt (fun _ : ℝ => x₀) 0 t
  exact hasDerivAt_const t x₀

/-- 無制御定常流 `x(t)=x₀` における時刻tの到達可能集合。 -/
def theorem16_stationaryReachable (x₀ t : ℝ) : Set ℝ :=
  {x | x = theorem16_stationaryFlow x₀ t}

/-- 監査用トイ系の基礎ポテンシャル。 -/
def theorem16_stationaryPotential (_x : ℝ) : ℝ := 0

/-- 定理1・16の到達可能性とポテンシャル閾値によるTCZ定義の、定常・無制御特殊例。
初期値x₀からの到達可能集合は各時刻で一点、ポテンシャル閾値は0とする。 -/
def theorem16_stationaryTCZ (x₀ : ℝ) : Set ℝ :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ x ∈ theorem16_stationaryReachable x₀ t ∧
    theorem16_stationaryPotential x ≤ 0}

theorem theorem16_stationaryTCZ_eq_singleton (x₀ : ℝ) :
    theorem16_stationaryTCZ x₀ = {x₀} := by
  ext x
  constructor
  · rintro ⟨t, ht, hx, hV⟩
    simpa [theorem16_stationaryReachable, theorem16_stationaryFlow] using hx
  · intro hx
    refine ⟨0, le_rfl, ?_, ?_⟩
    · simpa [theorem16_stationaryReachable, theorem16_stationaryFlow] using hx
    · simp [theorem16_stationaryPotential]

/-- 区間TCZ用のスカラー制御系。許容定数制御は `u∈[-1,1]`。
積分軌道 `x(t)=u t` とし、この制御集合は区間内の履歴別勾配フィードバック
`u=b_h-x` も許す。 -/
def theorem16_intervalControlledTrajectory (u t : ℝ) : ℝ := u * t

theorem theorem16_intervalControlledTrajectory_hasDerivAt (u t : ℝ) :
    HasDerivAt (theorem16_intervalControlledTrajectory u) u t := by
  change HasDerivAt (fun s : ℝ => u * s) u t
  convert (hasDerivAt_id t).const_mul u using 1
  · funext s
    simp
  · ring

/-- 定数許容制御で時刻tに到達する状態の集合。 -/
def theorem16_intervalControlledReachable (t : ℝ) : Set ℝ :=
  {x | ∃ u ∈ Set.Icc (-1 : ℝ) 1,
    theorem16_intervalControlledTrajectory u t = x}

/-- clampへの二乗誤差で定める連続な非負評価コスト。零集合は `[0,1]`。 -/
def theorem16_intervalControlledPotential (x : ℝ) : ℝ :=
  (x - max 0 (min x 1)) ^ 2

theorem theorem16_intervalControlledPotential_continuous :
    Continuous theorem16_intervalControlledPotential := by
  exact (continuous_id.sub (continuous_const.max
    (continuous_id.min continuous_const))).pow 2

theorem theorem16_intervalControlledPotential_nonneg (x : ℝ) :
    0 ≤ theorem16_intervalControlledPotential x := by
  exact sq_nonneg _

theorem theorem16_intervalControlledPotential_le_zero_iff (x : ℝ) :
    theorem16_intervalControlledPotential x ≤ 0 ↔ x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · intro hcost
    have hsq : (x - max 0 (min x 1)) ^ 2 = 0 := by
      unfold theorem16_intervalControlledPotential at hcost
      nlinarith [sq_nonneg (x - max 0 (min x 1))]
    have heq : x = max 0 (min x 1) := by
      have := (sq_eq_zero_iff.mp hsq)
      linarith
    have hclamp : max 0 (min x 1) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_right _ _)
    rw [heq]
    exact hclamp
  · intro hx
    unfold theorem16_intervalControlledPotential
    rw [min_eq_left hx.2, max_eq_right hx.1]
    norm_num

/-- 原文の到達可能・閾値定義による区間制御系のTCZ。 -/
def theorem16_intervalControlledTCZ : Set ℝ :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ x ∈ theorem16_intervalControlledReachable t ∧
    theorem16_intervalControlledPotential x ≤ 0}

theorem theorem16_intervalControlledTCZ_eq_Icc :
    theorem16_intervalControlledTCZ = Set.Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, hreach, hcost⟩
    exact theorem16_intervalControlledPotential_le_zero_iff x |>.mp hcost
  · intro hx
    refine ⟨1, by norm_num, ?_, ?_⟩
    · exact ⟨x, ⟨by linarith [hx.1], hx.2⟩,
        by simp [theorem16_intervalControlledTrajectory]⟩
    · exact theorem16_intervalControlledPotential_le_zero_iff x |>.mpr hx


/-!
## 25-Dを満たさない自己スライス例

自己スライス条件と機能的完備性条件の違いを示す有限モデル。
-/

/-- 25-A(2)の主体自身に対応する一断面の不変性だけでは、全存在・全層を量化する25-Dは
導けないことを示す量化監査用モデル。法則値はBoolであり、確率SCMではない。 -/
def theorem25_selfSliceOnlyModel :
    Theorem25CausalModel Bool Unit Unit (fun _ _ => Bool) (fun _ _ => Bool) :=
  { baselineLaw := fun _ _ _ => false
    intervenedLaw := fun d _ _ s => if d then s else false
    independentFixedIndividualization := fun _ _ _ => True }

theorem theorem25_selfSliceOnlyModel_satisfies_selfSliceA2 :
    ∀ h s,
      theorem25_selfSliceOnlyModel.intervenedLaw false () h s =
        theorem25_selfSliceOnlyModel.baselineLaw false () h := by
  intro h s
  cases s <;> rfl

theorem theorem25_selfSliceOnlyModel_doesNot_satisfy25D :
    ¬ theorem25_selfSliceOnlyModel.FunctionallyComplete := by
  intro hcomplete
  have h := hcomplete true () () true
  change true = false at h
  contradiction

/-- 同じ量化差を、(Γ,Y⁺)の同時法則をもつ実際の有限確率モデルで再現する。
`d=false` を主体自身とみなすと、その全履歴・候補介入で法則は不変だが、別の
存在 `d=true` の出力は候補に依存するため、全称条件25-Dは成立しない。 -/
noncomputable def theorem25_selfSliceOnlyProbabilityModel :
    Theorem25ProbabilityCausalModel Bool Unit Unit
      (fun _ : Unit => Unit) (fun _ : Unit => Bool) (fun _ : Unit => Bool) :=
  { baselineJointLaw := fun _ _ _ =>
      ⟨MeasureTheory.Measure.dirac ((), false), inferInstance⟩
    intervenedJointLaw := fun d _ _ s =>
      ⟨MeasureTheory.Measure.dirac ((), if d then s else false), inferInstance⟩
    independentFixedIndividualization := fun _ _ _ => True }

theorem theorem25_selfSliceOnlyProbabilityModel_satisfies_selfSliceA2 :
    ∀ h s,
      theorem25_selfSliceOnlyProbabilityModel.intervenedJointLaw false () h s =
        theorem25_selfSliceOnlyProbabilityModel.baselineJointLaw false () h := by
  intro h s
  cases s <;> rfl

theorem theorem25_selfSliceOnlyProbabilityModel_doesNot_satisfy25D :
    ¬ ∀ d a h s,
      theorem25_selfSliceOnlyProbabilityModel.intervenedJointLaw d a h s =
        theorem25_selfSliceOnlyProbabilityModel.baselineJointLaw d a h := by
  intro hcomplete
  have heq := congrArg MeasureTheory.ProbabilityMeasure.toMeasure
    (hcomplete true () () true)
  have htest := congrArg (fun μ : MeasureTheory.Measure (Unit × Bool) =>
    μ {x | x.2 = true}) heq
  simp [theorem25_selfSliceOnlyProbabilityModel,
    MeasureTheory.ProbabilityMeasure.toMeasure,
    MeasureTheory.Measure.dirac_apply] at htest

/-- 主体自身の全履歴・全候補値で25-A(2)型不変性が成立しても、
別の存在・層では固定候補に非冗長な効果が残り得る。 -/
theorem theorem25_selfSliceOnlyProbabilityModel_hasAtman_elsewhere :
    (theorem25_selfSliceOnlyProbabilityModel.toCausalModel).hasAtman true () := by
  refine ⟨true, trivial, ⟨(), ?_⟩⟩
  intro heq
  have h' := congrArg MeasureTheory.ProbabilityMeasure.toMeasure heq
  change MeasureTheory.Measure.dirac ((), true) =
    MeasureTheory.Measure.dirac ((), false) at h'
  have hne : MeasureTheory.Measure.dirac ((), true) ≠
      MeasureTheory.Measure.dirac ((), false) :=
    MeasureTheory.dirac_ne_dirac (by decide)
  exact hne h'



/-!
## 定理16の有限・区間逆極限モデル

ここには一次元・区間状態空間で作った有限層系、勾配流、履歴別固定点の具体例を置く。一般の逆極限定理はCoreに残す。
-/

/-- Bool履歴ごとに異なる実数一点TCZを全ての自然数層へ置くtoy逆系。
以下のキャリアは、上の定常・無制御系のTCZとして具体化される。
射影とフィードバックは恒等写像で、一般の認知TCZモデルではない。 -/
noncomputable def theorem16_singletonHistoryLayerSystem :
    Theorem16HistoryLayerSystem Bool Nat (fun _ : Nat => ℝ) := by
  classical
  refine {
    carrier := fun h _ => {if h then 1 else 0}
    compact := ?_
    nonempty := ?_
    convex := ?_
    project := fun _ x => x
    projectAffineOnCarrier := ?_
    projectRefl := ?_
    projectComp := ?_
    projectMaps := ?_
    projectContinuousOn := ?_
    noMax := ?_
    feedback := ?_
    feedbackCommutes := ?_
    feedbackContinuous := ?_ }
  · intro h i
    exact isCompact_singleton
  · intro h i
    exact ⟨if h then 1 else 0, Set.mem_singleton _⟩
  · intro h i
    exact convex_singleton _
  · intro h β α hβα x y a b hx hy ha hb hab
    rfl
  · intro h i x
    rfl
  · intro h γ β α hγβ hβα x
    rfl
  · intro h β α hβα x hx
    simpa using hx
  · intro h j
    exact continuousOn_id
  · intro i
    exact ⟨i + 1, Nat.lt_succ_self i⟩
  · intro h i x
    exact x
  · intro h β α hβα x
    rfl
  · intro h i
    exact continuous_id

/-- 各層の一点carrierは、対応する初期値からの定常力学のTCZそのもの。 -/
theorem theorem16_singletonHistoryLayerSystem_carrier_eq_stationaryTCZ
    (h : Bool) (i : Nat) :
    theorem16_singletonHistoryLayerSystem.carrier h i =
      theorem16_stationaryTCZ (if h then 1 else 0) := by
  rw [theorem16_stationaryTCZ_eq_singleton]
  simp [theorem16_singletonHistoryLayerSystem]

/-- 上のtoy逆系は、原文の逆極限固定点存在定理を満たす。 -/
theorem theorem16_singletonHistoryLayerSystem_hasFixedPoint (h : Bool) :
    ∃ x : {x : ∀ i : Nat, ℝ //
      x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
        theorem16_singletonHistoryLayerSystem.carrier
        theorem16_singletonHistoryLayerSystem.project h},
      historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
        theorem16_singletonHistoryLayerSystem.carrier
        theorem16_singletonHistoryLayerSystem.project
        theorem16_singletonHistoryLayerSystem.projectMaps
        theorem16_singletonHistoryLayerSystem.feedback
        theorem16_singletonHistoryLayerSystem.feedbackCommutes h x = x := by
  exact theorem16_singletonHistoryLayerSystem.fixedPointExists h

/-- このtoy逆系の履歴別SC部分型は一点集合である。 -/
theorem theorem16_singletonHistoryLayerSystem_SC_subsingleton (h : Bool) :
    Subsingleton
      {x : ∀ i : Nat, ℝ //
        x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
          theorem16_singletonHistoryLayerSystem.carrier
          theorem16_singletonHistoryLayerSystem.project h} := by
  constructor
  intro x y
  apply Subtype.ext
  funext i
  have hx := x.2.1 i
  have hy := y.2.1 i
  change x.1 i ∈ {if h then 1 else 0} at hx
  change y.1 i ∈ {if h then 1 else 0} at hy
  exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm

/-- 原文の逆極限存在定理が与える固定点を束ねたBool履歴族。
本例ではSC自体が一点なので固定点一意性は縮小性なしに従うが、これは退化したtoy例に限る。 -/
noncomputable def theorem16_singletonHistoryFixedPoints :
    HistoryFixedPoints Bool (∀ i : Nat, ℝ) := by
  classical
  let carrier : Bool → (∀ i : Nat, ℝ) → Prop := fun h x =>
    x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
      theorem16_singletonHistoryLayerSystem.carrier
      theorem16_singletonHistoryLayerSystem.project h
  let feedback : ∀ h, {x : (∀ i : Nat, ℝ) // carrier h x} →
      {x : (∀ i : Nat, ℝ) // carrier h x} := fun h =>
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      theorem16_singletonHistoryLayerSystem.carrier
      theorem16_singletonHistoryLayerSystem.project
      theorem16_singletonHistoryLayerSystem.projectMaps
      theorem16_singletonHistoryLayerSystem.feedback
      theorem16_singletonHistoryLayerSystem.feedbackCommutes h
  let fixed (h : Bool) : {x : (∀ i : Nat, ℝ) // carrier h x} :=
    Classical.choose (theorem16_singletonHistoryLayerSystem.fixedPointExists h)
  have hfixed (h : Bool) : feedback h (fixed h) = fixed h :=
    Classical.choose_spec (theorem16_singletonHistoryLayerSystem.fixedPointExists h)
  refine ⟨carrier, feedback, fixed, hfixed, ?_⟩
  intro h y hy
  haveI := theorem16_singletonHistoryLayerSystem_SC_subsingleton h
  exact Subsingleton.elim y (fixed h)

/-- 履歴別固定点は異なる。これは定理25-A(1)と25.1のtoy逆系での実例。 -/
theorem theorem16_singletonHistoryFixedPoints_separate :
    (theorem16_singletonHistoryFixedPoints.fixedPoint false).1 ≠
      (theorem16_singletonHistoryFixedPoints.fixedPoint true).1 := by
  intro hEq
  have h0 := (theorem16_singletonHistoryFixedPoints.fixedPoint false).2.1 0
  have h1 := (theorem16_singletonHistoryFixedPoints.fixedPoint true).2.1 0
  change (theorem16_singletonHistoryFixedPoints.fixedPoint false).1 0 ∈ {0} at h0
  change (theorem16_singletonHistoryFixedPoints.fixedPoint true).1 0 ∈ {1} at h1
  have v0 : (theorem16_singletonHistoryFixedPoints.fixedPoint false).1 0 = 0 :=
    Set.mem_singleton_iff.mp h0
  have v1 : (theorem16_singletonHistoryFixedPoints.fixedPoint true).1 0 = 1 :=
    Set.mem_singleton_iff.mp h1
  have hcoord := congrFun hEq 0
  rw [v0, v1] at hcoord
  norm_num at hcoord

/-- この逆系例で定理25.1の全履歴共通固定状態不存在を得る。 -/
theorem theorem16_singletonHistoryFixedPoints_noCommonFixedPoint :
    ¬ ∃ s : (∀ i : Nat, ℝ), ∃ hmem : ∀ h,
      theorem16_singletonHistoryFixedPoints.carrier h s,
      ∀ h, theorem16_singletonHistoryFixedPoints.feedback h ⟨s, hmem h⟩ =
        ⟨s, hmem h⟩ := by
  rintro ⟨s, hmem, hfix⟩
  have hfalse := theorem16_singletonHistoryFixedPoints.unique false
    ⟨s, hmem false⟩ (hfix false)
  have htrue := theorem16_singletonHistoryFixedPoints.unique true
    ⟨s, hmem true⟩ (hfix true)
  apply theorem16_singletonHistoryFixedPoints_separate
  exact (congrArg Subtype.val hfalse).symm.trans (congrArg Subtype.val htrue)

/-- 各層TCZを非退化な閉区間 `[0,1]` とし、履歴ごとに端点へ写す定数フィードバックを置く。
射影は恒等写像なので、層間整合性と逆極限上の連続性が成り立つ。 -/
noncomputable def theorem16_intervalHistoryLayerSystem :
    Theorem16HistoryLayerSystem Bool Nat (fun _ : Nat => ℝ) := by
  refine {
    carrier := fun _ _ => Set.Icc (0 : ℝ) 1
    compact := ?_
    nonempty := ?_
    convex := ?_
    project := fun _ x => x
    projectAffineOnCarrier := ?_
    projectRefl := ?_
    projectComp := ?_
    projectMaps := ?_
    projectContinuousOn := ?_
    noMax := ?_
    feedback := ?_
    feedbackCommutes := ?_
    feedbackContinuous := ?_ }
  · intro h i
    exact isCompact_Icc
  · intro h i
    exact ⟨0, Set.left_mem_Icc.mpr (by norm_num)⟩
  · intro h i
    exact convex_Icc 0 1
  · intro h β α hβα x y a b hx hy ha hb hab
    rfl
  · intro h i x
    rfl
  · intro h γ β α hγβ hβα x
    rfl
  · intro h β α hβα x hx
    simpa using hx
  · intro h j
    exact continuousOn_id
  · intro i
    exact ⟨i + 1, Nat.lt_succ_self i⟩
  · intro h i x
    exact ⟨if h then 1 else 0, by cases h <;> simp⟩
  · intro h β α hβα x
    apply Subtype.ext
    rfl
  · intro h i
    exact continuous_const

/-- 非退化な各層carrier `[0,1]` は、上の制御系の実際のTCZである。 -/
theorem theorem16_intervalHistoryLayerSystem_carrier_eq_controlledTCZ
    (h : Bool) (i : Nat) :
    theorem16_intervalHistoryLayerSystem.carrier h i =
      theorem16_intervalControlledTCZ := by
  rw [theorem16_intervalControlledTCZ_eq_Icc]
  rfl

/-- 各履歴hの目標点を強凸ポテンシャルの唯一の谷とする。 -/
def theorem16_intervalGradientCenter (h : Bool) : ℝ := if h then 1 else 0

noncomputable def theorem16_intervalGradientPotential (h : Bool) (x : ℝ) : ℝ :=
  (x - theorem16_intervalGradientCenter h) ^ 2 / 2

def theorem16_intervalGradient (h : Bool) (x : ℝ) : ℝ :=
  x - theorem16_intervalGradientCenter h

/-- 勾配流 `x'=-(x-b_h)` の明示解。 -/
noncomputable def theorem16_intervalGradientFlow (h : Bool) (x t : ℝ) : ℝ :=
  theorem16_intervalGradientCenter h +
    (x - theorem16_intervalGradientCenter h) * Real.exp (-t)

theorem theorem16_intervalGradientFlow_hasDerivAt (h : Bool) (x t : ℝ) :
    HasDerivAt (theorem16_intervalGradientFlow h x)
      (-(theorem16_intervalGradient h (theorem16_intervalGradientFlow h x t))) t := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := by
    convert (hasDerivAt_id t).neg using 1
    funext s
    rfl
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s))
      (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t hneg using 1
    · funext s
      rfl
    · ring
  convert ((hexp.const_mul (x - theorem16_intervalGradientCenter h)).const_add
    (theorem16_intervalGradientCenter h)) using 1
  · funext s
    dsimp [theorem16_intervalGradientFlow]
  · dsimp [theorem16_intervalGradient, theorem16_intervalGradientFlow]
    ring

theorem theorem16_intervalGradientFlow_start (h : Bool) (x : ℝ) :
    theorem16_intervalGradientFlow h x 0 = x := by
  simp [theorem16_intervalGradientFlow]

theorem theorem16_intervalGradientFlow_stays (h : Bool) (x t : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    theorem16_intervalGradientFlow h x t ∈ Set.Icc (0 : ℝ) 1 := by
  have hqpos : 0 < Real.exp (-t) := Real.exp_pos _
  have hqle : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [ht.1]
  simp only [Set.mem_Icc] at hx ⊢
  cases h
  · simp only [theorem16_intervalGradientFlow, theorem16_intervalGradientCenter,
      Bool.false_eq_true, if_false] at ⊢
    simp only [sub_zero, zero_add] at ⊢
    constructor
    · exact mul_nonneg hx.1 hqpos.le
    · calc
        x * Real.exp (-t) ≤ 1 * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hx.2 hqpos.le
        _ = Real.exp (-t) := one_mul _
        _ ≤ 1 := hqle
  · simp only [theorem16_intervalGradientFlow, theorem16_intervalGradientCenter,
      if_true] at ⊢
    have hflow : 1 + (x - 1) * Real.exp (-t) =
        1 - (1 - x) * Real.exp (-t) := by
      ring
    rw [hflow]
    have hleft : 0 ≤ (1 - x) * Real.exp (-t) :=
      mul_nonneg (by linarith [hx.2]) hqpos.le
    have hright : (1 - x) * Real.exp (-t) ≤ 1 := by
      calc
        (1 - x) * Real.exp (-t) ≤ 1 * 1 :=
          mul_le_mul (by linarith [hx.1]) hqle (by linarith [hx.2]) (by norm_num)
        _ = 1 := by norm_num
    change 0 ≤ 1 - (1 - x) * Real.exp (-t) ∧
      1 - (1 - x) * Real.exp (-t) ≤ 1
    constructor <;> nlinarith

/-- 勾配フィードバックの入力 `b_h-x` は、TCZ生成系と共通の許容範囲 `[-1,1]` に入る。 -/
theorem theorem16_intervalGradientFlow_control_admissible (h : Bool) (x t : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    theorem16_intervalGradientCenter h - theorem16_intervalGradientFlow h x t ∈
      Set.Icc (-1 : ℝ) 1 := by
  have hf := theorem16_intervalGradientFlow_stays h x t hx ht
  have hf' : 0 ≤ theorem16_intervalGradientFlow h x t ∧
      theorem16_intervalGradientFlow h x t ≤ 1 := by
    simpa only [Set.mem_Icc] using hf
  cases h
  · simp only [theorem16_intervalGradientCenter, Bool.false_eq_true, if_false] at *
    constructor <;> linarith [hf'.1, hf'.2]
  · simp only [theorem16_intervalGradientCenter, if_true] at *
    constructor <;> linarith [hf'.1, hf'.2]

theorem theorem16_intervalGradientPotential_stronglyConvex (h : Bool) :
    Tomabechi.Theorem21.StronglyConvexOn (Set.Icc (0 : ℝ) 1)
      (theorem16_intervalGradientPotential h) (theorem16_intervalGradient h) 1 := by
  intro x hx y hy
  rw [Real.norm_eq_abs]
  rw [RCLike.inner_apply]
  simp [theorem16_intervalGradientPotential, theorem16_intervalGradient]
  nlinarith [sq_nonneg (y - x)]

/-- 区間逆系の各履歴フィードバックを、上の強凸勾配流の時刻1写像とする。 -/
noncomputable def theorem16_intervalGradientFlowFeedback (h : Bool) (i : Nat)
    (x : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) :
    {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} :=
  ⟨theorem16_intervalGradientFlow h x.1 1,
    theorem16_intervalGradientFlow_stays h x.1 1 x.2 ⟨by norm_num, le_rfl⟩⟩

/-- 各層の非定数フィードバック写像は強凸勾配流の時間1写像なので縮小写像である。 -/
theorem theorem16_intervalGradientFlowFeedback_contracting (h : Bool) (i : Nat) :
    ContractingWith ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩
      (theorem16_intervalGradientFlowFeedback h i) := by
  let trajectory : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} → ℝ → ℝ :=
    fun x t => theorem16_intervalGradientFlow h x.1 t
  have hcontract := stronglyConvexGradientFlow_timeMap_contracting
    (Set.Icc (0 : ℝ) 1) (theorem16_intervalGradientPotential h)
    (theorem16_intervalGradient h) 1 1 (by norm_num)
    (theorem16_intervalGradientPotential_stronglyConvex h) (by norm_num)
    trajectory
    (by intro x t; exact theorem16_intervalGradientFlow_hasDerivAt h x.1 t)
    (by
      intro x t ht
      exact theorem16_intervalGradientFlow_stays h x.1 t x.2 ht)
    (by intro x; exact theorem16_intervalGradientFlow_start h x.1)
  have hmaps : theorem16_intervalGradientFlowFeedback h i = fun x =>
      (⟨trajectory x 1,
        theorem16_intervalGradientFlow_stays h x.1 1 x.2 ⟨by norm_num, le_rfl⟩⟩ :
        {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) := by
    funext x
    apply Subtype.ext
    rfl
  rw [hmaps]
  simpa [trajectory, mul_comm] using hcontract

/-- 閉区間carrierは完備であるため、勾配流の時刻1写像はBanach固定点をもつ。 -/
theorem theorem16_intervalGradientFlowFeedback_hasUniqueFixedPoint (h : Bool) (i : Nat) :
    HasUniqueFixedPoint (theorem16_intervalGradientFlowFeedback h i) := by
  letI : CompleteSpace {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} :=
    isClosed_Icc.completeSpace_coe
  exact hasUniqueFixedPoint_of_contraction
    (theorem16_intervalGradientFlowFeedback_contracting h i)

/-- 各層での反復はBanach固定点へ収束し、誤差は `(e⁻¹)^n` 倍以下となる。
これは追加した強凸勾配流モデル内の定理16幾何収束節の実例。 -/
theorem theorem16_intervalGradientFlowFeedback_iterates_tendsto_and_rate
    (h : Bool) (i : Nat) (x : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) :
    Filter.Tendsto
        (fun n : Nat => (theorem16_intervalGradientFlowFeedback h i)^[n] x)
        Filter.atTop
        (nhds (ContractingWith.fixedPoint
          (theorem16_intervalGradientFlowFeedback h i)
          (theorem16_intervalGradientFlowFeedback_contracting h i))) ∧
      ∀ n : Nat, dist
          ((theorem16_intervalGradientFlowFeedback h i)^[n] x)
          (ContractingWith.fixedPoint (theorem16_intervalGradientFlowFeedback h i)
            (theorem16_intervalGradientFlowFeedback_contracting h i)) ≤
        (Real.exp (-1)) ^ n * dist x
          (ContractingWith.fixedPoint (theorem16_intervalGradientFlowFeedback h i)
            (theorem16_intervalGradientFlowFeedback_contracting h i)) := by
  letI : CompleteSpace {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} :=
    isClosed_Icc.completeSpace_coe
  exact contraction_iterates_tendsto_and_rate
    (theorem16_intervalGradientFlowFeedback_contracting h i) x

/-- `[0,1]` TCZの履歴別逆系で、フィードバックを定理21型強凸勾配流の時刻1写像とする。
射影は恒等写像で、層間可換性は同じ履歴の同じ時間写像を使うことから従う。 -/
noncomputable def theorem16_intervalGradientFlowLayerSystem :
    Theorem16HistoryLayerSystem Bool Nat (fun _ : Nat => ℝ) := by
  let M := theorem16_intervalHistoryLayerSystem
  refine { M with
    feedback := fun h i => theorem16_intervalGradientFlowFeedback h i
    feedbackCommutes := ?_
    feedbackContinuous := ?_ }
  · intro h β α hβα x
    apply Subtype.ext
    rfl
  · intro h i
    apply Continuous.subtype_mk
    · exact continuous_const.add
        ((continuous_subtype_val.sub continuous_const).mul_const (Real.exp (-1)))

/-- 恒等射影の逆極限は第0座標で `[0,1]` と同型。これにより逆極限上へ
積位相と両立する完備距離を入れられる。 -/
def theorem16_intervalGradientFlowInverseLimitEquiv (h : Bool) :
    {x : ∀ i : Nat, ℝ // x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project h} ≃
      {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} where
  toFun x := ⟨x.1 0, x.2.1 0⟩
  invFun x := ⟨fun _ => x.1, by
    constructor
    · intro i
      exact x.2
    · intro β α hβα
      rfl⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hcompat := x.2.2 (show 0 ≤ i by omega)
    simpa [theorem16_intervalGradientFlowLayerSystem,
      theorem16_intervalHistoryLayerSystem] using hcompat.symm
  right_inv x := by
    apply Subtype.ext
    rfl

def theorem16_intervalGradientFlowInverseLimitHomeomorph (h : Bool) :
    {x : ∀ i : Nat, ℝ // x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project h} ≃ₜ
      {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} where
  toEquiv := theorem16_intervalGradientFlowInverseLimitEquiv h
  continuous_toFun := Continuous.subtype_mk
    ((continuous_apply 0).comp continuous_subtype_val)
    (fun x => x.2.1 0)
  continuous_invFun := Continuous.subtype_mk
    (continuous_pi fun _ => continuous_subtype_val)
    (fun x => by
      constructor
      · intro i
        exact x.2
      · intro β α hβα
        rfl)

/-- 第0座標同型で引き戻した距離は、逆極限の積部分空間位相と両立する。 -/
noncomputable def theorem16_intervalGradientFlowInverseLimitIsometryEquiv (h : Bool) :
    letI : MetricSpace
      {x : ∀ i : Nat, ℝ // x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
        theorem16_intervalGradientFlowLayerSystem.carrier
        theorem16_intervalGradientFlowLayerSystem.project h} :=
      MetricSpace.induced (theorem16_intervalGradientFlowInverseLimitEquiv h)
        (theorem16_intervalGradientFlowInverseLimitEquiv h).injective inferInstance
    {x : ∀ i : Nat, ℝ // x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project h} ≃ᵢ
      {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} := by
  letI : MetricSpace
      {x : ∀ i : Nat, ℝ // x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
        theorem16_intervalGradientFlowLayerSystem.carrier
        theorem16_intervalGradientFlowLayerSystem.project h} :=
      MetricSpace.induced (theorem16_intervalGradientFlowInverseLimitEquiv h)
        (theorem16_intervalGradientFlowInverseLimitEquiv h).injective inferInstance
  exact ⟨theorem16_intervalGradientFlowInverseLimitEquiv h, fun _ _ => rfl⟩

/-- 第0座標距離はこの恒等射影逆極限上で完備で、積部分空間位相とも両立する。
この特定の対角逆系では、勾配流作用素も全逆極限上の縮小写像になる。 -/
theorem theorem16_intervalGradientFlowInverseLimit_contracting (h : Bool) :
    letI : MetricSpace
      {x : ∀ i : Nat, ℝ // x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
        theorem16_intervalGradientFlowLayerSystem.carrier
        theorem16_intervalGradientFlowLayerSystem.project h} :=
      MetricSpace.induced (theorem16_intervalGradientFlowInverseLimitEquiv h)
        (theorem16_intervalGradientFlowInverseLimitEquiv h).injective inferInstance
    ContractingWith ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩
      (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
        theorem16_intervalGradientFlowLayerSystem.carrier
        theorem16_intervalGradientFlowLayerSystem.project
        theorem16_intervalGradientFlowLayerSystem.projectMaps
        theorem16_intervalGradientFlowLayerSystem.feedback
        theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h) := by
  let X := {x : ∀ i : Nat, ℝ // x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
    theorem16_intervalGradientFlowLayerSystem.carrier
    theorem16_intervalGradientFlowLayerSystem.project h}
  let e := theorem16_intervalGradientFlowInverseLimitEquiv h
  letI : MetricSpace X := MetricSpace.induced e e.injective inferInstance
  have hrate : (⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩ : NNReal) < 1 := by
    change Real.exp (-1) < 1
    rw [Real.exp_lt_one_iff]
    norm_num
  refine ⟨hrate, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  change dist ((historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project
      theorem16_intervalGradientFlowLayerSystem.projectMaps
      theorem16_intervalGradientFlowLayerSystem.feedback
      theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h x).1 0)
      ((historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project
      theorem16_intervalGradientFlowLayerSystem.projectMaps
      theorem16_intervalGradientFlowLayerSystem.feedback
      theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h y).1 0)
    ≤ Real.exp (-1) * dist (x.1 0) (y.1 0)
  have hx0 : (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project
      theorem16_intervalGradientFlowLayerSystem.projectMaps
      theorem16_intervalGradientFlowLayerSystem.feedback
      theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h x).1 0 =
      (theorem16_intervalGradientFlowFeedback h 0
        ⟨x.1 0, x.2.1 0⟩).1 := by
    change (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project
      theorem16_intervalGradientFlowLayerSystem.projectMaps
      theorem16_intervalGradientFlowLayerSystem.feedback
      theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h x).1 0 = _
    simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap, id]
    rfl
  have hy0 : (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project
      theorem16_intervalGradientFlowLayerSystem.projectMaps
      theorem16_intervalGradientFlowLayerSystem.feedback
      theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h y).1 0 =
      (theorem16_intervalGradientFlowFeedback h 0
        ⟨y.1 0, y.2.1 0⟩).1 := by
    change (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project
      theorem16_intervalGradientFlowLayerSystem.projectMaps
      theorem16_intervalGradientFlowLayerSystem.feedback
      theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h y).1 0 = _
    simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap, id]
    rfl
  rw [hx0, hy0]
  exact (theorem16_intervalGradientFlowFeedback_contracting h 0).2.dist_le_mul
    ⟨x.1 0, x.2.1 0⟩ ⟨y.1 0, y.2.1 0⟩

/-- 有限時間勾配流の固定点は履歴別の谷中心に限られる。 -/
theorem theorem16_intervalGradientFlowFeedback_fixedValue (h : Bool) (i : Nat)
    (x : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1})
    (hfix : theorem16_intervalGradientFlowFeedback h i x = x) :
    x.1 = theorem16_intervalGradientCenter h := by
  have hcoord := congrArg Subtype.val hfix
  change theorem16_intervalGradientFlow h x.1 1 = x.1 at hcoord
  have hq : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hqne : Real.exp (-1) ≠ 1 := ne_of_lt hq
  have hprod : (x.1 - theorem16_intervalGradientCenter h) *
      (Real.exp (-1) - 1) = 0 := by
    dsimp [theorem16_intervalGradientFlow] at hcoord
    nlinarith
  rcases mul_eq_zero.mp hprod with hcenter | hrate
  · linarith
  · exact (hqne (by linarith)).elim

theorem theorem16_intervalGradientFlowFeedback_banachFixedPoint_value (h : Bool) (i : Nat) :
    (ContractingWith.fixedPoint (theorem16_intervalGradientFlowFeedback h i)
      (theorem16_intervalGradientFlowFeedback_contracting h i)).1 =
        theorem16_intervalGradientCenter h := by
  let f := theorem16_intervalGradientFlowFeedback h i
  let hf := theorem16_intervalGradientFlowFeedback_contracting h i
  exact theorem16_intervalGradientFlowFeedback_fixedValue h i
    (ContractingWith.fixedPoint f hf) hf.fixedPoint_isFixedPt

/-- 原文定理16から勾配流時間写像の逆極限固定点が得られ、各座標は履歴別谷中心になる。 -/
noncomputable def theorem16_intervalGradientFlowFixedPoints :
    HistoryFixedPoints Bool (∀ i : Nat, ℝ) := by
  classical
  let M := theorem16_intervalGradientFlowLayerSystem
  let carrier : Bool → (∀ i : Nat, ℝ) → Prop := fun h x =>
    x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ) M.carrier M.project h
  let feedback : ∀ h, {x : (∀ i : Nat, ℝ) // carrier h x} →
      {x : (∀ i : Nat, ℝ) // carrier h x} := fun h =>
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ) M.carrier M.project
      M.projectMaps M.feedback M.feedbackCommutes h
  let fixed (h : Bool) : {x : (∀ i : Nat, ℝ) // carrier h x} :=
    Classical.choose (M.fixedPointExists h)
  have hfixed (h : Bool) : feedback h (fixed h) = fixed h :=
    Classical.choose_spec (M.fixedPointExists h)
  refine ⟨carrier, feedback, fixed, hfixed, ?_⟩
  intro h y hy
  apply Subtype.ext
  funext i
  let yi : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} :=
    ⟨y.1 i, by
      have hm := y.2.1 i
      change y.1 i ∈ Set.Icc (0 : ℝ) 1 at hm
      exact hm⟩
  let fi : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} :=
    ⟨(fixed h).1 i, by
      have hm := (fixed h).2.1 i
      change (fixed h).1 i ∈ Set.Icc (0 : ℝ) 1 at hm
      exact hm⟩
  have hyCoord := congrFun (congrArg Subtype.val hy) i
  have hfCoord := congrFun (congrArg Subtype.val (hfixed h)) i
  change (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
    M.carrier M.project M.projectMaps M.feedback M.feedbackCommutes h y).1 i = y.1 i
    at hyCoord
  change (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
    M.carrier M.project M.projectMaps M.feedback M.feedbackCommutes h (fixed h)).1 i =
      (fixed h).1 i at hfCoord
  simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap,
    id] at hyCoord hfCoord
  have hyLayer : theorem16_intervalGradientFlowFeedback h i yi = yi := by
    apply Subtype.ext
    exact hyCoord
  have hfLayer : theorem16_intervalGradientFlowFeedback h i fi = fi := by
    apply Subtype.ext
    exact hfCoord
  have hcenterY := theorem16_intervalGradientFlowFeedback_fixedValue h i yi hyLayer
  have hcenterF := theorem16_intervalGradientFlowFeedback_fixedValue h i fi hfLayer
  exact hcenterY.trans hcenterF.symm

theorem theorem16_intervalGradientFlowFixedPoint_coordinate (h : Bool) (i : Nat) :
    (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 i =
      theorem16_intervalGradientCenter h := by
  have hfix := theorem16_intervalGradientFlowFixedPoints.isFixed h
  have hcoord := congrFun (congrArg Subtype.val hfix) i
  let M := theorem16_intervalGradientFlowLayerSystem
  change (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
    M.carrier M.project M.projectMaps M.feedback M.feedbackCommutes h
    (theorem16_intervalGradientFlowFixedPoints.fixedPoint h)).1 i =
      (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 i at hcoord
  simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap,
    id] at hcoord
  let x : {z : ℝ // z ∈ Set.Icc (0 : ℝ) 1} :=
    ⟨(theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 i,
      (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).2.1 i⟩
  have hlayer : theorem16_intervalGradientFlowFeedback h i x = x := by
    apply Subtype.ext
    exact hcoord
  exact theorem16_intervalGradientFlowFeedback_fixedValue h i x hlayer

/-- 恒等射影の勾配流逆系では、層別反復の収束を積位相で逆極限全体へ移せる。
各座標のBanach収束から `tendsto_pi_nhds` を使う。逆極限全体の距離に関する
一様な縮小評価を主張するものではない。 -/
theorem theorem16_intervalGradientFlowInverseLimit_iterates_tendsto
    (h : Bool)
    (x : {y : ∀ i : Nat, ℝ // y ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project h}) :
    Filter.Tendsto
      (fun n : Nat =>
        (theorem16_intervalGradientFlowFixedPoints.feedback h)^[n] x)
      Filter.atTop
      (nhds (theorem16_intervalGradientFlowFixedPoints.fixedPoint h)) := by
  let F := theorem16_intervalGradientFlowFixedPoints
  let layerFeedback := theorem16_intervalGradientFlowFeedback h
  change {y : ∀ i : Nat, ℝ // F.carrier h y} at x
  let layerPoint (z : {y : ∀ i : Nat, ℝ // F.carrier h y}) (i : Nat) :
      {y : ℝ // y ∈ Set.Icc (0 : ℝ) 1} :=
    ⟨z.1 i, z.2.1 i⟩
  have hstep (z : {y : ∀ i : Nat, ℝ // F.carrier h y}) (i : Nat) :
      (F.feedback h z).1 i = (layerFeedback i (layerPoint z i)).1 := by
    change (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project
      theorem16_intervalGradientFlowLayerSystem.projectMaps
      theorem16_intervalGradientFlowLayerSystem.feedback
      theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h z).1 i = _
    simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap, id]
    rfl
  have hiter : ∀ n (z : {y : ∀ i : Nat, ℝ // F.carrier h y}) (i : Nat),
      ((F.feedback h)^[n] z).1 i =
        ((layerFeedback i)^[n] (layerPoint z i)).1 := by
    intro n
    induction n with
    | zero => intro z i; rfl
    | succ n ih =>
        intro z i
        simp only [Function.iterate_succ_apply]
        rw [ih (F.feedback h z) i]
        have hpoint : layerPoint (F.feedback h z) i =
            layerFeedback i (layerPoint z i) := by
          apply Subtype.ext
          exact hstep z i
        rw [hpoint]
  apply tendsto_subtype_rng.2
  apply tendsto_pi_nhds.2
  intro i
  have hlayer := theorem16_intervalGradientFlowFeedback_iterates_tendsto_and_rate
    h i (layerPoint x i)
  have hcoordinate :
      (F.fixedPoint h).1 i =
        (ContractingWith.fixedPoint (layerFeedback i)
          (theorem16_intervalGradientFlowFeedback_contracting h i)).1 := by
    rw [theorem16_intervalGradientFlowFixedPoint_coordinate,
      theorem16_intervalGradientFlowFeedback_banachFixedPoint_value]
  have hlayerVal := tendsto_subtype_rng.mp hlayer.1
  have htransport : Filter.Tendsto
      (fun n : Nat => ((F.feedback h)^[n] x).1 i) Filter.atTop
      (nhds ((F.fixedPoint h).1 i)) := by
    simpa [layerFeedback, layerPoint, hcoordinate] using
      hlayerVal.congr (fun n => (hiter n x i).symm)
  exact htransport

/-- 逆極限の反復は、各層座標ごとに同じ幾何率 `exp(-n)` で誤差が減る。
初期差に一様な上界がないため、これは積全体の一様距離評価ではなく座標別評価である。 -/
theorem theorem16_intervalGradientFlowInverseLimit_coordinate_rate
    (h : Bool)
    (x : {y : ∀ i : Nat, ℝ // y ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project h}) :
    ∀ n i, dist (((theorem16_intervalGradientFlowFixedPoints.feedback h)^[n] x).1 i)
        ((theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 i) ≤
      (Real.exp (-1)) ^ n * dist (x.1 i)
        ((theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 i) := by
  let F := theorem16_intervalGradientFlowFixedPoints
  let layerFeedback := theorem16_intervalGradientFlowFeedback h
  change {y : ∀ i : Nat, ℝ // F.carrier h y} at x
  let layerPoint (z : {y : ∀ i : Nat, ℝ // F.carrier h y}) (i : Nat) :
      {y : ℝ // y ∈ Set.Icc (0 : ℝ) 1} := ⟨z.1 i, z.2.1 i⟩
  have hstep (z : {y : ∀ i : Nat, ℝ // F.carrier h y}) (i : Nat) :
      (F.feedback h z).1 i = (layerFeedback i (layerPoint z i)).1 := by
    change (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project
      theorem16_intervalGradientFlowLayerSystem.projectMaps
      theorem16_intervalGradientFlowLayerSystem.feedback
      theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h z).1 i = _
    simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap, id]
    rfl
  have hiter : ∀ n (z : {y : ∀ i : Nat, ℝ // F.carrier h y}) (i : Nat),
      ((F.feedback h)^[n] z).1 i = ((layerFeedback i)^[n] (layerPoint z i)).1 := by
    intro n
    induction n with
    | zero => intro z i; rfl
    | succ n ih =>
        intro z i
        simp only [Function.iterate_succ_apply]
        rw [ih (F.feedback h z) i]
        have hpoint : layerPoint (F.feedback h z) i =
            layerFeedback i (layerPoint z i) := by
          apply Subtype.ext
          exact hstep z i
        rw [hpoint]
  intro n i
  have hlayer := theorem16_intervalGradientFlowFeedback_iterates_tendsto_and_rate
    h i (layerPoint x i)
  have hcoordinate :
      (F.fixedPoint h).1 i =
        (ContractingWith.fixedPoint (layerFeedback i)
          (theorem16_intervalGradientFlowFeedback_contracting h i)).1 := by
    rw [theorem16_intervalGradientFlowFixedPoint_coordinate,
      theorem16_intervalGradientFlowFeedback_banachFixedPoint_value]
  have hbound := hlayer.2 n
  rw [hiter n x i, hcoordinate]
  simpa only [Subtype.dist_eq] using hbound

theorem theorem16_intervalGradientFlowFixedPoints_separate :
    (theorem16_intervalGradientFlowFixedPoints.fixedPoint false).1 ≠
      (theorem16_intervalGradientFlowFixedPoints.fixedPoint true).1 := by
  intro hEq
  have hvf := theorem16_intervalGradientFlowFixedPoint_coordinate false 0
  have hvt := theorem16_intervalGradientFlowFixedPoint_coordinate true 0
  have hcoord := congrFun hEq 0
  rw [hvf, hvt] at hcoord
  simp [theorem16_intervalGradientCenter] at hcoord

/-- 強凸勾配流の履歴別逆極限固定点を、25-A(1)の履歴分離条件から定理25.1へ接続する。
本toyモデルでは別定理で固定点の座標が履歴中心になることを示している。 -/
theorem theorem25_firstConclusion_of_intervalGradientFlowFixedPoints
    {h₁ h₂ : Bool}
    (hsep : (theorem16_intervalGradientFlowFixedPoints.fixedPoint h₁).1 ≠
      (theorem16_intervalGradientFlowFixedPoints.fixedPoint h₂).1) :
    ¬ ∃ s : (∀ i : Nat, ℝ),
      ∃ hs₁ : theorem16_intervalGradientFlowFixedPoints.carrier h₁ s,
      ∃ hs₂ : theorem16_intervalGradientFlowFixedPoints.carrier h₂ s,
        theorem16_intervalGradientFlowFixedPoints.feedback h₁ ⟨s, hs₁⟩ = ⟨s, hs₁⟩ ∧
        theorem16_intervalGradientFlowFixedPoints.feedback h₂ ⟨s, hs₂⟩ = ⟨s, hs₂⟩ := by
  exact no_common_fixed_point_of_history_separation
    theorem16_intervalGradientFlowFixedPoints hsep

theorem theorem25_intervalGradientFlow_firstConclusion :
    ¬ ∃ s : (∀ i : Nat, ℝ),
      ∃ hs₁ : theorem16_intervalGradientFlowFixedPoints.carrier false s,
      ∃ hs₂ : theorem16_intervalGradientFlowFixedPoints.carrier true s,
        theorem16_intervalGradientFlowFixedPoints.feedback false ⟨s, hs₁⟩ = ⟨s, hs₁⟩ ∧
        theorem16_intervalGradientFlowFixedPoints.feedback true ⟨s, hs₂⟩ = ⟨s, hs₂⟩ := by
  exact theorem25_firstConclusion_of_intervalGradientFlowFixedPoints
    theorem16_intervalGradientFlowFixedPoints_separate

/-- 非退化区間逆極限から直接作る履歴別固定点族。
各SCには連続な多数の状態があるが、フィードバックが履歴端点への定数写像なので、
固定点は一意で、二履歴の固定点値は異なる。縮小定数のメトリック証明ではなく、
この特殊な定数作用素の方程式から一意性を示している。 -/
noncomputable def theorem16_intervalHistoryFixedPoints :
    HistoryFixedPoints Bool (∀ i : Nat, ℝ) := by
  classical
  let M := theorem16_intervalHistoryLayerSystem
  let carrier : Bool → (∀ i : Nat, ℝ) → Prop := fun h x =>
    x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ) M.carrier M.project h
  let feedback : ∀ h, {x : (∀ i : Nat, ℝ) // carrier h x} →
      {x : (∀ i : Nat, ℝ) // carrier h x} := fun h =>
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ) M.carrier M.project
      M.projectMaps M.feedback M.feedbackCommutes h
  let fixed (h : Bool) : {x : (∀ i : Nat, ℝ) // carrier h x} :=
    Classical.choose (M.fixedPointExists h)
  have hfixed (h : Bool) : feedback h (fixed h) = fixed h :=
    Classical.choose_spec (M.fixedPointExists h)
  refine ⟨carrier, feedback, fixed, hfixed, ?_⟩
  intro h y hy
  apply Subtype.ext
  funext i
  have hval := congrFun (congrArg Subtype.val hy) i
  have hfixedVal := congrFun (congrArg Subtype.val (hfixed h)) i
  change (if h then 1 else 0) = y.1 i at hval
  change (if h then 1 else 0) = (fixed h).1 i at hfixedVal
  exact hval.symm.trans hfixedVal

theorem theorem16_intervalHistoryFixedPoint_coordinate (h : Bool) :
    (theorem16_intervalHistoryFixedPoints.fixedPoint h).1 0 =
      (if h then 1 else 0) := by
  have hfix := theorem16_intervalHistoryFixedPoints.isFixed h
  have hcoord := congrFun (congrArg Subtype.val hfix) 0
  simp [theorem16_intervalHistoryFixedPoints, historyInducedAffineInverseLimitMap,
    theorem16_intervalHistoryLayerSystem] at hcoord
  exact hcoord.symm

/-- 区間TCZでは状態空間は非退化だが、層フィードバックが定数なので固定点は履歴依存。 -/
theorem theorem16_intervalHistoryFixedPoints_separate :
    (theorem16_intervalHistoryFixedPoints.fixedPoint false).1 ≠
      (theorem16_intervalHistoryFixedPoints.fixedPoint true).1 := by
  intro hEq
  have hvf := theorem16_intervalHistoryFixedPoint_coordinate false
  have hvt := theorem16_intervalHistoryFixedPoint_coordinate true
  have hcoord := congrFun hEq 0
  rw [hvf, hvt] at hcoord
  norm_num at hcoord

/-- 非退化区間逆系で、定理25.1の全履歴共通固定状態不存在が成立する。 -/
theorem theorem16_intervalHistoryFixedPoints_noCommonFixedPoint :
    ¬ ∃ s : (∀ i : Nat, ℝ), ∃ hmem : ∀ h,
      theorem16_intervalHistoryFixedPoints.carrier h s,
      ∀ h, theorem16_intervalHistoryFixedPoints.feedback h ⟨s, hmem h⟩ =
        ⟨s, hmem h⟩ := by
  rintro ⟨s, hmem, hfix⟩
  have hfalse := theorem16_intervalHistoryFixedPoints.unique false
    ⟨s, hmem false⟩ (hfix false)
  have htrue := theorem16_intervalHistoryFixedPoints.unique true
    ⟨s, hmem true⟩ (hfix true)
  apply theorem16_intervalHistoryFixedPoints_separate
  exact (congrArg Subtype.val hfalse).symm.trans (congrArg Subtype.val htrue)

/-- 25-Dの同時法則不変性は、完全なΓ観測の確率1整合も介入後に保存する。 -/
theorem theorem25_relationalStateCoherent_afterIntervention
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25C3IntegratedModel D History Layer Role
      Representation Gamma Output Candidate)
    (hcomplete : ∀ d a h s,
      M.integrated.probability.intervenedJointLaw d a h s =
        M.integrated.probability.baselineJointLaw d a h)
    (d : D) (a : Layer) (h : History) (s : Candidate a) :
    MeasureTheory.ProbabilityMeasure.toMeasure
      (M.integrated.probability.intervenedJointLaw d a h s)
      {ω | M.relationalStateObservation d a h ω.1 =
        M.integrated.presenceAndRelations.relationalState d h a} = 1 := by
  rw [hcomplete d a h s]
  exact M.baselineRelationalStateCoherent d a h




/-!
## 定理25の具体的SCM・反例・C3モデル

ここには固定点の一般定理とは独立した具体的な有限・区間モデルと、その条件充足/不充足を示す補題を置く。
-/

/-- 25-B/Cと基準観測の整合だけでは25-Dは出ず、(25.2)も従わないことを示す有限例。
存在は二点、抽象度は一層とし、全存在が共通の一元上位表現をもち、相互関係グラフは
連結である。一方、候補変数を false に固定した基準構造方程式へ true を介入すると、
将来出力が false から true に変わる。 -/
noncomputable def theorem25_twoExistenceCountermodelSCM :
    Theorem25StructuralCausalModel Bool Unit Unit Unit
      (fun _ : Unit => Unit) (fun _ : Unit => Bool) (fun _ : Unit => Bool) :=
  { defaultCandidate := fun _ => false
    exogenousLaw := fun _ _ =>
      ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
    stateEquation := fun _ _ _ _ _ => ()
    outputEquation := fun _ _ _ _ s => s
    baselineJointAEMeasurable := by
      intro d a h
      exact theorem25_finiteDomain_aemeasurable _ _
    intervenedJointAEMeasurable := by
      intro d a h s
      exact theorem25_finiteDomain_aemeasurable _ _
    independentFixedIndividualization := fun _ _ _ => True }

noncomputable def theorem25_twoExistencePresenceRelations :
    Theorem25PresenceRelationModel Bool Unit Unit Unit (fun _ : Unit => Unit) := by
  classical
  refine {
    profile := fun _ _ _ => some ()
    topMarker := ()
    topRepresentationIsSubsingleton := ?_
    supportNonempty := ?_
    supportUpwardClosed := ?_
    topLayerHasCommonMarker := ?_
    roleInverse := id
    roleInverseInvolutive := ?_
    relationEdge := fun _ d _ _ e _ => d ≠ e
    relationEdgeReverses := ?_
    everyExistenceIsRelated := ?_
    relationGraphConnected := ?_
  }
  · intro x y
    cases x
    cases y
    rfl
  · intro d h
    exact ⟨(), by simp⟩
  · intro d h a b hp hab
    simp
  · intro d h
    rfl
  · intro r
    rfl
  · intro h d a r e b
    simp [ne_comm]
  · intro h d
    cases d with
    | false => exact ⟨true, (), (), (), ⟨by decide, by decide⟩⟩
    | true => exact ⟨false, (), (), (), ⟨by decide, by decide⟩⟩
  · intro h d e
    cases d <;> cases e
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by decide, ⟨(), (), (), by decide⟩⟩
    · exact Relation.ReflTransGen.single ⟨by decide, ⟨(), (), (), by decide⟩⟩
    · exact Relation.ReflTransGen.refl

noncomputable def theorem25_twoExistenceCountermodel :
    Theorem25IntegratedModel Bool Unit Unit Unit
      (fun _ : Unit => Unit) (fun _ : Unit => Unit)
      (fun _ : Unit => Bool) (fun _ : Unit => Bool) := by
  classical
  refine ⟨?_, theorem25_twoExistencePresenceRelations, ?_, ?_, ?_, ?_⟩
  · exact theorem25_twoExistenceCountermodelSCM.toProbabilityCausalModel
  · exact fun _ _ => some ()
  · exact fun _ _ d _ _ e _ => d ≠ e
  · intro d a h
    change (MeasureTheory.Measure.dirac ()).map (fun _ : Unit => ((), false))
      {ω : Unit × Bool | some () = some ()} = 1
    rw [MeasureTheory.Measure.map_dirac]
    apply MeasureTheory.Measure.dirac_apply_of_mem
    simp
  · intro d a h e b r
    change (MeasureTheory.Measure.dirac ()).map (fun _ : Unit => ((), false))
      {ω : Unit × Bool | (d ≠ e) ↔ (d ≠ e)} = 1
    rw [MeasureTheory.Measure.map_dirac]
    apply MeasureTheory.Measure.dirac_apply_of_mem
    simp

/-- 有限B/C反例を25-C3の完全なΓ型にも載せた構造方程式モデル。
状態変数そのものを (Z,Vert,Inc) とし、基準観測整合を満たす。 -/
abbrev Theorem25TwoExistenceGamma :=
  Theorem25RelationalState Bool Unit Unit (fun _ : Unit => Unit)

instance : MeasurableSpace Theorem25TwoExistenceGamma := ⊤

/-- 候補Σを一様なBool外生変数にした、非退化な有限SCM。
各固定履歴でΣは関係状態Γと独立だが、`do(Σ=s)`で出力が変わる。
これは25-Dの必要性を示す有限反例で、H自体の同時分布はモデル化しない。 -/
noncomputable def theorem25_twoExistenceRandomizedSCM :
    Theorem25RandomizedStructuralCausalModel Bool Unit Unit Bool
      (fun _ : Unit => Theorem25TwoExistenceGamma)
      (fun _ : Unit => Bool) (fun _ : Unit => Bool) := by
  classical
  refine {
    exogenousLaw := fun _ _ =>
      ⟨ProbabilityTheory.uniformOn (Set.univ : Set Bool), inferInstance⟩
    candidateVariable := fun _ _ => id
    candidateVariableAEMeasurable := by
      intro d a
      exact theorem25_finiteDomain_aemeasurable _ _
    stateEquation := fun d _ h _ =>
      theorem25_twoExistencePresenceRelations.relationalState d h ()
    outputEquation := fun _ _ _ _ s => s
    baselineJointAEMeasurable := by
      intro d a h
      exact theorem25_finiteDomain_aemeasurable _ _
    intervenedJointAEMeasurable := by
      intro d a h s
      exact theorem25_finiteDomain_aemeasurable _ _
    candidateIndependentOfState := ?_
  }
  intro d a h
  cases a
  change ProbabilityTheory.IndepFun (fun u : Bool => u)
    (fun _ : Bool => theorem25_twoExistencePresenceRelations.relationalState d h ())
    (ProbabilityTheory.uniformOn (Set.univ : Set Bool))
  exact ProbabilityTheory.indepFun_const_right
    (μ := ProbabilityTheory.uniformOn (Set.univ : Set Bool))
    (fun u : Bool => u)
    (theorem25_twoExistencePresenceRelations.relationalState d h ())

/-- Σと大域履歴Hを独立なBool座標としてもつ有限SCM。
ΓはHと存在dから25-B/Cの関係モデルで定め、将来出力は介入候補Σそのものとする。 -/
noncomputable def theorem25_twoExistenceGlobalHistorySCM :
    Theorem25GlobalHistorySCM Bool Unit (Bool × Bool) Bool
      (fun _ : Unit => Theorem25TwoExistenceGamma)
      (fun _ : Unit => Bool) (fun _ : Unit => Bool) := by
  classical
  let μ : MeasureTheory.ProbabilityMeasure Bool :=
    ⟨ProbabilityTheory.uniformOn (Set.univ : Set Bool), inferInstance⟩
  refine {
    exogenousLaw := fun _ _ => ⟨
      (MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
        (MeasureTheory.ProbabilityMeasure.toMeasure μ), inferInstance⟩
    globalHistory := Prod.snd
    globalHistoryAEMeasurable := by
      intro d a
      exact theorem25_finiteDomain_aemeasurable _ _
    candidateVariable := fun _ _ => Prod.fst
    candidateVariableAEMeasurable := by
      intro d a
      exact theorem25_finiteDomain_aemeasurable _ _
    stateEquation := fun d _ h _ =>
      theorem25_twoExistencePresenceRelations.relationalState d () ()
    outputEquation := fun _ _ _ _ s => s
    baselineJointAEMeasurable := by
      intro d a h
      exact theorem25_finiteDomain_aemeasurable _ _
    intervenedJointAEMeasurable := by
      intro d a h s
      exact theorem25_finiteDomain_aemeasurable _ _
    candidateIndependentOfGlobalContext := ?_
    globalContextAEMeasurable := by
      intro d a
      exact theorem25_finiteDomain_aemeasurable _ _ }
  intro d a
  change ProbabilityTheory.IndepFun
    (fun u : Bool × Bool => u.1)
    (fun u => (u.2,
      theorem25_twoExistencePresenceRelations.relationalState d () ()))
    ((MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
      (MeasureTheory.ProbabilityMeasure.toMeasure μ))
  have hprod : ProbabilityTheory.IndepFun (fun u : Bool × Bool => u.1)
      (fun u => u.2)
      ((MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
        (MeasureTheory.ProbabilityMeasure.toMeasure μ)) :=
    ProbabilityTheory.indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  exact hprod.comp measurable_id
    (measurable_id.prodMk measurable_const)

theorem theorem25_twoExistenceGlobalHistory_candidate_has_positive_mass (s : Bool) :
    theorem25_twoExistenceGlobalHistorySCM.candidateHasPositiveMass false () s := by
  classical
  refine ⟨?_, ?_⟩
  · change MeasurableSet {u : Bool × Bool | u.1 = s}
    exact measurableSet_preimage
      (measurable_fst : Measurable (fun u : Bool × Bool => u.1))
      (measurableSet_singleton s)
  change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    {u : Bool × Bool | u.1 = s} > 0
  rw [show ({u : Bool × Bool | u.1 = s} : Set (Bool × Bool)) =
      ({s} : Set Bool) ×ˢ Set.univ by ext u; simp, MeasureTheory.Measure.prod_prod]
  rw [ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ]
  rw [MeasureTheory.Measure.count_singleton, MeasureTheory.Measure.count_univ,
    ENat.card_eq_coe_fintype_card]
  cases s <;> norm_num

/-- ランダム大域履歴と候補の同時独立性を満たしていても、Σ介入が将来出力を変える
有限例がある。Γは履歴一定のため、ここでは大域独立性と25-Dの論理的独立を示す。 -/
theorem theorem25_twoExistenceGlobalHistory_hasAtman :
    Theorem25CausalModel.hasAtman
      (theorem25_twoExistenceGlobalHistorySCM.toProbabilityCausalModel.toCausalModel)
      false () := by
  classical
  refine ⟨true, ?_, ?_⟩
  · change theorem25_twoExistenceGlobalHistorySCM.candidateHasPositiveMass false () true ∧
      ProbabilityTheory.IndepFun
        (theorem25_twoExistenceGlobalHistorySCM.candidateVariable false ())
        (fun u => (theorem25_twoExistenceGlobalHistorySCM.globalHistory u,
          theorem25_twoExistenceGlobalHistorySCM.stateEquation false ()
            (theorem25_twoExistenceGlobalHistorySCM.globalHistory u) u))
        (MeasureTheory.ProbabilityMeasure.toMeasure
          (theorem25_twoExistenceGlobalHistorySCM.exogenousLaw false ()))
    exact ⟨theorem25_twoExistenceGlobalHistory_candidate_has_positive_mass true,
      theorem25_twoExistenceGlobalHistorySCM.candidateIndependentOfGlobalContext false ()⟩
  refine ⟨false, ?_⟩
  intro h
  have h' := congrArg Subtype.val h
  have h'' := congrArg
    (fun μ : MeasureTheory.Measure (Theorem25TwoExistenceGamma × Bool) =>
      μ {x | x.2 = false}) h'
  simp [theorem25_twoExistenceGlobalHistorySCM,
    Theorem25GlobalHistorySCM.toProbabilityCausalModel,
    Theorem25ProbabilityCausalModel.toCausalModel,
    MeasureTheory.ProbabilityMeasure.map,
    MeasureTheory.ProbabilityMeasure.toMeasure] at h''
  rw [show ({x : Theorem25TwoExistenceGamma × Bool | x.2 = false} :
      Set (Theorem25TwoExistenceGamma × Bool)) = Prod.snd ⁻¹' ({false} : Set Bool)
    by rfl] at h''
  rw [MeasureTheory.Measure.map_apply (by fun_prop)
    (MeasurableSet.preimage (MeasurableSet.singleton false) measurable_snd)] at h''
  have hpre :
      (fun u : Bool × Bool =>
        (theorem25_twoExistencePresenceRelations.relationalState false () (), u.1)) ⁻¹'
          Prod.snd ⁻¹' ({false} : Set Bool) = {false} ×ˢ Set.univ := by
    ext u
    simp
  rw [hpre, MeasureTheory.Measure.prod_prod] at h''
  have huniv : ({false, true} : Set Bool) = Set.univ := by
    ext b
    cases b <;> simp
  rw [huniv] at h''
  rw [ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ,
    MeasureTheory.Measure.count_singleton, MeasureTheory.Measure.count_univ,
    ENat.card_eq_coe_fintype_card] at h''
  norm_num [Fintype.card_bool] at h''

/-- 履歴Boolを関係の役割ラベルへ反映する有限25-B/C構造。
全存在は全履歴で連結しつつ、実際の関係ラベルは履歴に応じて変わる。 -/
abbrev Theorem25HistoryDependentGamma :=
  Theorem25RelationalState Bool Bool Bool (fun _ : Bool => Unit)

instance : MeasurableSpace Theorem25HistoryDependentGamma := ⊤

noncomputable def theorem25_historyDependentPresenceRelations :
    Theorem25PresenceRelationModel Bool Bool Bool Bool (fun _ : Bool => Unit) := by
  classical
  refine {
    profile := fun _ _ _ => some ()
    topMarker := ()
    topRepresentationIsSubsingleton := ?_
    supportNonempty := ?_
    supportUpwardClosed := ?_
    topLayerHasCommonMarker := ?_
    roleInverse := id
    roleInverseInvolutive := ?_
    relationEdge := fun h d _ r e _ => d ≠ e ∧ r = h
    relationEdgeReverses := ?_
    everyExistenceIsRelated := ?_
    relationGraphConnected := ?_ }
  · intro x y
    cases x
    cases y
    rfl
  · intro d h
    exact ⟨false, by simp⟩
  · intro d h a b hp hab
    simp
  · intro d h
    rfl
  · intro r
    rfl
  · intro h d a r e b
    simp [ne_comm]
  · intro h d
    cases d with
    | false => exact ⟨true, false, false, h, ⟨by decide, ⟨by decide, rfl⟩⟩⟩
    | true => exact ⟨false, false, false, h, ⟨by decide, ⟨by decide, rfl⟩⟩⟩
  · intro h d e
    cases d <;> cases e
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by decide, ⟨false, false, h, ⟨by decide, rfl⟩⟩⟩
    · exact Relation.ReflTransGen.single ⟨by decide, ⟨false, false, h, ⟨by decide, rfl⟩⟩⟩
    · exact Relation.ReflTransGen.refl

/-- 先の定理16 toy逆系の固定点値から、履歴依存25-C関係状態を実際に符号化する。
`x 0` が0/1のどちらかで履歴を復元し、presence modelのΓ状態と一致する。 -/
noncomputable def theorem25_singletonInverseLimitStateCode :
    ∀ (d : Bool) (a : Bool), (∀ i : Nat, ℝ) → Theorem25HistoryDependentGamma :=
  fun d a x =>
    if x 0 = 1 then
      theorem25_historyDependentPresenceRelations.relationalState d true a
    else theorem25_historyDependentPresenceRelations.relationalState d false a

theorem theorem25_singletonInverseLimitStateCode_matches
    (d a h : Bool) :
    theorem25_singletonInverseLimitStateCode d a
        (theorem16_singletonHistoryFixedPoints.fixedPoint h).1 =
      theorem25_historyDependentPresenceRelations.relationalState d h a := by
  have hx := (theorem16_singletonHistoryFixedPoints.fixedPoint h).2.1 0
  change (theorem16_singletonHistoryFixedPoints.fixedPoint h).1 0 ∈
    {if h then 1 else 0} at hx
  have hvalue : (theorem16_singletonHistoryFixedPoints.fixedPoint h).1 0 =
      (if h then 1 else 0) := Set.mem_singleton_iff.mp hx
  cases h <;> simp [theorem25_singletonInverseLimitStateCode, hvalue,
    theorem25_historyDependentPresenceRelations]

/-- 逆極限固定点→25-B/C3共有確率モデル→25-D→25.2 の具体的toy接続。
履歴・存在・層は有限Bool、TCZ逆系は実数上の一点集合であり、一般の認知モデルの証明ではない。
候補非干渉は出力が固定点符号化だけに依存する設計条件として置く。 -/
noncomputable def theorem25_singletonInverseLimitMeasuredC3Model :
    Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool Bool Bool Unit
      (fun _ : Bool => Unit) (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Unit) (fun _ : Bool => Unit) := by
  classical
  let law : MeasureTheory.ProbabilityMeasure Unit :=
    ⟨ProbabilityTheory.uniformOn (Set.univ : Set Unit), inferInstance⟩
  exact Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
    theorem16_singletonHistoryFixedPoints theorem25_historyDependentPresenceRelations
    theorem25_singletonInverseLimitStateCode
    theorem25_singletonInverseLimitStateCode_matches
    (fun _ _ _ => ()) law (fun _ : Unit => false)
    (fun _ _ _ => ())
    measurable_const.aemeasurable
    (by intro d a; exact measurable_const.aemeasurable)
    (by
      intro d a
      exact ProbabilityTheory.indepFun_const_left
        (μ := MeasureTheory.ProbabilityMeasure.toMeasure law) () _)
    (by intro d a; exact measurable_const.aemeasurable)
    (by
      intro d a h
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | γ.profile a = theorem25_historyDependentPresenceRelations.profile d h a}
      have hEq : {ω : Theorem25HistoryDependentGamma × Unit |
          ω.1.profile a = theorem25_historyDependentPresenceRelations.profile d h a} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, u⟩
        cases u
        rfl
      rw [hEq]
      exact (measurable_fst : Measurable
        (fun z : Theorem25HistoryDependentGamma × Unit => z.1))
          MeasurableSpace.measurableSet_top)
    (by
      intro d a h e b r
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | (γ.incidentRelation d a r e b) ↔
          theorem25_historyDependentPresenceRelations.relationEdge h d a r e b}
      have hEq : {ω : Theorem25HistoryDependentGamma × Unit |
          (ω.1.incidentRelation d a r e b) ↔
            theorem25_historyDependentPresenceRelations.relationEdge h d a r e b} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, u⟩
        cases u
        rfl
      rw [hEq]
      exact (measurable_fst : Measurable
        (fun z : Theorem25HistoryDependentGamma × Unit => z.1))
          MeasurableSpace.measurableSet_top)
    (by
      intro d a h
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | γ = theorem25_historyDependentPresenceRelations.relationalState d h a}
      have hEq : {ω : Theorem25HistoryDependentGamma × Unit |
          ω.1 = theorem25_historyDependentPresenceRelations.relationalState d h a} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, u⟩
        cases u
        rfl
      rw [hEq]
      exact (measurable_fst : Measurable
        (fun z : Theorem25HistoryDependentGamma × Unit => z.1))
          MeasurableSpace.measurableSet_top)

/-- 上のtoy構成は実際に定理25第2結論を満たす。 -/
theorem theorem25_singletonInverseLimitMeasuredC3Model_noAtman :
    ∀ d a, ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      ((Theorem25SharedGlobalHistorySCM.toIndexed
        theorem25_singletonInverseLimitMeasuredC3Model.model.scm).toProbabilityCausalModel)).hasAtman d a := by
  exact theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference
    theorem25_singletonInverseLimitMeasuredC3Model (by
      intro d a h s
      filter_upwards with u
      exact Subsingleton.elim _ _)

/-- 非退化区間TCZの逆極限固定点を、25-C3の関係状態へ写す符号化。
固定点の第0座標が履歴端点0/1であることを用いる。 -/
noncomputable def theorem25_intervalInverseLimitStateCode :
    ∀ (d : Bool) (a : Bool), (∀ i : Nat, ℝ) → Theorem25HistoryDependentGamma :=
  fun d a x =>
    if x 0 = 1 then
      theorem25_historyDependentPresenceRelations.relationalState d true a
    else theorem25_historyDependentPresenceRelations.relationalState d false a

theorem theorem25_intervalInverseLimitStateCode_matches
    (d a h : Bool) :
    theorem25_intervalInverseLimitStateCode d a
        (theorem16_intervalHistoryFixedPoints.fixedPoint h).1 =
      theorem25_historyDependentPresenceRelations.relationalState d h a := by
  have hx := theorem16_intervalHistoryFixedPoint_coordinate h
  cases h <;> simp [theorem25_intervalInverseLimitStateCode, hx,
    theorem25_historyDependentPresenceRelations]

/-- 非退化な区間TCZ逆系の固定点コードを、測度付き25-B/C3モデルへ接続する。
25-Dと25.2はこの構成では候補に依存しない出力方程式から成立するため、一般認知モデルの
構造方程式から25-Dを導いた結果ではない。 -/
noncomputable def theorem25_intervalInverseLimitMeasuredC3Model :
    Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool Bool Bool Unit
      (fun _ : Bool => Unit) (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Unit) (fun _ : Bool => Unit) := by
  classical
  let law : MeasureTheory.ProbabilityMeasure Unit :=
    ⟨ProbabilityTheory.uniformOn (Set.univ : Set Unit), inferInstance⟩
  exact Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
    theorem16_intervalHistoryFixedPoints theorem25_historyDependentPresenceRelations
    theorem25_intervalInverseLimitStateCode
    theorem25_intervalInverseLimitStateCode_matches
    (fun _ _ _ => ()) law (fun _ : Unit => false)
    (fun _ _ _ => ())
    measurable_const.aemeasurable
    (by intro d a; exact measurable_const.aemeasurable)
    (by
      intro d a
      exact ProbabilityTheory.indepFun_const_left
        (μ := MeasureTheory.ProbabilityMeasure.toMeasure law) () _)
    (by intro d a; exact measurable_const.aemeasurable)
    (by
      intro d a h
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | γ.profile a = theorem25_historyDependentPresenceRelations.profile d h a}
      have hEq : {ω : Theorem25HistoryDependentGamma × Unit |
          ω.1.profile a = theorem25_historyDependentPresenceRelations.profile d h a} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, u⟩
        cases u
        rfl
      rw [hEq]
      exact (measurable_fst : Measurable
        (fun z : Theorem25HistoryDependentGamma × Unit => z.1))
          MeasurableSpace.measurableSet_top)
    (by
      intro d a h e b r
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | (γ.incidentRelation d a r e b) ↔
          theorem25_historyDependentPresenceRelations.relationEdge h d a r e b}
      have hEq : {ω : Theorem25HistoryDependentGamma × Unit |
          (ω.1.incidentRelation d a r e b) ↔
            theorem25_historyDependentPresenceRelations.relationEdge h d a r e b} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, u⟩
        cases u
        rfl
      rw [hEq]
      exact (measurable_fst : Measurable
        (fun z : Theorem25HistoryDependentGamma × Unit => z.1))
          MeasurableSpace.measurableSet_top)
    (by
      intro d a h
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | γ = theorem25_historyDependentPresenceRelations.relationalState d h a}
      have hEq : {ω : Theorem25HistoryDependentGamma × Unit |
          ω.1 = theorem25_historyDependentPresenceRelations.relationalState d h a} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, u⟩
        cases u
        rfl
      rw [hEq]
      exact (measurable_fst : Measurable
        (fun z : Theorem25HistoryDependentGamma × Unit => z.1))
          MeasurableSpace.measurableSet_top)

/-- 非退化区間TCZモデルでも、固定点コードから構成した25.2が成立する。 -/
theorem theorem25_intervalInverseLimitMeasuredC3Model_noAtman :
    ∀ d a, ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      ((Theorem25SharedGlobalHistorySCM.toIndexed
        theorem25_intervalInverseLimitMeasuredC3Model.model.scm).toProbabilityCausalModel)).hasAtman d a := by
  exact theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference
    theorem25_intervalInverseLimitMeasuredC3Model (by
      intro d a h s
      filter_upwards with u
      exact Subsingleton.elim _ _)

/-- 勾配流版の逆極限固定点から25-C3状態を符号化する。 -/
noncomputable def theorem25_intervalGradientFlowStateCode :
    ∀ (d : Bool) (a : Bool), (∀ i : Nat, ℝ) → Theorem25HistoryDependentGamma :=
  fun d a x => if x 0 = 1 then
    theorem25_historyDependentPresenceRelations.relationalState d true a
  else theorem25_historyDependentPresenceRelations.relationalState d false a

theorem theorem25_intervalGradientFlowStateCode_matches (d a h : Bool) :
    theorem25_intervalGradientFlowStateCode d a
      (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 =
        theorem25_historyDependentPresenceRelations.relationalState d h a := by
  have hx := theorem16_intervalGradientFlowFixedPoint_coordinate h 0
  cases h <;> simp [theorem25_intervalGradientFlowStateCode, hx,
    theorem16_intervalGradientCenter, theorem25_historyDependentPresenceRelations]

/-- 強凸勾配流の逆極限固定点から構成した共有測度C3モデル。25-Dと25.2まで接続する。
候補と出力はUnit値なので、この例の因果非干渉は構成上のもの。 -/
noncomputable def theorem25_intervalGradientFlowMeasuredC3Model :
    Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool Bool Bool Unit
      (fun _ : Bool => Unit) (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Unit) (fun _ : Bool => Unit) := by
  classical
  let law : MeasureTheory.ProbabilityMeasure Unit :=
    ⟨ProbabilityTheory.uniformOn (Set.univ : Set Unit), inferInstance⟩
  exact Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
    theorem16_intervalGradientFlowFixedPoints theorem25_historyDependentPresenceRelations
    theorem25_intervalGradientFlowStateCode
    theorem25_intervalGradientFlowStateCode_matches
    (fun _ _ _ => ()) law (fun _ : Unit => false)
    (fun _ _ _ => ())
    measurable_const.aemeasurable
    (by intro d a; exact measurable_const.aemeasurable)
    (by
      intro d a
      exact ProbabilityTheory.indepFun_const_left
        (μ := MeasureTheory.ProbabilityMeasure.toMeasure law) () _)
    (by intro d a; exact measurable_const.aemeasurable)
    (by
      intro d a h
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | γ.profile a = theorem25_historyDependentPresenceRelations.profile d h a}
      have hEq : {ω : Theorem25HistoryDependentGamma × Unit |
          ω.1.profile a = theorem25_historyDependentPresenceRelations.profile d h a} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, u⟩
        cases u
        rfl
      rw [hEq]
      exact (measurable_fst :
        Measurable (fun z : Theorem25HistoryDependentGamma × Unit => z.1))
          MeasurableSpace.measurableSet_top)
    (by
      intro d a h e b r
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | (γ.incidentRelation d a r e b) ↔
          theorem25_historyDependentPresenceRelations.relationEdge h d a r e b}
      have hEq : {ω : Theorem25HistoryDependentGamma × Unit |
          (ω.1.incidentRelation d a r e b) ↔
            theorem25_historyDependentPresenceRelations.relationEdge h d a r e b} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, u⟩
        cases u
        rfl
      rw [hEq]
      exact (measurable_fst :
        Measurable (fun z : Theorem25HistoryDependentGamma × Unit => z.1))
          MeasurableSpace.measurableSet_top)
    (by
      intro d a h
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | γ = theorem25_historyDependentPresenceRelations.relationalState d h a}
      have hEq : {ω : Theorem25HistoryDependentGamma × Unit |
          ω.1 = theorem25_historyDependentPresenceRelations.relationalState d h a} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, u⟩
        cases u
        rfl
      rw [hEq]
      exact (measurable_fst :
        Measurable (fun z : Theorem25HistoryDependentGamma × Unit => z.1))
          MeasurableSpace.measurableSet_top)

theorem theorem25_intervalGradientFlowMeasuredC3Model_noAtman :
    ∀ d a, ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      ((Theorem25SharedGlobalHistorySCM.toIndexed
        theorem25_intervalGradientFlowMeasuredC3Model.model.scm).toProbabilityCausalModel)).hasAtman d a := by
  exact theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference
    theorem25_intervalGradientFlowMeasuredC3Model (by
      intro d a h s
      filter_upwards with u
      exact Subsingleton.elim _ _)

/-- 非定数候補・出力を持つ共有C3モデルを、任意のBool履歴逆極限固定点族から作る。
符号化一致と候補独立性は明示条件として受け取る。 -/
noncomputable def theorem25_intervalRandomizedMeasuredC3Model_fromFixedPoints
    (F : HistoryFixedPoints Bool (∀ i : Nat, ℝ))
    (code : ∀ (d a : Bool), (∀ i : Nat, ℝ) → Theorem25HistoryDependentGamma)
    (hCode : ∀ d a h, code d a (F.fixedPoint h).1 =
      theorem25_historyDependentPresenceRelations.relationalState d h a)
    (hOutput : ∀ h, decide ((F.fixedPoint h).1 0 = 1) = h) :
    Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool Bool Bool (Bool × Bool)
      (fun _ : Bool => Unit) (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  let μ : MeasureTheory.ProbabilityMeasure Bool :=
    ⟨ProbabilityTheory.uniformOn (Set.univ : Set Bool), inferInstance⟩
  let law : MeasureTheory.ProbabilityMeasure (Bool × Bool) :=
    ⟨(MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
      (MeasureTheory.ProbabilityMeasure.toMeasure μ), inferInstance⟩
  exact Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
    F theorem25_historyDependentPresenceRelations code hCode
    (fun _ _ x => decide (x 0 = 1)) law Prod.snd
    (fun _ _ u => u.1)
    measurable_snd.aemeasurable
    (by intro d a; exact measurable_fst.aemeasurable)
    (by
      intro d a
      change ProbabilityTheory.IndepFun (fun u : Bool × Bool => u.1)
        (fun u => (u.2, code d a (F.fixedPoint u.2).1))
        ((MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
          (MeasureTheory.ProbabilityMeasure.toMeasure μ))
      have hprod : ProbabilityTheory.IndepFun (fun u : Bool × Bool => u.1)
          (fun u => u.2)
          ((MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
            (MeasureTheory.ProbabilityMeasure.toMeasure μ)) :=
        ProbabilityTheory.indepFun_prod (X := id) (Y := id) measurable_id measurable_id
      have hcodeMeas : Measurable (fun h : Bool => code d a (F.fixedPoint h).1) :=
        measurable_of_finite _
      exact ProbabilityTheory.IndepFun.comp hprod measurable_id
        (measurable_id.prodMk hcodeMeas))
    (by intro d a; exact (measurable_of_finite _).aemeasurable)
    (by
      intro d a h
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | γ.profile a = theorem25_historyDependentPresenceRelations.profile d h a}
      have hEq : {ω : Theorem25HistoryDependentGamma × Bool |
          ω.1.profile a = theorem25_historyDependentPresenceRelations.profile d h a} =
          Prod.fst ⁻¹' B := by ext z; rcases z with ⟨γ, y⟩; rfl
      rw [hEq]
      exact (measurable_fst :
        Measurable (fun z : Theorem25HistoryDependentGamma × Bool => z.1))
          MeasurableSpace.measurableSet_top)
    (by
      intro d a h e b r
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | (γ.incidentRelation d a r e b) ↔
          theorem25_historyDependentPresenceRelations.relationEdge h d a r e b}
      have hEq : {ω : Theorem25HistoryDependentGamma × Bool |
          (ω.1.incidentRelation d a r e b) ↔
            theorem25_historyDependentPresenceRelations.relationEdge h d a r e b} =
          Prod.fst ⁻¹' B := by ext z; rcases z with ⟨γ, y⟩; rfl
      rw [hEq]
      exact (measurable_fst :
        Measurable (fun z : Theorem25HistoryDependentGamma × Bool => z.1))
          MeasurableSpace.measurableSet_top)
    (by
      intro d a h
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | γ = theorem25_historyDependentPresenceRelations.relationalState d h a}
      have hEq : {ω : Theorem25HistoryDependentGamma × Bool |
          ω.1 = theorem25_historyDependentPresenceRelations.relationalState d h a} =
          Prod.fst ⁻¹' B := by ext z; rcases z with ⟨γ, y⟩; rfl
      rw [hEq]
      exact (measurable_fst :
        Measurable (fun z : Theorem25HistoryDependentGamma × Bool => z.1))
          MeasurableSpace.measurableSet_top)

noncomputable def theorem25_intervalGradientFlowRandomizedMeasuredC3Model :
    Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool Bool Bool (Bool × Bool)
      (fun _ : Bool => Unit) (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  apply theorem25_intervalRandomizedMeasuredC3Model_fromFixedPoints
    theorem16_intervalGradientFlowFixedPoints theorem25_intervalGradientFlowStateCode
    theorem25_intervalGradientFlowStateCode_matches
  intro h
  have hx := theorem16_intervalGradientFlowFixedPoint_coordinate h 0
  cases h <;> simp [hx, theorem16_intervalGradientCenter]

/-- 同じ履歴別固定点C3-SCMを、25-A(2)の自己過程SCMとして読む射影。
外生法則・履歴変数・候補変数・状態出力の構造式を元の共有SCMからそのまま取る。 -/
noncomputable def theorem25_intervalGradientFlowRandomizedSelfProcessSCM :
    Theorem25SelfProcessSCM Bool (Bool × Bool)
      Theorem25HistoryDependentGamma Bool Bool where
  exogenousLaw := theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw
  inputHistory := theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistory
  candidateVariable := fun u =>
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm).candidateVariable
      false false u
  inputHistoryAEMeasurable :=
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistoryAEMeasurable
  candidateAEMeasurable :=
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariableAEMeasurable
      false false
  baselineEquation := fun h u =>
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation
        false false h u,
      theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation
        false false h u
        (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable
          false false u))
  intervenedEquation := fun h s u =>
    (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation
        false false h u,
      theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation
        false false h u s)
  baselineAEMeasurable :=
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.baselineJointAEMeasurable
      false false
  intervenedAEMeasurable := fun h s =>
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.intervenedJointAEMeasurable
      false false h s

/-- 上の射影で定理25-A(2)を証明する。候補と入力履歴は同じ積確率空間の
独立座標であり、介入前後の状態・出力は固定点符号化で一致する。 -/
theorem theorem25_intervalGradientFlowRandomizedSelfProcessSCM_satisfies25A2 :
    theorem25_intervalGradientFlowRandomizedSelfProcessSCM.toLawModel.Condition25A2 () := by
  apply theorem25_intervalGradientFlowRandomizedSelfProcessSCM.condition25A2
  · change ProbabilityTheory.IndepFun Prod.snd Prod.fst
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    exact (ProbabilityTheory.indepFun_prod (X := id) (Y := id)
      measurable_id measurable_id).symm
  · intro h s
    apply Subtype.ext
    change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
        (fun u : Bool × Bool =>
          (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation
              false false h u,
            theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation
              false false h u s)) =
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
        (fun u : Bool × Bool =>
          (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation
              false false h u,
            (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm).outputEquation
              false false h u
                ((theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm).candidateVariable
                  false false u)))
    rw [MeasureTheory.Measure.map_congr]
    exact Filter.Eventually.of_forall fun u => by
      simp [theorem25_intervalGradientFlowRandomizedMeasuredC3Model,
        theorem25_intervalRandomizedMeasuredC3Model_fromFixedPoints,
        Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints,
        Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints,
        theorem16_intervalGradientFlowFixedPoint_coordinate,
        theorem16_intervalGradientCenter]

theorem theorem25_intervalGradientFlowRandomizedMeasuredC3Model_noAtman :
    ∀ d a, ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      ((Theorem25SharedGlobalHistorySCM.toIndexed
        theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm).toProbabilityCausalModel)).hasAtman d a := by
  exact theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model (by
      intro d a h s
      filter_upwards with u
      simp [theorem25_intervalGradientFlowRandomizedMeasuredC3Model,
        theorem25_intervalRandomizedMeasuredC3Model_fromFixedPoints,
        Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints,
        Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints])

theorem theorem25_intervalGradientFlowRandomized_candidate_has_positive_mass
    (s : Bool) :
    Theorem25GlobalHistorySCM.candidateHasPositiveMass
      (theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.toIndexed)
      false false s := by
  classical
  refine ⟨?_, ?_⟩
  · change MeasurableSet {u : Bool × Bool | u.1 = s}
    exact measurableSet_preimage (measurable_fst : Measurable (fun u : Bool × Bool => u.1))
      (measurableSet_singleton s)
  change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    {u : Bool × Bool | u.1 = s} > 0
  rw [show ({u : Bool × Bool | u.1 = s} : Set (Bool × Bool)) =
      ({s} : Set Bool) ×ˢ Set.univ by ext u; simp, MeasureTheory.Measure.prod_prod]
  rw [ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ]
  rw [MeasureTheory.Measure.count_singleton, MeasureTheory.Measure.count_univ,
    ENat.card_eq_coe_fintype_card]
  cases s <;> norm_num

theorem theorem25_intervalGradientFlowRandomized_output_eq_history
    (d a h : Bool) (u : Bool × Bool) (s : Bool) :
    theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation
      d a h u s = h := by
  cases h <;> simp [theorem25_intervalGradientFlowRandomizedMeasuredC3Model,
    theorem25_intervalRandomizedMeasuredC3Model_fromFixedPoints,
    Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints,
    Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints,
    theorem16_intervalGradientFlowFixedPoint_coordinate,
    theorem16_intervalGradientCenter]

/-- 候補と履歴を独立なBool座標として持ち、固定点由来の出力を履歴に応じて0/1へ変える。
したがって候補変数・将来出力はいずれも非定数だが、do介入は固定点由来出力を変えない。 -/
noncomputable def theorem25_intervalInverseLimitRandomizedMeasuredC3Model :
    Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool Bool Bool (Bool × Bool)
      (fun _ : Bool => Unit) (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  let μ : MeasureTheory.ProbabilityMeasure Bool :=
    ⟨ProbabilityTheory.uniformOn (Set.univ : Set Bool), inferInstance⟩
  let law : MeasureTheory.ProbabilityMeasure (Bool × Bool) :=
    ⟨(MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
      (MeasureTheory.ProbabilityMeasure.toMeasure μ), inferInstance⟩
  exact Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
    theorem16_intervalHistoryFixedPoints theorem25_historyDependentPresenceRelations
    theorem25_intervalInverseLimitStateCode theorem25_intervalInverseLimitStateCode_matches
    (fun _ _ x => decide (x 0 = 1)) law Prod.snd
    (fun _ _ u => u.1)
    measurable_snd.aemeasurable
    (by intro d a; exact measurable_fst.aemeasurable)
    (by
      intro d a
      change ProbabilityTheory.IndepFun
        (fun u : Bool × Bool => u.1)
        (fun u => (u.2,
          theorem25_intervalInverseLimitStateCode d a
            (theorem16_intervalHistoryFixedPoints.fixedPoint u.2).1))
        ((MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
          (MeasureTheory.ProbabilityMeasure.toMeasure μ))
      have hprod : ProbabilityTheory.IndepFun (fun u : Bool × Bool => u.1)
          (fun u => u.2)
          ((MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
            (MeasureTheory.ProbabilityMeasure.toMeasure μ)) :=
        ProbabilityTheory.indepFun_prod (X := id) (Y := id) measurable_id measurable_id
      have hcode : Measurable (fun h : Bool =>
          theorem25_intervalInverseLimitStateCode d a
            (theorem16_intervalHistoryFixedPoints.fixedPoint h).1) :=
        measurable_of_finite _
      have hcontextMap : Measurable (fun h : Bool =>
          (h, theorem25_intervalInverseLimitStateCode d a
            (theorem16_intervalHistoryFixedPoints.fixedPoint h).1)) :=
        measurable_id.prodMk hcode
      exact ProbabilityTheory.IndepFun.comp hprod measurable_id hcontextMap)
    (by intro d a; exact (measurable_of_finite _).aemeasurable)
    (by
      intro d a h
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | γ.profile a = theorem25_historyDependentPresenceRelations.profile d h a}
      have hEq : {ω : Theorem25HistoryDependentGamma × Bool |
          ω.1.profile a = theorem25_historyDependentPresenceRelations.profile d h a} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, y⟩
        rfl
      rw [hEq]
      exact (measurable_fst :
        Measurable (fun z : Theorem25HistoryDependentGamma × Bool => z.1))
          MeasurableSpace.measurableSet_top)
    (by
      intro d a h e b r
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | (γ.incidentRelation d a r e b) ↔
          theorem25_historyDependentPresenceRelations.relationEdge h d a r e b}
      have hEq : {ω : Theorem25HistoryDependentGamma × Bool |
          (ω.1.incidentRelation d a r e b) ↔
            theorem25_historyDependentPresenceRelations.relationEdge h d a r e b} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, y⟩
        rfl
      rw [hEq]
      exact (measurable_fst :
        Measurable (fun z : Theorem25HistoryDependentGamma × Bool => z.1))
          MeasurableSpace.measurableSet_top)
    (by
      intro d a h
      let B : Set Theorem25HistoryDependentGamma :=
        {γ | γ = theorem25_historyDependentPresenceRelations.relationalState d h a}
      have hEq : {ω : Theorem25HistoryDependentGamma × Bool |
          ω.1 = theorem25_historyDependentPresenceRelations.relationalState d h a} =
          Prod.fst ⁻¹' B := by
        ext z
        rcases z with ⟨γ, y⟩
        rfl
      rw [hEq]
      exact (measurable_fst :
        Measurable (fun z : Theorem25HistoryDependentGamma × Bool => z.1))
          MeasurableSpace.measurableSet_top)

/-- 非定数候補・履歴依存出力を持つ区間逆系C3モデルでも、25-Dから25.2が従う。 -/
theorem theorem25_intervalInverseLimitRandomizedMeasuredC3Model_noAtman :
    ∀ d a, ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      ((Theorem25SharedGlobalHistorySCM.toIndexed
        theorem25_intervalInverseLimitRandomizedMeasuredC3Model.model.scm).toProbabilityCausalModel)).hasAtman d a := by
  exact theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference
    theorem25_intervalInverseLimitRandomizedMeasuredC3Model (by
      intro d a h s
      filter_upwards with u
      simp [theorem25_intervalInverseLimitRandomizedMeasuredC3Model,
        Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints,
        Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints])

/-- このモデルの候補は各値に正確率を持つため、25.2は候補値の空事象化に頼らない。 -/
theorem theorem25_intervalInverseLimitRandomized_candidate_has_positive_mass
    (s : Bool) :
    Theorem25GlobalHistorySCM.candidateHasPositiveMass
      (theorem25_intervalInverseLimitRandomizedMeasuredC3Model.model.scm.toIndexed)
      false false s := by
  classical
  refine ⟨?_, ?_⟩
  · change MeasurableSet {u : Bool × Bool | u.1 = s}
    exact measurableSet_preimage
      (measurable_fst : Measurable (fun u : Bool × Bool => u.1))
      (measurableSet_singleton s)
  change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    {u : Bool × Bool | u.1 = s} > 0
  rw [show ({u : Bool × Bool | u.1 = s} : Set (Bool × Bool)) =
      ({s} : Set Bool) ×ˢ Set.univ by ext u; simp, MeasureTheory.Measure.prod_prod]
  rw [ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ]
  rw [MeasureTheory.Measure.count_singleton, MeasureTheory.Measure.count_univ,
    ENat.card_eq_coe_fintype_card]
  cases s <;> norm_num

/-- 各履歴下の候補介入値に依らず、将来出力は逆極限固定点の端点値に等しい。
従って出力は履歴false/trueで0/1と変わる一方、候補介入では変化しない。 -/
theorem theorem25_intervalInverseLimitRandomized_output_eq_history
    (d a h : Bool) (u : Bool × Bool) (s : Bool) :
    theorem25_intervalInverseLimitRandomizedMeasuredC3Model.model.scm.outputEquation
      d a h u s = h := by
  cases h <;> simp [theorem25_intervalInverseLimitRandomizedMeasuredC3Model,
    Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints,
    Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints,
    theorem16_intervalHistoryFixedPoint_coordinate]

/-- 履歴に応じてΓの役割辺が変わる大域履歴SCM。
候補Σは大域履歴と履歴別Γの組から独立な直積座標である。 -/
noncomputable def theorem25_historyDependentGlobalSCM :
    Theorem25GlobalHistorySCM Bool Bool (Bool × Bool) Bool
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  let μ : MeasureTheory.ProbabilityMeasure Bool :=
    ⟨ProbabilityTheory.uniformOn (Set.univ : Set Bool), inferInstance⟩
  refine {
    exogenousLaw := fun _ _ => ⟨
      (MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
        (MeasureTheory.ProbabilityMeasure.toMeasure μ), inferInstance⟩
    globalHistory := Prod.snd
    globalHistoryAEMeasurable := by
      intro d a
      exact theorem25_finiteDomain_aemeasurable _ _
    candidateVariable := fun _ _ => Prod.fst
    candidateVariableAEMeasurable := by
      intro d a
      exact theorem25_finiteDomain_aemeasurable _ _
    stateEquation := fun d a h _ =>
      theorem25_historyDependentPresenceRelations.relationalState d h a
    outputEquation := fun _ _ _ _ s => s
    baselineJointAEMeasurable := by
      intro d a h
      exact theorem25_finiteDomain_aemeasurable _ _
    intervenedJointAEMeasurable := by
      intro d a h s
      exact theorem25_finiteDomain_aemeasurable _ _
    candidateIndependentOfGlobalContext := ?_
    globalContextAEMeasurable := by
      intro d a
      exact theorem25_finiteDomain_aemeasurable _ _ }
  intro d a
  change ProbabilityTheory.IndepFun
    (fun u : Bool × Bool => u.1)
    (fun u => (u.2,
      theorem25_historyDependentPresenceRelations.relationalState d u.2 a))
    ((MeasureTheory.ProbabilityMeasure.toMeasure μ).prod
      (MeasureTheory.ProbabilityMeasure.toMeasure μ))
  exact ProbabilityTheory.indepFun_prod (X := id)
    (Y := fun h : Bool =>
      (h, theorem25_historyDependentPresenceRelations.relationalState d h a))
    measurable_id (measurable_of_finite _)

/-- 主体断面 `d=false` では候補介入が出力法則を変えない一方、
別の存在 `d=true` では候補が因果的に作用する大域履歴SCM。 -/
noncomputable def theorem25_selfSliceA2GlobalSCM :
    Theorem25GlobalHistorySCM Bool Bool (Bool × Bool) Bool
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) :=
  { theorem25_historyDependentGlobalSCM with
    outputEquation := fun d _ _ _ s => if d then s else false
    baselineJointAEMeasurable := by
      intro d a h
      exact theorem25_finiteDomain_aemeasurable _ _
    intervenedJointAEMeasurable := by
      intro d a h s
      exact theorem25_finiteDomain_aemeasurable _ _ }

/-- γを自己過程表現として読む場合、固定主体断面 `d=false` では
25-A(2)型の `(Γ,Y⁺)` 同時法則不変性が全履歴・候補値で成立する。 -/
theorem theorem25_selfSliceA2GlobalSCM_satisfies_selfA2 :
    ∀ a h s,
      (theorem25_selfSliceA2GlobalSCM.toProbabilityCausalModel).intervenedJointLaw
          false a h s =
        (theorem25_selfSliceA2GlobalSCM.toProbabilityCausalModel).baselineJointLaw
          false a h := by
  intro a h s
  apply Subtype.ext
  change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
      (fun u : Bool × Bool =>
        (theorem25_historyDependentPresenceRelations.relationalState false h a, false)) =
    ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
      (fun u : Bool × Bool =>
        (theorem25_historyDependentPresenceRelations.relationalState false h a, false))
  rfl

/-- 25-B/C3統合型へ渡すため、A(2)変種のSCMを一つの外生法則共有型にする。 -/
noncomputable def theorem25_selfSliceA2SharedSCM :
    Theorem25SharedGlobalHistorySCM Bool Bool (Bool × Bool) Bool
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  let μ := theorem25_selfSliceA2GlobalSCM.exogenousLaw false false
  exact theorem25_selfSliceA2GlobalSCM.toShared μ (by
    intro d a
    rfl) (theorem25_finiteDomain_aemeasurable _ _)
    (by intro d a; exact theorem25_finiteDomain_aemeasurable _ _)

/-- 25-Dを課さない履歴依存SCMも、全索引で同じ一様積法則を使う共有法則型にできる。 -/
noncomputable def theorem25_historyDependentSharedSCM :
    Theorem25SharedGlobalHistorySCM Bool Bool (Bool × Bool) Bool
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  let μ := theorem25_historyDependentGlobalSCM.exogenousLaw false false
  exact theorem25_historyDependentGlobalSCM.toShared μ (by
    intro d a
    rfl) (theorem25_finiteDomain_aemeasurable _ _)
    (by intro d a; exact theorem25_finiteDomain_aemeasurable _ _)

private noncomputable def theorem25_uniformBool : MeasureTheory.Measure Bool :=
  ProbabilityTheory.uniformOn (Set.univ : Set Bool)

/-- 有限離散空間上の一様法則は、任意の同型な可測全単射で保存される。
有限群の平行移動が一様ノイズの対称性となる際の基礎補題。 -/
theorem theorem25_uniformUniv_measurePreserving_of_equiv
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
    (e : Ω ≃ Ω) (he : Measurable e) :
    MeasureTheory.MeasurePreserving e
      (ProbabilityTheory.uniformOn (Set.univ : Set Ω))
      (ProbabilityTheory.uniformOn (Set.univ : Set Ω)) := by
  refine ⟨he, ?_⟩
  apply MeasureTheory.Measure.ext
  intro s hs
  rw [MeasureTheory.Measure.map_apply he hs,
    ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ,
    MeasureTheory.Measure.count_apply (hs.preimage he),
    MeasureTheory.Measure.count_apply hs,
    Set.encard_preimage_of_bijective e.bijective]

/-- 有限加法群の一様ノイズは平行移動で不変。有限群ノイズの候補依存な
再配置を構成するとき、Bool xor に依存しない一般形として用いる。 -/
theorem theorem25_uniformUniv_addTranslation_measurePreserving
    {G : Type*} [AddGroup G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [Fintype G] (g : G) :
    MeasureTheory.MeasurePreserving (fun x : G => x + g)
      (ProbabilityTheory.uniformOn (Set.univ : Set G))
      (ProbabilityTheory.uniformOn (Set.univ : Set G)) := by
  let e : G ≃ G :=
    { toFun := fun x => x + g
      invFun := fun x => x - g
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  exact theorem25_uniformUniv_measurePreserving_of_equiv e
    (measurable_of_finite _)

/-- Bool一様法則は、固定ビットとのxorで保存される。 -/
private theorem theorem25_boolXorMeasurePreserving (b : Bool) :
    MeasureTheory.MeasurePreserving (fun x : Bool => xor x b)
      theorem25_uniformBool theorem25_uniformBool := by
  cases b with
  | false =>
      convert (MeasureTheory.MeasurePreserving.id theorem25_uniformBool) using 1
      funext x
      cases x <;> rfl
  | true =>
      have hnotFun : (fun x : Bool => !x) = Equiv.boolNot := by
        funext x
        cases x <;> rfl
      have hnot : MeasureTheory.MeasurePreserving (fun x : Bool => !x)
          theorem25_uniformBool theorem25_uniformBool := by
        rw [hnotFun]
        exact theorem25_uniformUniv_measurePreserving_of_equiv Equiv.boolNot
          (measurable_of_finite _)
      convert hnot using 1
      funext x
      cases x <;> rfl

/-- 候補値は出力方程式に実際に入るが、独立な一様ノイズがあるため、
候補介入後も `(Γ,Y⁺)` の同時法則が変わらない共有法則SCM。 -/
noncomputable def theorem25_historyDependentMaskingSharedSCM :
    Theorem25SharedGlobalHistorySCM Bool Bool (Bool × (Bool × Bool)) Bool
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  letI : MeasureTheory.IsProbabilityMeasure theorem25_uniformBool :=
    ProbabilityTheory.isProbabilityMeasure_uniformOn' Set.finite_univ Set.univ_nonempty .univ
  let μ : MeasureTheory.ProbabilityMeasure Bool :=
    ⟨theorem25_uniformBool, inferInstance⟩
  refine {
    exogenousLaw := ⟨μ.toMeasure.prod (μ.toMeasure.prod μ.toMeasure), inferInstance⟩
    globalHistory := fun u => u.2.1
    globalHistoryAEMeasurable := by
      exact theorem25_finiteDomain_aemeasurable _ _
    candidateVariable := fun _ _ u => u.1
    candidateVariableAEMeasurable := by
      intro d a
      exact theorem25_finiteDomain_aemeasurable _ _
    stateEquation := fun d a h _ =>
      theorem25_historyDependentPresenceRelations.relationalState d h a
    outputEquation := fun _ _ _ u s => xor s u.2.2
    baselineJointAEMeasurable := by
      intro d a h
      exact theorem25_finiteDomain_aemeasurable _ _
    intervenedJointAEMeasurable := by
      intro d a h s
      exact theorem25_finiteDomain_aemeasurable _ _
    candidateIndependentOfGlobalContext := ?_
    globalContextAEMeasurable := by
      intro d a
      exact theorem25_finiteDomain_aemeasurable _ _ }
  intro d a
  change ProbabilityTheory.IndepFun
    (fun u : Bool × (Bool × Bool) => u.1)
    (fun u => (u.2.1,
      theorem25_historyDependentPresenceRelations.relationalState d u.2.1 a))
    (μ.toMeasure.prod (μ.toMeasure.prod μ.toMeasure))
  exact ProbabilityTheory.indepFun_prod (X := id)
    (Y := fun v : Bool × Bool =>
      (v.1, theorem25_historyDependentPresenceRelations.relationalState d v.1 a))
    measurable_id (measurable_of_finite _)

/-- ノイズ座標を候補値に応じてxor変換する写像は、独立な一様積法則を保存する。 -/
private theorem theorem25_maskingChange_measurePreserving (s : Bool) :
    MeasureTheory.MeasurePreserving
      (fun u : Bool × (Bool × Bool) =>
        (u.1, (u.2.1, xor u.2.2 (xor u.1 s))))
      (theorem25_uniformBool.prod
        (theorem25_uniformBool.prod theorem25_uniformBool))
      (theorem25_uniformBool.prod
        (theorem25_uniformBool.prod theorem25_uniformBool)) := by
  letI : MeasureTheory.IsProbabilityMeasure theorem25_uniformBool :=
    ProbabilityTheory.isProbabilityMeasure_uniformOn' Set.finite_univ Set.univ_nonempty .univ
  have hbase : MeasureTheory.MeasurePreserving id theorem25_uniformBool theorem25_uniformBool :=
    MeasureTheory.MeasurePreserving.id theorem25_uniformBool
  have hfiber (c : Bool) : MeasureTheory.MeasurePreserving
      (fun v : Bool × Bool => (v.1, xor v.2 (xor c s)))
      (theorem25_uniformBool.prod theorem25_uniformBool)
      (theorem25_uniformBool.prod theorem25_uniformBool) := by
    exact hbase.prod (theorem25_boolXorMeasurePreserving (xor c s))
  apply hbase.skew_product
    (g := fun (c : Bool) (v : Bool × Bool) => (v.1, xor v.2 (xor c s)))
    (by fun_prop)
  filter_upwards with c
  exact (hfiber c).map_eq

/-- マスキング構造方程式の候補介入を基準過程へ移す外生ノイズの測度保存対称性。 -/
theorem theorem25_historyDependentMaskingSharedSCM_measurePreservingSymmetry :
    ∀ d a h s,
      ∃ τ : Bool × (Bool × Bool) → Bool × (Bool × Bool),
        MeasureTheory.MeasurePreserving τ
          (MeasureTheory.ProbabilityMeasure.toMeasure
            theorem25_historyDependentMaskingSharedSCM.exogenousLaw)
          (MeasureTheory.ProbabilityMeasure.toMeasure
            theorem25_historyDependentMaskingSharedSCM.exogenousLaw) ∧
        Measurable τ ∧
        Measurable (fun u =>
          (theorem25_historyDependentMaskingSharedSCM.stateEquation d a h u,
            theorem25_historyDependentMaskingSharedSCM.outputEquation d a h u
              (theorem25_historyDependentMaskingSharedSCM.candidateVariable d a u))) ∧
        Measurable (fun u =>
          (theorem25_historyDependentMaskingSharedSCM.stateEquation d a h u,
            theorem25_historyDependentMaskingSharedSCM.outputEquation d a h u s)) ∧
        (∀ u, (theorem25_historyDependentMaskingSharedSCM.stateEquation d a h (τ u),
          theorem25_historyDependentMaskingSharedSCM.outputEquation d a h (τ u) s) =
            (theorem25_historyDependentMaskingSharedSCM.stateEquation d a h u,
              theorem25_historyDependentMaskingSharedSCM.outputEquation d a h u
                (theorem25_historyDependentMaskingSharedSCM.candidateVariable d a u))) := by
  intro d a h s
  let τ : Bool × (Bool × Bool) → Bool × (Bool × Bool) := fun u =>
    (u.1, (u.2.1, xor u.2.2 (xor u.1 s)))
  refine ⟨τ, ?_, ?_, ?_, ?_, ?_⟩
  · exact theorem25_maskingChange_measurePreserving s
  · fun_prop
  · fun_prop
  · fun_prop
  · intro u
    rcases u with ⟨c, h', n⟩
    cases c <;> cases h' <;> cases n <;> cases s <;> rfl

/-- ノイズマスキングの構造方程式から全履歴・全候補介入について25-Dを導く。 -/
theorem theorem25_historyDependentMaskingSharedSCM_satisfies25D :
    ∀ d a h s,
      Theorem25ProbabilityCausalModel.intervenedJointLaw
          ((theorem25_historyDependentMaskingSharedSCM.toIndexed).toProbabilityCausalModel)
          d a h s =
        Theorem25ProbabilityCausalModel.baselineJointLaw
          ((theorem25_historyDependentMaskingSharedSCM.toIndexed).toProbabilityCausalModel)
          d a h :=
  theorem25_globalHistorySCM_functionalCompleteness_of_measurePreservingSymmetry
    (theorem25_historyDependentMaskingSharedSCM.toIndexed)
    theorem25_historyDependentMaskingSharedSCM_measurePreservingSymmetry

/-- 25-Dの分布不変性にもかかわらず、候補値が変われば同じ外生点の出力は変わり得る。 -/
theorem theorem25_historyDependentMaskingSharedSCM_output_depends_on_candidate
    (d a : Bool) (h : Bool) :
    ∃ u : Bool × (Bool × Bool),
      theorem25_historyDependentMaskingSharedSCM.outputEquation d a h u false ≠
        theorem25_historyDependentMaskingSharedSCM.outputEquation d a h u true := by
  refine ⟨(false, (h, false)), ?_⟩
  change false ≠ true
  decide

/-- 自然候補値での出力と do 介入後の出力が、同じ外生点で食い違う例が各索引にある。
したがって25-Dの分布不変性は、構造方程式上の点ごとの因果作用までは否定しない。 -/
theorem theorem25_historyDependentMaskingSharedSCM_intervention_changes_output_pointwise
    (d a h : Bool) :
    ∃ u : Bool × (Bool × Bool), ∃ s : Bool,
      theorem25_historyDependentMaskingSharedSCM.outputEquation d a h u s ≠
        theorem25_historyDependentMaskingSharedSCM.outputEquation d a h u
          (theorem25_historyDependentMaskingSharedSCM.candidateVariable d a u) := by
  refine ⟨(false, (h, false)), true, ?_⟩
  change true ≠ false
  decide

/-- マスキングSCMの25-Dから全存在・全層の25.2を導く。 -/
theorem theorem25_historyDependentMaskingSharedSCM_noAtman :
    ∀ d a, ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      ((theorem25_historyDependentMaskingSharedSCM.toIndexed).toProbabilityCausalModel)).hasAtman d a := by
  apply theorem25_secondConclusion_of_probabilityFunctionalCompleteness
  exact theorem25_historyDependentMaskingSharedSCM_satisfies25D

/-- マスキングSCMの関係状態は、強凸勾配流から得た定理16の履歴別逆極限固定点を
`theorem25_intervalGradientFlowStateCode` で符号化した値に一致する。したがって同じ
モデル内で、定理16の固定点→25-C3のΓ状態→対称性による25-D→25.2の接続を検査できる。 -/
theorem theorem25_historyDependentMaskingSharedSCM_state_is_theorem16Code
    (d a h : Bool) (u : Bool × (Bool × Bool)) :
    theorem25_historyDependentMaskingSharedSCM.stateEquation d a h u =
      theorem25_intervalGradientFlowStateCode d a
        (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 := by
  change theorem25_historyDependentPresenceRelations.relationalState d h a = _
  exact (theorem25_intervalGradientFlowStateCode_matches d a h).symm

private theorem theorem25_uniformBoolProduct_measure_univ :
    ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool))) Set.univ = 1 :=
  MeasureTheory.measure_univ

theorem theorem25_historyDependentGlobalSCM_candidate_has_positive_mass (s : Bool) :
    theorem25_historyDependentGlobalSCM.candidateHasPositiveMass false false s := by
  classical
  refine ⟨?_, ?_⟩
  · change MeasurableSet {u : Bool × Bool | u.1 = s}
    exact measurableSet_preimage
      (measurable_fst : Measurable (fun u : Bool × Bool => u.1))
      (measurableSet_singleton s)
  change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    {u : Bool × Bool | u.1 = s} > 0
  rw [show ({u : Bool × Bool | u.1 = s} : Set (Bool × Bool)) =
      ({s} : Set Bool) ×ˢ Set.univ by ext u; simp, MeasureTheory.Measure.prod_prod]
  rw [ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ]
  rw [MeasureTheory.Measure.count_singleton, MeasureTheory.Measure.count_univ,
    ENat.card_eq_coe_fintype_card]
  cases s <;> norm_num

theorem theorem25_selfSliceA2GlobalSCM_candidate_has_positive_mass
    (d a s : Bool) :
    theorem25_selfSliceA2GlobalSCM.candidateHasPositiveMass d a s := by
  classical
  refine ⟨?_, ?_⟩
  · change MeasurableSet {u : Bool × Bool | u.1 = s}
    exact measurableSet_preimage
      (measurable_fst : Measurable (fun u : Bool × Bool => u.1))
      (measurableSet_singleton s)
  change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    {u : Bool × Bool | u.1 = s} > 0
  rw [show ({u : Bool × Bool | u.1 = s} : Set (Bool × Bool)) =
      ({s} : Set Bool) ×ˢ Set.univ by ext u; simp, MeasureTheory.Measure.prod_prod]
  rw [ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ]
  rw [MeasureTheory.Measure.count_singleton, MeasureTheory.Measure.count_univ,
    ENat.card_eq_coe_fintype_card]
  cases s <;> norm_num

/-- 履歴依存Γを持つSCMでも、大域独立性と候補介入の因果効果が両立する。 -/
theorem theorem25_historyDependentGlobalSCM_hasAtman :
    Theorem25CausalModel.hasAtman
      (theorem25_historyDependentGlobalSCM.toProbabilityCausalModel.toCausalModel)
      false false := by
  classical
  refine ⟨true, ?_, ?_⟩
  · change theorem25_historyDependentGlobalSCM.candidateHasPositiveMass false false true ∧
      ProbabilityTheory.IndepFun
        (theorem25_historyDependentGlobalSCM.candidateVariable false false)
        (fun u => (theorem25_historyDependentGlobalSCM.globalHistory u,
          theorem25_historyDependentGlobalSCM.stateEquation false false
            (theorem25_historyDependentGlobalSCM.globalHistory u) u))
        (MeasureTheory.ProbabilityMeasure.toMeasure
          (theorem25_historyDependentGlobalSCM.exogenousLaw false false))
    exact ⟨theorem25_historyDependentGlobalSCM_candidate_has_positive_mass true,
      theorem25_historyDependentGlobalSCM.candidateIndependentOfGlobalContext false false⟩
  refine ⟨false, ?_⟩
  intro h
  have h' := congrArg Subtype.val h
  have h'' := congrArg
    (fun μ : MeasureTheory.Measure (Theorem25HistoryDependentGamma × Bool) =>
      μ {x | x.2 = false}) h'
  simp [theorem25_historyDependentGlobalSCM,
    Theorem25GlobalHistorySCM.toProbabilityCausalModel,
    Theorem25ProbabilityCausalModel.toCausalModel,
    MeasureTheory.ProbabilityMeasure.map,
    MeasureTheory.ProbabilityMeasure.toMeasure] at h''
  rw [show ({x : Theorem25HistoryDependentGamma × Bool | x.2 = false} :
      Set (Theorem25HistoryDependentGamma × Bool)) = Prod.snd ⁻¹' ({false} : Set Bool)
    by rfl] at h''
  rw [MeasureTheory.Measure.map_apply (by fun_prop)
    (MeasurableSet.preimage (MeasurableSet.singleton false) measurable_snd)] at h''
  have hpre :
      (fun u : Bool × Bool =>
        (theorem25_historyDependentPresenceRelations.relationalState false false false,
          u.1)) ⁻¹' Prod.snd ⁻¹' ({false} : Set Bool) = {false} ×ˢ Set.univ := by
    ext u
    simp
  rw [hpre, MeasureTheory.Measure.prod_prod] at h''
  have huniv : ({false, true} : Set Bool) = Set.univ := by
    ext b
    cases b <;> simp
  rw [huniv] at h''
  rw [ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ,
    MeasureTheory.Measure.count_singleton, MeasureTheory.Measure.count_univ,
    ENat.card_eq_coe_fintype_card] at h''
  norm_num [Fintype.card_bool] at h''

/-- ランダム候補Σが実際に大域履歴・関係状態から独立なSCMでも、
主体断面の25-A(2)型不変性は別存在のAtman効果を排除しない。 -/
theorem theorem25_selfSliceA2GlobalSCM_hasAtman_elsewhere :
    Theorem25CausalModel.hasAtman
      (theorem25_selfSliceA2GlobalSCM.toProbabilityCausalModel.toCausalModel)
      true false := by
  classical
  refine ⟨true, ?_, ?_⟩
  · change theorem25_selfSliceA2GlobalSCM.candidateHasPositiveMass true false true ∧
      ProbabilityTheory.IndepFun
        (theorem25_selfSliceA2GlobalSCM.candidateVariable true false)
        (fun u => (theorem25_selfSliceA2GlobalSCM.globalHistory u,
          theorem25_selfSliceA2GlobalSCM.stateEquation true false
            (theorem25_selfSliceA2GlobalSCM.globalHistory u) u))
        (MeasureTheory.ProbabilityMeasure.toMeasure
          (theorem25_selfSliceA2GlobalSCM.exogenousLaw true false))
    exact ⟨theorem25_selfSliceA2GlobalSCM_candidate_has_positive_mass true false true,
      theorem25_historyDependentGlobalSCM.candidateIndependentOfGlobalContext true false⟩
  refine ⟨false, ?_⟩
  intro h
  have h' := congrArg Subtype.val h
  have h'' := congrArg
    (fun μ : MeasureTheory.Measure (Theorem25HistoryDependentGamma × Bool) =>
      μ {x | x.2 = false}) h'
  simp [theorem25_selfSliceA2GlobalSCM,
    theorem25_historyDependentGlobalSCM,
    Theorem25GlobalHistorySCM.toProbabilityCausalModel,
    Theorem25ProbabilityCausalModel.toCausalModel,
    MeasureTheory.ProbabilityMeasure.map,
    MeasureTheory.ProbabilityMeasure.toMeasure] at h''
  rw [show ({x : Theorem25HistoryDependentGamma × Bool | x.2 = false} :
      Set (Theorem25HistoryDependentGamma × Bool)) =
      Prod.snd ⁻¹' ({false} : Set Bool) by rfl] at h''
  rw [MeasureTheory.Measure.map_apply (by fun_prop)
    (MeasurableSet.preimage (MeasurableSet.singleton false) measurable_snd)] at h''
  have hpre :
      (fun u : Bool × Bool =>
        (theorem25_historyDependentPresenceRelations.relationalState true false false,
          u.1)) ⁻¹' Prod.snd ⁻¹' ({false} : Set Bool) = {false} ×ˢ Set.univ := by
    ext u
    simp
  rw [hpre, MeasureTheory.Measure.prod_prod] at h''
  have huniv : ({false, true} : Set Bool) = Set.univ := by
    ext b
    cases b <;> simp
  rw [huniv] at h''
  rw [ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ,
    MeasureTheory.Measure.count_singleton, MeasureTheory.Measure.count_univ,
    ENat.card_eq_coe_fintype_card] at h''
  norm_num [Fintype.card_bool] at h''

/-- 25-C3の辺成分を調べると、二つの履歴におけるΓ状態は異なる。 -/
theorem theorem25_historyDependentGamma_distinguishes_histories :
    theorem25_historyDependentPresenceRelations.relationalState false false false ≠
      theorem25_historyDependentPresenceRelations.relationalState false true false := by
  intro heq
  have h := congrArg (fun state : Theorem25HistoryDependentGamma =>
    state.incidentRelation false false false true false) heq
  simp [Theorem25PresenceRelationModel.relationalState,
    theorem25_historyDependentPresenceRelations] at h

/-- 履歴依存大域SCMを25-B/C3統合型へ束ねる。 Γはリレーショナル状態そのものであり、
基準生成法則のもとでプロファイル・辺・完全状態の各観測が確率1で一致する。 -/
noncomputable def theorem25_historyDependentGlobalC3Model :
    Theorem25C3IntegratedModel Bool Bool Bool Bool (fun _ : Bool => Unit)
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  refine ⟨?_, (fun _ _ _ state => state), (fun _ _ _ state => state), ?_, ?_⟩
  · refine ⟨?_, theorem25_historyDependentPresenceRelations,
      (fun a state => state.profile a),
      (fun _ state d a r e b => state.incidentRelation d a r e b), ?_, ?_⟩
    · exact theorem25_historyDependentGlobalSCM.toProbabilityCausalModel
    · intro d a h
      dsimp [Theorem25GlobalHistorySCM.toProbabilityCausalModel,
        theorem25_historyDependentGlobalSCM,
        MeasureTheory.ProbabilityMeasure.map,
        MeasureTheory.ProbabilityMeasure.toMeasure]
      change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
          (fun u : Bool × Bool =>
            (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1))
          {ω | ω.1.profile a =
            theorem25_historyDependentPresenceRelations.profile d h a} = 1
      have hset : MeasurableSet
          {ω : Theorem25HistoryDependentGamma × Bool |
            ω.1.profile a = theorem25_historyDependentPresenceRelations.profile d h a} :=
        MeasurableSet.preimage
          (MeasurableSpace.measurableSet_top (s :=
            {g : Theorem25HistoryDependentGamma |
              g.profile a = theorem25_historyDependentPresenceRelations.profile d h a}))
          measurable_fst
      rw [MeasureTheory.Measure.map_apply (measurable_const.prodMk measurable_fst) hset]
      have hpre :
          (fun u : Bool × Bool =>
            (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1)) ⁻¹'
              {ω : Theorem25HistoryDependentGamma × Bool |
                ω.1.profile a =
                  theorem25_historyDependentPresenceRelations.profile d h a} = Set.univ := by
        ext u
        simp [Theorem25PresenceRelationModel.relationalState]
      rw [hpre]
      exact theorem25_uniformBoolProduct_measure_univ
    · intro d a h e b r
      dsimp [Theorem25GlobalHistorySCM.toProbabilityCausalModel,
        theorem25_historyDependentGlobalSCM,
        MeasureTheory.ProbabilityMeasure.map,
        MeasureTheory.ProbabilityMeasure.toMeasure]
      change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
          (fun u : Bool × Bool =>
            (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1))
          {ω | (ω.1.incidentRelation d a r e b) ↔
            theorem25_historyDependentPresenceRelations.relationEdge h d a r e b} = 1
      have hset : MeasurableSet
          {ω : Theorem25HistoryDependentGamma × Bool |
            (ω.1.incidentRelation d a r e b) ↔
              theorem25_historyDependentPresenceRelations.relationEdge h d a r e b} :=
        MeasurableSet.preimage
          (MeasurableSpace.measurableSet_top (s :=
            {g : Theorem25HistoryDependentGamma |
              (g.incidentRelation d a r e b) ↔
                theorem25_historyDependentPresenceRelations.relationEdge h d a r e b}))
          measurable_fst
      rw [MeasureTheory.Measure.map_apply (measurable_const.prodMk measurable_fst) hset]
      have hpre :
          (fun u : Bool × Bool =>
            (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1)) ⁻¹'
              {ω : Theorem25HistoryDependentGamma × Bool |
                (ω.1.incidentRelation d a r e b) ↔
                  theorem25_historyDependentPresenceRelations.relationEdge h d a r e b} =
            Set.univ := by
        ext u
        simp [Theorem25PresenceRelationModel.relationalState,
          theorem25_historyDependentPresenceRelations, ne_comm]
      rw [hpre]
      exact theorem25_uniformBoolProduct_measure_univ
  · intro d a h state
    rfl
  · intro d a h
    change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
        (fun u : Bool × Bool =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1))
        {ω | ω.1 = theorem25_historyDependentPresenceRelations.relationalState d h a} = 1
    have hset : MeasurableSet
        {ω : Theorem25HistoryDependentGamma × Bool |
          ω.1 = theorem25_historyDependentPresenceRelations.relationalState d h a} :=
      MeasurableSet.preimage
        (MeasurableSpace.measurableSet_top (s :=
          {g : Theorem25HistoryDependentGamma |
            g = theorem25_historyDependentPresenceRelations.relationalState d h a}))
        measurable_fst
    rw [MeasureTheory.Measure.map_apply (measurable_const.prodMk measurable_fst) hset]
    have hpre :
        (fun u : Bool × Bool =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1)) ⁻¹'
            {ω : Theorem25HistoryDependentGamma × Bool |
              ω.1 = theorem25_historyDependentPresenceRelations.relationalState d h a} =
          Set.univ := by
      ext u
      simp
    rw [hpre]
    exact theorem25_uniformBoolProduct_measure_univ

/-- 履歴依存の有限C3反例では、B/C3基準観測イベントが実際に可測である。 -/
theorem theorem25_historyDependentGlobalC3Model_observationEventsMeasurable :
    theorem25_historyDependentGlobalC3Model.ObservationEventsMeasurable := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro d a h
    exact MeasurableSet.preimage
      (MeasurableSpace.measurableSet_top (s :=
        {g : Theorem25HistoryDependentGamma |
          g.profile a = theorem25_historyDependentPresenceRelations.profile d h a}))
      measurable_fst

  · intro d a h e b r
    exact MeasurableSet.preimage
      (MeasurableSpace.measurableSet_top (s :=
        {g : Theorem25HistoryDependentGamma |
          (g.incidentRelation d a r e b) ↔
            theorem25_historyDependentPresenceRelations.relationEdge h d a r e b}))
      measurable_fst
  · intro d a h
    exact MeasurableSet.preimage
      (MeasurableSpace.measurableSet_top (s :=
        {g : Theorem25HistoryDependentGamma |
          g = theorem25_historyDependentPresenceRelations.relationalState d h a}))
      measurable_fst

private theorem theorem25_historyDependentGamma_prodBool_eventMeasurable
    (P : Theorem25HistoryDependentGamma → Prop) :
    MeasurableSet {ω : Theorem25HistoryDependentGamma × Bool | P ω.1} := by
  exact MeasurableSet.preimage
    (MeasurableSpace.measurableSet_top (s := {g : Theorem25HistoryDependentGamma | P g}))
    measurable_fst

/-- 25-Dを課さない履歴依存B/C3例も、同じ一様積法則の共有C3型に束ねる。
これにより25-B/C3と大域法則共有だけでは25.2に足りないことを具体例で示す。 -/
noncomputable def theorem25_historyDependentSharedC3Model :
    Theorem25SharedGlobalHistoryC3Model Bool Bool Bool Bool (Bool × Bool)
      (fun _ : Bool => Unit)
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  let old := theorem25_historyDependentGlobalC3Model
  let shared := theorem25_historyDependentSharedSCM
  let P := (shared.toIndexed).toProbabilityCausalModel
  have hbase (d : Bool) (a : Bool) (h : Bool) :
      P.baselineJointLaw d a h = old.integrated.probability.baselineJointLaw d a h := by
    apply Subtype.ext
    change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
        (fun u : Bool × Bool =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1)) =
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
        (fun u : Bool × Bool =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1))
    rfl
  refine ⟨shared, old.integrated.presenceAndRelations,
    old.integrated.profileObservation, old.integrated.relationObservation,
    old.relationalStateObservation, old.encodeRelationalState,
    old.relationalStateObservation_encode, ?_, ?_, ?_⟩
  · intro d a h
    rw [hbase]
    exact old.integrated.baselineProfileCoherent d a h
  · intro d a h e b r
    rw [hbase]
    exact old.integrated.baselineRelationsCoherent d a h e b r
  · intro d a h
    rw [hbase]
    exact old.baselineRelationalStateCoherent d a h

private theorem theorem25_uniformBoolTriple_measure_univ :
    ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))) Set.univ = 1 :=
  MeasureTheory.measure_univ

/-- ノイズマスキングSCMを25-B/C3の観測統合型にも接続する。
観測事象はΓ成分だけで決まり、状態方程式は全外生点で関係状態そのものなので、
候補依存の出力ノイズがあっても基準観測の確率1整合は維持される。 -/
noncomputable def theorem25_historyDependentMaskingSharedC3Model :
    Theorem25SharedGlobalHistoryC3Model Bool Bool Bool Bool
      (Bool × (Bool × Bool))
      (fun _ : Bool => Unit)
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  let old := theorem25_historyDependentGlobalC3Model
  refine ⟨theorem25_historyDependentMaskingSharedSCM,
    old.integrated.presenceAndRelations, old.integrated.profileObservation,
    old.integrated.relationObservation, old.relationalStateObservation,
    old.encodeRelationalState, old.relationalStateObservation_encode, ?_, ?_, ?_⟩
  · intro d a h
    change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))).map
        (fun u : Bool × (Bool × Bool) =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a,
            xor u.1 u.2.2))
        {ω | old.integrated.profileObservation a ω.1 =
          old.integrated.presenceAndRelations.profile d h a} = 1
    have hset : MeasurableSet
        {ω : Theorem25HistoryDependentGamma × Bool |
          old.integrated.profileObservation a ω.1 =
            old.integrated.presenceAndRelations.profile d h a} :=
      MeasurableSet.preimage
        (MeasurableSpace.measurableSet_top (s :=
          {g : Theorem25HistoryDependentGamma |
            old.integrated.profileObservation a g =
              old.integrated.presenceAndRelations.profile d h a})) measurable_fst
    rw [MeasureTheory.Measure.map_apply (measurable_const.prodMk (measurable_of_finite _)) hset]
    have hpre :
        (fun u : Bool × (Bool × Bool) =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a,
            xor u.1 u.2.2)) ⁻¹'
          {ω : Theorem25HistoryDependentGamma × Bool |
            old.integrated.profileObservation a ω.1 =
              old.integrated.presenceAndRelations.profile d h a} = Set.univ := by
      ext u
      simp [old, theorem25_historyDependentGlobalC3Model,
        Theorem25PresenceRelationModel.relationalState,
        theorem25_historyDependentPresenceRelations]
    rw [hpre]
    exact theorem25_uniformBoolTriple_measure_univ
  · intro d a h e b r
    change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))).map
        (fun u : Bool × (Bool × Bool) =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a,
            xor u.1 u.2.2))
        {ω | old.integrated.relationObservation a ω.1 d a r e b ↔
          old.integrated.presenceAndRelations.relationEdge h d a r e b} = 1
    have hset : MeasurableSet
        {ω : Theorem25HistoryDependentGamma × Bool |
          old.integrated.relationObservation a ω.1 d a r e b ↔
            old.integrated.presenceAndRelations.relationEdge h d a r e b} :=
      MeasurableSet.preimage
        (MeasurableSpace.measurableSet_top (s :=
          {g : Theorem25HistoryDependentGamma |
            old.integrated.relationObservation a g d a r e b ↔
              old.integrated.presenceAndRelations.relationEdge h d a r e b})) measurable_fst
    rw [MeasureTheory.Measure.map_apply (measurable_const.prodMk (measurable_of_finite _)) hset]
    have hpre :
        (fun u : Bool × (Bool × Bool) =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a,
            xor u.1 u.2.2)) ⁻¹'
          {ω : Theorem25HistoryDependentGamma × Bool |
            old.integrated.relationObservation a ω.1 d a r e b ↔
              old.integrated.presenceAndRelations.relationEdge h d a r e b} = Set.univ := by
      ext u
      simp [old, theorem25_historyDependentGlobalC3Model,
        Theorem25PresenceRelationModel.relationalState,
        theorem25_historyDependentPresenceRelations, ne_comm]
    rw [hpre]
    exact theorem25_uniformBoolTriple_measure_univ
  · intro d a h
    change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))).map
        (fun u : Bool × (Bool × Bool) =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a,
            xor u.1 u.2.2))
        {ω | old.relationalStateObservation d a h ω.1 =
          old.integrated.presenceAndRelations.relationalState d h a} = 1
    have hset : MeasurableSet
        {ω : Theorem25HistoryDependentGamma × Bool |
          old.relationalStateObservation d a h ω.1 =
            old.integrated.presenceAndRelations.relationalState d h a} :=
      MeasurableSet.preimage
        (MeasurableSpace.measurableSet_top (s :=
          {g : Theorem25HistoryDependentGamma |
            old.relationalStateObservation d a h g =
              old.integrated.presenceAndRelations.relationalState d h a})) measurable_fst
    rw [MeasureTheory.Measure.map_apply (measurable_const.prodMk (measurable_of_finite _)) hset]
    have hpre :
        (fun u : Bool × (Bool × Bool) =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a,
            xor u.1 u.2.2)) ⁻¹'
          {ω : Theorem25HistoryDependentGamma × Bool |
            old.relationalStateObservation d a h ω.1 =
              old.integrated.presenceAndRelations.relationalState d h a} = Set.univ := by
      ext u
      simp [old, theorem25_historyDependentGlobalC3Model,
        Theorem25PresenceRelationModel.relationalState]
    rw [hpre]
    exact theorem25_uniformBoolTriple_measure_univ

/-- ノイズマスキングC3モデルの観測イベントは有限離散状態型上で可測である。 -/
theorem theorem25_historyDependentMaskingSharedC3Model_observationEventsMeasurable :
    theorem25_historyDependentMaskingSharedC3Model.ObservationEventsMeasurable := by
  refine ⟨?_, ?_, ?_⟩
  · intro d a h
    exact MeasurableSet.preimage
      (MeasurableSpace.measurableSet_top (s :=
        {g : Theorem25HistoryDependentGamma |
          theorem25_historyDependentMaskingSharedC3Model.profileObservation a g =
            theorem25_historyDependentMaskingSharedC3Model.presenceAndRelations.profile d h a}))
      measurable_fst
  · intro d a h e b r
    exact MeasurableSet.preimage
      (MeasurableSpace.measurableSet_top (s :=
        {g : Theorem25HistoryDependentGamma |
          (theorem25_historyDependentMaskingSharedC3Model.relationObservation a g d a r e b) ↔
            theorem25_historyDependentMaskingSharedC3Model.presenceAndRelations.relationEdge
              h d a r e b}))
      measurable_fst
  · intro d a h
    exact MeasurableSet.preimage
      (MeasurableSpace.measurableSet_top (s :=
        {g : Theorem25HistoryDependentGamma |
          theorem25_historyDependentMaskingSharedC3Model.relationalStateObservation d a h g =
            theorem25_historyDependentMaskingSharedC3Model.presenceAndRelations.relationalState
              d h a}))
      measurable_fst

/-- ノイズマスキング例を、確率1のC3観測イベント可測性を備えた型へ持ち上げる。 -/
noncomputable def theorem25_historyDependentMaskingMeasuredSharedC3Model :
    Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool Bool Bool
      (Bool × (Bool × Bool))
      (fun _ : Bool => Unit)
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) :=
  ⟨theorem25_historyDependentMaskingSharedC3Model,
    theorem25_historyDependentMaskingSharedC3Model_observationEventsMeasurable⟩

/-- C3観測統合済みのノイズマスキング例でも、25-Dから定理25第2結論が従う。 -/
theorem theorem25_historyDependentMaskingSharedC3Model_noAtman :
    ∀ d a, ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      ((theorem25_historyDependentMaskingSharedC3Model.scm.toIndexed).toProbabilityCausalModel)).hasAtman d a := by
  exact (theorem25_measurePreservingSymmetry_preservesSharedC3Observations
    theorem25_historyDependentMaskingMeasuredSharedC3Model
    theorem25_historyDependentMaskingSharedSCM_measurePreservingSymmetry).1

/-- マスキング例では、候補介入後もプロファイル・関係辺・完全Γ観測がすべて確率1で
基準C3構造に一致する。25.2と同じ対称性合成定理の観測整合成分である。 -/
theorem theorem25_historyDependentMaskingSharedC3Model_c3CoherentAfterIntervention :
    ∀ d a h s,
      MeasureTheory.ProbabilityMeasure.toMeasure
        ((theorem25_historyDependentMaskingMeasuredSharedC3Model.model.scm.toIndexed.toProbabilityCausalModel).intervenedJointLaw
          d a h s)
        {ω | theorem25_historyDependentMaskingMeasuredSharedC3Model.model.profileObservation
          a ω.1 = theorem25_historyDependentMaskingMeasuredSharedC3Model.model.presenceAndRelations.profile
            d h a} = 1 ∧
      (∀ e b r, MeasureTheory.ProbabilityMeasure.toMeasure
        ((theorem25_historyDependentMaskingMeasuredSharedC3Model.model.scm.toIndexed.toProbabilityCausalModel).intervenedJointLaw
          d a h s)
        {ω | theorem25_historyDependentMaskingMeasuredSharedC3Model.model.relationObservation
          a ω.1 d a r e b ↔
            theorem25_historyDependentMaskingMeasuredSharedC3Model.model.presenceAndRelations.relationEdge
              h d a r e b} = 1) ∧
      MeasureTheory.ProbabilityMeasure.toMeasure
        ((theorem25_historyDependentMaskingMeasuredSharedC3Model.model.scm.toIndexed.toProbabilityCausalModel).intervenedJointLaw
          d a h s)
        {ω | theorem25_historyDependentMaskingMeasuredSharedC3Model.model.relationalStateObservation
          d a h ω.1 =
            theorem25_historyDependentMaskingMeasuredSharedC3Model.model.presenceAndRelations.relationalState
              d h a} = 1 := by
  exact (theorem25_measurePreservingSymmetry_preservesSharedC3Observations
    theorem25_historyDependentMaskingMeasuredSharedC3Model
    theorem25_historyDependentMaskingSharedSCM_measurePreservingSymmetry).2

/-- 25-B/C3の確率1整合を束ねた後も、大域独立候補はAtman効果を持てる。 -/
theorem theorem25_historyDependentGlobalC3Model_hasAtman :
    Theorem25CausalModel.hasAtman
      (theorem25_historyDependentGlobalC3Model.integrated.probability.toCausalModel)
      false false := by
  simpa [theorem25_historyDependentGlobalC3Model] using
    theorem25_historyDependentGlobalSCM_hasAtman

theorem theorem25_historyDependentSharedSCM_hasAtman :
    Theorem25CausalModel.hasAtman
      (Theorem25ProbabilityCausalModel.toCausalModel
        ((theorem25_historyDependentSharedSCM.toIndexed).toProbabilityCausalModel))
      false false := by
  change Theorem25CausalModel.hasAtman
    (theorem25_historyDependentGlobalSCM.toProbabilityCausalModel.toCausalModel)
    false false
  exact theorem25_historyDependentGlobalSCM_hasAtman

theorem theorem25_historyDependentSharedC3Model_hasAtman :
    Theorem25CausalModel.hasAtman
      (Theorem25ProbabilityCausalModel.toCausalModel
        ((theorem25_historyDependentSharedC3Model.scm.toIndexed).toProbabilityCausalModel))
      false false := by
  change Theorem25CausalModel.hasAtman
    (Theorem25ProbabilityCausalModel.toCausalModel
      ((theorem25_historyDependentSharedSCM.toIndexed).toProbabilityCausalModel))
    false false
  exact theorem25_historyDependentSharedSCM_hasAtman

/-- 同じ履歴依存25-B/C3関係構造で、出力を候補Σに非依存とした比較SCM。
これは25-A(2)/25-Dを構造方程式で実現した条件付きモデルである。 -/
noncomputable def theorem25_historyDependentFunctionallyCompleteSCM :
    Theorem25GlobalHistorySCM Bool Bool (Bool × Bool) Bool
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) :=
  { theorem25_historyDependentGlobalSCM with
    outputEquation := fun _ _ _ _ _ => false
    baselineJointAEMeasurable := by
      intro d a h
      exact theorem25_finiteDomain_aemeasurable _ _
    intervenedJointAEMeasurable := by
      intro d a h s
      exact theorem25_finiteDomain_aemeasurable _ _ }

theorem theorem25_historyDependentFunctionallyCompleteSCM_satisfies25D :
    ∀ d a h s,
      (theorem25_historyDependentFunctionallyCompleteSCM.toProbabilityCausalModel).intervenedJointLaw
          d a h s =
        (theorem25_historyDependentFunctionallyCompleteSCM.toProbabilityCausalModel).baselineJointLaw
          d a h := by
  apply theorem25_globalHistorySCM_functionalCompleteness_of_ae_candidateIrrelevance
  intro d a h s
  filter_upwards with u
  rfl

/-- 履歴依存25-B/C3構造のまま25-Dを課すと、定理25第2結論が成立する。 -/
theorem theorem25_historyDependentFunctionallyCompleteSCM_noAtman :
    ∀ d a,
      ¬ Theorem25CausalModel.hasAtman
        ((theorem25_historyDependentFunctionallyCompleteSCM.toProbabilityCausalModel).toCausalModel)
        d a := by
  apply theorem25_secondConclusion_of_globalHistorySCM_ae_candidateIrrelevance
  intro d a h s
  filter_upwards with u
  rfl

/-- 履歴依存B/C3機能完備例を、全存在・層で単一外生法則を共有する型へ移す。 -/
noncomputable def theorem25_historyDependentFunctionallyCompleteSharedSCM :
    Theorem25SharedGlobalHistorySCM Bool Bool (Bool × Bool) Bool
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  let μ := theorem25_historyDependentGlobalSCM.exogenousLaw false false
  exact theorem25_historyDependentFunctionallyCompleteSCM.toShared μ (by
    intro d a
    rfl) (theorem25_finiteDomain_aemeasurable _ _)
    (by intro d a; exact theorem25_finiteDomain_aemeasurable _ _)

/-- Bool履歴を固定点値として返す、各履歴で一意な固定点族。
これは有限の整合性例であり、定理16の逆極限条件からこの族を構成したとは主張しない。 -/
def theorem25_historyIndexedBoolFixedPoints : HistoryFixedPoints Bool Bool where
  carrier := fun _ _ => True
  feedback := fun h _ => ⟨h, trivial⟩
  fixedPoint := fun h => ⟨h, trivial⟩
  isFixed := by
    intro h
    apply Subtype.ext
    rfl
  unique := by
    intro h y hy
    apply Subtype.ext
    exact (congrArg Subtype.val hy).symm

/-- 履歴別固定点が異なるという25-A(1)型の条件を満たす有限固定点族。 -/
theorem theorem25_historyIndexedBoolFixedPoints_separate :
    (theorem25_historyIndexedBoolFixedPoints.fixedPoint false).1 ≠
      (theorem25_historyIndexedBoolFixedPoints.fixedPoint true).1 := by
  simp [theorem25_historyIndexedBoolFixedPoints]

/-- 履歴ごとの固定点値を将来出力として記録する共有法則SCM。
基準出力を履歴 `h` とし、候補介入後も同じ `h` を返すので25-Dが成立する。
有限モデルで履歴固定点の「現行過程」出力と、25-Dの介入不変性が両立することを示す。 -/
noncomputable def theorem25_historyDependentFixedPointSharedSCM :
    Theorem25SharedGlobalHistorySCM Bool Bool (Bool × Bool) Bool
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  refine { theorem25_historyDependentFunctionallyCompleteSharedSCM with
    outputEquation := fun _ _ h _ _ => h
    baselineJointAEMeasurable := ?_
    intervenedJointAEMeasurable := ?_ }
  · intro d a h
    exact theorem25_finiteDomain_aemeasurable _ _
  · intro d a h s
    exact theorem25_finiteDomain_aemeasurable _ _

/-- この有限SCMの将来出力は、同じ履歴添字の一意固定点値そのものである。 -/
theorem theorem25_historyDependentFixedPointSharedSCM_output_is_fixedPoint :
    ∀ d a h u s,
      theorem25_historyDependentFixedPointSharedSCM.outputEquation d a h u s =
        (theorem25_historyIndexedBoolFixedPoints.fixedPoint h).1 := by
  intro d a h u s
  rfl

/-- 定理16の履歴別逆極限固定点をBool出力へ読むと、25のSCMが同じ履歴で
記録する固定点出力と一致する。出力の二値化は第0層が1であるかで行う。 -/
theorem theorem25_historyDependentFixedPointSharedSCM_output_is_inverseLimitFixedPoint :
    ∀ d a h u s,
      theorem25_historyDependentFixedPointSharedSCM.outputEquation d a h u s =
        decide ((theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 0 = 1) := by
  intro d a h u s
  change h = decide ((theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 0 = 1)
  cases h <;>
    simp [theorem16_intervalGradientFlowFixedPoint_coordinate,
      theorem16_intervalGradientCenter]

/-- 履歴ごとの逆極限固定点は実際に異なり、25-SCMの出力二値化も異なる。
この等式は、別に作ったBool固定点の族ではなく定理16の層系から得た値を使う。 -/
theorem theorem25_historyDependentFixedPointSharedSCM_inverseLimitOutputs_separate :
    decide ((theorem16_intervalGradientFlowFixedPoints.fixedPoint false).1 0 = 1) ≠
      decide ((theorem16_intervalGradientFlowFixedPoints.fixedPoint true).1 0 = 1) := by
  simp [theorem16_intervalGradientFlowFixedPoint_coordinate,
    theorem16_intervalGradientCenter]

/-- 同じ履歴付きSCMでは、任意の主体・層・履歴で候補介入が
`(Γ,Y⁺)` の同時法則を変えない。したがって固定点由来の出力接続と25-A(2)が両立する。 -/
theorem theorem25_historyDependentFixedPointSharedSCM_satisfies_selfProcessA2 :
    ∀ d a h s,
      (theorem25_historyDependentFixedPointSharedSCM.toIndexed.toProbabilityCausalModel).intervenedJointLaw
          d a h s =
        (theorem25_historyDependentFixedPointSharedSCM.toIndexed.toProbabilityCausalModel).baselineJointLaw
          d a h := by
  intro d a h s
  apply Subtype.ext
  change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
      (fun u : Bool × Bool =>
        (theorem25_historyDependentPresenceRelations.relationalState d h a, h)) =
    ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
      (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
      (fun u : Bool × Bool =>
        (theorem25_historyDependentPresenceRelations.relationalState d h a, h))
  rfl

/-- 同SCMのΓ状態方程式は、25-B/C関係モデルから作る全C3状態そのもの。 -/
theorem theorem25_historyDependentFixedPointSharedSCM_state_is_relationalState :
    ∀ d a h u,
      theorem25_historyDependentFixedPointSharedSCM.stateEquation d a h u =
        theorem25_historyDependentPresenceRelations.relationalState d h a := by
  intro d a h u
  rfl

theorem theorem25_historyDependentFixedPointSharedSCM_satisfies25D :
    ∀ d a h s,
      Theorem25ProbabilityCausalModel.intervenedJointLaw
          (theorem25_historyDependentFixedPointSharedSCM.toIndexed.toProbabilityCausalModel)
          d a h s =
        Theorem25ProbabilityCausalModel.baselineJointLaw
          (theorem25_historyDependentFixedPointSharedSCM.toIndexed.toProbabilityCausalModel)
          d a h := by
  apply theorem25_globalHistorySCM_functionalCompleteness_of_ae_candidateIrrelevance
    theorem25_historyDependentFixedPointSharedSCM.toIndexed
  intro d a h s
  filter_upwards with u
  rfl

theorem theorem25_historyDependentFixedPointSharedSCM_noAtman :
    ∀ d a,
      ¬ (Theorem25CausalModel.hasAtman
        (Theorem25ProbabilityCausalModel.toCausalModel
          (theorem25_historyDependentFixedPointSharedSCM.toIndexed.toProbabilityCausalModel))
        d a) := by
  apply theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance
  intro d a h s
  filter_upwards with u
  rfl

/-- 一つの有限な履歴添字のもとで、25-A(1)型の履歴別固定点差と、B/C履歴関係状態・
25-D・25.2を同時に実現する整合性証人。A1の固定点族自体は逆極限モデルではないため、
定理16のモデル構成まで完了したものとは区別する。 -/
theorem theorem25_jointFiniteConsistency_witness :
    (theorem25_historyIndexedBoolFixedPoints.fixedPoint false).1 ≠
      (theorem25_historyIndexedBoolFixedPoints.fixedPoint true).1 ∧
    (∀ d a h u,
      theorem25_historyDependentFixedPointSharedSCM.stateEquation d a h u =
        theorem25_historyDependentPresenceRelations.relationalState d h a) ∧
    (∀ d a h s,
      Theorem25ProbabilityCausalModel.intervenedJointLaw
          (theorem25_historyDependentFixedPointSharedSCM.toIndexed.toProbabilityCausalModel)
          d a h s =
        Theorem25ProbabilityCausalModel.baselineJointLaw
          (theorem25_historyDependentFixedPointSharedSCM.toIndexed.toProbabilityCausalModel)
          d a h) ∧
    (∀ d a,
      ¬ Theorem25CausalModel.hasAtman
        (Theorem25ProbabilityCausalModel.toCausalModel
          (theorem25_historyDependentFixedPointSharedSCM.toIndexed.toProbabilityCausalModel))
        d a) := by
  exact ⟨theorem25_historyIndexedBoolFixedPoints_separate,
    theorem25_historyDependentFixedPointSharedSCM_state_is_relationalState,
    theorem25_historyDependentFixedPointSharedSCM_satisfies25D,
    theorem25_historyDependentFixedPointSharedSCM_noAtman⟩

theorem theorem25_historyDependentFunctionallyCompleteSharedSCM_noAtman :
    ∀ d a,
      ¬ (Theorem25ProbabilityCausalModel.toCausalModel
        ((theorem25_historyDependentFunctionallyCompleteSharedSCM.toIndexed).toProbabilityCausalModel)).hasAtman d a := by
  apply theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance
    theorem25_historyDependentFunctionallyCompleteSharedSCM
  intro d a h s
  filter_upwards with u
  rfl

/-- 同じ第一成分をもつ二つの積値写像は、第一成分だけで定まる事象に同じ測度を与える。 -/
private theorem measure_map_prod_fst_event_congr
    {Ω Γ O : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace O]
    (μ : MeasureTheory.Measure Ω) (f g : Ω → Γ × O) (A : Set Γ)
    (hf : Measurable f) (hg : Measurable g) (hA : MeasurableSet A)
    (hfst : ∀ ω, (f ω).1 = (g ω).1) :
    μ.map f (Prod.fst ⁻¹' A) = μ.map g (Prod.fst ⁻¹' A) := by
  rw [MeasureTheory.Measure.map_apply hf (MeasurableSet.preimage hA measurable_fst)]
  rw [MeasureTheory.Measure.map_apply hg (MeasurableSet.preimage hA measurable_fst)]
  congr 1
  ext ω
  simp [hfst ω]

/-- A(2)変種と既存C3モデルは、Γ観測事象上で同じ測度を持つ。 -/
private theorem theorem25_selfSliceA2_baselineObservation_eq
    (d a h : Bool) (A : Set Theorem25HistoryDependentGamma)
    (hA : MeasurableSet A) :
    MeasureTheory.ProbabilityMeasure.toMeasure
        ((theorem25_selfSliceA2SharedSCM.toIndexed.toProbabilityCausalModel).baselineJointLaw
          d a h) (Prod.fst ⁻¹' A) =
      MeasureTheory.ProbabilityMeasure.toMeasure
        (theorem25_historyDependentGlobalC3Model.integrated.probability.baselineJointLaw
          d a h) (Prod.fst ⁻¹' A) := by
  change (MeasureTheory.ProbabilityMeasure.toMeasure
      (theorem25_historyDependentGlobalSCM.exogenousLaw d a)).map
        (fun u : Bool × Bool =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a,
            if d then u.1 else false)) (Prod.fst ⁻¹' A) =
    (MeasureTheory.ProbabilityMeasure.toMeasure
      (theorem25_historyDependentGlobalSCM.exogenousLaw d a)).map
        (fun u : Bool × Bool =>
          (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1))
        (Prod.fst ⁻¹' A)
  exact measure_map_prod_fst_event_congr _ _ _ _
    (measurable_const.prodMk (measurable_of_finite _))
    (measurable_const.prodMk measurable_fst) hA (by intro u; rfl)

/-- 自己スライスA(2)と25-B/C3観測整合を同じ共有法則SCMに束ねた具体例。 -/
noncomputable def theorem25_selfSliceA2GlobalC3Model :
    Theorem25SharedGlobalHistoryC3Model Bool Bool Bool Bool (Bool × Bool)
      (fun _ : Bool => Unit)
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  let old := theorem25_historyDependentGlobalC3Model
  refine ⟨theorem25_selfSliceA2SharedSCM,
    old.integrated.presenceAndRelations, old.integrated.profileObservation,
    old.integrated.relationObservation, old.relationalStateObservation,
    old.encodeRelationalState, old.relationalStateObservation_encode, ?_, ?_, ?_⟩
  · intro d a h
    let A : Set Theorem25HistoryDependentGamma :=
      {g | old.integrated.profileObservation a g =
        old.integrated.presenceAndRelations.profile d h a}
    have hEq := theorem25_selfSliceA2_baselineObservation_eq d a h A
      (MeasurableSpace.measurableSet_top (s := A))
    have hEq' :
        MeasureTheory.ProbabilityMeasure.toMeasure
            ((theorem25_selfSliceA2SharedSCM.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h)
            {ω | old.integrated.profileObservation a ω.1 =
              old.integrated.presenceAndRelations.profile d h a} =
          MeasureTheory.ProbabilityMeasure.toMeasure
            (old.integrated.probability.baselineJointLaw d a h)
            {ω | old.integrated.profileObservation a ω.1 =
              old.integrated.presenceAndRelations.profile d h a} := by
      simpa [A] using hEq
    rw [hEq']
    exact old.integrated.baselineProfileCoherent d a h
  · intro d a h e b r
    let A : Set Theorem25HistoryDependentGamma :=
      {g | old.integrated.relationObservation a g d a r e b ↔
        old.integrated.presenceAndRelations.relationEdge h d a r e b}
    have hEq := theorem25_selfSliceA2_baselineObservation_eq d a h A
      (MeasurableSpace.measurableSet_top (s := A))
    have hEq' :
        MeasureTheory.ProbabilityMeasure.toMeasure
            ((theorem25_selfSliceA2SharedSCM.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h)
            {ω | old.integrated.relationObservation a ω.1 d a r e b ↔
              old.integrated.presenceAndRelations.relationEdge h d a r e b} =
          MeasureTheory.ProbabilityMeasure.toMeasure
            (old.integrated.probability.baselineJointLaw d a h)
            {ω | old.integrated.relationObservation a ω.1 d a r e b ↔
              old.integrated.presenceAndRelations.relationEdge h d a r e b} := by
      simpa [A] using hEq
    rw [hEq']
    exact old.integrated.baselineRelationsCoherent d a h e b r
  · intro d a h
    let A : Set Theorem25HistoryDependentGamma :=
      {g | old.relationalStateObservation d a h g =
        old.integrated.presenceAndRelations.relationalState d h a}
    have hEq := theorem25_selfSliceA2_baselineObservation_eq d a h A
      (MeasurableSpace.measurableSet_top (s := A))
    have hEq' :
        MeasureTheory.ProbabilityMeasure.toMeasure
            ((theorem25_selfSliceA2SharedSCM.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h)
            {ω | old.relationalStateObservation d a h ω.1 =
              old.integrated.presenceAndRelations.relationalState d h a} =
          MeasureTheory.ProbabilityMeasure.toMeasure
            (old.integrated.probability.baselineJointLaw d a h)
            {ω | old.relationalStateObservation d a h ω.1 =
              old.integrated.presenceAndRelations.relationalState d h a} := by
      simpa [A] using hEq
    rw [hEq']
    exact old.baselineRelationalStateCoherent d a h

/-- 統合C3モデルでも自己スライスA(2)は成立する。 -/
theorem theorem25_selfSliceA2GlobalC3Model_satisfies_selfA2 :
    ∀ a h s,
      (theorem25_selfSliceA2GlobalC3Model.scm.toIndexed.toProbabilityCausalModel).intervenedJointLaw
          false a h s =
        (theorem25_selfSliceA2GlobalC3Model.scm.toIndexed.toProbabilityCausalModel).baselineJointLaw
          false a h := by
  exact theorem25_selfSliceA2GlobalSCM_satisfies_selfA2

/-- C3観測整合と自己スライスA(2)を保つ統合例でも別存在にはAtmanがある。 -/
theorem theorem25_selfSliceA2GlobalC3Model_hasAtman_elsewhere :
    (theorem25_selfSliceA2GlobalC3Model.scm.toIndexed.toProbabilityCausalModel
      ).toCausalModel.hasAtman true false := by
  exact theorem25_selfSliceA2GlobalSCM_hasAtman_elsewhere

/-- 25-D成立SCMにも25-B/C3の完全な基準観測整合を束ねる。
候補出力を置き換えても、Γ周辺法則は同じ状態方程式から生成される。 -/
noncomputable def theorem25_historyDependentFunctionallyCompleteC3Model :
    Theorem25C3IntegratedModel Bool Bool Bool Bool (fun _ : Bool => Unit)
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  let old := theorem25_historyDependentGlobalC3Model
  refine ⟨?_, old.relationalStateObservation, old.encodeRelationalState,
    old.relationalStateObservation_encode, ?_⟩
  · refine ⟨theorem25_historyDependentFunctionallyCompleteSCM.toProbabilityCausalModel,
      old.integrated.presenceAndRelations, old.integrated.profileObservation,
      old.integrated.relationObservation, ?_, ?_⟩
    · intro d a h
      have hEq :
          MeasureTheory.ProbabilityMeasure.toMeasure
              ((theorem25_historyDependentFunctionallyCompleteSCM.toProbabilityCausalModel).baselineJointLaw
                d a h)
              {ω | old.integrated.profileObservation a ω.1 =
                old.integrated.presenceAndRelations.profile d h a} =
            MeasureTheory.ProbabilityMeasure.toMeasure
              (old.integrated.probability.baselineJointLaw d a h)
              {ω | old.integrated.profileObservation a ω.1 =
                old.integrated.presenceAndRelations.profile d h a} := by
        change (MeasureTheory.ProbabilityMeasure.toMeasure
            (theorem25_historyDependentGlobalSCM.exogenousLaw d a)).map
            (fun u : Bool × Bool =>
              (theorem25_historyDependentPresenceRelations.relationalState d h a, false))
            (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
              old.integrated.profileObservation a g =
                old.integrated.presenceAndRelations.profile d h a}) =
          (MeasureTheory.ProbabilityMeasure.toMeasure
            (theorem25_historyDependentGlobalSCM.exogenousLaw d a)).map
            (fun u : Bool × Bool =>
              (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1))
            (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
              old.integrated.profileObservation a g =
                old.integrated.presenceAndRelations.profile d h a})
        exact measure_map_prod_fst_event_congr _ _ _ _
          (measurable_const.prodMk measurable_const)
          (measurable_const.prodMk measurable_fst)
          (MeasurableSpace.measurableSet_top (s := _)) (by intro u; rfl)
      rw [hEq]
      exact old.integrated.baselineProfileCoherent d a h
    · intro d a h e b r
      have hEq :
          MeasureTheory.ProbabilityMeasure.toMeasure
              ((theorem25_historyDependentFunctionallyCompleteSCM.toProbabilityCausalModel).baselineJointLaw
                d a h)
              {ω | old.integrated.relationObservation a ω.1 d a r e b ↔
                old.integrated.presenceAndRelations.relationEdge h d a r e b} =
            MeasureTheory.ProbabilityMeasure.toMeasure
              (old.integrated.probability.baselineJointLaw d a h)
              {ω | old.integrated.relationObservation a ω.1 d a r e b ↔
                old.integrated.presenceAndRelations.relationEdge h d a r e b} := by
        change (MeasureTheory.ProbabilityMeasure.toMeasure
            (theorem25_historyDependentGlobalSCM.exogenousLaw d a)).map
            (fun u : Bool × Bool =>
              (theorem25_historyDependentPresenceRelations.relationalState d h a, false))
            (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
              old.integrated.relationObservation a g d a r e b ↔
                old.integrated.presenceAndRelations.relationEdge h d a r e b}) =
          (MeasureTheory.ProbabilityMeasure.toMeasure
            (theorem25_historyDependentGlobalSCM.exogenousLaw d a)).map
            (fun u : Bool × Bool =>
              (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1))
            (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
              old.integrated.relationObservation a g d a r e b ↔
                old.integrated.presenceAndRelations.relationEdge h d a r e b})
        exact measure_map_prod_fst_event_congr _ _ _ _
          (measurable_const.prodMk measurable_const)
          (measurable_const.prodMk measurable_fst)
          (MeasurableSpace.measurableSet_top (s := _)) (by intro u; rfl)
      rw [hEq]
      exact old.integrated.baselineRelationsCoherent d a h e b r
  · intro d a h
    have hEq :
        MeasureTheory.ProbabilityMeasure.toMeasure
            ((theorem25_historyDependentFunctionallyCompleteSCM.toProbabilityCausalModel).baselineJointLaw
              d a h)
            {ω | old.relationalStateObservation d a h ω.1 =
              old.integrated.presenceAndRelations.relationalState d h a} =
          MeasureTheory.ProbabilityMeasure.toMeasure
            (old.integrated.probability.baselineJointLaw d a h)
            {ω | old.relationalStateObservation d a h ω.1 =
              old.integrated.presenceAndRelations.relationalState d h a} := by
      change (MeasureTheory.ProbabilityMeasure.toMeasure
          (theorem25_historyDependentGlobalSCM.exogenousLaw d a)).map
          (fun u : Bool × Bool =>
            (theorem25_historyDependentPresenceRelations.relationalState d h a, false))
          (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
            old.relationalStateObservation d a h g =
              old.integrated.presenceAndRelations.relationalState d h a}) =
        (MeasureTheory.ProbabilityMeasure.toMeasure
          (theorem25_historyDependentGlobalSCM.exogenousLaw d a)).map
          (fun u : Bool × Bool =>
            (theorem25_historyDependentPresenceRelations.relationalState d h a, u.1))
          (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
            old.relationalStateObservation d a h g =
              old.integrated.presenceAndRelations.relationalState d h a})
      exact measure_map_prod_fst_event_congr _ _ _ _
        (measurable_const.prodMk measurable_const)
        (measurable_const.prodMk measurable_fst)
        (MeasurableSpace.measurableSet_top (s := _)) (by intro u; rfl)
    rw [hEq]
    exact old.baselineRelationalStateCoherent d a h

/-- 機能完備な共有法則SCMと、25-B/C3の全観測整合を一つの具体モデルに束ねる。
既存C3統合モデルと共有法則モデルは同じ一様積測度を使い、候補出力だけが異なる。
Γだけで定まる観測事象について両pushforwardの測度が一致することを移送する。 -/
noncomputable def theorem25_historyDependentFunctionallyCompleteSharedC3Model :
    Theorem25SharedGlobalHistoryC3Model Bool Bool Bool Bool (Bool × Bool)
      (fun _ : Bool => Unit)
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  let old := theorem25_historyDependentFunctionallyCompleteC3Model
  refine ⟨theorem25_historyDependentFunctionallyCompleteSharedSCM,
    old.integrated.presenceAndRelations, old.integrated.profileObservation,
    old.integrated.relationObservation, old.relationalStateObservation,
    old.encodeRelationalState, old.relationalStateObservation_encode, ?_, ?_, ?_⟩
  · intro d a h
    have hEq :
        MeasureTheory.ProbabilityMeasure.toMeasure
            ((theorem25_historyDependentFunctionallyCompleteSharedSCM.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h)
            {ω | old.integrated.profileObservation a ω.1 =
              old.integrated.presenceAndRelations.profile d h a} =
          MeasureTheory.ProbabilityMeasure.toMeasure
            (old.integrated.probability.baselineJointLaw d a h)
            {ω | old.integrated.profileObservation a ω.1 =
              old.integrated.presenceAndRelations.profile d h a} := by
      change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
          (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
            (fun u : Bool × Bool =>
              (theorem25_historyDependentPresenceRelations.relationalState d h a, false))
            (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
              old.integrated.profileObservation a g =
                old.integrated.presenceAndRelations.profile d h a}) =
        ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
          (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
            (fun u : Bool × Bool =>
              (theorem25_historyDependentPresenceRelations.relationalState d h a, false))
            (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
              old.integrated.profileObservation a g =
                old.integrated.presenceAndRelations.profile d h a})
      rfl
    rw [hEq]
    exact old.integrated.baselineProfileCoherent d a h
  · intro d a h e b r
    have hEq :
        MeasureTheory.ProbabilityMeasure.toMeasure
            ((theorem25_historyDependentFunctionallyCompleteSharedSCM.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h)
            {ω | old.integrated.relationObservation a ω.1 d a r e b ↔
              old.integrated.presenceAndRelations.relationEdge h d a r e b} =
          MeasureTheory.ProbabilityMeasure.toMeasure
            (old.integrated.probability.baselineJointLaw d a h)
            {ω | old.integrated.relationObservation a ω.1 d a r e b ↔
              old.integrated.presenceAndRelations.relationEdge h d a r e b} := by
      change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
          (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
            (fun u : Bool × Bool =>
              (theorem25_historyDependentPresenceRelations.relationalState d h a, false))
            (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
              old.integrated.relationObservation a g d a r e b ↔
                old.integrated.presenceAndRelations.relationEdge h d a r e b}) =
        ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
          (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
            (fun u : Bool × Bool =>
              (theorem25_historyDependentPresenceRelations.relationalState d h a, false))
            (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
              old.integrated.relationObservation a g d a r e b ↔
                old.integrated.presenceAndRelations.relationEdge h d a r e b})
      rfl
    rw [hEq]
    exact old.integrated.baselineRelationsCoherent d a h e b r
  · intro d a h
    have hEq :
        MeasureTheory.ProbabilityMeasure.toMeasure
            ((theorem25_historyDependentFunctionallyCompleteSharedSCM.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h)
            {ω | old.relationalStateObservation d a h ω.1 =
              old.integrated.presenceAndRelations.relationalState d h a} =
          MeasureTheory.ProbabilityMeasure.toMeasure
            (old.integrated.probability.baselineJointLaw d a h)
            {ω | old.relationalStateObservation d a h ω.1 =
              old.integrated.presenceAndRelations.relationalState d h a} := by
      change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
          (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
            (fun u : Bool × Bool =>
              (theorem25_historyDependentPresenceRelations.relationalState d h a, false))
            (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
              old.relationalStateObservation d a h g =
                old.integrated.presenceAndRelations.relationalState d h a}) =
        ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
          (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
            (fun u : Bool × Bool =>
              (theorem25_historyDependentPresenceRelations.relationalState d h a, false))
            (Prod.fst ⁻¹' {g : Theorem25HistoryDependentGamma |
              old.relationalStateObservation d a h g =
                old.integrated.presenceAndRelations.relationalState d h a})
      rfl
    rw [hEq]
    exact old.baselineRelationalStateCoherent d a h

theorem theorem25_historyDependentFunctionallyCompleteSharedC3Model_observationEventsMeasurable :
    theorem25_historyDependentFunctionallyCompleteSharedC3Model.ObservationEventsMeasurable := by
  refine ⟨?_, ?_, ?_⟩
  · intro d a h
    exact theorem25_historyDependentGamma_prodBool_eventMeasurable fun g =>
      g.profile a = theorem25_historyDependentPresenceRelations.profile d h a
  · intro d a h e b r
    exact theorem25_historyDependentGamma_prodBool_eventMeasurable fun g =>
      (g.incidentRelation d a r e b) ↔
        theorem25_historyDependentPresenceRelations.relationEdge h d a r e b
  · intro d a h
    exact theorem25_historyDependentGamma_prodBool_eventMeasurable fun g =>
      g = theorem25_historyDependentPresenceRelations.relationalState d h a

noncomputable def theorem25_historyDependentFunctionallyCompleteMeasuredSharedC3Model :
    Theorem25MeasuredSharedGlobalHistoryC3Model Bool Bool Bool Bool (Bool × Bool)
      (fun _ : Bool => Unit)
      (fun _ : Bool => Theorem25HistoryDependentGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) :=
  ⟨theorem25_historyDependentFunctionallyCompleteSharedC3Model,
    theorem25_historyDependentFunctionallyCompleteSharedC3Model_observationEventsMeasurable⟩

theorem theorem25_historyDependentFunctionallyCompleteSharedC3Model_noAtman :
    ∀ d a, ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      ((theorem25_historyDependentFunctionallyCompleteSharedC3Model.scm.toIndexed).toProbabilityCausalModel)).hasAtman d a := by
  apply theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model
    theorem25_historyDependentFunctionallyCompleteMeasuredSharedC3Model
  exact theorem25_historyDependentFunctionallyCompleteSCM_satisfies25D

/-- 履歴依存25-B/C3モデルで25-Dの法則不変性を満たす比較構成では、
統合後も25-Dから定理25第2結論が従う。 -/
theorem theorem25_historyDependentFunctionallyCompleteC3Model_noAtman :
    ∀ d a,
      ¬ Theorem25CausalModel.hasAtman
        (Theorem25ProbabilityCausalModel.toCausalModel
          theorem25_historyDependentFunctionallyCompleteC3Model.integrated.probability) d a := by
  apply theorem25_secondConclusion_of_c3IntegratedModel
    theorem25_historyDependentFunctionallyCompleteC3Model
  exact theorem25_historyDependentFunctionallyCompleteSCM_satisfies25D

/-- 非退化SCMを25-B/Cの存在・関係データと同じ索引・Γ状態型に束ねた統合例。
基準分布でのプロフィール・辺観測整合も確認する。 -/
noncomputable def theorem25_twoExistenceRandomizedIntegratedModel :
    Theorem25IntegratedModel Bool Unit Unit Unit
      (fun _ : Unit => Unit)
      (fun _ : Unit => Theorem25TwoExistenceGamma)
      (fun _ : Unit => Bool) (fun _ : Unit => Bool) := by
  classical
  refine ⟨theorem25_twoExistenceRandomizedSCM.toProbabilityCausalModel,
    theorem25_twoExistencePresenceRelations,
    (fun _ state => state.profile ()),
    (fun _ state d _ r e _ => state.incidentRelation d () r e ()),
    ?_, ?_⟩
  · intro d a h
    cases a
    dsimp [Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel,
      theorem25_twoExistenceRandomizedSCM,
      theorem25_twoExistencePresenceRelations,
      MeasureTheory.ProbabilityMeasure.map,
      MeasureTheory.ProbabilityMeasure.toMeasure]
    change (ProbabilityTheory.uniformOn (Set.univ : Set Bool)).map
      (fun u : Bool =>
        (theorem25_twoExistencePresenceRelations.relationalState d h (), u))
      {ω | ω.1.profile () = theorem25_twoExistencePresenceRelations.profile d h ()} = 1
    have hmeas : MeasurableSet
        {ω : Theorem25TwoExistenceGamma × Bool | ω.1.profile () = some ()} := by
      exact MeasurableSet.preimage
        (MeasurableSpace.measurableSet_top (s :=
          {g : Theorem25TwoExistenceGamma | g.profile () = some ()})) measurable_fst
    rw [MeasureTheory.Measure.map_apply
      (μ := ProbabilityTheory.uniformOn (Set.univ : Set Bool))
      (f := fun u : Bool =>
        (theorem25_twoExistencePresenceRelations.relationalState d h (), u))
      (s := {ω : Theorem25TwoExistenceGamma × Bool |
        ω.1.profile () = theorem25_twoExistencePresenceRelations.profile d h ()})
      (measurable_const.prodMk measurable_id) hmeas]
    have hpre :
        (fun u : Bool =>
          (theorem25_twoExistencePresenceRelations.relationalState d h (), u)) ⁻¹'
            {ω : Theorem25TwoExistenceGamma × Bool |
              ω.1.profile () = theorem25_twoExistencePresenceRelations.profile d h ()} =
          Set.univ := by
      ext u
      simp [Theorem25PresenceRelationModel.relationalState,
        theorem25_twoExistencePresenceRelations]
    rw [hpre]
    rw [ProbabilityTheory.uniformOn_univ]
    rw [MeasureTheory.Measure.count_univ, ENat.card_eq_coe_fintype_card]
    simpa using (ENNReal.div_self (a := (2 : ENNReal)) (by norm_num) (by norm_num))
  · intro d a h e b r
    cases a
    cases b
    dsimp [Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel,
      theorem25_twoExistenceRandomizedSCM,
      theorem25_twoExistencePresenceRelations,
      MeasureTheory.ProbabilityMeasure.map,
      MeasureTheory.ProbabilityMeasure.toMeasure]
    change (ProbabilityTheory.uniformOn (Set.univ : Set Bool)).map
      (fun u : Bool =>
        (theorem25_twoExistencePresenceRelations.relationalState d h (), u))
      {ω | ω.1.incidentRelation d () r e () ↔
        theorem25_twoExistencePresenceRelations.relationEdge h d () r e ()} = 1
    have hmeas : MeasurableSet
        {ω : Theorem25TwoExistenceGamma × Bool |
          ω.1.incidentRelation d () r e () ↔
            theorem25_twoExistencePresenceRelations.relationEdge h d () r e ()} := by
      exact MeasurableSet.preimage
        (MeasurableSpace.measurableSet_top (s :=
          {g : Theorem25TwoExistenceGamma | g.incidentRelation d () r e () ↔
            theorem25_twoExistencePresenceRelations.relationEdge h d () r e ()}))
        measurable_fst
    rw [MeasureTheory.Measure.map_apply
      (μ := ProbabilityTheory.uniformOn (Set.univ : Set Bool))
      (f := fun u : Bool =>
        (theorem25_twoExistencePresenceRelations.relationalState d h (), u))
      (s := {ω : Theorem25TwoExistenceGamma × Bool |
        ω.1.incidentRelation d () r e () ↔
          theorem25_twoExistencePresenceRelations.relationEdge h d () r e ()})
      (measurable_const.prodMk measurable_id) hmeas]
    have hpre :
        (fun u : Bool =>
          (theorem25_twoExistencePresenceRelations.relationalState d h (), u)) ⁻¹'
            {ω : Theorem25TwoExistenceGamma × Bool |
              ω.1.incidentRelation d () r e () ↔
                theorem25_twoExistencePresenceRelations.relationEdge h d () r e ()} =
          Set.univ := by
      ext u
      simp [Theorem25PresenceRelationModel.relationalState,
        theorem25_twoExistencePresenceRelations, ne_comm]
    rw [hpre]
    rw [ProbabilityTheory.uniformOn_univ]
    rw [MeasureTheory.Measure.count_univ, ENat.card_eq_coe_fintype_card]
    simpa using (ENNReal.div_self (a := (2 : ENNReal)) (by norm_num) (by norm_num))

noncomputable def theorem25_twoExistenceRandomizedC3IntegratedModel :
    Theorem25C3IntegratedModel Bool Unit Unit Unit
      (fun _ : Unit => Unit)
      (fun _ : Unit => Theorem25TwoExistenceGamma)
      (fun _ : Unit => Bool) (fun _ : Unit => Bool) := by
  classical
  refine ⟨theorem25_twoExistenceRandomizedIntegratedModel,
    (fun _ _ _ state => state), (fun _ _ _ state => state), ?_, ?_⟩
  · intro d a h state
    rfl
  · intro d a h
    cases a
    dsimp [theorem25_twoExistenceRandomizedIntegratedModel,
      Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel,
      theorem25_twoExistenceRandomizedSCM,
      MeasureTheory.ProbabilityMeasure.map,
      MeasureTheory.ProbabilityMeasure.toMeasure]
    change (ProbabilityTheory.uniformOn (Set.univ : Set Bool)).map
      (fun u : Bool =>
        (theorem25_twoExistencePresenceRelations.relationalState d h (), u))
      {ω : Theorem25TwoExistenceGamma × Bool |
        ω.1 = theorem25_twoExistencePresenceRelations.relationalState d h ()} = 1
    have hmeas : MeasurableSet
        {ω : Theorem25TwoExistenceGamma × Bool |
          ω.1 = theorem25_twoExistencePresenceRelations.relationalState d h ()} := by
      exact MeasurableSet.preimage
        (MeasurableSpace.measurableSet_top (s :=
          {g : Theorem25TwoExistenceGamma |
            g = theorem25_twoExistencePresenceRelations.relationalState d h ()}))
        measurable_fst
    rw [MeasureTheory.Measure.map_apply
      (μ := ProbabilityTheory.uniformOn (Set.univ : Set Bool))
      (f := fun u : Bool =>
        (theorem25_twoExistencePresenceRelations.relationalState d h (), u))
      (s := {ω : Theorem25TwoExistenceGamma × Bool |
        ω.1 = theorem25_twoExistencePresenceRelations.relationalState d h ()})
      (measurable_const.prodMk measurable_id) hmeas]
    have hpre :
        (fun u : Bool =>
          (theorem25_twoExistencePresenceRelations.relationalState d h (), u)) ⁻¹'
            {ω : Theorem25TwoExistenceGamma × Bool |
              ω.1 = theorem25_twoExistencePresenceRelations.relationalState d h ()} =
          Set.univ := by
      ext u
      simp
    rw [hpre, ProbabilityTheory.uniformOn_univ,
      MeasureTheory.Measure.count_univ, ENat.card_eq_coe_fintype_card]
    simpa using (ENNReal.div_self (a := (2 : ENNReal)) (by norm_num) (by norm_num))

theorem theorem25_twoExistenceRandomized_candidate_has_positive_mass (s : Bool) :
    theorem25_twoExistenceRandomizedSCM.candidateHasPositiveMass false () s := by
  classical
  refine ⟨?_, ?_⟩
  · change MeasurableSet {u : Bool | u = s}
    exact measurableSet_preimage
      (measurable_id : Measurable (fun u : Bool => u))
      (measurableSet_singleton s)
  change (ProbabilityTheory.uniformOn (Set.univ : Set Bool)) {u : Bool | u = s} > 0
  cases s <;> rw [ProbabilityTheory.uniformOn_univ] <;> norm_num

/-- 非退化なΣ独立モデルでも、候補値の介入は将来出力を変える。
従って25-B/Cだけでは、ランダムな候補の範囲でもAtman不在は導けない。 -/
theorem theorem25_twoExistenceRandomized_hasAtman :
    (theorem25_twoExistenceRandomizedSCM.toProbabilityCausalModel.toCausalModel).hasAtman
      false () := by
  classical
  refine ⟨true, ?_, ?_⟩
  · change theorem25_twoExistenceRandomizedSCM.candidateHasPositiveMass false () true ∧
      theorem25_twoExistenceRandomizedSCM.independentAcrossHistories false ()
    constructor
    · exact theorem25_twoExistenceRandomized_candidate_has_positive_mass true
    · intro h
      exact theorem25_twoExistenceRandomizedSCM.candidateIndependentOfState false () h
  refine ⟨(), ?_⟩
  intro h
  have h' := congrArg Subtype.val h
  have h'' := congrArg
    (fun μ : MeasureTheory.Measure (Theorem25TwoExistenceGamma × Bool) =>
      μ {x | x.2 = false}) h'
  simp [theorem25_twoExistenceRandomizedSCM,
    Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel,
    Theorem25ProbabilityCausalModel.toCausalModel,
    MeasureTheory.ProbabilityMeasure.map,
    MeasureTheory.ProbabilityMeasure.toMeasure] at h''
  change 0 = (ProbabilityTheory.uniformOn ({false, true} : Set Bool)).map
    (fun u : Bool =>
      (theorem25_twoExistencePresenceRelations.relationalState false () (), u))
    {x | x.2 = false} at h''
  rw [show ({x : Theorem25TwoExistenceGamma × Bool | x.2 = false} :
      Set (Theorem25TwoExistenceGamma × Bool)) = Prod.snd ⁻¹' ({false} : Set Bool)
    by rfl] at h''
  rw [MeasureTheory.Measure.map_apply (by fun_prop)
    (MeasurableSet.preimage (MeasurableSet.singleton false) measurable_snd)] at h''
  have huniv : (Set.univ : Set Bool) = {false, true} := by
    ext b
    cases b <;> simp
  have hpre :
      (fun u : Bool =>
        (theorem25_twoExistencePresenceRelations.relationalState false () (), u)) ⁻¹'
          Prod.snd ⁻¹' ({false} : Set Bool) = {false} := by
    ext u
    simp
  rw [hpre, ← huniv, ProbabilityTheory.uniformOn_univ] at h''
  rw [MeasureTheory.Measure.count_singleton] at h''
  have hne : (1 : ENNReal) / (Fintype.card Bool : ENNReal) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨by simp, by simp⟩
  exact hne h''.symm

/-- 非退化SCMを25-B/C3統合型まで持ち上げても、25-DなしにはAtmanが除けない。 -/
theorem theorem25_C3Randomized_do_not_imply_noAtman :
    ((theorem25_twoExistenceRandomizedC3IntegratedModel.integrated.probability).toCausalModel).hasAtman
      false () := by
  simpa [theorem25_twoExistenceRandomizedC3IntegratedModel,
    theorem25_twoExistenceRandomizedIntegratedModel] using
    theorem25_twoExistenceRandomized_hasAtman

/-- 物理層と上位層を異なる点として持つ二層格子上のΓ状態。 -/
abbrev Theorem25TwoLayerGamma :=
  Theorem25RelationalState Bool Bool Unit (fun _ : Bool => Unit)

instance : MeasurableSpace Theorem25TwoLayerGamma := ⊤

/-- 層をBool格子、存在をBool二点とする25-B/Cデータ。両層に現前し、相互辺は連結。 -/
noncomputable def theorem25_twoLayerPresenceRelations :
    Theorem25PresenceRelationModel Bool Unit Bool Unit (fun _ : Bool => Unit) := by
  classical
  refine {
    profile := fun _ _ _ => some ()
    topMarker := ()
    topRepresentationIsSubsingleton := ?_
    supportNonempty := ?_
    supportUpwardClosed := ?_
    topLayerHasCommonMarker := ?_
    roleInverse := id
    roleInverseInvolutive := ?_
    relationEdge := fun _ d _ _ e _ => d ≠ e
    relationEdgeReverses := ?_
    everyExistenceIsRelated := ?_
    relationGraphConnected := ?_
  }
  · intro x y
    cases x
    cases y
    rfl
  · intro d h
    exact ⟨false, by simp⟩
  · intro d h a b hp hab
    simp
  · intro d h
    simp
  · intro r
    rfl
  · intro h d a r e b
    simp [ne_comm]
  · intro h d
    cases d with
    | false => exact ⟨true, false, false, (), by decide, by decide⟩
    | true => exact ⟨false, false, false, (), by decide, by decide⟩
  · intro h d e
    cases d <;> cases e
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by decide, ⟨false, false, (), by decide⟩⟩
    · exact Relation.ReflTransGen.single ⟨by decide, ⟨false, false, (), by decide⟩⟩
    · exact Relation.ReflTransGen.refl

/-- Bool一様候補を二層の完全Γ状態へ接続した25-B/C3モデル。Γは二層プロファイルと
その垂直近傍、水平入出辺を保持し、候補Σは各固定履歴でΓから独立。 -/
noncomputable def theorem25_twoLayerRandomizedSCM :
    Theorem25RandomizedStructuralCausalModel Bool Bool Unit Bool
      (fun _ : Bool => Theorem25TwoLayerGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  refine {
    exogenousLaw := fun _ _ =>
      ⟨ProbabilityTheory.uniformOn (Set.univ : Set Bool), inferInstance⟩
    candidateVariable := fun _ _ => id
    candidateVariableAEMeasurable := by
      intro d a
      exact theorem25_finiteDomain_aemeasurable _ _
    stateEquation := fun d a h _ =>
      theorem25_twoLayerPresenceRelations.relationalState d h a
    outputEquation := fun _ _ _ _ s => s
    baselineJointAEMeasurable := by
      intro d a h
      exact theorem25_finiteDomain_aemeasurable _ _
    intervenedJointAEMeasurable := by
      intro d a h s
      exact theorem25_finiteDomain_aemeasurable _ _
    candidateIndependentOfState := ?_
  }
  intro d a h
  change ProbabilityTheory.IndepFun (fun u : Bool => u)
    (fun _ : Bool => theorem25_twoLayerPresenceRelations.relationalState d h a)
    (ProbabilityTheory.uniformOn (Set.univ : Set Bool))
  exact ProbabilityTheory.indepFun_const_right
    (μ := ProbabilityTheory.uniformOn (Set.univ : Set Bool))
    (fun u : Bool => u)
    (theorem25_twoLayerPresenceRelations.relationalState d h a)

/-- 二層Bool格子の25-B/C3モデルでも、25-Dを外すと上位層にAtman候補が残る。
したがって第2結論の欠落は一層格子だけの退化現象ではない。 -/
theorem theorem25_twoLayerRandomized_hasAtman :
    (theorem25_twoLayerRandomizedSCM.toProbabilityCausalModel.toCausalModel).hasAtman
      false true := by
  classical
  refine ⟨true, ?_, ?_⟩
  · change theorem25_twoLayerRandomizedSCM.candidateHasPositiveMass false true true ∧
      theorem25_twoLayerRandomizedSCM.independentAcrossHistories false true
    constructor
    · unfold Theorem25RandomizedStructuralCausalModel.candidateHasPositiveMass
      refine ⟨?_, ?_⟩
      · change MeasurableSet {u : Bool | u = true}
        exact measurableSet_preimage
          (measurable_id : Measurable (fun u : Bool => u))
          (measurableSet_singleton true)
      change (ProbabilityTheory.uniformOn (Set.univ : Set Bool))
        {u | u = true} > 0
      rw [ProbabilityTheory.uniformOn_univ]
      norm_num
    · intro h
      exact theorem25_twoLayerRandomizedSCM.candidateIndependentOfState false true h
  refine ⟨(), ?_⟩
  intro h
  have h' := congrArg Subtype.val h
  have h'' := congrArg
    (fun μ : MeasureTheory.Measure (Theorem25TwoLayerGamma × Bool) =>
      μ {x | x.2 = false}) h'
  simp [theorem25_twoLayerRandomizedSCM,
    Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel,
    Theorem25ProbabilityCausalModel.toCausalModel,
    MeasureTheory.ProbabilityMeasure.map,
    MeasureTheory.ProbabilityMeasure.toMeasure] at h''
  change 0 = (ProbabilityTheory.uniformOn ({false, true} : Set Bool)).map
    (fun u : Bool =>
      (theorem25_twoLayerPresenceRelations.relationalState false () true, u))
    {x | x.2 = false} at h''
  rw [show ({x : Theorem25TwoLayerGamma × Bool | x.2 = false} :
      Set (Theorem25TwoLayerGamma × Bool)) = Prod.snd ⁻¹' ({false} : Set Bool)
    by rfl] at h''
  rw [MeasureTheory.Measure.map_apply (by fun_prop)
    (MeasurableSet.preimage (MeasurableSet.singleton false) measurable_snd)] at h''
  have hpre :
      (fun u : Bool =>
        (theorem25_twoLayerPresenceRelations.relationalState false () true, u)) ⁻¹'
          Prod.snd ⁻¹' ({false} : Set Bool) = {false} := by
    ext u
    simp
  rw [hpre] at h''
  have huniv : ({false, true} : Set Bool) = Set.univ := by
    ext b
    cases b <;> simp
  rw [huniv] at h''
  rw [ProbabilityTheory.uniformOn_univ] at h''
  rw [MeasureTheory.Measure.count_singleton] at h''
  have hne : (1 : ENNReal) / (Fintype.card Bool : ENNReal) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨by simp, by simp⟩
  exact hne h''.symm

noncomputable def theorem25_twoLayerRandomizedC3Model :
    Theorem25C3IntegratedModel Bool Unit Bool Unit
      (fun _ : Bool => Unit)
      (fun a : Bool => Theorem25TwoLayerGamma)
      (fun _ : Bool => Bool) (fun _ : Bool => Bool) := by
  classical
  refine ⟨?_, (fun _ _ _ state => state), (fun _ _ _ state => state), ?_, ?_⟩
  · refine ⟨theorem25_twoLayerRandomizedSCM.toProbabilityCausalModel,
      theorem25_twoLayerPresenceRelations,
      (fun a state => state.profile a),
      (fun a state d _ r e b => state.incidentRelation d a r e b),
      ?_, ?_⟩
    · intro d a h
      dsimp [Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel,
        theorem25_twoLayerRandomizedSCM,
        MeasureTheory.ProbabilityMeasure.map,
        MeasureTheory.ProbabilityMeasure.toMeasure]
      change (ProbabilityTheory.uniformOn (Set.univ : Set Bool)).map
        (fun u : Bool =>
          (theorem25_twoLayerPresenceRelations.relationalState d h a, u))
        {ω | ω.1.profile a = some ()} = 1
      have hs : MeasurableSet
          {ω : Theorem25TwoLayerGamma × Bool | ω.1.profile a = some ()} := by
        exact MeasurableSet.preimage
          (MeasurableSpace.measurableSet_top (s :=
            {g : Theorem25TwoLayerGamma | g.profile a = some ()})) measurable_fst
      rw [MeasureTheory.Measure.map_apply
        (μ := ProbabilityTheory.uniformOn (Set.univ : Set Bool))
        (f := fun u : Bool =>
          (theorem25_twoLayerPresenceRelations.relationalState d h a, u))
        (s := {ω : Theorem25TwoLayerGamma × Bool | ω.1.profile a = some ()})
        (measurable_const.prodMk measurable_id) hs]
      have hpre :
          (fun u : Bool =>
            (theorem25_twoLayerPresenceRelations.relationalState d h a, u)) ⁻¹'
              {ω : Theorem25TwoLayerGamma × Bool | ω.1.profile a = some ()} =
            Set.univ := by
        ext u
        simp [Theorem25PresenceRelationModel.relationalState,
          theorem25_twoLayerPresenceRelations]
      rw [hpre, ProbabilityTheory.uniformOn_univ,
        MeasureTheory.Measure.count_univ, ENat.card_eq_coe_fintype_card]
      simpa using (ENNReal.div_self (a := (2 : ENNReal)) (by norm_num) (by norm_num))
    · intro d a h e b r
      dsimp [Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel,
        theorem25_twoLayerRandomizedSCM,
        MeasureTheory.ProbabilityMeasure.map,
        MeasureTheory.ProbabilityMeasure.toMeasure]
      change (ProbabilityTheory.uniformOn (Set.univ : Set Bool)).map
        (fun u : Bool =>
          (theorem25_twoLayerPresenceRelations.relationalState d h a, u))
        {ω | ω.1.incidentRelation d a r e b ↔
          theorem25_twoLayerPresenceRelations.relationEdge h d a r e b} = 1
      have hs : MeasurableSet
          {ω : Theorem25TwoLayerGamma × Bool |
            ω.1.incidentRelation d a r e b ↔
              theorem25_twoLayerPresenceRelations.relationEdge h d a r e b} := by
        exact MeasurableSet.preimage
          (MeasurableSpace.measurableSet_top (s :=
            {g : Theorem25TwoLayerGamma |
              g.incidentRelation d a r e b ↔
                theorem25_twoLayerPresenceRelations.relationEdge h d a r e b}))
          measurable_fst
      rw [MeasureTheory.Measure.map_apply
        (μ := ProbabilityTheory.uniformOn (Set.univ : Set Bool))
        (f := fun u : Bool =>
          (theorem25_twoLayerPresenceRelations.relationalState d h a, u))
        (s := {ω : Theorem25TwoLayerGamma × Bool |
          ω.1.incidentRelation d a r e b ↔
            theorem25_twoLayerPresenceRelations.relationEdge h d a r e b})
        (measurable_const.prodMk measurable_id) hs]
      have hpre :
          (fun u : Bool =>
            (theorem25_twoLayerPresenceRelations.relationalState d h a, u)) ⁻¹'
              {ω : Theorem25TwoLayerGamma × Bool |
                ω.1.incidentRelation d a r e b ↔
                  theorem25_twoLayerPresenceRelations.relationEdge h d a r e b} =
            Set.univ := by
        ext u
        simp [Theorem25PresenceRelationModel.relationalState,
          theorem25_twoLayerPresenceRelations, ne_comm]
      rw [hpre, ProbabilityTheory.uniformOn_univ,
        MeasureTheory.Measure.count_univ, ENat.card_eq_coe_fintype_card]
      simpa using (ENNReal.div_self (a := (2 : ENNReal)) (by norm_num) (by norm_num))
  · intro d a h state
    rfl
  · intro d a h
    dsimp [theorem25_twoLayerRandomizedSCM,
      Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel,
      MeasureTheory.ProbabilityMeasure.map,
      MeasureTheory.ProbabilityMeasure.toMeasure]
    change (ProbabilityTheory.uniformOn (Set.univ : Set Bool)).map
      (fun u : Bool =>
        (theorem25_twoLayerPresenceRelations.relationalState d h a, u))
      {ω : Theorem25TwoLayerGamma × Bool |
        ω.1 = theorem25_twoLayerPresenceRelations.relationalState d h a} = 1
    have hs : MeasurableSet
        {ω : Theorem25TwoLayerGamma × Bool |
          ω.1 = theorem25_twoLayerPresenceRelations.relationalState d h a} := by
      exact MeasurableSet.preimage
        (MeasurableSpace.measurableSet_top (s :=
          {g : Theorem25TwoLayerGamma |
            g = theorem25_twoLayerPresenceRelations.relationalState d h a}))
        measurable_fst
    rw [MeasureTheory.Measure.map_apply
      (μ := ProbabilityTheory.uniformOn (Set.univ : Set Bool))
      (f := fun u : Bool =>
        (theorem25_twoLayerPresenceRelations.relationalState d h a, u))
      (s := {ω : Theorem25TwoLayerGamma × Bool |
        ω.1 = theorem25_twoLayerPresenceRelations.relationalState d h a})
      (measurable_const.prodMk measurable_id) hs]
    have hpre :
        (fun u : Bool =>
          (theorem25_twoLayerPresenceRelations.relationalState d h a, u)) ⁻¹'
            {ω : Theorem25TwoLayerGamma × Bool |
              ω.1 = theorem25_twoLayerPresenceRelations.relationalState d h a} =
          Set.univ := by
      ext u
      simp
    rw [hpre, ProbabilityTheory.uniformOn_univ,
      MeasureTheory.Measure.count_univ, ENat.card_eq_coe_fintype_card]
    simpa using (ENNReal.div_self (a := (2 : ENNReal)) (by norm_num) (by norm_num))

/-- 二層の完全Γ観測を統合したC3モデルでも、同じAtman候補が残る。 -/
theorem theorem25_twoLayerRandomizedC3_hasAtman :
    (theorem25_twoLayerRandomizedC3Model.integrated.probability.toCausalModel).hasAtman
      false true := by
  simpa [theorem25_twoLayerRandomizedC3Model,
    theorem25_twoLayerRandomizedSCM] using
    theorem25_twoLayerRandomized_hasAtman

noncomputable def theorem25_twoExistenceCountermodelC3 :
    Theorem25C3IntegratedModel Bool Unit Unit Unit
      (fun _ : Unit => Unit)
      (fun _ : Unit => Theorem25TwoExistenceGamma)
      (fun _ : Unit => Bool) (fun _ : Unit => Bool) := by
  classical
  let RState := Theorem25TwoExistenceGamma
  let S : Theorem25StructuralCausalModel Bool Unit Unit Unit
      (fun _ : Unit => RState) (fun _ : Unit => Bool) (fun _ : Unit => Bool) :=
    { defaultCandidate := fun _ => false
      exogenousLaw := fun _ _ => ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
      stateEquation := fun d _ h _ _ =>
        theorem25_twoExistencePresenceRelations.relationalState d h ()
      outputEquation := fun _ _ _ _ s => s
      baselineJointAEMeasurable := by
        intro d a h
        exact theorem25_finiteDomain_aemeasurable _ _
      intervenedJointAEMeasurable := by
        intro d a h s
        exact theorem25_finiteDomain_aemeasurable _ _
      independentFixedIndividualization := fun d _ s => ∀ h,
        ProbabilityTheory.IndepFun (fun _ : Unit => s)
          (fun _ : Unit =>
            theorem25_twoExistencePresenceRelations.relationalState d h ())
          (MeasureTheory.Measure.dirac ()) }
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨S.toProbabilityCausalModel,
      theorem25_twoExistencePresenceRelations,
      (fun _ state => state.profile ()),
      (fun _ state d _ r e b => state.incidentRelation d () r e b),
      ?_, ?_⟩
    · intro d a h
      cases a
      dsimp [S, Theorem25StructuralCausalModel.toProbabilityCausalModel,
        Theorem25PresenceRelationModel.relationalState,
        theorem25_twoExistencePresenceRelations,
        MeasureTheory.ProbabilityMeasure.map,
        MeasureTheory.ProbabilityMeasure.toMeasure]
      rw [MeasureTheory.Measure.map_dirac]
      apply MeasureTheory.Measure.dirac_apply_of_mem
      rfl
    · intro d a h e b r
      cases a
      dsimp [S, Theorem25StructuralCausalModel.toProbabilityCausalModel,
        Theorem25PresenceRelationModel.relationalState,
        theorem25_twoExistencePresenceRelations,
        MeasureTheory.ProbabilityMeasure.map,
        MeasureTheory.ProbabilityMeasure.toMeasure]
      rw [MeasureTheory.Measure.map_dirac]
      apply MeasureTheory.Measure.dirac_apply_of_mem
      change ((theorem25_twoExistencePresenceRelations.relationalState d h (), false).1).incidentRelation
        d () r e b ↔ d ≠ e
      simp [Theorem25PresenceRelationModel.relationalState,
        theorem25_twoExistencePresenceRelations, ne_comm]
  · exact fun _ _ _ state => state
  · exact fun _ _ _ state => state
  · intro d a h state
    rfl
  · intro d a h
    cases a
    dsimp [S, Theorem25StructuralCausalModel.toProbabilityCausalModel,
      Theorem25PresenceRelationModel.relationalState,
      theorem25_twoExistencePresenceRelations,
      MeasureTheory.ProbabilityMeasure.map,
      MeasureTheory.ProbabilityMeasure.toMeasure]
    rw [MeasureTheory.Measure.map_dirac]
    apply MeasureTheory.Measure.dirac_apply_of_mem
    rfl

/-- この有限モデルは条件25-B/Cと基準プロファイル・関係観測との確率1整合を満たすが、
候補介入の前後で出力法則が変わり、Atman(d,α) が成立する。よって25-Dは独立の実質条件。 -/
theorem theorem25_BC_do_not_imply_noAtman :
    (theorem25_twoExistenceCountermodel.probability.toCausalModel).hasAtman false () := by
  refine ⟨true, ?_, ?_⟩
  · simp [theorem25_twoExistenceCountermodel, theorem25_twoExistenceCountermodelSCM,
      Theorem25StructuralCausalModel.toProbabilityCausalModel,
      Theorem25ProbabilityCausalModel.toCausalModel]
  refine ⟨(), ?_⟩
  intro h
  have h' := congrArg Subtype.val h
  have h'' := congrArg
    (fun μ : MeasureTheory.Measure (Unit × Bool) => μ {x | x.2 = false}) h'
  simp [theorem25_twoExistenceCountermodel, theorem25_twoExistenceCountermodelSCM,
    Theorem25StructuralCausalModel.toProbabilityCausalModel,
    Theorem25ProbabilityCausalModel.toCausalModel,
    MeasureTheory.ProbabilityMeasure.map, MeasureTheory.ProbabilityMeasure.toMeasure] at h''

/-- 25-C3のΓを実際の状態型として保持しても、25-B/Cのみから25-Dは導けない。
本例は各固定履歴で候補値を定数確率変数として関係状態から独立にする退化モデルである。
ランダムなΣと履歴Hの同時分布をもつ一般の確率的個体化モデルまでは表さない。 -/
theorem theorem25_C3_do_not_imply_noAtman :
    (theorem25_twoExistenceCountermodelC3.integrated.probability.toCausalModel).hasAtman
      false () := by
  classical
  letI : MeasurableSpace Theorem25TwoExistenceGamma := ⊤
  refine ⟨true, ?_, ?_⟩
  · change ∀ h, ProbabilityTheory.IndepFun
      (fun _ : Unit => true)
      (fun _ : Unit =>
        theorem25_twoExistencePresenceRelations.relationalState false h ())
      (MeasureTheory.Measure.dirac ())
    intro h
    exact ProbabilityTheory.indepFun_const_left true
      (fun _ : Unit => theorem25_twoExistencePresenceRelations.relationalState false h ())
  refine ⟨(), ?_⟩
  intro h
  have h' := congrArg Subtype.val h
  have h'' := congrArg
    (fun μ : MeasureTheory.Measure (Theorem25TwoExistenceGamma × Bool) =>
      μ {x | x.2 = false}) h'
  simp [theorem25_twoExistenceCountermodelC3,
    Theorem25StructuralCausalModel.toProbabilityCausalModel,
    Theorem25ProbabilityCausalModel.toCausalModel,
    MeasureTheory.ProbabilityMeasure.map,
    MeasureTheory.ProbabilityMeasure.toMeasure,
    theorem25_twoExistencePresenceRelations] at h''




end Tomabechi.Theorem16_25
