import Tomabechi.Consistency.ConsistencyC1_HFlow
import Theorem4

/-!
# C1: 非定数の臨場感を持つ定理4モデル

定理1/H-flowのスカラー閉ループ `linearFlow 3 0` を使い、
`P(x)=exp(-x²)`、`Q=1`、`V₀(x)=1+x²+P(x)` とする。臨場感は非定数で
`[0,1]` に入り、実効ポテンシャルは `1+x²` となる。この具体モデルでは、
任意の初期値と非負開始時刻からの全未来について定理4の定量結論を得る。
-/

noncomputable section

namespace Tomabechi.Consistency.ConsistencyC1Theorem4

open MeasureTheory
open Filter
open scoped Topology
open Tomabechi.Theorem1
open Tomabechi.Theorem4
open Tomabechi.Consistency.ConsistencyC1

def presenceP4 (x _t : ℝ) : ℝ := Real.exp (-x ^ 2)
def presenceQ4 (_x _t : ℝ) : ℝ := 1
def presenceV04 (x t : ℝ) : ℝ := 1 + x ^ 2 + presenceP4 x t

theorem effectivePotential_eq (x t : ℝ) :
    effectivePotential (presenceV04 x t) (presenceP4 x t) (presenceQ4 x t) 1 =
      1 + x ^ 2 := by
  simp [effectivePotential, presenceV04, presenceQ4]

/-- 臨場感は `[0,1]` の範囲にあり、状態によって値が変化する。 -/
theorem presenceP4_bounds (x t : ℝ) : 0 < presenceP4 x t ∧ presenceP4 x t ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg x]

theorem presenceP4_nonconstant : presenceP4 0 0 ≠ presenceP4 1 0 := by
  have hexp : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h0 : presenceP4 0 0 = 1 := by simp [presenceP4]
  have h1 : presenceP4 1 0 = Real.exp (-1) := by simp [presenceP4]
  rw [h0, h1]
  exact Ne.symm hexp.ne

theorem residual4_eq_sq (x t : ℝ) :
    residual4 (presenceV04 x t) (presenceP4 x t) (presenceQ4 x t) 1 1 = x ^ 2 := by
  rw [residual4, effectivePotential_eq]
  simp [Tomabechi.Theorem1.residual1, max_eq_left (sq_nonneg x)]

theorem weightedTCZ_univ_eq_zero (t : ℝ) :
    weightedTCZ Set.univ presenceV04 presenceP4 presenceQ4 1 1 t = ({0} : Set ℝ) := by
  ext x
  change (x ∈ Set.univ ∧
    effectivePotential (presenceV04 x t) (presenceP4 x t) (presenceQ4 x t) 1 ≤ 1) ↔ x = 0
  simp only [Set.mem_univ, true_and]
  rw [effectivePotential_eq]
  constructor
  · intro h
    have hx : x ^ 2 ≤ 0 := by linarith
    exact (sq_eq_zero_iff).mp (le_antisymm hx (sq_nonneg x))
  · intro h
    subst x
    norm_num

def t4ResidualPath (x t₀ : ℝ) : ℝ → ℝ :=
  fun s => residual4
    (presenceV04 ((linearFlow 3 0).flow t₀ x s) s)
    (presenceP4 ((linearFlow 3 0).flow t₀ x s) s)
    (presenceQ4 ((linearFlow 3 0).flow t₀ x s) s) 1 1

theorem t4ResidualPath_eq (x t₀ : ℝ) :
    t4ResidualPath x t₀ = fun s => (x * Real.exp (-3 * (s - t₀))) ^ 2 := by
  funext s
  rw [t4ResidualPath, residual4_eq_sq]
  simp [linearFlow]

theorem t4ResidualPath_ac (x t₀ T : ℝ) :
    AbsolutelyContinuousOnInterval (t4ResidualPath x t₀) t₀ T := by
  have hclosed : ContDiff ℝ 1 (fun s : ℝ => (x * Real.exp (-3 * (s - t₀))) ^ 2) := by
    fun_prop
  exact hclosed.contDiffOn.absolutelyContinuousOnInterval.congr
    fun _ _ => (congrFun (t4ResidualPath_eq x t₀) _).symm

theorem t4ResidualPath_deriv (x t₀ s : ℝ) :
    HasDerivAt (t4ResidualPath x t₀) (-6 * t4ResidualPath x t₀ s) s := by
  rw [t4ResidualPath_eq]
  have hlin : HasDerivAt (fun u : ℝ => -3 * (u - t₀)) (-3) s := by
    simpa using (hasDerivAt_id s).sub_const t₀ |>.const_mul (-3)
  have hexp := (Real.hasDerivAt_exp (-3 * (s - t₀))).comp s hlin
  have hpow := (hexp.const_mul x).pow 2
  convert hpow using 1
  · funext u
    simp
  · simp
    ring

theorem t4ResidualPath_decay_ae (x t₀ T : ℝ) :
    ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
      deriv (t4ResidualPath x t₀) s ≤ -2 * 3 * t4ResidualPath x t₀ s := by
  filter_upwards with s
  rw [(t4ResidualPath_deriv x t₀ s).deriv]
  nlinarith

theorem t4_error_bound (x t₀ s : ℝ) :
    (Metric.infDist ((linearFlow 3 0).flow t₀ x s)
      (weightedTCZ Set.univ presenceV04 presenceP4 presenceQ4 1 1 s)) ^ 2 ≤
      residual4 (presenceV04 ((linearFlow 3 0).flow t₀ x s) s)
        (presenceP4 ((linearFlow 3 0).flow t₀ x s) s)
        (presenceQ4 ((linearFlow 3 0).flow t₀ x s) s) 1 1 := by
  rw [weightedTCZ_univ_eq_zero, Metric.infDist_singleton, Real.dist_eq, sq_abs,
    residual4_eq_sq]
  simp [linearFlow]

/-- 同じ `linearFlow 3 0` が作る閉到達集合を用いた定理4の全時間結論。
Pは非定数、Qは非零で、任意の実初期値から全ての未来時刻で定量評価する。 -/
theorem linearFlow_theorem4 (x t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t →
      Metric.infDist ((linearFlow 3 0).flow t₀ x t)
        (weightedTCZ (closedLoopReachableSet
          (policyFlowReachableAt (linearFlow 3 0) Set.univ t₀))
          presenceV04 presenceP4 presenceQ4 1 1 t) ≤
        Real.sqrt (t4ResidualPath x t₀ t₀) * Real.exp (-3 * (t - t₀))) ∧
      Filter.Tendsto (fun t => Metric.infDist ((linearFlow 3 0).flow t₀ x t)
        (weightedTCZ (closedLoopReachableSet
          (policyFlowReachableAt (linearFlow 3 0) Set.univ t₀))
          presenceV04 presenceP4 presenceQ4 1 1 t)) atTop (𝓝 0) := by
  have hK : closedLoopReachableSet
      (policyFlowReachableAt (linearFlow 3 0) Set.univ t₀) = Set.univ :=
    linearFlow_closedReachable_univ 3 0 t₀ ht₀
  have hcore := weighted_reachable_tcz_distance_tendsto_zero
    (fun t => (linearFlow 3 0).flow t₀ x t)
    (policyFlowReachableAt (linearFlow 3 0) Set.univ t₀)
    presenceV04 presenceP4 presenceQ4 1 1 3 1 t₀
    (fun t ht => mem_policyFlowReachableAt_of_flow
      (linearFlow 3 0) Set.univ t₀ t x (Set.mem_univ x) ht)
    (fun T hT s hs => by
      rw [hK]
      refine ⟨0, ?_⟩
      rw [weightedTCZ_univ_eq_zero]
      simp)
    (fun T hT => by
      change AbsolutelyContinuousOnInterval (t4ResidualPath x t₀) t₀ T
      exact t4ResidualPath_ac x t₀ T)
    (fun T hT => by
      change ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
        deriv (t4ResidualPath x t₀) s ≤ -2 * 3 * t4ResidualPath x t₀ s
      exact t4ResidualPath_decay_ae x t₀ T)
    (fun T hT s hs => by
      rw [hK]
      simpa using t4_error_bound x t₀ s)
    ht₀ three_pos one_pos
  refine ⟨?_, hcore.2.2⟩
  intro t ht
  have hpoint := hcore.2.1 t ht
  have hinit : (linearFlow 3 0).flow t₀ x t₀ = x := (linearFlow 3 0).initial t₀ x
  have hres0 : residual4 (presenceV04 x t₀) (presenceP4 x t₀)
      (presenceQ4 x t₀) 1 1 = t4ResidualPath x t₀ t₀ := by
    rw [residual4_eq_sq, t4ResidualPath_eq]
    simp
  rw [hinit] at hpoint
  rw [← hres0]
  simpa only [one_mul] using hpoint

end Tomabechi.Consistency.ConsistencyC1Theorem4

end
