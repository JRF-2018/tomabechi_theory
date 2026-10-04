import Theorem24_26_Model

/-!
# 定理26の2次元「輪」モデル（`examples/theorem26_27_dynamic_quiescence.py` の 26-A）

状態 `p=(r,φ)∈ℝ×ℝ`（半径方向のズレ `r` と輪上の位相 `φ`）、閉ループ `ṙ=-r`, `φ̇=3/2`（Python の
`u0=(-λ r, ω)`, `λ=1`, `ω=3/2`）。最高抽象度の走行コスト `V⊤=3r²`（位相に依らない）、割引 `ρ=1`、
空未満の層は走行コスト 1。制御空間は単点（`Theorem24_26_Model` と同じ無選択の特殊モデル）。

* 零残余苦価値集合 `𝒩⊤={r=0}`（輪）、`J*(r,φ)=r²`、`W=r²`（`c₁=c₂=1`, `λ_W=2`）、`ω(ρ)=ρ²`。
* 一般定理 `theorem24_to26_from_nonnegativeTimeData` を適用し、26-A の全条件と結論（PZS ⇔ 輪への所属、
  `W` の指数減衰、`J*→0`）を得る。
* 動的寂静: 輪の上から出発すれば全時刻で輪の上に留まり（`J*=0`）、位相は `φ(t)=φ0+(3/2)(t-T)` で
  動き続ける（`ṙ=0` でも静止しない）。

位相座標がコストにも `W` にも入らないので、距離は sup 距離で `dist(p,𝒩)=|r|`。
-/

noncomputable section

namespace Tomabechi.Examples.Theorem26Ring

open Tomabechi.Theorem24_26 Tomabechi.Theorem24_26_Model MeasureTheory

/-- 位相速度 `ω=3/2`。 -/
def omg : ℝ := 3 / 2

/-- 閉ループの流れ `r(s)=r0 e^{T-s}`, `φ(s)=φ0+ω(s-T)`。 -/
def flow2 (p : ℝ × ℝ) (T s : ℝ) : ℝ × ℝ := (flow p.1 T s, p.2 + omg * (s - T))

/-- 価値 `J*(r,φ)=r²`（位相に依らない）。 -/
def value2 (p : ℝ × ℝ) (T : ℝ) : ℝ := value p.1 T

theorem value2_eq (p : ℝ × ℝ) (T : ℝ) : value2 p T = p.1 ^ 2 := value_eq_sq p.1 T

/-- 零価値目標 `{r=0}`（輪）。 -/
def ring (T : ℝ) : Set (ℝ × ℝ) := theorem26ZeroValueTarget Set.univ value2 T

theorem ring_eq (T : ℝ) : ring T = {p | p.1 = 0} := by
  ext p; simp [ring, theorem26ZeroValueTarget, value2_eq]

theorem ring_closed (T : ℝ) : IsClosed (ring T) := by
  rw [ring_eq]; exact isClosed_eq continuous_fst continuous_const

/-- `dist(p,輪)=|r|`（sup 距離）。 -/
theorem infDist_ring (p : ℝ × ℝ) (T : ℝ) : Metric.infDist p (ring T) = |p.1| := by
  rw [ring_eq]
  have hne : ({p | p.1 = 0} : Set (ℝ × ℝ)).Nonempty := ⟨(0, 0), rfl⟩
  apply le_antisymm
  · have hmem : ((0 : ℝ), p.2) ∈ ({p | p.1 = 0} : Set (ℝ × ℝ)) := rfl
    have := Metric.infDist_le_dist_of_mem (x := p) hmem
    refine this.trans ?_
    rw [Prod.dist_eq]
    simp [Real.dist_eq]
  · rw [Metric.le_infDist hne]
    intro q hq
    have hq0 : q.1 = 0 := hq
    rw [Prod.dist_eq]
    refine le_trans ?_ (le_max_left _ _)
    simp [Real.dist_eq, hq0]

theorem infDist_ring_sq (p : ℝ × ℝ) (T : ℝ) : Metric.infDist p (ring T) ^ 2 = p.1 ^ 2 := by
  rw [infDist_ring, sq_abs]

/-! ## 定理24/26 の共通データ -/

abbrev RState : Bool → Type
  | false => Unit
  | true => ℝ × ℝ

abbrev RFeedback : Bool → Type
  | false => PUnit
  | true => NonnegativeTimeBorelMarkovFeedback (ℝ × ℝ) Control

def feedback0 : NonnegativeTimeBorelMarkovFeedback (ℝ × ℝ) Control where
  action := fun _ => PUnit.unit
  measurable_action := measurable_const

def rTrajectory : (a : Bool) → RFeedback a → RState a → ℝ → ℝ → RState a
  | false, _, x, _, _ => x
  | true, _, x, T, s => flow2 x T s

def rRunningCost : (a : Bool) → RFeedback a → RState a → ℝ → ℝ
  | false, _, _, _ => 1
  | true, _, p, _ => runningCost p.1 0

def rOptimalValue : (a : Bool) → RState a → ℝ → ℝ
  | false, _, T => lowerValue T
  | true, p, T => value2 p T

def rOptimalPolicy : (a : Bool) → (x : RState a) → ℝ → RFeedback a
  | false, _, _ => PUnit.unit
  | true, _, _ => feedback0

def rAdmissible : (a : Bool) → RFeedback a → RState a → ℝ → Prop
  | false, _, _, _ => True
  | true, _, _, _ => True

theorem top_lintegral_eq (p : ℝ × ℝ) (T : ℝ) :
    ENNReal.ofReal (value2 p T) = ∫⁻ s,
      ENNReal.ofReal (theorem26DiscountWeight 1 T s * runningCost (flow2 p T s).1 s)
        ∂futureLebesgueMeasure T := by
  exact source_top_lintegral_eq p.1 T

noncomputable def rData : Theorem24NonnegativeTimeData RState RFeedback where
  rho := 1
  rho_pos := by norm_num
  trajectory := rTrajectory
  runningCost := rRunningCost
  admissible := rAdmissible
  optimalValue := rOptimalValue
  optimalPolicy := rOptimalPolicy
  trajectory_initial := by
    intro a π x T hT hπ
    cases a with
    | false => rfl
    | true => simp [rTrajectory, flow2, flow]
  runningCost_nonnegative := by
    intro a π x t
    cases a with
    | false => norm_num [rRunningCost]
    | true => simp [rRunningCost, runningCost]; positivity
  measurable_cost := by
    intro a x T π hT hπ
    cases a with
    | false => fun_prop [rRunningCost, theorem26DiscountWeight]
    | true => fun_prop [rTrajectory, rRunningCost, runningCost, theorem26DiscountWeight, flow2, flow]
  optimal_cost_integrable := by
    intro a x T hT
    cases a with
    | false => exact lower_discounted_integrand_integrable T
    | true => exact discountedIntegrand_integrable x.1 T
  optimal_policy_admissible := by
    intro a x T hT
    cases a <;> trivial
  optimal_value_attained := by
    intro a x T hT
    cases a <;> rfl
  optimal_value_minimal := by
    intro a x T π hT hπ
    cases a with
    | false =>
        apply le_of_eq
        simpa [rOptimalValue, rTrajectory, rRunningCost, rAdmissible, lowerRunningCost] using
          source_lower_lintegral_eq T
    | true =>
        apply le_of_eq
        simpa [rOptimalValue, rTrajectory, rRunningCost, rAdmissible, runningCost] using
          top_lintegral_eq x T
  condition24A := by
    intro a ha x T hT π hπ
    cases a with
    | false =>
        simpa [rRunningCost, rTrajectory, lowerRunningCost] using lower_condition24A () T
    | true => exact (lt_irrefl (⊤ : Bool) ha).elim

/-! ## 定理26 のダイナミクス（輪への指数収束） -/

local instance rTopPseudoMetric : PseudoMetricSpace (RState (⊤ : Bool)) := by
  change PseudoMetricSpace (ℝ × ℝ); infer_instance

local instance rTopMeasurableSpace : MeasurableSpace (RState (⊤ : Bool)) := by
  change MeasurableSpace (ℝ × ℝ); infer_instance

local instance rTopBorelSpace : BorelSpace (RState (⊤ : Bool)) := by
  change BorelSpace (ℝ × ℝ); infer_instance

local instance rTopProductBorelSpace : BorelSpace (Set.Ici (0 : ℝ) × RState (⊤ : Bool)) := by
  change BorelSpace (Set.Ici (0 : ℝ) × (ℝ × ℝ)); infer_instance

/-- `W(r,φ)=r²`。 -/
def W2 (p : ℝ × ℝ) (t : ℝ) : ℝ := lyapunov p.1 t

theorem W2_along (x : ℝ × ℝ) (T : ℝ) : (fun s => W2 (flow2 x T s) s) = WAlong x.1 T := rfl

theorem target_eq (T : ℝ) :
    theorem26ZeroValueTarget Set.univ (rData.optimalValue (⊤ : Bool)) T = ring T := by
  ext p
  simp [theorem26ZeroValueTarget, rData, rOptimalValue, value2_eq, ring]

noncomputable def rDynamics : Theorem26NonnegativeTimeDynamics rData Control where
  policyEquiv := Equiv.refl _
  feedback := feedback0
  alive := Set.univ
  feedback_attains_optimum := by
    intro x T hT hx
    have hEq : rData.optimalPolicy (⊤ : Bool) x T = feedback0 := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [← hEq]; exact rData.optimal_policy_admissible (⊤ : Bool) x T hT
    · rw [← hEq]; exact rData.optimal_cost_integrable (⊤ : Bool) x T hT
    · rw [← hEq]; exact rData.optimal_value_attained (⊤ : Bool) x T hT
  W := W2
  ω := fun r => r ^ 2
  c₁ := 1
  c₂ := 1
  rate := 2
  c₁_pos := by norm_num
  c₂_pos := by norm_num
  rate_pos := by norm_num
  trajectory_alive := by intro x T s hT hx hTs; exact Set.mem_univ _
  target_nonempty := by
    intro T hT
    rw [target_eq, ring_eq]; exact ⟨((0 : ℝ), (0 : ℝ)), rfl⟩
  target_closed := by
    intro T hT
    rw [target_eq]; exact ring_closed T
  target_invariant := by
    intro x T s hT hmem hTs
    rw [target_eq] at hmem ⊢
    rw [ring_eq] at hmem ⊢
    have hx0 : x.1 = 0 := hmem
    show (flow2 x T s).1 = 0
    simp [flow2, flow, hx0]
  W_absolutelyContinuous := by
    intro x T s hT hx hTs
    let x' : ℝ × ℝ := x
    have hregular : ContDiffOn ℝ 1 (WAlong x'.1 T) (Set.uIcc T s) := by
      have hglobal : ContDiff ℝ 1 (WAlong x'.1 T) := by
        unfold WAlong lyapunov flow
        fun_prop
      exact hglobal.contDiffOn
    have hac := hregular.absolutelyContinuousOnInterval
    rw [sourceNormedMetric_eq_real] at hac
    change AbsolutelyContinuousOnInterval (fun s => W2 (flow2 x T s) s) T s
    rw [W2_along]
    exact hac
  W_nonnegative := by
    intro x T s hT hx hTs
    let x' : ℝ × ℝ := x
    exact sq_nonneg (flow x'.1 T s)
  W_rightSlope := by
    intro x T u hT hx hTu
    let x' : ℝ × ℝ := x
    have := Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
      (WAlong x'.1 T) u (-2 * WAlong x'.1 T u) (-2 * WAlong x'.1 T u)
      (WAlong_hasDerivAt x'.1 T u) le_rfl
    exact this
  W_lower_distance_bound := by
    intro x T s hT hx hTs
    rw [target_eq s]
    change 1 * (Metric.infDist (flow2 x T s) (ring s)) ^ 2 ≤ W2 (flow2 x T s) s
    rw [infDist_ring_sq]
    simp [W2, lyapunov]
  W_upper_distance_bound := by
    intro x T s hT hx hTs
    rw [target_eq s]
    change W2 (flow2 x T s) s ≤ 1 * (Metric.infDist (flow2 x T s) (ring s)) ^ 2
    rw [infDist_ring_sq]
    simp [W2, lyapunov]
  ω_continuous := by fun_prop
  ω_zero := by norm_num
  ω_nonnegative := by intro r hr; positivity
  ω_monotone_on_nonnegative := by
    intro r₁ r₂ hr₁ hr₁₂
    nlinarith [sq_nonneg (r₂ - r₁)]
  value_distance_bound := by
    intro y t ht hy
    change 0 ≤ value2 y t ∧ value2 y t ≤ (Metric.infDist y (theorem26ZeroValueTarget Set.univ
      (rData.optimalValue (⊤ : Bool)) t)) ^ 2
    rw [target_eq, infDist_ring_sq, value2_eq]
    exact ⟨sq_nonneg _, le_rfl⟩

/-! ## 定理26の結論（動的寂静） -/

theorem ring_theorem26 (x : ℝ × ℝ) (T : ℝ) (hT : 0 ≤ T) :
    -- 空未満の層では零苦不能（`J*_a>0`、PZS 不成立）
    (∀ y : RState false, 0 < rData.optimalValue false y T ∧
      ¬ FeedbackPZS (rData.admissible false) (fun _ => futureLebesgueMeasure T)
        (fun π z t s => rData.runningCost false π (rData.trajectory false π z t s) s) y T) ∧
    -- 最高抽象度: PZS ⇔ 輪への所属
    (FeedbackPZS (rData.admissible (⊤ : Bool)) futureLebesgueMeasure
        (fun π y t s => rData.runningCost (⊤ : Bool) π (rData.trajectory (⊤ : Bool) π y t s) s) x T ↔
      x ∈ ring T) ∧
    -- (26.2): W と輪への距離の指数減衰
    (∀ s ≥ T, (flow2 x T s).1 ^ 2 ≤ x.1 ^ 2 * Real.exp (-2 * (s - T)) ∧
      Metric.infDist (flow2 x T s) (ring s) ≤ |x.1| * Real.exp (-(s - T))) ∧
    -- J*→0
    Filter.Tendsto (fun s => value2 (flow2 x T s) s) Filter.atTop (nhds 0) := by
  have h := theorem24_to26_from_nonnegativeTimeData rData rDynamics x T hT (Set.mem_univ x)
  obtain ⟨hlow, hpzs, hconv, hval, -, -⟩ := h
  refine ⟨fun y => hlow false (by decide) y, ?_, ?_, ?_⟩
  · have halive : rDynamics.alive = Set.univ := rfl
    have := hpzs
    rw [halive, target_eq] at this
    exact this
  · intro s hs
    have hc := hconv s hs
    have halive : rDynamics.alive = Set.univ := rfl
    refine ⟨?_, ?_⟩
    · have h1 := hc.1
      simp only [rDynamics, W2, lyapunov] at h1
      simpa [rData, rTrajectory] using h1
    · have h2 := hc.2
      rw [halive, target_eq] at h2
      simp only [rDynamics, W2, lyapunov] at h2
      have h3 := h2
      simp [rData, rTrajectory, Real.sqrt_sq_eq_abs] at h3
      simpa [mul_comm] using h3
  · simpa [rDynamics, rData, rOptimalValue, rTrajectory] using hval

/-- 動的寂静: 輪の上から出発すれば全時刻で輪の上（`J*=0`）に留まり、位相は動き続ける。 -/
theorem dynamic_quiescence (x : ℝ × ℝ) (T : ℝ) (hx : x ∈ ring T) :
    ∀ s ≥ T, flow2 x T s ∈ ring s ∧ value2 (flow2 x T s) s = 0 ∧
      (flow2 x T s).2 = x.2 + 3 / 2 * (s - T) := by
  intro s hs
  have hx0 : x.1 = 0 := by rw [ring_eq] at hx; exact hx
  have h1 : (flow2 x T s).1 = 0 := by simp [flow2, flow, hx0]
  refine ⟨by rw [ring_eq]; exact h1, ?_, by simp [flow2, omg]⟩
  rw [value2_eq, h1]; norm_num

/-- 位相は静止しない: 輪の上でも異なる時刻で状態は異なる（`φ(s)≠φ(T)`）。 -/
theorem phase_keeps_moving (x : ℝ × ℝ) (T s : ℝ) (hs : T < s) :
    (flow2 x T s).2 ≠ (flow2 x T T).2 := by
  simp only [flow2, omg]
  intro h
  nlinarith

end Tomabechi.Examples.Theorem26Ring

end
