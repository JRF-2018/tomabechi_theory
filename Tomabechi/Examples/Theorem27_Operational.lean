import Theorem24_26_27
import Theorem24_26_Model

/-!
# 定理27の一般定理（操作的無明の同値）の適用 (`examples/theorem26_27_dynamic_quiescence.py`)

状態 `x=(r,φ)∈E2=EuclideanSpace ℝ (Fin 2)`、制御 `u∈E2`、アクチュエータ `G=id`、自然ドリフト
`f0(x)=(-μ r,0)`、指定方策 `π0(t,x)=u0=(-κ r,ω)`（`μ=κ=1/2`, `ω=3/2`）、閉ループ `ṙ=-r`, `φ̇=3/2`。
基準入力 A: `utr=(μ r,ω)`（27-A2 を満たす: `F_tr=f0+utr=(0,ω)` は `W=r²` を変えない）。
走行コスト `3r²`、割引 `ρ=1`、空未満の層は走行コスト 1（`Theorem26_RingModel` と同じ値・目標）。

**モデル化の注意:** `Feedback ⊤` は Borel Markov 全体と同値（`policyEquiv`）である必要があるが、任意の
feedback の閉ループは解けないので、**許容方策を一点 `π0` に制限**し（`admissible π := π=π0`）、
軌道は `π` に依らず `π0` の流れとする（無選択の特殊モデルの一般化）。基準入力 `utr` は 27-A の定義どおり
独立に固定する入力で、許容性は要求されない。
-/

noncomputable section

namespace Tomabechi.Examples.Theorem27Op

open Tomabechi.Theorem24_26 Tomabechi.Theorem24_26_Model MeasureTheory

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def e0 : E2 := EuclideanSpace.single 0 1
def e1 : E2 := EuclideanSpace.single 1 1

def mu : ℝ := 1 / 2
def kap : ℝ := 1 / 2
def omg : ℝ := 3 / 2

theorem e0_apply0 : e0 0 = 1 := by simp [e0]
theorem e0_apply1 : e0 1 = 0 := by simp [e0]
theorem e1_apply0 : e1 0 = 0 := by simp [e1]
theorem e1_apply1 : e1 1 = 1 := by simp [e1]

/-- 閉ループの流れ `(r e^{T-s}, φ+ω(s-T))`。 -/
def flowE (x : E2) (T s : ℝ) : E2 := flow (x 0) T s • e0 + (x 1 + omg * (s - T)) • e1

theorem flowE_0 (x : E2) (T s : ℝ) : flowE x T s 0 = flow (x 0) T s := by
  simp [flowE, e0_apply0, e1_apply0]
theorem flowE_1 (x : E2) (T s : ℝ) : flowE x T s 1 = x 1 + omg * (s - T) := by
  simp [flowE, e0_apply1, e1_apply1]

def value3 (x : E2) (T : ℝ) : ℝ := value (x 0) T

theorem value3_eq (x : E2) (T : ℝ) : value3 x T = x 0 ^ 2 := value_eq_sq _ _

/-- 零価値目標 `{r=0}`（輪）。 -/
def ringE (T : ℝ) : Set E2 := theorem26ZeroValueTarget Set.univ value3 T

theorem ringE_eq (T : ℝ) : ringE T = {x | x 0 = 0} := by
  ext p; simp [ringE, theorem26ZeroValueTarget, value3_eq]

theorem ringE_closed (T : ℝ) : IsClosed (ringE T) := by
  rw [ringE_eq]
  exact isClosed_eq (by fun_prop) continuous_const

/-- `dist(x,輪)=|r|`（L² 距離でも）。 -/
theorem infDist_ringE (x : E2) (T : ℝ) : Metric.infDist x (ringE T) = |x 0| := by
  rw [ringE_eq]
  have hne : ({p | p 0 = 0} : Set E2).Nonempty := ⟨0, rfl⟩
  apply le_antisymm
  · have hmem : x - (x 0) • e0 ∈ ({p | p 0 = 0} : Set E2) := by
      show (x - (x 0) • e0) 0 = 0
      simp [e0_apply0]
    have h := Metric.infDist_le_dist_of_mem (x := x) hmem
    refine h.trans ?_
    rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs]
    have : ‖e0‖ = 1 := by simp [e0]
    rw [this, mul_one]
  · rw [Metric.le_infDist hne]
    intro q hq
    have hq0 : q 0 = 0 := hq
    have h := PiLp.norm_apply_le (x - q) 0
    rw [dist_eq_norm]
    simpa [hq0, Real.norm_eq_abs] using h

theorem infDist_ringE_sq (x : E2) (T : ℝ) : Metric.infDist x (ringE T) ^ 2 = x 0 ^ 2 := by
  rw [infDist_ringE, sq_abs]

/-! ## 定理24/26 の共通データ（許容方策を `π0` の一点に制限） -/

abbrev RState : Bool → Type
  | false => Unit
  | true => E2

abbrev RFeedback : Bool → Type
  | false => PUnit
  | true => NonnegativeTimeBorelMarkovFeedback E2 E2

/-- 指定方策 `π0(t,x)=u0=(-κ r,ω)`。 -/
def pi0Action (q : Set.Ici (0 : ℝ) × E2) : E2 := (-kap * q.2 0) • e0 + omg • e1

local instance rTopBorel : BorelSpace (Set.Ici (0 : ℝ) × RState (⊤ : Bool)) := by
  change BorelSpace (Set.Ici (0 : ℝ) × E2); infer_instance

def pi0 : NonnegativeTimeBorelMarkovFeedback E2 E2 where
  action := pi0Action
  measurable_action := by
    unfold pi0Action
    exact Continuous.measurable (by fun_prop)

def rTraj : (a : Bool) → RFeedback a → RState a → ℝ → ℝ → RState a
  | false, _, x, _, _ => x
  | true, _, x, T, s => flowE x T s

def rCost : (a : Bool) → RFeedback a → RState a → ℝ → ℝ
  | false, _, _, _ => 1
  | true, _, x, _ => runningCost (x 0) 0

def rOpt : (a : Bool) → RState a → ℝ → ℝ
  | false, _, T => lowerValue T
  | true, x, T => value3 x T

def rPolicy : (a : Bool) → (x : RState a) → ℝ → RFeedback a
  | false, _, _ => PUnit.unit
  | true, _, _ => pi0

/-- 許容方策は `π0` のみ（無選択の特殊化）。 -/
def rAdm : (a : Bool) → RFeedback a → RState a → ℝ → Prop
  | false, _, _, _ => True
  | true, π, _, _ => π = pi0

theorem cost_flowE (x : E2) (T s : ℝ) : runningCost (flowE x T s 0) 0 = runningCost (flow (x 0) T s) 0 := by
  rw [flowE_0]

theorem top_lintegral (x : E2) (T : ℝ) :
    ENNReal.ofReal (value3 x T) = ∫⁻ s,
      ENNReal.ofReal (theorem26DiscountWeight 1 T s * runningCost (flowE x T s 0) 0)
        ∂futureLebesgueMeasure T := by
  simp only [cost_flowE]
  exact source_top_lintegral_eq (x 0) T

noncomputable def rData : Theorem24NonnegativeTimeData RState RFeedback where
  rho := 1
  rho_pos := by norm_num
  trajectory := rTraj
  runningCost := rCost
  admissible := rAdm
  optimalValue := rOpt
  optimalPolicy := rPolicy
  trajectory_initial := by
    intro a π x T hT hπ
    cases a with
    | false => rfl
    | true =>
        change flowE x T T = x
        ext i; fin_cases i
        · simp [flowE_0, flow]
        · simp [flowE_1]
  runningCost_nonnegative := by
    intro a π x t
    cases a with
    | false => norm_num [rCost]
    | true => simp [rCost, runningCost]; positivity
  measurable_cost := by
    intro a x T π hT hπ
    cases a with
    | false => fun_prop [rCost, theorem26DiscountWeight]
    | true =>
        change Measurable (fun s => ENNReal.ofReal (theorem26DiscountWeight 1 T s *
          runningCost (flowE x T s 0) 0))
        simp only [cost_flowE]
        fun_prop [runningCost, theorem26DiscountWeight, flow]
  optimal_cost_integrable := by
    intro a x T hT
    cases a with
    | false => exact lower_discounted_integrand_integrable T
    | true =>
        change Integrable (fun s => theorem26DiscountWeight 1 T s * runningCost (flowE x T s 0) 0)
          (futureLebesgueMeasure T)
        simp only [cost_flowE]
        exact discountedIntegrand_integrable (x 0) T
  optimal_policy_admissible := by
    intro a x T hT
    cases a with
    | false => trivial
    | true => rfl
  optimal_value_attained := by
    intro a x T hT
    cases a with
    | false => rfl
    | true =>
        change value3 x T = ∫ s, theorem26DiscountWeight 1 T s * runningCost (flowE x T s 0) 0
          ∂futureLebesgueMeasure T
        simp only [cost_flowE]
        rfl
  optimal_value_minimal := by
    intro a x T π hT hπ
    cases a with
    | false =>
        apply le_of_eq
        simpa [rOpt, rTraj, rCost, rAdm, lowerRunningCost] using source_lower_lintegral_eq T
    | true =>
        apply le_of_eq
        simpa [rOpt, rTraj, rCost, rAdm, runningCost] using top_lintegral x T
  condition24A := by
    intro a ha x T hT π hπ
    cases a with
    | false => simpa [rCost, rTraj, lowerRunningCost] using lower_condition24A () T
    | true => exact (lt_irrefl (⊤ : Bool) ha).elim

/-! ## 定理26 のダイナミクス -/

local instance rTopPseudo : PseudoMetricSpace (RState (⊤ : Bool)) := inferInstanceAs (PseudoMetricSpace E2)
local instance rTopNormed : NormedAddCommGroup (RState (⊤ : Bool)) := inferInstanceAs (NormedAddCommGroup E2)
local instance rTopInner : InnerProductSpace ℝ (RState (⊤ : Bool)) := inferInstanceAs (InnerProductSpace ℝ E2)
local instance rTopComplete : CompleteSpace (RState (⊤ : Bool)) := inferInstanceAs (CompleteSpace E2)
local instance rTopSMul : ContinuousSMul ℝ (RState (⊤ : Bool)) := inferInstanceAs (ContinuousSMul ℝ E2)
local instance rTopMeas : MeasurableSpace (RState (⊤ : Bool)) := inferInstanceAs (MeasurableSpace E2)
local instance rTopBorelS : BorelSpace (RState (⊤ : Bool)) := inferInstanceAs (BorelSpace E2)

/-- `W(y)=r²`。 -/
def W3 (y : E2) (t : ℝ) : ℝ := lyapunov (y 0) t

theorem W3_along (x : E2) (T : ℝ) : (fun s => W3 (flowE x T s) s) = WAlong (x 0) T := by
  funext s; simp [W3, lyapunov, WAlong, flowE_0]

theorem target_eq (T : ℝ) :
    theorem26ZeroValueTarget Set.univ (rData.optimalValue (⊤ : Bool)) T = ringE T := by
  ext p
  simp [theorem26ZeroValueTarget, rData, rOpt, value3_eq, ringE]

noncomputable def rDyn : Theorem26NonnegativeTimeDynamics rData E2 where
  policyEquiv := Equiv.refl _
  feedback := pi0
  alive := Set.univ
  feedback_attains_optimum := by
    intro x T hT hx
    have hEq : rData.optimalPolicy (⊤ : Bool) x T = pi0 := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [← hEq]; exact rData.optimal_policy_admissible (⊤ : Bool) x T hT
    · rw [← hEq]; exact rData.optimal_cost_integrable (⊤ : Bool) x T hT
    · rw [← hEq]; exact rData.optimal_value_attained (⊤ : Bool) x T hT
  W := W3
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
    rw [target_eq, ringE_eq]; exact ⟨(0 : E2), rfl⟩
  target_closed := by
    intro T hT
    rw [target_eq]; exact ringE_closed T
  target_invariant := by
    intro x T s hT hmem hTs
    rw [target_eq] at hmem ⊢
    rw [ringE_eq] at hmem ⊢
    have hx0 : (x : E2) 0 = 0 := hmem
    show (flowE x T s) 0 = 0
    simp [flowE_0, flow, hx0]
  W_absolutelyContinuous := by
    intro x T s hT hx hTs
    let x' : E2 := x
    have hregular : ContDiffOn ℝ 1 (WAlong (x' 0) T) (Set.uIcc T s) := by
      have hglobal : ContDiff ℝ 1 (WAlong (x' 0) T) := by
        unfold WAlong lyapunov flow
        fun_prop
      exact hglobal.contDiffOn
    have hac := hregular.absolutelyContinuousOnInterval
    rw [sourceNormedMetric_eq_real] at hac
    change AbsolutelyContinuousOnInterval (fun s => W3 (flowE x' T s) s) T s
    rw [W3_along]
    exact hac
  W_nonnegative := by
    intro x T s hT hx hTs
    let x' : E2 := x
    show 0 ≤ lyapunov (flowE x' T s 0) s
    exact sq_nonneg _
  W_rightSlope := by
    intro x T u hT hx hTu
    let x' : E2 := x
    have := Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
      (WAlong (x' 0) T) u (-2 * WAlong (x' 0) T u) (-2 * WAlong (x' 0) T u)
      (WAlong_hasDerivAt (x' 0) T u) le_rfl
    have hfun : (fun s => W3 (flowE x' T s) s) = WAlong (x' 0) T := W3_along x' T
    change Tomabechi.Theorem1.RightSlopeBound (fun s => W3 (flowE x' T s) s) u
      (-2 * W3 (flowE x' T u) u)
    rw [hfun]
    have hu : W3 (flowE x' T u) u = WAlong (x' 0) T u := congrFun hfun u
    rw [hu]
    exact this
  W_lower_distance_bound := by
    intro x T s hT hx hTs
    rw [target_eq s]
    change 1 * (Metric.infDist (flowE x T s) (ringE s)) ^ 2 ≤ W3 (flowE x T s) s
    rw [infDist_ringE_sq]
    simp [W3, lyapunov]
  W_upper_distance_bound := by
    intro x T s hT hx hTs
    rw [target_eq s]
    change W3 (flowE x T s) s ≤ 1 * (Metric.infDist (flowE x T s) (ringE s)) ^ 2
    rw [infDist_ringE_sq]
    simp [W3, lyapunov]
  ω_continuous := by fun_prop
  ω_zero := by norm_num
  ω_nonnegative := by intro r hr; positivity
  ω_monotone_on_nonnegative := by
    intro r₁ r₂ hr₁ hr₁₂
    nlinarith [sq_nonneg (r₂ - r₁)]
  value_distance_bound := by
    intro y t ht hy
    change 0 ≤ value3 y t ∧ value3 y t ≤ (Metric.infDist y (theorem26ZeroValueTarget Set.univ
      (rData.optimalValue (⊤ : Bool)) t)) ^ 2
    rw [target_eq, infDist_ringE_sq, value3_eq]
    exact ⟨sq_nonneg _, le_rfl⟩

/-! ## 定理27の入力（27-A） -/

/-- 自然ドリフト `f0=(-μ r,0)`（軌道上）。 -/
def driftE (x : E2) (T : ℝ) (t : ℝ) : E2 := (-mu * flow (x 0) T t) • e0

/-- 基準入力 A: `utr=(μ r,ω)`（27-A2 を満たす）。 -/
def utrE (x : E2) (T : ℝ) (t : ℝ) : E2 := (mu * flow (x 0) T t) • e0 + omg • e1

/-- 指定入力 `u0=(-κ r,ω)`。 -/
def u0E (x : E2) (T : ℝ) (t : ℝ) : E2 := (-kap * flow (x 0) T t) • e0 + omg • e1

/-- 時刻 `t` の `W` の（状態部分の）勾配 `2r e0`。 -/
def gradWE (x : E2) (T : ℝ) (t : ℝ) : E2 := (2 * flow (x 0) T t) • e0

/-- 全微分 `dW t (a,z)=2 r z_0`。 -/
def dWE (x : E2) (T : ℝ) (t : ℝ) : ℝ × E2 →L[ℝ] ℝ :=
  (2 * flow (x 0) T t) • ((EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E2))

theorem dWE_apply (x : E2) (T t : ℝ) (a : ℝ) (z : E2) : dWE x T t (a, z) = 2 * flow (x 0) T t * z 0 := by
  simp [dWE]

/-- アクチュエータ `G=id`。 -/
def GE : E2 →L[ℝ] E2 := ContinuousLinearMap.id ℝ E2

theorem mu_add_kap : mu + kap = 1 := by norm_num [mu, kap]

/-- 閉ループ軌道の微分: `ṙ=-(μ+κ)r=-r`, `φ̇=ω`。 -/
theorem hasDerivAt_flowE (x : E2) (T t : ℝ) :
    HasDerivAt (fun s => flowE x T s) (driftE x T t + GE (u0E x T t)) t := by
  have hr : HasDerivAt (fun s => flow (x 0) T s) (-(flow (x 0) T t)) t := flow_hasDerivAt (x 0) T t
  have hp : HasDerivAt (fun s => x 1 + omg * (s - T)) omg t := by
    have := ((hasDerivAt_id t).sub_const T).const_mul omg |>.const_add (x 1)
    simpa using this
  have h := (hr.smul_const e0).add (hp.smul_const e1)
  unfold flowE
  refine h.congr_deriv ?_
  unfold driftE u0E GE
  simp only [ContinuousLinearMap.id_apply]
  ext i; fin_cases i
  · simp [e0_apply0, e1_apply0, mu, kap]; ring
  · simp [e0_apply1, e1_apply1]

/-! ## 27-A の各前提 -/

theorem inner_gradWE (x : E2) (T t : ℝ) (z : E2) :
    inner ℝ (gradWE x T t) z = 2 * flow (x 0) T t * z 0 := by
  unfold gradWE e0
  rw [real_inner_smul_left, EuclideanSpace.inner_single_left]
  simp

theorem stateGrad (x : E2) (T t : ℝ) (z : E2) : dWE x T t (0, z) = inner ℝ (gradWE x T t) z := by
  rw [dWE_apply, inner_gradWE]

/-- 基準閉ループ `F_tr=f0+G utr=(0,ω)` は `W` を変えない（27-A2）。 -/
theorem reference_cancellation (x : E2) (T t : ℝ) :
    dWE x T t (1, 0) + inner ℝ (gradWE x T t) (driftE x T t + GE (utrE x T t)) = 0 := by
  rw [inner_gradWE, dWE_apply]
  simp only [driftE, utrE, GE, ContinuousLinearMap.id_apply]
  have h0 : ((-mu * flow (x 0) T t) • e0 + ((mu * flow (x 0) T t) • e0 + omg • e1) : E2) 0 = 0 := by
    simp [e1_apply0]
  rw [h0]
  simp

/-- 同じ `x` から出る別時刻の再始動恒等式。 -/
theorem flowE_semigroup (y : E2) (a s t : ℝ) : flowE (flowE y a s) s t = flowE y a t := by
  ext i; fin_cases i
  · simp [flowE_0, flow_semigroup]
  · simp [flowE_1, omg]; ring

theorem u0E_eq_action (x : E2) (T t : ℝ) (ht : 0 ≤ t) :
    u0E x T t = pi0Action (⟨t, ht⟩, flowE x T t) := by
  simp [u0E, pi0Action, flowE_0]

theorem pzs_iff (y : E2) (t : ℝ) (ht : 0 ≤ t) :
    FeedbackPZS (rData.admissible (⊤ : Bool)) futureLebesgueMeasure
      (fun π z a s => rData.runningCost (⊤ : Bool) π (rData.trajectory (⊤ : Bool) π z a s) s) y t ↔
      y ∈ ringE t := by
  have h := theorem24_to26_from_nonnegativeTimeData rData rDyn y t ht (Set.mem_univ y)
  have halive : rDyn.alive = Set.univ := rfl
  have h2 := h.2.1
  rw [halive, target_eq] at h2
  exact h2

theorem hasFDerivAt_W (x : E2) (T t : ℝ) :
    HasFDerivAt (fun p : ℝ × E2 => W3 p.2 p.1) (dWE x T t) (t, flowE x T t) := by
  have h1 : HasFDerivAt (fun p : ℝ × E2 => p.2 0)
      ((EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E2)) (t, flowE x T t) :=
    (ContinuousLinearMap.hasFDerivAt
      ((EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E2)))
  have h2 := h1.pow 2
  have hfun : (fun p : ℝ × E2 => W3 p.2 p.1) = fun p : ℝ × E2 => (p.2 0) ^ 2 := by
    funext p; simp [W3, lyapunov]
  rw [hfun]
  refine h2.congr_fderiv ?_
  ext q
  · simp [dWE]
  · simp [dWE, flowE_0]

theorem locallyLipschitz_W (x : E2) (T : ℝ) :
    LocallyLipschitzOn (Set.Ici T) (fun s => W3 (flowE x T s) s) := by
  rw [W3_along]
  have : ContDiff ℝ 1 (WAlong (x 0) T) := by
    unfold WAlong lyapunov flow; fun_prop
  exact this.locallyLipschitz.locallyLipschitzOn

/-- 定理27（操作的無明の同値）をこの具体モデルに適用した結論。 -/
theorem operational_ignorance (x : E2) (T : ℝ) (hT : 0 ≤ T) :
    -- (27.6)(27.10): 無明（輪の外）⇔ Lyapunov 残差の下降率が正
    (∀ t, T ≤ t → (flowE x T t ∉ ringE t ↔
      0 < Tomabechi.Theorem27.residualDescentRateAlong (fun s y => W3 y s)
        (fun s => flowE x T s) t)) ∧
    -- (27.10): 無明 ⇔ 行（実アクチュエータの正の寄与 `-⟪∇W,G(u0-utr)⟫>0`）
    (∀ᵐ t ∂futureLebesgueMeasure T, ∀ htt : T ≤ t,
      (flowE x T t ∉ ringE t ↔
        0 < -(inner ℝ (gradWE x T t) (GE (u0E x T t - utrE x T t))))) ∧
    -- (27.8): 無明のとき制御差のノルムは正（下界 `λ c₁ dist²/L₂₇`）
    (∀ᵐ t ∂futureLebesgueMeasure T, flowE x T t ∉ ringE t →
      0 < ‖u0E x T t - utrE x T t‖) := by
  have halive : rDyn.alive = Set.univ := rfl
  have hL : 0 < 2 * |x 0| + 1 := by positivity
  have h := Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae
    (A := Bool) (State := RState) (Feedback := RFeedback) (Control := E2)
    rfl rfl rData rDyn (x : RState (⊤ : Bool)) T hT (by rw [halive]; trivial)
    (fun y a s t ha has hst hadm => by
      change flowE (flowE y a s) s t = flowE y a t
      exact flowE_semigroup y a s t)
    (fun t => dWE x T t) (fun t => gradWE x T t) (fun t => driftE x T t)
    (fun t => u0E x T t) (fun t => utrE x T t) (fun _ => GE)
    (Filter.Eventually.of_forall fun t => hasDerivAt_flowE x T t)
    (Filter.Eventually.of_forall fun t z => stateGrad x T t z)
    (Filter.Eventually.of_forall fun t => reference_cancellation x T t)
    (locallyLipschitz_W x T)
    (Filter.Eventually.of_forall fun t => hasFDerivAt_W x T t)
    (fun t htt => u0E_eq_action x T t (hT.trans htt))
    (2 * |x 0| + 1) hL
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Ici : MeasurableSet (Set.Ici T))] with t ht _ v
      rw [show (GE v) = v from rfl, inner_gradWE]
      have hr : |flow (x 0) T t| ≤ |x 0| := by
        unfold flow
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have : Real.exp (T - t) ≤ 1 := by rw [Real.exp_le_one_iff]; exact sub_nonpos.2 ht
        nlinarith [abs_nonneg (x 0)]
      have hv : |v 0| ≤ ‖v‖ := by
        have := PiLp.norm_apply_le v 0
        simpa [Real.norm_eq_abs] using this
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [abs_nonneg (v 0), abs_nonneg (flow (x 0) T t), norm_nonneg v,
        mul_le_mul hr hv (abs_nonneg _) (abs_nonneg _)])
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have this : (¬ FeedbackPZS (rData.admissible (⊤ : Bool)) futureLebesgueMeasure
        (fun π z a s => rData.runningCost (⊤ : Bool) π (rData.trajectory (⊤ : Bool) π z a s) s)
        (flowE x T t) t ↔
        0 < Tomabechi.Theorem27.residualDescentRateAlong (fun s y => W3 y s)
          (fun s => flowE x T s) t) := h1 t ht
    rw [← pzs_iff (flowE x T t) t (hT.trans ht)]
    exact this
  · filter_upwards [h2] with t ht htt
    have this : (¬ FeedbackPZS (rData.admissible (⊤ : Bool)) futureLebesgueMeasure
        (fun π z a s => rData.runningCost (⊤ : Bool) π (rData.trajectory (⊤ : Bool) π z a s) s)
        (flowE x T t) t ↔
        0 < -(inner ℝ (gradWE x T t)
          (GE ((rDyn.policyEquiv rDyn.feedback).action
            ⟨⟨t, hT.trans htt⟩, flowE x T t⟩ - utrE x T t)))) := ht htt
    have e : (rDyn.policyEquiv rDyn.feedback).action ⟨⟨t, hT.trans htt⟩, flowE x T t⟩ = u0E x T t :=
      (u0E_eq_action x T t (hT.trans htt)).symm
    rw [e] at this
    rw [← pzs_iff (flowE x T t) t (hT.trans htt)]
    exact this
  · filter_upwards [h3, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Ici : MeasurableSet (Set.Ici T))] with t ht hmem hnot
    have htT : T ≤ t := hmem
    rw [← pzs_iff (flowE x T t) t (hT.trans htT)] at hnot
    exact (ht hnot).2

/-- 非空虚性: `r₀≠0`（無明の初期点）なら全時刻で輪の外にあり、したがって行の寄与が正（a.e.）。 -/
theorem ignorance_gives_action (x : E2) (T : ℝ) (hT : 0 ≤ T) (hx : x 0 ≠ 0) :
    (∀ t, flowE x T t ∉ ringE t) ∧
    ∀ᵐ t ∂futureLebesgueMeasure T, T ≤ t →
      0 < -(inner ℝ (gradWE x T t) (GE (u0E x T t - utrE x T t))) := by
  have hout : ∀ t, flowE x T t ∉ ringE t := by
    intro t ht
    rw [ringE_eq] at ht
    have h0 : flowE x T t 0 = 0 := ht
    rw [flowE_0] at h0
    unfold flow at h0
    exact hx ((mul_eq_zero.1 h0).resolve_right (Real.exp_pos _).ne')
  refine ⟨hout, ?_⟩
  filter_upwards [(operational_ignorance x T hT).2.1] with t ht htt
  exact (ht htt).1 (hout t)

end Tomabechi.Examples.Theorem27Op
