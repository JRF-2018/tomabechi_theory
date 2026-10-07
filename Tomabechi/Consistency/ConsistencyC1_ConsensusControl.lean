import Tomabechi.Consistency.ConsistencyC1_Consensus
import Tomabechi.Consistency.ConsistencyC1_HFlow
import Theorem4

/-!
# C1: 二主体合意モデル上の有限地平argmin

既存の最大ゲイン最適化核を、定理1/2で使う二主体状態空間へ移す。
制御信号 `u∈[0,3]` は平均を保ち、不一致成分を `exp(-∫u)` 倍する。
したがって選択制御 `u=3` の閉ループflowは指数率3の合意流となる。
-/

noncomputable section

namespace Tomabechi.Consistency.ConsistencyC1Consensus

open MeasureTheory
open Filter
open scoped Topology Gradient
open Tomabechi.Theorem1
open Tomabechi.Examples.Theorem2
open Tomabechi.Consistency.ConsistencyC1

/-- 可測ゲイン信号で動く二主体の明示軌道。平均は保ち、半差だけを減衰させる。 -/
def controlledConsensusState (x : AgentState) (t₀ : ℝ)
    (u : C1GainSignal) (t : ℝ) : AgentState :=
  ![meanState x + c1ControlledOrbit (halfDifference x) t₀ u t,
    meanState x - c1ControlledOrbit (halfDifference x) t₀ u t]

theorem controlledConsensusState_halfDifference (x : AgentState) (t₀ : ℝ)
    (u : C1GainSignal) (t : ℝ) :
    halfDifference (controlledConsensusState x t₀ u t) =
      c1ControlledOrbit (halfDifference x) t₀ u t := by
  simp [halfDifference, controlledConsensusState]

/-- 二主体モデルで最小化する有限地平費用。 -/
def consensusFiniteHorizonCost (x : AgentState) (t₀ T : ℝ)
    (u : C1GainSignal) : ENNReal :=
  ∫⁻ s, ENNReal.ofReal
      (1 + (halfDifference (controlledConsensusState x t₀ u s)) ^ 2)
    ∂volume.restrict (Set.Icc t₀ (t₀ + T))

theorem consensusFiniteHorizonCost_eq_scalar (x : AgentState) (t₀ T : ℝ)
    (u : C1GainSignal) :
    consensusFiniteHorizonCost x t₀ T u =
      c1FiniteHorizonCost (halfDifference x) t₀ T u := by
  unfold consensusFiniteHorizonCost c1FiniteHorizonCost
  apply lintegral_congr_ae
  filter_upwards with s
  rw [controlledConsensusState_halfDifference]

/-- 最大ゲインは同じ二主体初期状態・費用の全可測ゲイン競合に対するargmin。 -/
theorem consensus_maxGain_attains_finite_horizon_argmin
    (x : AgentState) (t₀ T : ℝ) (hT : 0 < T) :
    ∀ u : C1GainSignal,
      consensusFiniteHorizonCost x t₀ T c1MaxGainSignal ≤
        consensusFiniteHorizonCost x t₀ T u := by
  intro u
  rw [consensusFiniteHorizonCost_eq_scalar, consensusFiniteHorizonCost_eq_scalar]
  exact c1_maximum_gain_attains_finite_horizon_argmin
    (halfDifference x) t₀ T hT u

/-- 選択最大ゲインの二主体費用は有限。 -/
theorem consensus_maxGain_finite_cost (x : AgentState) (t₀ T : ℝ) :
    consensusFiniteHorizonCost x t₀ T c1MaxGainSignal < ⊤ := by
  rw [consensusFiniteHorizonCost_eq_scalar]
  exact c1_maximum_gain_finite_cost (halfDifference x) t₀ T

/-- 定理1で使う `V₀=1+Φ₂` の実際の有限地平費用。`Φ₂=8d²` なので、
既存の `1+d²` 費用とは定数倍部分が異なる。 -/
def consensusTheorem1HorizonCost (x : AgentState) (t₀ T : ℝ)
    (u : C1GainSignal) : ENNReal :=
  ∫⁻ s, ENNReal.ofReal
      (1 + DA.potential (controlledConsensusState x t₀ u s) s)
    ∂volume.restrict (Set.Icc t₀ (t₀ + T))

/-- 任意の許容ゲインが作る二主体状態は、初期箱の中にとどまる。 -/
theorem controlledConsensusState_mem_box (x : AgentState) (hx : x ∈ box)
    (t₀ s : ℝ) (u : C1GainSignal) (hs : t₀ ≤ s) :
    controlledConsensusState x t₀ u s ∈ box := by
  have hacc := c1AccumulatedGain_bounds u t₀ s hs
  have he : 0 ≤ Real.exp (-(c1AccumulatedGain u t₀ s)) ∧
      Real.exp (-(c1AccumulatedGain u t₀ s)) ≤ 1 := by
    constructor
    · exact (Real.exp_pos _).le
    · apply Real.exp_le_one_iff.mpr
      linarith [hacc.1]
  have ha : 0 ≤ (1 + Real.exp (-(c1AccumulatedGain u t₀ s))) / 2 := by linarith
  have ha1 : (1 + Real.exp (-(c1AccumulatedGain u t₀ s))) / 2 ≤ 1 := by linarith
  have hb : 0 ≤ (1 - Real.exp (-(c1AccumulatedGain u t₀ s))) / 2 := by linarith
  have hb1 : (1 - Real.exp (-(c1AccumulatedGain u t₀ s))) / 2 ≤ 1 := by linarith
  intro i
  fin_cases i
  · change |meanState x + c1ControlledOrbit (halfDifference x) t₀ u s| ≤ 1 / 4
    rw [c1ControlledOrbit]
    change |meanState x + halfDifference x *
      Real.exp (-(c1AccumulatedGain u t₀ s))| ≤ 1 / 4
    have hform : meanState x + halfDifference x * Real.exp
        (-(c1AccumulatedGain u t₀ s)) =
        ((1 + Real.exp (-(c1AccumulatedGain u t₀ s))) / 2) * x 0 +
          (1 - (1 + Real.exp (-(c1AccumulatedGain u t₀ s))) / 2) * x 1 := by
      simp [meanState, halfDifference]
      ring
    rw [hform]
    exact convexCombination_mem_box (x 0) (x 1) _ (hx 0) (hx 1) ha ha1
  · change |meanState x - c1ControlledOrbit (halfDifference x) t₀ u s| ≤ 1 / 4
    rw [c1ControlledOrbit]
    change |meanState x - halfDifference x *
      Real.exp (-(c1AccumulatedGain u t₀ s))| ≤ 1 / 4
    have hform : meanState x - halfDifference x * Real.exp
        (-(c1AccumulatedGain u t₀ s)) =
        ((1 - Real.exp (-(c1AccumulatedGain u t₀ s))) / 2) * x 0 +
          (1 - (1 - Real.exp (-(c1AccumulatedGain u t₀ s))) / 2) * x 1 := by
      simp [meanState, halfDifference]
      ring
    rw [hform]
    exact convexCombination_mem_box (x 0) (x 1) _ (hx 0) (hx 1) hb hb1

/-- 定理1の `V₀` 費用でも最大ゲインが全Borelゲイン信号上でargminを達成する。
比較は各時刻での不一致二乗の大小を直接積分する。 -/
theorem consensus_maxGain_attains_theorem1_horizon_argmin
    (x : AgentState) (hx : x ∈ box) (t₀ T : ℝ) (hT : 0 < T) :
    ∀ u : C1GainSignal,
      consensusTheorem1HorizonCost x t₀ T c1MaxGainSignal ≤
        consensusTheorem1HorizonCost x t₀ T u := by
  intro u
  unfold consensusTheorem1HorizonCost
  apply MeasureTheory.lintegral_mono_ae
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards with s hs
  have hmaxsq := c1MaxGain_orbit_sq_le (halfDifference x) t₀ s u hs.1
  have hflowSq :
      (halfDifference (controlledConsensusState x t₀ c1MaxGainSignal s)) ^ 2 ≤
        (halfDifference (controlledConsensusState x t₀ u s)) ^ 2 := by
    rw [controlledConsensusState_halfDifference, controlledConsensusState_halfDifference]
    have hmax : c1ControlledOrbit (halfDifference x) t₀ c1MaxGainSignal s =
        halfDifference x * Real.exp (-(3 * (s - t₀))) := by
      simp [c1ControlledOrbit, c1MaxGain_accumulation]
    rw [hmax]
    exact hmaxsq
  have hboxMax := controlledConsensusState_mem_box x hx t₀ s c1MaxGainSignal hs.1
  have hboxU := controlledConsensusState_mem_box x hx t₀ s u hs.1
  have hpot (v : AgentState) (hv : v ∈ box) (t : ℝ) :
      DA.potential v t = 8 * (halfDifference v) ^ 2 := by
    rw [sharedPotential_eq_coupling v hv t]
    simp [γ, halfDifference]
    ring
  have hpotMax := hpot (controlledConsensusState x t₀ c1MaxGainSignal s) hboxMax s
  rw [hpotMax, hpot (controlledConsensusState x t₀ u s) hboxU s]
  apply ENNReal.ofReal_le_ofReal
  have h8 := mul_le_mul_of_nonneg_left hflowSq (by norm_num : (0 : ℝ) ≤ 8)
  nlinarith

/-- The selected controller has finite cost for the same `V₀` used by
Theorem 1, on every positive finite horizon and initial state in the box. -/
theorem consensus_maxGain_finite_theorem1_cost
    (x : AgentState) (hx : x ∈ box) (t₀ T : ℝ) (hT : 0 < T) :
    consensusTheorem1HorizonCost x t₀ T c1MaxGainSignal < ⊤ := by
  unfold consensusTheorem1HorizonCost
  let f : ℝ → ℝ := fun s =>
    1 + 8 * (halfDifference x * Real.exp (-3 * (s - t₀))) ^ 2
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hint : Integrable f (volume.restrict (Set.Icc t₀ (t₀ + T))) :=
    hfcont.continuousOn.integrableOn_compact isCompact_Icc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc t₀ (t₀ + T))] f := by
    filter_upwards with s
    positivity
  have heq :
      (∫⁻ s, ENNReal.ofReal
        (1 + DA.potential (controlledConsensusState x t₀ c1MaxGainSignal s) s)
        ∂volume.restrict (Set.Icc t₀ (t₀ + T))) =
      ENNReal.ofReal (∫ s, f s ∂volume.restrict (Set.Icc t₀ (t₀ + T))) := by
    calc
      _ = ∫⁻ s, ENNReal.ofReal (f s)
          ∂volume.restrict (Set.Icc t₀ (t₀ + T)) := by
        apply lintegral_congr_ae
        apply (ae_restrict_iff' measurableSet_Icc).2
        filter_upwards with s hs
        have hbox := controlledConsensusState_mem_box x hx t₀ s
          c1MaxGainSignal hs.1
        have hpot := sharedPotential_eq_coupling
          (controlledConsensusState x t₀ c1MaxGainSignal s) hbox s
        apply congrArg ENNReal.ofReal
        rw [hpot]
        have hgap :
            controlledConsensusState x t₀ c1MaxGainSignal s 0 -
              controlledConsensusState x t₀ c1MaxGainSignal s 1 =
            2 * halfDifference (controlledConsensusState x t₀ c1MaxGainSignal s) := by
          simp [halfDifference]
          ring
        rw [hgap, controlledConsensusState_halfDifference]
        simp [f, c1ControlledOrbit, c1MaxGain_accumulation, γ]
        ring
      _ = ENNReal.ofReal (∫ s, f s ∂volume.restrict (Set.Icc t₀ (t₀ + T))) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
  rw [heq]
  exact ENNReal.ofReal_lt_top

/-- 全状態・全実数時刻に定義した最大ゲインの閉ループ合意flow。 -/
def consensusOptimalFlow : ClosedLoopPolicyFlow AgentState ℝ where
  admissible := fun u => 0 ≤ u ∧ u ≤ 3
  feedback := fun _ _ => 3
  vectorField := fun x u _ => ![ -(u / 2) * (x 0 - x 1), (u / 2) * (x 0 - x 1) ]
  flow := fun t₀ x t =>
    ![meanState x + halfDifference x * Real.exp (-3 * (t - t₀)),
      meanState x - halfDifference x * Real.exp (-3 * (t - t₀))]
  feedback_admissible := by intro x t; constructor <;> norm_num
  initial := by
    intro t₀ x
    ext i
    fin_cases i <;> simp [meanState, halfDifference] <;> ring
  restart := by
    intro t₀ x s t h₀s hst
    ext i
    fin_cases i <;>
      simp [meanState, halfDifference] <;>
      rw [show -(3 * (t - t₀)) = -(3 * (s - t₀)) + -(3 * (t - s)) by ring,
        Real.exp_add] <;> ring

/-- rate-3最適flowをrate-2合意flowで表す時間変換。 -/
def consensusOptimalTimeMap (t₀ t : ℝ) : ℝ := t₀ + (3 / 2 : ℝ) * (t - t₀)

theorem consensusOptimalFlow_eq_retimed (x : AgentState) (t₀ t : ℝ) :
    consensusOptimalFlow.flow t₀ x t =
      consensusFlow.flow t₀ x (consensusOptimalTimeMap t₀ t) := by
  change ![meanState x + halfDifference x * Real.exp (-3 * (t - t₀)),
      meanState x - halfDifference x * Real.exp (-3 * (t - t₀))] =
    ![meanState x + halfDifference x * Real.exp
        (-2 * (consensusOptimalTimeMap t₀ t - t₀)),
      meanState x - halfDifference x * Real.exp
        (-2 * (consensusOptimalTimeMap t₀ t - t₀))]
  have hexp : -3 * (t - t₀) = -2 * (consensusOptimalTimeMap t₀ t - t₀) := by
    unfold consensusOptimalTimeMap
    ring
  rw [hexp]

theorem consensusOptimalFlow_gap (x : AgentState) (t₀ t : ℝ) :
    (consensusOptimalFlow.flow t₀ x t) 0 - (consensusOptimalFlow.flow t₀ x t) 1 =
      (x 0 - x 1) * Real.exp (-3 * (t - t₀)) := by
  change (meanState x + halfDifference x * Real.exp (-3 * (t - t₀))) -
      (meanState x - halfDifference x * Real.exp (-3 * (t - t₀))) = _
  rw [meanState, halfDifference]
  ring

/-- rate-3最適flowは、初期箱をすべての未来時刻で保つ。 -/
theorem consensusOptimalFlow_forward_invariant (x : AgentState) (hx : x ∈ box)
    (t₀ t : ℝ) (ht : t₀ ≤ t) : consensusOptimalFlow.flow t₀ x t ∈ box := by
  have htime : t₀ ≤ consensusOptimalTimeMap t₀ t := by
    unfold consensusOptimalTimeMap
    nlinarith
  rw [consensusOptimalFlow_eq_retimed]
  exact consensusFlow_forward_invariant x hx t₀ _ htime

/-- rate-3最適flowが初期箱から生成する閉到達集合は箱そのもの。 -/
theorem consensusOptimalFlow_reachable_closure_eq_box (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀) = box := by
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ box_isClosed
    rintro y ⟨τ, hτ, hy⟩
    rcases hy with ⟨hstart, x, hx, rfl⟩
    exact consensusOptimalFlow_forward_invariant x hx t₀ τ hstart
  · intro y hy
    apply subset_closure
    refine ⟨t₀, ht₀, ?_⟩
    exact ⟨le_rfl, y, hy, (consensusOptimalFlow.initial t₀ y).symm⟩

/-- rate-3最適flow上の共有残差を表す滑らかな閉形式。 -/
def consensusOptimalResidualPath (x : AgentState) (t₀ s : ℝ) : ℝ :=
  γ * ((x 0 - x 1) * Real.exp (-3 * (s - t₀))) ^ 2

theorem consensusOptimalResidualPath_hasDerivAt (x : AgentState) (t₀ s : ℝ) :
    HasDerivAt (consensusOptimalResidualPath x t₀)
      (-2 * 3 * consensusOptimalResidualPath x t₀ s) s := by
  have hlin : HasDerivAt (fun v : ℝ => -3 * (v - t₀)) (-3) s := by
    simpa using (hasDerivAt_id s).sub_const t₀ |>.const_mul (-3)
  have hexp := (Real.hasDerivAt_exp (-3 * (s - t₀))).comp s hlin
  have hgap := hexp.const_mul (x 0 - x 1)
  have hsquare := hgap.pow 2
  have hpath := hsquare.const_mul γ
  convert hpath using 1
  · funext v
    simp [consensusOptimalResidualPath]
  · simp [consensusOptimalResidualPath]
    ring

theorem consensusOptimalResidualPath_ac (x : AgentState) (t₀ T : ℝ) :
    AbsolutelyContinuousOnInterval (consensusOptimalResidualPath x t₀) t₀ T := by
  have hcont : ContDiff ℝ 1 (consensusOptimalResidualPath x t₀) := by
    unfold consensusOptimalResidualPath
    fun_prop
  exact hcont.contDiffOn.absolutelyContinuousOnInterval

/-- 最適flow上では実共有残差が閉形式の率3 pathに一致する。 -/
def consensusOptimalPotentialAlong (x : AgentState) (t₀ : ℝ) : ℝ → ℝ :=
  fun s => DA.potential (consensusOptimalFlow.flow t₀ x s) s

theorem consensusOptimalPotentialAlong_eq (x : AgentState) (hx : x ∈ box)
    (t₀ T : ℝ) (hT : t₀ ≤ T) :
    Set.EqOn (consensusOptimalPotentialAlong x t₀)
      (consensusOptimalResidualPath x t₀) (Set.uIcc t₀ T) := by
  intro s hs
  rw [Set.uIcc_of_le hT] at hs
  change DA.potential (consensusOptimalFlow.flow t₀ x s) s = _
  rw [sharedPotential_eq_coupling _
    (consensusOptimalFlow_forward_invariant x hx t₀ s hs.1) s]
  rw [consensusOptimalFlow_gap]
  rfl

theorem consensusOptimalPotentialAlong_ac (x : AgentState) (hx : x ∈ box)
    (t₀ T : ℝ) (hT : t₀ ≤ T) :
    AbsolutelyContinuousOnInterval (consensusOptimalPotentialAlong x t₀) t₀ T := by
  apply (consensusOptimalResidualPath_ac x t₀ T).congr
  intro s hs
  exact (consensusOptimalPotentialAlong_eq x hx t₀ T hT hs).symm

/-- 最適flow上の実共有残差は有限区間でa.e.に率6で減少する。 -/
theorem consensusOptimalPotentialAlong_decay_ae (x : AgentState) (hx : x ∈ box)
    (t₀ T : ℝ) (hT : t₀ < T) :
    ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
      deriv (consensusOptimalPotentialAlong x t₀) s ≤
        -2 * 3 * consensusOptimalPotentialAlong x t₀ s := by
  have hpair : ({t₀, T} : Set ℝ) = {t₀} ∪ {T} := by ext u; simp [or_comm]
  have hnull : volume ({t₀, T} : Set ℝ) = 0 := by
    rw [hpair]
    exact measure_union_null (measure_singleton t₀) (measure_singleton T)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hnull] with s hs hIcc
  have hst₀ : s ≠ t₀ := by intro h; apply hs; simp [h]
  have hsT : s ≠ T := by intro h; apply hs; simp [h]
  have hinside : s ∈ Set.Ioo t₀ T :=
    ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hst₀), lt_of_le_of_ne hIcc.2 hsT⟩
  have hnear : consensusOptimalPotentialAlong x t₀ =ᶠ[𝓝 s]
      consensusOptimalResidualPath x t₀ := by
    have hnhds := Ioo_mem_nhds hinside.1 hinside.2
    filter_upwards [hnhds] with u hu
    apply consensusOptimalPotentialAlong_eq x hx t₀ T hT.le
    rw [Set.uIcc_of_le hT.le]
    exact ⟨hu.1.le, hu.2.le⟩
  have hderiv := (consensusOptimalResidualPath_hasDerivAt x t₀ s).congr_of_eventuallyEq hnear
  rw [hderiv.deriv]
  have hval := consensusOptimalPotentialAlong_eq x hx t₀ T hT.le (by
    rw [Set.uIcc_of_le hT.le]
    exact ⟨hinside.1.le, hinside.2.le⟩)
  rw [hval]

/-- rate-3最適flowの定理1 TCZ。元の基礎評価を `1+Φ₂` とする。 -/
def consensusOptimalTheorem1Target (t₀ t : ℝ) : Set AgentState :=
  {y | y ∈ closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀) ∧
    consensusV0 y t ≤ 1}

theorem consensusOptimalTheorem1Target_eq_shared
    (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    consensusOptimalTheorem1Target t₀ t = DA.sharedTCZ box t := by
  unfold consensusOptimalTheorem1Target
  rw [consensusOptimalFlow_reachable_closure_eq_box t₀ ht₀]
  ext x
  constructor
  · rintro ⟨hx, hV⟩
    refine ⟨hx, ?_⟩
    change 1 + DA.potential x 0 ≤ 1 at hV
    have htime : DA.potential x 0 = DA.potential x t := by
      rw [sharedPotential_eq_coupling x hx 0, sharedPotential_eq_coupling x hx t]
    rw [htime] at hV
    change DA.potential x t = 0
    apply le_antisymm
    · linarith
    · rw [sharedPotential_eq_coupling x hx t]
      unfold γ
      positivity
  · rintro ⟨hx, hpot⟩
    refine ⟨hx, ?_⟩
    change 1 + DA.potential x 0 ≤ 1
    have htime : DA.potential x 0 = DA.potential x t := by
      rw [sharedPotential_eq_coupling x hx 0, sharedPotential_eq_coupling x hx t]
    rw [htime, hpot]
    norm_num

/-- O02最適化flow上で定理1の全未来定量結論と距離収束を得る。

これは `consensusOptimalFlow` 自身を定理1のH-flowとして渡し、全有限区間条件を
rate-3共有残差の閉形式から供給する適用である。 -/
theorem consensusOptimalFlow_theorem1
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈
      closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀)) ∧
    (∀ t, t₀ ≤ t → Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (consensusOptimalTheorem1Target t₀ t) ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))) ∧
    Filter.Tendsto (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (consensusOptimalTheorem1Target t₀ t)) atTop (𝓝 0) := by
  have htarget : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (consensusOptimalTheorem1Target t₀ s).Nonempty := by
    intro T hT s hs
    rw [consensusOptimalTheorem1Target_eq_shared t₀ s ht₀]
    exact consensus_sharedTCZ_nonempty s
  have hresidual_eq : Set.EqOn
      (fun s => residual1 (consensusV0 (consensusOptimalFlow.flow t₀ x s) s) 1)
      (consensusOptimalPotentialAlong x t₀) (Set.Ici t₀) := by
    intro s hs
    change residual1 (consensusV0 (consensusOptimalFlow.flow t₀ x s) s) 1 =
      DA.potential (consensusOptimalFlow.flow t₀ x s) s
    exact consensusV0_residual_eq_potential _
      (consensusOptimalFlow_forward_invariant x hx t₀ s hs) s
  have hresidual_ac : ∀ T, t₀ ≤ T →
      AbsolutelyContinuousOnInterval
        (fun s => residual1 (consensusV0 (consensusOptimalFlow.flow t₀ x s) s) 1)
        t₀ T := by
    intro T hT
    apply (consensusOptimalPotentialAlong_ac x hx t₀ T hT).congr
    intro s hs
    exact (hresidual_eq (show s ∈ Set.Ici t₀ from by
      rw [Set.uIcc_of_le hT] at hs
      exact hs.1)).symm
  have hdecay : ∀ T, t₀ ≤ T →
      ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
        deriv (fun r => residual1 (consensusV0 (consensusOptimalFlow.flow t₀ x r) r) 1) s ≤
          -2 * 3 * residual1 (consensusV0 (consensusOptimalFlow.flow t₀ x s) s) 1 := by
    intro T hT
    rcases lt_or_eq_of_le hT with hlt | heq
    · have hpair : ({t₀, T} : Set ℝ) = {t₀} ∪ {T} := by ext u; simp [or_comm]
      have hnull : volume ({t₀, T} : Set ℝ) = 0 := by
        rw [hpair]
        exact measure_union_null (measure_singleton t₀) (measure_singleton T)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hnull] with s hs hIcc
      have hst₀ : s ≠ t₀ := by intro h; apply hs; simp [h]
      have hsT : s ≠ T := by intro h; apply hs; simp [h]
      have hinside : s ∈ Set.Ioo t₀ T :=
        ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hst₀), lt_of_le_of_ne hIcc.2 hsT⟩
      have hnear : (fun r => residual1
          (consensusV0 (consensusOptimalFlow.flow t₀ x r) r) 1) =ᶠ[𝓝 s]
          consensusOptimalResidualPath x t₀ := by
        have hnhds := Ioo_mem_nhds hinside.1 hinside.2
        filter_upwards [hnhds] with r hr
        calc
          residual1 (consensusV0 (consensusOptimalFlow.flow t₀ x r) r) 1 =
              consensusOptimalPotentialAlong x t₀ r :=
            hresidual_eq (show r ∈ Set.Ici t₀ from le_of_lt hr.1)
          _ = consensusOptimalResidualPath x t₀ r := by
            apply consensusOptimalPotentialAlong_eq x hx t₀ T hT
            rw [Set.uIcc_of_le hT]
            exact ⟨hr.1.le, hr.2.le⟩
      have hderiv := (consensusOptimalResidualPath_hasDerivAt x t₀ s).congr_of_eventuallyEq hnear
      have hval := hresidual_eq (show s ∈ Set.Ici t₀ from hIcc.1)
      have hval' := consensusOptimalPotentialAlong_eq x hx t₀ T hT (by
        rw [Set.uIcc_of_le hT]
        exact ⟨hinside.1.le, hinside.2.le⟩)
      rw [hderiv.deriv, ← hval', ← hval]
    · subst T
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1
        (by simp : volume (Set.Icc t₀ t₀) = 0)] with s hs hmem
      exact False.elim (hs hmem)
  have herror : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (Metric.infDist (consensusOptimalFlow.flow t₀ x s)
        {y : AgentState | y ∈ closedLoopReachableSet
          (policyFlowReachableAt consensusOptimalFlow box t₀) ∧ consensusV0 y s ≤ 1}) ^ 2 ≤
      1 * residual1 (consensusV0 (consensusOptimalFlow.flow t₀ x s) s) 1 := by
    intro T hT s hs
    change (Metric.infDist (consensusOptimalFlow.flow t₀ x s)
        (consensusOptimalTheorem1Target t₀ s)) ^ 2 ≤ _
    rw [consensusOptimalTheorem1Target_eq_shared t₀ s ht₀]
    have hxs := consensusOptimalFlow_forward_invariant x hx t₀ s hs.1
    rw [consensusV0_residual_eq_potential _ hxs s]
    simpa [one_mul] using consensus_global_error_bound _ hxs s
  have hresult := theorem1_policy_flow_reachable_tcz_distance_tendsto_zero
    (F := consensusOptimalFlow) (initialSet := box) (x₀ := x) (hx₀ := hx)
    (V₀ := consensusV0) (θ := 1) (c := 3) (C := 1) (t₀ := t₀)
    htarget hresidual_ac hdecay herror
    (by
      intro y hy t ht
      have hybox : y ∈ box := (consensusOptimalFlow_reachable_closure_eq_box t₀ ht₀) ▸ hy
      have hflow := consensusOptimalFlow_forward_invariant y hybox t₀ t ht
      exact (consensusOptimalFlow_reachable_closure_eq_box t₀ ht₀).symm ▸ hflow)
    ht₀ (by norm_num) (by norm_num)
  rcases hresult with ⟨hreach, hbound, htend⟩
  refine ⟨hreach, ?_, ?_⟩
  · intro t ht
    have h := hbound t ht
    have hinit : residual1 (consensusV0 (consensusOptimalFlow.flow t₀ x t₀) t₀) 1 =
        DA.potential x t₀ := by
      rw [consensusOptimalFlow.initial]
      exact consensusV0_residual_eq_potential x hx t₀
    simpa [consensusOptimalTheorem1Target, hinit, one_mul] using h
  · exact htend

/-- 二主体共有ポテンシャルから作る非定数の臨場感。 -/
def consensusPresenceP (x : AgentState) (_t : ℝ) : ℝ :=
  Real.exp (-(DA.potential x 0))

def consensusPresenceQ (_x : AgentState) (_t : ℝ) : ℝ := 1

def consensusPresenceV0 (x : AgentState) (_t : ℝ) : ℝ :=
  1 + DA.potential x 0 + consensusPresenceP x 0

theorem consensusPresence_potential_nonneg (x : AgentState) (t : ℝ) :
    0 ≤ DA.potential x t := by
  rw [potential_eq ![0, 0]]
  simp only [Tomabechi.Examples.Theorem2.γ]
  positivity

theorem consensusPresenceP_bounds (x : AgentState) (t : ℝ) :
    0 < consensusPresenceP x t ∧ consensusPresenceP x t ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (consensusPresence_potential_nonneg x 0)

theorem consensusPresenceP_nonconstant :
    consensusPresenceP (![0, 0]) 0 ≠ consensusPresenceP (![1, 0]) 0 := by
  have hzero : DA.potential (![0, 0]) 0 = 0 := by
    rw [potential_eq ![0, 0]]
    norm_num [Tomabechi.Examples.Theorem2.θ, Tomabechi.Examples.Theorem2.γ]
  have hone : 0 < DA.potential (![1, 0]) 0 := by
    rw [potential_eq ![0, 0]]
    norm_num [Tomabechi.Examples.Theorem2.θ, Tomabechi.Examples.Theorem2.γ]
  rw [consensusPresenceP, consensusPresenceP, hzero]
  have hexp : Real.exp (-(DA.potential (![1, 0]) 0)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos hone)
  simpa using hexp.ne.symm

theorem consensusPresence_effective_eq_shared (x : AgentState) (t : ℝ) :
    Tomabechi.Theorem4.effectivePotential (consensusPresenceV0 x t)
      (consensusPresenceP x t) (consensusPresenceQ x t) 1 =
      1 + DA.potential x 0 := by
  simp [Tomabechi.Theorem4.effectivePotential, consensusPresenceV0,
    consensusPresenceP, consensusPresenceQ]

theorem consensusPresence_residual_eq_potential
    (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    Tomabechi.Theorem4.residual4 (consensusPresenceV0 x t)
      (consensusPresenceP x t) (consensusPresenceQ x t) 1 1 = DA.potential x t := by
  rw [Tomabechi.Theorem4.residual4, consensusPresence_effective_eq_shared]
  have htime : DA.potential x 0 = DA.potential x t := by
    rw [potential_eq ![0, 0] x 0, potential_eq ![0, 0] x t]
  rw [htime]
  exact consensusV0_residual_eq_potential x hx t

theorem consensusPresence_weightedTCZ_eq_shared (t : ℝ) :
    Tomabechi.Theorem4.weightedTCZ box consensusPresenceV0 consensusPresenceP
      consensusPresenceQ 1 1 t = DA.sharedTCZ box t := by
  ext y
  change (y ∈ box ∧ Tomabechi.Theorem4.effectivePotential
    (consensusPresenceV0 y t) (consensusPresenceP y t)
    (consensusPresenceQ y t) 1 ≤ 1) ↔ y ∈ DA.sharedTCZ box t
  rw [consensusPresence_effective_eq_shared]
  change (y ∈ box ∧ 1 + DA.potential y 0 ≤ 1) ↔
    (y ∈ box ∧ DA.potential y t = 0)
  have htime : DA.potential y 0 = DA.potential y t := by
    rw [potential_eq ![0, 0], potential_eq ![0, 0]]
  have hnonneg := consensusPresence_potential_nonneg y t
  constructor
  · rintro ⟨hy, hp⟩
    refine ⟨hy, ?_⟩
    rw [← htime]
    linarith
  · rintro ⟨hy, hp⟩
    refine ⟨hy, ?_⟩
    rw [htime, hp]
    norm_num

/-! ## 二主体flowに結び付けた定理20の有限象徴データ

情報束は二主体の冪集合束で、利用可能情報は `{∅, {0}}` という真部分束（全体 `{0,1}` を含まない）にする。
象徴の指示集合は `{0}`、そのLUBも `{0}` であり、状態空間側ではこのアドレスを合意集合へ
対応させる。以下はC1の同一二主体状態・flowに結び付いたO13用の具体データである。
-/

abbrev C1SymbolConcept := Finset (Fin 2)

def c1SymbolInfoLattice : Set C1SymbolConcept :=
  {a | a = (∅ : Finset (Fin 2)) ∨ a = ({0} : Finset (Fin 2))}

def c1AvailableInformation (_i : Fin 2) (_t : ℝ) : Set C1SymbolConcept :=
  c1SymbolInfoLattice

def c1SymbolW : Set C1SymbolConcept := {({0} : Finset (Fin 2))}

def c1SymbolAddress : C1SymbolConcept := {0}

theorem c1SymbolInfo_bot : (∅ : C1SymbolConcept) ∈ c1SymbolInfoLattice := by
  simp [c1SymbolInfoLattice]

theorem c1SymbolInfo_join_closed {a b : C1SymbolConcept}
    (ha : a ∈ c1SymbolInfoLattice) (hb : b ∈ c1SymbolInfoLattice) :
    a ∪ b ∈ c1SymbolInfoLattice := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [c1SymbolInfoLattice]

theorem c1SymbolInfo_meet_closed {a b : C1SymbolConcept}
    (ha : a ∈ c1SymbolInfoLattice) (hb : b ∈ c1SymbolInfoLattice) :
    a ∩ b ∈ c1SymbolInfoLattice := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [c1SymbolInfoLattice]

theorem c1SymbolInfo_proper :
    (Finset.univ : C1SymbolConcept) ∉ c1SymbolInfoLattice := by
  intro h
  rcases h with h | h
  · have h1 : (1 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ _
    rw [h] at h1
    simp at h1
  · have h1 : (1 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ _
    rw [h] at h1
    simp at h1

theorem c1AvailableInformation_proper (i : Fin 2) (t : ℝ) :
    c1AvailableInformation i t ⊆ Set.univ ∧ c1AvailableInformation i t ≠ Set.univ := by
  constructor
  · intro a ha
    exact Set.mem_univ a
  · intro hEq
    have htop : (Finset.univ : C1SymbolConcept) ∈ c1AvailableInformation i t := by
      rw [hEq]
      exact Set.mem_univ _
    exact c1SymbolInfo_proper htop

theorem c1SymbolW_subset_info : c1SymbolW ⊆ c1SymbolInfoLattice := by
  intro a ha
  simp only [c1SymbolW, Set.mem_singleton_iff] at ha
  subst a
  right
  rfl

theorem c1SymbolAddress_isLUB :
    (∀ w ∈ c1SymbolW, w ⊆ c1SymbolAddress) ∧
      ∀ b, (∀ w ∈ c1SymbolW, w ⊆ b) → c1SymbolAddress ⊆ b := by
  constructor
  · intro w hw
    have heq : w = ({0} : Finset (Fin 2)) := by simpa [c1SymbolW] using hw
    rw [heq]
    simp [c1SymbolAddress]
  · intro b hb
    have h := hb ({0} : Finset (Fin 2)) (by simp [c1SymbolW])
    simpa [c1SymbolAddress] using h

def c1SymbolTarget (u : C1SymbolConcept) : Set AgentState :=
  if u = c1SymbolAddress then {x | x 0 = x 1} else ∅

def c1SymbolDistance (x : AgentState) : ℝ :=
  1 / 4 * (x 0 - x 1) ^ 2

theorem c1SymbolTarget_nonempty : (c1SymbolTarget c1SymbolAddress).Nonempty := by
  refine ⟨![0, 0], ?_⟩
  simp [c1SymbolTarget]

theorem c1SymbolTarget_closed : IsClosed (c1SymbolTarget c1SymbolAddress) := by
  change IsClosed {x : AgentState | x 0 = x 1}
  exact isClosed_eq (continuous_apply 0) (continuous_apply 1)

theorem c1SymbolDistance_nonneg (x : AgentState) : 0 ≤ c1SymbolDistance x := by
  unfold c1SymbolDistance
  nlinarith [sq_nonneg (x 0 - x 1)]

theorem c1SymbolDistance_zero_iff (x : AgentState) :
    c1SymbolDistance x = 0 ↔ x ∈ c1SymbolTarget c1SymbolAddress := by
  rw [c1SymbolDistance, c1SymbolTarget]
  simp only [↓reduceIte, Set.mem_setOf_eq]
  constructor
  · intro h
    have hzsq : (x 0 - x 1) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left (by norm_num)
    have hz : x 0 - x 1 = 0 := (sq_eq_zero_iff).mp hzsq
    linarith
  · intro h
    have : x 0 - x 1 = 0 := sub_eq_zero.mpr h
    simp [this]

theorem c1SymbolDistance_eq_sharedPotential_on_box
    (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    c1SymbolDistance x = (1 / 8 : ℝ) * DA.potential x t := by
  rw [sharedPotential_eq_coupling x hx t]
  unfold c1SymbolDistance
  norm_num [Tomabechi.Examples.Theorem2.γ]
  ring

theorem c1SymbolTarget_box_eq_sharedTCZ (t : ℝ) :
    {x : AgentState | x ∈ box ∧ x ∈ c1SymbolTarget c1SymbolAddress} =
      DA.sharedTCZ box t := by
  ext x
  change (x ∈ box ∧ x 0 = x 1) ↔ x ∈ DA.sharedTCZ box t
  constructor
  · rintro ⟨hx, hEq⟩
    refine ⟨hx, ?_⟩
    rw [sharedPotential_eq_coupling x hx t, sub_eq_zero.mpr hEq]
    ring
  · rintro ⟨hx, hpotential⟩
    have hform := sharedPotential_eq_coupling x hx t
    rw [hform] at hpotential
    have hγ : 0 < γ := by norm_num [γ]
    have hsquare : (x 0 - x 1) ^ 2 = 0 :=
      (mul_eq_zero.mp hpotential).resolve_left hγ.ne'
    have hgap : x 0 - x 1 = 0 := (sq_eq_zero_iff).mp hsquare
    exact ⟨hx, sub_eq_zero.mp hgap⟩

theorem c1SymbolDistance_optimalFlow_decay
    (x : AgentState) (t₀ t : ℝ) :
    c1SymbolDistance (consensusOptimalFlow.flow t₀ x t) =
      c1SymbolDistance x * Real.exp (-6 * (t - t₀)) := by
  unfold c1SymbolDistance
  rw [consensusOptimalFlow_gap, mul_pow, ← Real.exp_nat_mul]
  ring

def c1SymbolBasePresence (_x : AgentState) (_t : ℝ) : ℝ := 0

def c1SymbolAmplification (u : C1SymbolConcept) (_x : AgentState) (_t : ℝ) : ℝ :=
  if u = c1SymbolAddress then 1 else 0

def c1SymbolLambda : ℝ := 1

def c1SymbolPresence (u : C1SymbolConcept) (x : AgentState) (t : ℝ) : ℝ :=
  c1SymbolBasePresence x t + c1SymbolLambda * c1SymbolAmplification u x t

def c1SymbolQ (_u : C1SymbolConcept) (_x : AgentState) (_t : ℝ) : ℝ := 1

def c1SymbolV0 (x : AgentState) (_t : ℝ) : ℝ := 2 * c1SymbolDistance x

def c1SymbolSlope (d : ℝ) : ℝ := -d

def c1SymbolEffectivePotential (x : AgentState) : ℝ :=
  c1SymbolV0 x 0 - 1 * 1 *
    (c1SymbolPresence c1SymbolAddress x 0 * c1SymbolSlope (c1SymbolDistance x))

theorem c1SymbolDistance_contDiff : ContDiff ℝ 1 c1SymbolDistance := by
  unfold c1SymbolDistance
  fun_prop

theorem c1SymbolV0_contDiff (t : ℝ) :
    ContDiff ℝ 1 (fun x => c1SymbolV0 x t) := by
  change ContDiff ℝ 1 (fun x => 2 * c1SymbolDistance x)
  simpa [smul_eq_mul, mul_comm] using c1SymbolDistance_contDiff.smul_const (2 : ℝ)

theorem c1SymbolSelectedPresence_contDiff (t : ℝ) :
    ContDiff ℝ 1 (fun x => c1SymbolPresence c1SymbolAddress x t) := by
  have h : (fun x => c1SymbolPresence c1SymbolAddress x t) = fun _ => 1 := by
    funext x
    simp [c1SymbolPresence, c1SymbolBasePresence, c1SymbolLambda,
      c1SymbolAmplification]
  rw [h]
  fun_prop

theorem c1SymbolSlope_contDiff : ContDiff ℝ 1 c1SymbolSlope := by
  unfold c1SymbolSlope
  fun_prop

theorem c1SymbolPresence_selected (x : AgentState) (t : ℝ) :
    c1SymbolPresence c1SymbolAddress x t = 1 := by
  simp [c1SymbolPresence, c1SymbolBasePresence, c1SymbolLambda,
    c1SymbolAmplification]

theorem c1SymbolAmplification_selected (x : AgentState) (t : ℝ) :
    c1SymbolAmplification c1SymbolAddress x t = 1 := by
  simp [c1SymbolAmplification]

theorem c1SymbolLambda_positive : 0 < c1SymbolLambda := by
  norm_num [c1SymbolLambda]

theorem c1SymbolBasePresence_unitInterval (x : AgentState) (t : ℝ) :
    c1SymbolBasePresence x t ∈ Set.Icc 0 1 := by
  simp [c1SymbolBasePresence]

theorem c1SymbolSlope_derivative (d : ℝ) :
    HasDerivAt c1SymbolSlope (-1) d := by
  change HasDerivAt (fun x : ℝ => -x) (-1) d
  exact hasDerivAt_neg d

theorem c1SymbolEffectivePotential_selected (x : AgentState) (t : ℝ) :
    c1SymbolEffectivePotential x = 3 * c1SymbolDistance x := by
  simp [c1SymbolEffectivePotential, c1SymbolV0,
    c1SymbolPresence_selected, c1SymbolSlope]
  ring

theorem c1SymbolQ_positive (u : C1SymbolConcept) (x : AgentState) (t : ℝ) :
    0 < c1SymbolQ u x t := by
  norm_num [c1SymbolQ]

theorem c1SymbolEffectivePotential_optimalFlow_decay
    (x : AgentState) (t₀ t : ℝ) :
    c1SymbolEffectivePotential (consensusOptimalFlow.flow t₀ x t) =
      c1SymbolEffectivePotential x * Real.exp (-6 * (t - t₀)) := by
  rw [c1SymbolEffectivePotential_selected (consensusOptimalFlow.flow t₀ x t) 0,
    c1SymbolEffectivePotential_selected x 0]
  rw [c1SymbolDistance_optimalFlow_decay]
  ring

theorem c1SymbolPresence_selected_bounds (x : AgentState) (t : ℝ) :
    0 ≤ c1SymbolPresence c1SymbolAddress x t ∧
      c1SymbolPresence c1SymbolAddress x t ≤ 1 := by
  rw [c1SymbolPresence_selected]
  norm_num

theorem c1SymbolQ_range (u : C1SymbolConcept) (x : AgentState) (t : ℝ) :
    c1SymbolQ u x t ∈ Set.Icc (-1) 1 := by
  simp [c1SymbolQ]

/-! ## Euclidean coordinate realization for Theorem 20

`AgentState` is a function type with the sup norm and has no inner-product-space instance.
Transport the same coordinate dynamics through the canonical continuous linear equivalence to
`EuclideanSpace ℝ (Fin 2)`, where Theorem 20's gradient-flow interface applies. -/

abbrev C1EuclideanAgentState := EuclideanSpace ℝ (Fin 2)

def c1EuclideanCoordinates : C1EuclideanAgentState ≃L[ℝ] AgentState :=
  EuclideanSpace.equiv (Fin 2) ℝ

@[simp] theorem c1EuclideanCoordinates_toLp (x : AgentState) :
    c1EuclideanCoordinates (WithLp.toLp 2 x) = x := by
  change (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ))
    (WithLp.toLp 2 x) = x
  exact WithLp.ofLp_toLp 2 x

/-- The Euclidean direction normal to the two-agent consensus diagonal. -/
def c1EuclideanDisagreementDirection : C1EuclideanAgentState :=
  EuclideanSpace.single 0 1 - EuclideanSpace.single 1 1

/-- The symbolic distance transported to Euclidean coordinates. -/
def c1EuclideanSymbolDistance (x : C1EuclideanAgentState) : ℝ :=
  1 / 4 * inner ℝ c1EuclideanDisagreementDirection x ^ 2

/-- The gradient of the transported quadratic distance. -/
def c1EuclideanSymbolDistanceGradient (x : C1EuclideanAgentState) :
    C1EuclideanAgentState :=
  (1 / 2 * inner ℝ c1EuclideanDisagreementDirection x) •
    c1EuclideanDisagreementDirection

theorem c1EuclideanDisagreement_inner (x : C1EuclideanAgentState) :
    inner ℝ c1EuclideanDisagreementDirection x = x 0 - x 1 := by
  simp [c1EuclideanDisagreementDirection, EuclideanSpace.single, PiLp.inner_apply]
  ring

theorem c1EuclideanDisagreementDirection_norm_sq :
    ‖c1EuclideanDisagreementDirection‖ ^ 2 = 2 := by
  rw [c1EuclideanDisagreementDirection, norm_sub_sq_real]
  simp [EuclideanSpace.single, PiLp.inner_apply]
  norm_num

theorem c1EuclideanSymbolGradient_inner_self (x : C1EuclideanAgentState) :
    inner ℝ (c1EuclideanSymbolDistanceGradient x)
      (c1EuclideanSymbolDistanceGradient x) =
        2 * c1EuclideanSymbolDistance x := by
  simp only [c1EuclideanSymbolDistanceGradient, inner_smul_left, inner_smul_right]
  rw [real_inner_self_eq_norm_sq, c1EuclideanDisagreementDirection_norm_sq,
    c1EuclideanDisagreement_inner]
  simp only [c1EuclideanSymbolDistance]
  simp [c1EuclideanDisagreement_inner, star_trivial]
  ring

theorem c1EuclideanSymbolDistance_hasGradientAt (x : C1EuclideanAgentState) :
    HasGradientAt c1EuclideanSymbolDistance
      (c1EuclideanSymbolDistanceGradient x) x := by
  have h := ((hasStrictFDerivAt_norm_sq
      (inner ℝ c1EuclideanDisagreementDirection x)).hasFDerivAt.comp x
      (innerSL ℝ c1EuclideanDisagreementDirection).hasFDerivAt).const_mul (1 / 4)
  have h' : HasFDerivAt c1EuclideanSymbolDistance
      (InnerProductSpace.toDual ℝ C1EuclideanAgentState
        (c1EuclideanSymbolDistanceGradient x)) x := by
    convert h.congr_fderiv
      (g' := InnerProductSpace.toDual ℝ C1EuclideanAgentState
        (c1EuclideanSymbolDistanceGradient x)) ?_ using 1
    · ext y
      simp [c1EuclideanSymbolDistance, Real.norm_eq_abs, sq_abs]
    · ext v
      simp [c1EuclideanSymbolDistanceGradient,
        InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
      ring
  rwa [hasGradientAt_iff_hasFDerivAt]

theorem c1EuclideanSymbolDistance_eq_coordinates (x : C1EuclideanAgentState) :
    c1EuclideanSymbolDistance x =
      c1SymbolDistance (c1EuclideanCoordinates x) := by
  simp [c1EuclideanSymbolDistance, c1EuclideanDisagreementDirection,
    c1EuclideanCoordinates, c1SymbolDistance, EuclideanSpace.single,
    PiLp.inner_apply]
  ring

theorem c1EuclideanEffectivePotential_hasGradientAt
    (x : C1EuclideanAgentState) :
    HasGradientAt
      (fun y => 0 -
        3 * (1 * ((fun d : ℝ => -d) (c1EuclideanSymbolDistance y))))
      (3 • c1EuclideanSymbolDistanceGradient x) x := by
  have hD := c1EuclideanSymbolDistance_hasGradientAt x
  have hV : HasGradientAt (fun _ : C1EuclideanAgentState => (0 : ℝ)) 0 x :=
    hasGradientAt_const x 0
  have hP : HasGradientAt (fun _ : C1EuclideanAgentState => (1 : ℝ)) 0 x :=
    hasGradientAt_const x 1
  have hs : HasDerivAt (fun d : ℝ => -d) (-1) (c1EuclideanSymbolDistance x) :=
    hasDerivAt_neg (c1EuclideanSymbolDistance x)
  have h := Tomabechi.Theorem20.effective_potential_hasGradientAt
    (fun _ : C1EuclideanAgentState => (0 : ℝ))
    (fun _ : C1EuclideanAgentState => (1 : ℝ))
    c1EuclideanSymbolDistance (fun d : ℝ => -d) x
    0 0 (c1EuclideanSymbolDistanceGradient x) (-1) 3 hV hP hD hs
  convert h using 1 <;> simp <;> module

def differentiableConsensusOptimalFlow : DifferentiableClosedLoopPolicyFlow AgentState ℝ where
  toClosedLoopPolicyFlow := consensusOptimalFlow
  solves := by
    intro t₀ x t ht
    apply hasDerivAt_pi.2
    intro i
    have hlin : HasDerivAt (fun s : ℝ => -3 * (s - t₀)) (-3) t := by
      simpa using (hasDerivAt_id t).sub_const t₀ |>.const_mul (-3)
    have hexp := (Real.hasDerivAt_exp (-3 * (t - t₀))).comp t hlin
    fin_cases i
    · have hcoord := (hexp.const_mul (halfDifference x)).add_const (meanState x)
      convert hcoord using 1
      · funext s
        simp [consensusOptimalFlow, meanState, halfDifference]
        ring
      · simp [consensusOptimalFlow, meanState, halfDifference]
        ring
    · have hcoord := (hexp.const_mul (-halfDifference x)).add_const (meanState x)
      convert hcoord using 1
      · funext s
        simp [consensusOptimalFlow, meanState, halfDifference]
        ring
      · simp [consensusOptimalFlow, meanState, halfDifference]
        ring

def euclideanConsensusOptimalFlow : ClosedLoopPolicyFlow C1EuclideanAgentState ℝ where
  admissible := consensusOptimalFlow.admissible
  feedback := fun x t => consensusOptimalFlow.feedback (c1EuclideanCoordinates x) t
  vectorField := fun x u t => c1EuclideanCoordinates.symm
    (consensusOptimalFlow.vectorField (c1EuclideanCoordinates x) u t)
  flow := fun t₀ x t => c1EuclideanCoordinates.symm
    (consensusOptimalFlow.flow t₀ (c1EuclideanCoordinates x) t)
  feedback_admissible := by
    intro x t
    exact consensusOptimalFlow.feedback_admissible (c1EuclideanCoordinates x) t
  initial := by
    intro t₀ x
    apply c1EuclideanCoordinates.injective
    simp [c1EuclideanCoordinates, consensusOptimalFlow.initial]
  restart := by
    intro t₀ x s t h₀s hst
    apply c1EuclideanCoordinates.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact consensusOptimalFlow.restart t₀ (c1EuclideanCoordinates x) s t h₀s hst

theorem euclideanConsensusOptimalFlow_coordinates
    (x : C1EuclideanAgentState) (t₀ t : ℝ) :
    c1EuclideanCoordinates (euclideanConsensusOptimalFlow.flow t₀ x t) =
      consensusOptimalFlow.flow t₀ (c1EuclideanCoordinates x) t := by
  simp [euclideanConsensusOptimalFlow, c1EuclideanCoordinates_toLp]

def differentiableEuclideanConsensusOptimalFlow :
    DifferentiableClosedLoopPolicyFlow C1EuclideanAgentState ℝ where
  toClosedLoopPolicyFlow := euclideanConsensusOptimalFlow
  solves := by
    intro t₀ x t ht
    have h := (hasDerivAt_const t
      c1EuclideanCoordinates.symm.toContinuousLinearMap).clm_apply
      (differentiableConsensusOptimalFlow.solves t₀ (c1EuclideanCoordinates x) t ht)
    simpa [euclideanConsensusOptimalFlow, differentiableConsensusOptimalFlow,
      c1EuclideanCoordinates_toLp, ContinuousLinearEquiv.apply_symm_apply] using h

def c1EuclideanBox : Set C1EuclideanAgentState :=
  {x | c1EuclideanCoordinates x ∈ box}

def c1EuclideanSymbolTarget : Set C1EuclideanAgentState :=
  {x | x 0 = x 1}

theorem c1EuclideanSymbolTarget_nonempty : c1EuclideanSymbolTarget.Nonempty := by
  refine ⟨0, ?_⟩
  simp [c1EuclideanSymbolTarget]

theorem c1EuclideanSymbolTarget_closed : IsClosed c1EuclideanSymbolTarget := by
  change IsClosed {x : C1EuclideanAgentState | x 0 = x 1}
  exact isClosed_eq (PiLp.continuous_apply (p := 2)
    (β := fun _ : Fin 2 => ℝ) 0) (PiLp.continuous_apply (p := 2)
    (β := fun _ : Fin 2 => ℝ) 1)

theorem c1EuclideanSymbolDistance_nonneg (x : C1EuclideanAgentState) :
    0 ≤ c1EuclideanSymbolDistance x := by
  unfold c1EuclideanSymbolDistance
  positivity

theorem c1EuclideanSymbolDistance_zero_iff (x : C1EuclideanAgentState) :
    c1EuclideanSymbolDistance x = 0 ↔ x ∈ c1EuclideanSymbolTarget := by
  rw [c1EuclideanSymbolDistance, c1EuclideanDisagreement_inner,
    c1EuclideanSymbolTarget]
  constructor
  · intro h
    have hz : (x 0 - x 1) ^ 2 = 0 := by nlinarith
    exact sub_eq_zero.mp ((sq_eq_zero_iff).mp hz)
  · intro h
    rw [sub_eq_zero.mpr h]
    norm_num

theorem c1EuclideanSymbolDistance_error_bound (x : C1EuclideanAgentState) :
    Metric.infDist x c1EuclideanSymbolTarget ≤
      2 * Real.sqrt (c1EuclideanSymbolDistance x) := by
  let m : ℝ := (x 0 + x 1) / 2
  let y : C1EuclideanAgentState := WithLp.toLp 2 (fun _ : Fin 2 => m)
  have hy : y ∈ c1EuclideanSymbolTarget := by
    simp [y, m, c1EuclideanSymbolTarget]
  have hdist : dist x y =
      Real.sqrt ((x 0 - m) ^ 2 + (x 1 - m) ^ 2) := by
    rw [PiLp.dist_eq_of_L2]
    simp [y, m, Real.dist_eq, sq_abs]
  have hdist_le : dist x y ≤ |x 0 - x 1| := by
    rw [hdist, Real.sqrt_le_iff]
    constructor
    · exact abs_nonneg _
    · dsimp [m]
      rw [show (x 0 - (x 0 + x 1) / 2) ^ 2 +
          (x 1 - (x 0 + x 1) / 2) ^ 2 =
            (x 0 - x 1) ^ 2 / 2 by ring, sq_abs]
      nlinarith [sq_nonneg (x 0 - x 1)]
  have hroot : 2 * Real.sqrt (c1EuclideanSymbolDistance x) =
      |x 0 - x 1| := by
    rw [c1EuclideanSymbolDistance, c1EuclideanDisagreement_inner]
    rw [show (1 / 4 : ℝ) * (x 0 - x 1) ^ 2 = ((x 0 - x 1) / 2) ^ 2 by ring,
      Real.sqrt_sq_eq_abs]
    rw [abs_div]
    norm_num
    ring
  calc
    Metric.infDist x c1EuclideanSymbolTarget ≤ dist x y :=
      Metric.infDist_le_dist_of_mem hy
    _ ≤ |x 0 - x 1| := hdist_le
    _ = 2 * Real.sqrt (c1EuclideanSymbolDistance x) := hroot.symm

theorem box_isCompact : IsCompact box := by
  have hrepr : box = {x : AgentState | ∀ i, x i ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4)} := by
    ext x
    simp [box, abs_le]
  rw [hrepr]
  exact isCompact_pi_infinite (fun _ => isCompact_Icc)

theorem c1EuclideanBox_eq_image :
    c1EuclideanBox = c1EuclideanCoordinates.symm '' box := by
  ext x
  constructor
  · intro hx
    exact ⟨c1EuclideanCoordinates x, hx, c1EuclideanCoordinates.symm_apply_apply x⟩
  · rintro ⟨y, hy, hxy⟩
    have hcoord : c1EuclideanCoordinates x = y := by
      rw [← hxy]
      exact c1EuclideanCoordinates.apply_symm_apply y
    simpa [c1EuclideanBox, hcoord] using hy

theorem c1EuclideanBox_isCompact : IsCompact c1EuclideanBox := by
  rw [c1EuclideanBox_eq_image]
  exact box_isCompact.image c1EuclideanCoordinates.symm.continuous

theorem euclideanConsensusOptimalFlow_forward_invariant
    (x : C1EuclideanAgentState) (hx : x ∈ c1EuclideanBox)
    (t₀ t : ℝ) (ht : t₀ ≤ t) :
    euclideanConsensusOptimalFlow.flow t₀ x t ∈ c1EuclideanBox := by
  change c1EuclideanCoordinates
      (euclideanConsensusOptimalFlow.flow t₀ x t) ∈ box
  simpa [euclideanConsensusOptimalFlow, c1EuclideanCoordinates_toLp] using
    consensusOptimalFlow_forward_invariant (c1EuclideanCoordinates x) hx t₀ t ht

theorem euclideanConsensusOptimalFlow_reachable_closure_eq_box
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    closedLoopReachableSet
      (policyFlowReachableAt euclideanConsensusOptimalFlow c1EuclideanBox t₀) =
        c1EuclideanBox := by
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ c1EuclideanBox_isCompact.isClosed
    rintro y ⟨τ, hτ, hy⟩
    rcases hy with ⟨hstart, x, hx, rfl⟩
    exact euclideanConsensusOptimalFlow_forward_invariant x hx t₀ τ hstart
  · intro y hy
    apply subset_closure
    refine ⟨t₀, ht₀, ?_⟩
    exact ⟨le_rfl, y, hy, (euclideanConsensusOptimalFlow.initial t₀ y).symm⟩

/-- Apply the original-condition Theorem 20 entry to the same rate-3 consensus
flow used for finite-horizon optimality and Theorems 1, 2, and 4. -/
theorem consensusOptimalEuclideanFlow_theorem20
    (x₀ : C1EuclideanAgentState) (hx₀ : x₀ ∈ c1EuclideanBox)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t →
      c1EuclideanSymbolDistance (euclideanConsensusOptimalFlow.flow t₀ x₀ t) ≤
        c1EuclideanSymbolDistance (euclideanConsensusOptimalFlow.flow t₀ x₀ t₀) *
          Real.exp (-(t - t₀)) ∧
      Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x₀ t)
          c1EuclideanSymbolTarget ≤
        2 * Real.sqrt (c1EuclideanSymbolDistance
          (euclideanConsensusOptimalFlow.flow t₀ x₀ t₀)) *
          Real.exp (-((1 / 2 : ℝ) * (t - t₀)))) ∧
      Filter.Tendsto (fun t => Metric.infDist
        (euclideanConsensusOptimalFlow.flow t₀ x₀ t) c1EuclideanSymbolTarget)
        atTop (𝓝 0) := by
  let F := differentiableEuclideanConsensusOptimalFlow
  let M : ℝ → C1EuclideanAgentState →L[ℝ] C1EuclideanAgentState :=
    fun _ => ContinuousLinearMap.id ℝ C1EuclideanAgentState
  let D := c1EuclideanSymbolDistance
  let V₀ : C1EuclideanAgentState → ℝ := fun x => 2 * D x
  let P : C1EuclideanAgentState → ℝ := fun _ => 1
  let s : ℝ → ℝ := fun d => -d
  let gradD : ℝ → C1EuclideanAgentState := fun r =>
    c1EuclideanSymbolDistanceGradient (F.flow t₀ x₀ r)
  let gradV : ℝ → C1EuclideanAgentState := fun r =>
    (2 : ℝ) • c1EuclideanSymbolDistanceGradient (F.flow t₀ x₀ r)
  let gradZero : ℝ → C1EuclideanAgentState := fun _ => 0
  let g2 : ℝ → ℝ := fun r => 2 * D (F.flow t₀ x₀ r)
  have hK : closedLoopReachableSet
      (policyFlowReachableAt F.toClosedLoopPolicyFlow c1EuclideanBox t₀) =
        c1EuclideanBox :=
    euclideanConsensusOptimalFlow_reachable_closure_eq_box t₀ ht₀
  have hField : ∀ y r,
      F.vectorField y (F.feedback y r) r =
        -((M r) (∇ (fun z => V₀ z - 1 * 1 * (P z * s (D z))) y)) := by
    intro y r
    have hgrad := c1EuclideanEffectivePotential_hasGradientAt y
    have hfun : (fun z => V₀ z - 1 * 1 * (P z * s (D z))) =
        (fun z => 0 - 3 * (1 * ((fun d : ℝ => -d) (c1EuclideanSymbolDistance z)))) := by
      funext z
      simp [V₀, P, D, s] <;> ring
    have hgrad' : ∇ (fun z => V₀ z - 1 * 1 * (P z * s (D z))) y =
        3 • c1EuclideanSymbolDistanceGradient y := by
      rw [hfun]
      exact hgrad.gradient
    have hfield0 : euclideanConsensusOptimalFlow.vectorField y
        (euclideanConsensusOptimalFlow.feedback y r) r =
          -3 • c1EuclideanSymbolDistanceGradient y := by
      apply c1EuclideanCoordinates.injective
      simp [euclideanConsensusOptimalFlow, consensusOptimalFlow,
        c1EuclideanSymbolDistanceGradient, c1EuclideanDisagreementDirection,
        c1EuclideanCoordinates, EuclideanSpace.equiv, EuclideanSpace.single,
        PiLp.coe_continuousLinearEquiv, PiLp.ofLp_single, PiLp.inner_apply]
      ext i
      fin_cases i <;> simp [Pi.single] <;> ring
    change euclideanConsensusOptimalFlow.vectorField y
      (euclideanConsensusOptimalFlow.feedback y r) r = _
    rw [hfield0, hgrad']
    simp [M, ContinuousLinearMap.id_apply]
    rfl
  have hKforward : ∀ y ∈ closedLoopReachableSet
      (policyFlowReachableAt F.toClosedLoopPolicyFlow c1EuclideanBox t₀),
      ∀ r, t₀ ≤ r → F.flow t₀ y r ∈ closedLoopReachableSet
        (policyFlowReachableAt F.toClosedLoopPolicyFlow c1EuclideanBox t₀) := by
    intro y hy r hr
    rw [hK] at hy ⊢
    exact euclideanConsensusOptimalFlow_forward_invariant y hy t₀ r hr
  have hresult := Tomabechi.Theorem20.theorem20_policy_flow_original_condition_conclusion
    F M M V₀ P D s 1 1 (1 / 2) (1 / 2) 1 2 1 t₀ ht₀ c1EuclideanBox x₀ hx₀
    c1EuclideanSymbolTarget g2 (fun _ => -1) gradV gradZero gradD hField
    (by rw [hK]; exact c1EuclideanBox_isCompact)
    hKforward
    (by
      intro r hr
      apply (hasGradientAt_iff_hasFDerivAt).2
      have hD := (c1EuclideanSymbolDistance_hasGradientAt
        (F.flow t₀ x₀ r)).hasFDerivAt
      convert hD.const_smul (2 : ℝ) using 1
      change (InnerProductSpace.toDual ℝ C1EuclideanAgentState)
        ((2 : ℝ) • c1EuclideanSymbolDistanceGradient (F.flow t₀ x₀ r)) = _
      exact map_smul (InnerProductSpace.toDual ℝ C1EuclideanAgentState) 2 _)
    (by intro r hr; exact hasGradientAt_const (F.flow t₀ x₀ r) 1)
    (by intro r hr; exact c1EuclideanSymbolDistance_hasGradientAt _)
    (by intro y; exact c1EuclideanSymbolDistance_nonneg y)
    (by intro y; exact c1EuclideanSymbolDistance_zero_iff y)
    c1EuclideanSymbolTarget_nonempty c1EuclideanSymbolTarget_closed
    (by intro r hr; exact hasDerivAt_neg (D (F.flow t₀ x₀ r)))
    (by intro r hr y; simp [M])
    (by intro r hr y z; simp [M, real_inner_comm])
    (by intro r hr y; simp [M, real_inner_self_eq_norm_sq])
    (by
      intro r hr hreach hnot
      have hnorm : inner ℝ (gradD r) (gradD r) = g2 r := by
        simpa [g2, D, gradD] using
          c1EuclideanSymbolGradient_inner_self (F.flow t₀ x₀ r)
      have hnorm' : ‖gradD r‖ ^ 2 = g2 r := by
        have hh := hnorm
        rw [real_inner_self_eq_norm_sq] at hh
        exact hh
      have hscale : gradV r = (2 : ℝ) • gradD r := rfl
      simp [M, gradZero]
      rw [hscale, real_inner_smul_right, hnorm, hnorm']
      have hg2 : 0 ≤ g2 r := by
        simp [g2, D, c1EuclideanSymbolDistance_nonneg]
      nlinarith [hg2])
    (by intro r hr hreach hnot; norm_num)
    (by intro r hr; norm_num [g2, D])
    (by
      intro r hr
      change 2 * D (F.flow t₀ x₀ r) =
        inner ℝ (c1EuclideanSymbolDistanceGradient (F.flow t₀ x₀ r))
          (M r (c1EuclideanSymbolDistanceGradient (F.flow t₀ x₀ r)))
      change 2 * D (F.flow t₀ x₀ r) =
        inner ℝ (c1EuclideanSymbolDistanceGradient (F.flow t₀ x₀ r))
          (c1EuclideanSymbolDistanceGradient (F.flow t₀ x₀ r))
      rw [c1EuclideanSymbolGradient_inner_self])
    (by intro r hr; exact c1EuclideanSymbolDistance_error_bound _)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · intro t ht
    rcases hresult.1 t ht with ⟨hD, hdist, _, _, _⟩
    norm_num [D, F, differentiableEuclideanConsensusOptimalFlow] at hD hdist ⊢
    exact ⟨hD, hdist⟩
  · exact hresult.2

theorem c1EuclideanOptimalField_eq_neg_three_gradient
    (x : C1EuclideanAgentState) (t : ℝ) :
    euclideanConsensusOptimalFlow.vectorField x
      (euclideanConsensusOptimalFlow.feedback x t) t =
        -3 • c1EuclideanSymbolDistanceGradient x := by
  apply c1EuclideanCoordinates.injective
  simp [euclideanConsensusOptimalFlow, consensusOptimalFlow,
    c1EuclideanSymbolDistanceGradient, c1EuclideanDisagreementDirection,
    c1EuclideanCoordinates, EuclideanSpace.equiv, EuclideanSpace.single,
    PiLp.coe_continuousLinearEquiv, PiLp.ofLp_single, PiLp.inner_apply]
  ext i
  fin_cases i <;> simp [Pi.single] <;> ring

/-- The selected closed-loop vector field is globally smooth, hence locally
Lipschitz, in the Euclidean state variable. This supplies O13's regularity
condition independently of the Theorem 20 wrapper, whose API does not ask for
it as a separate argument. -/
theorem c1EuclideanOptimalField_contDiff (t : ℝ) :
    ContDiff ℝ 1 (fun x : C1EuclideanAgentState =>
      euclideanConsensusOptimalFlow.vectorField x
        (euclideanConsensusOptimalFlow.feedback x t) t) := by
  have hfield : (fun x : C1EuclideanAgentState =>
      euclideanConsensusOptimalFlow.vectorField x
        (euclideanConsensusOptimalFlow.feedback x t) t) =
      fun x => -3 • c1EuclideanSymbolDistanceGradient x := by
    funext x
    exact c1EuclideanOptimalField_eq_neg_three_gradient x t
  rw [hfield]
  have hinner : ContDiff ℝ 1
      (fun x : C1EuclideanAgentState =>
        inner ℝ c1EuclideanDisagreementDirection x) := by
    convert (innerSL ℝ c1EuclideanDisagreementDirection).contDiff using 1
    ext x
    exact innerSL_apply_apply (𝕜 := ℝ)
      c1EuclideanDisagreementDirection x
  unfold c1EuclideanSymbolDistanceGradient
  fun_prop (disch := assumption)

theorem c1EuclideanOptimalField_locallyLipschitz (t : ℝ) :
    LocallyLipschitz (fun x : C1EuclideanAgentState =>
      euclideanConsensusOptimalFlow.vectorField x
        (euclideanConsensusOptimalFlow.feedback x t) t) :=
  (c1EuclideanOptimalField_contDiff t).locallyLipschitz

theorem c1EuclideanSymbolDistance_optimalFlow_decay
    (x : C1EuclideanAgentState) (t₀ t : ℝ) :
    c1EuclideanSymbolDistance
        (euclideanConsensusOptimalFlow.flow t₀ x t) =
      c1EuclideanSymbolDistance x * Real.exp (-6 * (t - t₀)) := by
  rw [c1EuclideanSymbolDistance_eq_coordinates,
    c1EuclideanSymbolDistance_eq_coordinates]
  simpa [euclideanConsensusOptimalFlow, c1EuclideanCoordinates_toLp] using
    c1SymbolDistance_optimalFlow_decay (c1EuclideanCoordinates x) t₀ t

/-- 定理4をO02最適rate-3二主体flowへ適用する。Pは非定数だが、V₀に同じPを
加えているため実効ポテンシャルでは相殺され、定量的な残差は共有ポテンシャルとなる。 -/
theorem consensusOptimalFlow_theorem4
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈
      closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀)) ∧
    (∀ t, t₀ ≤ t → Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (Tomabechi.Theorem4.weightedTCZ
        (closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀))
        consensusPresenceV0 consensusPresenceP consensusPresenceQ 1 1 t) ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))) ∧
    Filter.Tendsto (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (Tomabechi.Theorem4.weightedTCZ
        (closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀))
        consensusPresenceV0 consensusPresenceP consensusPresenceQ 1 1 t))
      atTop (𝓝 0) := by
  have hK := consensusOptimalFlow_reachable_closure_eq_box t₀ ht₀
  have hresidual_eq : Set.EqOn
      (fun s => Tomabechi.Theorem4.residual4
        (consensusPresenceV0 (consensusOptimalFlow.flow t₀ x s) s)
        (consensusPresenceP (consensusOptimalFlow.flow t₀ x s) s)
        (consensusPresenceQ (consensusOptimalFlow.flow t₀ x s) s) 1 1)
      (consensusOptimalPotentialAlong x t₀) (Set.Ici t₀) := by
    intro s hs
    exact consensusPresence_residual_eq_potential _
      (consensusOptimalFlow_forward_invariant x hx t₀ s hs) s
  have hresult := Tomabechi.Theorem4.weighted_reachable_tcz_distance_tendsto_zero
    (trajectory := fun s => consensusOptimalFlow.flow t₀ x s)
    (reachableAt := policyFlowReachableAt consensusOptimalFlow box t₀)
    (V₀ := consensusPresenceV0) (P := consensusPresenceP) (Q := consensusPresenceQ)
    (κ := 1) (θP := 1) (c := 3) (C := 1) (t₀ := t₀)
    (fun s hs => mem_policyFlowReachableAt_of_flow consensusOptimalFlow box t₀ s x hx hs)
    (by
      intro T hT s hs
      rw [hK]
      have hOrigin : ![0, 0] ∈ Tomabechi.Theorem4.weightedTCZ box
          consensusPresenceV0 consensusPresenceP consensusPresenceQ 1 1 s := by
        rw [Tomabechi.Theorem4.weightedTCZ]
        constructor
        · simp [box]
        · rw [consensusPresence_effective_eq_shared]
          have hp : DA.potential (![0, 0]) 0 = 0 := by
            rw [potential_eq ![0, 0]]
            norm_num [Tomabechi.Examples.Theorem2.θ, Tomabechi.Examples.Theorem2.γ]
          rw [hp]
          norm_num
      exact ⟨![0, 0], hOrigin⟩)
    (by
      intro T hT
      apply (consensusOptimalPotentialAlong_ac x hx t₀ T hT).congr
      intro s hs
      exact (hresidual_eq (show s ∈ Set.Ici t₀ from by
        rw [Set.uIcc_of_le hT] at hs
        exact hs.1)).symm)
    (by
      intro T hT
      rcases lt_or_eq_of_le hT with hlt | heq
      · have hpair : ({t₀, T} : Set ℝ) = {t₀} ∪ {T} := by ext u; simp [or_comm]
        have hnull : volume ({t₀, T} : Set ℝ) = 0 := by
          rw [hpair]
          exact measure_union_null (measure_singleton t₀) (measure_singleton T)
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
        filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hnull] with s hs hIcc
        have hst₀ : s ≠ t₀ := by intro h; apply hs; simp [h]
        have hsT : s ≠ T := by intro h; apply hs; simp [h]
        have hinside : s ∈ Set.Ioo t₀ T :=
          ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hst₀), lt_of_le_of_ne hIcc.2 hsT⟩
        have hnear : (fun r => Tomabechi.Theorem4.residual4
            (consensusPresenceV0 (consensusOptimalFlow.flow t₀ x r) r)
            (consensusPresenceP (consensusOptimalFlow.flow t₀ x r) r)
            (consensusPresenceQ (consensusOptimalFlow.flow t₀ x r) r) 1 1) =ᶠ[𝓝 s]
            consensusOptimalResidualPath x t₀ := by
          have hnhds := Ioo_mem_nhds hinside.1 hinside.2
          filter_upwards [hnhds] with r hr
          calc
            _ = consensusOptimalPotentialAlong x t₀ r :=
              hresidual_eq (show r ∈ Set.Ici t₀ from le_of_lt hr.1)
            _ = consensusOptimalResidualPath x t₀ r := by
              exact consensusOptimalPotentialAlong_eq x hx t₀ T hT
                (by rw [Set.uIcc_of_le hT]; exact ⟨hr.1.le, hr.2.le⟩)
        have hderiv := (consensusOptimalResidualPath_hasDerivAt x t₀ s).congr_of_eventuallyEq hnear
        have hval := hresidual_eq (show s ∈ Set.Ici t₀ from hIcc.1)
        have hval' := consensusOptimalPotentialAlong_eq x hx t₀ T hT (by
          rw [Set.uIcc_of_le hT]
          exact ⟨hinside.1.le, hinside.2.le⟩)
        rw [hderiv.deriv, ← hval', ← hval]
      · subst T
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
        filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1
          (by simp : volume (Set.Icc t₀ t₀) = 0)] with s hs hmem
        exact False.elim (hs hmem))
    (by
      intro T hT s hs
      rw [hK]
      have hxs := consensusOptimalFlow_forward_invariant x hx t₀ s hs.1
      rw [consensusPresence_weightedTCZ_eq_shared]
      rw [consensusPresence_residual_eq_potential _ hxs s]
      simpa [one_mul] using consensus_global_error_bound _ hxs s)
    ht₀ (by norm_num) (by norm_num)
  refine ⟨?_, ?_, hresult.2.2⟩
  · intro t ht
    rw [hK]
    exact consensusOptimalFlow_forward_invariant x hx t₀ t ht
  · intro t ht
    have hbound := hresult.2.1 t ht
    have hinit : Tomabechi.Theorem4.residual4
        (consensusPresenceV0 (consensusOptimalFlow.flow t₀ x t₀) t₀)
        (consensusPresenceP (consensusOptimalFlow.flow t₀ x t₀) t₀)
        (consensusPresenceQ (consensusOptimalFlow.flow t₀ x t₀) t₀) 1 1 =
        DA.potential x t₀ := by
      rw [consensusOptimalFlow.initial]
      exact consensusPresence_residual_eq_potential x hx t₀
    simpa [hK, hinit] using hbound

/-- 最適制御選択は初期時刻・二主体状態についてBorel可測。 -/
def consensusSelectedHorizonControl (_p : ℝ × AgentState) : ℝ → ℝ := fun _ => 3

theorem consensusSelectedHorizonControl_measurable :
    Measurable consensusSelectedHorizonControl := measurable_const

/-- 定数最適制御列の開始点右極限は最適feedback `3`。 -/
theorem consensusSelectedHorizonControl_rightLimit (t₀ : ℝ) (x : AgentState) :
    Tendsto (fun s => consensusSelectedHorizonControl (t₀, x) s)
      (𝓝[>] t₀) (𝓝 (consensusOptimalFlow.feedback x t₀)) := by
  simpa [consensusSelectedHorizonControl, consensusOptimalFlow] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (3 : ℝ)) (𝓝[>] t₀) (𝓝 3))

/-- 選ばれた最適列の積分軌道と同じ制御の閉ループH-flowは同じ二主体状態を作る。 -/
theorem consensusOptimalFlow_eq_selected_orbit (x : AgentState) (t₀ t : ℝ) :
    consensusOptimalFlow.flow t₀ x t =
      controlledConsensusState x t₀ c1MaxGainSignal t := by
  have horb : c1ControlledOrbit (halfDifference x) t₀ c1MaxGainSignal t =
      halfDifference x * Real.exp (-3 * (t - t₀)) := by
    rw [c1ControlledOrbit, c1MaxGain_accumulation]
    congr 1
    ring
  change ![meanState x + halfDifference x * Real.exp (-3 * (t - t₀)),
      meanState x - halfDifference x * Real.exp (-3 * (t - t₀))] = _
  rw [controlledConsensusState, horb]

/-- ゼロと最大ゲインは異なる許容制御列なので、方策族は非退化。 -/
theorem consensus_two_distinct_admissible_controls :
    c1ZeroGainSignal ≠ c1MaxGainSignal := c1_two_distinct_admissible_gains

/-- 最適ゲインflowは定理2と同じ共有TCZへ、時計変換後の指数率で収束する。

`consensusOptimalFlow` は旧 `consensusFlow` の1.5倍速い時間再パラメータ化なので、
TCZと残差は同じで距離率は2から3へ変わる。 -/
theorem consensusOptimalFlow_theorem2_distance
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht : t₀ ≤ t) :
    Metric.infDist (consensusOptimalFlow.flow t₀ x t) (DA.sharedTCZ box t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀)) := by
  by_cases hEq : t₀ = t
  · subst t
    have herror := consensus_global_error_bound x hx t₀
    have hdist := Real.le_sqrt_of_sq_le herror
    simpa [consensusOptimalFlow.initial] using hdist
  · have hlt : t₀ < t := lt_of_le_of_ne ht hEq
    let s := t₀ + (3 / 2 : ℝ) * (t - t₀)
    have hts : t₀ < s := by dsimp [s]; nlinarith
    have hslow := consensusFlow_theorem2 x hx t₀ s hts
    have hflow : consensusOptimalFlow.flow t₀ x t = consensusFlow.flow t₀ x s := by
      simpa [s, consensusOptimalTimeMap] using consensusOptimalFlow_eq_retimed x t₀ t
    rw [hflow]
    have hTCZ : DA.sharedTCZ box s = DA.sharedTCZ box t := by rfl
    rw [hTCZ] at hslow
    have hrate : -2 * (s - t₀) = -3 * (t - t₀) := by
      dsimp [s]
      ring
    simpa [hrate] using hslow.1.2

/-- 定理2をrate-3最適flowへ適用し、共有距離に加えて個人残差と
辺不整合の指数誤差も、箱内の任意の初期対・全ての後続時刻で与える。 -/
theorem consensusOptimalFlow_theorem2_full
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht : t₀ ≤ t) :
    (consensusOptimalFlow.flow t₀ x t ∈ box ∧
      Metric.infDist (consensusOptimalFlow.flow t₀ x t) (DA.sharedTCZ box t) ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))) ∧
    (∀ i, DA.individual i ((consensusOptimalFlow.flow t₀ x t) i) t ≤
      (DA.potential x t₀ / DA.individualWeight i) * Real.exp (-6 * (t - t₀))) ∧
    (∀ e, DA.mismatch e ((consensusOptimalFlow.flow t₀ x t) (DA.endpoint e).1)
      ((consensusOptimalFlow.flow t₀ x t) (DA.endpoint e).2) t ≤
      (DA.potential x t₀ / DA.edgeWeight e) * Real.exp (-6 * (t - t₀))) := by
  have hconnected : ∀ i j : Fin 2, Relation.ReflTransGen
      (fun a b => ∃ e, ((DA.endpoint e).1 = a ∧ (DA.endpoint e).2 = b) ∨
        ((DA.endpoint e).1 = b ∧ (DA.endpoint e).2 = a)) i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨0, Or.inl ⟨rfl, rfl⟩⟩
    · exact Relation.ReflTransGen.single ⟨0, Or.inr ⟨rfl, rfl⟩⟩
    · exact Relation.ReflTransGen.refl
  have hdecay : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      deriv (consensusOptimalPotentialAlong x t₀) s ≤
        -2 * 3 * consensusOptimalPotentialAlong x t₀ s := by
    by_cases hEq : t = t₀
    · subst t
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1
        (by simp : volume (Set.Icc t₀ t₀) = 0)] with s hs hmem
      exact False.elim (hs hmem)
    · exact consensusOptimalPotentialAlong_decay_ae x hx t₀ t
        (lt_of_le_of_ne ht (Ne.symm hEq))
  have hres := DA.theorem2_state_pair_conditional_conclusion
    box (fun s => consensusOptimalFlow.flow t₀ x s) hconnected 3 1 t₀ t
    (by norm_num) (by norm_num) ht
    (fun s hs => consensusOptimalFlow_forward_invariant x hx t₀ s hs.1)
    (fun s _ => consensus_sharedTCZ_nonempty s)
    (by
      change AbsolutelyContinuousOnInterval
        (consensusOptimalPotentialAlong x t₀) t₀ t
      exact consensusOptimalPotentialAlong_ac x hx t₀ t ht)
    hdecay
    (fun s hs => by
      simpa using consensus_global_error_bound
        (consensusOptimalFlow.flow t₀ x s)
        (consensusOptimalFlow_forward_invariant x hx t₀ s hs.1) s)
  have hpot : DA.potential (consensusOptimalFlow.flow t₀ x t₀) t₀ =
      DA.potential x t₀ := by rw [consensusOptimalFlow.initial]
  rw [hpot] at hres
  have hexp : -(2 * 3 * (t - t₀)) = -(6 * (t - t₀)) := by ring
  refine ⟨?_, ?_, ?_⟩
  · simpa using hres.1
  · intro i
    simpa [DA, Dsys, hexp] using hres.2.1 i
  · intro e
    simpa [hexp] using hres.2.2.1 e

end Tomabechi.Consistency.ConsistencyC1Consensus

end
