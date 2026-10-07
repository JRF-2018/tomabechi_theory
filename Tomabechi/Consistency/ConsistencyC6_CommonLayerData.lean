import Tomabechi.Consistency.ConsistencyC6_ControlCore

/-!
# C6: 共通束上の24/26/27データ

共通束 `WithTop ℕ` の各有限層にはC1の二主体状態と全可測有界ゲイン族を置き、頂点には
C5の上位ベクトル状態・方策・費用を置く。有限層は最大ゲイン3のC1制御と正baselineを
持ち、頂点の26/27解析条件は既存C5証人から移送する。両方を同じ層添字付きデータ
`c6LayeredNonnegativeTimeData` にまとめる。
-/

noncomputable section

namespace Tomabechi.Consistency.C6

open MeasureTheory
open Filter
open scoped Topology
open Tomabechi.Theorem24_26
open Tomabechi.Theorem24_26_Model
open Tomabechi.Examples.Theorem27
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus

/-- 全実数上のC1制御軌道は連続である。開始時刻より前は、その時刻からの
再始動等式で開始を動かして有限前向き区間の絶対連続性を使う。 -/
theorem c1ControlledOrbit_continuous (x T : ℝ) (u : C1GainSignal) :
    Continuous (fun s => c1ControlledOrbit x T u s) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s ≤ T
  · let a := s - 1
    let b := T + 1
    have hab : a ≤ b := by dsimp [a, b]; linarith
    have hrestart : (fun t => c1ControlledOrbit x T u t) =
        fun t => c1ControlledOrbit (c1ControlledOrbit x T u a) a u t := by
      funext t
      exact c1ControlledOrbit_restart x T a t u
    have hac := c1ControlledOrbit_absolutelyContinuousOnInterval
      (c1ControlledOrbit x T u a) a b hab u
    have haccont : ContinuousOn
        (fun t => c1ControlledOrbit (c1ControlledOrbit x T u a) a u t)
        (Set.Icc a b) := by
      simpa only [Set.uIcc_of_le hab] using hac.continuousOn
    have hcont : ContinuousOn (fun t => c1ControlledOrbit x T u t) (Set.Icc a b) := by
      rw [hrestart]
      exact haccont
    have hmem : Set.Icc a b ∈ 𝓝 s := by
      apply Filter.mem_of_superset
        (Ioo_mem_nhds (a := a) (b := b) (x := s)
          (by dsimp [a]; linarith) (by dsimp [b]; linarith)) (by
        intro t ht
        exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    exact hcont.continuousAt hmem
  · have hsT : T < s := lt_of_not_ge hs
    let b := s + 1
    have hTb : T ≤ b := by dsimp [b]; linarith
    have hac := c1ControlledOrbit_absolutelyContinuousOnInterval x T b hTb u
    have haccont : ContinuousOn (fun t => c1ControlledOrbit x T u t) (Set.Icc T b) := by
      simpa only [Set.uIcc_of_le hTb] using hac.continuousOn
    have hmem : Set.Icc T b ∈ 𝓝 s := by
      apply Filter.mem_of_superset
        (Ioo_mem_nhds (a := T) (b := b) (x := s) hsT (by dsimp [b]; linarith)) (by
        intro t ht
        exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    exact haccont.continuousAt hmem

/-- C1二主体軌道も、任意の可測ゲイン方策に対して連続である。 -/
theorem controlledConsensusState_continuous
    (x : AgentState) (T : ℝ) (u : C1GainSignal) :
    Continuous (fun s => controlledConsensusState x T u s) := by
  have hq := c1ControlledOrbit_continuous (halfDifference x) T u
  unfold controlledConsensusState
  fun_prop

/-- 半差は連続な二主体軌道の座標線形写像なので連続である。 -/
theorem controlledConsensusState_halfDifference_continuous
    (x : AgentState) (T : ℝ) (u : C1GainSignal) :
    Continuous (fun s => halfDifference (controlledConsensusState x T u s)) := by
  have hstate := controlledConsensusState_continuous x T u
  change Continuous (fun s =>
    (controlledConsensusState x T u s 0 - controlledConsensusState x T u s 1) / 2)
  exact (((continuous_apply 0).comp hstate).sub
    ((continuous_apply 1).comp hstate)).div_const 2

/-- 任意のC1ゲイン競合が作る割引評価被積分関数は可測である。 -/
theorem c1FiniteLayer_discounted_cost_measurable
    (x : AgentState) (T : ℝ) (u : C1GainSignal) :
    Measurable (fun s => ENNReal.ofReal
      (theorem26DiscountWeight 1 T s *
        (1 + 8 * (halfDifference (controlledConsensusState x T u s)) ^ 2))) := by
  have hhalf := controlledConsensusState_halfDifference_continuous x T u
  have hcost : Continuous (fun s : ℝ =>
      1 + 8 * (halfDifference (controlledConsensusState x T u s)) ^ 2) := by
    exact continuous_const.add (continuous_const.mul (hhalf.pow 2))
  have hweight : Continuous (fun s : ℝ => theorem26DiscountWeight 1 T s) := by
    fun_prop [theorem26DiscountWeight]
  exact ENNReal.measurable_ofReal.comp (hweight.mul hcost).measurable

/-- 将来半直線上の指数関数は積分可能。率 `c>0` を明示しておく。 -/
theorem c6_future_exp_integrable {c : ℝ} (hc : 0 < c) (T : ℝ) :
    Integrable (fun s => Real.exp (-c * (s - T))) (futureLebesgueMeasure T) := by
  change Integrable (fun s => Real.exp (-c * (s - T)))
    (MeasureTheory.volume.restrict (Set.Ici T))
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-c * s)) (Set.Ioi T) :=
    integrableOn_exp_mul_Ioi (a := -c) (by linarith) T
  have hbaseIci : IntegrableOn (fun s : ℝ => Real.exp (-c * s)) (Set.Ici T) :=
    integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.2 hbase
  have hscaled : IntegrableOn
      (fun s : ℝ => Real.exp (c * T) * Real.exp (-c * s)) (Set.Ici T) :=
    hbaseIci.const_mul (Real.exp (c * T))
  have heq : (fun s : ℝ => Real.exp (-c * (s - T))) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ici T)]
      (fun s => Real.exp (c * T) * Real.exp (-c * s)) := by
    filter_upwards with s
    rw [show -c * (s - T) = c * T + (-c * s) by ring, Real.exp_add]
  exact hscaled.congr heq.symm

/-- 最大ゲイン3の有限層C1割引評価は実際に積分でき、候補価値は
`1 + 8 d²/7`（`d` は初期半差）となる。 -/
theorem c1FiniteLayer_optimalValue_integral (x : AgentState) (T : ℝ) :
    (∫ s, theorem26DiscountWeight 1 T s *
      (1 + 8 * (halfDifference
        (controlledConsensusState x T c1MaxGainSignal s)) ^ 2)
      ∂futureLebesgueMeasure T) =
      1 + 8 * (halfDifference x) ^ 2 / 7 := by
  let d := halfDifference x
  have hstate (s : ℝ) :
      halfDifference (controlledConsensusState x T c1MaxGainSignal s) =
        d * Real.exp (-3 * (s - T)) := by
    rw [controlledConsensusState_halfDifference, c1ControlledOrbit,
      c1MaxGain_accumulation]
    rw [show -(3 * (s - T)) = -3 * (s - T) by ring]
  have hintegrand : (fun s => theorem26DiscountWeight 1 T s *
      (1 + 8 * (halfDifference
        (controlledConsensusState x T c1MaxGainSignal s)) ^ 2)) =
      (fun s => Real.exp (-1 * (s - T)) +
        (8 * d ^ 2) * Real.exp (-7 * (s - T))) := by
    funext s
    rw [theorem26DiscountWeight, hstate]
    let δ := s - T
    have hexp : Real.exp (-1 * δ) * Real.exp (-3 * δ) *
        Real.exp (-3 * δ) = Real.exp (-7 * δ) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1 <;> dsimp [δ] <;> ring
    calc
      Real.exp (-1 * δ) * (1 + 8 * (d * Real.exp (-3 * δ)) ^ 2) =
          Real.exp (-1 * δ) +
            8 * d ^ 2 * (Real.exp (-1 * δ) * Real.exp (-3 * δ) *
              Real.exp (-3 * δ)) := by ring
      _ = Real.exp (-1 * δ) + 8 * d ^ 2 * Real.exp (-7 * δ) := by rw [hexp]
  have hi1 : Integrable (fun s : ℝ => Real.exp (-1 * (s - T)))
      (futureLebesgueMeasure T) := c6_future_exp_integrable (by norm_num) T
  have hi7 : Integrable (fun s : ℝ => Real.exp (-7 * (s - T)))
      (futureLebesgueMeasure T) := c6_future_exp_integrable (by norm_num) T
  have hsum : Integrable
      (fun s : ℝ => Real.exp (-1 * (s - T)) +
        (8 * d ^ 2) * Real.exp (-7 * (s - T)))
      (futureLebesgueMeasure T) := hi1.add (hi7.const_mul (8 * d ^ 2))
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun s => congrFun hintegrand s))]
  rw [MeasureTheory.integral_add hi1 (hi7.const_mul (8 * d ^ 2)),
    MeasureTheory.integral_const_mul]
  rw [future_exp_integral (c := 1) (by norm_num) T,
    future_exp_integral (c := 7) (by norm_num) T]
  dsimp [d]
  ring

/-- 最大ゲインのC1有限層割引被積分関数を二つの指数核に分ける恒等式。 -/
theorem c1FiniteLayer_optimal_integrand_eq (x : AgentState) (T s : ℝ) :
    theorem26DiscountWeight 1 T s *
      (1 + 8 * (halfDifference
        (controlledConsensusState x T c1MaxGainSignal s)) ^ 2) =
      Real.exp (-1 * (s - T)) +
        (8 * (halfDifference x) ^ 2) * Real.exp (-7 * (s - T)) := by
  let d := halfDifference x
  have hstate : halfDifference
      (controlledConsensusState x T c1MaxGainSignal s) =
        d * Real.exp (-3 * (s - T)) := by
    rw [controlledConsensusState_halfDifference, c1ControlledOrbit,
      c1MaxGain_accumulation]
    rw [show -(3 * (s - T)) = -3 * (s - T) by ring]
  rw [theorem26DiscountWeight, hstate]
  let δ := s - T
  have hexp : Real.exp (-1 * δ) * Real.exp (-3 * δ) *
      Real.exp (-3 * δ) = Real.exp (-7 * δ) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1 <;> dsimp [δ] <;> ring
  calc
    Real.exp (-1 * δ) * (1 + 8 * (d * Real.exp (-3 * δ)) ^ 2) =
        Real.exp (-1 * δ) +
          8 * d ^ 2 * (Real.exp (-1 * δ) * Real.exp (-3 * δ) *
            Real.exp (-3 * δ)) := by ring
    _ = Real.exp (-1 * δ) + 8 * d ^ 2 * Real.exp (-7 * δ) := by rw [hexp]

/-- C1有限層の最大ゲイン費用は、将来半直線上で可積分である。 -/
theorem c1FiniteLayer_optimalCost_integrable (x : AgentState) (T : ℝ) :
    Integrable (fun s => theorem26DiscountWeight 1 T s *
      (1 + 8 * (halfDifference
        (controlledConsensusState x T c1MaxGainSignal s)) ^ 2))
      (futureLebesgueMeasure T) := by
  have h1 : Integrable (fun s : ℝ => Real.exp (-1 * (s - T)))
      (futureLebesgueMeasure T) := c6_future_exp_integrable (by norm_num) T
  have h7 : Integrable (fun s : ℝ => Real.exp (-7 * (s - T)))
      (futureLebesgueMeasure T) := c6_future_exp_integrable (by norm_num) T
  have hsum : Integrable
      (fun s : ℝ => Real.exp (-1 * (s - T)) +
        (8 * (halfDifference x) ^ 2) * Real.exp (-7 * (s - T)))
      (futureLebesgueMeasure T) := h1.add (h7.const_mul (8 * (halfDifference x) ^ 2))
  apply hsum.congr
  filter_upwards with s
  exact (c1FiniteLayer_optimal_integrand_eq x T s).symm

/-- 有限層の割引最適値は、全てのC1ゲイン競合の拡張実数費用以下。 -/
theorem c1FiniteLayer_optimalValue_minimal
    (x : AgentState) (T : ℝ) (u : C1GainSignal) :
    ENNReal.ofReal (1 + 8 * (halfDifference x) ^ 2 / 7) ≤
      ∫⁻ s, ENNReal.ofReal (theorem26DiscountWeight 1 T s *
        (1 + 8 * (halfDifference
          (controlledConsensusState x T u s)) ^ 2))
        ∂futureLebesgueMeasure T := by
  have hoptInt := c1FiniteLayer_optimalCost_integrable x T
  have hoptNonneg : 0 ≤ᵐ[futureLebesgueMeasure T]
      (fun s => theorem26DiscountWeight 1 T s *
        (1 + 8 * (halfDifference
          (controlledConsensusState x T c1MaxGainSignal s)) ^ 2)) := by
    filter_upwards with s
    rw [theorem26DiscountWeight]
    positivity
  have hoptLin := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hoptInt hoptNonneg
  have hvalue : ENNReal.ofReal (1 + 8 * (halfDifference x) ^ 2 / 7) =
      ∫⁻ s, ENNReal.ofReal (theorem26DiscountWeight 1 T s *
        (1 + 8 * (halfDifference
          (controlledConsensusState x T c1MaxGainSignal s)) ^ 2))
        ∂futureLebesgueMeasure T := by
    rw [← c1FiniteLayer_optimalValue_integral x T]
    exact hoptLin
  have hpoint : ∀ᵐ s ∂futureLebesgueMeasure T,
      theorem26DiscountWeight 1 T s *
          (1 + 8 * (halfDifference
            (controlledConsensusState x T c1MaxGainSignal s)) ^ 2) ≤
        theorem26DiscountWeight 1 T s *
          (1 + 8 * (halfDifference
            (controlledConsensusState x T u s)) ^ 2) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ici] with s hs
    exact c1FiniteLayer_discounted_cost_minimal_pointwise x T s u hs
  calc
    _ = ∫⁻ s, ENNReal.ofReal (theorem26DiscountWeight 1 T s *
          (1 + 8 * (halfDifference
            (controlledConsensusState x T c1MaxGainSignal s)) ^ 2))
          ∂futureLebesgueMeasure T := hvalue
    _ ≤ ∫⁻ s, ENNReal.ofReal (theorem26DiscountWeight 1 T s *
          (1 + 8 * (halfDifference
            (controlledConsensusState x T u s)) ^ 2))
          ∂futureLebesgueMeasure T := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [hpoint] with s hs
      exact ENNReal.ofReal_le_ofReal hs

/-- `WithTop ℕ` 上、有限層はC1二主体状態と全可測ゲイン族、頂点はC5ベクトル状態と
元のC5 feedbackを持つ層別型。 -/
abbrev C6LayeredState : CommonLayer → Type
  | none => VectorSourceState true
  | some _ => AgentState

abbrev C6LayeredPolicy : (a : CommonLayer) → Type
  | none => VectorSourcePolicy true
  | some _ => C1GainSignal

def c6LayeredTrajectory : (a : CommonLayer) → C6LayeredPolicy a →
    C6LayeredState a → ℝ → ℝ → C6LayeredState a
  | none, π, x, T, s => vectorSourceData.trajectory true π x T s
  | some _, π, x, T, s => controlledConsensusState x T π s

def c6LayeredRunningCost : (a : CommonLayer) → C6LayeredPolicy a →
    C6LayeredState a → ℝ → ℝ
  | none, π, x, t => vectorSourceData.runningCost true π x t
  | some _, _, x, _ => 1 + 8 * (halfDifference x) ^ 2

/-- 有限層Dの実走行費は、箱内C1モデルの基礎評価 `V₀` と一致する。
正baselineと残差係数を同じ層上で保つS2の保存式。 -/
theorem c6LayeredFiniteRunningCost_eq_C1V0
    (n : ℕ) (π : C1GainSignal) (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    c6LayeredRunningCost (some n) π x t = consensusV0 x t := by
  rw [c1V0_eq_baseline_add_centeredPotential x hx t]
  simp [c6LayeredRunningCost, centeredQuadraticPotential, c1ToCompleteState,
    Tomabechi.Consistency.C2.cognitiveCoordinate, halfDifference]
  ring

/-- Dの有限添字nに対応する中心 `representation n` で測った
再中心化済み二次評価として表す。C2正層kはDの添字k+1に入る。 -/
theorem c6LayeredFiniteRunningCost_eq_layerPotential
    (n : ℕ) (π : C1GainSignal) (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    c6LayeredRunningCost (some n) π x t =
      1 + 16 * centeredQuadraticPotential
        (Tomabechi.Consistency.C3.representation n)
        (recenterEntropyState 1
          (Tomabechi.Consistency.C3.representation n)
          (c1ToCompleteState x)) := by
  rw [c6LayeredFiniteRunningCost_eq_C1V0 n π x hx t,
    c1V0_eq_baseline_add_centeredPotential x hx t,
    recenterEntropyState_potential]

/-- 有限層C1 flow上でも、走行費は同じ層中心で再中心化した評価そのもの。 -/
theorem c6LayeredTrajectory_runningCost_eq_layerPotential
    (n : ℕ) (π : C1GainSignal) (x : AgentState) (hx : x ∈ box)
    (T s : ℝ) (hTs : T ≤ s) :
    c6LayeredRunningCost (some n) π
        (c6LayeredTrajectory (some n) π x T s) s =
      1 + 16 * centeredQuadraticPotential
        (Tomabechi.Consistency.C3.representation n)
        (recenterEntropyState 1
          (Tomabechi.Consistency.C3.representation n)
          (c1ToCompleteState (c6LayeredTrajectory (some n) π x T s))) := by
  apply c6LayeredFiniteRunningCost_eq_layerPotential
  exact controlledConsensusState_mem_box x hx T s π hTs

def c6LayeredAdmissible : (a : CommonLayer) → C6LayeredPolicy a →
    C6LayeredState a → ℝ → Prop
  | none, π, x, T => vectorSourceData.admissible true π x T
  | some _, _, _, _ => True

def c6LayeredOptimalValue : (a : CommonLayer) → C6LayeredState a → ℝ → ℝ
  | none, x, T => vectorSourceData.optimalValue true x T
  | some _, x, _ => 1 + 8 * (halfDifference x) ^ 2 / 7

noncomputable def c6LayeredOptimalPolicy : (a : CommonLayer) →
    (x : C6LayeredState a) → ℝ → C6LayeredPolicy a
  | none, x, T => vectorSourceData.optimalPolicy true x T
  | some _, _, _ => c1MaxGainSignal

/-- C1全制御族を全有限層へ、C5元データを頂点へ置いた共通束上の定理24データ。
有限層と頂点のcontextを層型で保ち、C1下位層を単点Unitへ潰さない。 -/
def c6LayeredNonnegativeTimeData :
    Theorem24NonnegativeTimeData C6LayeredState C6LayeredPolicy where
  rho := 1
  rho_pos := by norm_num
  trajectory := c6LayeredTrajectory
  runningCost := c6LayeredRunningCost
  admissible := c6LayeredAdmissible
  optimalValue := c6LayeredOptimalValue
  optimalPolicy := c6LayeredOptimalPolicy
  trajectory_initial := by
    intro a π x T hT hπ
    cases a with
    | none =>
      simpa [c6LayeredTrajectory, c6LayeredAdmissible] using
        (vectorSourceData.trajectory_initial true π x T hT hπ)
    | some n =>
      change controlledConsensusState x T π T = x
      ext i
      fin_cases i <;> simp [controlledConsensusState, c1ControlledOrbit_initial,
        meanState, halfDifference] <;> ring
  runningCost_nonnegative := by
    intro a π x t
    cases a with
    | none => exact vectorSourceData.runningCost_nonnegative true π x t
    | some n =>
      dsimp [c6LayeredRunningCost]
      positivity
  measurable_cost := by
    intro a x T π hT hπ
    cases a with
    | none =>
      have hrho : vectorSourceData.rho = 1 := rfl
      rw [← hrho]
      exact vectorSourceData.measurable_cost true x T π hT hπ
    | some n =>
      exact c1FiniteLayer_discounted_cost_measurable x T π
  optimal_cost_integrable := by
    intro a x T hT
    cases a with
    | none =>
      have hrho : vectorSourceData.rho = 1 := rfl
      rw [← hrho]
      exact vectorSourceData.optimal_cost_integrable true x T hT
    | some n =>
      exact c1FiniteLayer_optimalCost_integrable x T
  optimal_policy_admissible := by
    intro a x T hT
    cases a with
    | none =>
      simpa [c6LayeredAdmissible, c6LayeredOptimalPolicy] using
        (vectorSourceData.optimal_policy_admissible true x T hT)
    | some n => trivial
  optimal_value_attained := by
    intro a x T hT
    cases a with
    | none =>
      have hrho : vectorSourceData.rho = 1 := rfl
      rw [← hrho]
      exact vectorSourceData.optimal_value_attained true x T hT
    | some n =>
      simpa [c6LayeredTrajectory, c6LayeredRunningCost,
        c6LayeredOptimalPolicy, c6LayeredOptimalValue] using
          (c1FiniteLayer_optimalValue_integral x T).symm
  optimal_value_minimal := by
    intro a x T π hT hπ
    cases a with
    | none =>
      have hrho : vectorSourceData.rho = 1 := rfl
      rw [← hrho]
      exact vectorSourceData.optimal_value_minimal true x T π hT hπ
    | some n => exact c1FiniteLayer_optimalValue_minimal x T π
  condition24A := by
    intro a ha x T hT π hπ
    cases a with
    | none => exact (lt_irrefl ⊤ ha).elim
    | some n =>
      have hpositive : ∀ u : C1GainSignal, c6LayeredAdmissible (some n) u x T →
          ∀ᵐ s ∂futureLebesgueMeasure T,
            0 < c6LayeredRunningCost (some n) u
              (c6LayeredTrajectory (some n) u x T s) s := by
        intro u hu
        filter_upwards with s
        dsimp [c6LayeredRunningCost]
        positivity
      have hcondition := theorem24_condition24A_of_ae_strictlyPositive
        (fun u y t s => c6LayeredRunningCost (some n) u
          (c6LayeredTrajectory (some n) u y t s) s)
        (c6LayeredAdmissible (some n)) x T hpositive
      exact hcondition π hπ

@[simp] theorem c6LayeredData_rho : c6LayeredNonnegativeTimeData.rho = 1 := rfl

/-- この実際の `WithTop ℕ` 層別データから定理24を全有限層で適用する。 -/
theorem c6LayeredData_all_finite_theorem24 :
    ∀ a (ha : a < (⊤ : CommonLayer))
      (x : C6LayeredState a) (T : ℝ), 0 ≤ T →
      0 < c6LayeredNonnegativeTimeData.optimalValue a x T ∧
        ¬ FeedbackPZS (c6LayeredNonnegativeTimeData.admissible a)
          (fun _ => futureLebesgueMeasure T)
          (fun π y t s => c6LayeredNonnegativeTimeData.runningCost a π
            (c6LayeredNonnegativeTimeData.trajectory a π y t s) s) x T := by
  exact theorem24_lower_conclusions_from_nonnegativeTimeData c6LayeredNonnegativeTimeData

@[simp] theorem c6LayeredData_top_trajectory (π : VectorSourcePolicy true)
    (x : VectorSourceState true) (T s : ℝ) :
    c6LayeredNonnegativeTimeData.trajectory (⊤ : CommonLayer) π x T s =
      vectorSourceData.trajectory true π x T s := rfl

@[simp] theorem c6LayeredData_top_runningCost (π : VectorSourcePolicy true)
    (x : VectorSourceState true) (t : ℝ) :
    c6LayeredNonnegativeTimeData.runningCost (⊤ : CommonLayer) π x t =
      vectorSourceData.runningCost true π x t := rfl

@[simp] theorem c6LayeredData_top_optimalValue (x : VectorSourceState true) (t : ℝ) :
    c6LayeredNonnegativeTimeData.optimalValue (⊤ : CommonLayer) x t =
      vectorSourceData.optimalValue true x t := rfl

@[simp] theorem c6LayeredData_top_admissible (π : VectorSourcePolicy true)
    (x : VectorSourceState true) (T : ℝ) :
    c6LayeredNonnegativeTimeData.admissible (⊤ : CommonLayer) π x T =
      vectorSourceData.admissible true π x T := rfl

@[simp] theorem c6LayeredData_top_optimalPolicy (x : VectorSourceState true) (T : ℝ) :
    c6LayeredNonnegativeTimeData.optimalPolicy (⊤ : CommonLayer) x T =
      vectorSourceData.optimalPolicy true x T := rfl

theorem c6LayeredData_top_admissible_fun :
    c6LayeredNonnegativeTimeData.admissible (⊤ : CommonLayer) =
      vectorSourceData.admissible true := rfl

@[simp] theorem c6LayeredAdmissible_top :
    c6LayeredAdmissible (⊤ : CommonLayer) = vectorSourceData.admissible true := rfl

@[simp] theorem c6LayeredOptimalValue_top :
    c6LayeredOptimalValue (⊤ : CommonLayer) = vectorSourceData.optimalValue true := rfl

theorem c6LayeredData_top_trajectory_fun :
    c6LayeredNonnegativeTimeData.trajectory (⊤ : CommonLayer) =
      vectorSourceData.trajectory true := rfl

theorem c6LayeredData_top_runningCost_fun :
    c6LayeredNonnegativeTimeData.runningCost (⊤ : CommonLayer) =
      vectorSourceData.runningCost true := rfl

theorem c6LayeredData_top_optimalValue_fun :
    c6LayeredNonnegativeTimeData.optimalValue (⊤ : CommonLayer) =
      vectorSourceData.optimalValue true := rfl

/-- 26 dynamics uses the same C1-rich common-layer 24 data; its top projection
is definitionally the existing C5 dynamics witness. -/
def c6LayeredDynamics :
    Theorem26NonnegativeTimeDynamics c6LayeredNonnegativeTimeData E2 where
  policyEquiv := vectorSourceDynamics.policyEquiv
  feedback := vectorSourceDynamics.feedback
  alive := vectorSourceDynamics.alive
  feedback_attains_optimum := by
    intro x T hT hx
    rw [c6LayeredData_rho]
    have hsource := vectorSourceDynamics.feedback_attains_optimum x T hT hx
    rw [show vectorSourceData.rho = 1 by rfl] at hsource
    simpa [c6LayeredData_top_admissible, c6LayeredData_top_runningCost,
      c6LayeredData_top_trajectory, c6LayeredData_top_optimalValue] using hsource
  W := vectorSourceDynamics.W
  ω := vectorSourceDynamics.ω
  c₁ := vectorSourceDynamics.c₁
  c₂ := vectorSourceDynamics.c₂
  rate := vectorSourceDynamics.rate
  c₁_pos := vectorSourceDynamics.c₁_pos
  c₂_pos := vectorSourceDynamics.c₂_pos
  rate_pos := vectorSourceDynamics.rate_pos
  trajectory_alive := by
    intro x T s hT hx hTs
    simpa using vectorSourceDynamics.trajectory_alive x T s hT hx hTs
  target_nonempty := by
    intro T hT
    rw [c6LayeredData_top_optimalValue_fun]
    exact vectorSourceDynamics.target_nonempty T hT
  target_closed := by
    intro T hT
    rw [c6LayeredData_top_optimalValue_fun]
    exact vectorSourceDynamics.target_closed T hT
  target_invariant := by
    intro x T s hT hx hTs
    rw [c6LayeredData_top_optimalValue_fun, c6LayeredData_top_trajectory_fun]
    exact vectorSourceDynamics.target_invariant x T s hT hx hTs
  W_absolutelyContinuous := by
    intro x T s hT hx hTs
    rw [c6LayeredData_top_trajectory_fun]
    exact vectorSourceDynamics.W_absolutelyContinuous x T s hT hx hTs
  W_nonnegative := by
    intro x T s hT hx hTs
    rw [c6LayeredData_top_trajectory_fun]
    exact vectorSourceDynamics.W_nonnegative x T s hT hx hTs
  W_rightSlope := by
    intro x T u hT hx hu
    rw [c6LayeredData_top_trajectory_fun]
    exact vectorSourceDynamics.W_rightSlope x T u hT hx hu
  W_lower_distance_bound := by
    intro x T s hT hx hTs
    rw [c6LayeredData_top_optimalValue_fun, c6LayeredData_top_trajectory_fun]
    exact vectorSourceDynamics.W_lower_distance_bound x T s hT hx hTs
  W_upper_distance_bound := by
    intro x T s hT hx hTs
    rw [c6LayeredData_top_optimalValue_fun, c6LayeredData_top_trajectory_fun]
    exact vectorSourceDynamics.W_upper_distance_bound x T s hT hx hTs
  ω_continuous := vectorSourceDynamics.ω_continuous
  ω_zero := vectorSourceDynamics.ω_zero
  ω_nonnegative := vectorSourceDynamics.ω_nonnegative
  ω_monotone_on_nonnegative := vectorSourceDynamics.ω_monotone_on_nonnegative
  value_distance_bound := by
    intro y t ht hy
    rw [c6LayeredData_top_optimalValue_fun]
    exact vectorSourceDynamics.value_distance_bound y t ht hy

/-- 新しい共通Dの有限層24-Aと頂点Eの26条件を同じrecordから取り出す。 -/
noncomputable def c6LayeredData_jointConclusion
    (x : VectorSourceState true) (T : ℝ) (hT : 0 ≤ T)
    (hx : x ∈ c6LayeredDynamics.alive) :=
  theorem24_to26_from_nonnegativeTimeData
    c6LayeredNonnegativeTimeData c6LayeredDynamics x T hT hx

/-- 共通束の有限層は下位抽象、頂点は上位抽象を表す。 -/
abbrev commonLayerToC5Abstraction : CommonLayer → Bool
  | none => true
  | some _ => false

theorem commonLayerToC5Abstraction_top :
    commonLayerToC5Abstraction (⊤ : CommonLayer) = true := by
  rfl

theorem commonLayerToC5Abstraction_coe (n : ℕ) :
    commonLayerToC5Abstraction (n : CommonLayer) = false := by
  rfl

theorem commonLayerToC5Abstraction_eq_false_of_lt_top
    (a : CommonLayer) (ha : a < ⊤) :
    commonLayerToC5Abstraction a = false := by
  have hne : a ≠ ⊤ := ne_of_lt ha
  cases a with
  | none => exact False.elim (hne rfl)
  | some n => rfl

/-- C5のデータを層写像で引き戻した共通束上の24データ。
全ての有限層で同じ下位費用を使い、頂点ではC5上位の実データを使う。 -/
def c6C5PullbackData :
    Theorem24NonnegativeTimeData
      (fun a : CommonLayer =>
        VectorSourceState (commonLayerToC5Abstraction a))
      (fun a : CommonLayer =>
        VectorSourcePolicy (commonLayerToC5Abstraction a)) where
  rho := vectorSourceData.rho
  rho_pos := vectorSourceData.rho_pos
  trajectory := fun a => vectorSourceData.trajectory (commonLayerToC5Abstraction a)
  runningCost := fun a => vectorSourceData.runningCost (commonLayerToC5Abstraction a)
  admissible := fun a => vectorSourceData.admissible (commonLayerToC5Abstraction a)
  optimalValue := fun a => vectorSourceData.optimalValue (commonLayerToC5Abstraction a)
  optimalPolicy := fun a => vectorSourceData.optimalPolicy (commonLayerToC5Abstraction a)
  trajectory_initial := by
    intro a π x T hT hπ
    exact vectorSourceData.trajectory_initial (commonLayerToC5Abstraction a) π x T hT hπ
  runningCost_nonnegative := by
    intro a π y t
    exact vectorSourceData.runningCost_nonnegative (commonLayerToC5Abstraction a) π y t
  measurable_cost := by
    intro a x T π hT hπ
    exact vectorSourceData.measurable_cost (commonLayerToC5Abstraction a) x T π hT hπ
  optimal_cost_integrable := by
    intro a x T hT
    exact vectorSourceData.optimal_cost_integrable (commonLayerToC5Abstraction a) x T hT
  optimal_policy_admissible := by
    intro a x T hT
    exact vectorSourceData.optimal_policy_admissible (commonLayerToC5Abstraction a) x T hT
  optimal_value_attained := by
    intro a x T hT
    exact vectorSourceData.optimal_value_attained (commonLayerToC5Abstraction a) x T hT
  optimal_value_minimal := by
    intro a x T π hT hπ
    exact vectorSourceData.optimal_value_minimal (commonLayerToC5Abstraction a) x T π hT hπ
  condition24A := by
    intro a ha x T hT π hπ
    have hlow : commonLayerToC5Abstraction a < (⊤ : Bool) := by
      rw [commonLayerToC5Abstraction_eq_false_of_lt_top a ha]
      decide
    exact vectorSourceData.condition24A (commonLayerToC5Abstraction a)
      hlow x T hT π hπ

/-- 頂点で引き戻したデータはC5上位データそのもの。 -/
theorem c6C5PullbackData_top_trajectory (π : VectorSourcePolicy true)
    (x : VectorSourceState true) (T s : ℝ) :
    c6C5PullbackData.trajectory (⊤ : CommonLayer) π x T s =
      vectorSourceData.trajectory true π x T s := by
  rfl

theorem c6C5PullbackData_top_runningCost (π : VectorSourcePolicy true)
    (x : VectorSourceState true) (t : ℝ) :
    c6C5PullbackData.runningCost (⊤ : CommonLayer) π x t =
      vectorSourceData.runningCost true π x t := by
  rfl

theorem c6C5PullbackData_top_optimalValue (x : VectorSourceState true) (t : ℝ) :
    c6C5PullbackData.optimalValue (⊤ : CommonLayer) x t =
      vectorSourceData.optimalValue true x t := by
  rfl

theorem c6C5PullbackData_top_admissible (π : VectorSourcePolicy true)
    (x : VectorSourceState true) (T : ℝ) :
    c6C5PullbackData.admissible (⊤ : CommonLayer) π x T =
      vectorSourceData.admissible true π x T := by
  rfl

theorem c6C5PullbackData_top_optimalPolicy (x : VectorSourceState true) (T : ℝ) :
    c6C5PullbackData.optimalPolicy (⊤ : CommonLayer) x T =
      vectorSourceData.optimalPolicy true x T := by
  rfl

/-- 同じ共通束データから、全有限層で定理24の正費用結論を得る。 -/
theorem c6C5PullbackData_all_finite_theorem24 :
    ∀ a (ha : a < (⊤ : CommonLayer))
      (x : VectorSourceState (commonLayerToC5Abstraction a)) (T : ℝ),
      0 ≤ T →
        0 < c6C5PullbackData.optimalValue a x T ∧
        ¬ FeedbackPZS (c6C5PullbackData.admissible a)
          (fun _ => futureLebesgueMeasure T)
          (fun π y t s => c6C5PullbackData.runningCost a π
            (c6C5PullbackData.trajectory a π y t s) s) x T := by
  exact theorem24_lower_conclusions_from_nonnegativeTimeData c6C5PullbackData

/-- 頂点の26力学も、上で定義した同じ層別Dの最上位射影を使う。
解析条件は既存C5証人から輸送し、Dの費用・軌道・値との同定を明示する。 -/
def c6C5PullbackDynamics :
    Theorem26NonnegativeTimeDynamics c6C5PullbackData E2 where
  policyEquiv := vectorSourceDynamics.policyEquiv
  feedback := vectorSourceDynamics.feedback
  alive := vectorSourceDynamics.alive
  feedback_attains_optimum := by
    intro x T hT hx
    simpa [c6C5PullbackData, c6C5PullbackData_top_admissible,
      c6C5PullbackData_top_runningCost, c6C5PullbackData_top_trajectory,
      c6C5PullbackData_top_optimalValue] using
      (vectorSourceDynamics.feedback_attains_optimum x T hT hx)
  W := vectorSourceDynamics.W
  ω := vectorSourceDynamics.ω
  c₁ := vectorSourceDynamics.c₁
  c₂ := vectorSourceDynamics.c₂
  rate := vectorSourceDynamics.rate
  c₁_pos := vectorSourceDynamics.c₁_pos
  c₂_pos := vectorSourceDynamics.c₂_pos
  rate_pos := vectorSourceDynamics.rate_pos
  trajectory_alive := by
    intro x T s hT hx hTs
    simpa [c6C5PullbackData, c6C5PullbackData_top_trajectory] using
      vectorSourceDynamics.trajectory_alive x T s hT hx hTs
  target_nonempty := by
    intro T hT
    simpa [c6C5PullbackData, c6C5PullbackData_top_optimalValue] using
      vectorSourceDynamics.target_nonempty T hT
  target_closed := by
    intro T hT
    simpa [c6C5PullbackData, c6C5PullbackData_top_optimalValue] using
      vectorSourceDynamics.target_closed T hT
  target_invariant := by
    intro x T s hT hx hTs
    simpa [c6C5PullbackData, c6C5PullbackData_top_trajectory,
      c6C5PullbackData_top_optimalValue] using
      vectorSourceDynamics.target_invariant x T s hT hx hTs
  W_absolutelyContinuous := by
    intro x T s hT hx hTs
    simpa [c6C5PullbackData, c6C5PullbackData_top_trajectory] using
      vectorSourceDynamics.W_absolutelyContinuous x T s hT hx hTs
  W_nonnegative := by
    intro x T s hT hx hTs
    simpa [c6C5PullbackData, c6C5PullbackData_top_trajectory] using
      vectorSourceDynamics.W_nonnegative x T s hT hx hTs
  W_rightSlope := by
    intro x T u hT hx hu
    simpa [c6C5PullbackData, c6C5PullbackData_top_trajectory] using
      vectorSourceDynamics.W_rightSlope x T u hT hx hu
  W_lower_distance_bound := by
    intro x T s hT hx hTs
    simpa [c6C5PullbackData, c6C5PullbackData_top_trajectory,
      c6C5PullbackData_top_optimalValue] using
      vectorSourceDynamics.W_lower_distance_bound x T s hT hx hTs
  W_upper_distance_bound := by
    intro x T s hT hx hTs
    simpa [c6C5PullbackData, c6C5PullbackData_top_trajectory,
      c6C5PullbackData_top_optimalValue] using
      vectorSourceDynamics.W_upper_distance_bound x T s hT hx hTs
  ω_continuous := vectorSourceDynamics.ω_continuous
  ω_zero := vectorSourceDynamics.ω_zero
  ω_nonnegative := vectorSourceDynamics.ω_nonnegative
  ω_monotone_on_nonnegative := vectorSourceDynamics.ω_monotone_on_nonnegative
  value_distance_bound := by
    intro y t ht hy
    simpa [c6C5PullbackData, c6C5PullbackData_top_trajectory,
      c6C5PullbackData_top_optimalValue] using
      vectorSourceDynamics.value_distance_bound y t ht hy

/-- 24→26の実入口を、有限層の条件24-Aと同じ層別Dの頂点Eへ適用する。 -/
noncomputable def c6C5PullbackData_jointConclusion
    (x : VectorSourceState true) (T : ℝ) (hT : 0 ≤ T)
    (hx : x ∈ c6C5PullbackDynamics.alive) :=
  theorem24_to26_from_nonnegativeTimeData
    c6C5PullbackData c6C5PullbackDynamics x T hT hx

/-- 頂点のC6モデルが使う同じ状態・方策・費用を指定した27-A/27.6/27.7–27.10の
出力形。参照入力は元のベクトル例の入力で、状態は共通D/Eのtrajectoryである。 -/
def c6C5PullbackTheorem27Conclusion
    (x : VectorSourceState true) (T : ℝ) (hT : 0 ≤ T) : Prop :=
  (∀ t, T ≤ t →
    (¬ FeedbackPZS (c6C5PullbackData.admissible ⊤)
      futureLebesgueMeasure
      (fun π y a s => c6C5PullbackData.runningCost ⊤ π
        (c6C5PullbackData.trajectory ⊤ π y a s) s)
      (c6C5PullbackData.trajectory ⊤ c6C5PullbackDynamics.feedback x T t) t ↔
      0 < Tomabechi.Theorem27.residualDescentRateAlong
        (fun s y => c6C5PullbackDynamics.W y s)
        (fun s => c6C5PullbackData.trajectory ⊤
          c6C5PullbackDynamics.feedback x T s) t)) ∧
  (∀ᵐ t ∂futureLebesgueMeasure T,
    ∀ htt : T ≤ t,
      (¬ FeedbackPZS (c6C5PullbackData.admissible ⊤)
        futureLebesgueMeasure
        (fun π y a s => c6C5PullbackData.runningCost ⊤ π
          (c6C5PullbackData.trajectory ⊤ π y a s) s)
        (c6C5PullbackData.trajectory ⊤ c6C5PullbackDynamics.feedback x T t) t ↔
        0 < -inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
          (Tomabechi.Examples.Theorem27Op.GE
            ((c6C5PullbackDynamics.policyEquiv c6C5PullbackDynamics.feedback).action
              (⟨⟨t, hT.trans htt⟩,
                c6C5PullbackData.trajectory ⊤ c6C5PullbackDynamics.feedback x T t⟩) -
             Tomabechi.Examples.Theorem27.vectorSourceReferenceInput x T t)))) ∧
  (∀ᵐ t ∂futureLebesgueMeasure T,
    (¬ FeedbackPZS (c6C5PullbackData.admissible ⊤)
      futureLebesgueMeasure
      (fun π y a s => c6C5PullbackData.runningCost ⊤ π
        (c6C5PullbackData.trajectory ⊤ π y a s) s)
      (c6C5PullbackData.trajectory ⊤ c6C5PullbackDynamics.feedback x T t) t →
      c6C5PullbackDynamics.rate * c6C5PullbackDynamics.c₁ *
        Metric.infDist
          (c6C5PullbackData.trajectory ⊤ c6C5PullbackDynamics.feedback x T t)
          (theorem26ZeroValueTarget c6C5PullbackDynamics.alive
            (c6C5PullbackData.optimalValue ⊤) t) ^ 2 /
          (2 * |x 0| + 1) ≤
        ‖Tomabechi.Examples.Theorem27Op.u0E x T t -
          Tomabechi.Examples.Theorem27.vectorSourceReferenceInput x T t‖ ∧
      0 < ‖Tomabechi.Examples.Theorem27Op.u0E x T t -
        Tomabechi.Examples.Theorem27.vectorSourceReferenceInput x T t‖))

/-- 既存の27-A実入力・基準入力証明を、共通束データの頂点projectionへ移す。
sourceとC6のtrajectory/cost/value/admissibilityを同定して結論を移送する。 -/
theorem c6C5PullbackData_theorem27_kernel
    (x : VectorSourceState true) (T : ℝ) (hT : 0 ≤ T) :
    c6C5PullbackTheorem27Conclusion x T hT := by
  simpa [c6C5PullbackTheorem27Conclusion, c6C5PullbackData,
    c6C5PullbackDynamics, c6C5PullbackData_top_admissible,
    c6C5PullbackData_top_runningCost, c6C5PullbackData_top_trajectory,
    c6C5PullbackData_top_optimalValue] using
    Tomabechi.Examples.Theorem27.vectorSourceData_theorem27_kernel x T hT

/-- 同一の27結論を、有限層C1状態を持つ新しい共通Dの頂点で記述する。 -/
def c6LayeredTheorem27Conclusion
    (x : VectorSourceState true) (T : ℝ) (hT : 0 ≤ T) : Prop :=
  (∀ t, T ≤ t →
    (¬ FeedbackPZS (c6LayeredNonnegativeTimeData.admissible ⊤)
      futureLebesgueMeasure
      (fun π y a s => c6LayeredNonnegativeTimeData.runningCost ⊤ π
        (c6LayeredNonnegativeTimeData.trajectory ⊤ π y a s) s)
      (c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback x T t) t ↔
      0 < Tomabechi.Theorem27.residualDescentRateAlong
        (fun s y => c6LayeredDynamics.W y s)
        (fun s => c6LayeredNonnegativeTimeData.trajectory ⊤
          c6LayeredDynamics.feedback x T s) t)) ∧
  (∀ᵐ t ∂futureLebesgueMeasure T,
    ∀ htt : T ≤ t,
      (¬ FeedbackPZS (c6LayeredNonnegativeTimeData.admissible ⊤)
        futureLebesgueMeasure
        (fun π y a s => c6LayeredNonnegativeTimeData.runningCost ⊤ π
          (c6LayeredNonnegativeTimeData.trajectory ⊤ π y a s) s)
        (c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback x T t) t ↔
        0 < -inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
          (Tomabechi.Examples.Theorem27Op.GE
            ((c6LayeredDynamics.policyEquiv c6LayeredDynamics.feedback).action
              (⟨⟨t, hT.trans htt⟩,
                c6LayeredNonnegativeTimeData.trajectory ⊤
                  c6LayeredDynamics.feedback x T t⟩) -
             Tomabechi.Examples.Theorem27.vectorSourceReferenceInput x T t)))) ∧
  (∀ᵐ t ∂futureLebesgueMeasure T,
    (¬ FeedbackPZS (c6LayeredNonnegativeTimeData.admissible ⊤)
      futureLebesgueMeasure
      (fun π y a s => c6LayeredNonnegativeTimeData.runningCost ⊤ π
        (c6LayeredNonnegativeTimeData.trajectory ⊤ π y a s) s)
      (c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback x T t) t →
      c6LayeredDynamics.rate * c6LayeredDynamics.c₁ *
        Metric.infDist
          (c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback x T t)
          (theorem26ZeroValueTarget c6LayeredDynamics.alive
            (c6LayeredNonnegativeTimeData.optimalValue ⊤) t) ^ 2 /
          (2 * |x 0| + 1) ≤
        ‖Tomabechi.Examples.Theorem27Op.u0E x T t -
          Tomabechi.Examples.Theorem27.vectorSourceReferenceInput x T t‖ ∧
      0 < ‖Tomabechi.Examples.Theorem27Op.u0E x T t -
        Tomabechi.Examples.Theorem27.vectorSourceReferenceInput x T t‖))

/-- 27の運用出力を、同じ新L上24/26データの頂点projectionへ適用する。 -/
theorem c6LayeredData_theorem27_kernel
    (x : VectorSourceState true) (T : ℝ) (hT : 0 ≤ T) :
    c6LayeredTheorem27Conclusion x T hT := by
  simpa [c6LayeredTheorem27Conclusion,
    c6LayeredNonnegativeTimeData, c6LayeredTrajectory, c6LayeredRunningCost,
    c6LayeredAdmissible, c6LayeredOptimalValue, c6LayeredOptimalPolicy,
    c6LayeredDynamics, c6LayeredData_top_admissible,
    c6LayeredData_top_runningCost, c6LayeredData_top_trajectory,
    c6LayeredData_top_optimalValue, c6LayeredData_top_optimalPolicy,
    c6LayeredData_top_admissible_fun, c6LayeredAdmissible_top,
    c6LayeredOptimalValue_top] using
    Tomabechi.Examples.Theorem27.vectorSourceData_theorem27_kernel x T hT

/-- 現行C6の標準共通D。有限層はC1状態を持つ層別データを指す。 -/
abbrev c6CommonLayerData := c6LayeredNonnegativeTimeData

/-- 標準共通Dの頂点力学。 -/
abbrev c6CommonLayerDynamics := c6LayeredDynamics

abbrev c6CommonLayerData_all_finite_theorem24 := c6LayeredData_all_finite_theorem24

abbrev c6CommonLayerData_jointConclusion := c6LayeredData_jointConclusion

theorem c6CommonLayerData_theorem27_kernel
    (x : VectorSourceState true) (T : ℝ) (hT : 0 ≤ T) :
    c6LayeredTheorem27Conclusion x T hT :=
  c6LayeredData_theorem27_kernel x T hT

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.c6CommonLayerData_theorem27_kernel
#print axioms Tomabechi.Consistency.C6.c6LayeredData_all_finite_theorem24
#print axioms Tomabechi.Consistency.C6.c6LayeredData_jointConclusion
#print axioms Tomabechi.Consistency.C6.c6LayeredData_theorem27_kernel
