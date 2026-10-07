import Tomabechi.Consistency.ConsistencyR2_PointReachability

/-!
# R3: 一つの基礎評価から作る1・4・20の候補

このファイルでは、既存入口を勝手に同一視せず、共通基礎評価を持つ再設計候補を別名で定義する。
箱内では定理1の評価と一致し、定理4・20の実効評価がどのように得られるかを式として証明する。
既存の定理4/20の入口へこの候補を接続する最適性・微分条件は別途必要である。
-/

noncomputable section

namespace Tomabechi.Consistency.R3

open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Examples.Theorem2
open MeasureTheory

/-- 1・4・20で共有する正の基礎評価。 -/
def commonBaseV0 (x : AgentState) (_t : ℝ) : ℝ := 1 + DA.potential x 0

/-- 定理4候補の非定数臨場感 `P=exp(-F)`。 -/
def commonBasePresenceP (x : AgentState) (_t : ℝ) : ℝ :=
  Real.exp (-(DA.potential x 0))

def commonBasePresenceQ (_x : AgentState) (_t : ℝ) : ℝ := 1

/-- 定理4候補の実効評価 `1+F-exp(-F)`。 -/
def commonBaseTheorem4Effective (x : AgentState) (_t : ℝ) : ℝ :=
  Tomabechi.Theorem4.effectivePotential (commonBaseV0 x 0)
    (commonBasePresenceP x 0) (commonBasePresenceQ x 0) 1

/-- 定理20の距離二乗 `D=(x₀-x₁)²`。 -/
def commonBaseD (x : AgentState) : ℝ := (x 0 - x 1) ^ 2

/-- 定理20候補の傾き `s(D)=-D`。 -/
def commonBaseSlope (x : AgentState) : ℝ := -commonBaseD x

/-- 定理20候補の正baselineつき実効評価。 -/
def commonBaseTheorem20Effective (x : AgentState) : ℝ :=
  commonBaseV0 x 0 - 1 * 1 * commonBaseSlope x

theorem commonBaseV0_eq_theorem1_on_box
    (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    commonBaseV0 x t = consensusV0 x t := by rfl

theorem commonBaseV0_eq_theorem20_candidate_on_box
    (x : AgentState) (hx : x ∈ box) :
    commonBaseV0 x 0 = 1 + 2 * commonBaseD x := by
  rw [commonBaseV0, sharedPotential_eq_coupling x hx 0]
  simp [commonBaseD, γ]

theorem commonBaseV0_positive (x : AgentState) (t : ℝ) :
    0 < commonBaseV0 x t := by
  rw [commonBaseV0]
  have hpot := consensusPresence_potential_nonneg x 0
  linarith

theorem commonBaseTheorem4Effective_formula (x : AgentState) (t : ℝ) :
    commonBaseTheorem4Effective x t =
      1 + DA.potential x 0 - Real.exp (-(DA.potential x 0)) := by
  simp [commonBaseTheorem4Effective, commonBaseV0, commonBasePresenceP,
    commonBasePresenceQ, Tomabechi.Theorem4.effectivePotential]

/-- The common-base Theorem 4 effective value is increasing in the underlying
nonnegative residual `F`; this is the scalar comparison needed for argmin transfer. -/
theorem commonBaseTheorem4Effective_monotone {a b : ℝ} (hab : a ≤ b) :
    1 + a - Real.exp (-a) ≤ 1 + b - Real.exp (-b) := by
  have hexp : Real.exp (-b) ≤ Real.exp (-a) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

theorem commonBaseTheorem4_bounds (x : AgentState) (t : ℝ) :
    DA.potential x 0 ≤ commonBaseTheorem4Effective x t ∧
      commonBaseTheorem4Effective x t ≤ 2 * DA.potential x 0 := by
  rw [commonBaseTheorem4Effective_formula]
  have hF := consensusPresence_potential_nonneg x 0
  have hexp_le : Real.exp (-(DA.potential x 0)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hone_sub : 1 - DA.potential x 0 ≤ Real.exp (-(DA.potential x 0)) := by
    have h := Real.add_one_le_exp (-(DA.potential x 0))
    linarith
  constructor <;> linarith

theorem commonBaseTheorem4_zero_iff (x : AgentState) (t : ℝ) :
    commonBaseTheorem4Effective x t = 0 ↔ DA.potential x 0 = 0 := by
  constructor
  · intro h
    have hbounds := commonBaseTheorem4_bounds x t
    apply le_antisymm
    · rw [h] at hbounds
      exact hbounds.1
    · exact consensusPresence_potential_nonneg x 0
  · intro h
    rw [commonBaseTheorem4Effective_formula, h]
    simp

/-- The zero-threshold TCZ of the shared-base Theorem 4 candidate is exactly
the existing shared zero-residual target inside the common reachability box. -/
theorem commonBaseTheorem4_weightedTCZ_eq_shared (t : ℝ) :
    Tomabechi.Theorem4.weightedTCZ box
      commonBaseV0 commonBasePresenceP commonBasePresenceQ 1 0 t =
        DA.sharedTCZ box t := by
  ext y
  change (y ∈ box ∧ Tomabechi.Theorem4.effectivePotential
      (commonBaseV0 y t) (commonBasePresenceP y t)
      (commonBasePresenceQ y t) 1 ≤ 0) ↔
    (y ∈ box ∧ DA.potential y t = 0)
  have heffective : Tomabechi.Theorem4.effectivePotential
      (commonBaseV0 y t) (commonBasePresenceP y t)
      (commonBasePresenceQ y t) 1 = commonBaseTheorem4Effective y t := by
    simp [commonBaseTheorem4Effective, commonBaseV0, commonBasePresenceP,
      commonBasePresenceQ, Tomabechi.Theorem4.effectivePotential]
  rw [heffective]
  constructor
  · rintro ⟨hy, hle⟩
    have hnonneg : 0 ≤ commonBaseTheorem4Effective y t :=
      le_trans (consensusPresence_potential_nonneg y 0)
        (commonBaseTheorem4_bounds y t).1
    have hzero : commonBaseTheorem4Effective y t = 0 := le_antisymm hle hnonneg
    have hF := (commonBaseTheorem4_zero_iff y t).mp hzero
    have htime : DA.potential y 0 = DA.potential y t := by
      rw [potential_eq ![0, 0] y 0, potential_eq ![0, 0] y t]
    exact ⟨hy, htime ▸ hF⟩
  · rintro ⟨hy, hF⟩
    have htime : DA.potential y 0 = DA.potential y t := by
      rw [potential_eq ![0, 0] y 0, potential_eq ![0, 0] y t]
    have hzero : DA.potential y 0 = 0 := htime.symm ▸ hF
    exact ⟨hy, le_of_eq ((commonBaseTheorem4_zero_iff y t).mpr hzero)⟩

/-- rate-3流に連鎖律を適用したときの候補散逸右辺を支える代数的不等式。 -/
theorem commonBaseTheorem4_rate3_dissipation_rhs_bound
    (x : AgentState) (t : ℝ) :
    -6 * DA.potential x 0 * (1 + Real.exp (-(DA.potential x 0))) ≤
      -3 * commonBaseTheorem4Effective x t := by
  have hF := consensusPresence_potential_nonneg x 0
  have hbounds := commonBaseTheorem4_bounds x t
  have hexp := Real.exp_pos (-(DA.potential x 0))
  nlinarith

/-- 共通基礎評価から作った定理4候補は、C1 rate-3流上で定量的に減衰する。 -/
theorem commonBaseTheorem4Effective_rate3_decay
    (x : AgentState) (hx : x ∈ box) (t₀ s : ℝ) (ht : t₀ ≤ s) :
    commonBaseTheorem4Effective (consensusOptimalFlow.flow t₀ x s) s ≤
      2 * commonBaseTheorem4Effective x t₀ * Real.exp (-6 * (s - t₀)) := by
  have hybox := consensusOptimalFlow_forward_invariant x hx t₀ s ht
  have hF : DA.potential (consensusOptimalFlow.flow t₀ x s) 0 =
      DA.potential x 0 * Real.exp (-6 * (s - t₀)) := by
    rw [sharedPotential_eq_coupling _ hybox 0, consensusOptimalFlow_gap,
      mul_pow, ← Real.exp_nat_mul]
    rw [sharedPotential_eq_coupling x hx 0]
    ring
  have hbounds := commonBaseTheorem4_bounds
    (consensusOptimalFlow.flow t₀ x s) s
  have hstart := commonBaseTheorem4_bounds x t₀
  calc
    commonBaseTheorem4Effective (consensusOptimalFlow.flow t₀ x s) s ≤
        2 * DA.potential (consensusOptimalFlow.flow t₀ x s) 0 := hbounds.2
    _ = 2 * DA.potential x 0 * Real.exp (-6 * (s - t₀)) := by rw [hF]; ring
    _ ≤ 2 * commonBaseTheorem4Effective x t₀ * Real.exp (-6 * (s - t₀)) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hstart.1 (by norm_num))
      exact le_of_lt (Real.exp_pos _)

/-- Finite-horizon cost built from the shared-base Theorem 4 candidate. -/
def commonBaseTheorem4FiniteHorizonCost (x : AgentState) (t₀ T : ℝ)
    (u : Tomabechi.Consistency.ConsistencyC1.C1GainSignal) : ENNReal :=
  ∫⁻ s, ENNReal.ofReal
    (commonBaseTheorem4Effective (controlledConsensusState x t₀ u s) s)
    ∂volume.restrict (Set.Icc t₀ (t₀ + T))

/-- The maximum gain minimizes the new shared-base Theorem 4 cost against every
measurable admissible gain on every positive finite horizon. -/
theorem commonBaseTheorem4_maxGain_argmin
    (x : AgentState) (hx : x ∈ box) (t₀ T : ℝ) (hT : 0 < T) :
    ∀ u : Tomabechi.Consistency.ConsistencyC1.C1GainSignal,
      commonBaseTheorem4FiniteHorizonCost x t₀ T c1MaxGainSignal ≤
        commonBaseTheorem4FiniteHorizonCost x t₀ T u := by
  intro u
  unfold commonBaseTheorem4FiniteHorizonCost
  apply MeasureTheory.lintegral_mono_ae
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards with s hs
  have hsq := Tomabechi.Consistency.ConsistencyC1.c1MaxGain_orbit_sq_le
    (halfDifference x) t₀ s u hs.1
  have hflowSq :
      (halfDifference (controlledConsensusState x t₀ c1MaxGainSignal s)) ^ 2 ≤
        (halfDifference (controlledConsensusState x t₀ u s)) ^ 2 := by
    rw [controlledConsensusState_halfDifference,
      controlledConsensusState_halfDifference]
    have hmax : c1ControlledOrbit (halfDifference x) t₀ c1MaxGainSignal s =
        halfDifference x * Real.exp (-(3 * (s - t₀))) := by
      simp [c1ControlledOrbit, c1MaxGain_accumulation]
    rw [hmax]
    exact hsq
  have hboxMax := controlledConsensusState_mem_box x hx t₀ s c1MaxGainSignal hs.1
  have hboxU := controlledConsensusState_mem_box x hx t₀ s u hs.1
  have hpot (v : AgentState) (hv : v ∈ box) :
      DA.potential v 0 = 8 * (halfDifference v) ^ 2 := by
    rw [sharedPotential_eq_coupling v hv 0]
    simp [γ, halfDifference]
    ring
  have hF := mul_le_mul_of_nonneg_left hflowSq (by norm_num : (0 : ℝ) ≤ 8)
  have hFmax := hpot (controlledConsensusState x t₀ c1MaxGainSignal s) hboxMax
  have hFu := hpot (controlledConsensusState x t₀ u s) hboxU
  have hresidual :
      DA.potential (controlledConsensusState x t₀ c1MaxGainSignal s) 0 ≤
        DA.potential (controlledConsensusState x t₀ u s) 0 := by
    rw [hFmax, hFu]
    exact hF
  have hreal := commonBaseTheorem4Effective_monotone hresidual
  rw [commonBaseTheorem4Effective_formula,
    commonBaseTheorem4Effective_formula]
  exact ENNReal.ofReal_le_ofReal hreal

theorem commonBaseTheorem20Effective_formula
    (x : AgentState) (hx : x ∈ box) :
    commonBaseTheorem20Effective x = 1 + 3 * commonBaseD x := by
  rw [commonBaseTheorem20Effective, commonBaseV0_eq_theorem20_candidate_on_box x hx,
    commonBaseSlope]
  dsimp [commonBaseD]
  ring

theorem commonBaseD_eq_halfDifference_sq (x : AgentState) :
    commonBaseD x = 4 * (halfDifference x) ^ 2 := by
  simp [commonBaseD, halfDifference]
  ring

/-- Finite-horizon cost obtained by integrating the shared-base Theorem 20
candidate effective value along any admissible two-agent gain signal. -/
def commonBaseTheorem20FiniteHorizonCost (x : AgentState) (t₀ T : ℝ)
    (u : C1GainSignal) : ENNReal :=
  ∫⁻ s, ENNReal.ofReal
    (commonBaseTheorem20Effective (controlledConsensusState x t₀ u s))
    ∂volume.restrict (Set.Icc t₀ (t₀ + T))

/-- The same maximum gain minimizes the new Theorem 20 candidate cost on every
positive finite horizon: the candidate is an increasing affine function of
the disagreement square minimized pointwise by the rate-3 feedback. -/
theorem commonBaseTheorem20_maxGain_argmin
    (x : AgentState) (hx : x ∈ box) (t₀ T : ℝ) (hT : 0 < T) :
    ∀ u : C1GainSignal,
      commonBaseTheorem20FiniteHorizonCost x t₀ T c1MaxGainSignal ≤
        commonBaseTheorem20FiniteHorizonCost x t₀ T u := by
  intro u
  unfold commonBaseTheorem20FiniteHorizonCost
  apply MeasureTheory.lintegral_mono_ae
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards with s hs
  have hsq := Tomabechi.Consistency.ConsistencyC1.c1MaxGain_orbit_sq_le
    (halfDifference x) t₀ s u hs.1
  have hmax : c1ControlledOrbit (halfDifference x) t₀ c1MaxGainSignal s =
      halfDifference x * Real.exp (-(3 * (s - t₀))) := by
    simp [c1ControlledOrbit, c1MaxGain_accumulation]
  have hD :
      commonBaseD (controlledConsensusState x t₀ c1MaxGainSignal s) ≤
        commonBaseD (controlledConsensusState x t₀ u s) := by
    calc
      commonBaseD (controlledConsensusState x t₀ c1MaxGainSignal s) =
          4 * (c1ControlledOrbit (halfDifference x) t₀ c1MaxGainSignal s) ^ 2 := by
        rw [commonBaseD_eq_halfDifference_sq, controlledConsensusState_halfDifference]
      _ ≤ 4 * (c1ControlledOrbit (halfDifference x) t₀ u s) ^ 2 :=
        mul_le_mul_of_nonneg_left (by rw [hmax]; exact hsq) (by norm_num)
      _ = commonBaseD (controlledConsensusState x t₀ u s) := by
        rw [← controlledConsensusState_halfDifference, ← commonBaseD_eq_halfDifference_sq]
  have hboxMax := controlledConsensusState_mem_box x hx t₀ s c1MaxGainSignal hs.1
  have hboxU := controlledConsensusState_mem_box x hx t₀ s u hs.1
  have hreal :
      commonBaseTheorem20Effective
          (controlledConsensusState x t₀ c1MaxGainSignal s) ≤
        commonBaseTheorem20Effective (controlledConsensusState x t₀ u s) := by
    rw [commonBaseTheorem20Effective_formula _ hboxMax,
      commonBaseTheorem20Effective_formula _ hboxU]
    nlinarith
  exact ENNReal.ofReal_le_ofReal hreal

theorem commonBaseTheorem20_minimum_shift
    (x : AgentState) (hx : x ∈ box) :
    commonBaseTheorem20Effective x - 1 = 3 * commonBaseD x := by
  rw [commonBaseTheorem20Effective_formula x hx]
  ring

/-- Theorem 20's shared-candidate excess is exactly twelve times the
transported Euclidean symbol distance. This identifies the candidate's
zero set and quantitative scale with the distance used by the existing
Euclidean entry. -/
theorem commonBaseTheorem20_excess_eq_euclidean_distance
    (x : AgentState) (hx : x ∈ box) :
    commonBaseTheorem20Effective x - 1 =
      12 * c1EuclideanSymbolDistance (WithLp.toLp 2 x) := by
  rw [commonBaseTheorem20_minimum_shift x hx,
    c1EuclideanSymbolDistance_eq_coordinates]
  have hcoords : c1EuclideanCoordinates (WithLp.toLp 2 x) = x :=
    c1EuclideanCoordinates_toLp x
  rw [hcoords]
  simp [commonBaseD, c1SymbolDistance]
  ring

/-- Inside the invariant box, the sublevel set at the candidate's minimum is
exactly the transported symbolic consensus target from Theorem 20. -/
theorem commonBaseTheorem20_minimum_sublevel_iff_symbol_target
    (x : AgentState) (hx : x ∈ box) :
    commonBaseTheorem20Effective x - 1 ≤ 0 ↔
      WithLp.toLp 2 x ∈ c1EuclideanSymbolTarget := by
  rw [commonBaseTheorem20_excess_eq_euclidean_distance x hx]
  constructor
  · intro h
    have hnonneg := c1EuclideanSymbolDistance_nonneg (WithLp.toLp 2 x)
    have hzero : c1EuclideanSymbolDistance (WithLp.toLp 2 x) = 0 := by
      nlinarith
    exact (c1EuclideanSymbolDistance_zero_iff _).mp hzero
  · intro h
    have hzero := (c1EuclideanSymbolDistance_zero_iff _).mpr h
    rw [hzero]
    norm_num

/-- 定理20候補の実効評価は、rate-3流上で最小値からの差が正確に率6で減衰する。 -/
theorem commonBaseTheorem20Effective_excess_rate3_decay
    (x : AgentState) (hx : x ∈ box) (t₀ s : ℝ) (ht : t₀ ≤ s) :
    commonBaseTheorem20Effective (consensusOptimalFlow.flow t₀ x s) - 1 =
      (commonBaseTheorem20Effective x - 1) * Real.exp (-6 * (s - t₀)) := by
  have hybox := consensusOptimalFlow_forward_invariant x hx t₀ s ht
  rw [commonBaseTheorem20Effective_formula _ hybox,
    commonBaseTheorem20Effective_formula x hx]
  unfold commonBaseD
  rw [consensusOptimalFlow_gap, mul_pow, ← Real.exp_nat_mul]
  ring

/-- 新しい共有評価の代数的契約。これは原文条件の追加証明ではなく、1/4/20入口へ接続する候補データ。 -/
structure C1CommonBaseContract where
  V0 : AgentState → ℝ → ℝ
  V0_eq_shared : ∀ x t, V0 x t = commonBaseV0 x t
  theorem1_matches : ∀ x ∈ box, ∀ t, V0 x t = consensusV0 x t
  theorem4_effective : ∀ x t,
    Tomabechi.Theorem4.effectivePotential (V0 x t)
      (commonBasePresenceP x t) (commonBasePresenceQ x t) 1 =
        commonBaseTheorem4Effective x t
  theorem20_box_value : ∀ x ∈ box,
    V0 x 0 = 1 + 2 * commonBaseD x

def commonBaseContract : C1CommonBaseContract where
  V0 := commonBaseV0
  V0_eq_shared := by intro x t; rfl
  theorem1_matches := by intro x hx t; exact commonBaseV0_eq_theorem1_on_box x hx t
  theorem4_effective := by intro x t; rfl
  theorem20_box_value := by intro x hx; exact commonBaseV0_eq_theorem20_candidate_on_box x hx

end Tomabechi.Consistency.R3
