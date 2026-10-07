import Tomabechi.Consistency.ConsistencyC6_ActuatorInputs

/-!
# C6：頂点feedbackのCarathéodory解の一意性

全初期対で、絶対連続な競合解を同じ頂点軌道へ同定する。
再始動等式だけから一意性を推測せず、半径の有界ゲイン一意性と位相の積分式を使う。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Examples.Theorem27Op
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Theorem24_26
open MeasureTheory

/-- 実際の最大feedbackの閉ループ場。自然半径減衰と入力が各1/2を担う。 -/
def c6TopClosedField (y : C6TopState) : C6TopState :=
  (-y 0) • e0 + omg • e1

/-- 固定した場は、同じMの実Markov feedbackと自然ドリフトの和である。
軌道に限定せず、非負時刻の全状態で同定する。 -/
theorem commonModel_topClosedField_binding (t : Set.Ici (0 : ℝ)) (y : C6TopState) :
    c6TopNaturalDrift y + GE
      ((commonModel.dynamics.policyEquiv commonModel.dynamics.feedback).action (t, y)) =
      c6TopClosedField y := by
  change (-mu * y 0) • e0 + GE
    ((-(1 / 2 : ℝ) * y 0) • e0 + (3 / 2 : ℝ) • e1) = _
  ext i
  fin_cases i <;> simp [GE, c6TopClosedField, mu, omg, e0, e1] <;> ring

/-- 全状態上の固定したfeedback場の競合解は、同じMの頂点軌道に一致する。 -/
theorem commonModel_topPath_unique
    (x : C6TopState) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (y : ℝ → C6TopState) (hyAC : AbsolutelyContinuousOnInterval y a b)
    (hyInitial : y a = x)
    (hyODE : ∀ᵐ t ∂volume.restrict (Set.Icc a b), HasDerivAt y (c6TopClosedField (y t)) t) :
    y b = commonModel.topPath x a b := by
  let proj (i : Fin 2) : C6TopState →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i
  have hac (i : Fin 2) : AbsolutelyContinuousOnInterval (fun t => y t i) a b :=
    (proj i).lipschitz.comp_absolutelyContinuousOnInterval hyAC
  have hode (i : Fin 2) : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      HasDerivAt (fun s => y s i) ((c6TopClosedField (y t)) i) t := by
    filter_upwards [hyODE] with t ht
    exact (proj i).hasFDerivAt.comp_hasDerivAt t ht
  have hrad : y b 0 = c1ControlledState 0 (x 0) a c6UnitGainSignal b := by
    apply c1ControlledState_unique_on_interval 0 (x 0) a b c6UnitGainSignal
      (fun t => y t 0) hab (hac 0)
    · rw [hyInitial]
    · filter_upwards [hode 0] with t ht
      simpa [c6TopClosedField, c6UnitGainSignal, e0_apply0, e1_apply0] using ht
  have hphase : y b 1 = x 1 + omg * (b - a) := by
    have hd : (fun t => deriv (fun s => y s 1) t) =ᵐ[volume.restrict (Set.uIcc a b)]
        (fun _ => omg) := by
      rw [Set.uIcc_of_le hab]
      filter_upwards [hode 1] with t ht
      simpa [c6TopClosedField, e0_apply1, e1_apply1] using ht.deriv
    have hint : (∫ t in a..b, deriv (fun s => y s 1) t) = ∫ _t in a..b, omg :=
      intervalIntegral.integral_congr_ae_restrict
        (ae_restrict_of_ae_restrict_of_subset Set.uIoc_subset_uIcc hd)
    rw [(hac 1).integral_deriv_eq_sub, intervalIntegral.integral_const] at hint
    rw [hyInitial] at hint
    simp only [smul_eq_mul] at hint
    linarith
  change y b = c6TopPath x a b
  rw [c6TopPath_eq_flow x a b ha hab]
  ext i
  fin_cases i
  · change y b 0 = flowE x a b 0
    rw [flowE_0]
    simpa [c1ControlledState, c1ControlledOrbit, c1AccumulatedGain,
      c6UnitGainSignal, intervalIntegral.integral_const,
      Tomabechi.Theorem24_26_Model.flow] using hrad
  · change y b 1 = flowE x a b 1
    rw [flowE_1]
    exact hphase

open Tomabechi.Examples.Theorem27
open Tomabechi.Examples.Theorem26_27ControlClasses

/-- 頂点の全有界可測ゲインをC1の積分一意性核へ送る。自然減衰1/2を含む。 -/
def c6TopGainSignal (k : BoundedMeasurableGainSignal) : C1GainSignal :=
  ⟨fun t => 1 / 2 + k.1 t, measurable_const.add k.2.1, fun t => by
    have hk := k.2.2 t
    constructor <;> linarith⟩

theorem c6TopGainSignal_accumulated (k : BoundedMeasurableGainSignal) (a b : ℝ) :
    c1AccumulatedGain (c6TopGainSignal k) a b =
      (1 / 2) * (b - a) + measurableAccumulatedGain k a b := by
  unfold c1AccumulatedGain c6TopGainSignal measurableAccumulatedGain
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (boundedMeasurableGain_intervalIntegrable k a b)]
  simp [mul_comm]

/-- 全許容ゲインの固定した自然場と実入力の和。 -/
def c6TopGainField (k : BoundedMeasurableGainSignal) (t : ℝ) (y : C6TopState) : C6TopState :=
  (-(1 / 2 + k.1 t) * y 0) • e0 + omg • e1

/-- 最大feedbackへ限定しない、全有界可測ゲインのCarathéodory解一意性。 -/
theorem c6TopGainOrbit_unique
    (k : BoundedMeasurableGainSignal) (x : C6TopState) (a b : ℝ)
    (hab : a ≤ b) (y : ℝ → C6TopState)
    (hyAC : AbsolutelyContinuousOnInterval y a b) (hyInitial : y a = x)
    (hyODE : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      HasDerivAt y (c6TopGainField k t (y t)) t) :
    y b = measurableGainVectorOrbit (x 0) (x 1) a b k := by
  let proj (i : Fin 2) : C6TopState →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i
  have hac (i : Fin 2) : AbsolutelyContinuousOnInterval (fun t => y t i) a b :=
    (proj i).lipschitz.comp_absolutelyContinuousOnInterval hyAC
  have hode (i : Fin 2) : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      HasDerivAt (fun s => y s i) ((c6TopGainField k t (y t)) i) t := by
    filter_upwards [hyODE] with t ht
    exact (proj i).hasFDerivAt.comp_hasDerivAt t ht
  have hrad : y b 0 = c1ControlledState 0 (x 0) a (c6TopGainSignal k) b := by
    apply c1ControlledState_unique_on_interval 0 (x 0) a b (c6TopGainSignal k)
      (fun t => y t 0) hab (hac 0)
    · rw [hyInitial]
    · filter_upwards [hode 0] with t ht
      simpa [c6TopGainField, c6TopGainSignal, e0_apply0, e1_apply0] using ht
  have hphase : y b 1 = x 1 + omg * (b - a) := by
    have hd : (fun t => deriv (fun s => y s 1) t) =ᵐ[volume.restrict (Set.uIcc a b)]
        (fun _ => omg) := by
      rw [Set.uIcc_of_le hab]
      filter_upwards [hode 1] with t ht
      simpa [c6TopGainField, e0_apply1, e1_apply1] using ht.deriv
    have hint : (∫ t in a..b, deriv (fun s => y s 1) t) = ∫ _t in a..b, omg :=
      intervalIntegral.integral_congr_ae_restrict
        (ae_restrict_of_ae_restrict_of_subset Set.uIoc_subset_uIcc hd)
    rw [(hac 1).integral_deriv_eq_sub, intervalIntegral.integral_const] at hint
    rw [hyInitial] at hint
    simp only [smul_eq_mul] at hint
    linarith
  ext i
  fin_cases i
  · change y b 0 = (measurableGainVectorOrbit (x 0) (x 1) a b k) 0
    simpa [c1ControlledState, c1ControlledOrbit, c6TopGainSignal_accumulated,
      measurableGainVectorOrbit, Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit,
      e0_apply0, e1_apply0] using hrad
  · change y b 1 = (measurableGainVectorOrbit (x 0) (x 1) a b k) 1
    simpa [measurableGainVectorOrbit, omg, e0_apply1, e1_apply1] using hphase

/-- 同じMの任意頂点方策の実軌道は、選んだ有界可測ゲインの全状態解である。 -/
theorem commonModel_topControl_solution (π : C6LayeredPolicy ⊤) (x : C6TopState) (a b : ℝ) :
    commonModel.data.trajectory ⊤ π x a b =
      measurableGainVectorOrbit (x 0) (x 1) a b (selectedMeasurableVectorGain π) := rfl

/-- 許容方策の全非負時刻/全状態で、ODE場が実Markov入力と一致する。 -/
theorem commonModel_topControl_field (π : C6LayeredPolicy ⊤) (x : C6TopState) (a : ℝ)
    (hπ : commonModel.data.admissible ⊤ π x a) (t : Set.Ici (0 : ℝ)) (y : C6TopState) :
    c6TopNaturalDrift y + GE (π.action (t, y)) =
      c6TopGainField (selectedMeasurableVectorGain π) t.1 y := by
  rw [selectedMeasurableVectorGain_spec π hπ t y]
  ext i
  fin_cases i <;> simp [c6TopNaturalDrift, GE, measurableGainVectorPolicy,
    c6TopGainField, mu, omg, e0_apply0, e1_apply0, e0_apply1, e1_apply1] <;> ring

/-- 同じMの全頂点方策の競合解を実D軌道へ同定する。 -/
theorem commonModel_topControl_unique (π : C6LayeredPolicy ⊤) (x : C6TopState) (a b : ℝ)
    (hab : a ≤ b) (y : ℝ → C6TopState)
    (hyAC : AbsolutelyContinuousOnInterval y a b) (hyInitial : y a = x)
    (hyODE : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      HasDerivAt y (c6TopGainField (selectedMeasurableVectorGain π) t (y t)) t) :
    y b = commonModel.data.trajectory ⊤ π x a b :=
  c6TopGainOrbit_unique (selectedMeasurableVectorGain π) x a b hab y hyAC hyInitial hyODE

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.commonModel_topPath_unique

#print axioms Tomabechi.Consistency.C6.commonModel_topControl_unique
