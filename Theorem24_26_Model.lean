import Theorem24_26

/-!
# A concrete scalar model for the Theorem 24 → 26 interface

This file develops a deliberately small finite-dimensional discounted control
model.  At the top level the state follows `x(t) = x₀ exp (-(t-T))`, the
running cost is `3 x²`, and the discount rate is `1`.  The intended value is
`x₀²`, so the zero-value target is `{0}` and `W(x) = x²` is an exact Lyapunov
certificate.  A separate lower-abstraction layer has constant running cost
`1`, which verifies condition 24-A there.

This is an explicit special model, not a derivation of the paper's hypotheses
from its general cognitive-control setup.  Its control space is a singleton,
so optimality is intentionally a no-choice special case; the feedback is still
an actual Borel Markov map and all theorem statements are checked with the
project's discounted-integral and PZS interfaces.
-/

namespace Tomabechi.Theorem24_26_Model

open MeasureTheory Set
open Tomabechi.Theorem24_26

abbrev Control : Type := PUnit
abbrev Feedback : Type := BorelMarkovFeedback ℝ Control

/-- The unique control action as a Borel Markov feedback. -/
def commonFeedback : Feedback :=
  ⟨fun _ => PUnit.unit, measurable_const⟩

theorem commonFeedback_measurable : Measurable commonFeedback.action :=
  commonFeedback.measurable_action

/-- Every Borel Markov feedback is admissible in this no-choice model. -/
def admissible (_π : Feedback) (_x : ℝ) (_T : ℝ) : Prop := True

/-- The global closed-loop flow for `ẋ = -x`. -/
noncomputable def flow (x : ℝ) (T s : ℝ) : ℝ :=
  x * Real.exp (T - s)

/-- Quadratic running cost, scaled to make the discounted value exactly `x²`. -/
def runningCost (x _s : ℝ) : ℝ := 3 * x ^ 2

/-- The theorem-26 discounted running cost along the closed-loop flow. -/
noncomputable def discountedIntegrand (x T s : ℝ) : ℝ :=
  theorem26DiscountWeight 1 T s * runningCost (flow x T s) s

/-- Top-level model value, specified by the closed-loop discounted integral. -/
noncomputable def value (x T : ℝ) : ℝ :=
  ∫ s, discountedIntegrand x T s ∂futureLebesgueMeasure T

/-- The lower abstraction has no zero-running-cost trajectory. -/
def lowerRunningCost (_x : Unit) (_s : ℝ) : ℝ := 1

abbrev LowerFeedback : Type := PUnit

def lowerAdmissible (_π : LowerFeedback) (_x : Unit) (_T : ℝ) : Prop := True

/-- The lower layer's (trivial) controlled trajectory, with its initial state
recorded explicitly for the theorem-24 interface. -/
def lowerTrajectory (_π : LowerFeedback) (x : Unit) (_T _s : ℝ) : Unit := x



theorem lower_condition24A (x : Unit) (T : ℝ) :
    ¬ (fun s => lowerRunningCost x s) =ᵐ[futureLebesgueMeasure T] 0 := by
  have hcondition := theorem24_condition24A_of_ae_strictlyPositive
    (fun _π _x _T s => lowerRunningCost x s)
    lowerAdmissible x T (by
      intro π hπ
      filter_upwards with s
      simp [lowerRunningCost])
  exact hcondition PUnit.unit trivial

/-- The future-discounted integrand is an exponential with rate `3`. -/
theorem discountedIntegrand_eq (x T s : ℝ) :
    discountedIntegrand x T s = 3 * x ^ 2 * Real.exp (-3 * (s - T)) := by
  rw [discountedIntegrand, theorem26DiscountWeight, runningCost, flow]
  rw [show T - s = -(s - T) by ring]
  rw [neg_one_mul]
  calc
    Real.exp (-(s - T)) * (3 * (x * Real.exp (-(s - T))) ^ 2) =
        3 * x ^ 2 * (Real.exp (-(s - T)) * Real.exp (-(s - T)) *
          Real.exp (-(s - T))) := by ring
    _ = 3 * x ^ 2 * Real.exp (-(s - T) + (-(s - T) + -(s - T))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring
    _ = 3 * x ^ 2 * Real.exp (-3 * (s - T)) := by
      congr 2
      ring

/-- Integrability of the concrete discounted cost on the future half-line. -/
theorem discountedIntegrand_integrable (x T : ℝ) :
    MeasureTheory.Integrable (discountedIntegrand x T)
      (futureLebesgueMeasure T) := by
  change MeasureTheory.Integrable (discountedIntegrand x T)
    (MeasureTheory.volume.restrict (Set.Ici T))
  have hbase : MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.exp (-3 * s)) (Set.Ioi T) :=
    integrableOn_exp_mul_Ioi (by norm_num) T
  have hbaseIci : MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.exp (-3 * s)) (Set.Ici T) :=
    integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.2 hbase
  have hscaled : MeasureTheory.IntegrableOn
      (fun s : ℝ => 3 * x ^ 2 * Real.exp (3 * T) * Real.exp (-3 * s))
      (Set.Ici T) := hbaseIci.const_mul _
  have heq : (fun s => discountedIntegrand x T s) =ᵐ[MeasureTheory.volume.restrict (Set.Ici T)]
      (fun s => 3 * x ^ 2 * Real.exp (3 * T) * Real.exp (-3 * s)) := by
    filter_upwards with s
    rw [discountedIntegrand_eq, show -3 * (s - T) = 3 * T + (-3 * s) by ring,
      Real.exp_add]
    ring
  exact hscaled.congr heq.symm

/-- The discounted integral is exactly the quadratic initial-state value. -/
theorem value_eq_sq (x T : ℝ) : value x T = x ^ 2 := by
  unfold value
  change (∫ s in Set.Ici T, discountedIntegrand x T s ∂MeasureTheory.volume) = x ^ 2
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hrewrite : (fun s : ℝ => discountedIntegrand x T s) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi T)]
      (fun s => (3 * x ^ 2 * Real.exp (3 * T)) * Real.exp (-3 * s)) := by
    filter_upwards with s
    rw [discountedIntegrand_eq, show -3 * (s - T) = 3 * T + (-3 * s) by ring,
      Real.exp_add]
    ring
  rw [MeasureTheory.integral_congr_ae hrewrite]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_exp_mul_Ioi (a := -3) (by norm_num) T]
  rw [show -Real.exp (-3 * T) / -3 = Real.exp (-3 * T) / 3 by ring]
  have hexp : Real.exp (3 * T) * Real.exp (-3 * T) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    3 * x ^ 2 * Real.exp (3 * T) * (Real.exp (-3 * T) / 3) =
        3 * x ^ 2 * (Real.exp (3 * T) * (Real.exp (-3 * T) / 3)) := by ring
    _ =
        3 * x ^ 2 * ((Real.exp (3 * T) * Real.exp (-3 * T)) / 3) := by ring
    _ = x ^ 2 := by rw [hexp]; ring

/-- Exponential moments under the future Lebesgue measure. -/
theorem future_exp_integral {c : ℝ} (hc : 0 < c) (T : ℝ) :
    (∫ s, Real.exp (-c * (s - T)) ∂futureLebesgueMeasure T) = c⁻¹ := by
  change (∫ s in Set.Ici T, Real.exp (-c * (s - T)) ∂MeasureTheory.volume) = c⁻¹
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hrewrite : (fun s : ℝ => Real.exp (-c * (s - T))) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi T)]
      (fun s => Real.exp (c * T) * Real.exp (-c * s)) := by
    filter_upwards with s
    rw [show -c * (s - T) = c * T + (-c * s) by ring, Real.exp_add]
  rw [MeasureTheory.integral_congr_ae hrewrite, MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi (a := -c) (by linarith) T]
  rw [show -Real.exp (-c * T) / -c = Real.exp (-c * T) / c by ring]
  have hexp : Real.exp (c * T) * Real.exp (-c * T) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    Real.exp (c * T) * (Real.exp (-c * T) / c) =
        (Real.exp (c * T) * Real.exp (-c * T)) / c := by ring
    _ = c⁻¹ := by rw [hexp]; simp [div_eq_mul_inv]

/-- The lower-level constant-cost model has attained optimal value `1`. -/
noncomputable def lowerValue (T : ℝ) : ℝ :=
  ∫ s, theorem26DiscountWeight 1 T s * lowerRunningCost () s
    ∂futureLebesgueMeasure T

noncomputable def lowerPolicyValue (_π : LowerFeedback) (_x : Unit) (T : ℝ) : ℝ :=
  lowerValue T

theorem lowerValue_eq_one (T : ℝ) : lowerValue T = 1 := by
  unfold lowerValue
  simp only [theorem26DiscountWeight, lowerRunningCost]
  simpa using future_exp_integral (c := 1) (by norm_num) T

theorem lower_policy_value_attained (x : Unit) (T : ℝ) :
    lowerAdmissible PUnit.unit x T ∧
      lowerPolicyValue PUnit.unit x T = lowerValue T ∧
      ∀ π, lowerAdmissible π x T → lowerValue T ≤ lowerPolicyValue π x T := by
  refine ⟨trivial, rfl, ?_⟩
  intro π _
  rfl

theorem lower_discounted_integrand_integrable (T : ℝ) :
    MeasureTheory.Integrable
      (fun s => theorem26DiscountWeight 1 T s * lowerRunningCost () s)
      (futureLebesgueMeasure T) := by
  change MeasureTheory.Integrable
    (fun s : ℝ => theorem26DiscountWeight 1 T s * (1 : ℝ))
    (futureLebesgueMeasure T)
  simp only [theorem26DiscountWeight, mul_one]
  change MeasureTheory.Integrable
    (fun s : ℝ => Real.exp (-1 * (s - T))) (futureLebesgueMeasure T)
  simp only [neg_one_mul]
  change MeasureTheory.Integrable (fun s : ℝ => Real.exp (-(s - T)))
    (MeasureTheory.volume.restrict (Set.Ici T))
  have hbase : MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.exp (-1 * s)) (Set.Ioi T) :=
    integrableOn_exp_mul_Ioi (by norm_num) T
  have hbaseIci : MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.exp (-1 * s)) (Set.Ici T) :=
    integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.2 hbase
  have hscaled : MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.exp T * Real.exp (-1 * s)) (Set.Ici T) :=
    hbaseIci.const_mul (Real.exp T)
  have heq : (fun s : ℝ => Real.exp (-(s - T))) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ici T)]
      (fun s => Real.exp T * Real.exp (-1 * s)) := by
    filter_upwards with s
    rw [show -(s - T) = T + (-1 * s) by ring, Real.exp_add]
  exact hscaled.congr heq.symm

/-- The zero-value set of the scalar model is the singleton equilibrium. -/
def zeroTarget (T : ℝ) : Set ℝ :=
  theorem26ZeroValueTarget Set.univ value T

theorem zeroTarget_eq_singleton (T : ℝ) : zeroTarget T = ({0} : Set ℝ) := by
  ext x
  simp [zeroTarget, theorem26ZeroValueTarget, value_eq_sq]

/-- Distance squared to the model target is exactly the quadratic Lyapunov value. -/
theorem infDist_zeroTarget_sq (x T : ℝ) :
    (Metric.infDist x (zeroTarget T)) ^ 2 = x ^ 2 := by
  rw [zeroTarget_eq_singleton, Metric.infDist_singleton]
  simp [Real.dist_eq, sq_abs]

/-- The closed-loop trajectory is a global solution of `ẋ = -x`. -/
theorem flow_hasDerivAt (x T s : ℝ) :
    HasDerivAt (flow x T) (-(flow x T s)) s := by
  have harg : HasDerivAt (fun u : ℝ => T - u) (-1) s := by
    convert (hasDerivAt_const s T).sub (hasDerivAt_id s) using 1
    · rfl
    · norm_num
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (T - u))
      (-Real.exp (T - s)) s := by
    convert (Real.hasDerivAt_exp (T - s)).comp s harg using 1
    · rfl
    · ring
  have h := (hasDerivAt_const s x).mul hexp
  change HasDerivAt (fun u => x * Real.exp (T - u))
    (-(x * Real.exp (T - s))) s
  convert h using 1 <;> ring

/-- State-time Lyapunov function for the scalar model. -/
def lyapunov (x t : ℝ) : ℝ := x ^ 2

/-- The Lyapunov function evaluated along the explicit closed-loop flow. -/
noncomputable def WAlong (x T s : ℝ) : ℝ := lyapunov (flow x T s) s

theorem WAlong_hasDerivAt (x T s : ℝ) :
    HasDerivAt (WAlong x T) (-2 * WAlong x T s) s := by
  have hflow := flow_hasDerivAt x T s
  have hsq := hflow.pow 2
  change HasDerivAt (fun u => (flow x T u) ^ 2)
    (-2 * (flow x T s) ^ 2) s
  convert hsq using 1 <;> simp only [Nat.cast_ofNat, pow_one] <;> ring

/-- All requirements of condition 26-A hold with `c₁=c₂=1`, `λ=2`, and
`W(x)=x²`. The value bound (26.C) holds with `ω(r)=r²`. -/
theorem model_satisfies_condition26A (x T s : ℝ) :
    ((Metric.infDist (flow x T s) (zeroTarget s)) ^ 2 = WAlong x T s) ∧
      (deriv (WAlong x T) s) = -2 * WAlong x T s ∧
      value (flow x T s) s =
        (Metric.infDist (flow x T s) (zeroTarget s)) ^ 2 := by
  have hderiv := (WAlong_hasDerivAt x T s).deriv
  have hvalue := value_eq_sq (flow x T s) s
  refine ⟨?_, hderiv, ?_⟩
  · simp [WAlong, lyapunov, infDist_zeroTarget_sq]
  · rw [hvalue, infDist_zeroTarget_sq]

/-- The closed-form flow has the semigroup property, so restarting the
common feedback at an intermediate state reproduces the same global orbit. -/
theorem flow_semigroup (x T s u : ℝ) :
    flow (flow x T s) s u = flow x T u := by
  change (x * Real.exp (T - s)) * Real.exp (s - u) =
    x * Real.exp (T - u)
  calc
    (x * Real.exp (T - s)) * Real.exp (s - u) =
        x * (Real.exp (T - s) * Real.exp (s - u)) := by ring
    _ = x * Real.exp ((T - s) + (s - u)) := by rw [← Real.exp_add]
    _ = x * Real.exp (T - u) := by congr 2 <;> ring

/-- Global existence, alive-set invariance, and forward invariance of the
zero-value target hold for the explicit flow. -/
theorem model_forward_complete_and_target_invariant (x T s : ℝ)
    (hx : x ∈ zeroTarget T) :
    flow x T s ∈ Set.univ ∧
      (∀ u, flow x T u ∈ Set.univ) ∧
      (∀ u, flow x T u ∈ zeroTarget u) := by
  have hx0 : x = 0 := by
    simpa [zeroTarget, theorem26ZeroValueTarget, value_eq_sq] using hx
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · intro u
    exact Set.mem_univ _
  · intro u
    rw [zeroTarget_eq_singleton]
    simp [flow, hx0]

/-- The running-value function supplied to the theorem-26 interface. -/
noncomputable def topRunningValue (_π : Feedback) (x : ℝ) (T s : ℝ) : ℝ :=
  runningCost (flow x T s) s



/-- The common feedback attains the optimal value, and every admissible
feedback has the same value in this model. -/
theorem commonFeedback_is_optimal (x T : ℝ) :
    admissible commonFeedback x T ∧
      value x T = discountedFeedbackValue (fun t => futureLebesgueMeasure t)
        (theorem26DiscountWeight 1) topRunningValue commonFeedback x T ∧
      ∀ π, admissible π x T →
        value x T ≤ discountedFeedbackValue (fun t => futureLebesgueMeasure t)
          (theorem26DiscountWeight 1) topRunningValue π x T := by
  refine ⟨trivial, ?_, ?_⟩
  · rfl
  · intro π _
    rfl

/-- Applying the existing theorem-26 interface to the concrete Borel Markov
feedback identifies PZS exactly with the model's zero state. -/
theorem model_PZS_iff_target (x T : ℝ) :
    FeedbackPZS admissible (fun t => futureLebesgueMeasure t)
      topRunningValue x T ↔ x ∈ zeroTarget T := by
  have hmodel := commonFeedback_is_optimal x T
  have htarget := feedbackPZS_iff_mem_theorem26ZeroValueTarget_borelMarkov
    (fun t => futureLebesgueMeasure t) 1 topRunningValue admissible
    commonFeedback Set.univ value x T
    (fun π _ => by
      filter_upwards with s
      exact mul_nonneg (by norm_num) (sq_nonneg (flow x T s)))
    (fun π _ => by
      change MeasureTheory.Integrable (discountedIntegrand x T)
        (futureLebesgueMeasure T)
      exact discountedIntegrand_integrable x T)
    hmodel.1 hmodel.2.1 hmodel.2.2 (Set.mem_univ x)
  simpa [zeroTarget] using htarget

/-- The complete discounted value identity and common-feedback optimality
used by (26.1), with attainment for every initial pair. -/
theorem top_value_attained_for_all_initial_pairs (x T : ℝ) :
    value x T = discountedFeedbackValue (fun t => futureLebesgueMeasure t)
        (theorem26DiscountWeight 1) topRunningValue commonFeedback x T ∧
      ∀ π, admissible π x T →
        value x T ≤ discountedFeedbackValue (fun t => futureLebesgueMeasure t)
          (theorem26DiscountWeight 1) topRunningValue π x T := by
  exact ⟨(commonFeedback_is_optimal x T).2.1,
    (commonFeedback_is_optimal x T).2.2⟩

/-- The lower-level model satisfies 24-A and has a positive attained value. -/
theorem lower_model_theorem24 (T : ℝ) :
    (∀ π, lowerAdmissible π () T →
      ¬ (fun s => lowerRunningCost () s) =ᵐ[futureLebesgueMeasure T] 0) ∧
      lowerPolicyValue PUnit.unit () T = lowerValue T ∧
      0 < lowerValue T := by
  have hoptimalIntegrable := lower_discounted_integrand_integrable T
  have hpositive := theorem24_positive_optimal_value_of_condition24A_ennreal
    lowerTrajectory (fun _ => lowerRunningCost) lowerAdmissible PUnit.unit () T 1
    (lowerValue T) (by intro π hπ; rfl) (by norm_num)
    (theorem26DiscountWeight_pos_ae 1 T)
    (by
      intro π hπ
      filter_upwards with s
      simp [lowerRunningCost])
    (by
      intro π hπ
      fun_prop [theorem26DiscountWeight, lowerTrajectory, lowerRunningCost])
    (by
      simpa [lowerTrajectory, lowerRunningCost] using hoptimalIntegrable)
    trivial
    (by
      unfold lowerValue
      rfl)
    (by
      intro π hπ
      have hrealCost : (∫ s, theorem26DiscountWeight 1 T s *
          lowerRunningCost (lowerTrajectory π () T s) s
            ∂futureLebesgueMeasure T) = lowerValue T := by
        unfold lowerValue
        simp [lowerTrajectory, lowerRunningCost]
      rw [← hrealCost]
      have hcostNonneg : 0 ≤ᵐ[futureLebesgueMeasure T]
          (fun s => theorem26DiscountWeight 1 T s *
            lowerRunningCost (lowerTrajectory π () T s) s) := by
        filter_upwards with s
        have hw : 0 ≤ theorem26DiscountWeight 1 T s := Real.exp_nonneg _
        have hv : 0 ≤ lowerRunningCost (lowerTrajectory π () T s) s := by
          norm_num [lowerRunningCost]
        exact mul_nonneg hw hv
      have hcostIdentity := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (by simpa [lowerTrajectory, lowerRunningCost] using hoptimalIntegrable)
        hcostNonneg
      exact hcostIdentity.le)
    (by
      intro π hπ
      exact lower_condition24A () T)
  refine ⟨?_, (lower_policy_value_attained () T).2.1, hpositive⟩
  · intro π hπ
    exact lower_condition24A () T

/-- The model satisfies the exact value, Lyapunov, and target relations in
condition 26-A for every initial pair and every future time. -/
theorem concrete_condition26A (x T s : ℝ) (hTs : T ≤ s) :
    s ∈ Set.univ ∧
      zeroTarget s = ({0} : Set ℝ) ∧
      IsClosed (zeroTarget s) ∧
      (zeroTarget s).Nonempty ∧
      (Metric.infDist (flow x T s) (zeroTarget s)) ^ 2 = WAlong x T s ∧
      deriv (WAlong x T) s ≤ -2 * WAlong x T s ∧
      value (flow x T s) s ≤ (Metric.infDist (flow x T s) (zeroTarget s)) ^ 2 := by
  have h26 := model_satisfies_condition26A x T s
  refine ⟨Set.mem_univ _, zeroTarget_eq_singleton s, ?_, ?_, h26.1, ?_, ?_⟩
  · rw [zeroTarget_eq_singleton]
    exact isClosed_singleton
  · rw [zeroTarget_eq_singleton]
    exact Set.singleton_nonempty 0
  · rw [h26.2.1]
  · exact le_of_eq h26.2.2

/-- All dynamic conclusions of theorem 26 for the scalar model: the quantitative
exponential estimates, optimal-value convergence, and the characterization of
zero Lyapunov residual by membership in the nonempty closed zero-value target.
The proof now invokes the Dini/right-slope version of the general theorem. -/
theorem model_theorem26_full_convergence (x T : ℝ) :
    (∀ s ≥ T,
      WAlong x T s ≤ WAlong x T T * Real.exp (-2 * (s - T)) ∧
        Metric.infDist (flow x T s) (zeroTarget s) ≤
          Real.sqrt (WAlong x T T) * Real.exp (-(2 / 2) * (s - T))) ∧
    Filter.Tendsto (fun s => value (flow x T s) s) Filter.atTop (nhds 0) ∧
    (∀ s ≥ T, WAlong x T s = 0 ↔ flow x T s ∈ zeroTarget s) := by
  have hglobal := theorem26_full_conditional_convergence_of_rightSlopeBound
    (fun u => flow x T u) Set.univ value (WAlong x T) (fun r => r ^ 2)
    1 1 2 T (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => Set.mem_univ _) (fun u _ => by
      change (zeroTarget u).Nonempty
      rw [zeroTarget_eq_singleton]
      exact Set.singleton_nonempty 0)
    (fun u _ => by
      change IsClosed (zeroTarget u)
      rw [zeroTarget_eq_singleton]
      exact isClosed_singleton)
    (fun u hu => by
      have hcont : Continuous (fun v : ℝ => (x * Real.exp (T - v)) ^ 2) := by
        fun_prop
      change ContinuousOn (fun v : ℝ => (x * Real.exp (T - v)) ^ 2)
        (Set.Icc T u)
      exact hcont.continuousOn)
    (fun _ _ => sq_nonneg _)
    (fun u hu v hv => by
      apply Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
        (WAlong x T) v (-2 * WAlong x T v) (-2 * WAlong x T v)
      · exact WAlong_hasDerivAt x T v
      · exact le_rfl)
    (fun u hu => by
      change 1 * (Metric.infDist (flow x T u)
        (zeroTarget u)) ^ 2 ≤ WAlong x T u
      rw [infDist_zeroTarget_sq]
      simp [WAlong, lyapunov])
    (fun u hu => by
      change WAlong x T u ≤ 1 *
        (Metric.infDist (flow x T u) (zeroTarget u)) ^ 2
      rw [infDist_zeroTarget_sq]
      simp [WAlong, lyapunov])
    (by fun_prop)
    (by norm_num)
    (fun u hu => by
      constructor
      · rw [value_eq_sq]
        positivity
      · change value (flow x T u) u ≤
          (Metric.infDist (flow x T u) (zeroTarget u)) ^ 2
        rw [value_eq_sq, infDist_zeroTarget_sq])
  rcases hglobal with ⟨_, hbounds, hvalueTendsto, hzeroiff⟩
  refine ⟨?_, hvalueTendsto, ?_⟩
  · intro u hu
    simpa [zeroTarget, div_one] using hbounds u hu
  · intro u hu
    simpa [zeroTarget] using hzeroiff u hu

/-- Pointwise form of theorem 26's quantitative exponential estimate for the
concrete scalar trajectory. -/
theorem model_theorem26_exponential_convergence (x T s : ℝ) (hTs : T ≤ s) :
    WAlong x T s ≤ WAlong x T T * Real.exp (-2 * (s - T)) ∧
      Metric.infDist (flow x T s) (zeroTarget s) ≤
        Real.sqrt (WAlong x T T) * Real.exp (-(2 / 2) * (s - T)) := by
  simpa using (model_theorem26_full_convergence x T).1 s hTs

/-- The two-layer abstraction order used to instantiate the nonnegative-time
general theorem: `false` is the lower layer and `true = ⊤` is the scalar top. -/
abbrev SourceAbstraction := Bool

abbrev SourceState : SourceAbstraction → Type
  | false => Unit
  | true => ℝ

abbrev SourceFeedback : SourceAbstraction → Type
  | false => PUnit
  | true => NonnegativeTimeBorelMarkovFeedback ℝ Control

def sourceFeedback0 : NonnegativeTimeBorelMarkovFeedback ℝ Control where
  action := fun _ => PUnit.unit
  measurable_action := measurable_const

noncomputable def sourceTrajectory : (a : SourceAbstraction) → SourceFeedback a →
    SourceState a → ℝ → ℝ → SourceState a
  | false, _, x, _, _ => x
  | true, _, x, T, s => flow x T s

def sourceRunningCost : (a : SourceAbstraction) → SourceFeedback a →
    SourceState a → ℝ → ℝ
  | false, _, _, _ => 1
  | true, _, x, _ => runningCost x 0

noncomputable def sourceOptimalValue : (a : SourceAbstraction) →
    SourceState a → ℝ → ℝ
  | false, _, T => lowerValue T
  | true, x, T => value x T

def sourceOptimalPolicy : (a : SourceAbstraction) →
    (x : SourceState a) → ℝ → SourceFeedback a
  | false, _, _ => PUnit.unit
  | true, _, _ => sourceFeedback0

def sourceAdmissible : (a : SourceAbstraction) → SourceFeedback a →
    SourceState a → ℝ → Prop
  | false, _, _, _ => True
  | true, _, _, _ => True

theorem source_lower_lintegral_eq (T : ℝ) :
    ENNReal.ofReal (lowerValue T) = ∫⁻ s,
      ENNReal.ofReal (theorem26DiscountWeight 1 T s * lowerRunningCost () s)
        ∂futureLebesgueMeasure T := by
  rw [lowerValue]
  apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
  · exact lower_discounted_integrand_integrable T
  · filter_upwards with s
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (by norm_num [lowerRunningCost])

theorem source_top_lintegral_eq (x T : ℝ) :
    ENNReal.ofReal (value x T) = ∫⁻ s,
      ENNReal.ofReal (theorem26DiscountWeight 1 T s *
        runningCost (flow x T s) s) ∂futureLebesgueMeasure T := by
  rw [value]
  apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
  · exact discountedIntegrand_integrable x T
  · filter_upwards with s
    apply mul_nonneg
    · exact (Real.exp_pos _).le
    · simp [runningCost]
      positivity

/-- Source-domain data for a two-layer instance: the lower layer has constant
positive cost, while the top layer is the explicit Borel-controlled scalar
flow from this file. -/
noncomputable def sourceData :
    Theorem24NonnegativeTimeData SourceState SourceFeedback where
  rho := 1
  rho_pos := by norm_num
  trajectory := sourceTrajectory
  runningCost := sourceRunningCost
  admissible := sourceAdmissible
  optimalValue := sourceOptimalValue
  optimalPolicy := sourceOptimalPolicy
  trajectory_initial := by
    intro a π x T hT hπ
    cases a with
    | false => rfl
    | true => simp [sourceTrajectory, flow]
  runningCost_nonnegative := by
    intro a π x t
    cases a with
    | false => norm_num [sourceRunningCost]
    | true => simp [sourceRunningCost, runningCost]; positivity
  measurable_cost := by
    intro a x T π hT hπ
    cases a with
    | false => fun_prop [sourceRunningCost, theorem26DiscountWeight]
    | true => fun_prop [sourceTrajectory, sourceRunningCost, runningCost,
        theorem26DiscountWeight, flow]
  optimal_cost_integrable := by
    intro a x T hT
    cases a with
    | false => exact lower_discounted_integrand_integrable T
    | true => exact discountedIntegrand_integrable x T
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
        simpa [sourceOptimalValue, sourceTrajectory, sourceRunningCost,
          sourceAdmissible, lowerRunningCost] using source_lower_lintegral_eq T
    | true =>
        apply le_of_eq
        simpa [sourceOptimalValue, sourceTrajectory, sourceRunningCost,
          sourceAdmissible, runningCost] using source_top_lintegral_eq x T
  condition24A := by
    intro a ha x T hT π hπ
    cases a with
    | false =>
        simpa [sourceRunningCost, sourceTrajectory, lowerRunningCost] using
          lower_condition24A () T
    | true => exact (lt_irrefl (⊤ : SourceAbstraction) ha).elim

local instance sourceTopPseudoMetric :
    PseudoMetricSpace (SourceState (⊤ : SourceAbstraction)) :=
  Real.pseudoMetricSpace

local instance sourceTopMeasurableSpace :
    MeasurableSpace (SourceState (⊤ : SourceAbstraction)) := by
  change MeasurableSpace ℝ
  infer_instance

local instance sourceTopBorelSpace :
    BorelSpace (SourceState (⊤ : SourceAbstraction)) := by
  change BorelSpace ℝ
  infer_instance

local instance sourceTopProductBorelSpace :
    BorelSpace (Set.Ici (0 : ℝ) × SourceState (⊤ : SourceAbstraction)) := by
  change BorelSpace (Set.Ici (0 : ℝ) × ℝ)
  infer_instance

theorem sourceNormedMetric_eq_real :
    SeminormedAddCommGroup.toPseudoMetricSpace (E := ℝ) = Real.pseudoMetricSpace := by
  apply PseudoMetricSpace.ext
  ext x y
  simp [Real.dist_eq]

theorem sourceData_target_eq (T : ℝ) :
    theorem26ZeroValueTarget Set.univ
      (sourceData.optimalValue (⊤ : SourceAbstraction)) T = zeroTarget T := by
  ext x
  simp [theorem26ZeroValueTarget, sourceData, sourceOptimalValue,
    value_eq_sq, zeroTarget]

noncomputable def sourceDynamics :
    Theorem26NonnegativeTimeDynamics sourceData Control where
  policyEquiv := Equiv.refl _
  feedback := sourceFeedback0
  alive := Set.univ
  feedback_attains_optimum := by
    intro x T hT hx
    have hEq : sourceOptimalPolicy (⊤ : SourceAbstraction) x T =
        sourceFeedback0 := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [← hEq]
      exact sourceData.optimal_policy_admissible (⊤ : SourceAbstraction) x T hT
    · rw [← hEq]
      exact sourceData.optimal_cost_integrable (⊤ : SourceAbstraction) x T hT
    · rw [← hEq]
      exact sourceData.optimal_value_attained (⊤ : SourceAbstraction) x T hT
  W := lyapunov
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
    rw [sourceData_target_eq, zeroTarget_eq_singleton]
    exact Set.singleton_nonempty 0
  target_closed := by
    intro T hT
    rw [sourceData_target_eq, zeroTarget_eq_singleton]
    exact isClosed_singleton
  target_invariant := by
    intro x T s hT hmem hTs
    rw [sourceData_target_eq] at hmem ⊢
    have hforward := model_forward_complete_and_target_invariant x T s hmem
    exact hforward.2.2 s
  W_absolutelyContinuous := by
    intro x T s hT hx hTs
    have hregular : ContDiffOn ℝ 1 (WAlong x T) (Set.uIcc T s) := by
      have hglobal : ContDiff ℝ 1 (WAlong x T) := by
        unfold WAlong lyapunov flow
        fun_prop
      exact hglobal.contDiffOn
    have hac := hregular.absolutelyContinuousOnInterval
    rw [sourceNormedMetric_eq_real] at hac
    change AbsolutelyContinuousOnInterval (WAlong x T) T s
    exact hac
  W_nonnegative := by
    intro x T s hT hx hTs
    simpa [sourceData, sourceTrajectory, lyapunov] using
      (sq_nonneg (flow x T s))
  W_rightSlope := by
    intro x T u hT hx hTu
    apply Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
      (WAlong x T) u (-2 * WAlong x T u) (-2 * WAlong x T u)
    · exact WAlong_hasDerivAt x T u
    · exact le_rfl
  W_lower_distance_bound := by
    intro x T s hT hx hTs
    rw [sourceData_target_eq s]
    change 1 * (Metric.infDist (flow x T s) (zeroTarget s)) ^ 2 ≤
      lyapunov (flow x T s) s
    rw [zeroTarget_eq_singleton, Metric.infDist_singleton]
    simp [lyapunov, Real.dist_eq, sq_abs]
  W_upper_distance_bound := by
    intro x T s hT hx hTs
    rw [sourceData_target_eq s]
    change lyapunov (flow x T s) s ≤
      1 * (Metric.infDist (flow x T s) (zeroTarget s)) ^ 2
    rw [zeroTarget_eq_singleton, Metric.infDist_singleton]
    simp [lyapunov, Real.dist_eq, sq_abs]
  ω_continuous := by fun_prop
  ω_zero := by norm_num
  ω_nonnegative := by intro r hr; positivity
  ω_monotone_on_nonnegative := by
    intro r₁ r₂ hr₁ hr₁₂
    nlinarith [sq_nonneg (r₂ - r₁)]
  value_distance_bound := by
    intro y t ht hy
    change 0 ≤ value y t ∧
      value y t ≤ (Metric.infDist y (zeroTarget t)) ^ 2
    rw [value_eq_sq, zeroTarget_eq_singleton, Metric.infDist_singleton]
    constructor
    · positivity
    · simp [Real.dist_eq, sq_abs]

/-- The explicit scalar model is now an instance of the general nonnegative-
time theorem-24-to-26 interface. This wrapper exposes the combined result at
each nonnegative initial pair. -/
theorem source_model_general_lower_positive (T : ℝ) (hT : 0 ≤ T) :
    0 < sourceData.optimalValue false PUnit.unit T := by
  have hgeneral := theorem24_to26_from_nonnegativeTimeData
    sourceData sourceDynamics (x := (0 : ℝ)) T hT (Set.mem_univ _)
  exact (hgeneral.1 false (by decide) PUnit.unit).1

theorem source_model_general_top_pzs (x T : ℝ) (hT : 0 ≤ T) :
      FeedbackPZS (sourceData.admissible true)
        futureLebesgueMeasure
        (fun π y t s => sourceData.runningCost true π
          (sourceData.trajectory true π y t s) s) x T ↔
      x ∈ theorem26ZeroValueTarget Set.univ
        (sourceData.optimalValue true) T := by
  have hgeneral := theorem24_to26_from_nonnegativeTimeData
    sourceData sourceDynamics x T hT (Set.mem_univ x)
  exact hgeneral.2.1

theorem source_model_general_exponential_decay (x T : ℝ) (hT : 0 ≤ T)
    (s : ℝ) (hs : T ≤ s) :
    sourceDynamics.W (sourceData.trajectory true sourceDynamics.feedback x T s) s ≤
        sourceDynamics.W x T * Real.exp (-sourceDynamics.rate * (s - T)) ∧
      Metric.infDist
          (sourceData.trajectory true sourceDynamics.feedback x T s)
          (theorem26ZeroValueTarget sourceDynamics.alive
            (sourceData.optimalValue true) s) ≤
        Real.sqrt (sourceDynamics.W x T / sourceDynamics.c₁) *
          Real.exp (-(sourceDynamics.rate / 2) * (s - T)) := by
  have hgeneral := theorem24_to26_from_nonnegativeTimeData
    sourceData sourceDynamics x T hT (Set.mem_univ x)
  exact hgeneral.2.2.1 s hs

end Tomabechi.Theorem24_26_Model
