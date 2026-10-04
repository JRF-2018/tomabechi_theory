import Theorem24_26_Model

/-!
# A two-action control model for the Theorem 24 → 26 interface

Unlike `Theorem24_26_Model`, this model has two control actions with different
closed-loop dynamics. The admissible Borel Markov feedbacks are restricted to
the two constant policies: action `true` gives `x' = -x`, while action `false`
gives `x' = 0`. Both use the same running cost `3 x²` and discount rate `1`.
Thus the respective values are `x₀²` and `3 x₀²`; the first policy is optimal,
and the optimal zero-value target is `{0}`. This verifies the theorem interfaces
in a two-policy model, but does not derive the paper's hypotheses for arbitrary
feedback controls or from a cognitive-control model.
-/

namespace Tomabechi.Theorem24_26_ControlledModel

open MeasureTheory Set
open Tomabechi.Theorem24_26
open Tomabechi.Theorem24_26_Model

abbrev Control : Type := Bool
abbrev Feedback : Type := BorelMarkovFeedback ℝ Control

/-- The two control actions select the linear drifts `-x` and `0`. -/
def dynamics (x : ℝ) (u : Control) : ℝ := if u then -x else 0

def optimalFeedback : Feedback := ⟨fun _ => true, measurable_const⟩
def zeroDriftFeedback : Feedback := ⟨fun _ => false, measurable_const⟩

def admissible (π : Feedback) (_x : ℝ) (_T : ℝ) : Prop :=
  (∀ t y, π.action (t, y) = true) ∨ (∀ t y, π.action (t, y) = false)

theorem optimalFeedback_admissible (x T : ℝ) : admissible optimalFeedback x T := by
  left
  intro t y
  rfl

theorem zeroDriftFeedback_admissible (x T : ℝ) : admissible zeroDriftFeedback x T := by
  right
  intro t y
  rfl

/-- The explicit closed-loop trajectory associated with a feedback. -/
noncomputable def trajectory (π : Feedback) (x T s : ℝ) : ℝ :=
  if π.action (T, x) then flow x T s else x

theorem trajectory_eq_flow_of_true (π : Feedback) (x T s : ℝ)
    (hπ : ∀ t y, π.action (t, y) = true) :
    trajectory π x T s = flow x T s := by
  simp [trajectory, hπ]

theorem trajectory_eq_const_of_false (π : Feedback) (x T s : ℝ)
    (hπ : ∀ t y, π.action (t, y) = false) :
    trajectory π x T s = x := by
  simp [trajectory, hπ]

/-- Both actions share the nonnegative running cost `3 x²`; their trajectories
are the part of the model affected by control. -/
def runningCost (_π : Feedback) (x _T _s : ℝ) : ℝ := 3 * x ^ 2

noncomputable def discountedIntegrand (π : Feedback) (x T s : ℝ) : ℝ :=
  theorem26DiscountWeight 1 T s *
    runningCost π (trajectory π x T s) T s

noncomputable def policyValue (π : Feedback) (x T : ℝ) : ℝ :=
  ∫ s, discountedIntegrand π x T s ∂futureLebesgueMeasure T

theorem discountedIntegrand_eq_of_true (π : Feedback) (x T s : ℝ)
    (hπ : ∀ t y, π.action (t, y) = true) :
    discountedIntegrand π x T s =
      Tomabechi.Theorem24_26_Model.discountedIntegrand x T s := by
  rw [discountedIntegrand, trajectory_eq_flow_of_true π x T s hπ,
    runningCost, Tomabechi.Theorem24_26_Model.discountedIntegrand,
    Tomabechi.Theorem24_26_Model.runningCost]

theorem discountedIntegrand_eq_of_false (π : Feedback) (x T s : ℝ)
    (hπ : ∀ t y, π.action (t, y) = false) :
    discountedIntegrand π x T s =
      3 * x ^ 2 * Real.exp (-(s - T)) := by
  rw [discountedIntegrand, trajectory_eq_const_of_false π x T s hπ,
    runningCost, theorem26DiscountWeight]
  ring_nf

theorem exp_future_integrable (x T : ℝ) :
    Integrable (fun s : ℝ => 3 * x ^ 2 * Real.exp (-(s - T)))
      (futureLebesgueMeasure T) := by
  change Integrable (fun s : ℝ => 3 * x ^ 2 * Real.exp (-(s - T)))
    (volume.restrict (Set.Ici T))
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-1 * s)) (Set.Ioi T) :=
    integrableOn_exp_mul_Ioi (by norm_num) T
  have hbaseIci : IntegrableOn (fun s : ℝ => Real.exp (-1 * s)) (Set.Ici T) :=
    integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.2 hbase
  have hscaled : IntegrableOn
      (fun s : ℝ => 3 * x ^ 2 * Real.exp T * Real.exp (-1 * s)) (Set.Ici T) :=
    hbaseIci.const_mul _
  have heq : (fun s : ℝ => 3 * x ^ 2 * Real.exp (-(s - T))) =ᵐ[volume.restrict (Set.Ici T)]
      (fun s => 3 * x ^ 2 * Real.exp T * Real.exp (-1 * s)) := by
    filter_upwards with s
    rw [show -(s - T) = T + (-s) by ring, Real.exp_add]
    ring_nf
  exact hscaled.congr heq.symm

theorem policyIntegrand_integrable (π : Feedback) (x T : ℝ)
    (hπ : admissible π x T) :
    Integrable (discountedIntegrand π x T) (futureLebesgueMeasure T) := by
  rcases hπ with htrue | hfalse
  · have heq : discountedIntegrand π x T =ᵐ[futureLebesgueMeasure T]
        Tomabechi.Theorem24_26_Model.discountedIntegrand x T := by
      filter_upwards with s
      exact discountedIntegrand_eq_of_true π x T s htrue
    exact (discountedIntegrand_integrable x T).congr heq.symm
  · have heq : discountedIntegrand π x T =ᵐ[futureLebesgueMeasure T]
        (fun s => 3 * x ^ 2 * Real.exp (-(s - T))) := by
      filter_upwards with s
      exact discountedIntegrand_eq_of_false π x T s hfalse
    exact (exp_future_integrable x T).congr heq.symm

theorem policyValue_eq_sq_of_true (π : Feedback) (x T : ℝ)
    (hπ : ∀ t y, π.action (t, y) = true) :
    policyValue π x T = x ^ 2 := by
  unfold policyValue
  have heq : discountedIntegrand π x T =ᵐ[futureLebesgueMeasure T]
      Tomabechi.Theorem24_26_Model.discountedIntegrand x T := by
    filter_upwards with s
    exact discountedIntegrand_eq_of_true π x T s hπ
  rw [MeasureTheory.integral_congr_ae heq]
  exact value_eq_sq x T

theorem policyValue_eq_three_sq_of_false (π : Feedback) (x T : ℝ)
    (hπ : ∀ t y, π.action (t, y) = false) :
    policyValue π x T = 3 * x ^ 2 := by
  unfold policyValue
  have heq : discountedIntegrand π x T =ᵐ[futureLebesgueMeasure T]
      (fun s => 3 * x ^ 2 * Real.exp (-(s - T))) := by
    filter_upwards with s
    exact discountedIntegrand_eq_of_false π x T s hπ
  rw [MeasureTheory.integral_congr_ae heq]
  rw [MeasureTheory.integral_const_mul]
  have hexp :
      (∫ s, Real.exp (-(s - T)) ∂futureLebesgueMeasure T) = 1 := by
    simpa using future_exp_integral (c := 1) (by norm_num) T
  rw [hexp]
  ring

/-- The true-action policy is optimal among both admissible stationary
feedbacks, and its value is exactly `x²`. -/
theorem optimalFeedback_attains_and_is_minimal (x T : ℝ) :
    admissible optimalFeedback x T ∧
      policyValue optimalFeedback x T = x ^ 2 ∧
      ∀ π, admissible π x T → x ^ 2 ≤ policyValue π x T := by
  refine ⟨optimalFeedback_admissible x T,
    policyValue_eq_sq_of_true optimalFeedback x T (by intro t y; rfl), ?_⟩
  intro π hπ
  rcases hπ with htrue | hfalse
  · rw [policyValue_eq_sq_of_true π x T htrue]
  · rw [policyValue_eq_three_sq_of_false π x T hfalse]
    nlinarith [sq_nonneg x]

def zeroValueTarget (T : ℝ) : Set ℝ :=
  theorem26ZeroValueTarget Set.univ (fun x _ => x ^ 2) T

theorem zeroValueTarget_eq_singleton (T : ℝ) :
    zeroValueTarget T = ({0} : Set ℝ) := by
  ext x
  simp [zeroValueTarget, theorem26ZeroValueTarget]

/-- The Lyapunov, target, and value bounds in theorem 26-A follow from the
explicit optimum, not as assumptions to the model. -/
theorem concrete_condition26A (x T s : ℝ) :
    (Metric.infDist (flow x T s) (zeroValueTarget s)) ^ 2 =
        WAlong x T s ∧
      deriv (WAlong x T) s = -2 * WAlong x T s ∧
      (flow x T s) ^ 2 =
        (Metric.infDist (flow x T s) (zeroValueTarget s)) ^ 2 := by
  have hmodel := model_satisfies_condition26A x T s
  have htargets : zeroValueTarget s = zeroTarget s := by
    rw [zeroValueTarget_eq_singleton, zeroTarget_eq_singleton]
  rcases hmodel with ⟨hdist, hderiv, hvalue⟩
  have hvalue' : (flow x T s) ^ 2 =
      (Metric.infDist (flow x T s) (zeroTarget s)) ^ 2 := by
    rw [value_eq_sq] at hvalue
    exact hvalue
  rw [htargets]
  exact ⟨hdist, hderiv, hvalue'⟩

/-- Full geometric package used by theorem 26-A on the forward time interval:
alive invariance, closed nonempty zero-value targets, both Lyapunov distance
bounds, and exponential dissipation. -/
theorem concrete_condition26A_full (x T s : ℝ) (hTs : T ≤ s) :
    flow x T s ∈ Set.univ ∧
      zeroValueTarget s = ({0} : Set ℝ) ∧
      IsClosed (zeroValueTarget s) ∧
      (zeroValueTarget s).Nonempty ∧
      (Metric.infDist (flow x T s) (zeroValueTarget s)) ^ 2 = WAlong x T s ∧
      deriv (WAlong x T) s ≤ -2 * WAlong x T s ∧
      (flow x T s) ^ 2 ≤
        (Metric.infDist (flow x T s) (zeroValueTarget s)) ^ 2 := by
  rcases Tomabechi.Theorem24_26_Model.concrete_condition26A x T s hTs with
    ⟨halive, _htarget, _hclosed, _hnonempty, hdist, hdecay, hvalue⟩
  have htargets : zeroValueTarget s = zeroTarget s := by
    rw [zeroValueTarget_eq_singleton, zeroTarget_eq_singleton]
  have hvalue' : (flow x T s) ^ 2 ≤
      (Metric.infDist (flow x T s) (zeroTarget s)) ^ 2 := by
    rw [value_eq_sq] at hvalue
    exact hvalue
  refine ⟨halive, zeroValueTarget_eq_singleton s, ?_, ?_, ?_, hdecay, ?_⟩
  · rw [zeroValueTarget_eq_singleton]
    exact isClosed_singleton
  · rw [zeroValueTarget_eq_singleton]
    exact Set.singleton_nonempty 0
  · rw [htargets]
    exact hdist
  · rw [htargets]
    exact hvalue'

/-- The trajectory solves the controlled equation `x' = -x` under the
true-action feedback and `x' = 0` under the zero-drift feedback. -/
theorem trajectory_hasDerivAt (π : Feedback) (x T s : ℝ)
    (hπ : admissible π x T) :
    HasDerivAt (trajectory π x T) (if π.action (T, x) then
      -(trajectory π x T s) else 0) s := by
  rcases hπ with htrue | hfalse
  · have hderiv := flow_hasDerivAt x T s
    have hval : π.action (T, x) = true := htrue T x
    change HasDerivAt
      (fun u => if π.action (T, x) then flow x T u else x)
      (if π.action (T, x) then -(trajectory π x T s) else 0) s
    rw [hval]
    simp [trajectory, hval]
    exact hderiv
  · have hconst : HasDerivAt (fun _ : ℝ => x) 0 s := hasDerivAt_const s x
    have hval : π.action (T, x) = false := hfalse T x
    change HasDerivAt
      (fun u => if π.action (T, x) then flow x T u else x)
      (if π.action (T, x) then -(trajectory π x T s) else 0) s
    rw [hval]
    simp
    change HasDerivAt (fun _ : ℝ => x) 0 s
    exact hconst

theorem trajectory_solves_controlled_ode (π : Feedback) (x T s : ℝ)
    (hπ : admissible π x T) :
    HasDerivAt (trajectory π x T)
      (dynamics (trajectory π x T s) (π.action (s, trajectory π x T s))) s := by
  have hderiv := trajectory_hasDerivAt π x T s hπ
  rcases hπ with htrue | hfalse
  · have hinitial := htrue T x
    have hrhs : dynamics (trajectory π x T s)
        (π.action (s, trajectory π x T s)) = -(trajectory π x T s) := by
      simp [dynamics, htrue]
    rw [hrhs]
    simpa [hinitial] using hderiv
  · have hinitial := hfalse T x
    have hrhs : dynamics (trajectory π x T s)
        (π.action (s, trajectory π x T s)) = 0 := by
      simp [dynamics, hfalse]
    rw [hrhs]
    simpa [hinitial] using hderiv

/-- The running value used by the general PZS and optimal-value interface. -/
noncomputable def topRunningValue (π : Feedback) (x : ℝ) (T s : ℝ) : ℝ :=
  runningCost π (trajectory π x T s) T s

/-- In this concrete control model, PZS is equivalent to membership in the
zero-value target, by the already-proved theorem-26 interface. -/
theorem feedbackPZS_iff_zeroValueTarget (x T : ℝ) :
    FeedbackPZS admissible (fun t => futureLebesgueMeasure t)
      topRunningValue x T ↔ x ∈ zeroValueTarget T := by
  have hopt := optimalFeedback_attains_and_is_minimal x T
  have hbridge := feedbackPZS_iff_optimal_value_eq_zero
    (fun t => futureLebesgueMeasure t) (theorem26DiscountWeight 1)
    topRunningValue admissible optimalFeedback x T (x ^ 2)
    (by
      filter_upwards with s
      exact Real.exp_pos _)
    (by
      intro π hπ
      filter_upwards with s
      exact mul_nonneg (by norm_num)
        (sq_nonneg (trajectory π x T s)))
    (by
      intro π hπ
      change Integrable (discountedIntegrand π x T)
        (futureLebesgueMeasure T)
      exact policyIntegrand_integrable π x T hπ)
    hopt.1
    (by
      simpa [discountedFeedbackValue, topRunningValue,
        discountedIntegrand, policyValue] using hopt.2.1.symm)
    (by
      intro π hπ
      simpa [discountedFeedbackValue, topRunningValue,
        discountedIntegrand, policyValue] using hopt.2.2 π hπ)
  rw [hbridge]
  simp [zeroValueTarget, theorem26ZeroValueTarget]

/-- The two-level instance of the theorem-24 → theorem-26 classification:
condition 24-A excludes PZS at the lower layer, while the explicit optimal
upper-layer feedback has PZS exactly on its zero-value target. -/
theorem concrete_theorem24_to26_bridge (x T : ℝ) :
    0 < lowerValue T ∧
      ¬ FeedbackPZS lowerAdmissible (fun t => futureLebesgueMeasure t)
        (fun _π _x _T s => lowerRunningCost () s) () T ∧
      (FeedbackPZS admissible (fun t => futureLebesgueMeasure t)
        topRunningValue x T ↔ x ∈ zeroValueTarget T) := by
  have h24 := lower_model_theorem24 T
  have hlowerNoPZS := theorem24_no_feedbackPZS_of_condition24A
    (fun t => futureLebesgueMeasure t)
    (fun _π _x _T s => lowerRunningCost () s)
    lowerAdmissible () T (fun π hπ => h24.1 π hπ)
  exact ⟨h24.2.2, hlowerNoPZS, feedbackPZS_iff_zeroValueTarget x T⟩

/-- The optimal feedback's trajectory inherits the quantitative convergence
bound proved by the general theorem-26 conditional result. -/
theorem optimal_feedback_exponential_convergence (x T s : ℝ) (hTs : T ≤ s) :
    WAlong x T s ≤ WAlong x T T * Real.exp (-2 * (s - T)) ∧
      Metric.infDist (trajectory optimalFeedback x T s)
        (zeroValueTarget s) ≤
        Real.sqrt (WAlong x T T) * Real.exp (-(2 / 2) * (s - T)) := by
  have hbase := model_theorem26_exponential_convergence x T s hTs
  have htraj : trajectory optimalFeedback x T s = flow x T s :=
    trajectory_eq_flow_of_true optimalFeedback x T s (by intro t y; rfl)
  simpa [htraj, zeroValueTarget_eq_singleton, zeroTarget_eq_singleton]
    using hbase

/-- Full theorem-26 conclusions for the two-action model's optimal feedback,
including the optimal-value limit and the exact zero-residual/target
equivalence. This transports the Dini-based result for the explicit flow
through the verified true-action feedback trajectory. -/
theorem optimal_feedback_full_convergence (x T : ℝ) :
    (∀ s ≥ T,
      WAlong x T s ≤ WAlong x T T * Real.exp (-2 * (s - T)) ∧
        Metric.infDist (trajectory optimalFeedback x T s)
          (zeroValueTarget s) ≤
          Real.sqrt (WAlong x T T) * Real.exp (-(2 / 2) * (s - T))) ∧
    Filter.Tendsto
      (fun s => policyValue optimalFeedback
        (trajectory optimalFeedback x T s) s)
      Filter.atTop (nhds 0) ∧
    (∀ s ≥ T, WAlong x T s = 0 ↔
      trajectory optimalFeedback x T s ∈ zeroValueTarget s) := by
  have hbase := Tomabechi.Theorem24_26_Model.model_theorem26_full_convergence x T
  have htrajectory (s : ℝ) : trajectory optimalFeedback x T s = flow x T s :=
    trajectory_eq_flow_of_true optimalFeedback x T s (by intro t y; rfl)
  have hcost (s : ℝ) : policyValue optimalFeedback
      (trajectory optimalFeedback x T s) s =
        Tomabechi.Theorem24_26_Model.value (flow x T s) s := by
    calc
      policyValue optimalFeedback (trajectory optimalFeedback x T s) s =
          (trajectory optimalFeedback x T s) ^ 2 :=
        policyValue_eq_sq_of_true optimalFeedback
          (trajectory optimalFeedback x T s) s (by intro t y; rfl)
      _ = (flow x T s) ^ 2 := by rw [htrajectory s]
      _ = Tomabechi.Theorem24_26_Model.value (flow x T s) s :=
        (Tomabechi.Theorem24_26_Model.value_eq_sq _ _).symm
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hbound := hbase.1 s hs
    simpa [htrajectory s, zeroValueTarget_eq_singleton,
      Tomabechi.Theorem24_26_Model.zeroTarget_eq_singleton] using hbound
  · have hfun :
      (fun s => policyValue optimalFeedback
        (trajectory optimalFeedback x T s) s) =
      (fun s => Tomabechi.Theorem24_26_Model.value (flow x T s) s) :=
        funext hcost
    rw [hfun]
    exact hbase.2.1
  · intro s hs
    simpa [htrajectory s, zeroValueTarget_eq_singleton,
      Tomabechi.Theorem24_26_Model.zeroTarget_eq_singleton] using hbase.2.2 s hs

theorem optimal_feedback_alive_for_all_times (x T : ℝ) :
    ∀ s, trajectory optimalFeedback x T s ∈ (Set.univ : Set ℝ) := by
  intro s
  exact Set.mem_univ _

/-- The optimal closed-loop orbit preserves the zero-value target. -/
theorem optimal_feedback_target_forward_invariant (x T : ℝ)
    (hx : x ∈ zeroValueTarget T) :
    ∀ s, trajectory optimalFeedback x T s ∈ zeroValueTarget s := by
  have hx' : x ∈ zeroTarget T := by
    simpa [zeroValueTarget_eq_singleton, zeroTarget_eq_singleton] using hx
  intro s
  have hinv := model_forward_complete_and_target_invariant x T s hx'
  have hflow := hinv.2.2 s
  have htraj : trajectory optimalFeedback x T s = flow x T s :=
    trajectory_eq_flow_of_true optimalFeedback x T s (by intro t y; rfl)
  simpa [htraj, zeroValueTarget_eq_singleton, zeroTarget_eq_singleton]
    using hflow

/-! ## Instantiating the cross-abstraction theorem

The next definitions put the lower no-zero-cost layer and the upper controlled
layer into one two-element abstraction order. This makes the generic (26.3)
classification apply to an actual controlled model, with all upper-level
admissible feedbacks compared rather than only the selected optimum.
-/

abbrev HierarchyState : Bool → Type
  | false => Unit
  | true => ℝ
abbrev HierarchyFeedback : Bool → Type
  | false => LowerFeedback
  | true => Feedback

noncomputable def hierarchyTrajectory : (a : Bool) → HierarchyFeedback a → HierarchyState a →
    ℝ → ℝ → HierarchyState a
  | false, _, x, _, _ => x
  | true, π, x, T, s => trajectory π x T s

def hierarchyValueDensity : (a : Bool) → HierarchyState a → ℝ → ℝ
  | false, _, _ => 1
  | true, x, _ => 3 * x ^ 2

def hierarchyAdmissible : (a : Bool) → HierarchyFeedback a → HierarchyState a →
    ℝ → Prop
  | false, π, x, T => lowerAdmissible π x T
  | true, π, x, T => admissible π x T

def hierarchyOptimalValue : HierarchyState (⊤ : Bool) → ℝ → ℝ := fun x _ => x ^ 2

def hierarchyAlive : Set (HierarchyState true) := Set.univ

/-- The concrete two-level model satisfies the theorem's complete PZS
classification: no lower-level policy is permanently zero, while upstairs
PZS is exactly membership in the zero-optimal-value target `{0}`. -/
theorem concrete_hierarchy_pzs_classification :
    (∀ a (_ha : a < (⊤ : Bool)) (x : HierarchyState a) (T : ℝ),
      ¬ FeedbackPZS (hierarchyAdmissible a)
        (fun t => futureLebesgueMeasure t)
        (fun π x t s => hierarchyValueDensity a
          (hierarchyTrajectory a π x t s) s) x T) ∧
    (∀ (x : HierarchyState (⊤ : Bool)) (T : ℝ), x ∈ hierarchyAlive →
      (FeedbackPZS (hierarchyAdmissible (⊤ : Bool))
          (fun t => futureLebesgueMeasure t)
          (fun π x t s => hierarchyValueDensity (⊤ : Bool)
            (hierarchyTrajectory (⊤ : Bool) π x t s) s) x T ↔
        x ∈ theorem26ZeroValueTarget hierarchyAlive hierarchyOptimalValue T)) := by
  have hclass := theorem24_26_pzs_classification_expDiscount
    (A := Bool) (State := HierarchyState) (Feedback := HierarchyFeedback)
    1 (by norm_num) hierarchyTrajectory hierarchyValueDensity hierarchyAdmissible
    optimalFeedback hierarchyAlive hierarchyOptimalValue
    (by
      intro a ha x T π hπ
      have haFalse : a = false := by
        cases a <;> simp_all
      subst a
      have heq : (fun s => hierarchyValueDensity false
          (hierarchyTrajectory false π x T s) s) =ᵐ[futureLebesgueMeasure T]
          (fun s => lowerRunningCost x s) := by
        filter_upwards with s
        simp [hierarchyValueDensity, lowerRunningCost]
      intro hzero
      exact lower_condition24A x T (heq.trans hzero))
    (by
      intro x T hx π hπ
      filter_upwards with s
      cases hπ with
      | inl htrue =>
          simp only [hierarchyValueDensity]
          positivity
      | inr hfalse =>
          simp only [hierarchyValueDensity]
          positivity)
    (by
      intro x T π hx hπ
      cases hπ with
      | inl htrue =>
          have heq : (fun s => theorem26DiscountWeight 1 T s *
              hierarchyValueDensity true (trajectory π x T s) s) =ᵐ[futureLebesgueMeasure T]
              discountedIntegrand π x T := by
            filter_upwards with s
            simp [hierarchyValueDensity, discountedIntegrand, runningCost]
          exact (policyIntegrand_integrable π x T (Or.inl htrue)).congr heq.symm
      | inr hfalse =>
          have heq : (fun s => theorem26DiscountWeight 1 T s *
              hierarchyValueDensity true (trajectory π x T s) s) =ᵐ[futureLebesgueMeasure T]
              discountedIntegrand π x T := by
            filter_upwards with s
            simp [hierarchyValueDensity, discountedIntegrand, runningCost]
          exact (policyIntegrand_integrable π x T (Or.inr hfalse)).congr heq.symm)
    (by
      intro x T hx
      exact optimalFeedback_admissible x T)
    (by
      intro x T hx
      change x ^ 2 = ∫ s, theorem26DiscountWeight 1 T s *
        hierarchyValueDensity true (trajectory optimalFeedback x T s) s
          ∂futureLebesgueMeasure T
      have hvalue := policyValue_eq_sq_of_true optimalFeedback x T (by intro t y; rfl)
      rw [← hvalue]
      unfold policyValue
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      simp [hierarchyValueDensity, discountedIntegrand, runningCost])
    (by
      intro x T π hx hπ
      have hopt := optimalFeedback_attains_and_is_minimal x T
      rcases hπ with htrue | hfalse
      · change x ^ 2 ≤ _
        change x ^ 2 ≤ ∫ s, theorem26DiscountWeight 1 T s *
          hierarchyValueDensity true (trajectory π x T s) s
            ∂futureLebesgueMeasure T
        have heq : (∫ s, theorem26DiscountWeight 1 T s *
            hierarchyValueDensity true (trajectory π x T s) s
              ∂futureLebesgueMeasure T) = policyValue π x T := by
          unfold policyValue
          apply MeasureTheory.integral_congr_ae
          filter_upwards with s
          simp [hierarchyValueDensity, discountedIntegrand, runningCost]
        rw [heq]
        exact hopt.2.2 π (Or.inl htrue)
      · change x ^ 2 ≤ _
        change x ^ 2 ≤ ∫ s, theorem26DiscountWeight 1 T s *
          hierarchyValueDensity true (trajectory π x T s) s
            ∂futureLebesgueMeasure T
        have heq : (∫ s, theorem26DiscountWeight 1 T s *
            hierarchyValueDensity true (trajectory π x T s) s
              ∂futureLebesgueMeasure T) = policyValue π x T := by
          unfold policyValue
          apply MeasureTheory.integral_congr_ae
          filter_upwards with s
          simp [hierarchyValueDensity, discountedIntegrand, runningCost]
        rw [heq]
        exact hopt.2.2 π (Or.inr hfalse))
  constructor
  · intro a ha x T
    exact hclass.1 a ha x T
  · intro x T hx
    exact hclass.2 x T hx

end Tomabechi.Theorem24_26_ControlledModel
