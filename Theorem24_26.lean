import Mathlib
import Theorem1

/-!
# Theorem 24 → Theorem 26 foundations

This module contains the discounted-cost/PZS bridge, theorem 24's fixed-pair
positive-value result, theorem 26's zero-value target characterization, and
the differentiable Lyapunov form of its quantitative stability conclusion.
Model existence, optimal-feedback construction, and the source conditions
24-A/26-A remain explicit hypotheses rather than being derived here.
-/

namespace Tomabechi.Theorem24_26

/-- A nonnegative running value has zero discounted integral exactly when it
vanishes almost everywhere, provided the discount weight is positive almost
everywhere. This is the analytic bridge between zero optimal cost and the
permanent-zero-value condition used by PZS. -/
theorem nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (weight value : α → ℝ)
    (hweight : ∀ᵐ x ∂μ, 0 < weight x)
    (hvalue : ∀ᵐ x ∂μ, 0 ≤ value x)
    (hint : MeasureTheory.Integrable (fun x => weight x * value x) μ) :
    (∫ x, weight x * value x ∂μ) = 0 ↔ value =ᵐ[μ] 0 := by
  have hproduct_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x * value x := by
    filter_upwards [hweight, hvalue] with x hw hv
    exact mul_nonneg hw.le hv
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hproduct_nonneg hint]
  constructor
  · intro hproduct
    filter_upwards [hproduct, hweight] with x hprod hw
    have hmul : weight x * value x = 0 := by simpa using hprod
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hw)
  · intro hvalueZero
    filter_upwards [hvalueZero] with x hx
    simp [hx]

/-- Discounted trajectory cost, with the policy's running value integrated
against a strictly positive weight. -/
noncomputable def discountedTrajectoryCost
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (weight : α → ℝ) (runningValue : Policy → α → ℝ)
    (policy : Policy) : ℝ :=
  ∫ x, weight x * runningValue policy x ∂μ

/-- The policy-form of permanent zero suffering: one admissible policy keeps
the running value zero almost everywhere on the future time domain. -/
def HasPermanentZeroValuePolicy
    {α Policy : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (runningValue : Policy → α → ℝ) : Prop :=
  ∃ policy, runningValue policy =ᵐ[μ] 0

/-- A zero-value policy exists exactly when some admissible policy has zero
discounted cost, assuming nonnegative running values and positive discount. -/
theorem permanentZeroValuePolicy_iff_exists_zero_discounted_cost
    {α Policy : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (weight : α → ℝ)
    (runningValue : Policy → α → ℝ)
    (hweight : ∀ᵐ x ∂μ, 0 < weight x)
    (hnonneg : ∀ policy, ∀ᵐ x ∂μ, 0 ≤ runningValue policy x)
    (hint : ∀ policy,
      MeasureTheory.Integrable (fun x => weight x * runningValue policy x) μ) :
    HasPermanentZeroValuePolicy μ runningValue ↔
      ∃ policy, discountedTrajectoryCost μ weight runningValue policy = 0 := by
  constructor
  · rintro ⟨policy, hzero⟩
    refine ⟨policy, ?_⟩
    exact (nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero
      weight (runningValue policy) hweight (hnonneg policy) (hint policy)).2 hzero
  · rintro ⟨policy, hcost⟩
    refine ⟨policy, ?_⟩
    exact (nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero
      weight (runningValue policy) hweight (hnonneg policy) (hint policy)).1 hcost

/-- Attainment of the optimal value turns existence of a zero-cost policy
into the assertion that the optimal value itself is zero. -/
theorem exists_zero_cost_policy_iff_optimal_value_zero
    {Policy : Type*} (cost : Policy → ℝ) (optimalPolicy : Policy)
    (optimalValue : ℝ)
    (hattains : optimalValue = cost optimalPolicy)
    (hminimal : ∀ policy, optimalValue ≤ cost policy)
    (hnonneg : ∀ policy, 0 ≤ cost policy) :
    (∃ policy, cost policy = 0) ↔ optimalValue = 0 := by
  constructor
  · rintro ⟨policy, hzero⟩
    have hge : 0 ≤ optimalValue := by rw [hattains]; exact hnonneg optimalPolicy
    have hle : optimalValue ≤ 0 := by
      calc
        optimalValue ≤ cost policy := hminimal policy
        _ = 0 := hzero
    linarith
  · intro hzero
    refine ⟨optimalPolicy, ?_⟩
    calc
      cost optimalPolicy = optimalValue := hattains.symm
      _ = 0 := hzero

/-- For a fixed initial state and time, an attained minimum of the
nonnegative discounted running cost is zero exactly when a permanent
zero-value policy exists. This is the policy-level PZS characterization
used to define the top-level target in equation (26.1). Admissibility,
trajectory construction, and integrability are supplied by the model. -/
theorem permanentZeroValuePolicy_iff_optimal_discounted_cost_eq_zero
    {α Policy : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (weight : α → ℝ)
    (runningValue : Policy → α → ℝ)
    (hweight : ∀ᵐ x ∂μ, 0 < weight x)
    (hnonneg : ∀ policy, ∀ᵐ x ∂μ, 0 ≤ runningValue policy x)
    (hint : ∀ policy,
      MeasureTheory.Integrable (fun x => weight x * runningValue policy x) μ)
    (optimalPolicy : Policy) (optimalValue : ℝ)
    (hattains : optimalValue =
      discountedTrajectoryCost μ weight runningValue optimalPolicy)
    (hminimal : ∀ policy, optimalValue ≤
      discountedTrajectoryCost μ weight runningValue policy) :
    HasPermanentZeroValuePolicy μ runningValue ↔ optimalValue = 0 := by
  rw [permanentZeroValuePolicy_iff_exists_zero_discounted_cost
    μ weight runningValue hweight hnonneg hint]
  exact exists_zero_cost_policy_iff_optimal_value_zero
    (discountedTrajectoryCost μ weight runningValue) optimalPolicy optimalValue
    hattains hminimal (fun policy => by
      have hnonnegProd : ∀ᵐ x ∂μ,
          0 ≤ weight x * runningValue policy x := by
        filter_upwards [hweight, hnonneg policy] with x hw hv
        exact mul_nonneg hw.le hv
      exact MeasureTheory.integral_nonneg_of_ae hnonnegProd)

/-- The value of a single feedback policy from initial state `x` at time `T`.
`μ T` is the future-time measure (for example Lebesgue measure restricted to
`[T, ∞)`), and `weight T` is the discount factor. -/
noncomputable def discountedFeedbackValue
    {State Feedback : Type*} [MeasurableSpace ℝ]
    (μ : ℝ → MeasureTheory.Measure ℝ)
    (weight : ℝ → ℝ → ℝ)
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (π : Feedback) (x : State) (T : ℝ) : ℝ :=
  ∫ s, weight T s * runningValue π x T s ∂(μ T)

/-- A Borel-measurable Markov feedback: one fixed measurable map from time
and state to control. Keeping the map in a subtype makes both the Markov
dependence and Borel measurability explicit in theorem 26 specializations. -/
structure BorelMarkovFeedback (State Control : Type*)
    [MeasurableSpace State] [MeasurableSpace Control] where
  action : ℝ × State → Control
  measurable_action : Measurable action

/-- A Borel Markov feedback on the paper's actual time domain `[0, ∞)`. -/
structure NonnegativeTimeBorelMarkovFeedback (State Control : Type*)
    [MeasurableSpace State] [MeasurableSpace Control] where
  action : Set.Ici (0 : ℝ) × State → Control
  measurable_action : Measurable action

/-- Exponential discount used in theorem 26's definition of `J*`. -/
noncomputable def theorem26DiscountWeight (ρ T s : ℝ) : ℝ :=
  Real.exp (-ρ * (s - T))

/-- Lebesgue measure restricted to the theorem's future half-line. -/
noncomputable def futureLebesgueMeasure (T : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Ici T)

/-- The exponential discount weight is strictly positive everywhere, hence
positive almost everywhere for any future-time measure. -/
theorem theorem26DiscountWeight_pos_ae
    [MeasurableSpace ℝ] {μ : MeasureTheory.Measure ℝ} (ρ T : ℝ) :
    ∀ᵐ s ∂μ, 0 < theorem26DiscountWeight ρ T s := by
  filter_upwards with s
  exact Real.exp_pos _

/-- Permanent zero value from an initial pair means that one admissible
feedback keeps the nonnegative running value zero almost everywhere on its
future-time measure. The feedback type is global, so a policy is not replaced
by a newly chosen policy at each later time. -/
def FeedbackPZS
    {State Feedback : Type*} [MeasurableSpace ℝ]
    (admissible : Feedback → State → ℝ → Prop)
    (μ : ℝ → MeasureTheory.Measure ℝ)
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (x : State) (T : ℝ) : Prop :=
  ∃ π, admissible π x T ∧ runningValue π x T =ᵐ[μ T] 0

/-- In the fixed-feedback model of theorem 26, PZS is equivalent to zero
optimal value, provided the common feedback is admissible and optimal for this
initial pair, costs are attained, and the discount and running value satisfy
the stated positivity and nonnegativity conditions. This real-integral
convenience form assumes every admissible competitor is integrable; use the
`_of_lintegral` version when competitors may have infinite cost. -/
theorem feedbackPZS_iff_optimal_value_eq_zero
    {State Feedback : Type*} [MeasurableSpace ℝ]
    (μ : ℝ → MeasureTheory.Measure ℝ)
    (weight : ℝ → ℝ → ℝ)
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (π₀ : Feedback) (x : State) (T optimalValue : ℝ)
    (hweight : ∀ᵐ s ∂(μ T), 0 < weight T s)
    (hnonneg : ∀ π, admissible π x T →
      ∀ᵐ s ∂(μ T), 0 ≤ runningValue π x T s)
    (hint : ∀ π, admissible π x T →
      MeasureTheory.Integrable (fun s => weight T s * runningValue π x T s) (μ T))
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue = discountedFeedbackValue μ weight runningValue π₀ x T)
    (hminimal : ∀ π, admissible π x T →
      optimalValue ≤ discountedFeedbackValue μ weight runningValue π x T) :
    FeedbackPZS admissible μ runningValue x T ↔ optimalValue = 0 := by
  let Policy := {π : Feedback // admissible π x T}
  let rv : Policy → ℝ → ℝ := fun π s => runningValue π.1 x T s
  let cost : Policy → ℝ := fun π =>
    discountedFeedbackValue μ weight runningValue π.1 x T
  have hpzs : FeedbackPZS admissible μ runningValue x T ↔
      ∃ π : Policy, rv π =ᵐ[μ T] 0 := by
    constructor
    · rintro ⟨π, hπ, hzero⟩
      exact ⟨⟨π, hπ⟩, hzero⟩
    · rintro ⟨π, hzero⟩
      exact ⟨π.1, π.2, hzero⟩
  have hexists : (∃ π : Policy, cost π = 0) ↔ optimalValue = 0 :=
    exists_zero_cost_policy_iff_optimal_value_zero cost ⟨π₀, hπ₀⟩
      optimalValue (by simpa [cost] using hattains)
      (by intro π; exact hminimal π.1 π.2)
      (by
        intro π
        have hprod : ∀ᵐ s ∂(μ T),
            0 ≤ weight T s * runningValue π.1 x T s := by
          filter_upwards [hweight, hnonneg π.1 π.2] with s hw hv
          exact mul_nonneg hw.le hv
        simpa [cost, discountedFeedbackValue] using
          MeasureTheory.integral_nonneg_of_ae hprod)
  have hcost : (∃ π : Policy, cost π = 0) ↔
      ∃ π : Policy, rv π =ᵐ[μ T] 0 := by
    constructor
    · rintro ⟨π, hzeroCost⟩
      refine ⟨π, ?_⟩
      exact (nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero
        (weight T) (rv π) hweight (hnonneg π.1 π.2) (hint π.1 π.2)).1
        (by simpa [cost, discountedFeedbackValue] using hzeroCost)
    · rintro ⟨π, hzeroValue⟩
      refine ⟨π, ?_⟩
      exact (nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero
        (weight T) (rv π) hweight (hnonneg π.1 π.2) (hint π.1 π.2)).2 hzeroValue
  exact hpzs.trans (hcost.symm.trans hexists)

/-- The source theorem allows an admissible competitor to have infinite cost.
This extended-integral version therefore needs integrability only for the
attaining optimal feedback. The real-valued optimum is finite by attainment;
competitor costs and their optimality comparison live in `ℝ≥0∞`. -/
theorem feedbackPZS_iff_optimal_value_eq_zero_of_lintegral
    {State Feedback : Type*} [MeasurableSpace ℝ]
    (μ : ℝ → MeasureTheory.Measure ℝ)
    (weight : ℝ → ℝ → ℝ)
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (π₀ : Feedback) (x : State) (T optimalValue : ℝ)
    (hweight : ∀ᵐ s ∂(μ T), 0 < weight T s)
    (hnonneg : ∀ π, admissible π x T →
      ∀ᵐ s ∂(μ T), 0 ≤ runningValue π x T s)
    (hmeasurable : ∀ π, admissible π x T →
      Measurable (fun s => ENNReal.ofReal
        (weight T s * runningValue π x T s)))
    (hint₀ : MeasureTheory.Integrable
      (fun s => weight T s * runningValue π₀ x T s) (μ T))
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue =
      discountedFeedbackValue μ weight runningValue π₀ x T)
    (hminimal : ∀ π, admissible π x T →
      ENNReal.ofReal optimalValue ≤ ∫⁻ s, ENNReal.ofReal
        (weight T s * runningValue π x T s) ∂(μ T)) :
    FeedbackPZS admissible μ runningValue x T ↔ optimalValue = 0 := by
  constructor
  · rintro ⟨π, hπ, hzero⟩
    have hzeroIntegrand : (fun s => ENNReal.ofReal
        (weight T s * runningValue π x T s)) =ᵐ[μ T] 0 := by
      filter_upwards [hzero] with s hs
      simp [hs]
    have hzeroCost : ∫⁻ s, ENNReal.ofReal
        (weight T s * runningValue π x T s) ∂(μ T) = 0 := by
      rw [MeasureTheory.lintegral_congr_ae hzeroIntegrand]
      simp
    have hopt₀ : ENNReal.ofReal optimalValue ≤ 0 :=
      (hminimal π hπ).trans_eq hzeroCost
    have hopt_nonpos : optimalValue ≤ 0 := by
      by_contra h
      have hpos : 0 < ENNReal.ofReal optimalValue :=
        ENNReal.ofReal_pos.mpr (lt_of_not_ge h)
      exact (not_le_of_gt hpos) hopt₀
    have hprodNonneg : ∀ᵐ s ∂(μ T),
        0 ≤ weight T s * runningValue π₀ x T s := by
      filter_upwards [hweight, hnonneg π₀ hπ₀] with s hw hv
      exact mul_nonneg hw.le hv
    have hopt_nonneg : 0 ≤ optimalValue := by
      rw [hattains]
      exact MeasureTheory.integral_nonneg_of_ae hprodNonneg
    exact le_antisymm hopt_nonpos hopt_nonneg
  · intro hoptZero
    refine ⟨π₀, hπ₀, ?_⟩
    have hprodNonneg : ∀ᵐ s ∂(μ T),
        0 ≤ weight T s * runningValue π₀ x T s := by
      filter_upwards [hweight, hnonneg π₀ hπ₀] with s hw hv
      exact mul_nonneg hw.le hv
    have hlintegral : ENNReal.ofReal optimalValue = ∫⁻ s,
        ENNReal.ofReal (weight T s * runningValue π₀ x T s) ∂(μ T) := by
      rw [hattains]
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint₀ hprodNonneg
    have hcostZero : ∫⁻ s, ENNReal.ofReal
        (weight T s * runningValue π₀ x T s) ∂(μ T) = 0 := by
      calc
        ∫⁻ s, ENNReal.ofReal
            (weight T s * runningValue π₀ x T s) ∂(μ T) =
          ENNReal.ofReal optimalValue := hlintegral.symm
        _ = 0 := by simp [hoptZero]
    have hproductZero : (fun s => ENNReal.ofReal
        (weight T s * runningValue π₀ x T s)) =ᵐ[μ T] 0 :=
      (MeasureTheory.lintegral_eq_zero_iff
        (hmeasurable π₀ hπ₀)).mp hcostZero
    filter_upwards [hproductZero, hweight, hnonneg π₀ hπ₀] with s hprod hw hv
    have hmul_le : weight T s * runningValue π₀ x T s ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp hprod
    have hmul_eq : weight T s * runningValue π₀ x T s = 0 :=
      le_antisymm hmul_le (mul_nonneg hw.le hv)
    exact (mul_eq_zero.mp hmul_eq).resolve_left (ne_of_gt hw)

/-- Theorem 24's condition 24-A excludes every admissible policy whose
running value vanishes almost everywhere.  When the nonnegative discounted
cost has an attained optimum, this forces the optimal value to be strictly
positive.  This is the fixed-initial-pair form of the paper's argument from
condition 24-A to theorem 24's positive optimal cost. -/
theorem theorem24_positive_optimal_value_of_condition24A
    {State Feedback : Type*} [MeasurableSpace ℝ]
    (μ : ℝ → MeasureTheory.Measure ℝ)
    (weight : ℝ → ℝ → ℝ)
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (π₀ : Feedback) (x : State) (T optimalValue : ℝ)
    (hweight : ∀ᵐ s ∂(μ T), 0 < weight T s)
    (hnonneg : ∀ π, admissible π x T →
      ∀ᵐ s ∂(μ T), 0 ≤ runningValue π x T s)
    (hint : ∀ π, admissible π x T →
      MeasureTheory.Integrable (fun s => weight T s * runningValue π x T s) (μ T))
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue = discountedFeedbackValue μ weight runningValue π₀ x T)
    (hminimal : ∀ π, admissible π x T →
      optimalValue ≤ discountedFeedbackValue μ weight runningValue π x T)
    (hcondition24A : ∀ π, admissible π x T →
      ¬ runningValue π x T =ᵐ[μ T] 0) :
    0 < optimalValue := by
  have hvalueNonneg : 0 ≤ optimalValue := by
    rw [hattains, discountedFeedbackValue]
    have hprod : ∀ᵐ s ∂(μ T),
        0 ≤ weight T s * runningValue π₀ x T s := by
      filter_upwards [hweight, hnonneg π₀ hπ₀] with s hw hv
      exact mul_nonneg hw.le hv
    exact MeasureTheory.integral_nonneg_of_ae hprod
  have hnoPZS : ¬ FeedbackPZS admissible μ runningValue x T := by
    rintro ⟨π, hπ, hzero⟩
    exact hcondition24A π hπ hzero
  have hvalueNe : optimalValue ≠ 0 := by
    intro hzero
    exact hnoPZS ((feedbackPZS_iff_optimal_value_eq_zero μ weight runningValue
      admissible π₀ x T optimalValue hweight hnonneg hint hπ₀ hattains hminimal).2 hzero)
  exact lt_of_le_of_ne hvalueNonneg (Ne.symm hvalueNe)

/-- Theorem 24 with the paper's finite-cost attainment assumption: only the
attaining optimal policy must have an integrable real-valued cost. Competing
policies are compared in `ℝ≥0∞`, so admissible policies with infinite cost are
allowed. This avoids the stronger assumption that every admissible policy has
finite cost. -/
theorem theorem24_positive_optimal_value_of_condition24A_ennreal
    {State Feedback : Type*}
    (trajectory : Feedback → State → ℝ → ℝ → State)
    (V : Feedback → State → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (π₀ : Feedback) (x : State) (T ρ optimalValue : ℝ)
    (_htrajectory_initial : ∀ π, admissible π x T →
      trajectory π x T T = x)
    (_hρ : 0 < ρ)
    (hweight : ∀ᵐ s ∂futureLebesgueMeasure T,
      0 < theorem26DiscountWeight ρ T s)
    (hnonneg : ∀ π, admissible π x T →
      ∀ᵐ s ∂futureLebesgueMeasure T, 0 ≤ V π (trajectory π x T s) s)
    (hmeasurable : ∀ π, admissible π x T →
      Measurable (fun s => ENNReal.ofReal
        (theorem26DiscountWeight ρ T s * V π (trajectory π x T s) s)))
    (hint₀ : MeasureTheory.Integrable
      (fun s => theorem26DiscountWeight ρ T s * V π₀ (trajectory π₀ x T s) s)
      (futureLebesgueMeasure T))
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue = ∫ s,
      theorem26DiscountWeight ρ T s * V π₀ (trajectory π₀ x T s) s
        ∂(futureLebesgueMeasure T))
    (_hminimal : ∀ π, admissible π x T →
      ENNReal.ofReal optimalValue ≤ ∫⁻ s, ENNReal.ofReal
        (theorem26DiscountWeight ρ T s * V π (trajectory π x T s) s)
          ∂(futureLebesgueMeasure T))
    (hcondition24A : ∀ π, admissible π x T →
      ¬ (fun s => V π (trajectory π x T s) s) =ᵐ[futureLebesgueMeasure T] 0) :
    0 < optimalValue := by
  by_contra hnot
  have hnonpos : optimalValue ≤ 0 := le_of_not_gt hnot
  have hprodNonneg : ∀ᵐ s ∂futureLebesgueMeasure T,
      0 ≤ theorem26DiscountWeight ρ T s * V π₀ (trajectory π₀ x T s) s := by
    filter_upwards [hweight, hnonneg π₀ hπ₀] with s hw hv
    exact mul_nonneg hw.le hv
  have hlintegral : ENNReal.ofReal optimalValue =
      ∫⁻ s, ENNReal.ofReal
        (theorem26DiscountWeight ρ T s * V π₀ (trajectory π₀ x T s) s)
          ∂(futureLebesgueMeasure T) := by
    rw [hattains]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint₀ hprodNonneg
  have hcostZero : ∫⁻ s, ENNReal.ofReal
      (theorem26DiscountWeight ρ T s * V π₀ (trajectory π₀ x T s) s)
        ∂(futureLebesgueMeasure T) = 0 := by
    rw [← hlintegral]
    exact ENNReal.ofReal_eq_zero.mpr hnonpos
  have hproductZero : (fun s => ENNReal.ofReal
      (theorem26DiscountWeight ρ T s * V π₀ (trajectory π₀ x T s) s)) =ᵐ[
        futureLebesgueMeasure T] 0 :=
    (MeasureTheory.lintegral_eq_zero_iff
      (μ := futureLebesgueMeasure T) (hmeasurable π₀ hπ₀)).mp hcostZero
  have hvalueZero : (fun s => V π₀ (trajectory π₀ x T s) s) =ᵐ[
      futureLebesgueMeasure T] 0 := by
    filter_upwards [hproductZero, hweight, hnonneg π₀ hπ₀] with s hprod hw hv
    have hmul_le : theorem26DiscountWeight ρ T s *
        V π₀ (trajectory π₀ x T s) s ≤ 0 := ENNReal.ofReal_eq_zero.mp hprod
    have hmul_eq : theorem26DiscountWeight ρ T s *
        V π₀ (trajectory π₀ x T s) s = 0 :=
      le_antisymm hmul_le (mul_nonneg hw.le hv)
    exact (mul_eq_zero.mp hmul_eq).resolve_left (ne_of_gt hw)
  exact hcondition24A π₀ hπ₀ hvalueZero

/-- Theorem 24 specialized to the paper's discounted Lebesgue cost along
policy-generated trajectories. Condition 24-A is stated on the future
half-line with Lebesgue measure, and the discounted value is attained and
minimal among admissible feedbacks. -/
theorem theorem24_positive_optimal_value_expDiscount_of_condition24A
    {State Feedback : Type*}
    (trajectory : Feedback → State → ℝ → ℝ → State)
    (V : State → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (π₀ : Feedback) (x : State) (T ρ optimalValue : ℝ)
    (_htrajectory_initial : ∀ π, admissible π x T →
      trajectory π x T T = x)
    (_hρ : 0 < ρ)
    (hnonneg : ∀ π, admissible π x T →
      ∀ᵐ s ∂(futureLebesgueMeasure T), 0 ≤ V (trajectory π x T s) s)
    (hint : ∀ π, admissible π x T →
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight ρ T s * V (trajectory π x T s) s)
        (futureLebesgueMeasure T))
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue = ∫ s,
      theorem26DiscountWeight ρ T s * V (trajectory π₀ x T s) s
        ∂(futureLebesgueMeasure T))
    (hminimal : ∀ π, admissible π x T → optimalValue ≤ ∫ s,
      theorem26DiscountWeight ρ T s * V (trajectory π x T s) s
        ∂(futureLebesgueMeasure T))
    (hcondition24A : ∀ π, admissible π x T →
      ¬ (fun s => V (trajectory π x T s) s) =ᵐ[futureLebesgueMeasure T] 0) :
    0 < optimalValue := by
  let μ : ℝ → MeasureTheory.Measure ℝ := fun _ => futureLebesgueMeasure T
  let runningValue : Feedback → State → ℝ → ℝ → ℝ :=
    fun π y t s => V (trajectory π y t s) s
  have hweight : ∀ᵐ s ∂(μ T), 0 < theorem26DiscountWeight ρ T s :=
    theorem26DiscountWeight_pos_ae ρ T
  have hcondition : ∀ π, admissible π x T →
      ¬ runningValue π x T =ᵐ[μ T] 0 := by
    intro π hπ
    exact hcondition24A π hπ
  exact theorem24_positive_optimal_value_of_condition24A
    μ (theorem26DiscountWeight ρ) runningValue admissible π₀ x T optimalValue
    hweight hnonneg hint hπ₀ (by simpa [μ, runningValue, discountedFeedbackValue] using hattains)
    (by intro π hπ; simpa [μ, runningValue, discountedFeedbackValue] using hminimal π hπ)
    hcondition

/-- The universally quantified form of theorem 24's conclusion: every
abstraction below `⊤`, every initial state, and every start time has strictly
positive optimal discounted value. The minimizing policy may depend on the
initial pair, as allowed by theorem 24; this is separate from theorem 26's
single common feedback hypothesis. The result also records the implied
nonexistence of a permanent-zero-value policy at each lower initial pair. -/
theorem theorem24_positive_all_lower_levels_expDiscount
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    (ρ : ℝ) (hρ : 0 < ρ)
    (trajectory : ∀ a, Feedback a → State a → ℝ → ℝ → State a)
    (V : ∀ a, State a → ℝ → ℝ)
    (admissible : ∀ a, Feedback a → State a → ℝ → Prop)
    (optimalValue : ∀ a, State a → ℝ → ℝ)
    (htrajectory_initial : ∀ a (π : Feedback a) (x : State a) (T : ℝ),
      admissible a π x T → trajectory a π x T T = x)
    (optimalPolicy : ∀ a (x : State a) (T : ℝ), Feedback a)
    (hnonneg : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T →
      ∀ᵐ s ∂(futureLebesgueMeasure T), 0 ≤ V a (trajectory a π x T s) s)
    (hint : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T →
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight ρ T s *
          V a (trajectory a π x T s) s) (futureLebesgueMeasure T))
    (hoptimalPolicy : ∀ a (x : State a) (T : ℝ),
      admissible a (optimalPolicy a x T) x T)
    (hattains : ∀ a (x : State a) (T : ℝ),
      optimalValue a x T = ∫ s, theorem26DiscountWeight ρ T s *
        V a (trajectory a (optimalPolicy a x T) x T s) s
          ∂(futureLebesgueMeasure T))
    (hminimal : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T → optimalValue a x T ≤ ∫ s,
        theorem26DiscountWeight ρ T s * V a (trajectory a π x T s) s
          ∂(futureLebesgueMeasure T))
    (hcondition24A : ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ)
      (π : Feedback a), admissible a π x T →
      ¬ (fun s => V a (trajectory a π x T s) s) =ᵐ[futureLebesgueMeasure T] 0) :
    ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ),
      0 < optimalValue a x T ∧
        ¬ FeedbackPZS (admissible a)
          (fun _ => futureLebesgueMeasure T)
          (fun π y t s => V a (trajectory a π y t s) s) x T := by
  intro a ha x T
  have hpositive := theorem24_positive_optimal_value_expDiscount_of_condition24A
    (trajectory a) (V a) (admissible a)
    (optimalPolicy a x T) x T ρ (optimalValue a x T)
    (fun π hπ => htrajectory_initial a π x T hπ) hρ
    (fun π hπ => hnonneg a x T π hπ)
    (fun π hπ => hint a x T π hπ)
    (hoptimalPolicy a x T) (hattains a x T)
    (fun π hπ => hminimal a x T π hπ)
    (fun π hπ => hcondition24A a ha x T π hπ)
  refine ⟨hpositive, ?_⟩
  rintro ⟨π, hπ, hzero⟩
  exact hcondition24A a ha x T π hπ (by simpa using hzero)

/-- The universally quantified theorem 24 conclusion with finite cost required
only for the attained optimal policy. Competing admissible policies are
compared using extended nonnegative integrals, so they may have infinite cost. -/
theorem theorem24_positive_all_lower_levels_expDiscount_ennreal
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    (ρ : ℝ) (hρ : 0 < ρ)
    (trajectory : ∀ a, Feedback a → State a → ℝ → ℝ → State a)
    (V : ∀ a, State a → ℝ → ℝ)
    (admissible : ∀ a, Feedback a → State a → ℝ → Prop)
    (optimalValue : ∀ a, State a → ℝ → ℝ)
    (htrajectory_initial : ∀ a (π : Feedback a) (x : State a) (T : ℝ),
      admissible a π x T → trajectory a π x T T = x)
    (optimalPolicy : ∀ a (x : State a) (T : ℝ), Feedback a)
    (hnonneg : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T →
      ∀ᵐ s ∂(futureLebesgueMeasure T), 0 ≤ V a (trajectory a π x T s) s)
    (hmeasurable : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T →
      Measurable (fun s => ENNReal.ofReal (theorem26DiscountWeight ρ T s *
        V a (trajectory a π x T s) s)))
    (hintOptimal : ∀ a (x : State a) (T : ℝ),
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight ρ T s *
          V a (trajectory a (optimalPolicy a x T) x T s) s)
        (futureLebesgueMeasure T))
    (hoptimalPolicy : ∀ a (x : State a) (T : ℝ),
      admissible a (optimalPolicy a x T) x T)
    (hattains : ∀ a (x : State a) (T : ℝ),
      optimalValue a x T = ∫ s, theorem26DiscountWeight ρ T s *
        V a (trajectory a (optimalPolicy a x T) x T s) s
          ∂(futureLebesgueMeasure T))
    (hminimal : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T → ENNReal.ofReal (optimalValue a x T) ≤ ∫⁻ s,
        ENNReal.ofReal (theorem26DiscountWeight ρ T s *
          V a (trajectory a π x T s) s) ∂(futureLebesgueMeasure T))
    (hcondition24A : ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ)
      (π : Feedback a), admissible a π x T →
      ¬ (fun s => V a (trajectory a π x T s) s) =ᵐ[futureLebesgueMeasure T] 0) :
    ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ),
      0 < optimalValue a x T ∧
        ¬ FeedbackPZS (admissible a)
          (fun _ => futureLebesgueMeasure T)
          (fun π y t s => V a (trajectory a π y t s) s) x T := by
  intro a ha x T
  have hpositive := theorem24_positive_optimal_value_of_condition24A_ennreal
    (trajectory a) (fun _ => V a) (admissible a) (optimalPolicy a x T) x T ρ
    (optimalValue a x T) (fun π hπ => htrajectory_initial a π x T hπ) hρ
    (theorem26DiscountWeight_pos_ae ρ T)
    (fun π hπ => hnonneg a x T π hπ)
    (fun π hπ => hmeasurable a x T π hπ)
    (hintOptimal a x T) (hoptimalPolicy a x T) (hattains a x T)
    (fun π hπ => hminimal a x T π hπ)
    (fun π hπ => hcondition24A a ha x T π hπ)
  refine ⟨hpositive, ?_⟩
  rintro ⟨π, hπ, hzero⟩
  exact hcondition24A a ha x T π hπ (by simpa using hzero)

/-- Source-domain corollary of theorem 24. The data are still supplied for
all real start times, while the conclusion is stated only for the paper's
domain `T ≥ 0`. This makes the logical restriction explicit without
repeating the measure-theoretic proof. -/
theorem theorem24_positive_all_lower_levels_nonnegativeStartTimes
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    (ρ : ℝ) (hρ : 0 < ρ)
    (trajectory : ∀ a, Feedback a → State a → ℝ → ℝ → State a)
    (V : ∀ a, State a → ℝ → ℝ)
    (admissible : ∀ a, Feedback a → State a → ℝ → Prop)
    (optimalValue : ∀ a, State a → ℝ → ℝ)
    (htrajectory_initial : ∀ a (π : Feedback a) (x : State a) (T : ℝ),
      admissible a π x T → trajectory a π x T T = x)
    (optimalPolicy : ∀ a (x : State a) (T : ℝ), Feedback a)
    (hnonneg : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T →
      ∀ᵐ s ∂(futureLebesgueMeasure T),
        0 ≤ V a (trajectory a π x T s) s)
    (hmeasurable : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T →
      Measurable (fun s => ENNReal.ofReal (theorem26DiscountWeight ρ T s *
        V a (trajectory a π x T s) s)))
    (hintOptimal : ∀ a (x : State a) (T : ℝ),
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight ρ T s *
          V a (trajectory a (optimalPolicy a x T) x T s) s)
        (futureLebesgueMeasure T))
    (hoptimalPolicy : ∀ a (x : State a) (T : ℝ),
      admissible a (optimalPolicy a x T) x T)
    (hattains : ∀ a (x : State a) (T : ℝ),
      optimalValue a x T = ∫ s, theorem26DiscountWeight ρ T s *
        V a (trajectory a (optimalPolicy a x T) x T s) s
          ∂(futureLebesgueMeasure T))
    (hminimal : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T → ENNReal.ofReal (optimalValue a x T) ≤ ∫⁻ s,
        ENNReal.ofReal (theorem26DiscountWeight ρ T s *
          V a (trajectory a π x T s) s) ∂(futureLebesgueMeasure T))
    (hcondition24A : ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ)
      (π : Feedback a), admissible a π x T →
      ¬ (fun s => V a (trajectory a π x T s) s) =ᵐ[futureLebesgueMeasure T] 0) :
    ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ), 0 ≤ T →
      0 < optimalValue a x T ∧
        ¬ FeedbackPZS (admissible a)
          (fun _ => futureLebesgueMeasure T)
          (fun π y t s => V a (trajectory a π y t s) s) x T := by
  intro a ha x T hT
  exact theorem24_positive_all_lower_levels_expDiscount_ennreal
    ρ hρ trajectory V admissible optimalValue htrajectory_initial optimalPolicy
    hnonneg hmeasurable hintOptimal hoptimalPolicy hattains hminimal
    hcondition24A a ha x T

/-- Inputs for theorem 24 restricted to the source's nonnegative start-time
domain. Keeping these assumptions in a structure makes the source-domain
corollary's proof term small and keeps the time restriction visible. -/
structure Theorem24NonnegativeTimeData
    {A : Type*} [PartialOrder A] [OrderTop A]
    (State : A → Type*) (Feedback : A → Type*) where
  rho : ℝ
  rho_pos : 0 < rho
  trajectory : ∀ a, Feedback a → State a → ℝ → ℝ → State a
  runningCost : ∀ a, Feedback a → State a → ℝ → ℝ
  admissible : ∀ a, Feedback a → State a → ℝ → Prop
  optimalValue : ∀ a, State a → ℝ → ℝ
  optimalPolicy : ∀ a (x : State a) (T : ℝ), Feedback a
  trajectory_initial : ∀ a (π : Feedback a) (x : State a) (T : ℝ),
    0 ≤ T → admissible a π x T → trajectory a π x T T = x
  runningCost_nonnegative : ∀ a (π : Feedback a) (y : State a) (t : ℝ),
    0 ≤ runningCost a π y t
  measurable_cost : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
    0 ≤ T → admissible a π x T →
    Measurable (fun s => ENNReal.ofReal (theorem26DiscountWeight rho T s *
      runningCost a π (trajectory a π x T s) s))
  optimal_cost_integrable : ∀ a (x : State a) (T : ℝ), 0 ≤ T →
    MeasureTheory.Integrable
      (fun s => theorem26DiscountWeight rho T s *
        runningCost a (optimalPolicy a x T)
          (trajectory a (optimalPolicy a x T) x T s) s)
      (futureLebesgueMeasure T)
  optimal_policy_admissible : ∀ a (x : State a) (T : ℝ), 0 ≤ T →
    admissible a (optimalPolicy a x T) x T
  optimal_value_attained : ∀ a (x : State a) (T : ℝ), 0 ≤ T →
    optimalValue a x T = ∫ s, theorem26DiscountWeight rho T s *
      runningCost a (optimalPolicy a x T)
        (trajectory a (optimalPolicy a x T) x T s) s
        ∂(futureLebesgueMeasure T)
  optimal_value_minimal : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
    0 ≤ T → admissible a π x T →
    ENNReal.ofReal (optimalValue a x T) ≤ ∫⁻ s,
      ENNReal.ofReal (theorem26DiscountWeight rho T s *
        runningCost a π (trajectory a π x T s) s)
          ∂(futureLebesgueMeasure T)
  condition24A : ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ),
    0 ≤ T → ∀ (π : Feedback a), admissible a π x T →
      ¬ (fun s => runningCost a π (trajectory a π x T s) s) =ᵐ[
        futureLebesgueMeasure T] 0

/-- Theorem 24 from assumptions supplied only on `T ≥ 0`. The proof is
pointwise in the initial pair; no assumptions at negative times are needed. -/
theorem theorem24_lower_conclusions_from_nonnegativeTimeData
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    (D : Theorem24NonnegativeTimeData State Feedback) :
    ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ), 0 ≤ T →
      0 < D.optimalValue a x T ∧
        ¬ FeedbackPZS (D.admissible a)
          (fun _ => futureLebesgueMeasure T)
          (fun π y t s => D.runningCost a π
            (D.trajectory a π y t s) s) x T := by
  intro a ha x T hT
  refine ⟨?_, ?_⟩
  · exact theorem24_positive_optimal_value_of_condition24A_ennreal
      (D.trajectory a) (fun π y s => D.runningCost a π y s)
      (D.admissible a)
      (D.optimalPolicy a x T) x T D.rho (D.optimalValue a x T)
      (fun π hπ => D.trajectory_initial a π x T hT hπ) D.rho_pos
      (theorem26DiscountWeight_pos_ae D.rho T)
      (fun π hπ => Filter.Eventually.of_forall fun s =>
        D.runningCost_nonnegative a π (D.trajectory a π x T s) s)
      (fun π hπ => D.measurable_cost a x T π hT hπ)
      (D.optimal_cost_integrable a x T hT)
      (D.optimal_policy_admissible a x T hT)
      (D.optimal_value_attained a x T hT)
      (fun π hπ => D.optimal_value_minimal a x T π hT hπ)
      (fun π hπ => D.condition24A a ha x T hT π hπ)
  · rintro ⟨π, hπ, hzero⟩
    exact D.condition24A a ha x T hT π hπ hzero

/-- The pointwise lower-abstraction conclusion of (27.2) inherited from
condition 24-A, stated directly as failure of permanent zero suffering. -/
theorem theorem24_no_feedbackPZS_of_condition24A
    {State Feedback : Type*} [MeasurableSpace ℝ]
    (μ : ℝ → MeasureTheory.Measure ℝ)
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (x : State) (T : ℝ)
    (hcondition24A : ∀ π, admissible π x T →
      ¬ runningValue π x T =ᵐ[μ T] 0) :
    ¬ FeedbackPZS admissible μ runningValue x T := by
  rintro ⟨π, hπ, hzero⟩
  exact hcondition24A π hπ hzero

/-- Strictly positive running value almost everywhere on a nonzero measure
space rules out an almost-everywhere zero running-value trajectory. -/
theorem not_ae_zero_of_ae_strictlyPositive
    (μ : MeasureTheory.Measure ℝ) (runningValue : ℝ → ℝ)
    (hμ : μ Set.univ ≠ 0)
    (hpositive : ∀ᵐ s ∂μ, 0 < runningValue s) :
    ¬ runningValue =ᵐ[μ] 0 := by
  intro hzero
  have hfalse : ∀ᵐ s ∂μ, False := by
    filter_upwards [hpositive, hzero] with s hpos hz
    rw [hz] at hpos
    exact (lt_irrefl 0 hpos)
  have hmeasureZero : μ Set.univ = 0 := by
    rw [MeasureTheory.ae_iff] at hfalse
    simpa using hfalse
  exact hμ hmeasureZero

/-- A condition-24-A criterion for the paper's future Lebesgue measure: if
every admissible trajectory has strictly positive running value a.e., then no
such trajectory is permanently zero a.e. -/
theorem theorem24_condition24A_of_ae_strictlyPositive
    {State Feedback : Type*}
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (x : State) (T : ℝ)
    (hpositive : ∀ π, admissible π x T →
      ∀ᵐ s ∂futureLebesgueMeasure T, 0 < runningValue π x T s) :
    ∀ π, admissible π x T →
      ¬ runningValue π x T =ᵐ[futureLebesgueMeasure T] 0 := by
  intro π hπ
  apply not_ae_zero_of_ae_strictlyPositive (futureLebesgueMeasure T)
    (runningValue π x T) ?_ (hpositive π hπ)
  rw [futureLebesgueMeasure, MeasureTheory.Measure.restrict_apply_univ,
    Real.volume_Ici]
  exact ENNReal.top_ne_zero


/-- The zero optimal-value set in equation (26.1), intersected with the alive
region. -/
def theorem26ZeroValueTarget {State : Type*}
    (alive : Set State) (optimalValue : State → ℝ → ℝ) (T : ℝ) : Set State :=
  alive ∩ {x | optimalValue x T = 0}

/-- The quantitative stability conclusion (26.2) from the paper's upper
right-slope (upper Dini derivative) form of condition 26-A. Continuity of the
Lyapunov path and the quadratic lower distance bound suffice; pointwise
differentiability is not required. -/
theorem theorem26_lyapunov_exponential_decay_of_rightSlopeBound
    {State : Type*} [PseudoMetricSpace State]
    (trajectory : ℝ → State) (N : ℝ → Set State)
    (WAlong distAlong : ℝ → ℝ) (c₁ rate T t : ℝ)
    (hc₁ : 0 < c₁) (hrate : 0 < rate) (hTt : T ≤ t)
    (hWcontinuous : ContinuousOn WAlong (Set.Icc T t))
    (hWnonneg : ∀ s ≥ T, 0 ≤ WAlong s)
    (hWdecay : ∀ s ∈ Set.Ico T t,
      Tomabechi.Theorem1.RightSlopeBound WAlong s (-rate * WAlong s))
    (hdist_nonneg : ∀ s ≥ T, 0 ≤ distAlong s)
    (hdist_eq : ∀ s, distAlong s = Metric.infDist (trajectory s) (N s))
    (herror : ∀ s ≥ T, c₁ * (distAlong s) ^ 2 ≤ WAlong s) :
    WAlong t ≤ WAlong T * Real.exp (-rate * (t - T)) ∧
      distAlong t ≤ Real.sqrt (WAlong T / c₁) *
        Real.exp (-(rate / 2) * (t - T)) := by
  have hpotential := Tomabechi.Theorem1.lyapunov_exponential_decay_of_right_slope_bound
    WAlong (rate / 2) T t (by linarith) hTt hWcontinuous
    (by
      intro s hs
      have hrateEq : -rate * WAlong s =
          -2 * (rate / 2) * WAlong s := by ring
      simpa [Tomabechi.Theorem1.RightSlopeBound, hrateEq] using
        hWdecay s hs)
  have hdiv : (distAlong t) ^ 2 ≤ WAlong t / c₁ :=
    (le_div_iff₀ hc₁).2 (by nlinarith [herror t hTt])
  have hbase : 0 ≤ WAlong T / c₁ := div_nonneg (hWnonneg T le_rfl) hc₁.le
  have hexp_nonneg : 0 ≤ Real.exp (-(rate / 2) * (t - T)) := Real.exp_nonneg _
  have hsquare : (distAlong t) ^ 2 ≤
      (Real.sqrt (WAlong T / c₁) * Real.exp (-(rate / 2) * (t - T))) ^ 2 := by
    have hexp_sq : Real.exp (-(rate / 2) * (t - T)) ^ 2 =
        Real.exp (-rate * (t - T)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hsqrt := Real.sq_sqrt hbase
    calc
      (distAlong t) ^ 2 ≤ WAlong t / c₁ := hdiv
      _ ≤ (WAlong T * Real.exp (-rate * (t - T))) / c₁ := by
        have hexp : -2 * (rate / 2) * (t - T) = -rate * (t - T) := by ring
        rw [hexp] at hpotential
        exact div_le_div_of_nonneg_right hpotential hc₁.le
      _ = (Real.sqrt (WAlong T / c₁) *
          Real.exp (-(rate / 2) * (t - T))) ^ 2 := by
        rw [div_eq_mul_inv, mul_pow, hsqrt, hexp_sq]
        field_simp
  have hrhs_nonneg : 0 ≤ Real.sqrt (WAlong T / c₁) *
      Real.exp (-(rate / 2) * (t - T)) := mul_nonneg (Real.sqrt_nonneg _) hexp_nonneg
  constructor
  · have hexp : -2 * (rate / 2) * (t - T) = -rate * (t - T) := by ring
    rw [hexp] at hpotential
    exact hpotential
  · simpa [hdist_eq] using
      (sq_le_sq₀ (hdist_nonneg t hTt) hrhs_nonneg).mp hsquare

/-- The common Lyapunov lemma in the source paper explicitly assumes absolute
continuity along each finite trajectory interval. Absolute continuity gives
the continuity required by the upper-Dini comparison theorem above. -/
theorem theorem26_lyapunov_exponential_decay_of_rightSlopeBound_of_ac
    {State : Type*} [PseudoMetricSpace State]
    (trajectory : ℝ → State) (N : ℝ → Set State)
    (WAlong distAlong : ℝ → ℝ) (c₁ rate T t : ℝ)
    (hc₁ : 0 < c₁) (hrate : 0 < rate) (hTt : T ≤ t)
    (hWac : AbsolutelyContinuousOnInterval WAlong T t)
    (hWnonneg : ∀ s ≥ T, 0 ≤ WAlong s)
    (hWdecay : ∀ s ∈ Set.Ico T t,
      Tomabechi.Theorem1.RightSlopeBound WAlong s (-rate * WAlong s))
    (hdist_nonneg : ∀ s ≥ T, 0 ≤ distAlong s)
    (hdist_eq : ∀ s, distAlong s = Metric.infDist (trajectory s) (N s))
    (herror : ∀ s ≥ T, c₁ * (distAlong s) ^ 2 ≤ WAlong s) :
    WAlong t ≤ WAlong T * Real.exp (-rate * (t - T)) ∧
      distAlong t ≤ Real.sqrt (WAlong T / c₁) *
        Real.exp (-(rate / 2) * (t - T)) := by
  apply theorem26_lyapunov_exponential_decay_of_rightSlopeBound
    trajectory N WAlong distAlong c₁ rate T t hc₁ hrate hTt
    (by simpa [Set.uIcc_of_le hTt] using hWac.continuousOn)
    hWnonneg hWdecay hdist_nonneg hdist_eq herror

/-- The quantitative stability conclusion (26.2), under the differentiable
trajectory form of condition 26-A.  The source paper states an upper right
Dini derivative bound; this Lean theorem uses pointwise differentiability and
the corresponding derivative inequality. -/
theorem theorem26_lyapunov_exponential_decay
    {State : Type*} [PseudoMetricSpace State]
    (trajectory : ℝ → State) (N : ℝ → Set State)
    (WAlong distAlong : ℝ → ℝ) (c₁ rate T t : ℝ)
    (hc₁ : 0 < c₁) (hrate : 0 < rate) (hTt : T ≤ t)
    (hWdiff : ∀ s, HasDerivAt WAlong (deriv WAlong s) s)
    (hWnonneg : ∀ s ≥ T, 0 ≤ WAlong s)
    (hWdecay : ∀ s ≥ T, deriv WAlong s ≤ -rate * WAlong s)
    (hdist_nonneg : ∀ s ≥ T, 0 ≤ distAlong s)
    (hdist_eq : ∀ s, distAlong s = Metric.infDist (trajectory s) (N s))
    (herror : ∀ s ≥ T, c₁ * (distAlong s) ^ 2 ≤ WAlong s) :
    WAlong t ≤ WAlong T * Real.exp (-rate * (t - T)) ∧
      distAlong t ≤ Real.sqrt (WAlong T / c₁) *
        Real.exp (-(rate / 2) * (t - T)) := by
  have hpotential := Tomabechi.Theorem1.lyapunov_exponential_decay_by_mathlib_gronwall
    WAlong (deriv WAlong) (rate / 2) T t (by linarith) hTt hWdiff
    (by intro s hs; nlinarith [hWdecay s hs])
  have hdistance := Tomabechi.Theorem1.distance_decay WAlong distAlong
    (rate / 2) (1 / c₁) T t (by linarith) (by positivity) hTt hWdiff
    hWnonneg (by intro s hs; nlinarith [hWdecay s hs]) hdist_nonneg
    (by
      intro s hs
      have hdiv : (distAlong s) ^ 2 ≤ WAlong s / c₁ :=
        (le_div_iff₀ hc₁).2 (by nlinarith [herror s hs])
      calc
        (distAlong s) ^ 2 ≤ WAlong s / c₁ := hdiv
        _ = (1 / c₁) * WAlong s := by
          field_simp [ne_of_gt hc₁])
  constructor
  · have hexp : -2 * (rate / 2) * (t - T) = -rate * (t - T) := by ring
    rw [hexp] at hpotential
    exact hpotential
  · simpa [hdist_eq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdistance

/-- A nonnegative distance with the exponential upper bound in (26.2)
tends to zero. This makes the qualitative limit in the theorem an explicit
consequence of its quantitative estimate. -/
theorem theorem26_exponential_bound_tendsto_zero
    (distance : ℝ → ℝ) (amplitude rate T : ℝ)
    (hrate : 0 < rate)
    (hdistance_nonneg : ∀ᶠ t in Filter.atTop, 0 ≤ distance t)
    (hdistance_bound : ∀ᶠ t in Filter.atTop,
      distance t ≤ amplitude * Real.exp (-rate * (t - T))) :
    Filter.Tendsto distance Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun t : ℝ => t - T) Filter.atTop Filter.atTop := by
    change Filter.map (fun t : ℝ => t - T) Filter.atTop ≤ Filter.atTop
    rw [Filter.map_sub_atTop_eq]
  have hlinear : Filter.Tendsto (fun t : ℝ => -rate * (t - T))
      Filter.atTop Filter.atBot :=
    (Filter.tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hrate)).2 hshift
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-rate * (t - T)))
      Filter.atTop (nhds 0) := Real.tendsto_exp_comp_nhds_zero.mpr hlinear
  have hboundTendsto : Filter.Tendsto
      (fun t : ℝ => amplitude * Real.exp (-rate * (t - T)))
      Filter.atTop (nhds 0) := by
    simpa [mul_comm] using hexp.const_mul amplitude
  exact squeeze_zero' hdistance_nonneg hdistance_bound hboundTendsto

/-- The value-convergence part following (26.C): if the distance to the
zero-value target tends to zero and `J* ≤ ω(dist)` with `ω` continuous at
zero and `ω(0)=0`, then the optimal value along the trajectory tends to zero.
Only continuity at zero is needed for this implication. -/
theorem theorem26_value_tendsto_zero_of_distance_tendsto
    (optimalValueAlong distance : ℝ → ℝ) (ω : ℝ → ℝ)
    (hωcontinuous : ContinuousAt ω 0) (hωzero : ω 0 = 0)
    (hdistance : Filter.Tendsto distance Filter.atTop (nhds 0))
    (hvalue_nonneg : ∀ᶠ t in Filter.atTop, 0 ≤ optimalValueAlong t)
    (hvalue_bound : ∀ᶠ t in Filter.atTop,
      optimalValueAlong t ≤ ω (distance t)) :
    Filter.Tendsto optimalValueAlong Filter.atTop (nhds 0) := by
  have hω : Filter.Tendsto (fun t => ω (distance t)) Filter.atTop (nhds 0) := by
    simpa [Function.comp_def, hωzero] using hωcontinuous.tendsto.comp hdistance
  exact squeeze_zero' hvalue_nonneg hvalue_bound hω

/-- The optimal-value convergence conclusion in theorem 26 follows from its
quantitative stability estimate and condition (26.C).  The hypotheses are
stated along one trajectory: they require the differentiable form of the
Lyapunov decay condition and the value-distance comparison with a modulus
continuous at zero. -/
theorem theorem26_optimal_value_tendsto_zero
    {State : Type*} [PseudoMetricSpace State]
    (trajectory : ℝ → State) (N : ℝ → Set State)
    (WAlong : ℝ → ℝ) (optimalValue : State → ℝ → ℝ) (ω : ℝ → ℝ)
    (c₁ rate T : ℝ) (hc₁ : 0 < c₁) (hrate : 0 < rate)
    (hWdiff : ∀ s, HasDerivAt WAlong (deriv WAlong s) s)
    (hWnonneg : ∀ s ≥ T, 0 ≤ WAlong s)
    (hWdecay : ∀ s ≥ T, deriv WAlong s ≤ -rate * WAlong s)
    (herror : ∀ s ≥ T,
      c₁ * (Metric.infDist (trajectory s) (N s)) ^ 2 ≤ WAlong s)
    (hωcontinuous : ContinuousAt ω 0) (hωzero : ω 0 = 0)
    (hvalue_nonneg : ∀ᶠ t in Filter.atTop,
      0 ≤ optimalValue (trajectory t) t)
    (h26C : ∀ᶠ t in Filter.atTop,
      optimalValue (trajectory t) t ≤
        ω (Metric.infDist (trajectory t) (N t))) :
    Filter.Tendsto (fun t => optimalValue (trajectory t) t)
      Filter.atTop (nhds 0) := by
  let distance : ℝ → ℝ := fun s => Metric.infDist (trajectory s) (N s)
  have hdist_nonneg : ∀ s ≥ T, 0 ≤ distance s := by
    intro s hs
    exact Metric.infDist_nonneg
  have hdist_bound : ∀ᶠ s in Filter.atTop,
      distance s ≤ Real.sqrt (WAlong T / c₁) *
        Real.exp (-(rate / 2) * (s - T)) := by
    filter_upwards [Filter.eventually_ge_atTop T] with s hs
    have hdecay := theorem26_lyapunov_exponential_decay trajectory N WAlong
      distance c₁ rate T s hc₁ hrate hs hWdiff hWnonneg hWdecay
      (by intro u hu; exact Metric.infDist_nonneg)
      (by intro u; rfl)
      (by intro u hu; exact herror u hu)
    exact hdecay.2
  have hdist_tendsto : Filter.Tendsto distance Filter.atTop (nhds 0) :=
    theorem26_exponential_bound_tendsto_zero distance
      (Real.sqrt (WAlong T / c₁)) (rate / 2) T (by linarith)
      (Filter.Eventually.of_forall fun s => Metric.infDist_nonneg)
      hdist_bound
  exact theorem26_value_tendsto_zero_of_distance_tendsto
    (fun t => optimalValue (trajectory t) t) distance ω
    hωcontinuous hωzero hdist_tendsto hvalue_nonneg (by
      filter_upwards [h26C] with t ht
      simpa [distance] using ht)

/-- The combined dynamic conclusion of theorem 26 for the actual target
`N_top(t) = B_alive ∩ {x | J*(x,t)=0}`. Along a forward-complete alive
trajectory, the differentiable form of (26.B), the lower distance comparison
in (26.A), and (26.C) imply both the quantitative estimates (26.2) and
`J*(x(t),t) → 0`. The condition 26-A assumptions are explicit inputs; this
lemma does not construct the trajectory or establish those assumptions from a
control model. -/
theorem theorem26_full_conditional_convergence
    {State : Type*} [PseudoMetricSpace State]
    (trajectory : ℝ → State) (alive : Set State)
    (optimalValue : State → ℝ → ℝ) (WAlong : ℝ → ℝ) (ω : ℝ → ℝ)
    (c₁ rate T : ℝ) (hc₁ : 0 < c₁) (hrate : 0 < rate)
    (hAlive : ∀ s ≥ T, trajectory s ∈ alive)
    (hWdiff : ∀ s, HasDerivAt WAlong (deriv WAlong s) s)
    (hWnonneg : ∀ s ≥ T, 0 ≤ WAlong s)
    (hWdecay : ∀ s ≥ T, deriv WAlong s ≤ -rate * WAlong s)
    (herror : ∀ s ≥ T,
      c₁ * (Metric.infDist (trajectory s)
        (theorem26ZeroValueTarget alive optimalValue s)) ^ 2 ≤ WAlong s)
    (ωcontinuous : ContinuousAt ω 0) (hωzero : ω 0 = 0)
    (h26C : ∀ s ≥ T,
      0 ≤ optimalValue (trajectory s) s ∧
        optimalValue (trajectory s) s ≤
          ω (Metric.infDist (trajectory s)
            (theorem26ZeroValueTarget alive optimalValue s))) :
    (∀ s ≥ T, trajectory s ∈ alive) ∧
    (∀ s ≥ T,
      WAlong s ≤ WAlong T * Real.exp (-rate * (s - T)) ∧
        Metric.infDist (trajectory s)
          (theorem26ZeroValueTarget alive optimalValue s) ≤
          Real.sqrt (WAlong T / c₁) * Real.exp (-(rate / 2) * (s - T))) ∧
    Filter.Tendsto (fun s => optimalValue (trajectory s) s)
      Filter.atTop (nhds 0) := by
  have hvalue_nonneg : ∀ᶠ s in Filter.atTop,
      0 ≤ optimalValue (trajectory s) s := by
    filter_upwards [Filter.eventually_ge_atTop T] with s hs
    exact (h26C s hs).1
  have hvalue_bound : ∀ᶠ s in Filter.atTop,
      optimalValue (trajectory s) s ≤
        ω (Metric.infDist (trajectory s)
          (theorem26ZeroValueTarget alive optimalValue s)) := by
    filter_upwards [Filter.eventually_ge_atTop T] with s hs
    exact (h26C s hs).2
  have hvalue_tendsto := theorem26_optimal_value_tendsto_zero
    trajectory (theorem26ZeroValueTarget alive optimalValue) WAlong
    optimalValue ω c₁ rate T hc₁ hrate hWdiff hWnonneg hWdecay herror
    ωcontinuous hωzero hvalue_nonneg hvalue_bound
  refine ⟨hAlive, ?_, hvalue_tendsto⟩
  intro s hs
  have hdecay := theorem26_lyapunov_exponential_decay trajectory
    (theorem26ZeroValueTarget alive optimalValue) WAlong
    (fun u => Metric.infDist (trajectory u)
      (theorem26ZeroValueTarget alive optimalValue u))
    c₁ rate T s hc₁ hrate hs hWdiff hWnonneg hWdecay
    (by intro u hu; exact Metric.infDist_nonneg)
    (by intro u; rfl)
    (by intro u hu; exact herror u hu)
  exact hdecay

/-- A right-sided Dini bound alone does not control a jump at the right
endpoint. This witness explains why the comparison proof below requires
continuity of the Lyapunov path on each finite interval. -/
noncomputable def rightJumpLyapunov (t : ℝ) : ℝ :=
  if t < 1 then Real.exp (-2 * t) else 2 * Real.exp (-2 * t)

/-- The state-time Lyapunov function behind the jump witness. -/
noncomputable def rightJumpLyapunovState (x t : ℝ) : ℝ :=
  (if t < 1 then 1 else 2) * x ^ 2

/-- The state-time witness satisfies the full two-sided quadratic comparison
with distance to the target `{0}`; its defect is time regularity. -/
theorem rightJumpLyapunovState_quadratic_comparison (x t : ℝ) :
    x ^ 2 ≤ rightJumpLyapunovState x t ∧
      rightJumpLyapunovState x t ≤ 2 * x ^ 2 := by
  by_cases h : t < 1 <;> simp [rightJumpLyapunovState, h] <;> nlinarith [sq_nonneg x]

theorem rightJumpLyapunovState_along_expTrajectory (t : ℝ) :
    rightJumpLyapunovState (Real.exp (-t)) t = rightJumpLyapunov t := by
  have hexp : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1 <;> ring
  by_cases h : t < 1
  · simp [rightJumpLyapunovState, rightJumpLyapunov, h, hexp]
  · simp [rightJumpLyapunovState, rightJumpLyapunov, h, hexp]

theorem rightJumpLyapunov_satisfies_slope_before_jump (t : ℝ) (ht : t < 1) :
    Tomabechi.Theorem1.RightSlopeBound rightJumpLyapunov t
      (-2 * rightJumpLyapunov t) := by
  have hinner : HasDerivAt (fun s : ℝ => -2 * s) (-2) t := by
    simpa using (hasDerivAt_id t).const_mul (-2)
  have hderivExp : HasDerivAt (fun s : ℝ => Real.exp (-2 * s))
      (-2 * Real.exp (-2 * t)) t := by
    convert (Real.hasDerivAt_exp (-2 * t)).comp t hinner using 1
    · funext s
      rfl
    · ring
  have hevent : rightJumpLyapunov =ᶠ[nhds t] (fun s => Real.exp (-2 * s)) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    change s < 1 at hs
    simp [rightJumpLyapunov, hs]
  have hderiv : HasDerivAt rightJumpLyapunov (-2 * Real.exp (-2 * t)) t :=
    hderivExp.congr_of_eventuallyEq hevent
  apply Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
    rightJumpLyapunov t (-2 * Real.exp (-2 * t))
    (-2 * rightJumpLyapunov t) hderiv
  simp [rightJumpLyapunov, ht]

theorem rightJumpLyapunov_satisfies_slope_on_rightBranch (t : ℝ) (ht : 1 ≤ t) :
    Tomabechi.Theorem1.RightSlopeBound rightJumpLyapunov t
      (-2 * rightJumpLyapunov t) := by
  have hinner : HasDerivAt (fun s : ℝ => -2 * s) (-2) t := by
    simpa using (hasDerivAt_id t).const_mul (-2)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-2 * s))
      (-2 * Real.exp (-2 * t)) t := by
    convert (Real.hasDerivAt_exp (-2 * t)).comp t hinner using 1
    · funext s
      rfl
    · ring
  have hbranch : HasDerivAt (fun s : ℝ => 2 * Real.exp (-2 * s))
      (-4 * Real.exp (-2 * t)) t := by
    convert (HasDerivAt.const_mul 2 hexp) using 1 <;> ring
  have hwithin : HasDerivWithinAt
      (fun s => 2 * Real.exp (-2 * s))
      (-4 * Real.exp (-2 * t)) (Set.Ici t) t :=
    hbranch.hasDerivWithinAt
  have hEq : ∀ s ∈ Set.Ici t,
      rightJumpLyapunov s = 2 * Real.exp (-2 * s) := by
    intro s hs
    have hle : 1 ≤ s := le_trans ht hs
    simp [rightJumpLyapunov, not_lt.mpr hle]
  have hfunction : HasDerivWithinAt rightJumpLyapunov
      (-4 * Real.exp (-2 * t)) (Set.Ici t) t :=
    hwithin.congr hEq (hEq t (Set.mem_Ici.mpr le_rfl))
  apply Tomabechi.Theorem1.rightSlopeBound_of_hasDerivWithinAt_le
    rightJumpLyapunov t (-4 * Real.exp (-2 * t))
    (-2 * rightJumpLyapunov t) hfunction
  simp [rightJumpLyapunov, not_lt.mpr ht]
  nlinarith

theorem rightJumpLyapunov_satisfies_slope_all_nonnegative_times (t : ℝ)
    (ht : 0 ≤ t) :
      Tomabechi.Theorem1.RightSlopeBound rightJumpLyapunov t
        (-2 * rightJumpLyapunov t) := by
  by_cases h : t < 1
  · exact rightJumpLyapunov_satisfies_slope_before_jump t h
  · exact rightJumpLyapunov_satisfies_slope_on_rightBranch t (le_of_not_gt h)

/-- For the scalar trajectory `x(t) = exp(-t)` toward zero, the witness
obeys the quadratic comparison `dist² ≤ W ≤ 2 dist²` at every time. -/
theorem rightJumpLyapunov_quadratic_comparison (t : ℝ) :
    Real.exp (-2 * t) ≤ rightJumpLyapunov t ∧
      rightJumpLyapunov t ≤ 2 * Real.exp (-2 * t) := by
  by_cases h : t < 1
  · rw [rightJumpLyapunov]
    simp only [if_pos h]
    constructor
    · exact le_of_eq rfl
    · have hp : 0 < Real.exp (-2 * t) := Real.exp_pos _
      nlinarith
  · rw [rightJumpLyapunov]
    simp only [if_neg h]
    constructor
    · have hp : 0 < Real.exp (-2 * t) := Real.exp_pos _
      nlinarith
    · exact le_of_eq rfl

/-- Without interval continuity, the right-slope hypothesis on `[0,1)` is
compatible with an upward jump at `1`, contradicting the endpoint decay
estimate. Thus continuity (or another hypothesis excluding such jumps) is a
mathematical requirement of the Grönwall step, not just a Lean convenience. -/
theorem rightSlopeBound_does_not_imply_endpoint_decay_without_continuity :
    (∀ t ≥ (0 : ℝ),
      Tomabechi.Theorem1.RightSlopeBound rightJumpLyapunov t
        (-2 * rightJumpLyapunov t) ∧
        Real.exp (-2 * t) ≤ rightJumpLyapunov t ∧
          rightJumpLyapunov t ≤ 2 * Real.exp (-2 * t)) ∧
      ¬ rightJumpLyapunov 1 ≤
        rightJumpLyapunov 0 * Real.exp (-(2 : ℝ) * (1 - 0)) := by
  constructor
  · intro t ht
    exact ⟨rightJumpLyapunov_satisfies_slope_all_nonnegative_times t ht,
      rightJumpLyapunov_quadratic_comparison t⟩
  · intro hdecay
    have hpos : 0 < Real.exp (-2 : ℝ) := Real.exp_pos _
    have hlarge : rightJumpLyapunov 1 = 2 * Real.exp (-2 : ℝ) := by
      norm_num [rightJumpLyapunov]
    have hsmall : rightJumpLyapunov 0 = 1 := by
      norm_num [rightJumpLyapunov]
    rw [hlarge, hsmall] at hdecay
    have htime : (1 : ℝ) - 0 = 1 := by norm_num
    rw [htime] at hdecay
    norm_num at hdecay
    nlinarith [hpos]

/-- The integrated theorem-26 convergence result under the source paper's
upper right-slope condition in (26-A). For each finite interval after `T`,
the Lyapunov path is continuous and satisfies its Dini decay bound; the
quadratic distance comparison and value modulus then give (26.2) and
`J*(x(t),t) → 0`. -/
theorem theorem26_full_conditional_convergence_of_rightSlopeBound
    {State : Type*} [PseudoMetricSpace State]
    (trajectory : ℝ → State) (alive : Set State)
    (optimalValue : State → ℝ → ℝ) (WAlong : ℝ → ℝ) (ω : ℝ → ℝ)
    (c₁ c₂ rate T : ℝ) (hc₁ : 0 < c₁) (_hc₂ : 0 < c₂)
    (hrate : 0 < rate)
    (hAlive : ∀ s ≥ T, trajectory s ∈ alive)
    (hTargetNonempty : ∀ s ≥ T,
      (theorem26ZeroValueTarget alive optimalValue s).Nonempty)
    (hTargetClosed : ∀ s ≥ T,
      IsClosed (theorem26ZeroValueTarget alive optimalValue s))
    (hWcontinuous : ∀ s ≥ T, ContinuousOn WAlong (Set.Icc T s))
    (hWnonneg : ∀ s ≥ T, 0 ≤ WAlong s)
    (hWdecay : ∀ s ≥ T, ∀ u ∈ Set.Ico T s,
      Tomabechi.Theorem1.RightSlopeBound WAlong u (-rate * WAlong u))
    (herror : ∀ s ≥ T,
      c₁ * (Metric.infDist (trajectory s)
        (theorem26ZeroValueTarget alive optimalValue s)) ^ 2 ≤ WAlong s)
    (hWupper : ∀ s ≥ T,
      WAlong s ≤ c₂ * (Metric.infDist (trajectory s)
        (theorem26ZeroValueTarget alive optimalValue s)) ^ 2)
    (ωcontinuous : ContinuousAt ω 0) (hωzero : ω 0 = 0)
    (h26C : ∀ s ≥ T,
      0 ≤ optimalValue (trajectory s) s ∧
        optimalValue (trajectory s) s ≤
          ω (Metric.infDist (trajectory s)
            (theorem26ZeroValueTarget alive optimalValue s))) :
    (∀ s ≥ T, trajectory s ∈ alive) ∧
    (∀ s ≥ T,
      WAlong s ≤ WAlong T * Real.exp (-rate * (s - T)) ∧
        Metric.infDist (trajectory s)
          (theorem26ZeroValueTarget alive optimalValue s) ≤
          Real.sqrt (WAlong T / c₁) * Real.exp (-(rate / 2) * (s - T))) ∧
    Filter.Tendsto (fun s => optimalValue (trajectory s) s)
      Filter.atTop (nhds 0) ∧
    (∀ s ≥ T, WAlong s = 0 ↔
      trajectory s ∈ theorem26ZeroValueTarget alive optimalValue s) := by
  have hvalue_nonneg : ∀ᶠ s in Filter.atTop,
      0 ≤ optimalValue (trajectory s) s := by
    filter_upwards [Filter.eventually_ge_atTop T] with s hs
    exact (h26C s hs).1
  have hvalue_bound : ∀ᶠ s in Filter.atTop,
      optimalValue (trajectory s) s ≤
        ω (Metric.infDist (trajectory s)
          (theorem26ZeroValueTarget alive optimalValue s)) := by
    filter_upwards [Filter.eventually_ge_atTop T] with s hs
    exact (h26C s hs).2
  have hdist_nonneg : ∀ s, 0 ≤ Metric.infDist (trajectory s)
      (theorem26ZeroValueTarget alive optimalValue s) := by
    intro s
    exact Metric.infDist_nonneg
  have hdist_bound : ∀ᶠ s in Filter.atTop,
      Metric.infDist (trajectory s)
        (theorem26ZeroValueTarget alive optimalValue s) ≤
          Real.sqrt (WAlong T / c₁) * Real.exp (-(rate / 2) * (s - T)) := by
    filter_upwards [Filter.eventually_ge_atTop T] with s hs
    exact (theorem26_lyapunov_exponential_decay_of_rightSlopeBound trajectory
      (theorem26ZeroValueTarget alive optimalValue) WAlong
      (fun u => Metric.infDist (trajectory u)
        (theorem26ZeroValueTarget alive optimalValue u))
      c₁ rate T s hc₁ hrate hs (hWcontinuous s hs) hWnonneg
      (hWdecay s hs) (by intro u hu; exact Metric.infDist_nonneg)
      (by intro u; rfl) (by intro u hu; exact herror u hu)).2
  have hdist_tendsto : Filter.Tendsto
      (fun s => Metric.infDist (trajectory s)
        (theorem26ZeroValueTarget alive optimalValue s))
      Filter.atTop (nhds 0) :=
    theorem26_exponential_bound_tendsto_zero _
      (Real.sqrt (WAlong T / c₁)) (rate / 2) T (by linarith)
      (Filter.Eventually.of_forall hdist_nonneg) hdist_bound
  have hvalue_tendsto := theorem26_value_tendsto_zero_of_distance_tendsto
    (fun s => optimalValue (trajectory s) s)
    (fun s => Metric.infDist (trajectory s)
      (theorem26ZeroValueTarget alive optimalValue s))
    ω ωcontinuous hωzero hdist_tendsto hvalue_nonneg hvalue_bound
  refine ⟨hAlive, ?_, hvalue_tendsto, ?_⟩
  · intro s hs
    exact theorem26_lyapunov_exponential_decay_of_rightSlopeBound trajectory
      (theorem26ZeroValueTarget alive optimalValue) WAlong
      (fun u => Metric.infDist (trajectory u)
        (theorem26ZeroValueTarget alive optimalValue u))
      c₁ rate T s hc₁ hrate hs (hWcontinuous s hs) hWnonneg
      (hWdecay s hs) (by intro u hu; exact Metric.infDist_nonneg)
      (by intro u; rfl) (by intro u hu; exact herror u hu)
  · intro s hs
    constructor
    · intro hWzero
      have hdist_sq :
          (Metric.infDist (trajectory s)
            (theorem26ZeroValueTarget alive optimalValue s)) ^ 2 ≤ 0 := by
        have := herror s hs
        nlinarith
      have hdist_zero : Metric.infDist (trajectory s)
          (theorem26ZeroValueTarget alive optimalValue s) = 0 := by
        nlinarith [sq_nonneg (Metric.infDist (trajectory s)
          (theorem26ZeroValueTarget alive optimalValue s))]
      exact (hTargetClosed s hs).mem_iff_infDist_zero
        (hTargetNonempty s hs) |>.mpr hdist_zero
    · intro hmem
      have hdist_zero : Metric.infDist (trajectory s)
          (theorem26ZeroValueTarget alive optimalValue s) = 0 :=
        Metric.infDist_zero_of_mem hmem
      have hWle : WAlong s ≤ 0 := by
        have hUpper := hWupper s hs
        rw [hdist_zero] at hUpper
        simpa using hUpper
      exact le_antisymm hWle (hWnonneg s hs)

/-- The theorem-26 conclusion in the regularity form stated by the paper's
common Lyapunov lemma: the pathwise Lyapunov function is absolutely
continuous on every finite interval. The Dini decrease and all remaining
26-A inputs are unchanged. -/
theorem theorem26_full_conditional_convergence_of_rightSlopeBound_of_ac
    {State : Type*} [PseudoMetricSpace State]
    (trajectory : ℝ → State) (alive : Set State)
    (optimalValue : State → ℝ → ℝ) (WAlong : ℝ → ℝ) (ω : ℝ → ℝ)
    (c₁ c₂ rate T : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hrate : 0 < rate)
    (hAlive : ∀ s ≥ T, trajectory s ∈ alive)
    (hTargetNonempty : ∀ s ≥ T,
      (theorem26ZeroValueTarget alive optimalValue s).Nonempty)
    (hTargetClosed : ∀ s ≥ T,
      IsClosed (theorem26ZeroValueTarget alive optimalValue s))
    (hWac : ∀ s ≥ T, AbsolutelyContinuousOnInterval WAlong T s)
    (hWnonneg : ∀ s ≥ T, 0 ≤ WAlong s)
    (hWdecay : ∀ s ≥ T, ∀ u ∈ Set.Ico T s,
      Tomabechi.Theorem1.RightSlopeBound WAlong u (-rate * WAlong u))
    (herror : ∀ s ≥ T,
      c₁ * (Metric.infDist (trajectory s)
        (theorem26ZeroValueTarget alive optimalValue s)) ^ 2 ≤ WAlong s)
    (hWupper : ∀ s ≥ T,
      WAlong s ≤ c₂ * (Metric.infDist (trajectory s)
        (theorem26ZeroValueTarget alive optimalValue s)) ^ 2)
    (ωcontinuous : ContinuousAt ω 0) (hωzero : ω 0 = 0)
    (h26C : ∀ s ≥ T,
      0 ≤ optimalValue (trajectory s) s ∧
        optimalValue (trajectory s) s ≤
          ω (Metric.infDist (trajectory s)
            (theorem26ZeroValueTarget alive optimalValue s))) :
    (∀ s ≥ T, trajectory s ∈ alive) ∧
    (∀ s ≥ T,
      WAlong s ≤ WAlong T * Real.exp (-rate * (s - T)) ∧
        Metric.infDist (trajectory s)
          (theorem26ZeroValueTarget alive optimalValue s) ≤
          Real.sqrt (WAlong T / c₁) * Real.exp (-(rate / 2) * (s - T))) ∧
    Filter.Tendsto (fun s => optimalValue (trajectory s) s)
      Filter.atTop (nhds 0) ∧
    (∀ s ≥ T, WAlong s = 0 ↔
      trajectory s ∈ theorem26ZeroValueTarget alive optimalValue s) := by
  exact theorem26_full_conditional_convergence_of_rightSlopeBound
    trajectory alive optimalValue WAlong ω c₁ c₂ rate T hc₁ hc₂ hrate
    hAlive hTargetNonempty hTargetClosed
    (fun s hs => by
      simpa [Set.uIcc_of_le hs] using (hWac s hs).continuousOn)
    hWnonneg hWdecay herror hWupper ωcontinuous hωzero h26C

/-- The full theorem-26 convergence conclusion for the trajectory generated
by the single feedback `π₀`, uniformly over every alive initial pair. The
pathwise hypotheses are stated on those closed-loop trajectories; this
prevents an unrelated trajectory from being substituted into (26.2). -/
theorem theorem26_commonFeedback_full_convergence_of_rightSlopeBound_of_ac
    {State Feedback : Type*} [PseudoMetricSpace State]
    (closedLoop : Feedback → State → ℝ → ℝ → State)
    (π₀ : Feedback) (alive : Set State)
    (optimalValue : State → ℝ → ℝ) (W : State → ℝ → ℝ) (ω : ℝ → ℝ)
    (c₁ c₂ rate : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hrate : 0 < rate)
    (hTrajectoryInitial : ∀ (x : State) (T : ℝ), x ∈ alive →
      closedLoop π₀ x T T = x)
    (hTrajectoryAlive : ∀ (x : State) (T s : ℝ), x ∈ alive → T ≤ s →
      closedLoop π₀ x T s ∈ alive)
    (hTargetNonempty : ∀ T : ℝ,
      (theorem26ZeroValueTarget alive optimalValue T).Nonempty)
    (hTargetClosed : ∀ T : ℝ,
      IsClosed (theorem26ZeroValueTarget alive optimalValue T))
    (hTargetInvariant : ∀ (x : State) (T s : ℝ),
      x ∈ theorem26ZeroValueTarget alive optimalValue T → T ≤ s →
      closedLoop π₀ x T s ∈ theorem26ZeroValueTarget alive optimalValue s)
    (hWac : ∀ (x : State) (T s : ℝ), x ∈ alive → T ≤ s →
      AbsolutelyContinuousOnInterval
        (fun u => W (closedLoop π₀ x T u) u) T s)
    (hWnonneg : ∀ (x : State) (T s : ℝ), x ∈ alive → T ≤ s →
      0 ≤ W (closedLoop π₀ x T s) s)
    (hWdecay : ∀ (x : State) (T u : ℝ), x ∈ alive → T ≤ u →
      Tomabechi.Theorem1.RightSlopeBound
        (fun s => W (closedLoop π₀ x T s) s) u
        (-rate * W (closedLoop π₀ x T u) u))
    (herror : ∀ (x : State) (T s : ℝ), x ∈ alive → T ≤ s →
      c₁ * (Metric.infDist (closedLoop π₀ x T s)
        (theorem26ZeroValueTarget alive optimalValue s)) ^ 2 ≤
          W (closedLoop π₀ x T s) s)
    (hWupper : ∀ (x : State) (T s : ℝ), x ∈ alive → T ≤ s →
      W (closedLoop π₀ x T s) s ≤ c₂ *
        (Metric.infDist (closedLoop π₀ x T s)
          (theorem26ZeroValueTarget alive optimalValue s)) ^ 2)
    (ωcontinuous : ContinuousAt ω 0) (hωzero : ω 0 = 0)
    (h26C : ∀ (y : State) (t : ℝ), y ∈ alive →
      0 ≤ optimalValue y t ∧ optimalValue y t ≤
        ω (Metric.infDist y (theorem26ZeroValueTarget alive optimalValue t))) :
    ∀ (x : State) (T : ℝ), x ∈ alive →
      (∀ s ≥ T,
        W (closedLoop π₀ x T s) s ≤ W x T * Real.exp (-rate * (s - T)) ∧
          Metric.infDist (closedLoop π₀ x T s)
            (theorem26ZeroValueTarget alive optimalValue s) ≤
            Real.sqrt (W x T / c₁) * Real.exp (-(rate / 2) * (s - T))) ∧
      Filter.Tendsto (fun s => optimalValue (closedLoop π₀ x T s) s)
        Filter.atTop (nhds 0) ∧
      (∀ s ≥ T, W (closedLoop π₀ x T s) s = 0 ↔
        closedLoop π₀ x T s ∈ theorem26ZeroValueTarget alive optimalValue s) ∧
      (∀ s ≥ T, x ∈ theorem26ZeroValueTarget alive optimalValue T →
        closedLoop π₀ x T s ∈ theorem26ZeroValueTarget alive optimalValue s) := by
  intro x T hx
  let trajectory : ℝ → State := fun s => closedLoop π₀ x T s
  let WAlong : ℝ → ℝ := fun s => W (closedLoop π₀ x T s) s
  have hresult := theorem26_full_conditional_convergence_of_rightSlopeBound_of_ac
    trajectory alive optimalValue WAlong ω c₁ c₂ rate T hc₁ hc₂ hrate
    (by intro s hs; exact hTrajectoryAlive x T s hx hs)
    (by intro s hs; exact hTargetNonempty s)
    (by intro s hs; exact hTargetClosed s)
    (by
      intro s hs
      simpa [WAlong] using hWac x T s hx hs)
    (by intro s hs; exact hWnonneg x T s hx hs)
    (by
      intro s hs u hu
      simpa [WAlong] using hWdecay x T u hx hu.1)
    (by intro s hs; exact herror x T s hx hs)
    (by intro s hs; exact hWupper x T s hx hs)
    ωcontinuous hωzero
    (by
      intro s hs
      exact h26C (closedLoop π₀ x T s) s
        (hTrajectoryAlive x T s hx hs))
  rcases hresult with ⟨_, hdecay, hvalueTendsto, hzeroIff⟩
  refine ⟨?_, hvalueTendsto, ?_, ?_⟩
  · intro s hs
    simpa [WAlong, hTrajectoryInitial x T hx] using hdecay s hs
  · intro s hs
    simpa [WAlong] using hzeroIff s hs
  · intro s hs hmem
    exact hTargetInvariant x T s hmem hs

/-- Theorem 26's PZS characterization, with its actual zero-optimal-value
target definition. The implication is restricted to alive states, as in
equation (26.1). -/
theorem feedbackPZS_iff_mem_theorem26ZeroValueTarget
    {State Feedback : Type*} [MeasurableSpace ℝ]
    (μ : ℝ → MeasureTheory.Measure ℝ)
    (weight : ℝ → ℝ → ℝ)
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (π₀ : Feedback) (alive : Set State)
    (optimalValue : State → ℝ → ℝ)
    (x : State) (T : ℝ)
    (hweight : ∀ᵐ s ∂(μ T), 0 < weight T s)
    (hnonneg : ∀ π, admissible π x T →
      ∀ᵐ s ∂(μ T), 0 ≤ runningValue π x T s)
    (hint : ∀ π, admissible π x T →
      MeasureTheory.Integrable (fun s => weight T s * runningValue π x T s) (μ T))
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue x T = discountedFeedbackValue μ weight runningValue π₀ x T)
    (hminimal : ∀ π, admissible π x T →
      optimalValue x T ≤ discountedFeedbackValue μ weight runningValue π x T)
    (hx : x ∈ alive) :
    FeedbackPZS admissible μ runningValue x T ↔
      x ∈ theorem26ZeroValueTarget alive optimalValue T := by
  rw [feedbackPZS_iff_optimal_value_eq_zero μ weight runningValue admissible
    π₀ x T (optimalValue x T) hweight hnonneg hint hπ₀ hattains hminimal]
  simp [theorem26ZeroValueTarget, hx]

/-- The equation (26.1) form with the paper's exponential discount written
explicitly. `μ T` must be the future-time measure on `[T,∞)`; callers provide
the nonnegativity, integrability, common-feedback attainment, and global
optimality conditions from the theorem-26 model. -/
theorem feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount
    {State Feedback : Type*} [MeasurableSpace ℝ]
    (μ : ℝ → MeasureTheory.Measure ℝ) (ρ : ℝ)
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (π₀ : Feedback) (alive : Set State)
    (optimalValue : State → ℝ → ℝ)
    (x : State) (T : ℝ)
    (hnonneg : ∀ π, admissible π x T →
      ∀ᵐ s ∂(μ T), 0 ≤ runningValue π x T s)
    (hint : ∀ π, admissible π x T →
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight ρ T s * runningValue π x T s) (μ T))
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue x T = discountedFeedbackValue μ
      (theorem26DiscountWeight ρ) runningValue π₀ x T)
    (hminimal : ∀ π, admissible π x T →
      optimalValue x T ≤ discountedFeedbackValue μ
        (theorem26DiscountWeight ρ) runningValue π x T)
    (hx : x ∈ alive) :
    FeedbackPZS admissible μ runningValue x T ↔
      x ∈ theorem26ZeroValueTarget alive optimalValue T := by
  exact feedbackPZS_iff_mem_theorem26ZeroValueTarget μ
    (theorem26DiscountWeight ρ) runningValue admissible π₀ alive optimalValue
    x T (theorem26DiscountWeight_pos_ae (μ := μ T) ρ T) hnonneg hint hπ₀
    hattains hminimal hx

/-- The equation (26.1) PZS/target equivalence without assuming every
competitor has finite cost. Only the attained common optimal feedback needs
Bochner integrability; competitor minimality is stated with the extended
nonnegative integral, matching an infinite-horizon infimum. -/
theorem feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount_ennreal
    {State Feedback : Type*}
    (ρ : ℝ) (_hρ : 0 < ρ)
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (π₀ : Feedback) (alive : Set State)
    (optimalValue : State → ℝ → ℝ)
    (x : State) (T : ℝ)
    (hnonneg : ∀ π, admissible π x T →
      ∀ᵐ s ∂futureLebesgueMeasure T,
        0 ≤ runningValue π x T s)
    (hmeasurable : ∀ π, admissible π x T →
      Measurable (fun s => ENNReal.ofReal
        (theorem26DiscountWeight ρ T s * runningValue π x T s)))
    (hint₀ : MeasureTheory.Integrable
      (fun s => theorem26DiscountWeight ρ T s *
        runningValue π₀ x T s) (futureLebesgueMeasure T))
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue x T = ∫ s,
      theorem26DiscountWeight ρ T s * runningValue π₀ x T s
        ∂futureLebesgueMeasure T)
    (hminimal : ∀ π, admissible π x T →
      ENNReal.ofReal (optimalValue x T) ≤ ∫⁻ s,
        ENNReal.ofReal (theorem26DiscountWeight ρ T s *
          runningValue π x T s) ∂futureLebesgueMeasure T)
    (hx : x ∈ alive) :
    FeedbackPZS admissible (fun t => futureLebesgueMeasure t)
      (fun π y t s => runningValue π y t s) x T ↔
        x ∈ theorem26ZeroValueTarget alive optimalValue T := by
  have hclass := feedbackPZS_iff_optimal_value_eq_zero_of_lintegral
    (fun t => futureLebesgueMeasure t) (theorem26DiscountWeight ρ)
    runningValue admissible π₀ x T (optimalValue x T)
    (theorem26DiscountWeight_pos_ae ρ T) hnonneg hmeasurable hint₀ hπ₀
    (by simpa [discountedFeedbackValue] using hattains)
    (by intro π hπ; exact hminimal π hπ)
  rw [hclass]
  simp [theorem26ZeroValueTarget, hx]

/-- Theorem 26's PZS/target equivalence specialized to its stated common
Borel Markov feedback. A single measurable time-state control map `π₀` is
used for every admissible initial pair represented by this model. -/
theorem feedbackPZS_iff_mem_theorem26ZeroValueTarget_borelMarkov
    {State Control : Type*} [MeasurableSpace State] [MeasurableSpace Control]
    [MeasurableSpace ℝ]
    (μ : ℝ → MeasureTheory.Measure ℝ) (ρ : ℝ)
    (runningValue : BorelMarkovFeedback State Control → State → ℝ → ℝ → ℝ)
    (admissible : BorelMarkovFeedback State Control → State → ℝ → Prop)
    (π₀ : BorelMarkovFeedback State Control) (alive : Set State)
    (optimalValue : State → ℝ → ℝ)
    (x : State) (T : ℝ)
    (hnonneg : ∀ π, admissible π x T →
      ∀ᵐ s ∂(μ T), 0 ≤ runningValue π x T s)
    (hint : ∀ π, admissible π x T →
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight ρ T s * runningValue π x T s) (μ T))
    (hπ₀ : admissible π₀ x T)
    (hattains : optimalValue x T = discountedFeedbackValue μ
      (theorem26DiscountWeight ρ) runningValue π₀ x T)
    (hminimal : ∀ π, admissible π x T →
      optimalValue x T ≤ discountedFeedbackValue μ
        (theorem26DiscountWeight ρ) runningValue π x T)
    (hx : x ∈ alive) :
    FeedbackPZS admissible μ runningValue x T ↔
      x ∈ theorem26ZeroValueTarget alive optimalValue T := by
  exact feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount μ ρ
    runningValue admissible π₀ alive optimalValue x T hnonneg hint hπ₀
    hattains hminimal hx

/-- The invariant-target part of theorem 26: starting in `N(T)` keeps the
trajectory in the zero-optimal-value target, and attainment by the common
feedback turns the initial zero value into a permanent-zero-value policy.
The running-value conclusion is a.e. on the future measure supplied at the
initial pair. -/
theorem theorem26_invariant_target_implies_quiescence
    {State Feedback : Type*} [MeasurableSpace ℝ]
    (μ : ℝ → MeasureTheory.Measure ℝ) (weight : ℝ → ℝ → ℝ)
    (runningValue : Feedback → State → ℝ → ℝ → ℝ)
    (admissible : Feedback → State → ℝ → Prop)
    (π₀ : Feedback) (alive : Set State)
    (optimalValue : State → ℝ → ℝ) (N : ℝ → Set State)
    (trajectory : ℝ → State) (T : ℝ)
    (hN_eq : ∀ t, N t = theorem26ZeroValueTarget alive optimalValue t)
    (hxN : trajectory T ∈ N T)
    (hforward : ∀ s t, s ≤ t → trajectory s ∈ N s → trajectory t ∈ N t)
    (hweight : ∀ᵐ s ∂(μ T), 0 < weight T s)
    (hnonneg : ∀ᵐ s ∂(μ T), 0 ≤ runningValue π₀ (trajectory T) T s)
    (hint : MeasureTheory.Integrable
      (fun s => weight T s * runningValue π₀ (trajectory T) T s) (μ T))
    (hπ₀ : admissible π₀ (trajectory T) T)
    (hattains : optimalValue (trajectory T) T =
      discountedFeedbackValue μ weight runningValue π₀ (trajectory T) T) :
    (∀ t ≥ T, optimalValue (trajectory t) t = 0) ∧
      FeedbackPZS admissible μ runningValue (trajectory T) T ∧
      runningValue π₀ (trajectory T) T =ᵐ[μ T] 0 := by
  have hvalueAlong : ∀ t ≥ T, optimalValue (trajectory t) t = 0 := by
    intro t hTt
    have htarget : trajectory t ∈ theorem26ZeroValueTarget alive optimalValue t := by
      rw [← hN_eq t]
      exact hforward T t hTt hxN
    exact htarget.2
  have hcostZero : discountedFeedbackValue μ weight runningValue π₀
      (trajectory T) T = 0 := by
    rw [← hattains]
    exact hvalueAlong T le_rfl
  have hzeroAe : runningValue π₀ (trajectory T) T =ᵐ[μ T] 0 :=
    (nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero
      (weight T) (runningValue π₀ (trajectory T) T) hweight hnonneg hint).1
      (by simpa [discountedFeedbackValue] using hcostZero)
  refine ⟨hvalueAlong, ⟨π₀, hπ₀, hzeroAe⟩, hzeroAe⟩

/-- The cross-theorem classification (26.3): condition 24-A rules out PZS at
every abstraction below `⊤`, while theorem 26's common optimal feedback
identifies top-level PZS exactly with the alive zero-optimal-value target.
The common-feedback attainment and optimality hypotheses are quantified over
all alive initial pairs, preserving the source theorem's single-feedback
requirement. -/
theorem theorem24_26_pzs_classification
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*} [MeasurableSpace ℝ]
    (μ : ∀ a, ℝ → MeasureTheory.Measure ℝ)
    (weight : ∀ a, ℝ → ℝ → ℝ)
    (runningValue : ∀ a, Feedback a → State a → ℝ → ℝ → ℝ)
    (admissible : ∀ a, Feedback a → State a → ℝ → Prop)
    (π₀ : Feedback (⊤ : A)) (alive : Set (State (⊤ : A)))
    (optimalValue : State (⊤ : A) → ℝ → ℝ)
    (hcondition24A : ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ)
      (π : Feedback a), admissible a π x T →
      ¬ runningValue a π x T =ᵐ[μ a T] 0)
    (hweight : ∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      ∀ᵐ s ∂(μ (⊤ : A) T), 0 < weight (⊤ : A) T s)
    (hnonneg : ∀ (x : State (⊤ : A)) (T : ℝ) (π : Feedback (⊤ : A)),
      x ∈ alive → admissible (⊤ : A) π x T →
      ∀ᵐ s ∂(μ (⊤ : A) T), 0 ≤ runningValue (⊤ : A) π x T s)
    (hint : ∀ (x : State (⊤ : A)) (T : ℝ) (π : Feedback (⊤ : A)),
      x ∈ alive → admissible (⊤ : A) π x T →
      MeasureTheory.Integrable
        (fun s => weight (⊤ : A) T s * runningValue (⊤ : A) π x T s)
        (μ (⊤ : A) T))
    (hπ₀ : ∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      admissible (⊤ : A) π₀ x T)
    (hattains : ∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      optimalValue x T = discountedFeedbackValue (μ (⊤ : A)) (weight (⊤ : A))
        (runningValue (⊤ : A)) π₀ x T)
    (hminimal : ∀ (x : State (⊤ : A)) (T : ℝ) (π : Feedback (⊤ : A)),
      x ∈ alive → admissible (⊤ : A) π x T →
      optimalValue x T ≤ discountedFeedbackValue (μ (⊤ : A)) (weight (⊤ : A))
        (runningValue (⊤ : A)) π x T) :
    (∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ),
      ¬ FeedbackPZS (admissible a) (μ a) (runningValue a) x T) ∧
    (∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      (FeedbackPZS (admissible (⊤ : A)) (μ (⊤ : A))
          (runningValue (⊤ : A)) x T ↔
        x ∈ theorem26ZeroValueTarget alive optimalValue T)) := by
  constructor
  · intro a ha x T
    exact theorem24_no_feedbackPZS_of_condition24A
      (μ a) (runningValue a) (admissible a) x T
      (fun π hπ => hcondition24A a ha x T π hπ)
  · intro x T hx
    exact feedbackPZS_iff_mem_theorem26ZeroValueTarget
      (μ (⊤ : A)) (weight (⊤ : A)) (runningValue (⊤ : A))
      (admissible (⊤ : A)) π₀ alive
      optimalValue x T (hweight x T hx)
      (fun π hπ => hnonneg x T π hx hπ)
      (fun π hπ => hint x T π hx hπ)
      (hπ₀ x T hx) (hattains x T hx)
      (fun π hπ => hminimal x T π hx hπ) hx

/-- Equation (26.3) in the paper's concrete measure setup, in a Bochner
integral form that assumes each admissible top-level policy has finite cost.
The `_ennreal` variant below removes that restriction. -/
theorem theorem24_26_pzs_classification_expDiscount
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    (ρ : ℝ) (_hρ : 0 < ρ)
    (trajectory : ∀ a, Feedback a → State a → ℝ → ℝ → State a)
    (V : ∀ a, State a → ℝ → ℝ)
    (admissible : ∀ a, Feedback a → State a → ℝ → Prop)
    (π₀ : Feedback (⊤ : A)) (alive : Set (State (⊤ : A)))
    (optimalValue : State (⊤ : A) → ℝ → ℝ)
    (hcondition24A : ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ)
      (π : Feedback a), admissible a π x T →
      ¬ (fun s => V a (trajectory a π x T s) s) =ᵐ[futureLebesgueMeasure T] 0)
    (hnonneg : ∀ (x : State (⊤ : A)) (T : ℝ) (π : Feedback (⊤ : A)),
      x ∈ alive → admissible (⊤ : A) π x T →
      ∀ᵐ s ∂(futureLebesgueMeasure T),
        0 ≤ V (⊤ : A) (trajectory (⊤ : A) π x T s) s)
    (hint : ∀ (x : State (⊤ : A)) (T : ℝ) (π : Feedback (⊤ : A)),
      x ∈ alive → admissible (⊤ : A) π x T →
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight ρ T s *
          V (⊤ : A) (trajectory (⊤ : A) π x T s) s)
        (futureLebesgueMeasure T))
    (hπ₀ : ∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      admissible (⊤ : A) π₀ x T)
    (hattains : ∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      optimalValue x T = ∫ s, theorem26DiscountWeight ρ T s *
        V (⊤ : A) (trajectory (⊤ : A) π₀ x T s) s
          ∂(futureLebesgueMeasure T))
    (hminimal : ∀ (x : State (⊤ : A)) (T : ℝ) (π : Feedback (⊤ : A)),
      x ∈ alive → admissible (⊤ : A) π x T →
      optimalValue x T ≤ ∫ s, theorem26DiscountWeight ρ T s *
        V (⊤ : A) (trajectory (⊤ : A) π x T s) s
          ∂(futureLebesgueMeasure T)) :
    (∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ),
      ¬ FeedbackPZS (admissible a) futureLebesgueMeasure
        (fun π y t s => V a (trajectory a π y t s) s) x T) ∧
    (∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      (FeedbackPZS (admissible (⊤ : A))
          futureLebesgueMeasure
          (fun π y t s => V (⊤ : A) (trajectory (⊤ : A) π y t s) s) x T ↔
        x ∈ theorem26ZeroValueTarget alive optimalValue T)) := by
  let μ : ∀ a : A, ℝ → MeasureTheory.Measure ℝ :=
    fun _ T => futureLebesgueMeasure T
  let weight : ∀ a : A, ℝ → ℝ → ℝ :=
    fun _ T s => theorem26DiscountWeight ρ T s
  let runningValue : ∀ a : A, Feedback a → State a → ℝ → ℝ → ℝ :=
    fun a π x T s => V a (trajectory a π x T s) s
  have hweight : ∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      ∀ᵐ s ∂(μ (⊤ : A) T), 0 < weight (⊤ : A) T s := by
    intro x T hx
    exact theorem26DiscountWeight_pos_ae ρ T
  have hattains' : ∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      optimalValue x T = discountedFeedbackValue (μ (⊤ : A))
        (weight (⊤ : A)) (runningValue (⊤ : A)) π₀ x T := by
    intro x T hx
    simpa [μ, weight, runningValue, discountedFeedbackValue] using hattains x T hx
  have hminimal' : ∀ (x : State (⊤ : A)) (T : ℝ) (π : Feedback (⊤ : A)),
      x ∈ alive → admissible (⊤ : A) π x T →
      optimalValue x T ≤ discountedFeedbackValue (μ (⊤ : A))
        (weight (⊤ : A)) (runningValue (⊤ : A)) π x T := by
    intro x T π hx hπ
    simpa [μ, weight, runningValue, discountedFeedbackValue] using hminimal x T π hx hπ
  have hclassification := theorem24_26_pzs_classification μ weight
    runningValue admissible π₀ alive optimalValue
    (by
      intro a ha x T π hπ
      exact hcondition24A a ha x T π hπ)
    hweight
    (by
      intro x T π hx hπ
      simpa [μ, runningValue] using hnonneg x T π hx hπ)
    (by
      intro x T π hx hπ
      simpa [μ, weight, runningValue] using hint x T π hx hπ)
    hπ₀ hattains' hminimal'
  simpa [μ, weight, runningValue] using hclassification

/-- Source-faithful extended-cost form of (26.3). The unique feedback named
in the paper attains a finite real optimum, while other admissible policies
may have infinite discounted cost. The lower-level PZS exclusion is exactly
condition 24-A; at `⊤`, zero-cost attainability identifies PZS with `N_top`.
-/
theorem theorem24_26_pzs_classification_expDiscount_ennreal
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    (ρ : ℝ) (_hρ : 0 < ρ)
    (trajectory : ∀ a, Feedback a → State a → ℝ → ℝ → State a)
    (V : ∀ a, State a → ℝ → ℝ)
    (admissible : ∀ a, Feedback a → State a → ℝ → Prop)
    (π₀ : Feedback (⊤ : A)) (alive : Set (State (⊤ : A)))
    (optimalValue : State (⊤ : A) → ℝ → ℝ)
    (hcondition24A : ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ)
      (π : Feedback a), admissible a π x T →
      ¬ (fun s => V a (trajectory a π x T s) s) =ᵐ[futureLebesgueMeasure T] 0)
    (hnonneg : ∀ (x : State (⊤ : A)) (T : ℝ) (π : Feedback (⊤ : A)),
      x ∈ alive → admissible (⊤ : A) π x T →
      ∀ᵐ s ∂futureLebesgueMeasure T,
        0 ≤ V (⊤ : A) (trajectory (⊤ : A) π x T s) s)
    (hmeasurable : ∀ (x : State (⊤ : A)) (T : ℝ)
      (π : Feedback (⊤ : A)), x ∈ alive → admissible (⊤ : A) π x T →
      Measurable (fun s => ENNReal.ofReal (theorem26DiscountWeight ρ T s *
        V (⊤ : A) (trajectory (⊤ : A) π x T s) s)))
    (hint₀ : ∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight ρ T s *
          V (⊤ : A) (trajectory (⊤ : A) π₀ x T s) s)
        (futureLebesgueMeasure T))
    (hπ₀ : ∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      admissible (⊤ : A) π₀ x T)
    (hattains : ∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      optimalValue x T = ∫ s, theorem26DiscountWeight ρ T s *
        V (⊤ : A) (trajectory (⊤ : A) π₀ x T s) s
          ∂(futureLebesgueMeasure T))
    (hminimal : ∀ (x : State (⊤ : A)) (T : ℝ)
      (π : Feedback (⊤ : A)), x ∈ alive → admissible (⊤ : A) π x T →
      ENNReal.ofReal (optimalValue x T) ≤ ∫⁻ s,
        ENNReal.ofReal (theorem26DiscountWeight ρ T s *
          V (⊤ : A) (trajectory (⊤ : A) π x T s) s)
            ∂(futureLebesgueMeasure T)) :
    (∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ),
      ¬ FeedbackPZS (admissible a) futureLebesgueMeasure
        (fun π y t s => V a (trajectory a π y t s) s) x T) ∧
    (∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      (FeedbackPZS (admissible (⊤ : A)) futureLebesgueMeasure
          (fun π y t s => V (⊤ : A) (trajectory (⊤ : A) π y t s) s) x T ↔
        x ∈ theorem26ZeroValueTarget alive optimalValue T)) := by
  constructor
  · intro a ha x T
    exact theorem24_no_feedbackPZS_of_condition24A
      (futureLebesgueMeasure) (fun π y t s => V a (trajectory a π y t s) s)
      (admissible a) x T (fun π hπ => hcondition24A a ha x T π hπ)
  · intro x T hx
    exact feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount_ennreal
      ρ _hρ (fun π y t s => V (⊤ : A) (trajectory (⊤ : A) π y t s) s)
      (admissible (⊤ : A)) π₀ alive optimalValue x T
      (fun π hπ => hnonneg x T π hx hπ)
      (fun π hπ => hmeasurable x T π hx hπ)
      (hint₀ x T hx) (hπ₀ x T hx)
      (by simpa using hattains x T hx)
      (fun π hπ => hminimal x T π hx hπ) hx

/-- The top-level PZS/zero-value-target equivalence from theorem 26, using
the same common optimal feedback as theorem 24's data. All optimization
hypotheses are needed only at nonnegative initial times. -/
theorem theorem24_26_top_pzs_from_feedback_attainment
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    (D : Theorem24NonnegativeTimeData State Feedback)
    (π₀ : Feedback (⊤ : A)) (alive : Set (State (⊤ : A)))
    (x : State (⊤ : A)) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ alive)
    (hπ₀ : D.admissible (⊤ : A) π₀ x T)
    (hint₀ : MeasureTheory.Integrable
      (fun s => theorem26DiscountWeight D.rho T s *
        D.runningCost (⊤ : A) π₀
          (D.trajectory (⊤ : A) π₀ x T s) s)
      (futureLebesgueMeasure T))
    (hattains₀ : D.optimalValue (⊤ : A) x T = ∫ s,
      theorem26DiscountWeight D.rho T s *
        D.runningCost (⊤ : A) π₀
          (D.trajectory (⊤ : A) π₀ x T s) s
          ∂(futureLebesgueMeasure T)) :
    (FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
      (fun π y t s => D.runningCost (⊤ : A) π
        (D.trajectory (⊤ : A) π y t s) s) x T ↔
      x ∈ theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) T) := by
  exact feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount_ennreal
    D.rho D.rho_pos
    (fun π y t s => D.runningCost (⊤ : A) π
      (D.trajectory (⊤ : A) π y t s) s)
    (D.admissible (⊤ : A)) π₀ alive
    (D.optimalValue (⊤ : A)) x T
    (fun π hπ => Filter.Eventually.of_forall fun s =>
      D.runningCost_nonnegative (⊤ : A) π
        (D.trajectory (⊤ : A) π x T s) s)
    (fun π hπ => D.measurable_cost (⊤ : A) x T π hT hπ)
    hint₀ hπ₀ (by simpa [discountedFeedbackValue] using hattains₀)
    (fun π hπ => D.optimal_value_minimal (⊤ : A) x T π hT hπ) hx

theorem theorem24_26_top_pzs_from_nonnegativeTimeData
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    (D : Theorem24NonnegativeTimeData State Feedback)
    (π₀ : Feedback (⊤ : A)) (alive : Set (State (⊤ : A)))
    (hcommonFeedback : ∀ (x : State (⊤ : A)) (T : ℝ), 0 ≤ T → x ∈ alive →
      D.optimalPolicy (⊤ : A) x T = π₀) :
    ∀ (x : State (⊤ : A)) (T : ℝ), 0 ≤ T → x ∈ alive →
      (FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y t s => D.runningCost (⊤ : A) π
          (D.trajectory (⊤ : A) π y t s) s) x T ↔
        x ∈ theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) T) := by
  intro x T hT hx
  have hπ₀ : D.admissible (⊤ : A) π₀ x T := by
    rw [← hcommonFeedback x T hT hx]
    exact D.optimal_policy_admissible (⊤ : A) x T hT
  have hint₀ : MeasureTheory.Integrable
      (fun s => theorem26DiscountWeight D.rho T s *
        D.runningCost (⊤ : A) π₀
          (D.trajectory (⊤ : A) π₀ x T s) s)
      (futureLebesgueMeasure T) := by
    rw [← hcommonFeedback x T hT hx]
    exact D.optimal_cost_integrable (⊤ : A) x T hT
  have hattains₀ : D.optimalValue (⊤ : A) x T = ∫ s,
      theorem26DiscountWeight D.rho T s *
        D.runningCost (⊤ : A) π₀
          (D.trajectory (⊤ : A) π₀ x T s) s
          ∂(futureLebesgueMeasure T) := by
    rw [← hcommonFeedback x T hT hx]
    exact D.optimal_value_attained (⊤ : A) x T hT
  exact theorem24_26_top_pzs_from_feedback_attainment
    D π₀ alive x T hT hx hπ₀ hint₀ hattains₀

/-- Theorem 26's quantitative conclusion for one initial pair, using only
source-domain data at nonnegative times. The path is generated by the same
common feedback used in the top-level PZS classification. -/
theorem theorem26_convergence_from_nonnegativeTimeData
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [PseudoMetricSpace (State (⊤ : A))]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (π₀ : Feedback (⊤ : A)) (alive : Set (State (⊤ : A)))
    (hfeedbackAdmissible : ∀ (y : State (⊤ : A)) (t : ℝ),
      0 ≤ t → y ∈ alive → D.admissible (⊤ : A) π₀ y t)
    (W : State (⊤ : A) → ℝ → ℝ) (ω : ℝ → ℝ)
    (c₁ c₂ rate : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hrate : 0 < rate)
    (x : State (⊤ : A)) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ alive)
    (hTrajectoryAlive : ∀ s ≥ T,
      D.trajectory (⊤ : A) π₀ x T s ∈ alive)
    (hTargetNonempty : ∀ s ≥ T,
      (theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s).Nonempty)
    (hTargetClosed : ∀ s ≥ T,
      IsClosed (theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s))
    (hTargetInvariant : ∀ s ≥ T,
      x ∈ theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) T →
      D.trajectory (⊤ : A) π₀ x T s ∈
        theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s)
    (hWac : ∀ s ≥ T,
      AbsolutelyContinuousOnInterval
        (fun u => W (D.trajectory (⊤ : A) π₀ x T u) u) T s)
    (hWnonneg : ∀ s ≥ T,
      0 ≤ W (D.trajectory (⊤ : A) π₀ x T s) s)
    (hWdecay : ∀ s ≥ T, ∀ u ∈ Set.Ico T s,
      Tomabechi.Theorem1.RightSlopeBound
        (fun v => W (D.trajectory (⊤ : A) π₀ x T v) v) u
        (-rate * W (D.trajectory (⊤ : A) π₀ x T u) u))
    (herror : ∀ s ≥ T,
      c₁ * (Metric.infDist
        (D.trajectory (⊤ : A) π₀ x T s)
        (theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s)) ^ 2 ≤
          W (D.trajectory (⊤ : A) π₀ x T s) s)
    (hWupper : ∀ s ≥ T,
      W (D.trajectory (⊤ : A) π₀ x T s) s ≤ c₂ *
        (Metric.infDist (D.trajectory (⊤ : A) π₀ x T s)
          (theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s)) ^ 2)
    (ωcontinuous : ContinuousAt ω 0) (hωzero : ω 0 = 0)
    (h26C : ∀ s ≥ T,
      0 ≤ D.optimalValue (⊤ : A)
        (D.trajectory (⊤ : A) π₀ x T s) s ∧
      D.optimalValue (⊤ : A) (D.trajectory (⊤ : A) π₀ x T s) s ≤
        ω (Metric.infDist (D.trajectory (⊤ : A) π₀ x T s)
          (theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s))) :
    (∀ s ≥ T,
      W (D.trajectory (⊤ : A) π₀ x T s) s ≤ W x T *
          Real.exp (-rate * (s - T)) ∧
        Metric.infDist (D.trajectory (⊤ : A) π₀ x T s)
          (theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s) ≤
          Real.sqrt (W x T / c₁) * Real.exp (-(rate / 2) * (s - T))) ∧
    Filter.Tendsto
      (fun s => D.optimalValue (⊤ : A)
        (D.trajectory (⊤ : A) π₀ x T s) s)
      Filter.atTop (nhds 0) ∧
    (∀ s ≥ T,
      W (D.trajectory (⊤ : A) π₀ x T s) s = 0 ↔
        D.trajectory (⊤ : A) π₀ x T s ∈
          theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s) ∧
    (∀ s ≥ T,
      x ∈ theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) T →
      D.trajectory (⊤ : A) π₀ x T s ∈
        theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s) := by
  let path : ℝ → State (⊤ : A) :=
    fun s => D.trajectory (⊤ : A) π₀ x T s
  let WAlong : ℝ → ℝ := fun s => W (path s) s
  have hπ₀ : D.admissible (⊤ : A) π₀ x T := by
    exact hfeedbackAdmissible x T hT hx
  have hinitial : path T = x := by
    exact D.trajectory_initial (⊤ : A) π₀ x T hT hπ₀
  have hresult := theorem26_full_conditional_convergence_of_rightSlopeBound_of_ac
    path alive (D.optimalValue (⊤ : A)) WAlong ω c₁ c₂ rate T
    hc₁ hc₂ hrate
    (by intro s hs; exact hTrajectoryAlive s hs)
    hTargetNonempty hTargetClosed
    (by intro s hs; simpa [WAlong, path] using hWac s hs)
    (by intro s hs; exact hWnonneg s hs)
    (by
      intro s hs u hu
      simpa [WAlong, path] using hWdecay s hs u hu)
    (by intro s hs; exact herror s hs)
    (by intro s hs; exact hWupper s hs)
    ωcontinuous hωzero h26C
  rcases hresult with ⟨_, hdecay, hvalueTendsto, hzeroIff⟩
  refine ⟨?_, hvalueTendsto, ?_, ?_⟩
  · intro s hs
    simpa [WAlong, path, hinitial] using hdecay s hs
  · intro s hs
    simpa [WAlong, path] using hzeroIff s hs
  · intro s hs hmem
    exact hTargetInvariant s hs hmem

/-- The nonnegative-time assumptions for theorem 26's selected feedback
trajectory. On alive initial data the feedback itself attains the optimum;
no pointwise equality with a separately selected optimizer is imposed.
Every time-indexed analytic hypothesis is restricted to `t ≥ 0` or to a
future interval beginning at a nonnegative time. -/
structure Theorem26NonnegativeTimeDynamics
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [PseudoMetricSpace (State (⊤ : A))]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (Control : Type*) [MeasurableSpace (State (⊤ : A))]
    [BorelSpace (State (⊤ : A))] [TopologicalSpace Control]
    [MeasurableSpace Control] [BorelSpace Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))] where
  /-- The top-level policy class is exactly the class of Borel Markov maps
  on the paper's nonnegative time domain. -/
  policyEquiv : Feedback (⊤ : A) ≃
    NonnegativeTimeBorelMarkovFeedback (State (⊤ : A)) Control
  feedback : Feedback (⊤ : A)
  alive : Set (State (⊤ : A))
  /-- On alive initial data, the chosen Markov feedback itself is admissible
  and attains the optimum. This is the source-level property needed by PZS
  and the trajectory estimates; equality with an arbitrary selected
  `optimalPolicy` function is not required. -/
  feedback_attains_optimum : ∀ (x : State (⊤ : A)) (T : ℝ),
    0 ≤ T → x ∈ alive →
    D.admissible (⊤ : A) feedback x T ∧
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight D.rho T s *
          D.runningCost (⊤ : A) feedback
            (D.trajectory (⊤ : A) feedback x T s) s)
        (futureLebesgueMeasure T) ∧
      D.optimalValue (⊤ : A) x T = ∫ s,
        theorem26DiscountWeight D.rho T s *
          D.runningCost (⊤ : A) feedback
            (D.trajectory (⊤ : A) feedback x T s) s
            ∂(futureLebesgueMeasure T)
  W : State (⊤ : A) → ℝ → ℝ
  ω : ℝ → ℝ
  c₁ : ℝ
  c₂ : ℝ
  rate : ℝ
  c₁_pos : 0 < c₁
  c₂_pos : 0 < c₂
  rate_pos : 0 < rate
  trajectory_alive : ∀ (x : State (⊤ : A)) (T s : ℝ),
    0 ≤ T → x ∈ alive → T ≤ s →
    D.trajectory (⊤ : A) feedback x T s ∈ alive
  target_nonempty : ∀ T : ℝ, 0 ≤ T →
    (theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) T).Nonempty
  target_closed : ∀ T : ℝ, 0 ≤ T →
    IsClosed (theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) T)
  target_invariant : ∀ (x : State (⊤ : A)) (T s : ℝ), 0 ≤ T →
    x ∈ theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) T →
    T ≤ s →
    D.trajectory (⊤ : A) feedback x T s ∈
      theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s
  W_absolutelyContinuous : ∀ (x : State (⊤ : A)) (T s : ℝ),
    0 ≤ T → x ∈ alive → T ≤ s →
    AbsolutelyContinuousOnInterval
      (fun u => W (D.trajectory (⊤ : A) feedback x T u) u) T s
  W_nonnegative : ∀ (x : State (⊤ : A)) (T s : ℝ),
    0 ≤ T → x ∈ alive → T ≤ s →
    0 ≤ W (D.trajectory (⊤ : A) feedback x T s) s
  W_rightSlope : ∀ (x : State (⊤ : A)) (T u : ℝ),
    0 ≤ T → x ∈ alive → T ≤ u →
    Tomabechi.Theorem1.RightSlopeBound
      (fun s => W (D.trajectory (⊤ : A) feedback x T s) s) u
      (-rate * W (D.trajectory (⊤ : A) feedback x T u) u)
  W_lower_distance_bound : ∀ (x : State (⊤ : A)) (T s : ℝ),
    0 ≤ T → x ∈ alive → T ≤ s →
    c₁ * (Metric.infDist (D.trajectory (⊤ : A) feedback x T s)
      (theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s)) ^ 2 ≤
        W (D.trajectory (⊤ : A) feedback x T s) s
  W_upper_distance_bound : ∀ (x : State (⊤ : A)) (T s : ℝ),
    0 ≤ T → x ∈ alive → T ≤ s →
    W (D.trajectory (⊤ : A) feedback x T s) s ≤ c₂ *
      (Metric.infDist (D.trajectory (⊤ : A) feedback x T s)
        (theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) s)) ^ 2
  ω_continuous : ContinuousAt ω 0
  ω_zero : ω 0 = 0
  ω_nonnegative : ∀ r, 0 ≤ r → 0 ≤ ω r
  ω_monotone_on_nonnegative : ∀ r₁ r₂, 0 ≤ r₁ → r₁ ≤ r₂ → ω r₁ ≤ ω r₂
  value_distance_bound : ∀ (y : State (⊤ : A)) (t : ℝ),
    0 ≤ t → y ∈ alive →
    0 ≤ D.optimalValue (⊤ : A) y t ∧
      D.optimalValue (⊤ : A) y t ≤
        ω (Metric.infDist y (theorem26ZeroValueTarget alive
          (D.optimalValue (⊤ : A)) t))

/-- Source-time-domain integration of the lower-level theorem-24 conclusion,
the top-level PZS classification, and the quantitative theorem-26 result.
The theorem is uniform over every nonnegative initial pair; the proof is
assembled from pointwise results whose assumptions are stored in `D` and
`E`. -/
theorem theorem24_to26_from_nonnegativeTimeData
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [PseudoMetricSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace (State (⊤ : A))]
    [BorelSpace (State (⊤ : A))] [TopologicalSpace Control]
    [MeasurableSpace Control] [BorelSpace Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control) :
    ∀ (x : State (⊤ : A)) (T : ℝ), 0 ≤ T → x ∈ E.alive →
      (∀ a (ha : a < (⊤ : A)) (y : State a),
        0 < D.optimalValue a y T ∧
          ¬ FeedbackPZS (D.admissible a)
            (fun _ => futureLebesgueMeasure T)
            (fun π z t s => D.runningCost a π
              (D.trajectory a π z t s) s) y T) ∧
      (FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y t s => D.runningCost (⊤ : A) π
          (D.trajectory (⊤ : A) π y t s) s) x T ↔
        x ∈ theorem26ZeroValueTarget E.alive
          (D.optimalValue (⊤ : A)) T) ∧
      (∀ s ≥ T,
        E.W (D.trajectory (⊤ : A) E.feedback x T s) s ≤ E.W x T *
            Real.exp (-E.rate * (s - T)) ∧
          Metric.infDist (D.trajectory (⊤ : A) E.feedback x T s)
            (theorem26ZeroValueTarget E.alive
              (D.optimalValue (⊤ : A)) s) ≤
            Real.sqrt (E.W x T / E.c₁) *
              Real.exp (-(E.rate / 2) * (s - T))) ∧
      Filter.Tendsto
        (fun s => D.optimalValue (⊤ : A)
          (D.trajectory (⊤ : A) E.feedback x T s) s)
        Filter.atTop (nhds 0) ∧
      (∀ s ≥ T,
        E.W (D.trajectory (⊤ : A) E.feedback x T s) s = 0 ↔
          D.trajectory (⊤ : A) E.feedback x T s ∈
            theorem26ZeroValueTarget E.alive
              (D.optimalValue (⊤ : A)) s) ∧
      (∀ s ≥ T,
        x ∈ theorem26ZeroValueTarget E.alive
          (D.optimalValue (⊤ : A)) T →
        D.trajectory (⊤ : A) E.feedback x T s ∈
          theorem26ZeroValueTarget E.alive
            (D.optimalValue (⊤ : A)) s) := by
  intro x T hT hx
  refine ⟨?_, ?_, ?_⟩
  · intro a ha y
    exact theorem24_lower_conclusions_from_nonnegativeTimeData D a ha y T hT
  · exact theorem24_26_top_pzs_from_feedback_attainment
      D E.feedback E.alive x T hT hx
      (E.feedback_attains_optimum x T hT hx).1
      (E.feedback_attains_optimum x T hT hx).2.1
      (E.feedback_attains_optimum x T hT hx).2.2
  · exact theorem26_convergence_from_nonnegativeTimeData
      D E.feedback E.alive
      (by
        intro y t ht hy
        exact (E.feedback_attains_optimum y t ht hy).1)
      E.W E.ω E.c₁ E.c₂ E.rate
      E.c₁_pos E.c₂_pos E.rate_pos x T hT hx
      (fun s hs => E.trajectory_alive x T s hT hx hs)
      (fun s hs => E.target_nonempty s (le_trans hT hs))
      (fun s hs => E.target_closed s (le_trans hT hs))
      (fun s hs hmem => E.target_invariant x T s hT hmem hs)
      (fun s hs => E.W_absolutelyContinuous x T s hT hx hs)
      (fun s hs => E.W_nonnegative x T s hT hx hs)
      (by
        intro s hs u hu
        exact E.W_rightSlope x T u hT hx hu.1)
      (fun s hs => E.W_lower_distance_bound x T s hT hx hs)
      (fun s hs => E.W_upper_distance_bound x T s hT hx hs)
      E.ω_continuous E.ω_zero
      (by
        intro s hs
        exact E.value_distance_bound
          (D.trajectory (⊤ : A) E.feedback x T s) s
          (le_trans hT hs) (E.trajectory_alive x T s hT hx hs))

/-- All-real-time extension of the general-condition integration of theorem
24 with theorem 26. The paper states the initial-time conclusions for `T ≥ 0`;
this bundled extension assumes its trajectory and optimization data for every
real `T`, which is stronger than the source time domain. The same
selected optimal policy is used at every level; at `⊤` it is the single
feedback `π₀` for all alive initial pairs. The result combines strict
positive optimal value and PZS exclusion below `⊤`, the top-level PZS/zero
value-set equivalence, and quantitative theorem-26 convergence along the
closed-loop trajectories generated by that same feedback. -/
theorem theorem24_to26_general_conditions_allRealTimeExtension
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [PseudoMetricSpace (State (⊤ : A))]
    (ρ : ℝ) (hρ : 0 < ρ)
    (trajectory : ∀ a, Feedback a → State a → ℝ → ℝ → State a)
    (V : ∀ a, State a → ℝ → ℝ)
    (admissible : ∀ a, Feedback a → State a → ℝ → Prop)
    (optimalValue : ∀ a, State a → ℝ → ℝ)
    (optimalPolicy : ∀ a (x : State a) (T : ℝ), Feedback a)
    (π₀ : Feedback (⊤ : A)) (alive : Set (State (⊤ : A)))
    (htrajectory_initial : ∀ a (π : Feedback a) (x : State a) (T : ℝ),
      admissible a π x T → trajectory a π x T T = x)
    (hnonneg : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T →
      ∀ᵐ s ∂(futureLebesgueMeasure T),
        0 ≤ V a (trajectory a π x T s) s)
    (hmeasurable : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T →
      Measurable (fun s => ENNReal.ofReal (theorem26DiscountWeight ρ T s *
        V a (trajectory a π x T s) s)))
    (hintOptimal : ∀ a (x : State a) (T : ℝ),
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight ρ T s *
          V a (trajectory a (optimalPolicy a x T) x T s) s)
        (futureLebesgueMeasure T))
    (hoptimalPolicy : ∀ a (x : State a) (T : ℝ),
      admissible a (optimalPolicy a x T) x T)
    (hcommonFeedback : ∀ (x : State (⊤ : A)) (T : ℝ),
      x ∈ alive → optimalPolicy (⊤ : A) x T = π₀)
    (hattains : ∀ a (x : State a) (T : ℝ),
      optimalValue a x T = ∫ s, theorem26DiscountWeight ρ T s *
        V a (trajectory a (optimalPolicy a x T) x T s) s
          ∂(futureLebesgueMeasure T))
    (hminimal : ∀ a (x : State a) (T : ℝ) (π : Feedback a),
      admissible a π x T → ENNReal.ofReal (optimalValue a x T) ≤ ∫⁻ s,
        ENNReal.ofReal (theorem26DiscountWeight ρ T s *
          V a (trajectory a π x T s) s) ∂(futureLebesgueMeasure T))
    (hcondition24A : ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ)
      (π : Feedback a), admissible a π x T →
      ¬ (fun s => V a (trajectory a π x T s) s) =ᵐ[futureLebesgueMeasure T] 0)
    (W : State (⊤ : A) → ℝ → ℝ) (ω : ℝ → ℝ)
    (c₁ c₂ rate : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hrate : 0 < rate)
    (hTrajectoryAlive : ∀ (x : State (⊤ : A)) (T s : ℝ),
      x ∈ alive → T ≤ s → trajectory (⊤ : A) π₀ x T s ∈ alive)
    (hTargetNonempty : ∀ T : ℝ,
      (theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) T).Nonempty)
    (hTargetClosed : ∀ T : ℝ,
      IsClosed (theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) T))
    (hTargetInvariant : ∀ (x : State (⊤ : A)) (T s : ℝ),
      x ∈ theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) T → T ≤ s →
      trajectory (⊤ : A) π₀ x T s ∈
        theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) s)
    (hWac : ∀ (x : State (⊤ : A)) (T s : ℝ), x ∈ alive → T ≤ s →
      AbsolutelyContinuousOnInterval
        (fun u => W (trajectory (⊤ : A) π₀ x T u) u) T s)
    (hWnonneg : ∀ (x : State (⊤ : A)) (T s : ℝ),
      x ∈ alive → T ≤ s →
      0 ≤ W (trajectory (⊤ : A) π₀ x T s) s)
    (hWdecay : ∀ (x : State (⊤ : A)) (T u : ℝ),
      x ∈ alive → T ≤ u →
      Tomabechi.Theorem1.RightSlopeBound
        (fun s => W (trajectory (⊤ : A) π₀ x T s) s) u
        (-rate * W (trajectory (⊤ : A) π₀ x T u) u))
    (herror : ∀ (x : State (⊤ : A)) (T s : ℝ),
      x ∈ alive → T ≤ s →
      c₁ * (Metric.infDist (trajectory (⊤ : A) π₀ x T s)
        (theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) s)) ^ 2 ≤
          W (trajectory (⊤ : A) π₀ x T s) s)
    (hWupper : ∀ (x : State (⊤ : A)) (T s : ℝ),
      x ∈ alive → T ≤ s →
      W (trajectory (⊤ : A) π₀ x T s) s ≤ c₂ *
        (Metric.infDist (trajectory (⊤ : A) π₀ x T s)
          (theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) s)) ^ 2)
    (ωcontinuous : ContinuousAt ω 0) (hωzero : ω 0 = 0)
    (h26C : ∀ (y : State (⊤ : A)) (t : ℝ), y ∈ alive →
      0 ≤ optimalValue (⊤ : A) y t ∧
        optimalValue (⊤ : A) y t ≤ ω (Metric.infDist y
          (theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) t))) :
    (∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ),
      0 < optimalValue a x T) ∧
    (∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ),
      ¬ FeedbackPZS (admissible a) (fun _ => futureLebesgueMeasure T)
        (fun π y t s => V a (trajectory a π y t s) s) x T) ∧
    (∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      (FeedbackPZS (admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y t s => V (⊤ : A) (trajectory (⊤ : A) π y t s) s) x T ↔
        x ∈ theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) T)) ∧
    (∀ (x : State (⊤ : A)) (T : ℝ), x ∈ alive →
      (∀ s ≥ T,
        W (trajectory (⊤ : A) π₀ x T s) s ≤ W x T *
            Real.exp (-rate * (s - T)) ∧
          Metric.infDist (trajectory (⊤ : A) π₀ x T s)
            (theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) s) ≤
            Real.sqrt (W x T / c₁) * Real.exp (-(rate / 2) * (s - T))) ∧
      Filter.Tendsto
        (fun s => optimalValue (⊤ : A) (trajectory (⊤ : A) π₀ x T s) s)
        Filter.atTop (nhds 0) ∧
      (∀ s ≥ T, W (trajectory (⊤ : A) π₀ x T s) s = 0 ↔
        trajectory (⊤ : A) π₀ x T s ∈
          theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) s) ∧
      (∀ s ≥ T, x ∈
        theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) T →
        trajectory (⊤ : A) π₀ x T s ∈
          theorem26ZeroValueTarget alive (optimalValue (⊤ : A)) s)) := by
  have hpositive := theorem24_positive_all_lower_levels_expDiscount_ennreal
    ρ hρ trajectory V admissible optimalValue htrajectory_initial optimalPolicy
    hnonneg hmeasurable hintOptimal hoptimalPolicy hattains hminimal hcondition24A
  have hclassification := theorem24_26_pzs_classification_expDiscount_ennreal
    ρ hρ trajectory V admissible π₀ alive (optimalValue (⊤ : A)) hcondition24A
    (by
      intro x T π hx hπ
      exact hnonneg (⊤ : A) x T π hπ)
    (by
      intro x T π hx hπ
      exact hmeasurable (⊤ : A) x T π hπ)
    (by
      intro x T hx
      simpa [hcommonFeedback x T hx] using hintOptimal (⊤ : A) x T)
    (by
      intro x T hx
      simpa [hcommonFeedback x T hx] using hoptimalPolicy (⊤ : A) x T)
    (by
      intro x T hx
      simpa [hcommonFeedback x T hx] using hattains (⊤ : A) x T)
    (by
      intro x T π hx hπ
      exact hminimal (⊤ : A) x T π hπ)
  have hconvergence := theorem26_commonFeedback_full_convergence_of_rightSlopeBound_of_ac
    (trajectory (⊤ : A)) π₀ alive (optimalValue (⊤ : A)) W ω c₁ c₂ rate
    hc₁ hc₂ hrate
    (by
      intro x T hx
      exact htrajectory_initial (⊤ : A) π₀ x T
        (by simpa [hcommonFeedback x T hx] using hoptimalPolicy (⊤ : A) x T))
    hTrajectoryAlive hTargetNonempty hTargetClosed hTargetInvariant
    hWac hWnonneg hWdecay herror hWupper ωcontinuous hωzero h26C
  refine ⟨?_, ?_, hclassification.2, hconvergence⟩
  · intro a ha x T
    exact (hpositive a ha x T).1
  · intro a ha x T
    exact (hpositive a ha x T).2

end Tomabechi.Theorem24_26

#print axioms Tomabechi.Theorem24_26.theorem24_26_top_pzs_from_feedback_attainment
#print axioms Tomabechi.Theorem24_26.theorem26_convergence_from_nonnegativeTimeData
#print axioms Tomabechi.Theorem24_26.theorem24_to26_from_nonnegativeTimeData
