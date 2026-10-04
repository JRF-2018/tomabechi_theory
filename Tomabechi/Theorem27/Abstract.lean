import Theorem24_26

/-! 定理27の型付き状態と無明分類に関する抽象核。-/

namespace Tomabechi.Theorem27

open _root_.Tomabechi.Theorem24_26

/-- Typed state domain from (27.2): every lower abstraction level carries
its own state type, while the top level is restricted to the alive region's
state type. -/
def TypedState27 {A : Type*} [PartialOrder A] [OrderTop A]
    (State : A → Type*) (alive : Set (State ⊤)) :=
  Sum (Σ a : {a : A // a < (⊤ : A)}, State a.1) {x : State ⊤ // x ∈ alive}

/-- Permanent zero-suffering predicate on the typed disjoint union.  It is
inherited from theorem 24 below the top level and theorem 26 at the top. -/
def pzsOnTypedState27 {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*}
    (PZS : ∀ a, State a → ℝ → Prop) (alive : Set (State ⊤))
    (s : TypedState27 State alive) (T : ℝ) : Prop :=
  match s with
  | .inl ⟨a, x⟩ => PZS a.1 x T
  | .inr x => PZS ⊤ x.1 T

/-- Definition (27.1): operational ignorance is failure of permanent
zero-suffering at the typed state and initial time. -/
def operationalIgnorance27 {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*}
    (PZS : ∀ a, State a → ℝ → Prop) (alive : Set (State ⊤))
    (s : TypedState27 State alive) (T : ℝ) : Prop :=
  ¬pzsOnTypedState27 PZS alive s T

/-- Classification (27.2), conditional on the inherited theorem 24/26
equivalences: every lower-level state is operationally ignorant, while at the
top level ignorance is exactly exclusion from the zero-residual target. -/
theorem operationalIgnorance27_classification
    {A : Type*} [PartialOrder A] [OrderTop A] {State : A → Type*}
    (PZS : ∀ a, State a → ℝ → Prop) (alive : Set (State ⊤))
    (N : ℝ → Set (State ⊤))
    (hbelow : ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ),
      ¬PZS a x T)
    (htop : ∀ (x : State ⊤) (T : ℝ), PZS ⊤ x T ↔ x ∈ N T)
    (s : TypedState27 State alive) (T : ℝ) :
    operationalIgnorance27 PZS alive s T ↔
      match s with
      | .inl _ => True
      | .inr x => x.1 ∉ N T := by
  cases s with
  | inl lower =>
      rcases lower with ⟨⟨a, ha⟩, x⟩
      simp [operationalIgnorance27, pzsOnTypedState27, hbelow a ha x T]
  | inr x =>
      simp [operationalIgnorance27, pzsOnTypedState27, htop x.1 T]

/-- Equation (27.2) with the lower-abstraction branch derived from
condition 24-A at every lower level and every initial pair.  The top-level
PZS/target equivalence is still supplied by theorem 26, while the lower-level
policy, state, and future-measure models may depend on the abstraction. -/
theorem theorem27_classification_of_condition24A
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    (alive : Set (State ⊤))
    (μ : ∀ a, ℝ → MeasureTheory.Measure ℝ)
    (runningValue : ∀ a, Feedback a → State a → ℝ → ℝ → ℝ)
    (admissible : ∀ a, Feedback a → State a → ℝ → Prop)
    (hcondition24A : ∀ a (ha : a < (⊤ : A)) (x : State a) (T : ℝ)
      (π : Feedback a), admissible a π x T →
      ¬ runningValue a π x T =ᵐ[μ a T] 0)
    (N : ℝ → Set (State ⊤))
    (htop : ∀ (x : State ⊤) (T : ℝ),
      FeedbackPZS (admissible ⊤) (μ ⊤) (runningValue ⊤) x T ↔ x ∈ N T)
    (s : TypedState27 State alive) (T : ℝ) :
    operationalIgnorance27
        (fun a x t => FeedbackPZS (admissible a) (μ a) (runningValue a) x t)
        alive s T ↔
      match s with
      | .inl _ => True
      | .inr x => x.1 ∉ N T := by
  apply operationalIgnorance27_classification
    (PZS := fun a x t =>
      FeedbackPZS (admissible a) (μ a) (runningValue a) x t)
    (alive := alive) N ?_ htop s T
  intro a ha x t
  exact theorem24_no_feedbackPZS_of_condition24A
    (μ a) (runningValue a) (admissible a) x t
    (fun π hπ => hcondition24A a ha x t π hπ)

/-- Equation (27.2)'s top-level branch, pointwise along a trajectory, from
the actual feedback-flow definition of PZS and `J*`. A single Markov
feedback is used at every initial pair; its restart consistency identifies
the cost from `(x t,t)` with the future segment of `x`. -/
theorem feedbackPZS_failure_iff_outside_theorem26_target
    {State U : Type*} [MeasurableSpace ℝ]
    (μ : ℝ → MeasureTheory.Measure ℝ) (ρ : ℝ)
    (flow : (ℝ → State → U) → State → ℝ → ℝ → State)
    (V : State → ℝ → ℝ)
    (admissible : (ℝ → State → U) → State → ℝ → Prop)
    (π₀ : ℝ → State → U) (alive : Set State)
    (optimalValue : State → ℝ → ℝ)
    (x : ℝ → State)
    (hfuture : ∀ t, ∀ᵐ s ∂(μ t), t ≤ s)
    (hflow : ∀ t s, t ≤ s → flow π₀ (x t) t s = x s)
    (hnonneg : ∀ t π, admissible π (x t) t →
      ∀ᵐ s ∂(μ t), 0 ≤ V (flow π (x t) t s) s)
    (hint : ∀ t π, admissible π (x t) t →
      MeasureTheory.Integrable
        (fun s => theorem26DiscountWeight ρ t s * V (flow π (x t) t s) s)
        (μ t))
    (hπ₀ : ∀ t, admissible π₀ (x t) t)
    (hvalue : ∀ t, optimalValue (x t) t =
      ∫ s, theorem26DiscountWeight ρ t s * V (x s) s ∂(μ t))
    (hminimal : ∀ t π, admissible π (x t) t →
      optimalValue (x t) t ≤ discountedFeedbackValue μ
        (theorem26DiscountWeight ρ)
        (fun π y T s => V (flow π y T s) s) π (x t) t)
    (halive : ∀ t, x t ∈ alive) :
    ∀ t, ¬FeedbackPZS admissible μ
        (fun π y T s => V (flow π y T s) s) (x t) t ↔
      x t ∉ theorem26ZeroValueTarget alive optimalValue t := by
  intro t
  have hpzsTarget := feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount
    (μ := μ) ρ (fun π y T s => V (flow π y T s) s) admissible π₀ alive
    optimalValue (x t) t (hnonneg t) (hint t) (hπ₀ t)
    (by
      calc
        optimalValue (x t) t =
            ∫ s, theorem26DiscountWeight ρ t s * V (x s) s ∂(μ t) := hvalue t
        _ = discountedFeedbackValue μ (theorem26DiscountWeight ρ)
            (fun π y T s => V (flow π y T s) s) π₀ (x t) t := by
          unfold discountedFeedbackValue
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hfuture t] with s hs
          rw [hflow t s hs])
    (hminimal t) (halive t)
  exact not_congr hpzsTarget

/-- Under the Lyapunov lower bound and strict decay assumption, every point
outside a nonempty closed zero-residual set has a strictly positive residual
descent rate, quantitatively bounded below by its squared distance to the set.

This is the metric-space form of equation (27.6), conditional on the
corresponding hypotheses from condition 26-A. -/
theorem residual_descent_of_outside_closed_target
    {X : Type*} [PseudoMetricSpace X]
    (N : Set X) (hN_closed : IsClosed N) (hN_nonempty : N.Nonempty)
    (W : X → ℝ) (x : X)
    (c₁ decayRate : ℝ) (hc₁ : 0 < c₁) (hdecayRate : 0 < decayRate)
    (descentRate : ℝ)
    (hW_lower : c₁ * (Metric.infDist x N) ^ 2 ≤ W x)
    (hW_decay : decayRate * W x ≤ descentRate)
    (hx : x ∉ N) :
    decayRate * c₁ * (Metric.infDist x N) ^ 2 ≤ descentRate ∧ 0 < descentRate := by
  have hdist : 0 < Metric.infDist x N :=
    (hN_closed.notMem_iff_infDist_pos hN_nonempty).mp hx
  have hquant : decayRate * c₁ * (Metric.infDist x N) ^ 2 ≤ descentRate := by
    have hmul := mul_le_mul_of_nonneg_left hW_lower (le_of_lt hdecayRate)
    nlinarith
  refine ⟨hquant, ?_⟩
  have hW_pos : 0 < W x := by
    have hsq : 0 < (Metric.infDist x N) ^ 2 := sq_pos_of_pos hdist
    nlinarith
  have : 0 < decayRate * W x := mul_pos hdecayRate hW_pos
  exact lt_of_lt_of_le this hW_decay

/-- Pointwise form of the first equivalence in (27.10).  The reverse
implication uses the zero-descent property on the invariant target, which in
the paper follows from forward invariance and `W = 0` on that target. -/
theorem outside_target_iff_positive_descent
    {X : Type*} [PseudoMetricSpace X]
    (N : Set X) (hN_closed : IsClosed N) (hN_nonempty : N.Nonempty)
    (W : X → ℝ) (x : X)
    (c₁ decayRate : ℝ) (hc₁ : 0 < c₁) (hdecayRate : 0 < decayRate)
    (descentRate : ℝ)
    (hW_lower : c₁ * (Metric.infDist x N) ^ 2 ≤ W x)
    (hW_decay : decayRate * W x ≤ descentRate)
    (hzero_on_target : x ∈ N → descentRate = 0) :
    x ∉ N ↔ 0 < descentRate := by
  constructor
  · intro hx
    exact (residual_descent_of_outside_closed_target N hN_closed hN_nonempty
      W x c₁ decayRate hc₁ hdecayRate descentRate hW_lower hW_decay hx).2
  · intro hpositive hx
    have hzero := hzero_on_target hx
    rw [hzero] at hpositive
    exact (lt_irrefl 0 hpositive)

/-- Almost-everywhere, time-dependent form of (27.6).  The zero-residual
target may vary with time; condition 26-A supplies its closedness,
nonemptiness, distance comparison, and Lyapunov decay at each relevant time.
-/
theorem ae_residual_descent_of_outside_closed_target
    {X : Type*} [PseudoMetricSpace X]
    (N : ℝ → Set X) (hNclosed : ∀ t, IsClosed (N t))
    (hNnonempty : ∀ t, (N t).Nonempty)
    (W : ℝ → X → ℝ) (x : ℝ → X)
    (c₁ decayRate : ℝ) (hc₁ : 0 < c₁) (hdecayRate : 0 < decayRate)
    (descentRate : ℝ → ℝ)
    (hWlower : ∀ᵐ t, c₁ * (Metric.infDist (x t) (N t)) ^ 2 ≤ W t (x t))
    (hWdecay : ∀ᵐ t, decayRate * W t (x t) ≤ descentRate t)
    (houtside : ∀ᵐ t, x t ∉ N t) :
    ∀ᵐ t,
      decayRate * c₁ * (Metric.infDist (x t) (N t)) ^ 2 ≤ descentRate t ∧
      0 < descentRate t := by
  filter_upwards [hWlower, hWdecay, houtside] with t hLower hDecay hOutside
  exact residual_descent_of_outside_closed_target (N t) (hNclosed t)
    (hNnonempty t) (W t) (x t) c₁ decayRate hc₁ hdecayRate
    (descentRate t) hLower hDecay hOutside

/-- Almost-everywhere, time-dependent form of the first equivalence in
(27.10).  The reverse implication uses zero descent on the invariant target.
-/
theorem ae_outside_target_iff_positive_descent
    {X : Type*} [PseudoMetricSpace X]
    (N : ℝ → Set X) (hNclosed : ∀ t, IsClosed (N t))
    (hNnonempty : ∀ t, (N t).Nonempty)
    (W : ℝ → X → ℝ) (x : ℝ → X)
    (c₁ decayRate : ℝ) (hc₁ : 0 < c₁) (hdecayRate : 0 < decayRate)
    (descentRate : ℝ → ℝ)
    (hWlower : ∀ᵐ t, c₁ * (Metric.infDist (x t) (N t)) ^ 2 ≤ W t (x t))
    (hWdecay : ∀ᵐ t, decayRate * W t (x t) ≤ descentRate t)
    (hzeroOnTarget : ∀ᵐ t, x t ∈ N t → descentRate t = 0) :
    ∀ᵐ t, x t ∉ N t ↔ 0 < descentRate t := by
  filter_upwards [hWlower, hWdecay, hzeroOnTarget] with t hLower hDecay hZero
  exact outside_target_iff_positive_descent (N t) (hNclosed t)
    (hNnonempty t) (W t) (x t) c₁ decayRate hc₁ hdecayRate
    (descentRate t) hLower hDecay hZero

/-- The zero-residual target used in the theorem 27 paper: the alive region
intersected with the zero set of the time-dependent Lyapunov residual. -/
def zeroResidualTarget {E : Type*} (alive : Set E)
    (W : ℝ × E → ℝ) (t : ℝ) : Set E :=
  alive ∩ {x | W (t, x) = 0}

/-- If the alive region is closed and the residual is continuous in state,
then the zero-residual target is closed, as used in 26-A. -/
theorem isClosed_zeroResidualTarget
    {E : Type*} [TopologicalSpace E]
    (alive : Set E) (W : ℝ × E → ℝ) (t : ℝ)
    (halive : IsClosed alive) (hW : Continuous fun x : E => W (t, x)) :
    IsClosed (zeroResidualTarget alive W t) := by
  exact halive.inter (isClosed_eq hW continuous_const)

/-- Membership in the zero-residual target entails zero Lyapunov residual. -/
theorem residual_eq_zero_of_mem_zeroResidualTarget
    {E : Type*} (alive : Set E) (W : ℝ × E → ℝ) (t : ℝ) (x : E)
    (hx : x ∈ zeroResidualTarget alive W t) : W (t, x) = 0 :=
  hx.2

/-- On the alive region, the lower distance estimate in 26-A makes zero
Lyapunov residual equivalent to membership in the zero-residual target. -/
theorem residual_eq_zero_iff_mem_zeroResidualTarget
    {E : Type*} [PseudoMetricSpace E]
    (alive : Set E) (W : ℝ × E → ℝ) (t : ℝ)
    (hNclosed : IsClosed (zeroResidualTarget alive W t))
    (hNnonempty : (zeroResidualTarget alive W t).Nonempty)
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (x : E) (hxAlive : x ∈ alive)
    (hWlower : x ∈ alive → c₁ *
      (Metric.infDist x (zeroResidualTarget alive W t)) ^ 2 ≤ W (t, x)) :
    W (t, x) = 0 ↔ x ∈ zeroResidualTarget alive W t := by
  constructor
  · intro hWzero
    have hdistSq :
        (Metric.infDist x (zeroResidualTarget alive W t)) ^ 2 = 0 := by
      nlinarith [sq_nonneg (Metric.infDist x (zeroResidualTarget alive W t)),
        hWlower hxAlive]
    have hdist : Metric.infDist x (zeroResidualTarget alive W t) = 0 :=
      (sq_eq_zero_iff).mp hdistSq
    exact (hNclosed.mem_iff_infDist_zero hNnonempty).2 hdist
  · exact residual_eq_zero_of_mem_zeroResidualTarget alive W t x

/-- On alive states, the same estimate and closed target characterize
operational ignorance by strict positivity of the residual. -/
theorem residual_positive_iff_outside_zeroResidualTarget
    {E : Type*} [PseudoMetricSpace E]
    (alive : Set E) (W : ℝ × E → ℝ) (t : ℝ)
    (hNclosed : IsClosed (zeroResidualTarget alive W t))
    (hNnonempty : (zeroResidualTarget alive W t).Nonempty)
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (x : E) (hxAlive : x ∈ alive)
    (hWlower : x ∈ alive → c₁ *
      (Metric.infDist x (zeroResidualTarget alive W t)) ^ 2 ≤ W (t, x)) :
    0 < W (t, x) ↔ x ∉ zeroResidualTarget alive W t := by
  constructor
  · intro hWpos hmem
    have hzero := residual_eq_zero_of_mem_zeroResidualTarget alive W t x hmem
    rw [hzero] at hWpos
    exact (lt_irrefl (0 : ℝ) hWpos)
  · intro houtside
    have hdist :
        0 < Metric.infDist x (zeroResidualTarget alive W t) :=
      (hNclosed.notMem_iff_infDist_pos hNnonempty).mp houtside
    have hsq :
        0 < (Metric.infDist x (zeroResidualTarget alive W t)) ^ 2 :=
      sq_pos_of_pos hdist
    nlinarith [hWlower hxAlive]

/-- The full two-sided distance estimate (26.A) characterizes the zero set
of the Lyapunov residual by the closed target itself. This applies when the
target is defined independently as the zero optimal-value set in (26.1). -/
theorem residual_eq_zero_iff_mem_closed_target
    {E : Type*} [PseudoMetricSpace E]
    (N alive : Set E) (W : E → ℝ)
    (hNclosed : IsClosed N) (hNnonempty : N.Nonempty)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hLower : ∀ x ∈ alive, c₁ * (Metric.infDist x N) ^ 2 ≤ W x)
    (hUpper : ∀ x ∈ alive, W x ≤ c₂ * (Metric.infDist x N) ^ 2)
    (x : E) (hxAlive : x ∈ alive) :
    W x = 0 ↔ x ∈ N := by
  constructor
  · intro hWzero
    have hdistSq : (Metric.infDist x N) ^ 2 = 0 := by
      nlinarith [sq_nonneg (Metric.infDist x N), hLower x hxAlive]
    have hdist : Metric.infDist x N = 0 := (sq_eq_zero_iff).mp hdistSq
    exact (hNclosed.mem_iff_infDist_zero hNnonempty).2 hdist
  · intro hxN
    have hdist : Metric.infDist x N = 0 :=
      (hNclosed.mem_iff_infDist_zero hNnonempty).1 hxN
    have hlow := hLower x hxAlive
    have hupp := hUpper x hxAlive
    rw [hdist] at hlow hupp
    linarith

/-- The two-sided condition (26.A) and closedness of the target identify
positive Lyapunov residual with being outside that target, on alive states. -/
theorem residual_positive_iff_not_mem_closed_target
    {E : Type*} [PseudoMetricSpace E]
    (N alive : Set E) (W : E → ℝ)
    (hNclosed : IsClosed N) (hNnonempty : N.Nonempty)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hLower : ∀ x ∈ alive, c₁ * (Metric.infDist x N) ^ 2 ≤ W x)
    (hUpper : ∀ x ∈ alive, W x ≤ c₂ * (Metric.infDist x N) ^ 2)
    (x : E) (hxAlive : x ∈ alive) :
    0 < W x ↔ x ∉ N := by
  constructor
  · intro hWpos hxN
    have hzero := (residual_eq_zero_iff_mem_closed_target N alive W
      hNclosed hNnonempty c₁ c₂ hc₁ hc₂ hLower hUpper x hxAlive).2 hxN
    rw [hzero] at hWpos
    exact (lt_irrefl (0 : ℝ) hWpos)
  · intro houtside
    have hdist : 0 < Metric.infDist x N :=
      (hNclosed.notMem_iff_infDist_pos hNnonempty).mp houtside
    have hsq : 0 < (Metric.infDist x N) ^ 2 := sq_pos_of_pos hdist
    nlinarith [hLower x hxAlive]

/-- Both sides of the 26-A distance sandwich force the Lyapunov residual to
vanish on the zero-optimal-value set used as `N_top` in (26.1). -/
theorem residual_eq_zero_on_theorem26_target
    {E : Type*} [PseudoMetricSpace E]
    (alive : Set E) (Jstar : E → ℝ → ℝ) (N : ℝ → Set E)
    (W : ℝ × E → ℝ) (hN_eq : ∀ t, N t = theorem26ZeroValueTarget alive Jstar t)
    (hNclosed : ∀ t, IsClosed (N t))
    (hNnonempty : ∀ t, (N t).Nonempty)
    (c₁ c₂ : ℝ)
    (hLower : ∀ t x, x ∈ alive →
      c₁ * (Metric.infDist x (N t)) ^ 2 ≤ W (t, x))
    (hUpper : ∀ t x, x ∈ alive →
      W (t, x) ≤ c₂ * (Metric.infDist x (N t)) ^ 2)
    (t : ℝ) (y : E) (hy : y ∈ N t) : W (t, y) = 0 := by
  have hyAlive : y ∈ alive := by
    rw [hN_eq t] at hy
    exact hy.1
  have hdist : Metric.infDist y (N t) = 0 :=
    (hNclosed t).mem_iff_infDist_zero (hNnonempty t) |>.1 hy
  have hlow := hLower t y hyAlive
  have hupp := hUpper t y hyAlive
  rw [hdist] at hlow hupp
  simp at hlow hupp
  exact le_antisymm hupp hlow

/-- Equation (27.3) at the highest abstraction level: within the alive
region, positive Lyapunov ignorance residual is equivalent to operational
ignorance, assuming the theorem-26 PZS characterization and the 26-A lower
distance estimate. -/
theorem positive_ignorance_residual_iff_operationalIgnorance27_top
    {A : Type*} [PartialOrder A] [OrderTop A] {State : A → Type*}
    [PseudoMetricSpace (State ⊤)]
    (PZS : ∀ a, State a → ℝ → Prop)
    (N : ℝ → Set (State ⊤)) (alive : ℝ → Set (State ⊤))
    (W : (State ⊤) → ℝ)
    (hPZS : ∀ x t, PZS ⊤ x t ↔ x ∈ N t)
    (t : ℝ) (x : State ⊤) (hxAlive : x ∈ alive t)
    (hNclosed : IsClosed (N t)) (hNnonempty : (N t).Nonempty)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hWlower : ∀ y ∈ alive t,
      c₁ * (Metric.infDist y (N t)) ^ 2 ≤ W y)
    (hWupper : ∀ y ∈ alive t,
      W y ≤ c₂ * (Metric.infDist y (N t)) ^ 2) :
    0 < W x ↔
      operationalIgnorance27 PZS (alive t)
        (.inr ⟨x, hxAlive⟩ : TypedState27 State (alive t)) t := by
  have hgeom := residual_positive_iff_not_mem_closed_target
    (N t) (alive t) W hNclosed hNnonempty c₁ c₂ hc₁ hc₂
    hWlower hWupper x hxAlive
  change 0 < W x ↔ ¬PZS ⊤ x t
  rw [hPZS x t]
  exact hgeom

end Tomabechi.Theorem27
