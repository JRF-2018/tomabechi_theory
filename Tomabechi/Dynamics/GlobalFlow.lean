import Theorem1
import Tomabechi.Dynamics.MeanFieldReconstruction
import Tomabechi.Analysis.StrongConvexity
import Tomabechi.Dynamics.GradientFlow

/-! # 定理21の閾値と大域軌道

原文の臨界ゲイン条件を用いた不変領域・大域軌道・定量指数減衰を収録する。
証明と量化は移動のみで保持する。
-/

namespace Tomabechi.Theorem21

open RealInnerProductSpace
open Filter
open scoped Topology NNReal ContDiff

/-- The paper's critical-gain threshold yields both positive localOrbit curvature
and an outward-pointing boundary gradient estimate. The parameters are
positive as required by the threshold formula. -/
theorem critical_gain_estimates
    (κ m r β B p : ℝ)
    (hκ : 0 < κ) (hm : 0 < m) (hr : 0 < r)
    (hp : p > (max β (B / r)) / (κ * m)) :
    0 < κ * p * m - β ∧ B < κ * p * m * r := by
  have hkm : 0 < κ * m := mul_pos hκ hm
  have hscaled : max β (B / r) < p * (κ * m) :=
    (div_lt_iff₀ hkm).mp hp
  have hbeta : β < p * (κ * m) := lt_of_le_of_lt (le_max_left _ _) hscaled
  have hratio : B / r < p * (κ * m) := lt_of_le_of_lt (le_max_right _ _) hscaled
  have houtward : B < p * (κ * m) * r := (div_lt_iff₀ hr).mp hratio
  constructor
  · nlinarith [hbeta]
  · nlinarith [houtward]

/-- The critical gain makes the effective potential's radial derivative
strictly positive at the boundary, once the paper's base-gradient and biased
kernel curvature estimates have been established. The two directional bounds
are stated explicitly here; deriving them from the C² Hessian assumptions is
the remaining calculus step. -/
theorem effective_radial_gradient_positive
    (κ m r β B p : ℝ) (gradBase gradBias d : ℝ)
    (hκ : 0 < κ) (hm : 0 < m) (hr : 0 < r)
    (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (hbase : gradBase * d ≥ -B * r)
    (hbias : gradBias * d ≤ -m * r ^ 2) :
    (gradBase - κ * p * gradBias) * d > 0 := by
  obtain ⟨hc, houter⟩ := critical_gain_estimates κ m r β B p hκ hm hr hp
  have hbound : gradBase * d - κ * p * (gradBias * d) ≥
      -B * r + κ * p * m * r ^ 2 := by
    have hkmr : 0 < κ * m * r := by positivity
    have hp_pos : 0 < p := by nlinarith [houter, hkmr]
    have hκp : 0 < κ * p := mul_pos hκ hp_pos
    nlinarith
  have hpositive : -B * r + κ * p * m * r ^ 2 > 0 := by
    nlinarith [houter]
  calc
    (gradBase - κ * p * gradBias) * d =
        gradBase * d - κ * p * (gradBias * d) := by ring
    _ ≥ -B * r + κ * p * m * r ^ 2 := hbound
    _ > 0 := hpositive

/-- The Hessian hypotheses and gain threshold make the effective gradient
point radially outward on the boundary of the local ball. This is the exact
boundary estimate needed by `gradient_flow_stays_in_closedBall...`. -/
theorem effective_gradient_radial_positive_on_closedBall_of_threshold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (gradV gradS : E → E) (HS : E → E →L[ℝ] E)
    (hcenter : gradS center = 0)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B) :
    ∀ x ∈ Metric.closedBall center r, ‖x - center‖ = r →
      0 < inner ℝ (gradV x - (κ * p) • gradS x) (x - center) := by
  intro x hx hrx
  have hcenter_mem : center ∈ Metric.closedBall center r := by
    simp [Metric.mem_closedBall, hr.le]
  have hdir := boundary_directional_estimates_of_hessian
    (Metric.closedBall center r) center x gradV gradS HS B m r
    (by simpa using convex_closedBall center r) hcenter_mem hx hcenter hHS hSlower
    (hVbound x hx) hrx
  have hradial := effective_radial_gradient_positive κ m r β B p
    (inner ℝ (gradV x) (x - center)) (inner ℝ (gradS x) (x - center)) 1
    hκ hm hr hB hp (by simpa using hdir.1) (by simpa using hdir.2)
  have hgradpos :
      inner ℝ (gradV x) (x - center) - κ * p *
        inner ℝ (gradS x) (x - center) > 0 := by
    simpa using hradial
  simpa [inner_sub_left, inner_smul_left, star_trivial] using hgradpos

/-- On every compact time interval on which a solution already exists, the
paper's Hessian and gain assumptions keep the identity-mobility effective
gradient flow inside its closed local ball, when it starts in the interior. -/
theorem effective_gradient_flow_stays_in_closedBall_of_threshold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (gradV gradS : E → E) (HS : E → E →L[ℝ] E)
    (hcenter : gradS center = 0)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (a b : ℝ) (hab : a ≤ b)
    (hstart : ‖trajectory a - center‖ ^ 2 ≤ r ^ 2)
    (hcont : ContinuousOn trajectory (Set.Icc a b))
    (hflow : ∀ t ∈ Set.Icc a b,
      HasDerivAt trajectory
        (-(gradV (trajectory t) - (κ * p) • gradS (trajectory t))) t) :
    ∀ t ∈ Set.Icc a b, trajectory t ∈ Metric.closedBall center r := by
  apply gradient_flow_stays_in_closedBall_of_radial_gradient
    trajectory center (fun x => gradV x - (κ * p) • gradS x)
    a b r hab hr.le hstart hcont hflow
  intro t ht hbdy
  have hx : trajectory t ∈ Metric.closedBall center r := by
    change dist (trajectory t) center ≤ r
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (trajectory t - center), hbdy]
  have hrx : ‖trajectory t - center‖ = r := by
    have hnorm := norm_nonneg (trajectory t - center)
    nlinarith [hbdy, hr]
  exact effective_gradient_radial_positive_on_closedBall_of_threshold
    center r κ p m β B hr hκ hm hB hp gradV gradS HS hcenter hHS hSlower hVbound
    (trajectory t) hx hrx

/-- The paper's threshold assumptions give a common positive time, independent
of both the initial state and initial time, for which each solution starting
in the closed local ball stays in that ball. This joins compact-uniform
Picard--Lindelöf existence to the radial barrier estimate, including initial
states on the boundary. -/
theorem exists_uniform_invariant_effective_gradient_flow_segment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (gradV gradS : E → E) (HS : E → E →L[ℝ] E)
    (hcenter : gradS center = 0)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(gradV y - (κ * p) • gradS y)) x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ : ℝ, ∀ x ∈ Metric.closedBall center r,
      ∃ trajectory : ℝ → E,
        trajectory t₀ = x ∧
        (∀ t ∈ Set.Ioo t₀ (t₀ + δ),
          HasDerivAt trajectory
            (-(gradV (trajectory t) - (κ * p) • gradS (trajectory t))) t) ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt trajectory
            (-(gradV (trajectory t) - (κ * p) • gradS (trajectory t))) t) ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          trajectory t ∈ Metric.closedBall center r) := by
  let field : E → E := fun y => -(gradV y - (κ * p) • gradS y)
  have hcompact : IsCompact (Metric.closedBall center r) := isCompact_closedBall center r
  have hnonempty : (Metric.closedBall center r).Nonempty :=
    ⟨center, Metric.mem_closedBall_self (le_of_lt hr)⟩
  have hregular : ∀ y ∈ Metric.closedBall center r, ContDiffAt ℝ 1 field y := by
    intro y hy
    exact hfieldC1 y hy
  obtain ⟨δ₀, hδ₀, hlocal⟩ := exists_uniform_local_trajectory_on_compact
    field (Metric.closedBall center r) hcompact hnonempty hregular 0
  let δ : ℝ := δ₀ / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨δ, hδ, ?_⟩
  intro t₀ x hx
  obtain ⟨orbit, horbit, hflow⟩ := hlocal x hx
  let trajectory : ℝ → E := fun t => orbit (t - t₀)
  have hinit : trajectory t₀ = x := by simp [trajectory, horbit]
  have hflowShift : ∀ t ∈ Set.Ioo (t₀ - δ₀) (t₀ + δ₀),
      HasDerivAt trajectory (field (trajectory t)) t := by
    intro t ht
    have hmem : t - t₀ ∈ Set.Ioo (0 - δ₀) (0 + δ₀) := by
      constructor <;> linarith [ht.1, ht.2]
    have hderiv := hflow (t - t₀) hmem
    have hderiv' : HasDerivAt orbit (field (orbit (t - t₀))) (-t₀ + t) := by
      simpa [sub_eq_add_neg, add_comm] using hderiv
    simpa [trajectory, sub_eq_add_neg, add_comm] using hderiv'.comp_const_add (-t₀) t
  have hstart : ‖trajectory t₀ - center‖ ^ 2 ≤ r ^ 2 := by
    rw [hinit]
    have hdist := Metric.mem_closedBall.mp hx
    rw [dist_eq_norm] at hdist
    nlinarith [norm_nonneg (x - center), le_of_lt hr]
  have hforward : ∀ t ∈ Set.Ioo t₀ (t₀ + δ),
      HasDerivAt trajectory
        (-(gradV (trajectory t) - (κ * p) • gradS (trajectory t))) t := by
    intro t ht
    have hmem : t ∈ Set.Ioo (t₀ - δ₀) (t₀ + δ₀) := by
      constructor
      · dsimp [δ] at ht
        linarith [ht.1, hδ₀]
      · dsimp [δ] at ht
        linarith [ht.2]
    simpa [field] using hflowShift t hmem
  have hsegment : ∀ t ∈ Set.Icc t₀ (t₀ + δ),
      HasDerivAt trajectory
        (-(gradV (trajectory t) - (κ * p) • gradS (trajectory t))) t := by
    intro t ht
    have hmem : t ∈ Set.Ioo (t₀ - δ₀) (t₀ + δ₀) := by
      constructor
      · linarith [ht.1, hδ₀]
      · dsimp [δ] at ht
        linarith [ht.2, hδ₀]
    simpa [field] using hflowShift t hmem
  have hcontinuous : ContinuousOn trajectory (Set.Icc t₀ (t₀ + δ)) := by
    intro t ht
    exact (hsegment t ht).continuousAt.continuousWithinAt
  have hstay := effective_gradient_flow_stays_in_closedBall_of_threshold
    trajectory center r κ p m β B hr hκ hm hB hp gradV gradS HS hcenter hHS
    hSlower hVbound t₀ (t₀ + δ) (le_of_lt (by linarith [hδ])) hstart
    hcontinuous hsegment
  exact ⟨trajectory, hinit, hforward, hsegment, hstay⟩

/-- The boundary argument applies on each compact subinterval of a solution
defined on `[a,b)`. Consequently the orbit remains in the closed ball all the
way up to the finite endpoint, which supplies the invariant-region hypothesis
for the endpoint continuation theorem above. -/
theorem effective_gradient_flow_stays_in_closedBall_before_endpoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (gradV gradS : E → E) (HS : E → E →L[ℝ] E)
    (hcenter : gradS center = 0)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (a b : ℝ) (hab : a < b)
    (hstart : ‖trajectory a - center‖ ^ 2 ≤ r ^ 2)
    (hflow : ∀ t ∈ Set.Ico a b,
      HasDerivAt trajectory
        (-(gradV (trajectory t) - (κ * p) • gradS (trajectory t))) t) :
    ∀ t ∈ Set.Ico a b, trajectory t ∈ Metric.closedBall center r := by
  intro t ht
  have hflowSeg : ∀ s ∈ Set.Icc a t,
      HasDerivAt trajectory
        (-(gradV (trajectory s) - (κ * p) • gradS (trajectory s))) s := by
    intro s hs
    exact hflow s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hcontSeg : ContinuousOn trajectory (Set.Icc a t) := by
    intro s hs
    exact (hflowSeg s hs).continuousAt.continuousWithinAt
  have hstay := effective_gradient_flow_stays_in_closedBall_of_threshold
    trajectory center r κ p m β B hr hκ hm hB hp gradV gradS HS hcenter hHS
    hSlower hVbound a t ht.1 hstart hcontSeg hflowSeg
  exact hstay t ⟨ht.1, le_rfl⟩

/-- The threshold assumptions extend an existing identity-mobility orbit by a
fixed positive time, preserving the invariant-ball and ODE hypotheses needed
to repeat the continuation step. -/
theorem extend_effective_gradient_flow_by_uniform_step_of_threshold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (trajectory : ℝ → E) (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (gradV gradS : E → E) (HS : E → E →L[ℝ] E)
    (hcenter : gradS center = 0)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (hfield : Continuous (fun x => -(gradV x - (κ * p) • gradS x)))
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(gradV y - (κ * p) • gradS y)) x)
    (a b : ℝ) (hab : a < b)
    (hstart : ‖trajectory a - center‖ ^ 2 ≤ r ^ 2)
    (hflow : ∀ t ∈ Set.Ico a b,
      HasDerivAt trajectory
        (-(gradV (trajectory t) - (κ * p) • gradS (trajectory t))) t) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ continuation : ℝ → E,
      (∀ t ∈ Set.Ico a (b + δ),
        continuation t ∈ Metric.closedBall center r) ∧
      (∀ t ∈ Set.Ico a (b + δ),
        HasDerivAt continuation
          (-(gradV (continuation t) - (κ * p) • gradS (continuation t))) t) := by
  have hstay := effective_gradient_flow_stays_in_closedBall_before_endpoint
    trajectory center r κ p m β B hr hκ hm hB hp gradV gradS HS hcenter hHS
    hSlower hVbound a b hab hstart hflow
  let field : E → E := fun x => -(gradV x - (κ * p) • gradS x)
  obtain ⟨δ, hδ, huniform⟩ := exists_uniform_invariant_effective_gradient_flow_segment
    center r κ p m β B hr hκ hm hB hp gradV gradS HS hcenter hHS hSlower hVbound
    hfieldC1
  have huniform' : ∀ t₀ : ℝ, ∀ x ∈ Metric.closedBall center r,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit (field (localOrbit t)) t) ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          localOrbit t ∈ Metric.closedBall center r) := by
    intro t₀ x hx
    obtain ⟨localOrbit, hinit, _, hflowClosed, hstayClosed⟩ := huniform t₀ x hx
    exact ⟨localOrbit, hinit, by simpa [field] using hflowClosed,
      hstayClosed⟩
  obtain ⟨continuation, _, htrajectory', hflow'⟩ :=
    extend_ode_orbit_past_finite_endpoint_of_closedBall_uniform trajectory field
      center a b r δ hab hr.le hδ hfield huniform' hstay hflow
  exact ⟨δ, hδ, continuation, htrajectory', by simpa [field] using hflow'⟩

/-- For every finite number of uniform continuation steps, the threshold
assumptions produce an identity-mobility orbit over the corresponding finite
time interval. The step size is shared by all horizons and all starting
states in the ball. This is the finite-horizon existence theorem; it does not
by itself assert one coherent orbit on all of `[a, ∞)`. -/
theorem exists_effective_gradient_flow_on_every_finite_horizon
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (gradV gradS : E → E) (HS : E → E →L[ℝ] E)
    (hcenter : gradS center = 0)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (hfield : Continuous (fun x => -(gradV x - (κ * p) • gradS x)))
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(gradV y - (κ * p) • gradS y)) x)
    (a : ℝ) (x₀ : E) (hx₀ : x₀ ∈ Metric.closedBall center r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∃ trajectory : ℝ → E,
      trajectory a = x₀ ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ),
        trajectory t ∈ Metric.closedBall center r) ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ),
        HasDerivAt trajectory
          (-(gradV (trajectory t) - (κ * p) • gradS (trajectory t))) t) := by
  let field : E → E := fun x => -(gradV x - (κ * p) • gradS x)
  obtain ⟨δ, hδ, huniform⟩ := exists_uniform_invariant_effective_gradient_flow_segment
    center r κ p m β B hr hκ hm hB hp gradV gradS HS hcenter hHS hSlower hVbound
    hfieldC1
  have huniform' : ∀ t₀ : ℝ, ∀ x ∈ Metric.closedBall center r,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit (field (localOrbit t)) t) ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          localOrbit t ∈ Metric.closedBall center r) := by
    intro t₀ x hx
    obtain ⟨localOrbit, hinit, _, hflowClosed, hstayClosed⟩ := huniform t₀ x hx
    exact ⟨localOrbit, hinit, by simpa [field] using hflowClosed, hstayClosed⟩
  obtain ⟨initial, hinitial, _, hinitialFlow, hinitialStay⟩ := huniform a x₀ hx₀
  let endpoint : ℕ → ℝ := fun n => a + ((n + 1 : ℕ) : ℝ) * δ
  have hiterate : ∀ n : ℕ, ∃ trajectory : ℝ → E,
      trajectory a = x₀ ∧
      (∀ t ∈ Set.Ico a (endpoint n),
        trajectory t ∈ Metric.closedBall center r) ∧
      (∀ t ∈ Set.Ico a (endpoint n),
        HasDerivAt trajectory (field (trajectory t)) t) := by
    intro n
    induction n with
    | zero =>
        have hendpointZero : endpoint 0 = a + δ := by simp [endpoint]
        refine ⟨initial, hinitial, ?_, ?_⟩
        · intro t ht
          rw [hendpointZero] at ht
          have htIcc : t ∈ Set.Icc a (a + δ) := by
            exact ⟨ht.1, le_of_lt ht.2⟩
          exact hinitialStay t htIcc
        · intro t ht
          rw [hendpointZero] at ht
          have htIcc : t ∈ Set.Icc a (a + δ) := by
            exact ⟨ht.1, le_of_lt ht.2⟩
          simpa [field] using hinitialFlow t htIcc
    | succ n ih =>
        obtain ⟨old, holdInit, holdStay, holdFlow⟩ := ih
        have hstepPositive : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
        have hstart : ‖old a - center‖ ^ 2 ≤ r ^ 2 := by
          rw [holdInit]
          have hdist := Metric.mem_closedBall.mp hx₀
          rw [dist_eq_norm] at hdist
          nlinarith [norm_nonneg (x₀ - center), le_of_lt hr]
        have hab : a < endpoint n := by
          dsimp [endpoint]
          nlinarith [mul_pos hstepPositive hδ]
        obtain ⟨next, hnextInit, hnextStay, hnextFlow⟩ :=
          extend_ode_orbit_past_finite_endpoint_of_closedBall_uniform old field
            center a (endpoint n) r δ hab hr.le hδ hfield huniform'
            holdStay holdFlow
        have hendpoint : endpoint (n + 1) = endpoint n + δ := by
          dsimp [endpoint]
          push_cast
          ring
        refine ⟨next, ?_, ?_, ?_⟩
        · rw [hnextInit, holdInit]
        · intro t ht
          have ht' : t ∈ Set.Ico a (endpoint n + δ) := by
            simpa [hendpoint] using ht
          exact hnextStay t ht'
        · intro t ht
          have ht' : t ∈ Set.Ico a (endpoint n + δ) := by
            simpa [hendpoint] using ht
          simpa [field] using hnextFlow t ht'
  refine ⟨δ, hδ, ?_⟩
  intro n
  simpa [endpoint, field] using hiterate n

/-- A C¹ vector field has one Lipschitz constant on a compact closed ball:
local continuity of its derivative makes the derivative norm bounded, and the
mean-value theorem applies because the ball is convex. -/
theorem exists_lipschitz_constant_on_closedBall_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (field : E → E) (center : E) (r : ℝ)
    (hregular : ∀ x ∈ Metric.closedBall center r, ContDiffAt ℝ 1 field x) :
    ∃ L : ℝ≥0, LipschitzOnWith L field (Metric.closedBall center r) := by
  have hcompact : IsCompact (Metric.closedBall center r) := isCompact_closedBall center r
  have hfderivAt : ∀ x ∈ Metric.closedBall center r,
      ContinuousAt (fderiv ℝ field) x := by
    intro x hx
    obtain ⟨g, u, hu, hcont, hderiv⟩ :=
      (contDiffAt_one_iff (𝕜 := ℝ) (f := field) (x := x)).mp (hregular x hx)
    have hgcont : ContinuousAt g x :=
      (contDiffAt_zero (𝕜 := ℝ) (f := g) (x := x)).mpr ⟨u, hu, hcont⟩ |>.continuousAt
    have heq : fderiv ℝ field =ᶠ[𝓝 x] g := by
      filter_upwards [eventually_mem_set.mpr hu] with y hy
      exact (hderiv y hy).fderiv
    exact hgcont.congr heq.symm
  have hfderiv : ContinuousOn (fderiv ℝ field) (Metric.closedBall center r) := by
    intro x hx
    exact (hfderivAt x hx).continuousWithinAt
  have hnorm : ContinuousOn (fun x => ‖fderiv ℝ field x‖) (Metric.closedBall center r) :=
    continuous_norm.comp_continuousOn hfderiv
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hnorm
  let L : ℝ≥0 := ⟨max C 0 + 1, by positivity⟩
  have hbound : ∀ x ∈ Metric.closedBall center r,
      ‖fderiv ℝ field x‖₊ ≤ L := by
    intro x hx
    apply NNReal.coe_le_coe.mpr
    change ‖fderiv ℝ field x‖ ≤ max C 0 + 1
    have hCx : ‖fderiv ℝ field x‖ ≤ C := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC x hx
    have hC' : C ≤ max C 0 + 1 := by linarith [le_max_left C 0]
    exact le_trans hCx hC'
  have hdiff : ∀ x ∈ Metric.closedBall center r, DifferentiableAt ℝ field x := by
    intro x hx
    exact (hregular x hx).differentiableAt_one
  exact ⟨L, (convex_closedBall center r).lipschitzOnWith_of_nnnorm_fderiv_le
    hdiff hbound⟩

/-- Solutions contained in a closed ball are unique there when the vector
field is C¹ at every point of the ball. Uniqueness is first applied on each
compact subinterval strictly before the right endpoint, so no endpoint
continuity assumption is needed. -/
theorem ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (field : E → E) (center : E) (r a b : ℝ)
    (hregular : ∀ x ∈ Metric.closedBall center r, ContDiffAt ℝ 1 field x)
    (f g : ℝ → E)
    (hfball : ∀ t ∈ Set.Ico a b, f t ∈ Metric.closedBall center r)
    (hgball : ∀ t ∈ Set.Ico a b, g t ∈ Metric.closedBall center r)
    (hfflow : ∀ t ∈ Set.Ico a b, HasDerivAt f (field (f t)) t)
    (hgflow : ∀ t ∈ Set.Ico a b, HasDerivAt g (field (g t)) t)
    (hinit : f a = g a) : Set.EqOn f g (Set.Ico a b) := by
  obtain ⟨L, hL⟩ := exists_lipschitz_constant_on_closedBall_of_contDiffAt
    field center r hregular
  intro t ht
  let c : ℝ := (t + b) / 2
  have hac : a < c := by dsimp [c]; linarith [ht.1, ht.2]
  have htc : t ≤ c := by dsimp [c]; linarith [ht.2]
  have hcb : c < b := by dsimp [c]; linarith [ht.2]
  have hEq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => field) (s := fun _ => Metric.closedBall center r)
    (K := L)
    (fun _ _ => hL)
    (HasDerivAt.continuousOn fun s hs =>
      hfflow s ⟨hs.1, lt_of_le_of_lt hs.2 hcb⟩)
    (fun s hs =>
      ((hfflow s ⟨hs.1, lt_trans hs.2 hcb⟩).hasDerivWithinAt).mono
        (Set.subset_univ _))
    (fun s hs => hfball s ⟨hs.1, lt_trans hs.2 hcb⟩)
    (HasDerivAt.continuousOn fun s hs =>
      hgflow s ⟨hs.1, lt_of_le_of_lt hs.2 hcb⟩)
    (fun s hs =>
      ((hgflow s ⟨hs.1, lt_trans hs.2 hcb⟩).hasDerivWithinAt).mono
        (Set.subset_univ _))
    (fun s hs => hgball s ⟨hs.1, lt_trans hs.2 hcb⟩)
    hinit
  exact hEq ⟨ht.1, htc⟩

/-- ODE uniqueness in a complete normed-space setting from an explicit
Lipschitz bound on the closed ball. Unlike the compact-ball corollary below,
this lemma is dimension-free. -/
theorem ode_trajectories_eqOn_Ico_of_lipschitz_on_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E) (center : E) (r a b : ℝ) (L : ℝ≥0)
    (hL : LipschitzOnWith L field (Metric.closedBall center r))
    (f g : ℝ → E)
    (hfball : ∀ t ∈ Set.Ico a b, f t ∈ Metric.closedBall center r)
    (hgball : ∀ t ∈ Set.Ico a b, g t ∈ Metric.closedBall center r)
    (hfflow : ∀ t ∈ Set.Ico a b, HasDerivAt f (field (f t)) t)
    (hgflow : ∀ t ∈ Set.Ico a b, HasDerivAt g (field (g t)) t)
    (hinit : f a = g a) : Set.EqOn f g (Set.Ico a b) := by
  intro t ht
  let c : ℝ := (t + b) / 2
  have hac : a < c := by dsimp [c]; linarith [ht.1, ht.2]
  have htc : t ≤ c := by dsimp [c]; linarith [ht.2]
  have hcb : c < b := by dsimp [c]; linarith [ht.2]
  have hEq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => field) (s := fun _ => Metric.closedBall center r)
    (K := L)
    (fun _ _ => hL)
    (HasDerivAt.continuousOn fun s hs =>
      hfflow s ⟨hs.1, lt_of_le_of_lt hs.2 hcb⟩)
    (fun s hs =>
      ((hfflow s ⟨hs.1, lt_trans hs.2 hcb⟩).hasDerivWithinAt).mono
        (Set.subset_univ _))
    (fun s hs => hfball s ⟨hs.1, lt_trans hs.2 hcb⟩)
    (HasDerivAt.continuousOn fun s hs =>
      hgflow s ⟨hs.1, lt_of_le_of_lt hs.2 hcb⟩)
    (fun s hs =>
      ((hgflow s ⟨hs.1, lt_trans hs.2 hcb⟩).hasDerivWithinAt).mono
        (Set.subset_univ _))
    (fun s hs => hgball s ⟨hs.1, lt_trans hs.2 hcb⟩)
    hinit
  exact hEq ⟨ht.1, htc⟩

/-- Uniqueness specialized to Theorem 21's state-dependent mobility equation.
Any two closed-loop solutions with the same initial state agree as long as
both stay in the closed ball; the C¹ mobility and gradient assumptions make
the closed-loop field C¹ there. -/
theorem theorem21_state_dependent_closed_loop_unique_on_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E → E →L[ℝ] E) (gradient : E → E) (center : E)
    (r a b : ℝ)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (gradient y))) x)
    (f g : ℝ → E)
    (hfball : ∀ t ∈ Set.Ico a b, f t ∈ Metric.closedBall center r)
    (hgball : ∀ t ∈ Set.Ico a b, g t ∈ Metric.closedBall center r)
    (hfflow : ∀ t ∈ Set.Ico a b,
      HasDerivAt f (-(A (f t) (gradient (f t)))) t)
    (hgflow : ∀ t ∈ Set.Ico a b,
      HasDerivAt g (-(A (g t) (gradient (g t)))) t)
    (hinit : f a = g a) : Set.EqOn f g (Set.Ico a b) := by
  let field : E → E := fun x => -(A x (gradient x))
  apply ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall
    field center r a b hfieldC1 f g hfball hgball
  · intro t ht
    simpa [field] using hfflow t ht
  · intro t ht
    simpa [field] using hgflow t ht
  · exact hinit

/-- Two finite-horizon solutions with the same initial state agree on their
common forward interval, even when their right endpoints differ. -/
theorem finite_horizon_trajectories_coherent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (field : E → E) (center : E) (r a b₁ b₂ : ℝ)
    (hregular : ∀ x ∈ Metric.closedBall center r, ContDiffAt ℝ 1 field x)
    (f g : ℝ → E)
    (hfball : ∀ t ∈ Set.Ico a b₁, f t ∈ Metric.closedBall center r)
    (hgball : ∀ t ∈ Set.Ico a b₂, g t ∈ Metric.closedBall center r)
    (hfflow : ∀ t ∈ Set.Ico a b₁, HasDerivAt f (field (f t)) t)
    (hgflow : ∀ t ∈ Set.Ico a b₂, HasDerivAt g (field (g t)) t)
    (hinit : f a = g a) :
    Set.EqOn f g (Set.Ico a (min b₁ b₂)) := by
  by_cases h : b₁ ≤ b₂
  · have hEq := ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall
      field center r a b₁ hregular f g hfball
      (fun t ht => hgball t ⟨ht.1, lt_of_lt_of_le ht.2 h⟩)
      hfflow (fun t ht => hgflow t ⟨ht.1, lt_of_lt_of_le ht.2 h⟩) hinit
    intro t ht
    exact hEq (by simpa [min_eq_left h] using ht)
  · have h' : b₂ ≤ b₁ := le_of_not_ge h
    have hEq := ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall
      field center r a b₂ hregular g f hgball
      (fun t ht => hfball t ⟨ht.1, lt_of_lt_of_le ht.2 h'⟩)
      hgflow (fun t ht => hfflow t ⟨ht.1, lt_of_lt_of_le ht.2 h'⟩) hinit.symm
    intro t ht
    exact (hEq (by simpa [min_eq_right h'] using ht)).symm

/-- Uniform forward local existence on a compact set. If the field is C¹ at
every point of the compact set, there is one positive time `δ`, independent of
the initial time and the initial state in the set, such that a solution exists
on the closed forward interval `[t₀, t₀ + δ]`. A short two-sided local
solution supplies the ODE at and just before the initial time. -/
theorem exists_uniform_forward_local_trajectory_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (field : E → E) (K : Set E) (hK : IsCompact K) (hKne : K.Nonempty)
    (hfield : ∀ x ∈ K, ContDiffAt ℝ 1 field x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ : ℝ, ∀ x ∈ K, ∃ trajectory : ℝ → E,
      trajectory t₀ = x ∧
      ∀ t ∈ Set.Icc t₀ (t₀ + δ),
        HasDerivAt trajectory (field (trajectory t)) t := by
  obtain ⟨δ₀, hδ₀, hlocal⟩ :=
    exists_uniform_local_trajectory_on_compact field K hK hKne hfield 0
  refine ⟨δ₀ / 2, half_pos hδ₀, ?_⟩
  intro t₀ x hx
  obtain ⟨base, hbase, hflow⟩ := hlocal x hx
  let trajectory : ℝ → E := fun t => base (t - t₀)
  refine ⟨trajectory, ?_, ?_⟩
  · simpa [trajectory] using hbase
  · intro t ht
    have hs : t - t₀ ∈ Set.Ioo (0 - δ₀) (0 + δ₀) := by
      change 0 - δ₀ < t - t₀ ∧ t - t₀ < 0 + δ₀
      constructor <;> linarith [ht.1, ht.2, hδ₀]
    have hbaseFlow := hflow (t - t₀) (by simpa using hs)
    have hshift := hbaseFlow.scomp t ((hasDerivAt_id t).sub_const t₀)
    change HasDerivAt (base ∘ fun u => u - t₀)
      (field (base (t - t₀))) t
    simpa using hshift

/- The coherent finite-horizon solutions on a compact invariant set assemble into
one global forward identity-mobility orbit. Local C¹ regularity on the
surrounding ball supplies uniqueness. -/
theorem exists_global_forward_trajectory_of_finite_horizon_solutions_of_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (field : E → E) (K : Set E) (center : E) (r δ a : ℝ)
    (hδ : 0 < δ)
    (hregular : ∀ x ∈ Metric.closedBall center r, ContDiffAt ℝ 1 field x)
    (hunique : ∀ (a b : ℝ) (f g : ℝ → E),
      (∀ t ∈ Set.Ico a b, f t ∈ Metric.closedBall center r) →
      (∀ t ∈ Set.Ico a b, g t ∈ Metric.closedBall center r) →
      (∀ t ∈ Set.Ico a b, HasDerivAt f (field (f t)) t) →
      (∀ t ∈ Set.Ico a b, HasDerivAt g (field (g t)) t) →
      f a = g a → Set.EqOn f g (Set.Ico a b))
    (hKsubset : K ⊆ Metric.closedBall center r)
    (hKsubsetInterior : K ⊆ Metric.ball center r)
    (x₀ : E) (hx₀ : x₀ ∈ K)
    (hfinite : ∀ n : ℕ, ∃ trajectory : ℝ → E,
      trajectory a = x₀ ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ), trajectory t ∈ K) ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ),
        HasDerivAt trajectory (field (trajectory t)) t))
    :
    ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
      (∀ t ∈ Set.Ici a, trajectory t ∈ K) ∧
      (∀ t ∈ Set.Ioi (a - ε),
        HasDerivAt trajectory (field (trajectory t)) t) ∧
      (∀ t ∈ Set.Ioi (a - ε), trajectory t ∈ Metric.ball center r) := by
  classical
  have hfieldAt : ∀ x ∈ Metric.ball center r, ContinuousAt field x := by
    intro x hx
    exact (hregular x (Metric.ball_subset_closedBall hx)).continuousAt
  let endpoint : ℕ → ℝ := fun n => a + ((n + 1 : ℕ) : ℝ) * δ
  let orbit : ℕ → ℝ → E := fun n => Classical.choose (hfinite n)
  have horbit (n : ℕ) : orbit n a = x₀ ∧
      (∀ t ∈ Set.Ico a (endpoint n), orbit n t ∈ K) ∧
      (∀ t ∈ Set.Ico a (endpoint n),
        HasDerivAt (orbit n) (field (orbit n t)) t) := by
    have hspec := Classical.choose_spec (hfinite n)
    exact ⟨hspec.1, hspec.2.1, hspec.2.2⟩
  have hcoherent (m n : ℕ) (t : ℝ)
      (hmemb : t ∈ Set.Ico a (endpoint m))
      (hnemb : t ∈ Set.Ico a (endpoint n)) : orbit m t = orbit n t := by
    let b := min (endpoint m) (endpoint n)
    have hEq := hunique a b (orbit m) (orbit n)
      (fun s hs => hKsubset ((horbit m).2.1 s
        ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩))
      (fun s hs => hKsubset ((horbit n).2.1 s
        ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩))
      (fun s hs => (horbit m).2.2 s
        ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
      (fun s hs => (horbit n).2.2 s
        ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩)
      ((horbit m).1.trans (horbit n).1.symm)
    have ht' : t ∈ Set.Ico a b := by
      exact ⟨hmemb.1, lt_min hmemb.2 hnemb.2⟩
    exact hEq ht'
  have hindex_exists : ∀ t : ℝ, a < t → ∃ n : ℕ, t < endpoint n := by
    intro t hta
    obtain ⟨n, hn⟩ := exists_nat_gt ((t - a) / δ)
    refine ⟨n, ?_⟩
    have hscaled : t - a < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
    dsimp [endpoint]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg n) hδ.le]
  let index : ∀ t : ℝ, a < t → ℕ := fun t ht => Classical.choose (hindex_exists t ht)
  have hindex_spec (t : ℝ) (ht : a < t) : t < endpoint (index t ht) :=
    Classical.choose_spec (hindex_exists t ht)
  obtain ⟨ε₀, hε₀, initial, hinitial, hinitialFlow⟩ :=
    exists_local_trajectory_of_contDiffAt field x₀ (hregular x₀ (hKsubset hx₀)) a
  have hinitialStayEventually : ∀ᶠ t in 𝓝 a, initial t ∈ Metric.ball center r := by
    have htrajcont : ContinuousAt initial a := (hinitialFlow a ⟨by linarith [hε₀], by linarith [hε₀]⟩).continuousAt
    have hball : Metric.ball center r ∈ 𝓝 x₀ := Metric.isOpen_ball.mem_nhds (hKsubsetInterior hx₀)
    have hball' : Metric.ball center r ∈ 𝓝 (initial a) := by simpa [hinitial] using hball
    exact htrajcont.eventually hball'
  have htimeEventually : ∀ᶠ t in 𝓝 a, t ∈ Set.Ioo (a - ε₀) (a + ε₀) :=
    isOpen_Ioo.mem_nhds ⟨by linarith [hε₀], by linarith [hε₀]⟩
  have hjointEventually : {t | t ∈ Set.Ioo (a - ε₀) (a + ε₀) ∧
      initial t ∈ Metric.ball center r} ∈ 𝓝 a := by
    filter_upwards [htimeEventually, hinitialStayEventually] with t ht hball
    exact ⟨ht, hball⟩
  obtain ⟨ρ, hρ, hρball⟩ := Metric.mem_nhds_iff.mp hjointEventually
  let ε : ℝ := min (min (ε₀ / 2) (δ / 2)) (ρ / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (lt_min (half_pos hε₀) (half_pos hδ)) (half_pos hρ)
  have hε₀bound : ε ≤ ε₀ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεδbound : ε ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hερbound : ε ≤ ρ / 2 := min_le_right _ _
  have hinitialPreStay : ∀ t ∈ Set.Icc a (a + ε),
      initial t ∈ Metric.closedBall center r := by
    intro t ht
    have hdist : dist t a < ρ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      have : t - a ≤ ε := by linarith [ht.2]
      linarith
    have hmem := hρball (Metric.mem_ball.mpr hdist)
    exact Metric.ball_subset_closedBall hmem.2
  have hinitialClosedFlow : ∀ t ∈ Set.Icc a (a + ε),
      HasDerivAt initial (field (initial t)) t := by
    intro t ht
    apply hinitialFlow
    constructor
    · linarith [ht.1, hε₀]
    · have : t ≤ a + ε := ht.2
      linarith [hε₀bound]
  have hpreEq : Set.EqOn initial (orbit 0) (Set.Ico a (a + ε)) := by
    have hδendpoint : a + ε ≤ endpoint 0 := by
      simp [endpoint]
      linarith [hεδbound]
    apply hunique a (a + ε) initial (orbit 0)
    · intro t ht
      exact hinitialPreStay t ⟨ht.1, le_of_lt ht.2⟩
    · intro t ht
      exact hKsubset ((horbit 0).2.1 t ⟨ht.1, lt_of_lt_of_le ht.2 hδendpoint⟩)
    · intro t ht
      exact hinitialClosedFlow t ⟨ht.1, le_of_lt ht.2⟩
    · intro t ht
      exact (horbit 0).2.2 t ⟨ht.1, lt_of_lt_of_le ht.2 hδendpoint⟩
    · exact hinitial.trans (horbit 0).1.symm
  let trajectory : ℝ → E := fun t =>
    if ht : a < t then orbit (index t ht) t else initial t
  have htrajectoryInit : trajectory a = x₀ := by simp [trajectory, hinitial]
  have htrajectoryK : ∀ t ∈ Set.Ici a, trajectory t ∈ K := by
    intro t ht
    by_cases hta : a < t
    · let n := index t hta
      have hEnd := hindex_spec t hta
      simpa [trajectory, hta] using (horbit n).2.1 t ⟨ht, hEnd⟩
    · have htaeq : t = a := le_antisymm (le_of_not_gt hta) ht
      subst t
      simpa [trajectory, hinitial] using hx₀
  have htrajectoryODE : ∀ t ∈ Set.Ioi (a - ε),
      HasDerivAt trajectory (field (trajectory t)) t := by
    intro t ht
    by_cases hta : a < t
    · let n := index t hta
      have hEnd := hindex_spec t hta
      have hevent : trajectory =ᶠ[𝓝 t] orbit n := by
        filter_upwards [Ioi_mem_nhds hta, Iio_mem_nhds hEnd] with s hsa hsend
        have hs : a < s := by simpa using hsa
        have hsend' : s < endpoint n := by simpa using hsend
        let m := index s hs
        have hmend := hindex_spec s hs
        have hsame := hcoherent m n s
          ⟨le_of_lt hs, hmend⟩ ⟨le_of_lt hs, hsend'⟩
        simp [trajectory, hs, hsame, m]
      have hflow := (horbit n).2.2 t ⟨le_of_lt hta, hEnd⟩
      have hteq : trajectory t = orbit n t := hevent.self_of_nhds
      simpa [trajectory, hta, n, hteq] using
        hflow.congr_of_eventuallyEq hevent
    · by_cases hta' : t < a
      · have hmem : t ∈ Set.Ioo (a - ε₀) (a + ε₀) := by
          change a - ε < t at ht
          constructor <;> linarith [ht, hε₀bound, hta']
        have hevent : trajectory =ᶠ[𝓝 t] initial := by
          filter_upwards [Iio_mem_nhds hta'] with s hs
          change s < a at hs
          simp [trajectory, not_lt_of_ge (le_of_lt hs)]
        have hteq : trajectory t = initial t := hevent.self_of_nhds
        simpa [hteq] using
          (hinitialFlow t hmem).congr_of_eventuallyEq hevent
      · have htaeq : t = a := le_antisymm (le_of_not_gt hta) (le_of_not_gt hta')
        subst t
        have hevent : trajectory =ᶠ[𝓝 a] initial := by
          have hlo : a - ε < a := by linarith [hε]
          have hhi : a < a + ε := by linarith [hε]
          filter_upwards [Ioi_mem_nhds hlo, Iio_mem_nhds hhi] with s hslo hshi
          change a - ε < s at hslo
          change s < a + ε at hshi
          by_cases hsa : a < s
          · have hend0 : s < endpoint 0 := by
              have hend : a + ε ≤ endpoint 0 := by simp [endpoint]; linarith [hεδbound]
              exact lt_of_lt_of_le hshi hend
            let m := index s hsa
            have hmend : s < endpoint m := hindex_spec s hsa
            have hsame := hcoherent m 0 s
              ⟨le_of_lt hsa, hmend⟩ ⟨le_of_lt hsa, hend0⟩
            have hpre := hpreEq ⟨le_of_lt hsa, hshi⟩
            have hsame' : orbit m s = initial s := hsame.trans hpre.symm
            simp [trajectory, hsa, m, hsame']
          · simp [trajectory, hsa]
        have hbase := hinitialFlow a ⟨by linarith [hε₀], by linarith [hε₀]⟩
        simpa [htrajectoryInit, hinitial] using
          hbase.congr_of_eventuallyEq hevent
  have htrajectoryBall : ∀ t ∈ Set.Ioi (a - ε),
      trajectory t ∈ Metric.ball center r := by
    intro t ht
    by_cases hta : a ≤ t
    · exact hKsubsetInterior (htrajectoryK t hta)
    · have hta' : t < a := lt_of_not_ge hta
      have hdist : dist t a < ρ := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hta')]
        change a - ε < t at ht
        linarith [hερbound]
      have hlocalBall := hρball (Metric.mem_ball.mpr hdist)
      simpa [trajectory, not_lt_of_ge (le_of_lt hta')] using hlocalBall.2
  exact ⟨trajectory, ε, hε, htrajectoryInit, htrajectoryK,
    htrajectoryODE, htrajectoryBall⟩

/-- Finite-dimensional wrapper: C¹ regularity on the closed ball supplies the
solution-uniqueness premise required by the dimension-free assembly theorem. -/
theorem exists_global_forward_trajectory_of_finite_horizon_solutions
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (field : E → E) (K : Set E) (center : E) (r δ a : ℝ)
    (hδ : 0 < δ)
    (hregular : ∀ x ∈ Metric.closedBall center r, ContDiffAt ℝ 1 field x)
    (hKsubset : K ⊆ Metric.closedBall center r)
    (hKsubsetInterior : K ⊆ Metric.ball center r)
    (x₀ : E) (hx₀ : x₀ ∈ K)
    (hfinite : ∀ n : ℕ, ∃ trajectory : ℝ → E,
      trajectory a = x₀ ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ), trajectory t ∈ K) ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ),
        HasDerivAt trajectory (field (trajectory t)) t)) :
    ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
      (∀ t ∈ Set.Ici a, trajectory t ∈ K) ∧
      (∀ t ∈ Set.Ioi (a - ε),
        HasDerivAt trajectory (field (trajectory t)) t) ∧
      (∀ t ∈ Set.Ioi (a - ε), trajectory t ∈ Metric.ball center r) := by
  have hunique : ∀ (a b : ℝ) (f g : ℝ → E),
      (∀ t ∈ Set.Ico a b, f t ∈ Metric.closedBall center r) →
      (∀ t ∈ Set.Ico a b, g t ∈ Metric.closedBall center r) →
      (∀ t ∈ Set.Ico a b, HasDerivAt f (field (f t)) t) →
      (∀ t ∈ Set.Ico a b, HasDerivAt g (field (g t)) t) →
      f a = g a → Set.EqOn f g (Set.Ico a b) := by
    intro a' b f g hf hg hff hgg hinit
    exact ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall
      field center r a' b hregular f g hf hg hff hgg hinit
  exact exists_global_forward_trajectory_of_finite_horizon_solutions_of_unique
    field K center r δ a hδ hregular hunique hKsubset hKsubsetInterior
    x₀ hx₀ hfinite

/- The global assembly theorem consumes uniformly long invariant segments.
   This wrapper derives the needed local existence part from compactness and
   C¹ regularity; forward invariance supplies the segment membership. -/
theorem exists_global_forward_trajectory_of_compact_forward_invariant_set
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (field : E → E) (K : Set E) (center : E) (r : ℝ)
    (hr : 0 ≤ r)
    (hregular : ∀ x ∈ Metric.closedBall center r, ContDiffAt ℝ 1 field x)
    (hKcompact : IsCompact K)
    (hKsubset : K ⊆ Metric.closedBall center r)
    (hKsubsetInterior : K ⊆ Metric.ball center r)
    (hinvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit t₀ = x → x ∈ K →
      (∀ t ∈ Set.Icc t₀ (t₀ + d),
        HasDerivAt orbit (field (orbit t)) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ K)
    (x₀ : E) (hx₀ : x₀ ∈ K) (a : ℝ) :
    ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
      (∀ t ∈ Set.Ici a, trajectory t ∈ K) ∧
      (∀ t ∈ Set.Ioi (a - ε),
        HasDerivAt trajectory (field (trajectory t)) t) ∧
      (∀ t ∈ Set.Ioi (a - ε), trajectory t ∈ Metric.ball center r) := by
  have hKne' : K.Nonempty := ⟨x₀, hx₀⟩
  have hregularK : ∀ x ∈ K, ContDiffAt ℝ 1 field x :=
    fun x hx => hregular x (hKsubset hx)
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_forward_local_trajectory_on_compact
    field K hKcompact hKne' hregularK
  have huniform : ∀ t₀ : ℝ, ∀ x ∈ K,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit (field (localOrbit t)) t) ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ), localOrbit t ∈ K) := by
    intro t₀ x hx
    obtain ⟨localOrbit, hinit, hflow⟩ := hlocal t₀ x hx
    refine ⟨localOrbit, hinit, hflow, ?_⟩
    exact hinvariant t₀ δ localOrbit x hδ.le hinit hx hflow
  have hfieldOn : ContinuousOn field (Metric.closedBall center r) := by
    intro x hx
    exact (hregular x hx).continuousAt.continuousWithinAt
  have hfieldAt : ∀ x ∈ Metric.ball center r, ContinuousAt field x := by
    intro x hx
    exact (hregular x (Metric.ball_subset_closedBall hx)).continuousAt
  have hfiniteIcc := exists_compact_invariant_trajectory_on_every_finite_horizon
    field K center r δ a hr hδ hfieldOn hfieldAt hKcompact hKsubset
    hKsubsetInterior huniform x₀ hx₀
  have hfinite : ∀ n : ℕ, ∃ trajectory : ℝ → E,
      trajectory a = x₀ ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ), trajectory t ∈ K) ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ),
        HasDerivAt trajectory (field (trajectory t)) t) := by
    intro n
    obtain ⟨trajectory, hinit, hstay, hflow⟩ := hfiniteIcc n
    exact ⟨trajectory, hinit, hstay, hflow⟩
  exact exists_global_forward_trajectory_of_finite_horizon_solutions
    field K center r δ a hδ hregular hKsubset hKsubsetInterior x₀ hx₀ hfinite

/-- The coherent family of finite-horizon solutions defines one forward
identity-mobility orbit for all future times. A local solution around the
initial time supplies the small backward neighborhood needed to express the
ODE on an open interval containing the initial state. -/
theorem exists_global_forward_effective_gradient_flow_of_threshold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (gradV gradS : E → E) (HS : E → E →L[ℝ] E)
    (hcenter : gradS center = 0)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (hfield : Continuous (fun x => -(gradV x - (κ * p) • gradS x)))
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(gradV y - (κ * p) • gradS y)) x)
    (a : ℝ) (x₀ : E) (hx₀ : x₀ ∈ Metric.closedBall center r) :
    ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
      (∀ t ∈ Set.Ici a, trajectory t ∈ Metric.closedBall center r) ∧
      (∀ t ∈ Set.Ioi (a - ε),
        HasDerivAt trajectory
          (-(gradV (trajectory t) - (κ * p) • gradS (trajectory t))) t) := by
  let field : E → E := fun x => -(gradV x - (κ * p) • gradS x)
  have hregular : ∀ x ∈ Metric.closedBall center r, ContDiffAt ℝ 1 field x := by
    intro x hx
    exact hfieldC1 x hx
  obtain ⟨δ, hδ, hfinite⟩ := exists_effective_gradient_flow_on_every_finite_horizon
    center r κ p m β B hr hκ hm hB hp gradV gradS HS hcenter hHS hSlower hVbound
    hfield hfieldC1 a x₀ hx₀
  let endpoint : ℕ → ℝ := fun n => a + ((n + 1 : ℕ) : ℝ) * δ
  let orbit : ℕ → ℝ → E := fun n => Classical.choose (hfinite n)
  have horbit (n : ℕ) : orbit n a = x₀ ∧
      (∀ t ∈ Set.Ico a (endpoint n),
        orbit n t ∈ Metric.closedBall center r) ∧
      (∀ t ∈ Set.Ico a (endpoint n),
        HasDerivAt (orbit n) (field (orbit n t)) t) := by
    have hspec := Classical.choose_spec (hfinite n)
    constructor
    · change Classical.choose (hfinite n) a = x₀
      exact hspec.1
    · constructor
      · intro t ht
        change Classical.choose (hfinite n) t ∈ Metric.closedBall center r
        exact hspec.2.1 t ht
      · intro t ht
        change HasDerivAt (Classical.choose (hfinite n))
          (field (Classical.choose (hfinite n) t)) t
        simpa [field] using hspec.2.2 t ht
  have hcoherent (m n : ℕ) (t : ℝ)
      (hmemb : t ∈ Set.Ico a (endpoint m))
      (hnemb : t ∈ Set.Ico a (endpoint n)) : orbit m t = orbit n t := by
    have hEq := finite_horizon_trajectories_coherent field center r a
      (endpoint m) (endpoint n) hregular (orbit m) (orbit n)
      (horbit m).2.1 (horbit n).2.1 (horbit m).2.2 (horbit n).2.2 (by
        rw [(horbit m).1, (horbit n).1])
    exact hEq ⟨hmemb.1, lt_min hmemb.2 hnemb.2⟩
  have hindex : ∀ t : ℝ, a < t → ∃ n : ℕ, t < endpoint n := by
    intro t hta
    obtain ⟨n, hn⟩ := exists_nat_gt ((t - a) / δ)
    refine ⟨n, ?_⟩
    have hscaled : t - a < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
    dsimp [endpoint]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg n) hδ.le]
  let index : ∀ t : ℝ, a < t → ℕ := fun t ht => Classical.choose (hindex t ht)
  have hindex_spec (t : ℝ) (ht : a < t) : t < endpoint (index t ht) :=
    Classical.choose_spec (hindex t ht)
  obtain ⟨ε₀, hε₀, initial, hinitial, hinitialFlow⟩ :=
    exists_local_trajectory_of_contDiffAt field x₀ (hregular x₀ hx₀) a
  let ε : ℝ := min (ε₀ / 2) (δ / 2)
  have hε : 0 < ε := by dsimp [ε]; exact lt_min (half_pos hε₀) (half_pos hδ)
  have hε₀bound : ε ≤ ε₀ / 2 := min_le_left _ _
  have hεδbound : ε ≤ δ / 2 := min_le_right _ _
  have hinitialStart : ‖initial a - center‖ ^ 2 ≤ r ^ 2 := by
    rw [hinitial]
    have hdist := Metric.mem_closedBall.mp hx₀
    rw [dist_eq_norm] at hdist
    nlinarith [norm_nonneg (x₀ - center), le_of_lt hr]
  have hinitialClosedFlow : ∀ t ∈ Set.Icc a (a + ε),
      HasDerivAt initial (field (initial t)) t := by
    intro t ht
    apply hinitialFlow t
    constructor
    · linarith [ht.1, hε₀]
    · dsimp [ε] at ht
      linarith [ht.2, hε₀, hδ]
  have hinitialCont : ContinuousOn initial (Set.Icc a (a + ε)) := by
    intro t ht
    exact (hinitialClosedFlow t ht).continuousAt.continuousWithinAt
  have hinitialStay := effective_gradient_flow_stays_in_closedBall_of_threshold
    initial center r κ p m β B hr hκ hm hB hp gradV gradS HS hcenter hHS
    hSlower hVbound a (a + ε) (le_of_lt (by linarith [hε])) hinitialStart
    hinitialCont hinitialClosedFlow
  have hpreEq : Set.EqOn initial (orbit 0) (Set.Ico a (a + ε)) := by
    have hδendpoint : a + ε ≤ endpoint 0 := by
      simp [endpoint]
      linarith [hεδbound, hδ]
    apply ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall
      field center r a (a + ε) hregular initial (orbit 0)
    · intro t ht
      exact hinitialStay t ⟨ht.1, le_of_lt ht.2⟩
    · intro t ht
      exact (horbit 0).2.1 t ⟨ht.1, lt_of_lt_of_le ht.2 hδendpoint⟩
    · intro t ht
      exact hinitialClosedFlow t ⟨ht.1, le_of_lt ht.2⟩
    · intro t ht
      exact (horbit 0).2.2 t ⟨ht.1, lt_of_lt_of_le ht.2 hδendpoint⟩
    · exact hinitial.trans (horbit 0).1.symm
  let trajectory : ℝ → E := fun t =>
    if ht : a < t then orbit (index t ht) t else initial t
  have htrajectoryInit : trajectory a = x₀ := by
    simp [trajectory, hinitial]
  have htrajectoryBall : ∀ t ∈ Set.Ici a,
      trajectory t ∈ Metric.closedBall center r := by
    intro t ht
    by_cases hta : a < t
    · let n := index t hta
      have hEnd := hindex_spec t hta
      simpa [trajectory, hta] using
        (horbit n).2.1 t ⟨ht, hEnd⟩
    · have hEq : t = a := le_antisymm (le_of_not_gt hta) ht
      subst t
      simpa [trajectory, hinitial] using hx₀
  have htrajectoryODE : ∀ t ∈ Set.Ioi (a - ε),
      HasDerivAt trajectory (field (trajectory t)) t := by
    intro t ht
    by_cases hta : a < t
    · let n := index t hta
      have hEnd := hindex_spec t hta
      have hevent : trajectory =ᶠ[𝓝 t] orbit n := by
        filter_upwards [Ioi_mem_nhds hta, Iio_mem_nhds hEnd] with s hsa hsend
        have hs : a < s := by simpa using hsa
        have hsend' : s < endpoint n := by simpa using hsend
        let m := index s hs
        have hmend := hindex_spec s hs
        have hsame := hcoherent m n s
          ⟨le_of_lt hs, hmend⟩ ⟨le_of_lt hs, hsend'⟩
        simp [trajectory, hs, hsame, m]
      have hflow := (horbit n).2.2 t ⟨le_of_lt hta, hEnd⟩
      simpa [field, trajectory, hta] using hflow.congr_of_eventuallyEq hevent
    · by_cases hta' : t < a
      · have hmem : t ∈ Set.Ioo (a - ε₀) (a + ε₀) := by
          change a - ε < t at ht
          constructor <;> linarith [ht, hε₀bound, hta']
        have hevent : trajectory =ᶠ[𝓝 t] initial := by
          filter_upwards [Iio_mem_nhds hta'] with s hs
          change s < a at hs
          simp [trajectory, not_lt_of_ge (le_of_lt hs)]
        simpa [field, trajectory, hta] using
          hinitialFlow t hmem |>.congr_of_eventuallyEq hevent
      · have htaeq : t = a := le_antisymm (le_of_not_gt hta) (le_of_not_gt hta')
        subst t
        have hevent : trajectory =ᶠ[𝓝 a] initial := by
          have hlo : a - ε < a := by linarith [hε]
          have hhi : a < a + ε := by linarith [hε]
          filter_upwards [Ioi_mem_nhds hlo, Iio_mem_nhds hhi] with s hslo hshi
          change a - ε < s at hslo
          change s < a + ε at hshi
          by_cases hsa : a < s
          · have hend0 : s < endpoint 0 := by
              have : s < a + ε := hshi
              have hend : a + ε ≤ endpoint 0 := by
                simp [endpoint]
                linarith [hεδbound, hδ]
              exact lt_of_lt_of_le this hend
            let m := index s hsa
            have hmend := hindex_spec s hsa
            have hmend' : s < endpoint m := by simpa [m] using hmend
            have hsame := hcoherent m 0 s
              ⟨le_of_lt hsa, hmend'⟩ ⟨le_of_lt hsa, hend0⟩
            have hpre := hpreEq ⟨le_of_lt hsa, hshi⟩
            have hsame' : orbit m s = initial s := hsame.trans hpre.symm
            simpa [trajectory, hsa, hsame']
          · simp [trajectory, hsa]
        have hflow := hinitialFlow a (by
          constructor <;> linarith [hε₀])
        simpa [field, trajectory, hinitial] using hflow.congr_of_eventuallyEq hevent
  exact ⟨trajectory, ε, hε, htrajectoryInit, htrajectoryBall,
    by simpa [field] using htrajectoryODE⟩

/-- In the identity-mobility case, the threshold assumptions give one global
forward orbit, and strong convexity plus the potential chain rule upgrade its
closed-ball invariance to explicit exponential decay for every future time. -/
theorem exists_global_exponentially_decaying_effective_gradient_flow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (center : E) (r κ p m β B c : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m) (hc : 0 < c)
    (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V S : E → ℝ) (gradV gradS : E → E) (HS : E → E →L[ℝ] E)
    (hcenter : gradS center = 0)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (hfield : Continuous (fun x => -(gradV x - (κ * p) • gradS x)))
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(gradV y - (κ * p) • gradS y)) x)
    (hpotential : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt (fun y => V y - κ * p * S y)
        (innerSL ℝ (gradV x - (κ * p) • gradS x)) x)
    (hpotentialC1 : ContDiffOn ℝ 1 (fun y => V y - κ * p * S y)
      (Metric.closedBall center r))
    (hconvex : StronglyConvexOn (Metric.closedBall center r)
      (fun y => V y - κ * p * S y) (fun y => gradV y - (κ * p) • gradS y) c)
    (xstar : E) (hxstar : xstar ∈ Metric.closedBall center r)
    (hstationary : gradV xstar - (κ * p) • gradS xstar = 0)
    (a : ℝ) (x₀ : E) (hx₀ : x₀ ∈ Metric.closedBall center r) :
    ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
      (∀ t ∈ Set.Ici a, trajectory t ∈ Metric.closedBall center r) ∧
      (∀ t ∈ Set.Ici a,
        0 ≤ (V (trajectory a) - κ * p * S (trajectory a)) -
            (V xstar - κ * p * S xstar) ∧
        (V (trajectory t) - κ * p * S (trajectory t)) -
            (V xstar - κ * p * S xstar) ≤
          ((V (trajectory a) - κ * p * S (trajectory a)) -
            (V xstar - κ * p * S xstar)) * Real.exp (-2 * c * (t - a)) ∧
        ‖trajectory t - xstar‖ ≤
          Real.sqrt (2 * ((V (trajectory a) - κ * p * S (trajectory a)) -
            (V xstar - κ * p * S xstar)) / c) * Real.exp (-c * (t - a))) := by
  obtain ⟨trajectory, ε, hε, hinit, hball, hflow⟩ :=
    exists_global_forward_effective_gradient_flow_of_threshold
      center r κ p m β B hr hκ hm hB hp gradV gradS HS hcenter hHS hSlower hVbound
      hfield hfieldC1 a x₀ hx₀
  let potential : E → ℝ := fun x => V x - κ * p * S x
  let gradient : E → E := fun x => gradV x - (κ * p) • gradS x
  refine ⟨trajectory, ε, hε, hinit, hball, ?_⟩
  intro t ht
  have hdecay := gradient_flow_exponential_decay_of_open_ode
    trajectory potential gradient (fun _ => ContinuousLinearMap.id ℝ E)
    (Metric.closedBall center r) (Set.Ioi (a - ε)) c 1 a t hc zero_lt_one ht
    isOpen_Ioi
    (by
      intro s hs
      simpa [potential, gradient, ContinuousLinearMap.id_apply] using
        hfield.continuousAt)
    (by
      intro s hs
      change a ≤ s ∧ s ≤ t at hs
      exact lt_of_lt_of_le (sub_lt_self a hε) hs.1)
    (fun s hs => hball s hs.1)
    xstar hxstar (by simpa [gradient] using hstationary)
    (by simpa [potential, gradient] using hconvex)
    (by
      intro x hx
      simpa [potential, gradient] using hpotential x hx)
    hpotentialC1
    (by simpa [potential, gradient, ContinuousLinearMap.id_apply] using hflow)
    (by
      intro x hx v
      simp [real_inner_self_eq_norm_sq])
  simpa [potential, gradient] using hdecay

/-- Combining the paper's Hessian and gain conditions with local C¹ regularity
rules out a finite right endpoint for an identity-mobility effective-gradient
orbit that starts in the interior of the local ball: the bounded orbit has a
limit in the ball, and Picard--Lindelöf extends it past that endpoint. -/
theorem extend_effective_gradient_flow_past_finite_endpoint_of_threshold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (trajectory : ℝ → E) (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (gradV gradS : E → E) (HS : E → E →L[ℝ] E)
    (hcenter : gradS center = 0)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (a b : ℝ) (hab : a < b)
    (hstart : ‖trajectory a - center‖ ^ 2 ≤ r ^ 2)
    (hfield : Continuous (fun x =>
      -(gradV x - (κ * p) • gradS x)))
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(gradV y - (κ * p) • gradS y)) x)
    (hflow : ∀ t ∈ Set.Ico a b,
      HasDerivAt trajectory
        (-(gradV (trajectory t) - (κ * p) • gradS (trajectory t))) t) :
    ∃ xend c continuation,
      Tendsto trajectory (𝓝[<] b) (𝓝 xend) ∧
      xend ∈ Metric.closedBall center r ∧ b < c ∧ continuation b = xend ∧
      (∀ t ∈ Set.Ioo a c,
        HasDerivAt continuation
          (-(gradV (continuation t) - (κ * p) • gradS (continuation t))) t) := by
  have htrajectory := effective_gradient_flow_stays_in_closedBall_before_endpoint
    trajectory center r κ p m β B hr hκ hm hB hp gradV gradS HS hcenter hHS
    hSlower hVbound a b hab hstart hflow
  exact extend_ode_orbit_past_finite_endpoint_of_closedBall trajectory
    (fun x => -(gradV x - (κ * p) • gradS x)) center a b r hab hr.le hfield hfieldC1
    htrajectory hflow

/-- The C² kernel/base assumptions and the paper's gain threshold jointly
give an interior global minimizer on the closed ball, and strong convexity
makes it unique. This packages Theorem 21's first two conclusions. -/
theorem exists_unique_interior_minimum_of_threshold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (center : E) (r κ p m β B : ℝ) (hr : 0 < r)
    (hκ : 0 < κ) (hm : 0 < m) (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V S : E → ℝ) (gradV gradS : E → E)
    (HV HS : E → E →L[ℝ] E)
    (hVcont : ContinuousOn V (Metric.closedBall center r))
    (hScont : ContinuousOn S (Metric.closedBall center r))
    (hV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt S (innerSL ℝ (gradS x)) x)
    (hHV : ∀ x ∈ Metric.closedBall center r, HasFDerivAt gradV (HV x) x)
    (hHS : ∀ x ∈ Metric.closedBall center r, HasFDerivAt gradS (HS x) x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (HV x v) v)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hcenter : gradS center = 0)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B) :
    ∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * S x) (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * S y = V xstar - κ * p * S xstar → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) := by
  let U := Metric.closedBall center r
  let geff : E → E := fun x => gradV x - (κ * p) • gradS x
  let Veff : E → ℝ := fun x => V x - κ * p * S x
  have hcenter_mem : center ∈ U := by
    simp [U, Metric.mem_closedBall, hr.le]
  have hκp : 0 ≤ κ * p := by
    have hkm : 0 < κ * m := mul_pos hκ hm
    have hmax : 0 ≤ max β (B / r) := le_trans hβ (le_max_left _ _)
    have hp0 : 0 < p := lt_of_le_of_lt (div_nonneg hmax (le_of_lt hkm)) hp
    exact mul_nonneg hκ.le hp0.le
  have hc : 0 < κ * p * m - β :=
    (critical_gain_estimates κ m r β B p hκ hm hr hp).1
  have hconvex : StronglyConvexOn U Veff geff (κ * p * m - β) := by
    exact effective_potential_strongly_convex U V S gradV gradS HV HS κ p m β
      (by simpa [U] using convex_closedBall center r) hV hS hHV hHS hVlower hSlower hκp
  have hVeff_cont : ContinuousOn Veff U := by
    exact hVcont.sub (hScont.const_mul (κ * p))
  have hVeffAt : ∀ x ∈ U, ContinuousAt Veff x := by
    intro x hx
    have h := (hV x hx).sub ((hS x hx).const_mul (κ * p))
    have hfun : Veff = V - fun y => κ * p * S y := by
      funext y
      simp [Veff, mul_assoc]
    rw [hfun]
    exact h.continuousAt
  have hboundary : ∀ x ∈ U, x ∉ interior U →
      ∃ D : E →L[ℝ] ℝ, HasFDerivAt Veff D x ∧ D (center - x) < 0 := by
    intro x hx hnot
    have hdist_le : dist x center ≤ r := by
      simpa [U, Metric.mem_closedBall] using hx
    have hdist_not_lt : ¬ dist x center < r := by
      intro hlt
      exact hnot (Metric.ball_subset_interior_closedBall (Metric.mem_ball.mpr hlt))
    have hdist_le' : dist center x ≤ r := by simpa [dist_comm] using hdist_le
    have hdist_not_lt' : ¬ dist center x < r := by simpa [dist_comm] using hdist_not_lt
    have hdist : dist center x = r := le_antisymm hdist_le' (le_of_not_gt hdist_not_lt')
    have hrx : ‖x - center‖ = r := by simpa [dist_eq_norm, norm_sub_rev] using hdist
    have hdir := boundary_directional_estimates_of_hessian U center x gradV gradS HS B m r
      (by simpa [U] using convex_closedBall center r) hcenter_mem hx hcenter hHS hSlower
      (hVbound x hx) hrx
    have hradial := effective_radial_gradient_positive κ m r β B p
      (inner ℝ (gradV x) (x - center)) (inner ℝ (gradS x) (x - center)) 1
      hκ hm hr hB hp (by simpa using hdir.1) (by simpa using hdir.2)
    have hgradpos : inner ℝ (geff x) (x - center) > 0 := by
      have hradial' :
          inner ℝ (gradV x) (x - center) - κ * p *
            inner ℝ (gradS x) (x - center) > 0 := by
        simpa using hradial
      simpa [geff, inner_sub_left, inner_smul_left, star_trivial] using hradial'
    let D : E →L[ℝ] ℝ := innerSL ℝ (geff x)
    have hD : HasFDerivAt Veff D x := by
      have h := (hV x hx).sub ((hS x hx).const_mul (κ * p))
      convert h using 1 <;> simp [Veff, D, geff, inner_smul_left]
    have hDinward : D (center - x) < 0 := by
      have heq : center - x = -(x - center) := by abel
      change inner ℝ (geff x) (center - x) < 0
      rw [heq, inner_neg_right]
      exact neg_lt_zero.mpr hgradpos
    exact ⟨D, hD, hDinward⟩
  have hcentergrad : ‖geff center‖ ≤ B := by
    simpa [geff, hcenter] using hVbound center hcenter_mem
  have hbounded : BddBelow (Veff '' U) := by
    refine ⟨Veff center - B * r, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    have hfirst := hconvex center hcenter_mem x hx
    have hdist : ‖x - center‖ ≤ r := by
      have hdist' : dist x center ≤ r := Metric.mem_closedBall.mp hx
      rw [dist_eq_norm] at hdist'
      simpa [norm_sub_rev] using hdist'
    have hprod₁ := mul_le_mul_of_nonneg_right hcentergrad (norm_nonneg (x - center))
    have hprod₂ := mul_le_mul_of_nonneg_left hdist hB
    have hprod : ‖geff center‖ * ‖x - center‖ ≤ B * r := le_trans hprod₁ hprod₂
    have habs := abs_real_inner_le_norm (geff center) (x - center)
    have hinner : -(B * r) ≤ inner ℝ (geff center) (x - center) := by
      have hinner' := (abs_le.mp habs).1
      nlinarith
    nlinarith [hfirst]
  have hminimum := exists_minimum_of_stronglyConvexOn_of_complete U Veff geff
    (κ * p * m - β) Metric.isClosed_closedBall (convex_closedBall center r)
    ⟨center, hcenter_mem⟩ hVeffAt hconvex hc hbounded
  obtain ⟨xstar, hxstar, hmin⟩ :=
    exists_interior_minimum_of_radial_boundary_derivative_of_exists_minimum
      center r hr.le Veff hminimum hboundary
  have hinterior_nhds : interior U ∈ 𝓝 xstar := isOpen_interior.mem_nhds hxstar
  have hU_nhds : U ∈ 𝓝 xstar := Filter.mem_of_superset hinterior_nhds interior_subset
  have hlocal : IsLocalMin Veff xstar := hmin.isLocalMin hU_nhds
  have hVeff_deriv : HasFDerivAt Veff (innerSL ℝ (geff xstar)) xstar := by
    have h := (hV xstar (interior_subset hxstar)).sub
      ((hS xstar (interior_subset hxstar)).const_mul (κ * p))
    convert h using 1 <;> simp [Veff, geff, inner_smul_left]
  have hstationary_map := hlocal.hasFDerivAt_eq_zero hVeff_deriv
  have hstationary : geff xstar = 0 := by
    have heval := congrArg (fun D : E →L[ℝ] ℝ => D (geff xstar)) hstationary_map
    have hinner : inner ℝ (geff xstar) (geff xstar) = 0 := by
      simpa [innerSL_apply_apply] using heval
    have hnorm : ‖geff xstar‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hinner
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hunique := stationary_point_is_unique_minimum_on_region Veff geff
    (κ * p * m - β) hc U hconvex xstar (interior_subset hxstar) hstationary
  have hdisplacement := minimizer_displacement_bound Veff geff
    (κ * p * m - β) B hc hB U hconvex xstar center
    (interior_subset hxstar) hcenter_mem hstationary hcentergrad
  exact ⟨xstar, hxstar, hmin,
    (fun y hy heq => hunique.2 y hy heq), hdisplacement⟩

/-- Derive the first two conclusions of Theorem 21 directly for an
integral reconstruction kernel. The dominated differentiation package turns
the integral into the gradient/Hessian data required by the local-valley
threshold theorem, which then gives an interior unique minimizer and its
quantitative displacement bound. -/
theorem theorem21_integral_kernel_interior_minimum
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V : E → ℝ) (gradV : E → E) (hessV : E → E →L[ℝ] E)
    (kernel : E → X → ℝ) (gradKernel : E → X → E)
    (hessKernel : E → X → E →L[ℝ] E)
    (hVcont : ContinuousOn V (Metric.closedBall center r))
    (hV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hHV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradV (hessV x) x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (hessV x v) v)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (hmeanHessianDom : HasDominatedContinuousReconstructionHessian μ hessKernel)
    (hkernelDiff : ∀ x ∈ Metric.closedBall center r,
      HasDominatedReconstructionKernelFDerivAt μ kernel gradKernel x)
    (hgradientDiff : ∀ x : E,
      HasDominatedReconstructionGradientFDerivAt μ gradKernel hessKernel x)
    (hcenterGradientZero : ∀ᵐ a ∂μ, gradKernel center a = 0)
    (hkernelCurvature : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      ∀ᵐ a ∂μ, inner ℝ (hessKernel x a v) v ≤ -m * ‖v‖ ^ 2) :
    ∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * (∫ a, kernel x a ∂μ))
        (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * (∫ a, kernel y a ∂μ) =
          V xstar - κ * p * (∫ a, kernel xstar a ∂μ) → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) := by
  have hcenterInterior : center ∈ interior (Metric.closedBall center r) :=
    Metric.ball_subset_interior_closedBall (by
      simpa [Metric.mem_ball] using hr)
  have hmeanHessianContinuous := mean_reconstruction_hessian_continuous_of_dominated
    μ hessKernel hmeanHessianDom
  have hmeanGradientC1On : ContDiffOn ℝ 1
      (fun x => ∫ a, gradKernel x a ∂μ) Set.univ :=
    integral_reconstruction_mean_gradient_contDiffOn_one μ Set.univ
      gradKernel hessKernel (fun x _ => hgradientDiff x)
      hmeanHessianContinuous.continuousOn convex_univ ⟨center, by simp⟩
  have hmeanGradientC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => ∫ a, gradKernel y a ∂μ) x := by
    intro x _
    exact hmeanGradientC1On.contDiffAt Filter.univ_mem
  have hhessianIntegrable : ∀ x ∈ Metric.closedBall center r,
      MeasureTheory.Integrable (hessKernel x) μ := by
    rcases hmeanHessianDom with ⟨bound, hmeas, hbound, hboundIntegrable, _⟩
    have hboundNorm : MeasureTheory.Integrable (fun a => |bound a|) μ := by
      simpa [Real.norm_eq_abs] using hboundIntegrable.norm
    intro x _
    apply hboundNorm.mono' (hmeas x)
    filter_upwards [hbound x] with a ha
    have hbound_nonneg : 0 ≤ bound a := le_trans (norm_nonneg _) ha
    simpa [Real.norm_eq_abs, abs_of_nonneg hbound_nonneg] using ha
  have hmeanCurvature : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ ((∫ a, hessKernel x a ∂μ) v) v ≤ -m * ‖v‖ ^ 2 := by
    intro x hx v
    exact mean_hessian_curvature_of_ae μ (fun a => hessKernel x a) x m v
      (hhessianIntegrable x hx) (hkernelCurvature x hx v)
  rcases hgradientDiff center with
    ⟨_, _, _, _, hcenterGradientIntegrable, _, _, _, _⟩
  have hmeanCenterZero := probability_integral_gradient_eq_zero μ
    (gradKernel center) hcenterGradientIntegrable hcenterGradientZero
  have hpotentialC1 := integral_reconstruction_potential_contDiffOn_one μ
    (Metric.closedBall center r) kernel gradKernel hmeanGradientC1 hkernelDiff
    (convex_closedBall center r) ⟨center, hcenterInterior⟩
  have hkernel := general_reconstruction_kernel_conditions μ
    (Metric.closedBall center r) kernel
    gradKernel hessKernel center m hpotentialC1 hmeanGradientC1
    hkernelDiff (fun x _ => hgradientDiff x) hmeanCenterZero hhessianIntegrable
    hmeanCurvature
  rcases hkernel with ⟨hSc1, hSderiv, _hgradSc1, hHS, hcenter, hSlower⟩
  let S : E → ℝ := fun x => ∫ a, kernel x a ∂μ
  let gradS : E → E := fun x => ∫ a, gradKernel x a ∂μ
  let HS : E → E →L[ℝ] E := fun x => ∫ a, hessKernel x a ∂μ
  have hScont : ContinuousOn S (Metric.closedBall center r) := by
    simpa [S] using hSc1.continuousOn
  have hS' : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt S (innerSL ℝ (gradS x)) x := by
    intro x hx
    simpa [S, gradS] using hSderiv x hx
  have hHS' : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x := by
    intro x hx
    simpa [gradS, HS] using hHS x hx
  have hcenter' : gradS center = 0 := by
    simpa [gradS] using hcenter
  have hSlower' : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2 := by
    intro x hx v
    exact hSlower x hx v
  exact exists_unique_interior_minimum_of_threshold center r κ p m β B
    hr hκ hm hβ hB hp V S gradV gradS hessV HS
    hVcont hScont hV hS' hHV hHS' hVlower hSlower' hcenter' hVbound

/-- C¹ regularity of the potential and trajectory supplies the absolute
continuity hypothesis used by the exponential estimate. The trajectory must
map the time interval into the region where the potential is C¹. -/
theorem potential_gap_absolutelyContinuous_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (U : Set E)
    (xstar : E) (t₀ t : ℝ)
    (hpotential : ContDiffOn ℝ 1 potential U)
    (htrajectory : ContDiffOn ℝ 1 trajectory (Set.uIcc t₀ t))
    (hmem : Set.MapsTo trajectory (Set.uIcc t₀ t) U) :
    AbsolutelyContinuousOnInterval
      (fun s => potential (trajectory s) - potential xstar) t₀ t := by
  have hcomp : ContDiffOn ℝ 1 (potential ∘ trajectory) (Set.uIcc t₀ t) :=
    hpotential.comp htrajectory hmem
  have hcomp_ac := hcomp.absolutelyContinuousOnInterval
  have hconst : ContDiffOn ℝ 1 (fun _ : ℝ => potential xstar) (Set.uIcc t₀ t) :=
    contDiffOn_const
  have hconst_ac := hconst.absolutelyContinuousOnInterval
  have hsub := hcomp_ac.sub hconst_ac
  change AbsolutelyContinuousOnInterval
    ((potential ∘ trajectory) - (fun _ : ℝ => potential xstar)) t₀ t at hsub
  convert hsub using 1 <;> funext s <;> rfl

/-- The general state-dependent-mobility part of Theorem 21, under its stated
forward-invariant-sublevel hypothesis. The mobility may vary with the state;
uniform coercivity gives the quantitative rate. The theorem assumes the orbit
and invariant region supplied in the paper's hypothesis, rather than deriving
that invariant region from the Hessian threshold alone. -/
theorem theorem21_state_dependent_mobility_exponential_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (A : E → E →L[ℝ] E) (U C : Set E) (I : Set ℝ) (c gamma t₀ t : ℝ)
    (hc : 0 < c) (hgamma : 0 < gamma) (ht : t₀ ≤ t)
    (hI : IsOpen I)
    (hfield : ∀ s ∈ I,
      ContinuousAt (fun x => -(A x (gradient x))) (trajectory s))
    (htime : Set.Icc t₀ t ⊆ I)
    (hCsub : C ⊆ U)
    (htrajectory_mem : ∀ s ∈ Set.Icc t₀ t, trajectory s ∈ C)
    (xstar : E) (hxstar : xstar ∈ C)
    (hstationary : gradient xstar = 0)
    (hconvex : StronglyConvexOn U potential gradient c)
    (hpotential : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hpotential_c1 : ContDiffOn ℝ 1 potential U)
    (hflow : ∀ s ∈ I,
      HasDerivAt trajectory (-(A (trajectory s) (gradient (trajectory s)))) s)
    (hcoercive : ∀ x ∈ U, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    0 ≤ potential (trajectory t₀) - potential xstar ∧
      potential (trajectory t) - potential xstar ≤
        (potential (trajectory t₀) - potential xstar) *
          Real.exp (-2 * gamma * c * (t - t₀)) ∧
      ‖trajectory t - xstar‖ ≤
        Real.sqrt (2 * (potential (trajectory t₀) - potential xstar) / c) *
          Real.exp (-gamma * c * (t - t₀)) := by
  have htrajectory_mem_U : ∀ s ∈ Set.Icc t₀ t, trajectory s ∈ U := by
    intro s hs
    exact hCsub (htrajectory_mem s hs)
  have hxstarU : xstar ∈ U := hCsub hxstar
  exact gradient_flow_exponential_decay_of_open_ode trajectory potential gradient A U I
    c gamma t₀ t hc hgamma ht hI hfield
    htime htrajectory_mem_U xstar hxstarU
    hstationary hconvex hpotential hpotential_c1 hflow hcoercive

/-- Global-time form of Theorem 21's state-dependent-mobility conclusion.
The forward solution is part of the hypothesis, and `htrajectory_sublevel`
states that it starts in and remains in the paper's forward-invariant sublevel
set. Thus this theorem establishes the full quantitative decay conclusion
under the paper's conditional existence and invariance assumptions. -/
theorem theorem21_state_dependent_mobility_global_exponential_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (A : E → E →L[ℝ] E) (U C : Set E) (c gamma t₀ : ℝ)
    (hc : 0 < c) (hgamma : 0 < gamma)
    (hfield : Continuous (fun x => -(A x (gradient x))))
    (hCsub : C ⊆ U)
    (htrajectory_sublevel : ∀ t ∈ Set.Ici t₀, trajectory t ∈ C)
    (xstar : E) (hxstar : xstar ∈ C)
    (hstationary : gradient xstar = 0)
    (hconvex : StronglyConvexOn U potential gradient c)
    (hpotential : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hpotential_c1 : ContDiffOn ℝ 1 potential U)
    (hflow : ∀ t,
      HasDerivAt trajectory (-(A (trajectory t) (gradient (trajectory t)))) t)
    (hcoercive : ∀ x ∈ U, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∀ t ∈ Set.Ici t₀,
      0 ≤ potential (trajectory t₀) - potential xstar ∧
      potential (trajectory t) - potential xstar ≤
        (potential (trajectory t₀) - potential xstar) *
          Real.exp (-2 * gamma * c * (t - t₀)) ∧
      ‖trajectory t - xstar‖ ≤
        Real.sqrt (2 * (potential (trajectory t₀) - potential xstar) / c) *
          Real.exp (-gamma * c * (t - t₀)) := by
  intro t ht
  exact theorem21_state_dependent_mobility_exponential_decay trajectory potential
    gradient A U C Set.univ c gamma t₀ t hc hgamma ht isOpen_univ
    (fun s _ => hfield.continuousAt)
    (Set.subset_univ _) hCsub (fun s hs => htrajectory_sublevel s hs.1)
    xstar hxstar hstationary hconvex hpotential hpotential_c1
    (fun s _ => hflow s) hcoercive

/-- Global existence and quantitative decay for Theorem 21 with a
state-dependent mobility. The invariant set itself need not be closed: its
closure is required to lie inside the local ball. Compactness of that closure
supplies a uniform local existence time, while forward invariance keeps every
restart point in the original set. -/
theorem theorem21_state_dependent_mobility_global_existence_and_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (center : E) (r a c gamma : ℝ)
    (hr : 0 ≤ r) (hc : 0 < c) (hgamma : 0 < gamma)
    (potential : E → ℝ) (gradient : E → E) (A : E → E →L[ℝ] E)
    (U C : Set E) (xstar x₀ : E)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (gradient y))) x)
    (hCclosureInterior : closure C ⊆ Metric.ball center r)
    (hinvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit t₀ = x → x ∈ C →
      (∀ t ∈ Set.Icc t₀ (t₀ + d),
        HasDerivAt orbit (-(A (orbit t) (gradient (orbit t)))) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ C)
    (hCsub : C ⊆ U)
    (hxstar : xstar ∈ C) (hx₀ : x₀ ∈ C)
    (hstationary : gradient xstar = 0)
    (hconvex : StronglyConvexOn U potential gradient c)
    (hpotential : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hpotential_c1 : ContDiffOn ℝ 1 potential U)
    (hcoercive : ∀ x ∈ U, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
      (∀ t ∈ Set.Ioi (a - ε),
        HasDerivAt trajectory (-(A (trajectory t) (gradient (trajectory t)))) t) ∧
      (∀ t ∈ Set.Ici a, trajectory t ∈ C) ∧
      (∀ t ∈ Set.Ici a,
        0 ≤ potential (trajectory a) - potential xstar ∧
        potential (trajectory t) - potential xstar ≤
          (potential (trajectory a) - potential xstar) *
            Real.exp (-2 * gamma * c * (t - a)) ∧
        ‖trajectory t - xstar‖ ≤
          Real.sqrt (2 * (potential (trajectory a) - potential xstar) / c) *
            Real.exp (-gamma * c * (t - a))) ∧
      (∀ other : ℝ → E, other a = x₀ →
        (∀ t ∈ Set.Ici a, other t ∈ C) →
        (∀ t ∈ Set.Ioi (a - ε),
          HasDerivAt other (-(A (other t) (gradient (other t)))) t) →
        ∀ t ∈ Set.Ici a, other t = trajectory t) := by
  have hCinterior : C ⊆ Metric.ball center r := by
    intro x hx
    exact hCclosureInterior (subset_closure hx)
  have hCball : C ⊆ Metric.closedBall center r :=
    hCinterior.trans Metric.ball_subset_closedBall
  have hclosureBall : closure C ⊆ Metric.closedBall center r := by
    exact closure_minimal hCball Metric.isClosed_closedBall
  have hclosureCompact : IsCompact (closure C) :=
    (isCompact_closedBall center r).of_isClosed_subset isClosed_closure hclosureBall
  have hclosureNonempty : (closure C).Nonempty := ⟨x₀, subset_closure hx₀⟩
  let field : E → E := fun x => -(A x (gradient x))
  have hregularClosure : ∀ x ∈ closure C, ContDiffAt ℝ 1 field x := by
    intro x hx
    exact hfieldC1 x (hclosureBall hx)
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_forward_local_trajectory_on_compact
    field (closure C) hclosureCompact hclosureNonempty hregularClosure
  have huniform : ∀ t₀ : ℝ, ∀ x ∈ C,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        ∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit (field (localOrbit t)) t := by
    intro t₀ x hx
    exact hlocal t₀ x (subset_closure hx)
  have hfieldOnC : ∀ x ∈ C, ContinuousAt field x := by
    intro x hx
    exact (hfieldC1 x (hCball hx)).continuousAt
  have hfiniteIcc := exists_forward_invariant_trajectory_on_every_finite_horizon
    field C δ a hδ hfieldOnC hinvariant huniform x₀ hx₀
  have hfinite : ∀ n : ℕ, ∃ orbit : ℝ → E,
      orbit a = x₀ ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ), orbit t ∈ C) ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ),
        HasDerivAt orbit (field (orbit t)) t) := by
    intro n
    obtain ⟨orbit, hinit, hstay, hflow⟩ := hfiniteIcc n
    exact ⟨orbit, hinit,
      (fun t ht => hstay t ⟨ht.1, le_of_lt ht.2⟩),
      (fun t ht => hflow t ⟨ht.1, le_of_lt ht.2⟩)⟩
  obtain ⟨trajectory, ε, hε, hinit, htrajectoryC, hflow, htrajectoryBall⟩ :=
    exists_global_forward_trajectory_of_finite_horizon_solutions
      field C center r δ a hδ hfieldC1 hCball hCinterior x₀ hx₀ hfinite
  refine ⟨trajectory, ε, hε, hinit, hflow, htrajectoryC, ?_, ?_⟩
  · intro t ht
    have htime : Set.Icc a t ⊆ Set.Ioi (a - ε) := by
      intro s hs
      change a - ε < s
      change a ≤ s ∧ s ≤ t at hs
      linarith [hs.1, hε]
    have hCinterval : ∀ s ∈ Set.Icc a t, trajectory s ∈ C := by
      intro s hs
      apply htrajectoryC s
      change a ≤ s ∧ s ≤ t at hs
      exact hs.1
    exact theorem21_state_dependent_mobility_exponential_decay trajectory potential
      gradient A U C (Set.Ioi (a - ε)) c gamma a t hc hgamma ht isOpen_Ioi
      (fun s hs => (hfieldC1 (trajectory s)
        (Metric.ball_subset_closedBall (htrajectoryBall s hs))).continuousAt)
      htime hCsub hCinterval xstar hxstar hstationary hconvex hpotential
      hpotential_c1 hflow hcoercive
  · intro other hotherInit hotherC hotherFlow t ht
    change a ≤ t at ht
    let b : ℝ := t + 1
    have hab : a < b := by dsimp [b]; linarith
    have hEq := theorem21_state_dependent_closed_loop_unique_on_ball A gradient
      center r a b hfieldC1 trajectory other
      (fun s hs => Metric.ball_subset_closedBall
        (htrajectoryBall s (by
          have hleft : a - ε < s := by linarith [hs.1, hε]
          exact hleft)))
      (fun s hs => hCball (hotherC s hs.1))
      (fun s hs => hflow s (by
        have hleft : a - ε < s := by linarith [hs.1, hε]
        exact hleft))
      (fun s hs => hotherFlow s (by
        have hleft : a - ε < s := by linarith [hs.1, hε]
        exact hleft))
      (by rw [hinit, hotherInit])
    exact (hEq ⟨ht, by dsimp [b]; linarith⟩).symm

/-- Dimension-free global existence and decay when a uniform local solution
time and closed-ball ODE uniqueness are supplied. In finite dimensions these
two facts follow from compactness and C¹ regularity; in a general complete
normed space they are explicit hypotheses. -/
theorem theorem21_state_dependent_mobility_global_existence_and_decay_of_uniform_local_solutions
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (center : E) (r a c gamma δ : ℝ)
    (hr : 0 ≤ r) (hc : 0 < c) (hgamma : 0 < gamma) (hδ : 0 < δ)
    (potential : E → ℝ) (gradient : E → E) (A : E → E →L[ℝ] E)
    (U C : Set E) (xstar x₀ : E)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (gradient y))) x)
    (hCclosureInterior : closure C ⊆ Metric.ball center r)
    (hinvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit t₀ = x → x ∈ C →
      (∀ t ∈ Set.Icc t₀ (t₀ + d),
        HasDerivAt orbit (-(A (orbit t) (gradient (orbit t)))) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ C)
    (hlocal : ∀ t₀ : ℝ, ∀ x ∈ C,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        ∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit (-(A (localOrbit t) (gradient (localOrbit t)))) t)
    (L : ℝ≥0)
    (hL : LipschitzOnWith L (fun y => -(A y (gradient y)))
      (Metric.closedBall center r))
    (hCsub : C ⊆ U)
    (hxstar : xstar ∈ C) (hx₀ : x₀ ∈ C)
    (hstationary : gradient xstar = 0)
    (hconvex : StronglyConvexOn U potential gradient c)
    (hpotential : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hpotential_c1 : ContDiffOn ℝ 1 potential U)
    (hcoercive : ∀ x ∈ U, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
      (∀ t ∈ Set.Ici a, trajectory t ∈ C) ∧
      (∀ t ∈ Set.Ici a,
        0 ≤ potential (trajectory a) - potential xstar ∧
        potential (trajectory t) - potential xstar ≤
          (potential (trajectory a) - potential xstar) *
            Real.exp (-2 * gamma * c * (t - a)) ∧
        ‖trajectory t - xstar‖ ≤
          Real.sqrt (2 * (potential (trajectory a) - potential xstar) / c) *
            Real.exp (-gamma * c * (t - a))) ∧
      (∀ other : ℝ → E, other a = x₀ →
        (∀ t ∈ Set.Ici a, other t ∈ C) →
        (∀ t ∈ Set.Ioi (a - ε),
          HasDerivAt other (-(A (other t) (gradient (other t)))) t) →
        ∀ t ∈ Set.Ici a, other t = trajectory t) := by
  have hCinterior : C ⊆ Metric.ball center r := by
    intro x hx
    exact hCclosureInterior (subset_closure hx)
  have hCball : C ⊆ Metric.closedBall center r :=
    hCinterior.trans Metric.ball_subset_closedBall
  let field : E → E := fun x => -(A x (gradient x))
  have hunique : ∀ (u v : ℝ) (f g : ℝ → E),
      (∀ t ∈ Set.Ico u v, f t ∈ Metric.closedBall center r) →
      (∀ t ∈ Set.Ico u v, g t ∈ Metric.closedBall center r) →
      (∀ t ∈ Set.Ico u v, HasDerivAt f (field (f t)) t) →
      (∀ t ∈ Set.Ico u v, HasDerivAt g (field (g t)) t) →
      f u = g u → Set.EqOn f g (Set.Ico u v) := by
    intro u v f g hfball hgball hfflow hgflow hinit
    exact ode_trajectories_eqOn_Ico_of_lipschitz_on_closedBall
      field center r u v L hL f g hfball hgball hfflow hgflow hinit
  have hregular : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 field x := hfieldC1
  have hfieldOnC : ∀ x ∈ C, ContinuousAt field x := by
    intro x hx
    exact (hfieldC1 x (hCball hx)).continuousAt
  have huniform : ∀ t₀ : ℝ, ∀ x ∈ C,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        ∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit (field (localOrbit t)) t := by
    intro t₀ x hx
    obtain ⟨localOrbit, hinit, hflow⟩ := hlocal t₀ x hx
    exact ⟨localOrbit, hinit, fun t ht => by simpa [field] using hflow t ht⟩
  have hfiniteIcc := exists_forward_invariant_trajectory_on_every_finite_horizon
    field C δ a hδ hfieldOnC hinvariant huniform x₀ hx₀
  have hfinite : ∀ n : ℕ, ∃ orbit : ℝ → E,
      orbit a = x₀ ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ), orbit t ∈ C) ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ),
        HasDerivAt orbit (field (orbit t)) t) := by
    intro n
    obtain ⟨orbit, hinit, hstay, hflow⟩ := hfiniteIcc n
    exact ⟨orbit, hinit,
      (fun t ht => hstay t ⟨ht.1, le_of_lt ht.2⟩),
      (fun t ht => hflow t ⟨ht.1, le_of_lt ht.2⟩)⟩
  obtain ⟨trajectory, ε, hε, hinit, htrajectoryC, hflow, htrajectoryBall⟩ :=
    exists_global_forward_trajectory_of_finite_horizon_solutions_of_unique
      field C center r δ a hδ hregular hunique hCball hCinterior x₀ hx₀ hfinite
  refine ⟨trajectory, ε, hε, hinit, htrajectoryC, ?_, ?_⟩
  · intro t ht
    have htime : Set.Icc a t ⊆ Set.Ioi (a - ε) := by
      intro s hs
      change a - ε < s
      change a ≤ s ∧ s ≤ t at hs
      linarith [hs.1, hε]
    have hCinterval : ∀ s ∈ Set.Icc a t, trajectory s ∈ C := by
      intro s hs
      apply htrajectoryC s
      change a ≤ s ∧ s ≤ t at hs
      exact hs.1
    exact theorem21_state_dependent_mobility_exponential_decay trajectory potential
      gradient A U C (Set.Ioi (a - ε)) c gamma a t hc hgamma ht isOpen_Ioi
      (fun s hs => (hfieldC1 (trajectory s)
        (Metric.ball_subset_closedBall (htrajectoryBall s hs))).continuousAt)
      htime hCsub hCinterval xstar hxstar hstationary hconvex hpotential
      hpotential_c1 hflow hcoercive
  · intro other hotherInit hotherC hotherFlow t ht
    change a ≤ t at ht
    have hb : a < t + 1 := by linarith [ht]
    have hEq := hunique a (t + 1) trajectory other
      (fun s hs => Metric.ball_subset_closedBall (htrajectoryBall s
        (by change a - ε < s; linarith [hs.1, hε])))
      (fun s hs => hCball (hotherC s hs.1))
      (fun s hs => hflow s (by change a - ε < s; linarith [hs.1, hε]))
      (fun s hs => by
        have htime : a - ε < s := by
          change a ≤ s ∧ s < t + 1 at hs
          linarith [hs.1, hε]
        have h := hotherFlow s htime
        simpa [field] using h)
      (by rw [hinit, hotherInit])
    exact (hEq ⟨ht, by linarith⟩).symm


end Tomabechi.Theorem21
