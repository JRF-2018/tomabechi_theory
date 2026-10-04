import Tomabechi.Analysis.StrongConvexity

/-! # 定理21の勾配流散逸と局所ODE延長

強凸性核を前提に、勾配散逸からの定量指数評価、Picard–Lindelöf局所解、
有限時間軌道の貼り合わせ・延長を収録。新たなODE仮定や結論変更は行わない。
-/

namespace Tomabechi.Theorem21

open RealInnerProductSpace
open Filter
open scoped Topology NNReal ContDiff

/-- On a forward invariant local region, strong convexity and almost-everywhere
gradient dissipation give the quantitative exponential decay rate from the
paper. The chain rule and the identity between the ODE and the gradient-flow
field remain explicit assumptions in `hdissipation`. -/
theorem potential_gap_exponential_decay_of_gradient_dissipation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (U : Set E) (c gamma t₀ t : ℝ)
    (hc : 0 < c) (hgamma : 0 < gamma) (ht : t₀ ≤ t)
    (htrajectory_mem : ∀ s ∈ Set.Icc t₀ t, trajectory s ∈ U)
    (xstar : E) (hxstar : xstar ∈ U)
    (hstationary : gradient xstar = 0)
    (hconvex : StronglyConvexOn U potential gradient c)
    (hphi_ac : AbsolutelyContinuousOnInterval
      (fun s => potential (trajectory s) - potential xstar) t₀ t)
    (hdissipation : ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc t₀ t),
      deriv (fun r => potential (trajectory r) - potential xstar) s ≤
        -gamma * ‖gradient (trajectory s)‖ ^ 2) :
    0 ≤ potential (trajectory t₀) - potential xstar ∧
      potential (trajectory t) - potential xstar ≤
      (potential (trajectory t₀) - potential xstar) *
        Real.exp (-2 * gamma * c * (t - t₀)) := by
  let phi : ℝ → ℝ := fun s => potential (trajectory s) - potential xstar
  have hphi_nonneg : ∀ s ∈ Set.Icc t₀ t, 0 ≤ phi s := by
    intro s hs
    have hmin := stationary_point_is_unique_minimum_on_region
      potential gradient c hc U hconvex xstar hxstar hstationary
    exact sub_nonneg.mpr (hmin.1 (trajectory s) (htrajectory_mem s hs))
  have hdecay : ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc t₀ t),
      deriv phi s ≤ -2 * (gamma * c) * phi s := by
    filter_upwards [hdissipation,
      MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hsD hsIcc
    have hPL := polyak_gradient_bound_of_strong_convexity
      potential gradient c hc U hconvex xstar (trajectory s) hxstar
      (htrajectory_mem s hsIcc)
    change deriv (fun r => potential (trajectory r) - potential xstar) s ≤
      -gamma * ‖gradient (trajectory s)‖ ^ 2 at hsD
    change deriv (fun r => potential (trajectory r) - potential xstar) s ≤
      -2 * (gamma * c) * (potential (trajectory s) - potential xstar)
    nlinarith [mul_le_mul_of_nonpos_left hPL (neg_nonpos.mpr (le_of_lt hgamma))]
  have hresult := Tomabechi.Theorem1.lyapunov_exponential_decay_of_ac_ae_derivative
    phi (gamma * c) t₀ t (mul_pos hgamma hc) ht
    (by simpa [phi] using hphi_ac) hdecay
  exact ⟨hphi_nonneg t₀ ⟨le_rfl, ht⟩,
    by simpa [phi, mul_assoc, mul_left_comm, mul_comm] using hresult⟩

/-- The closed-loop equation `x' = -A(x) ∇V(x)` and uniform coercivity of
`A` imply the gradient dissipation inequality used by the exponential-decay
lemma. This isolates the analytic chain-rule step from ODE existence. -/
theorem gradient_flow_dissipation_of_ode
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (A : E → E →L[ℝ] E) (U : Set E) (gamma t₀ t : ℝ)
    (hgamma : 0 < gamma) (ht : t₀ ≤ t)
    (htrajectory_mem : ∀ s ∈ Set.Icc t₀ t, trajectory s ∈ U)
    (hpotential : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hflow : ∀ s ∈ Set.Icc t₀ t,
      HasDerivAt trajectory (-(A (trajectory s) (gradient (trajectory s)))) s)
    (hcoercive : ∀ x ∈ U, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∀ s ∈ Set.Icc t₀ t,
      deriv (fun r => potential (trajectory r)) s ≤
        -gamma * ‖gradient (trajectory s)‖ ^ 2 := by
  intro s hs
  have hcomp := (hpotential (trajectory s) (htrajectory_mem s hs)).comp_hasDerivAt_of_eq
    s (hflow s hs) (by rfl)
  have hchain : HasDerivAt (fun r => potential (trajectory r))
      (-inner ℝ (gradient (trajectory s))
        (A (trajectory s) (gradient (trajectory s)))) s := by
    convert hcomp using 1 <;>
      simp [Function.comp_def, innerSL_apply_apply, inner_neg_right]
  have hderiv := hchain.deriv
  have hcoercive' := hcoercive (trajectory s) (htrajectory_mem s hs)
    (gradient (trajectory s))
  have hderiv' : deriv (fun r => potential (trajectory r)) s ≤
      -gamma * ‖gradient (trajectory s)‖ ^ 2 := by
    rw [hderiv]
    have hcomm := real_inner_comm (gradient (trajectory s))
      (A (trajectory s) (gradient (trajectory s)))
    nlinarith [hcoercive']
  exact hderiv'

/-- Dissipation makes the potential along a trajectory antitone. Hence every
potential sublevel that contains the initial state contains the whole segment
of trajectory. The vector field and dissipation hypotheses are required on an
ambient region containing that segment; this lemma alone does not construct the
ODE solution or establish that the ambient region is invariant. -/
theorem potential_sublevel_forward_invariant_of_gradient_flow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (A : E → E →L[ℝ] E) (D : Set E) (gamma t₀ t level : ℝ)
    (hgamma : 0 < gamma) (ht : t₀ ≤ t)
    (htrajectory_mem : ∀ s ∈ Set.Icc t₀ t, trajectory s ∈ D)
    (hpotential : ∀ x ∈ D,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hflow : ∀ s ∈ Set.Icc t₀ t,
      HasDerivAt trajectory (-(A (trajectory s) (gradient (trajectory s)))) s)
    (hcoercive : ∀ x ∈ D, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hinitial : potential (trajectory t₀) ≤ level) :
    ∀ s ∈ Set.Icc t₀ t, potential (trajectory s) ≤ level := by
  let along : ℝ → ℝ := fun s => potential (trajectory s)
  have hderiv := gradient_flow_dissipation_of_ode trajectory potential gradient A D
    gamma t₀ t hgamma ht htrajectory_mem hpotential hflow hcoercive
  have halong_cont : ContinuousOn along (Set.Icc t₀ t) := by
    intro s hs
    have htraj := (hflow s hs).continuousAt
    have hpot := (hpotential (trajectory s) (htrajectory_mem s hs)).continuousAt
    exact (hpot.comp htraj).continuousWithinAt
  have halong_diff : DifferentiableOn ℝ along (interior (Set.Icc t₀ t)) := by
    intro s hs
    have hs' : s ∈ Set.Icc t₀ t := interior_subset hs
    have hcomp := (hpotential (trajectory s) (htrajectory_mem s hs')).comp_hasDerivAt_of_eq
      s (hflow s hs') (by rfl)
    exact hcomp.differentiableAt.differentiableWithinAt
  have halong_deriv : ∀ s ∈ interior (Set.Icc t₀ t), deriv along s ≤ 0 := by
    intro s hs
    have hs' : s ∈ Set.Icc t₀ t := interior_subset hs
    have h := hderiv s hs'
    change deriv (fun r => potential (trajectory r)) s ≤ _ at h
    change deriv along s ≤ 0
    dsimp [along]
    have hnonneg : 0 ≤ gamma * ‖gradient (trajectory s)‖ ^ 2 :=
      mul_nonneg (le_of_lt hgamma) (sq_nonneg _)
    linarith
  have halong_anti : AntitoneOn along (Set.Icc t₀ t) :=
    antitoneOn_of_deriv_nonpos (convex_Icc t₀ t) halong_cont halong_diff halong_deriv
  intro s hs
  have hanti := halong_anti ⟨le_rfl, le_trans hs.1 hs.2⟩ hs hs.1
  change along s ≤ level
  exact hanti.trans (by simpa [along] using hinitial)

/-- A closed-ball sublevel strictly contained in the open ball is forward
invariant for a coercive gradient flow. The energy decreases until any
hypothetical first exit from the closed ball; continuity puts the exit state
back in the sublevel, contradicting strict containment in the open ball. -/
theorem forward_invariant_sublevel_of_strict_interior_barrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (A : E → E →L[ℝ] E) (center : E) (r gamma t₀ t level : ℝ)
    (hgamma : 0 < gamma) (ht : t₀ ≤ t)
    (C : Set E)
    (hCsublevel : C = {x | x ∈ Metric.closedBall center r ∧
      potential x ≤ level})
    (hCinterior : C ⊆ Metric.ball center r)
    (x₀ : E) (hx₀ : x₀ ∈ C)
    (hinit : trajectory t₀ = x₀)
    (hpotential : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hflow : ∀ s ∈ Set.Icc t₀ t,
      HasDerivAt trajectory (-(A (trajectory s) (gradient (trajectory s)))) s)
    (hcoercive : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∀ s ∈ Set.Icc t₀ t, trajectory s ∈ C := by
  have htraj_cont : ContinuousOn trajectory (Set.Icc t₀ t) := by
    intro s hs
    exact (hflow s hs).continuousAt.continuousWithinAt
  have hpotential0 : potential (trajectory t₀) ≤ level := by
    have hx₀' := hx₀
    rw [hCsublevel] at hx₀'
    simpa [hinit] using hx₀'.2
  have hball_all : ∀ s ∈ Set.Icc t₀ t,
      trajectory s ∈ Metric.ball center r := by
    by_contra hnot
    push_neg at hnot
    obtain ⟨sbad, hsbad, hsbadOut⟩ := hnot
    let bad : Set ℝ := Set.Icc t₀ t ∩ {s | trajectory s ∉ Metric.ball center r}
    have hbadClosed : IsClosed bad := by
      have hpre := htraj_cont.preimage_isClosed_of_isClosed
        (t := (Metric.ball center r)ᶜ) isClosed_Icc
        Metric.isOpen_ball.isClosed_compl
      simpa [bad, Set.preimage, Set.mem_compl_iff] using hpre
    have hbadCompact : IsCompact bad :=
      isCompact_Icc.of_isClosed_subset hbadClosed Set.inter_subset_left
    have hbadNonempty : bad.Nonempty := ⟨sbad, hsbad, hsbadOut⟩
    obtain ⟨τ, hτbad, hτmin⟩ :=
      hbadCompact.exists_isMinOn hbadNonempty continuousOn_id
    have hτIcc : τ ∈ Set.Icc t₀ t := hτbad.1
    have hτOut : trajectory τ ∉ Metric.ball center r := hτbad.2
    have hτgt : t₀ < τ := by
      by_contra hnotlt
      have hτeq : τ = t₀ := le_antisymm (le_of_not_gt hnotlt) hτIcc.1
      subst τ
      have hx₀ball : x₀ ∈ Metric.ball center r := hCinterior hx₀
      exact hτOut (by simpa [hinit] using hx₀ball)
    have hbefore : ∀ s ∈ Set.Icc t₀ τ, s < τ →
        trajectory s ∈ Metric.ball center r := by
      intro s hs hslt
      by_contra hsout
      have hsbad : s ∈ bad := ⟨⟨hs.1, le_trans hs.2 hτIcc.2⟩, hsout⟩
      have hτle := hτmin hsbad
      exact (not_le_of_gt hslt) hτle
    have hleft : ∀ᶠ s in 𝓝[<] τ, s ∈ Set.Icc t₀ τ ∧ s < τ := by
      have hlo : ∀ᶠ s in 𝓝[<] τ, t₀ < s :=
        nhdsWithin_le_nhds (Ioi_mem_nhds hτgt)
      filter_upwards [hlo, self_mem_nhdsWithin] with s hlow hhigh
      exact ⟨⟨le_of_lt hlow, le_of_lt hhigh⟩, hhigh⟩
    have hlim : Tendsto trajectory (𝓝[<] τ) (𝓝 (trajectory τ)) :=
      (hflow τ hτIcc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hτClosed : trajectory τ ∈ Metric.closedBall center r :=
      Metric.isClosed_closedBall.mem_of_tendsto hlim
        (hleft.mono fun s hs => Metric.ball_subset_closedBall
          (hbefore s hs.1 hs.2))
    have hpreτ : ∀ s ∈ Set.Icc t₀ τ,
        potential (trajectory s) ≤ level := by
      apply potential_sublevel_forward_invariant_of_gradient_flow
        trajectory potential gradient A (Metric.closedBall center r) gamma
        t₀ τ level hgamma (le_of_lt hτgt)
      · intro s hs
        by_cases hslt : s < τ
        · exact Metric.ball_subset_closedBall (hbefore s hs hslt)
        · have hseq : s = τ := le_antisymm hs.2 (le_of_not_gt hslt)
          subst s
          exact hτClosed
      · exact hpotential
      · intro s hs
        exact hflow s ⟨hs.1, le_trans hs.2 hτIcc.2⟩
      · exact hcoercive
      · simpa [hinit] using hpotential0
    have hτC : trajectory τ ∈ C := by
      rw [hCsublevel]
      exact ⟨hτClosed, hpreτ τ ⟨le_of_lt hτgt, le_rfl⟩⟩
    exact hτOut (hCinterior hτC)
  have htrajectoryClosed : ∀ s ∈ Set.Icc t₀ t,
      trajectory s ∈ Metric.closedBall center r := by
    intro s hs
    exact Metric.ball_subset_closedBall (hball_all s hs)
  have henergy : ∀ s ∈ Set.Icc t₀ t,
      potential (trajectory s) ≤ level := by
    apply potential_sublevel_forward_invariant_of_gradient_flow
      trajectory potential gradient A (Metric.closedBall center r) gamma
      t₀ t level hgamma ht htrajectoryClosed hpotential hflow hcoercive
    simpa [hinit] using hpotential0
  intro s hs
  rw [hCsublevel]
  exact ⟨htrajectoryClosed s hs, henergy s hs⟩

/-- The local ODE existence step available from Mathlib's Picard–Lindelöf
theorem. This gives a solution on the stated compact time interval when the
field satisfies `IsPicardLindelof` on a spatial ball. It is an interface lemma:
the hypotheses still have to be verified for the nonlinear closed-loop field
of a particular instance of Theorem 21. -/
theorem exists_local_trajectory_of_picardLindelof
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    (x₀ x : E) (a r L K : ℝ≥0)
    (hfield : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ Metric.closedBall x₀ r) :
    ∃ trajectory : ℝ → E, trajectory t₀ = x ∧
      ∀ s ∈ Set.Icc tmin tmax,
        HasDerivWithinAt trajectory (f s (trajectory s)) (Set.Icc tmin tmax) s :=
  IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hfield hx

/-- Any continuously differentiable autonomous vector field has a genuine
two-sided local trajectory through the chosen initial state. This applies to
theorem 21's closed-loop field once its local `C¹` regularity is established. -/
theorem exists_local_trajectory_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (x₀ : E) (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ trajectory : ℝ → E,
      trajectory t₀ = x₀ ∧
        ∀ s ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt trajectory (f (trajectory s)) s := by
  obtain ⟨r, hr, ε, hε, hlocal⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  have hx : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr.le
  obtain ⟨trajectory, hinit, hflow⟩ := hlocal x₀ hx
  exact ⟨ε, hε, trajectory, hinit, hflow⟩

/-- Local Picard--Lindelöf existence has a uniform positive time radius for
initial states in a compact set, when the autonomous vector field is C¹ at
every point of that set. The proof takes a finite subcover of the spatial
neighborhoods supplied by `ContDiffAt.exists_forall_mem_closedBall...`. -/
theorem exists_uniform_local_trajectory_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (field : E → E) (K : Set E) (hK : IsCompact K) (hKne : K.Nonempty)
    (hfield : ∀ x ∈ K, ContDiffAt ℝ 1 field x) (t₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∃ trajectory : ℝ → E,
      trajectory t₀ = x ∧
        ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
          HasDerivAt trajectory (field (trajectory t)) t := by
  classical
  have hlocal : ∀ x : K, ∃ R : ℝ, 0 < R ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ Metric.closedBall (x : E) R, ∃ trajectory : ℝ → E,
        trajectory t₀ = y ∧
          ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
            HasDerivAt trajectory (field (trajectory t)) t := by
    intro x
    exact ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
      (hfield x x.property) t₀
  choose R hR ε hε hsolve using hlocal
  let U : K → Set E := fun x => Metric.ball x (R x / 2)
  have hUopen : ∀ x, IsOpen (U x) := fun _ => Metric.isOpen_ball
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro y hy
    let yK : K := ⟨y, hy⟩
    apply Set.mem_iUnion.mpr
    refine ⟨yK, ?_⟩
    change dist y y < R yK / 2
    rw [dist_self]
    exact half_pos (hR yK)
  obtain ⟨s, hscover⟩ := hK.elim_finite_subcover U hUopen hcover
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    rcases Set.mem_iUnion₂.mp (hscover hx) with ⟨i, _, _⟩
    exact ⟨i, ‹i ∈ s›⟩
  let δ : ℝ := (s.image ε).min' (Finset.image_nonempty.mpr hsne)
  have hδpos : 0 < δ := by
    obtain ⟨i, _, hδeq⟩ := Finset.mem_image.mp (Finset.min'_mem (s.image ε)
      (Finset.image_nonempty.mpr hsne))
    simpa [δ, hδeq] using hε i
  refine ⟨δ, hδpos, ?_⟩
  intro x hx
  rcases Set.mem_iUnion₂.mp (hscover hx) with ⟨i, his, hxi⟩
  have hxiBall : x ∈ Metric.closedBall (i : E) (R i) := by
    have hdist := Metric.mem_ball.mp hxi
    change dist x (i : E) ≤ R i
    exact le_trans hdist.le (by linarith [hR i])
  obtain ⟨trajectory, hinit, hflow⟩ := hsolve i x hxiBall
  have hδle : δ ≤ ε i := by
    dsimp [δ]
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨i, his, rfl⟩
  refine ⟨trajectory, hinit, ?_⟩
  intro t ht
  apply hflow
  exact ⟨by linarith [ht.1, hδle], by linarith [ht.2, hδle]⟩

/-- Local existence for the actual closed-loop form `x' = -A(x)∇V(x)` when
both the state-dependent operator and gradient are C¹ at the initial state.
This still leaves their C¹ hypotheses to be verified from the paper's data. -/
theorem exists_local_gradient_flow_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E → E →L[ℝ] E) (gradient : E → E) (x₀ : E)
    (hA : ContDiffAt ℝ 1 A x₀)
    (hgradient : ContDiffAt ℝ 1 gradient x₀) (t₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ trajectory : ℝ → E,
      trajectory t₀ = x₀ ∧
        ∀ s ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt trajectory
            (-(A (trajectory s) (gradient (trajectory s)))) s := by
  have hfield : ContDiffAt ℝ 1 (fun x => -(A x (gradient x))) x₀ := by
    simpa using (hA.clm_apply hgradient).neg
  exact exists_local_trajectory_of_contDiffAt
    (fun x => -(A x (gradient x))) x₀ hfield t₀

/-- The Riesz-represented gradient associated with a scalar potential on a
complete real inner product space. -/
noncomputable def rieszGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (potential : E → ℝ) : E → E :=
  fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ potential x)

/-- The Riesz gradient represents the Fréchet derivative under the inner
product, fixing the convention used in the rest of this file. -/
theorem fderiv_eq_inner_rieszGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (potential : E → ℝ) (x v : E) :
    fderiv ℝ potential x v = inner ℝ (rieszGradient potential x) v := by
  change fderiv ℝ potential x v =
    inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ potential x)) v
  rw [← InnerProductSpace.toDual_symm_apply]

/-- A C² potential has a C¹ Riesz gradient. This supplies the gradient
regularity needed by the local existence theorem, provided the potential's
second-order regularity is available at the initial state. -/
theorem rieszGradient_contDiffAt_of_contDiffAt_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (potential : E → ℝ) (x₀ : E)
    (hpotential : ContDiffAt ℝ 2 potential x₀) :
    ContDiffAt ℝ 1 (rieszGradient potential) x₀ := by
  have hderiv : ContDiffAt ℝ 1 (fderiv ℝ potential) x₀ :=
    hpotential.fderiv_right (m := 1) (by norm_num)
  let R : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hcomp := hderiv.continuousLinearMap_comp R
  change ContDiffAt ℝ 1 (fun x => R (fderiv ℝ potential x)) x₀
  exact hcomp

/-- For a C² scalar potential and a C¹ state-dependent positive or general
operator field, the associated Riesz-gradient flow has a local solution. The
operator regularity remains an explicit hypothesis. -/
theorem exists_local_riesz_gradient_flow_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E → E →L[ℝ] E) (potential : E → ℝ) (x₀ : E)
    (hA : ContDiffAt ℝ 1 A x₀)
    (hpotential : ContDiffAt ℝ 2 potential x₀) (t₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ trajectory : ℝ → E,
      trajectory t₀ = x₀ ∧
        ∀ s ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt trajectory
            (-(A (trajectory s) (rieszGradient potential (trajectory s)))) s := by
  have hgradient := rieszGradient_contDiffAt_of_contDiffAt_two potential x₀ hpotential
  exact exists_local_gradient_flow_of_contDiffAt A (rieszGradient potential) x₀
    hA hgradient t₀

/-- The identity-mobility case `x' = -∇V(x)`: a C² potential on a complete
real inner product space has a two-sided local gradient-flow trajectory
through every point where that regularity holds. This is a special case of
the paper's dynamics if its mobility is the identity. -/
theorem exists_local_standard_gradient_flow_of_contDiffAt_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (potential : E → ℝ) (x₀ : E)
    (hpotential : ContDiffAt ℝ 2 potential x₀) (t₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ trajectory : ℝ → E,
      trajectory t₀ = x₀ ∧
        ∀ s ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt trajectory (-(rieszGradient potential (trajectory s))) s := by
  let A : E → E →L[ℝ] E := fun _ => ContinuousLinearMap.id ℝ E
  have hA : ContDiffAt ℝ 1 A x₀ := contDiffAt_const
  obtain ⟨ε, hε, trajectory, hinit, hflow⟩ :=
    exists_local_riesz_gradient_flow_of_contDiffAt A potential x₀ hA hpotential t₀
  refine ⟨ε, hε, trajectory, hinit, ?_⟩
  intro s hs
  simpa [A] using hflow s hs

/-- The identity-mobility gradient flow of Theorem 21's effective potential
`V - κ p S` has a local solution when both scalar potentials are C² at the
initial point. This is the local-existence part only; it does not establish
that the trajectory remains in the closed ball used by the theorem. -/
theorem exists_local_effective_gradient_flow_of_contDiffAt_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V S : E → ℝ) (κ p : ℝ) (x₀ : E)
    (hV : ContDiffAt ℝ 2 V x₀)
    (hS : ContDiffAt ℝ 2 S x₀) (t₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ trajectory : ℝ → E,
      trajectory t₀ = x₀ ∧
        ∀ s ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt trajectory
            (-(rieszGradient (fun x => V x - κ * p * S x) (trajectory s))) s := by
  have hVeff : ContDiffAt ℝ 2 (fun x => V x - κ * p * S x) x₀ := by
    have h := hV.sub (hS.const_smul (κ * p))
    convert h using 1 <;> simp [smul_eq_mul]
  exact exists_local_standard_gradient_flow_of_contDiffAt_two
    (fun x => V x - κ * p * S x) x₀ hVeff t₀

/-- If a trajectory solves an ODE on an open time interval and the vector field
is continuous, then the trajectory is C¹ there. This upgrades the local
Picard–Lindelöf output to the regularity needed by the absolute-continuity
lemma on compact subintervals. -/
theorem trajectory_contDiffOn_of_ode_of_continuous_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (trajectory : ℝ → E) (I : Set ℝ)
    (hI : IsOpen I)
    (hf : ∀ t ∈ I, ContinuousAt f (trajectory t))
    (hflow : ∀ t ∈ I, HasDerivAt trajectory (f (trajectory t)) t) :
    ContDiffOn ℝ 1 trajectory I := by
  rw [show (1 : ℕ∞ω) = 0 + 1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen hI]
  simp
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (hflow t ht).differentiableAt.differentiableWithinAt
  · have htrajectory_cont : ContinuousOn trajectory I := by
      intro t ht
      exact (hflow t ht).continuousAt.continuousWithinAt
    have hfield_cont : ContinuousOn (fun t => f (trajectory t)) I := by
      intro t ht
      have hcomp := ContinuousAt.comp (hf t ht) (hflow t ht).continuousAt
      exact hcomp.continuousWithinAt
    exact hfield_cont.congr fun t ht => (hflow t ht).deriv

/-- On any compact time segment contained in an open interval of ODE validity,
continuity of the vector field makes the trajectory C¹; composing with a C¹
potential therefore supplies the absolute continuity hypothesis for the
exponential estimate. -/
theorem potential_gap_absolutelyContinuous_of_ode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (trajectory : ℝ → E) (f : E → E) (potential : E → ℝ) (U : Set E)
    (xstar : E) (I : Set ℝ) (t₀ t : ℝ)
    (hI : IsOpen I)
    (hf : ∀ s ∈ I, ContinuousAt f (trajectory s))
    (hpotential : ContDiffOn ℝ 1 potential U)
    (hflow : ∀ s ∈ I, HasDerivAt trajectory (f (trajectory s)) s)
    (htime : Set.uIcc t₀ t ⊆ I)
    (hmem : Set.MapsTo trajectory (Set.uIcc t₀ t) U) :
    AbsolutelyContinuousOnInterval
      (fun s => potential (trajectory s) - potential xstar) t₀ t := by
  have htrajI : ContDiffOn ℝ 1 trajectory I :=
    trajectory_contDiffOn_of_ode_of_continuous_field f trajectory I hI hf hflow
  have htraj : ContDiffOn ℝ 1 trajectory (Set.uIcc t₀ t) := htrajI.mono htime
  have hcomp : ContDiffOn ℝ 1 (potential ∘ trajectory) (Set.uIcc t₀ t) :=
    hpotential.comp htraj hmem
  have hcomp_ac := hcomp.absolutelyContinuousOnInterval
  have hconst : ContDiffOn ℝ 1 (fun _ : ℝ => potential xstar) (Set.uIcc t₀ t) :=
    contDiffOn_const
  have hconst_ac := hconst.absolutelyContinuousOnInterval
  have hsub := hcomp_ac.sub hconst_ac
  change AbsolutelyContinuousOnInterval
    ((potential ∘ trajectory) - (fun _ : ℝ => potential xstar)) t₀ t at hsub
  convert hsub using 1 <;> funext s <;> rfl

/-- A trajectory satisfying the stated closed-loop equation, remaining in the
strongly convex region, and having an absolutely continuous potential gap
converges exponentially in both potential gap and distance. ODE existence,
forward invariance, and absolute continuity are explicit hypotheses. -/
theorem gradient_flow_exponential_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (A : E → E →L[ℝ] E) (U : Set E) (c gamma t₀ t : ℝ)
    (hc : 0 < c) (hgamma : 0 < gamma) (ht : t₀ ≤ t)
    (htrajectory_mem : ∀ s ∈ Set.Icc t₀ t, trajectory s ∈ U)
    (xstar : E) (hxstar : xstar ∈ U) (hstationary : gradient xstar = 0)
    (hconvex : StronglyConvexOn U potential gradient c)
    (hpotential : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hflow : ∀ s ∈ Set.Icc t₀ t,
      HasDerivAt trajectory (-(A (trajectory s) (gradient (trajectory s)))) s)
    (hcoercive : ∀ x ∈ U, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hgap_ac : AbsolutelyContinuousOnInterval
      (fun s => potential (trajectory s) - potential xstar) t₀ t) :
    0 ≤ potential (trajectory t₀) - potential xstar ∧
      potential (trajectory t) - potential xstar ≤
        (potential (trajectory t₀) - potential xstar) *
          Real.exp (-2 * gamma * c * (t - t₀)) ∧
      ‖trajectory t - xstar‖ ≤
        Real.sqrt (2 * (potential (trajectory t₀) - potential xstar) / c) *
          Real.exp (-gamma * c * (t - t₀)) := by
  have hdiss := gradient_flow_dissipation_of_ode trajectory potential gradient A U
    gamma t₀ t hgamma ht htrajectory_mem hpotential hflow hcoercive
  have hdecay := potential_gap_exponential_decay_of_gradient_dissipation
    trajectory potential gradient U c gamma t₀ t hc hgamma ht htrajectory_mem
    xstar hxstar hstationary hconvex hgap_ac
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
      have hsIcc : s ∈ Set.Icc t₀ t := hs
      have h := hdiss s hsIcc
      have heq : deriv (fun r => potential (trajectory r) - potential xstar) s =
          deriv (fun r => potential (trajectory r)) s := by
        simp
      rw [heq]
      exact h)
  have hgap0 : 0 ≤ potential (trajectory t₀) - potential xstar := hdecay.1
  have hgap_t := hdecay.2
  have hsupport := hconvex xstar hxstar (trajectory t) (htrajectory_mem t ⟨ht, le_rfl⟩)
  rw [hstationary, inner_zero_left, sub_zero] at hsupport
  have hnorm_sq : ‖trajectory t - xstar‖ ^ 2 ≤
      2 * (potential (trajectory t) - potential xstar) / c := by
    apply (le_div_iff₀ hc).2
    nlinarith [hsupport]
  have hnorm_sq' : ‖trajectory t - xstar‖ ^ 2 ≤
      (2 * (potential (trajectory t₀) - potential xstar) / c) *
        (Real.exp (-gamma * c * (t - t₀))) ^ 2 := by
    have hexp : (Real.exp (-gamma * c * (t - t₀))) ^ 2 =
        Real.exp (-2 * gamma * c * (t - t₀)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring
    rw [hexp]
    have hscale : 0 ≤ 2 / c := by positivity
    calc
      ‖trajectory t - xstar‖ ^ 2 ≤ 2 * (potential (trajectory t) - potential xstar) / c := hnorm_sq
      _ = (2 / c) * (potential (trajectory t) - potential xstar) := by ring
      _ ≤ (2 / c) * ((potential (trajectory t₀) - potential xstar) *
          Real.exp (-2 * gamma * c * (t - t₀))) :=
        mul_le_mul_of_nonneg_left hgap_t hscale
      _ = (2 * (potential (trajectory t₀) - potential xstar) / c) *
          Real.exp (-2 * gamma * c * (t - t₀)) := by ring
  have hCnonneg : 0 ≤ Real.sqrt
      (2 * (potential (trajectory t₀) - potential xstar) / c) := by positivity
  have hC2 : (Real.sqrt
      (2 * (potential (trajectory t₀) - potential xstar) / c)) ^ 2 =
      2 * (potential (trajectory t₀) - potential xstar) / c :=
    Real.sq_sqrt (by positivity)
  have hexp_nonneg : 0 ≤ Real.exp (-gamma * c * (t - t₀)) := (Real.exp_pos _).le
  have hdist : ‖trajectory t - xstar‖ ≤
      Real.sqrt (2 * (potential (trajectory t₀) - potential xstar) / c) *
        Real.exp (-gamma * c * (t - t₀)) := by
    let bound := Real.sqrt (2 * (potential (trajectory t₀) - potential xstar) / c) *
      Real.exp (-gamma * c * (t - t₀))
    have hbound_sq : ‖trajectory t - xstar‖ ^ 2 ≤ bound ^ 2 := by
      dsimp [bound]
      nlinarith [hnorm_sq']
    by_contra hnot
    have hgt : bound < ‖trajectory t - xstar‖ := lt_of_not_ge hnot
    have hbound_nonneg : 0 ≤ bound := mul_nonneg hCnonneg hexp_nonneg
    have hdiff : 0 < ‖trajectory t - xstar‖ - bound := by linarith
    have hsum : 0 < ‖trajectory t - xstar‖ + bound := by
      have : 0 ≤ ‖trajectory t - xstar‖ := norm_nonneg _
      linarith
    have hsqgt : bound ^ 2 < ‖trajectory t - xstar‖ ^ 2 := by
      nlinarith [mul_pos hdiff hsum]
    exact (not_lt_of_ge hbound_sq hsqgt)
  exact ⟨hgap0, hgap_t, hdist⟩

/-- Exponential convergence from an ODE valid on an open neighborhood of the
time segment. Unlike `gradient_flow_exponential_decay`, this version derives
absolute continuity of the potential gap from a continuous vector field and a
C¹ potential. Forward invariance of `U` along the segment is still explicit. -/
theorem gradient_flow_exponential_decay_of_open_ode
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (A : E → E →L[ℝ] E) (U I : Set _) (c gamma t₀ t : ℝ)
    (hc : 0 < c) (hgamma : 0 < gamma) (ht : t₀ ≤ t)
    (hI : IsOpen I)
    (hfield : ∀ s ∈ I,
      ContinuousAt (fun x => -(A x (gradient x))) (trajectory s))
    (htime : Set.Icc t₀ t ⊆ I)
    (htrajectory_mem : ∀ s ∈ Set.Icc t₀ t, trajectory s ∈ U)
    (xstar : E) (hxstar : xstar ∈ U) (hstationary : gradient xstar = 0)
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
  let f : E → E := fun x => -(A x (gradient x))
  have htime' : Set.uIcc t₀ t ⊆ I := by
    rw [Set.uIcc_of_le ht]
    exact htime
  have hmem : Set.MapsTo trajectory (Set.uIcc t₀ t) U := by
    intro s hs
    have hs' : s ∈ Set.Icc t₀ t := by
      simpa [Set.uIcc_of_le ht] using hs
    exact htrajectory_mem s hs'
  have hgap_ac := potential_gap_absolutelyContinuous_of_ode
    trajectory f potential U xstar I t₀ t hI
    (by intro s hs; simpa [f] using hfield s hs)
    hpotential_c1 (by simpa [f] using hflow) htime' hmem
  have hflow_segment : ∀ s ∈ Set.Icc t₀ t,
      HasDerivAt trajectory (-(A (trajectory s) (gradient (trajectory s)))) s := by
    intro s hs
    exact hflow s (htime hs)
  exact gradient_flow_exponential_decay trajectory potential gradient A U c gamma t₀ t
    hc hgamma ht htrajectory_mem xstar hxstar hstationary hconvex hpotential
    hflow_segment hcoercive hgap_ac

/-- An ODE trajectory starting in an open region remains in that region for
some positive forward time. The same interval can be chosen inside the open
time domain on which the differential equation is valid. -/
theorem local_trajectory_stays_in_open_region
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (trajectory : ℝ → E) (f : E → E) (I : Set ℝ) (U : Set E)
    (t₀ : ℝ) (x₀ : E)
    (hI : IsOpen I) (hU : IsOpen U) (ht₀ : t₀ ∈ I) (hx₀ : x₀ ∈ U)
    (hinit : trajectory t₀ = x₀)
    (hflow : ∀ s ∈ I, HasDerivAt trajectory (f (trajectory s)) s) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Icc t₀ (t₀ + δ) ⊆ I ∧
      ∀ s ∈ Set.Icc t₀ (t₀ + δ), trajectory s ∈ U := by
  have htraj_cont := (hflow t₀ ht₀).continuousAt
  have htrajectory_eventually : ∀ᶠ s in 𝓝 t₀, trajectory s ∈ U := by
    have hU_nhds : U ∈ 𝓝 x₀ := hU.mem_nhds hx₀
    have hU_nhds' : U ∈ 𝓝 (trajectory t₀) := by simpa [hinit] using hU_nhds
    exact htraj_cont.eventually hU_nhds'
  have htime_eventually : ∀ᶠ s in 𝓝 t₀, s ∈ I := hI.mem_nhds ht₀
  have hnbhd : {s | s ∈ I ∧ trajectory s ∈ U} ∈ 𝓝 t₀ := by
    filter_upwards [htime_eventually, htrajectory_eventually] with s hsI hsU
    exact ⟨hsI, hsU⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnbhd
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro s hs
    have hnonneg : 0 ≤ s - t₀ := sub_nonneg.mpr hs.1
    have hsupper : s ≤ t₀ + ε / 2 := by simpa [δ] using hs.2
    have hle : s - t₀ ≤ δ := by dsimp [δ]; linarith
    have hdist : dist s t₀ < ε := by
      rw [Real.dist_eq, abs_of_nonneg hnonneg]
      dsimp [δ] at hle ⊢
      linarith
    exact (hball (Metric.mem_ball.mpr hdist)).1
  · intro s hs
    have hnonneg : 0 ≤ s - t₀ := sub_nonneg.mpr hs.1
    have hsupper : s ≤ t₀ + ε / 2 := by simpa [δ] using hs.2
    have hle : s - t₀ ≤ δ := by dsimp [δ]; linarith
    have hdist : dist s t₀ < ε := by
      rw [Real.dist_eq, abs_of_nonneg hnonneg]
      dsimp [δ] at hle ⊢
      linarith
    exact (hball (Metric.mem_ball.mpr hdist)).2

/-- A locally defined gradient-flow trajectory starting in the interior of the
strongly convex region satisfies the paper's quantitative exponential bound
for some positive forward duration. This packages local invariance from
continuity with the open-ODE decay theorem; it does not claim global existence. -/
theorem exists_positive_time_gradient_flow_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (A : E → E →L[ℝ] E) (U : Set E) (I : Set ℝ) (c gamma t₀ : ℝ)
    (hc : 0 < c) (hgamma : 0 < gamma)
    (hI : IsOpen I) (hU : IsOpen U)
    (hfield : Continuous (fun x => -(A x (gradient x))))
    (ht₀ : t₀ ∈ I) (x₀ : E) (hx₀ : x₀ ∈ U)
    (hinit : trajectory t₀ = x₀)
    (hflow : ∀ s ∈ I,
      HasDerivAt trajectory (-(A (trajectory s) (gradient (trajectory s)))) s)
    (xstar : E) (hxstar : xstar ∈ U) (hstationary : gradient xstar = 0)
    (hconvex : StronglyConvexOn U potential gradient c)
    (hpotential : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hpotential_c1 : ContDiffOn ℝ 1 potential U)
    (hcoercive : ∀ x ∈ U, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∃ δ : ℝ, 0 < δ ∧
      0 ≤ potential (trajectory t₀) - potential xstar ∧
      potential (trajectory (t₀ + δ)) - potential xstar ≤
        (potential (trajectory t₀) - potential xstar) *
          Real.exp (-2 * gamma * c * δ) ∧
      ‖trajectory (t₀ + δ) - xstar‖ ≤
        Real.sqrt (2 * (potential (trajectory t₀) - potential xstar) / c) *
          Real.exp (-gamma * c * δ) := by
  obtain ⟨δ, hδ, htime, htrajectory_mem⟩ :=
    local_trajectory_stays_in_open_region trajectory
      (fun x => -(A x (gradient x))) I U t₀ x₀ hI hU ht₀ hx₀ hinit
      (by simpa using hflow)
  have hdecay := gradient_flow_exponential_decay_of_open_ode
    trajectory potential gradient A U I c gamma t₀ (t₀ + δ)
    hc hgamma (le_add_of_nonneg_right hδ.le) hI
    (fun s hs => hfield.continuousAt) htime htrajectory_mem
    xstar hxstar hstationary hconvex hpotential hpotential_c1 hflow hcoercive
  have hexp₁ : -2 * gamma * c * ((t₀ + δ) - t₀) = -2 * gamma * c * δ := by ring
  have hexp₂ : -gamma * c * ((t₀ + δ) - t₀) = -gamma * c * δ := by ring
  rcases hdecay with ⟨hgap₀, hgapT, hdist⟩
  rw [hexp₁] at hgapT
  rw [hexp₂] at hdist
  exact ⟨δ, hδ, hgap₀, hgapT, hdist⟩

/-- A globally C² potential with a strongly convex interior minimum admits an
identity-mobility gradient-flow solution that decays exponentially for some
positive time. This is a local special case: it assumes strong convexity on
an open region and does not establish invariance or global existence. -/
theorem exists_short_time_standard_gradient_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (potential : E → ℝ) (U : Set E) (c t₀ : ℝ) (hc : 0 < c)
    (hpotential : ContDiff ℝ 2 potential) (hU : IsOpen U)
    (x₀ xstar : E) (hx₀ : x₀ ∈ U) (hxstar : xstar ∈ U)
    (hstationary : rieszGradient potential xstar = 0)
    (hconvex : StronglyConvexOn U potential (rieszGradient potential) c) :
    ∃ trajectory : ℝ → E, trajectory t₀ = x₀ ∧
      ∃ δ : ℝ, 0 < δ ∧
        0 ≤ potential (trajectory t₀) - potential xstar ∧
        potential (trajectory (t₀ + δ)) - potential xstar ≤
          (potential (trajectory t₀) - potential xstar) *
            Real.exp (-2 * c * δ) ∧
        ‖trajectory (t₀ + δ) - xstar‖ ≤
          Real.sqrt (2 * (potential (trajectory t₀) - potential xstar) / c) *
            Real.exp (-c * δ) := by
  obtain ⟨ε, hε, trajectory, hinit, hflow⟩ :=
    exists_local_standard_gradient_flow_of_contDiffAt_two potential x₀
      (hpotential.contDiffAt) t₀
  let I : Set ℝ := Set.Ioo (t₀ - ε) (t₀ + ε)
  have hI : IsOpen I := isOpen_Ioo
  have ht₀ : t₀ ∈ I := by
    simp only [I, Set.mem_Ioo]
    constructor <;> linarith
  have hgrad_contDiff : ContDiff ℝ 1 (rieszGradient potential) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact rieszGradient_contDiffAt_of_contDiffAt_two potential x
      (hpotential.contDiffAt)
  have hfield : Continuous (fun x => -rieszGradient potential x) :=
    hgrad_contDiff.neg.continuous
  have hpotC1 : ContDiffOn ℝ 1 potential U :=
    (hpotential.of_le (by norm_num)).contDiffOn.mono (Set.subset_univ U)
  have hpotDeriv : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (rieszGradient potential x)) x := by
    intro x _
    have hd := (hpotential.differentiable (by norm_num) x).hasFDerivAt
    apply hd.congr_fderiv
    ext v
    exact fderiv_eq_inner_rieszGradient potential x v
  have hcoercive : ∀ x ∈ U, ∀ v : E,
      1 * ‖v‖ ^ 2 ≤ inner ℝ ((ContinuousLinearMap.id ℝ E) v) v := by
    intro x hx v
    simpa [real_inner_self_eq_norm_sq]
  obtain ⟨δ, hδ, hgap₀, hgapT, hdist⟩ :=
    exists_positive_time_gradient_flow_decay trajectory potential
      (rieszGradient potential) (fun _ => ContinuousLinearMap.id ℝ E)
      U I c 1 t₀ hc zero_lt_one hI hU (by simpa using hfield)
      ht₀ x₀ hx₀ hinit (by simpa [I] using hflow) xstar hxstar
      hstationary hconvex hpotDeriv hpotC1 hcoercive
  exact ⟨trajectory, hinit, δ, hδ, hgap₀, by simpa using hgapT,
    by simpa using hdist⟩

/-- The short-time decay result can be started from an interior minimizer on
a closed ball. The hypotheses explicitly provide strong convexity on the
closed ball; restricting it to the open ball lets local existence and decay
run around the minimizer. -/
theorem exists_short_time_decay_from_interior_ball_minimum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (potential : E → ℝ) (center x₀ : E) (r c t₀ : ℝ)
    (hpotential : ContDiff ℝ 2 potential) (hr : 0 < r) (hc : 0 < c)
    (xstar : E) (hmin : IsMinOn potential (Metric.closedBall center r) xstar)
    (hxstar : xstar ∈ interior (Metric.closedBall center r))
    (hx₀ : x₀ ∈ interior (Metric.closedBall center r))
    (hconvex : StronglyConvexOn (Metric.closedBall center r) potential
      (rieszGradient potential) c) :
    ∃ trajectory : ℝ → E, trajectory t₀ = x₀ ∧
      ∃ δ : ℝ, 0 < δ ∧
        0 ≤ potential (trajectory t₀) - potential xstar ∧
        potential (trajectory (t₀ + δ)) - potential xstar ≤
          (potential (trajectory t₀) - potential xstar) *
            Real.exp (-2 * c * δ) ∧
        ‖trajectory (t₀ + δ) - xstar‖ ≤
          Real.sqrt (2 * (potential (trajectory t₀) - potential xstar) / c) *
            Real.exp (-c * δ) := by
  let U := interior (Metric.closedBall center r)
  have hU : IsOpen U := isOpen_interior
  have hstarU : xstar ∈ U := hxstar
  have hx₀U : x₀ ∈ U := hx₀
  have hlocal : IsLocalMin potential xstar := by
    apply hmin.isLocalMin
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hxstar) interior_subset
  have hderiv : HasFDerivAt potential (innerSL ℝ (rieszGradient potential xstar)) xstar := by
    have hdiff := (hpotential.differentiable (by norm_num) xstar).hasFDerivAt
    apply hdiff.congr_fderiv
    ext v
    exact fderiv_eq_inner_rieszGradient potential xstar v
  have hstationary_map := hlocal.hasFDerivAt_eq_zero hderiv
  have hstationary : rieszGradient potential xstar = 0 := by
    have heval := congrArg (fun D : E →L[ℝ] ℝ => D (rieszGradient potential xstar))
      hstationary_map
    have hinner : inner ℝ (rieszGradient potential xstar)
        (rieszGradient potential xstar) = 0 := by
      simpa [innerSL_apply_apply] using heval
    have hnorm : ‖rieszGradient potential xstar‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hinner
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hconvexU : StronglyConvexOn U potential (rieszGradient potential) c := by
    intro x hx y hy
    exact hconvex x (interior_subset hx) y (interior_subset hy)
  exact exists_short_time_standard_gradient_decay potential U c t₀ hc hpotential
    hU x₀ xstar hx₀U hstarU hstationary hconvexU

/-- A vector field that is continuous on a compact set is bounded there.
This supplies the speed bound used by the Lipschitz estimates below, which
are needed before attempting finite-endpoint continuation of a locally
defined solution. -/
theorem continuous_field_bounded_on_compact
    {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F]
    (field : X → F) (K : Set X) (hK : IsCompact K)
    (hfield : ContinuousOn field K) :
    ∃ C : ℝ, ∀ x ∈ K, ‖field x‖ ≤ C := by
  exact IsCompact.exists_bound_of_continuousOn (α := X) (E := F) hK hfield

/-- In a finite-dimensional normed state space, continuity bounds an
autonomous vector field on each closed ball. -/
theorem continuous_field_bounded_on_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (field : E → E) (center : E) (r : ℝ)
    (hfield : ContinuousOn field (Metric.closedBall center r)) :
    ∃ C : ℝ, ∀ x ∈ Metric.closedBall center r, ‖field x‖ ≤ C := by
  exact continuous_field_bounded_on_compact field (Metric.closedBall center r)
    (isCompact_closedBall center r) hfield

theorem trajectory_lipschitz_of_bounded_ode_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (trajectory : ℝ → E) (field : E → E) (I : Set ℝ) (K : Set E)
    (J : Set ℝ) (C : ℝ≥0)
    (hJconvex : Convex ℝ J) (hJsubset : J ⊆ I)
    (htraj : ∀ t ∈ J, trajectory t ∈ K)
    (hbound : ∀ x ∈ K, ‖field x‖₊ ≤ C)
    (hflow : ∀ t ∈ I, HasDerivAt trajectory (field (trajectory t)) t) :
    LipschitzOnWith C trajectory J := by
  apply hJconvex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
  · intro t ht
    exact (hflow t (hJsubset ht)).hasDerivWithinAt
  · intro t ht
    exact hbound (trajectory t) (htraj t ht)

/-- The squared distance to a fixed center has derivative given by the radial
component of an ODE velocity. This is the scalar barrier quantity needed to
turn an inward boundary condition on a closed ball into a first-exit argument.
-/
theorem hasDerivAt_sq_distance_of_ode
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (center : E) (velocity : E) (t : ℝ)
    (htrajectory : HasDerivAt trajectory velocity t) :
    HasDerivAt (fun s => ‖trajectory s - center‖ ^ 2)
      (2 * inner ℝ (trajectory t - center) velocity) t := by
  have hshift : HasDerivAt (fun s => trajectory s - center) velocity t :=
    htrajectory.sub_const center
  simpa using hshift.norm_sq

/-- A uniform field bound and an ODE on the open interval give a Lipschitz
estimate up to, but excluding, its finite right endpoint. This is the form
needed to prove that a trajectory has an endpoint limit before extending it.
-/
theorem trajectory_lipschitz_before_finite_endpoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (trajectory : ℝ → E) (field : E → E) (a b : ℝ) (K : Set E)
    (C : ℝ≥0) (hab : a < b)
    (htraj : ∀ t ∈ Set.Ico a b, trajectory t ∈ K)
    (hbound : ∀ x ∈ K, ‖field x‖₊ ≤ C)
    (hflow : ∀ t ∈ Set.Ico a b,
      HasDerivAt trajectory (field (trajectory t)) t) :
    LipschitzOnWith C trajectory (Set.Ico a b) := by
  apply trajectory_lipschitz_of_bounded_ode_field trajectory field
    (Set.Ico a b) K (Set.Ico a b) C (convex_Ico a b)
  · intro t ht
    exact ht
  · exact htraj
  · exact hbound
  · exact hflow

/-- In finite-dimensional state spaces, a Lipschitz trajectory on `[a,b)` has
a finite left limit at `b`. Mathlib's finite-dimensional Lipschitz extension
provides an extension to all times; continuity of that extension identifies
the endpoint limit. -/
theorem trajectory_tendsto_finite_endpoint_of_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (trajectory : ℝ → E) (a b : ℝ) (C : ℝ≥0) (hab : a < b)
    (hlip : LipschitzOnWith C trajectory (Set.Ico a b)) :
    ∃ xend : E, Tendsto trajectory (𝓝[<] b) (𝓝 xend) := by
  obtain ⟨extended, hextended, heq⟩ := hlip.extend_finite_dimension
  refine ⟨extended b, ?_⟩
  have hleft : Tendsto extended (𝓝[<] b) (𝓝 (extended b)) :=
    hextended.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ t in 𝓝[<] b, t ∈ Set.Ico a b := by
    have hgt : ∀ᶠ t in 𝓝[<] b, a < t :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hab)
    filter_upwards [hgt, self_mem_nhdsWithin] with t hta htb
    exact ⟨le_of_lt hta, htb⟩
  have heqNear : trajectory =ᶠ[𝓝[<] b] extended :=
    hmem.mono fun t ht => heq ht
  exact hleft.congr' heqNear.symm

/-- Differentiability is preserved when two trajectories are pasted at a
time where their values and one-sided derivatives agree. This is the local
calculus step needed to join an old solution to a Picard–Lindelöf continuation.
-/
theorem hasDerivAt_paste_at_join
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (left right : ℝ → E) (b : ℝ) (v : E)
    (hleft : HasDerivWithinAt left v (Set.Iic b) b)
    (hright : HasDerivWithinAt right v (Set.Ici b) b)
    (hvalue : left b = right b) :
    HasDerivAt (fun t => if t ≤ b then left t else right t) v b := by
  let joined : ℝ → E := fun t => if t ≤ b then left t else right t
  have hleft' : HasDerivWithinAt joined v (Set.Iio b) b := by
    apply hleft.Iio_of_Iic.congr
    · intro t ht
      change t < b at ht
      simp [joined, le_of_lt ht]
    · simp [joined]
  have hright' : HasDerivWithinAt joined v (Set.Ioi b) b := by
    apply hright.Ioi_of_Ici.congr
    · intro t ht
      change b < t at ht
      simp [joined, not_le_of_gt ht]
    · simp [joined, hvalue]
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · simpa [hasDerivWithinAt_iff_tendsto_slope] using hleft'
  · simpa [hasDerivWithinAt_iff_tendsto_slope] using hright'

/-- If an ODE orbit has a finite left limit at a finite endpoint and the vector
field is continuous, its continuous extension has the expected left derivative.
This supplies the endpoint hypothesis needed to paste a Picard--Lindelöf
continuation to the old orbit. -/
theorem trajectory_hasDerivWithinAt_endpoint_of_ode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (trajectory : ℝ → E) (vectorField : E → E) (a b : ℝ) (xend : E)
    (hab : a < b) (hfield : ContinuousAt vectorField xend)
    (hlim : Tendsto trajectory (𝓝[<] b) (𝓝 xend))
    (hode : ∀ t ∈ Set.Ioo a b,
      HasDerivAt trajectory (vectorField (trajectory t)) t) :
    let extended : ℝ → E := fun t => if t < b then trajectory t else xend
    HasDerivWithinAt extended (vectorField xend) (Set.Iic b) b := by
  dsimp
  let extended : ℝ → E := fun t => if t < b then trajectory t else xend
  have hcontinuous : ContinuousWithinAt extended (Set.Ioo a b) b := by
    rw [ContinuousWithinAt]
    have htraj : Tendsto trajectory (𝓝[Set.Ioo a b] b) (𝓝 xend) :=
      hlim.mono_left (nhdsWithin_mono b (fun _ ht => ht.2))
    have heq : extended =ᶠ[𝓝[Set.Ioo a b] b] trajectory := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp [extended, ht.2]
    simpa [extended] using htraj.congr' heq.symm
  have hset : Set.Ioo a b ∈ 𝓝[<] b := by
    have hleft : ∀ᶠ t in 𝓝[<] b, a < t :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hab)
    filter_upwards [hleft, self_mem_nhdsWithin] with t hta htb
    exact ⟨hta, htb⟩
  have hdiff : DifferentiableOn ℝ extended (Set.Ioo a b) := by
    intro t ht
    have hevent : extended =ᶠ[𝓝 t] trajectory := by
      filter_upwards [Iio_mem_nhds ht.2] with u hu
      change u < b at hu
      simp [extended, hu]
    exact ((hode t ht).differentiableAt.congr_of_eventuallyEq hevent).differentiableWithinAt
  have hderiv : Tendsto (fun t => deriv extended t) (𝓝[<] b)
      (𝓝 (vectorField xend)) := by
    have hEq : deriv extended =ᶠ[𝓝[<] b] fun t => vectorField (trajectory t) := by
      filter_upwards [hset] with t ht
      have h := hode t ht
      have hevent : extended =ᶠ[𝓝 t] trajectory := by
        filter_upwards [Iio_mem_nhds ht.2] with u hu
        change u < b at hu
        simp [extended, hu]
      exact (h.congr_of_eventuallyEq hevent).deriv
    exact (hfield.tendsto.comp hlim).congr' hEq.symm
  exact hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hcontinuous hset hderiv

/-- At the left endpoint of a compact interval, a derivative within the compact
interval is also the right derivative. -/
theorem hasDerivWithinAt_Ici_of_Icc_left_endpoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (v : E) (hab : a < b)
    (h : HasDerivWithinAt f v (Set.Icc a b) a) :
    HasDerivWithinAt f v (Set.Ici a) a := by
  apply h.mono_of_mem_nhdsWithin
  have hupper : ∀ᶠ t in 𝓝[Set.Ici a] a, t < b :=
    nhdsWithin_le_nhds (Iio_mem_nhds hab)
  filter_upwards [hupper, self_mem_nhdsWithin] with t htb hta
  exact ⟨hta, le_of_lt htb⟩

/-- Join a finite-left-limit ODE orbit to a local ODE solution starting at that
limit. The result is differentiability of the pasted curve at the join; the
two component curves already satisfy their ODEs on their respective sides. -/
theorem paste_ode_orbit_to_local_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (trajectory continuation : ℝ → E) (vectorField : E → E)
    (a b c : ℝ) (xend : E) (hab : a < b) (hbc : b < c)
    (hfield : ContinuousAt vectorField xend)
    (hlim : Tendsto trajectory (𝓝[<] b) (𝓝 xend))
    (hleft : ∀ t ∈ Set.Ioo a b,
      HasDerivAt trajectory (vectorField (trajectory t)) t)
    (hinit : continuation b = xend)
    (hright : ∀ t ∈ Set.Icc b c,
      HasDerivWithinAt continuation (vectorField (continuation t))
        (Set.Icc b c) t) :
    HasDerivAt (fun t => if t ≤ b then
      (if t < b then trajectory t else xend) else continuation t)
      (vectorField xend) b := by
  have hleft' := trajectory_hasDerivWithinAt_endpoint_of_ode
    trajectory vectorField a b xend hab hfield hlim hleft
  have hright' : HasDerivWithinAt continuation (vectorField xend)
      (Set.Ici b) b := by
    simpa [hinit] using hasDerivWithinAt_Ici_of_Icc_left_endpoint
      continuation b c (vectorField (continuation b)) hbc
      (hright b ⟨le_rfl, le_of_lt hbc⟩)
  have hpaste := hasDerivAt_paste_at_join
    (fun t => if t < b then trajectory t else xend) continuation b
    (vectorField xend) hleft' hright' (by simp [hinit])
  simpa using hpaste

/-- The pasted curve from `paste_ode_orbit_to_local_solution` satisfies the
ODE throughout the combined open interval, including the joining time. -/
theorem pasted_orbit_satisfies_ode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (trajectory continuation : ℝ → E) (vectorField : E → E)
    (a b c : ℝ) (xend : E) (hab : a < b) (hbc : b < c)
    (hfield : ContinuousAt vectorField xend)
    (hlim : Tendsto trajectory (𝓝[<] b) (𝓝 xend))
    (hleft : ∀ t ∈ Set.Ioo a b,
      HasDerivAt trajectory (vectorField (trajectory t)) t)
    (hinit : continuation b = xend)
    (hright : ∀ t ∈ Set.Icc b c,
      HasDerivWithinAt continuation (vectorField (continuation t))
        (Set.Icc b c) t) :
    ∀ t ∈ Set.Ioo a c,
      HasDerivAt (fun s => if s ≤ b then
        (if s < b then trajectory s else xend) else continuation s)
        (vectorField (if t ≤ b then
          (if t < b then trajectory t else xend) else continuation t)) t := by
  intro t ht
  let joined : ℝ → E := fun s => if s ≤ b then
    (if s < b then trajectory s else xend) else continuation s
  by_cases htb : t < b
  · have hode := hleft t ⟨ht.1, htb⟩
    have hevent : joined =ᶠ[𝓝 t] trajectory := by
      filter_upwards [Iio_mem_nhds htb] with s hs
      change s < b at hs
      have hnot : ¬ b < s := not_lt_of_ge (le_of_lt hs)
      simp [joined, hs, hnot]
    have h := hode.congr_of_eventuallyEq hevent
    simpa [joined, htb, le_of_lt htb] using h
  · by_cases hbt : b < t
    · have htbc : t ∈ Set.Icc b c :=
        ⟨le_of_lt hbt, le_of_lt ht.2⟩
      have hderiv := hright t htbc
      have hmem' : Set.Icc b c ∈ 𝓝 t := by
        have hlo : ∀ᶠ s in 𝓝 t, b < s := Ioi_mem_nhds hbt
        have hhi : ∀ᶠ s in 𝓝 t, s < c := Iio_mem_nhds ht.2
        filter_upwards [hlo, hhi] with s hs₁ hs₂
        exact ⟨le_of_lt hs₁, le_of_lt hs₂⟩
      have hmem : Set.Icc b c ∈ 𝓝[Set.univ] t := by simpa using hmem'
      have hderivAt : HasDerivAt continuation
          (vectorField (continuation t)) t := by
        simpa using hderiv.mono_of_mem_nhdsWithin hmem
      have hevent : joined =ᶠ[𝓝 t] continuation := by
        filter_upwards [Ioi_mem_nhds hbt] with s hs
        change b < s at hs
        have hnot : ¬ s ≤ b := not_le_of_gt hs
        simp [joined, hnot, not_lt_of_ge (le_of_lt hs)]
      have h := hderivAt.congr_of_eventuallyEq hevent
      simpa [joined, not_le_of_gt hbt] using h
    · have htbEq : t = b := le_antisymm (le_of_not_gt hbt) (le_of_not_gt htb)
      subst t
      have hjoin := paste_ode_orbit_to_local_solution trajectory continuation
        vectorField a b c xend hab hbc hfield hlim hleft hinit hright
      simpa [joined] using hjoin

/-- Extend a closed-interval solution by one uniform local segment. The old
endpoint itself supplies the restart state, and forward invariance puts the
entire pasted solution back in `C`; no closedness of `C` is needed. -/
theorem extend_forward_invariant_ode_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E) (C : Set E) (trajectory : ℝ → E)
    (a b δ : ℝ) (hab : a < b) (hδ : 0 < δ)
    (hinvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit t₀ = x → x ∈ C →
      (∀ t ∈ Set.Icc t₀ (t₀ + d),
        HasDerivAt orbit (field (orbit t)) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ C)
    (hinit : trajectory a ∈ C)
    (htrajectory : ∀ t ∈ Set.Icc a b, trajectory t ∈ C)
    (hflow : ∀ t ∈ Set.Icc a b,
      HasDerivAt trajectory (field (trajectory t)) t)
    (hfield : ContinuousAt field (trajectory b))
    (huniform : ∀ x ∈ C, ∃ continuation : ℝ → E,
      continuation b = x ∧
      ∀ t ∈ Set.Icc b (b + δ),
        HasDerivAt continuation (field (continuation t)) t) :
    ∃ joined : ℝ → E,
      joined a = trajectory a ∧
      (∀ t ∈ Set.Icc a (b + δ), joined t ∈ C) ∧
      (∀ t ∈ Set.Icc a (b + δ),
        HasDerivAt joined (field (joined t)) t) := by
  let xend : E := trajectory b
  obtain ⟨continuation, hcontinuationInit, hcontinuationFlow⟩ :=
    huniform xend (htrajectory b ⟨hab.le, le_rfl⟩)
  have hbc : b < b + δ := by linarith
  have hlim : Tendsto trajectory (𝓝[<] b) (𝓝 xend) := by
    have hcontIcc : ContinuousWithinAt trajectory (Set.Icc a b) b :=
      (hflow b ⟨hab.le, le_rfl⟩).continuousAt.continuousWithinAt
    have hcontIic : ContinuousWithinAt trajectory (Set.Iic b) b :=
      (continuousWithinAt_Icc_iff_Iic hab).mp hcontIcc
    convert hcontIic.mono_left (nhdsWithin_mono b
      (fun t ht => Set.mem_Iic.mpr (le_of_lt ht))) using 1 <;> rfl
  have hleft : ∀ t ∈ Set.Ioo a b,
      HasDerivAt trajectory (field (trajectory t)) t := by
    intro t ht
    exact hflow t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hright : ∀ t ∈ Set.Icc b (b + δ),
      HasDerivWithinAt continuation (field (continuation t))
        (Set.Icc b (b + δ)) t := by
    intro t ht
    exact (hcontinuationFlow t ht).hasDerivWithinAt
  let joined : ℝ → E := fun t => if t ≤ b then
    (if t < b then trajectory t else xend) else continuation t
  have hjoinedOpen := pasted_orbit_satisfies_ode trajectory continuation field
    a b (b + δ) xend hab hbc
    (by simpa [xend] using hfield)
    (by simpa [xend] using hlim) hleft hcontinuationInit hright
  have hjoinedAtLeft : joined a = trajectory a := by
    simp [joined, hab.le, hab]
  have hjoinedAtRight : joined (b + δ) = continuation (b + δ) := by
    simp [joined, not_le_of_gt hbc]
  have hjoinedFlow : ∀ t ∈ Set.Icc a (b + δ),
      HasDerivAt joined (field (joined t)) t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hleft'
    · have hevent : joined =ᶠ[𝓝 a] trajectory := by
        filter_upwards [Iio_mem_nhds hab] with s hs
        change s < b at hs
        have hle : s ≤ b := le_of_lt hs
        simp [joined, hle, hs]
      have h := (hflow a ⟨le_rfl, hab.le⟩).congr_of_eventuallyEq hevent
      simpa [hjoinedAtLeft] using h
    · by_cases hright' : t = b + δ
      · subst t
        rw [hjoinedAtRight]
        exact (hcontinuationFlow (b + δ) ⟨le_of_lt hbc, le_rfl⟩).congr_of_eventuallyEq
          (by
            filter_upwards [Ioi_mem_nhds hbc] with s hs
            change b < s at hs
            simp [joined, not_le_of_gt hs])
      · have htopen : t ∈ Set.Ioo a (b + δ) :=
          ⟨hleft', lt_of_le_of_ne ht.2 hright'⟩
        simpa only [joined] using hjoinedOpen t htopen
  have hspan : a + (b + δ - a) = b + δ := by ring
  have hjoinedFlow' : ∀ t ∈ Set.Icc a (a + (b + δ - a)),
      HasDerivAt joined (field (joined t)) t := by
    simpa [hspan] using hjoinedFlow
  have hjoinedStay' := hinvariant a (b + δ - a) joined (trajectory a)
    (by linarith) hjoinedAtLeft hinit hjoinedFlow'
  have hjoinedStay : ∀ t ∈ Set.Icc a (b + δ), joined t ∈ C := by
    simpa [hspan] using hjoinedStay'
  refine ⟨joined, hjoinedAtLeft, hjoinedStay, hjoinedFlow⟩

/-- A Lipschitz trajectory on a closed time interval converges to its value at
the right endpoint when approached from the left. This makes the finite
endpoint state available as initial data for a subsequent local ODE segment. -/
theorem trajectory_tendsto_right_endpoint_of_lipschitz
    {E : Type*} [PseudoMetricSpace E]
    (trajectory : ℝ → E) (a b : ℝ) (C : ℝ≥0) (hab : a < b)
    (hlip : LipschitzOnWith C trajectory (Set.Icc a b)) :
    Tendsto trajectory (𝓝[<] b) (𝓝 (trajectory b)) := by
  have hcontIcc : ContinuousWithinAt trajectory (Set.Icc a b) b :=
    hlip.continuousOn.continuousWithinAt (by simp [hab.le])
  have hcontIic : ContinuousWithinAt trajectory (Set.Iic b) b :=
    (continuousWithinAt_Icc_iff_Iic hab).mp hcontIcc
  exact hcontIic.mono_left (nhdsWithin_mono b
    (fun _ ht => Set.mem_Iic.mpr (le_of_lt ht)))

/-- A trajectory that remains in a finite-dimensional closed ball up to a
finite right endpoint has a bounded velocity and therefore a finite endpoint
limit. If the vector field is C¹ at every point of the ball, a local solution
from that limit extends the old trajectory as an ODE solution past the
endpoint. This is the finite-step continuation result needed for a maximal
solution argument. -/
theorem extend_ode_orbit_past_finite_endpoint_of_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (trajectory : ℝ → E) (field : E → E) (center : E)
    (a b r : ℝ) (hab : a < b) (hr : 0 ≤ r)
    (hfield : Continuous field)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r, ContDiffAt ℝ 1 field x)
    (htrajectory : ∀ t ∈ Set.Ico a b,
      trajectory t ∈ Metric.closedBall center r)
    (hflow : ∀ t ∈ Set.Ico a b,
      HasDerivAt trajectory (field (trajectory t)) t) :
    ∃ xend c continuation,
      Tendsto trajectory (𝓝[<] b) (𝓝 xend) ∧
      xend ∈ Metric.closedBall center r ∧ b < c ∧ continuation b = xend ∧
      (∀ t ∈ Set.Ioo a c,
        HasDerivAt continuation (field (continuation t)) t) := by
  obtain ⟨C, hC⟩ := continuous_field_bounded_on_closedBall field center r
    (hfield.continuousOn.mono (fun _ hx => hx))
  have hcenter : center ∈ Metric.closedBall center r := by
    simp [Metric.mem_closedBall, hr]
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (field center)) (hC center hcenter)
  let Cnn : ℝ≥0 := ⟨C, hC0⟩
  have hbound : ∀ x ∈ Metric.closedBall center r, ‖field x‖₊ ≤ Cnn := by
    intro x hx
    exact_mod_cast hC x hx
  have hlip := trajectory_lipschitz_before_finite_endpoint trajectory field a b
    (Metric.closedBall center r) Cnn hab htrajectory hbound hflow
  obtain ⟨xend, hlim⟩ := trajectory_tendsto_finite_endpoint_of_lipschitz
    trajectory a b Cnn hab hlip
  have hnear : ∀ᶠ t in 𝓝[<] b, t ∈ Set.Ico a b := by
    have hleft : ∀ᶠ t in 𝓝[<] b, a < t :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hab)
    filter_upwards [hleft, self_mem_nhdsWithin] with t hta htb
    exact ⟨le_of_lt hta, htb⟩
  have hxend : xend ∈ Metric.closedBall center r :=
    Metric.isClosed_closedBall.mem_of_tendsto hlim
      (hnear.mono fun t ht => htrajectory t ht)
  obtain ⟨ε, hε, continuation, hinit, hlocal⟩ :=
    exists_local_trajectory_of_contDiffAt field xend (hfieldC1 xend hxend) b
  let c : ℝ := b + ε / 2
  have hbc : b < c := by dsimp [c]; linarith
  have hlocalOn : ∀ t ∈ Set.Icc b c,
      t ∈ Set.Ioo (b - ε) (b + ε) := by
    intro t ht
    constructor
    · exact lt_of_lt_of_le (by linarith [hε]) ht.1
    · calc
        t ≤ c := ht.2
        _ = b + ε / 2 := by rfl
        _ < b + ε := by linarith
  have hright : ∀ t ∈ Set.Icc b c,
      HasDerivWithinAt continuation (field (continuation t)) (Set.Icc b c) t := by
    intro t ht
    exact (hlocal t (hlocalOn t ht)).hasDerivWithinAt
  let joined : ℝ → E := fun t => if t ≤ b then
    (if t < b then trajectory t else xend) else continuation t
  have hjoined := pasted_orbit_satisfies_ode trajectory continuation field a b c xend
    hab hbc hfield.continuousAt hlim
    (fun t ht => hflow t ⟨le_of_lt ht.1, ht.2⟩)
    hinit hright
  refine ⟨xend, c, joined, hlim, hxend, hbc, ?_, ?_⟩
  · simp [joined, hinit]
  · intro t ht
    simpa [joined] using hjoined t ht

/-- Uniform continuation on a closed ball extends an orbit by one fixed
positive time, preserving both ball invariance and the ODE derivative at the
original left endpoint. The fixed step is what permits finite iteration. -/
theorem extend_ode_orbit_past_finite_endpoint_of_closedBall_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (trajectory : ℝ → E) (field : E → E) (center : E)
    (a b r δ : ℝ) (hab : a < b) (hr : 0 ≤ r) (hδ : 0 < δ)
    (hfield : Continuous field)
    (huniform : ∀ t₀ : ℝ, ∀ x ∈ Metric.closedBall center r,
      ∃ continuation : ℝ → E,
        continuation t₀ = x ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt continuation (field (continuation t)) t) ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          continuation t ∈ Metric.closedBall center r))
    (htrajectory : ∀ t ∈ Set.Ico a b,
      trajectory t ∈ Metric.closedBall center r)
    (hflow : ∀ t ∈ Set.Ico a b,
      HasDerivAt trajectory (field (trajectory t)) t) :
    ∃ continuation : ℝ → E,
      continuation a = trajectory a ∧
      (∀ t ∈ Set.Ico a (b + δ),
        continuation t ∈ Metric.closedBall center r) ∧
      (∀ t ∈ Set.Ico a (b + δ),
        HasDerivAt continuation (field (continuation t)) t) := by
  obtain ⟨C, hC⟩ := continuous_field_bounded_on_closedBall field center r
    (hfield.continuousOn.mono (fun _ hx => hx))
  have hcenter : center ∈ Metric.closedBall center r := by
    simp [Metric.mem_closedBall, hr]
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (field center)) (hC center hcenter)
  let Cnn : ℝ≥0 := ⟨C, hC0⟩
  have hbound : ∀ x ∈ Metric.closedBall center r, ‖field x‖₊ ≤ Cnn := by
    intro x hx
    exact_mod_cast hC x hx
  have hlip := trajectory_lipschitz_before_finite_endpoint trajectory field a b
    (Metric.closedBall center r) Cnn hab htrajectory hbound hflow
  obtain ⟨xend, hlim⟩ := trajectory_tendsto_finite_endpoint_of_lipschitz
    trajectory a b Cnn hab hlip
  have hnear : ∀ᶠ t in 𝓝[<] b, t ∈ Set.Ico a b := by
    have hleft : ∀ᶠ t in 𝓝[<] b, a < t :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hab)
    filter_upwards [hleft, self_mem_nhdsWithin] with t hta htb
    exact ⟨le_of_lt hta, htb⟩
  have hxend : xend ∈ Metric.closedBall center r :=
    Metric.isClosed_closedBall.mem_of_tendsto hlim
      (hnear.mono fun t ht => htrajectory t ht)
  obtain ⟨localOrbit, hinit, hlocal, hlocalStay⟩ := huniform b xend hxend
  have hbc : b < b + δ := by linarith
  let joined : ℝ → E := fun t => if t ≤ b then
    (if t < b then trajectory t else xend) else localOrbit t
  have hright : ∀ t ∈ Set.Icc b (b + δ),
      HasDerivWithinAt localOrbit (field (localOrbit t)) (Set.Icc b (b + δ)) t := by
    intro t ht
    exact (hlocal t ht).hasDerivWithinAt
  have hjoined := pasted_orbit_satisfies_ode trajectory localOrbit field a b
    (b + δ) xend hab hbc hfield.continuousAt hlim
    (fun t ht => hflow t ⟨le_of_lt ht.1, ht.2⟩)
    hinit hright
  have hjoinedStart : HasDerivAt joined (field (joined a)) a := by
    have hevent : joined =ᶠ[𝓝 a] trajectory := by
      filter_upwards [Iio_mem_nhds hab] with t ht
      change t < b at ht
      have hle : t ≤ b := le_of_lt ht
      simp [joined, ht, hle]
    have hjoinedAt : joined a = trajectory a := by
      simp [joined, hab.le, hab]
    rw [hjoinedAt]
    exact (hflow a ⟨le_rfl, hab⟩).congr_of_eventuallyEq hevent
  have hjoinedInitial : joined a = trajectory a := by
    simp [joined, hab.le, hab]
  refine ⟨joined, hjoinedInitial, ?_, ?_⟩
  · intro t ht
    by_cases htb : t < b
    · have htold : t ∈ Set.Ico a b := ⟨ht.1, htb⟩
      simpa [joined, le_of_lt htb, htb] using htrajectory t htold
    · by_cases hteq : t = b
      · subst t
        simpa [joined] using hxend
      · have hgt : b < t := lt_of_le_of_ne (le_of_not_gt htb) (Ne.symm hteq)
        have hnew : t ∈ Set.Icc b (b + δ) := ⟨le_of_lt hgt, le_of_lt ht.2⟩
        simpa [joined, not_le_of_gt hgt] using hlocalStay t hnew
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hleft
    · simpa [joined] using hjoinedStart
    · have htopen : t ∈ Set.Ioo a (b + δ) := ⟨hleft, ht.2⟩
      exact hjoined t htopen

/-- Endpoint continuation for a compact forward-invariant region contained in
a closed ball. Compactness puts the finite endpoint back in the invariant
region, where the uniform local continuation can restart. The ambient ball is
used only to bound the vector field and obtain an endpoint limit. -/
theorem extend_ode_orbit_past_finite_endpoint_of_compact_invariant_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (trajectory : ℝ → E) (field : E → E) (center : E)
    (K : Set E) (r a b δ : ℝ) (hab : a < b) (hr : 0 ≤ r)
    (hδ : 0 < δ)
    (hfield : ContinuousOn field (Metric.closedBall center r))
    (hfieldAt : ∀ x ∈ Metric.ball center r, ContinuousAt field x)
    (hKcompact : IsCompact K)
    (hKsubset : K ⊆ Metric.closedBall center r)
    (hKsubsetInterior : K ⊆ Metric.ball center r)
    (huniform : ∀ t₀ : ℝ, ∀ x ∈ K,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit (field (localOrbit t)) t) ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ), localOrbit t ∈ K))
    (htrajectory : ∀ t ∈ Set.Ico a b, trajectory t ∈ K)
    (hflow : ∀ t ∈ Set.Ico a b,
      HasDerivAt trajectory (field (trajectory t)) t) :
    ∃ continuation : ℝ → E,
      continuation a = trajectory a ∧
      (∀ t ∈ Set.Ico a (b + δ), continuation t ∈ K) ∧
      (∀ t ∈ Set.Ico a (b + δ),
        HasDerivAt continuation (field (continuation t)) t) := by
  obtain ⟨C, hC⟩ := continuous_field_bounded_on_closedBall field center r hfield
  have hcenter : center ∈ Metric.closedBall center r := by
    simp [Metric.mem_closedBall, hr]
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (field center)) (hC center hcenter)
  let Cnn : ℝ≥0 := ⟨C, hC0⟩
  have hbound : ∀ x ∈ Metric.closedBall center r, ‖field x‖₊ ≤ Cnn := by
    intro x hx
    exact_mod_cast hC x hx
  have htrajectoryBall : ∀ t ∈ Set.Ico a b,
      trajectory t ∈ Metric.closedBall center r := fun t ht => hKsubset (htrajectory t ht)
  have hlip := trajectory_lipschitz_before_finite_endpoint trajectory field a b
    (Metric.closedBall center r) Cnn hab htrajectoryBall hbound hflow
  obtain ⟨xend, hlim⟩ := trajectory_tendsto_finite_endpoint_of_lipschitz
    trajectory a b Cnn hab hlip
  have hnear : ∀ᶠ t in 𝓝[<] b, t ∈ Set.Ico a b := by
    have hleft : ∀ᶠ t in 𝓝[<] b, a < t :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hab)
    filter_upwards [hleft, self_mem_nhdsWithin] with t hta htb
    exact ⟨le_of_lt hta, htb⟩
  have hxend : xend ∈ K := hKcompact.isClosed.mem_of_tendsto hlim
    (hnear.mono fun t ht => htrajectory t ht)
  obtain ⟨localOrbit, hinit, hlocal, hlocalStay⟩ := huniform b xend hxend
  have hbc : b < b + δ := by linarith
  let joined : ℝ → E := fun t => if t ≤ b then
    (if t < b then trajectory t else xend) else localOrbit t
  have hright : ∀ t ∈ Set.Icc b (b + δ),
      HasDerivWithinAt localOrbit (field (localOrbit t)) (Set.Icc b (b + δ)) t := by
    intro t ht
    exact (hlocal t ht).hasDerivWithinAt
  have hjoined := pasted_orbit_satisfies_ode trajectory localOrbit field a b
    (b + δ) xend hab hbc (hfieldAt xend (hKsubsetInterior hxend)) hlim
    (fun t ht => hflow t ⟨le_of_lt ht.1, ht.2⟩) hinit hright
  have hjoinedStart : HasDerivAt joined (field (joined a)) a := by
    have hevent : joined =ᶠ[𝓝 a] trajectory := by
      filter_upwards [Iio_mem_nhds hab] with t ht
      change t < b at ht
      have hle : t ≤ b := le_of_lt ht
      simp [joined, ht, hle]
    have hjoinedAt : joined a = trajectory a := by simp [joined, hab.le, hab]
    rw [hjoinedAt]
    exact (hflow a ⟨le_rfl, hab⟩).congr_of_eventuallyEq hevent
  have hjoinedInitial : joined a = trajectory a := by simp [joined, hab.le, hab]
  refine ⟨joined, hjoinedInitial, ?_, ?_⟩
  · intro t ht
    by_cases htb : t < b
    · simpa [joined, le_of_lt htb, htb] using htrajectory t ⟨ht.1, htb⟩
    · by_cases hteq : t = b
      · subst t
        simpa [joined] using hxend
      · have hgt : b < t := lt_of_le_of_ne (le_of_not_gt htb) (Ne.symm hteq)
        have hnew : t ∈ Set.Icc b (b + δ) := ⟨le_of_lt hgt, le_of_lt ht.2⟩
        simpa [joined, not_le_of_gt hgt] using hlocalStay t hnew
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hleft
    · simpa [joined] using hjoinedStart
    · have htopen : t ∈ Set.Ioo a (b + δ) := ⟨hleft, ht.2⟩
      exact hjoined t htopen

/-- A compact forward-invariant set with a uniform local solution segment
supports solutions on every finite horizon. This generic construction is
independent of the gradient-flow structure; the field is only required to be
continuous so bounded trajectories have endpoint limits. -/
theorem exists_compact_invariant_trajectory_on_every_finite_horizon
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (field : E → E) (K : Set E) (center : E) (r δ a : ℝ)
    (hr : 0 ≤ r) (hδ : 0 < δ)
    (hfield : ContinuousOn field (Metric.closedBall center r))
    (hfieldAt : ∀ x ∈ Metric.ball center r, ContinuousAt field x)
    (hKcompact : IsCompact K)
    (hKsubset : K ⊆ Metric.closedBall center r)
    (hKsubsetInterior : K ⊆ Metric.ball center r)
    (huniform : ∀ t₀ : ℝ, ∀ x ∈ K,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit (field (localOrbit t)) t) ∧
        (∀ t ∈ Set.Icc t₀ (t₀ + δ), localOrbit t ∈ K))
    (x₀ : E) (hx₀ : x₀ ∈ K) :
    ∀ n : ℕ, ∃ trajectory : ℝ → E,
      trajectory a = x₀ ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ), trajectory t ∈ K) ∧
      (∀ t ∈ Set.Ico a (a + ((n + 1 : ℕ) : ℝ) * δ),
        HasDerivAt trajectory (field (trajectory t)) t) := by
  let endpoint : ℕ → ℝ := fun n => a + ((n + 1 : ℕ) : ℝ) * δ
  obtain ⟨initial, hinitial, hinitialFlow, hinitialStay⟩ := huniform a x₀ hx₀
  have hiterate : ∀ n : ℕ, ∃ trajectory : ℝ → E,
      trajectory a = x₀ ∧
      (∀ t ∈ Set.Ico a (endpoint n), trajectory t ∈ K) ∧
      (∀ t ∈ Set.Ico a (endpoint n),
        HasDerivAt trajectory (field (trajectory t)) t) := by
    intro n
    induction n with
    | zero =>
        have hendpoint : endpoint 0 = a + δ := by simp [endpoint]
        refine ⟨initial, hinitial, ?_, ?_⟩
        · intro t ht
          rw [hendpoint] at ht
          exact hinitialStay t ⟨ht.1, le_of_lt ht.2⟩
        · intro t ht
          rw [hendpoint] at ht
          exact hinitialFlow t ⟨ht.1, le_of_lt ht.2⟩
    | succ n ih =>
        obtain ⟨old, holdInit, holdStay, holdFlow⟩ := ih
        have hstepPositive : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
        have hab : a < endpoint n := by
          dsimp [endpoint]
          nlinarith [mul_pos hstepPositive hδ]
        obtain ⟨next, hnextInit, hnextStay, hnextFlow⟩ :=
          extend_ode_orbit_past_finite_endpoint_of_compact_invariant_uniform
            old field center K r a (endpoint n) δ hab hr
            hδ hfield hfieldAt hKcompact hKsubset hKsubsetInterior
            huniform holdStay holdFlow
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
          exact hnextFlow t ht'
  intro n
  simpa [endpoint] using hiterate n

/-- Finite-horizon solutions from forward invariance alone. A uniform local
solution is only required at points of the invariant set; invariance of each
pasted closed segment supplies the next restart point. In particular, this
construction does not require the invariant set itself to be closed. -/
theorem exists_forward_invariant_trajectory_on_every_finite_horizon
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E) (C : Set E) (δ a : ℝ) (hδ : 0 < δ)
    (hfield : ∀ x ∈ C, ContinuousAt field x)
    (hinvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit t₀ = x → x ∈ C →
      (∀ t ∈ Set.Icc t₀ (t₀ + d),
        HasDerivAt orbit (field (orbit t)) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ C)
    (huniform : ∀ t₀ : ℝ, ∀ x ∈ C,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        ∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit (field (localOrbit t)) t)
    (x₀ : E) (hx₀ : x₀ ∈ C) :
    ∀ n : ℕ, ∃ trajectory : ℝ → E,
      trajectory a = x₀ ∧
      (∀ t ∈ Set.Icc a (a + ((n + 1 : ℕ) : ℝ) * δ), trajectory t ∈ C) ∧
      (∀ t ∈ Set.Icc a (a + ((n + 1 : ℕ) : ℝ) * δ),
        HasDerivAt trajectory (field (trajectory t)) t) := by
  let endpoint : ℕ → ℝ := fun n => a + ((n + 1 : ℕ) : ℝ) * δ
  have hiterate : ∀ n : ℕ, ∃ trajectory : ℝ → E,
      trajectory a = x₀ ∧
      (∀ t ∈ Set.Icc a (endpoint n), trajectory t ∈ C) ∧
      (∀ t ∈ Set.Icc a (endpoint n),
        HasDerivAt trajectory (field (trajectory t)) t) := by
    intro n
    induction n with
    | zero =>
        obtain ⟨initial, hinit, hflow⟩ := huniform a x₀ hx₀
        have hendpoint : endpoint 0 = a + δ := by simp [endpoint]
        refine ⟨initial, hinit, ?_, ?_⟩
        · intro t ht
          rw [hendpoint] at ht
          exact hinvariant a δ initial x₀ hδ.le hinit hx₀ hflow t ht
        · intro t ht
          rw [hendpoint] at ht
          exact hflow t ht
    | succ n ih =>
        obtain ⟨old, holdInit, holdStay, holdFlow⟩ := ih
        have hab : a < endpoint n := by
          dsimp [endpoint]
          have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
          nlinarith [mul_pos hn hδ]
        have hδstep : 0 < δ := hδ
        have hfieldEnd : ContinuousAt field (old (endpoint n)) :=
          hfield _ (holdStay (endpoint n) ⟨le_of_lt hab, le_rfl⟩)
        obtain ⟨next, hnextInit, hnextStay, hnextFlow⟩ :=
          extend_forward_invariant_ode_segment field C old a (endpoint n) δ
            hab hδstep hinvariant
            (holdStay a ⟨le_rfl, le_of_lt hab⟩)
            holdStay holdFlow hfieldEnd
            (fun x hx => huniform (endpoint n) x hx)
        have hnextEndpoint : endpoint (n + 1) = endpoint n + δ := by
          dsimp [endpoint]
          push_cast
          ring
        refine ⟨next, ?_, ?_, ?_⟩
        · rw [hnextInit, holdInit]
        · intro t ht
          have ht' : t ∈ Set.Icc a (endpoint n + δ) := by
            simpa [hnextEndpoint] using ht
          exact hnextStay t ht'
        · intro t ht
          have ht' : t ∈ Set.Icc a (endpoint n + δ) := by
            simpa [hnextEndpoint] using ht
          exact hnextFlow t ht'
  intro n
  simpa [endpoint] using hiterate n


end Tomabechi.Theorem21
