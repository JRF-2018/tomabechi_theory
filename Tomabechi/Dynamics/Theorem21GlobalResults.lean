import Tomabechi.Information.DeterministicOutput
import Tomabechi.Dynamics.GlobalFlow
import Tomabechi.Dynamics.MeanFieldReconstruction
import Tomabechi.Analysis.StrongConvexity
import Tomabechi.Dynamics.GradientFlow

/-! 定理21の定量力学・情報結合結果。-/

namespace Tomabechi.Theorem21

open RealInnerProductSpace
open Filter
open scoped Topology NNReal ContDiff

/-- Package the paper's Hessian bounds, inward-gradient threshold, unique
interior minimum, global identity-mobility orbit, and quantitative exponential
decay into one theorem. The flow conclusion is for the identity-mobility
specialization and assumes C¹ regularity of the effective vector field on the
closed ball (plus its global continuity for endpoint pasting). -/
theorem theorem21_identity_mobility_global_exponential_case
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V S : E → ℝ) (gradV gradS : E → E)
    (HV HS : E → E →L[ℝ] E)
    (hVcontDiff : ContDiffOn ℝ 1 V (Metric.closedBall center r))
    (hScontDiff : ContDiffOn ℝ 1 S (Metric.closedBall center r))
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
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (hfield : Continuous (fun x => -(gradV x - (κ * p) • gradS x)))
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(gradV y - (κ * p) • gradS y)) x)
    (a : ℝ) (x₀ : E) (hx₀ : x₀ ∈ Metric.closedBall center r) :
    ∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * S x) (Metric.closedBall center r) xstar ∧
      ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
        (∀ t ∈ Set.Ici a, trajectory t ∈ Metric.closedBall center r) ∧
        (∀ t ∈ Set.Ici a,
          0 ≤ (V (trajectory a) - κ * p * S (trajectory a)) -
              (V xstar - κ * p * S xstar) ∧
          (V (trajectory t) - κ * p * S (trajectory t)) -
              (V xstar - κ * p * S xstar) ≤
            ((V (trajectory a) - κ * p * S (trajectory a)) -
              (V xstar - κ * p * S xstar)) * Real.exp
                (-2 * (κ * p * m - β) * (t - a)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((V (trajectory a) - κ * p * S (trajectory a)) -
              (V xstar - κ * p * S xstar)) / (κ * p * m - β)) * Real.exp
                (-(κ * p * m - β) * (t - a))) := by
  have hVcont : ContinuousOn V (Metric.closedBall center r) := hVcontDiff.continuousOn
  have hScont : ContinuousOn S (Metric.closedBall center r) := hScontDiff.continuousOn
  obtain ⟨xstar, hxinterior, hmin, _hunique, _hdisplacement⟩ :=
    exists_unique_interior_minimum_of_threshold center r κ p m β B hr hκ hm hβ hB hp
      V S gradV gradS HV HS hVcont hScont hV hS hHV hHS hVlower hSlower hcenter hVbound
  have hxstar : xstar ∈ Metric.closedBall center r := interior_subset hxinterior
  have hκm : 0 < κ * m := mul_pos hκ hm
  have hmax : 0 ≤ max β (B / r) := le_trans hβ (le_max_left _ _)
  have hpPos : 0 < p := lt_of_le_of_lt (div_nonneg hmax (le_of_lt hκm)) hp
  have hκp : 0 ≤ κ * p := mul_nonneg hκ.le hpPos.le
  have hc : 0 < κ * p * m - β :=
    (critical_gain_estimates κ m r β B p hκ hm hr hp).1
  let Veff : E → ℝ := fun x => V x - κ * p * S x
  let geff : E → E := fun x => gradV x - (κ * p) • gradS x
  have hconvex : StronglyConvexOn (Metric.closedBall center r) Veff geff
      (κ * p * m - β) := by
    exact effective_potential_strongly_convex (Metric.closedBall center r)
      V S gradV gradS HV HS κ p m β (convex_closedBall center r)
      hV hS hHV hHS hVlower hSlower hκp
  have hpotential : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt Veff (innerSL ℝ (geff x)) x := by
    intro x hx
    have h := (hV x hx).sub ((hS x hx).const_mul (κ * p))
    convert h using 1 <;>
      simp [Veff, geff, innerSL_apply_apply, inner_smul_left]
  have hpotentialC1 : ContDiffOn ℝ 1 Veff (Metric.closedBall center r) := by
    simpa [Veff, smul_eq_mul] using
      hVcontDiff.sub (ContDiffOn.const_smul (κ * p) hScontDiff)
  have hlocal : IsLocalMin Veff xstar := by
    apply hmin.isLocalMin
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hxinterior) interior_subset
  have hstationaryMap := hlocal.hasFDerivAt_eq_zero (hpotential xstar hxstar)
  have hstationary : geff xstar = 0 := by
    have heval := congrArg (fun D : E →L[ℝ] ℝ => D (geff xstar)) hstationaryMap
    have hinner : inner ℝ (geff xstar) (geff xstar) = 0 := by
      simpa [innerSL_apply_apply] using heval
    have hnorm : ‖geff xstar‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hinner
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  obtain ⟨trajectory, ε, hε, hinit, hball, hdecay⟩ :=
    exists_global_exponentially_decaying_effective_gradient_flow center r κ p m β B
      (κ * p * m - β) hr hκ hm hc hB hp V S gradV gradS HS hcenter hHS hSlower hVbound
      hfield hfieldC1 hpotential hpotentialC1 hconvex xstar hxstar
      (by simpa [geff] using hstationary) a x₀ hx₀
  refine ⟨xstar, hxinterior, hmin, trajectory, ε, hε, hinit, hball, ?_⟩
  intro t ht
  simpa [Veff, mul_assoc, mul_left_comm, mul_comm] using hdecay t ht

/-- The full Lyapunov part of Theorem 21 with a state-dependent mobility.
The threshold assumptions construct the unique interior minimizer and the
strong-convexity constant; a compact forward-invariant effective-potential
sublevel and a `C¹` mobility field then give global existence and quantitative
decay. -/
theorem theorem21_state_dependent_mobility_from_threshold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (center : E) (r κ p m β B gamma a : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V S : E → ℝ) (gradV gradS : E → E)
    (HV HS : E → E →L[ℝ] E)
    (hVcontDiff : ContDiffOn ℝ 1 V (Metric.closedBall center r))
    (hScontDiff : ContDiffOn ℝ 1 S (Metric.closedBall center r))
    (hV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt S (innerSL ℝ (gradS x)) x)
    (hHV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradV (HV x) x)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hgradV_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 gradV x)
    (hgradS_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 gradS x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (HV x v) v)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hcenter : gradS center = 0)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (A : E → E →L[ℝ] E)
    (hA_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 A x)
    (gamma_pos : 0 < gamma)
    (hcoercive : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (C : Set E) (level : ℝ)
    (hCinterior : C ⊆ Metric.ball center r)
    (hCsublevel : C = {x | x ∈ Metric.closedBall center r ∧
      V x - κ * p * S x ≤ level})
    (x₀ : E)
    (hx₀ : x₀ ∈ C) :
    ∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * S x)
        (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * S y = V xstar - κ * p * S xstar → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) ∧
      ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
        (∀ t ∈ Set.Ici a, trajectory t ∈ C) ∧
        (∀ t ∈ Set.Ici a,
          0 ≤ (V (trajectory a) - κ * p * S (trajectory a)) -
              (V xstar - κ * p * S xstar) ∧
          (V (trajectory t) - κ * p * S (trajectory t)) -
              (V xstar - κ * p * S xstar) ≤
            ((V (trajectory a) - κ * p * S (trajectory a)) -
              (V xstar - κ * p * S xstar)) *
                Real.exp (-2 * gamma * (κ * p * m - β) * (t - a)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((V (trajectory a) - κ * p * S (trajectory a)) -
              (V xstar - κ * p * S xstar)) / (κ * p * m - β)) *
                Real.exp (-gamma * (κ * p * m - β) * (t - a))) := by
  have hVcont : ContinuousOn V (Metric.closedBall center r) :=
    hVcontDiff.continuousOn
  have hScont : ContinuousOn S (Metric.closedBall center r) :=
    hScontDiff.continuousOn
  obtain ⟨xstar, hxinterior, hmin, hunique, hdisplacement⟩ :=
    exists_unique_interior_minimum_of_threshold center r κ p m β B hr hκ hm
      hβ hB hp V S gradV gradS HV HS hVcont hScont hV hS hHV hHS
      hVlower hSlower hcenter hVbound
  have hxstarBall : xstar ∈ Metric.closedBall center r :=
    interior_subset hxinterior
  have hκm : 0 < κ * m := mul_pos hκ hm
  have hmax : 0 ≤ max β (B / r) := le_trans hβ (le_max_left _ _)
  have hpPos : 0 < p := lt_of_le_of_lt (div_nonneg hmax (le_of_lt hκm)) hp
  have hκp : 0 ≤ κ * p := mul_nonneg hκ.le hpPos.le
  have hc : 0 < κ * p * m - β :=
    (critical_gain_estimates κ m r β B p hκ hm hr hp).1
  let Veff : E → ℝ := fun x => V x - κ * p * S x
  let geff : E → E := fun x => gradV x - (κ * p) • gradS x
  have hconvex : StronglyConvexOn (Metric.closedBall center r) Veff geff
      (κ * p * m - β) :=
    effective_potential_strongly_convex (Metric.closedBall center r)
      V S gradV gradS HV HS κ p m β (convex_closedBall center r)
      hV hS hHV hHS hVlower hSlower hκp
  have hpotential : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt Veff (innerSL ℝ (geff x)) x := by
    intro x hx
    have h := (hV x hx).sub ((hS x hx).const_mul (κ * p))
    convert h using 1 <;> simp [Veff, geff, innerSL_apply_apply, inner_smul_left]
  have hpotentialC1 : ContDiffOn ℝ 1 Veff (Metric.closedBall center r) := by
    simpa [Veff, smul_eq_mul] using
      hVcontDiff.sub (ContDiffOn.const_smul (κ * p) hScontDiff)
  have hlocal : IsLocalMin Veff xstar := by
    apply hmin.isLocalMin
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hxinterior)
      interior_subset
  have hstationaryMap := hlocal.hasFDerivAt_eq_zero
    (hpotential xstar hxstarBall)
  have hstationary : geff xstar = 0 := by
    have heval := congrArg (fun D : E →L[ℝ] ℝ => D (geff xstar))
      hstationaryMap
    have hinner : inner ℝ (geff xstar) (geff xstar) = 0 := by
      simpa [innerSL_apply_apply] using heval
    have hnorm : ‖geff xstar‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hinner
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hx₀spec : x₀ ∈ Metric.closedBall center r ∧ Veff x₀ ≤ level := by
    rw [hCsublevel] at hx₀
    simpa [Veff] using hx₀
  have hx₀sublevel : Veff x₀ ≤ level := hx₀spec.2
  have hx₀ball : x₀ ∈ Metric.closedBall center r := by
    exact hx₀spec.1
  have hxstarLevel : Veff xstar ≤ level := le_trans
    (hmin hx₀ball) hx₀sublevel
  have hxstarC : xstar ∈ C := by
    rw [hCsublevel]
    exact ⟨hxstarBall, hxstarLevel⟩
  have hgeffC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 geff x := by
    intro x hx
    exact (hgradV_C1 x hx).sub
      ((hgradS_C1 x hx).const_smul (κ * p))
  have hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (geff y))) x := by
    intro x hx
    exact ((hA_C1 x hx).clm_apply (hgeffC1 x hx)).neg
  have hCsublevel' : C =
      {x | x ∈ Metric.closedBall center r ∧ Veff x ≤ level} := by
    simpa [Veff] using hCsublevel
  have hCclosed : IsClosed C := by
    rw [hCsublevel']
    have hlevelClosed : IsClosed (Set.Iic level) := isClosed_Iic
    have hclosed := hpotentialC1.continuousOn.preimage_isClosed_of_isClosed
      (t := Set.Iic level) Metric.isClosed_closedBall hlevelClosed
    convert hclosed using 1 <;> ext x <;> simp
  have hCball : C ⊆ Metric.closedBall center r := by
    intro x hx
    rw [hCsublevel'] at hx
    exact hx.1
  have hcoercive' : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v := hcoercive
  have hinvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit t₀ = x → x ∈ C →
      (∀ t ∈ Set.Icc t₀ (t₀ + d),
        HasDerivAt orbit
          (-(A (orbit t) (gradV (orbit t) - (κ * p) • gradS (orbit t)))) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ C := by
    intro t₀ d orbit x hd hinit hx hflow
    exact forward_invariant_sublevel_of_strict_interior_barrier orbit Veff geff A
      center r gamma t₀ (t₀ + d) level gamma_pos (le_add_of_nonneg_right hd)
      C hCsublevel' hCinterior x hx hinit hpotential hflow hcoercive'
  obtain ⟨trajectory, ε, hε, hinit, _htrajectoryFlow, htrajectoryC,
      hdecay, _hODEunique⟩ :=
    theorem21_state_dependent_mobility_global_existence_and_decay center r a
      (κ * p * m - β) gamma hr.le hc gamma_pos Veff geff A
      (Metric.closedBall center r) C xstar x₀ hfieldC1
      (by simpa [hCclosed.closure_eq] using hCinterior)
      hinvariant hCball hxstarC hx₀
      (by simpa [geff] using hstationary) hconvex hpotential hpotentialC1
      hcoercive'
  refine ⟨xstar, hxinterior, hmin, hunique, hdisplacement,
    trajectory, ε, hε, hinit, htrajectoryC, ?_⟩
  intro t ht
  simpa [Veff, mul_assoc, mul_left_comm, mul_comm] using hdecay t ht

/-- The same threshold conclusion with an arbitrary forward-invariant partial
region whose closure lies inside the local ball. The region need only contain
the threshold minimizer and initial state; it need not equal a full potential
sublevel set. Its invariance is an explicit dynamical hypothesis, matching
the local-region formulation used in Theorem 21. -/
theorem theorem21_state_dependent_mobility_from_threshold_on_invariant_region
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (center : E) (r κ p m β B gamma a : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V S : E → ℝ) (gradV gradS : E → E)
    (HV HS : E → E →L[ℝ] E)
    (hVcontDiff : ContDiffOn ℝ 1 V (Metric.closedBall center r))
    (hScontDiff : ContDiffOn ℝ 1 S (Metric.closedBall center r))
    (hV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt S (innerSL ℝ (gradS x)) x)
    (hHV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradV (HV x) x)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hgradV_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 gradV x)
    (hgradS_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 gradS x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (HV x v) v)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hcenter : gradS center = 0)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (A : E → E →L[ℝ] E)
    (hA_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 A x)
    (gamma_pos : 0 < gamma)
    (hcoercive : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (C : Set E)
    (hCclosureInterior : closure C ⊆ Metric.ball center r)
    (δ : ℝ) (hδ : 0 < δ)
    (hlocalInput : ∀ t₀ : ℝ, ∀ x ∈ C,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        ∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit
            (-(A (localOrbit t) (gradV (localOrbit t) - (κ * p) • gradS (localOrbit t)))) t)
    (L : ℝ≥0)
    (hL : LipschitzOnWith L
      (fun y => -(A y (gradV y - (κ * p) • gradS y)))
      (Metric.closedBall center r))
    (hforwardInvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit t₀ = x → x ∈ C →
      (∀ t ∈ Set.Icc t₀ (t₀ + d),
        HasDerivAt orbit (-(A (orbit t)
          (gradV (orbit t) - (κ * p) • gradS (orbit t)))) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ C)
    (hminimizerInC : ∀ x, x ∈ Metric.closedBall center r →
      IsMinOn (fun y => V y - κ * p * S y)
        (Metric.closedBall center r) x → x ∈ C)
    (x₀ : E) (hx₀ : x₀ ∈ C) :
    ∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * S x)
        (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * S y = V xstar - κ * p * S xstar → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) ∧
      ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
        (∀ t ∈ Set.Ici a, trajectory t ∈ C) ∧
        (∀ t ∈ Set.Ici a,
          0 ≤ (V (trajectory a) - κ * p * S (trajectory a)) -
              (V xstar - κ * p * S xstar) ∧
          (V (trajectory t) - κ * p * S (trajectory t)) -
              (V xstar - κ * p * S xstar) ≤
            ((V (trajectory a) - κ * p * S (trajectory a)) -
              (V xstar - κ * p * S xstar)) *
                Real.exp (-2 * gamma * (κ * p * m - β) * (t - a)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((V (trajectory a) - κ * p * S (trajectory a)) -
              (V xstar - κ * p * S xstar)) / (κ * p * m - β)) *
                Real.exp (-gamma * (κ * p * m - β) * (t - a))) ∧
        (∀ other : ℝ → E, other a = x₀ →
          (∀ t ∈ Set.Ici a, other t ∈ C) →
          (∀ t ∈ Set.Ioi (a - ε), HasDerivAt other
            (-(A (other t) (gradV (other t) - (κ * p) • gradS (other t)))) t) →
          ∀ t ∈ Set.Ici a, other t = trajectory t) := by
  have hVcont : ContinuousOn V (Metric.closedBall center r) :=
    hVcontDiff.continuousOn
  have hScont : ContinuousOn S (Metric.closedBall center r) :=
    hScontDiff.continuousOn
  obtain ⟨xstar, hxinterior, hmin, hunique, hdisplacement⟩ :=
    exists_unique_interior_minimum_of_threshold center r κ p m β B hr hκ hm
      hβ hB hp V S gradV gradS HV HS hVcont hScont hV hS hHV hHS
      hVlower hSlower hcenter hVbound
  have hxstarBall : xstar ∈ Metric.closedBall center r :=
    interior_subset hxinterior
  have hκm : 0 < κ * m := mul_pos hκ hm
  have hmax : 0 ≤ max β (B / r) := le_trans hβ (le_max_left _ _)
  have hpPos : 0 < p := lt_of_le_of_lt (div_nonneg hmax (le_of_lt hκm)) hp
  have hκp : 0 ≤ κ * p := mul_nonneg hκ.le hpPos.le
  have hc : 0 < κ * p * m - β :=
    (critical_gain_estimates κ m r β B p hκ hm hr hp).1
  let Veff : E → ℝ := fun x => V x - κ * p * S x
  let geff : E → E := fun x => gradV x - (κ * p) • gradS x
  have hconvex : StronglyConvexOn (Metric.closedBall center r) Veff geff
      (κ * p * m - β) :=
    effective_potential_strongly_convex (Metric.closedBall center r)
      V S gradV gradS HV HS κ p m β (convex_closedBall center r)
      hV hS hHV hHS hVlower hSlower hκp
  have hpotential : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt Veff (innerSL ℝ (geff x)) x := by
    intro x hx
    have h := (hV x hx).sub ((hS x hx).const_mul (κ * p))
    convert h using 1 <;> simp [Veff, geff, innerSL_apply_apply, inner_smul_left]
  have hpotentialC1 : ContDiffOn ℝ 1 Veff (Metric.closedBall center r) := by
    simpa [Veff, smul_eq_mul] using
      hVcontDiff.sub (ContDiffOn.const_smul (κ * p) hScontDiff)
  have hlocal : IsLocalMin Veff xstar := by
    apply hmin.isLocalMin
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hxinterior)
      interior_subset
  have hstationaryMap := hlocal.hasFDerivAt_eq_zero
    (hpotential xstar hxstarBall)
  have hstationary : geff xstar = 0 := by
    have heval := congrArg (fun D : E →L[ℝ] ℝ => D (geff xstar))
      hstationaryMap
    have hinner : inner ℝ (geff xstar) (geff xstar) = 0 := by
      simpa [innerSL_apply_apply] using heval
    have hnorm : ‖geff xstar‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hinner
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hxstarC : xstar ∈ C :=
    hminimizerInC xstar hxstarBall (by simpa [Veff] using hmin)
  have hgeffC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 geff x := by
    intro x hx
    exact (hgradV_C1 x hx).sub
      ((hgradS_C1 x hx).const_smul (κ * p))
  have hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (geff y))) x := by
    intro x hx
    exact ((hA_C1 x hx).clm_apply (hgeffC1 x hx)).neg
  have hCball : C ⊆ Metric.closedBall center r := by
    intro x hx
    exact Metric.ball_subset_closedBall (hCclosureInterior (subset_closure hx))
  obtain ⟨trajectory, ε, hε, hinit, htrajectoryC, hdecay, hODEunique⟩ :=
    theorem21_state_dependent_mobility_global_existence_and_decay_of_uniform_local_solutions
      center r a (κ * p * m - β) gamma δ hr.le hc gamma_pos hδ
      Veff geff A (Metric.closedBall center r) C xstar x₀ hfieldC1
      hCclosureInterior hforwardInvariant hlocalInput L hL
      hCball hxstarC hx₀
      (by simpa [geff] using hstationary) hconvex hpotential hpotentialC1
      hcoercive
  refine ⟨xstar, hxinterior, hmin, hunique, hdisplacement,
    trajectory, ε, hε, hinit, htrajectoryC, ?_, ?_⟩
  · intro t ht
    simpa [Veff, mul_assoc, mul_left_comm, mul_comm] using hdecay t ht
  · intro other hotherInit hotherC hotherFlow t ht
    exact hODEunique other hotherInit hotherC
      (by simpa [geff] using hotherFlow) t ht

/-- The integral-kernel version of Theorem 21's first three conclusions.
Dominated differentiation supplies the mean gradient and Hessian; the gain
threshold then constructs the unique interior minimum, forward-invariant
sublevel, global state-dependent-mobility orbit, and quantitative exponential
decay. -/
theorem theorem21_integral_kernel_global_dynamics_from_threshold
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (center : E) (r κ p m β B gamma a : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V : E → ℝ) (gradV : E → E) (hessV : E → E →L[ℝ] E)
    (kernel : E → X → ℝ) (gradKernel : E → X → E)
    (hessKernel : E → X → E →L[ℝ] E)
    (hVcontDiff : ContDiffOn ℝ 1 V (Metric.closedBall center r))
    (hV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hHV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradV (hessV x) x)
    (hgradV_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 gradV x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (hessV x v) v)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (A : E → E →L[ℝ] E)
    (hA_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 A x)
    (gamma_pos : 0 < gamma)
    (hcoercive : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (C : Set E) (level : ℝ)
    (hCinterior : C ⊆ Metric.ball center r)
    (hCsublevel : C = {x | x ∈ Metric.closedBall center r ∧
      V x - κ * p * (∫ a, kernel x a ∂μ) ≤ level})
    (x₀ : E) (hx₀ : x₀ ∈ C)
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
          V xstar - κ * p * (∫ z, kernel xstar z ∂μ) → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) ∧
      ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
        (∀ t ∈ Set.Ici a, trajectory t ∈ C) ∧
        (∀ t ∈ Set.Ici a,
          0 ≤ (V (trajectory a) - κ * p * (∫ z, kernel (trajectory a) z ∂μ)) -
              (V xstar - κ * p * (∫ z, kernel xstar z ∂μ)) ∧
          (V (trajectory t) - κ * p * (∫ z, kernel (trajectory t) z ∂μ)) -
              (V xstar - κ * p * (∫ z, kernel xstar z ∂μ)) ≤
            ((V (trajectory a) - κ * p * (∫ z, kernel (trajectory a) z ∂μ)) -
              (V xstar - κ * p * (∫ z, kernel xstar z ∂μ))) *
                Real.exp (-2 * gamma * (κ * p * m - β) * (t - a)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((V (trajectory a) - κ * p *
              (∫ z, kernel (trajectory a) z ∂μ)) -
              (V xstar - κ * p * (∫ z, kernel xstar z ∂μ))) /
                (κ * p * m - β)) *
                Real.exp (-gamma * (κ * p * m - β) * (t - a))) := by
  have hcenterInterior : center ∈ interior (Metric.closedBall center r) :=
    Metric.ball_subset_interior_closedBall (by
      simpa [Metric.mem_ball] using hr)
  have hmeanHessianContinuous := mean_reconstruction_hessian_continuous_of_dominated
    μ hessKernel hmeanHessianDom
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
  have hmeanGradientC1 : ContDiffOn ℝ 1
      (fun x => ∫ a, gradKernel x a ∂μ) Set.univ :=
    integral_reconstruction_mean_gradient_contDiffOn_one μ Set.univ
      gradKernel hessKernel (fun x _ => hgradientDiff x)
      hmeanHessianContinuous.continuousOn convex_univ ⟨center, by simp⟩
  have hmeanGradientC1At : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => ∫ a, gradKernel y a ∂μ) x := by
    intro x _
    exact hmeanGradientC1.contDiffAt (Filter.univ_mem)
  have hpotentialC1 := integral_reconstruction_potential_contDiffOn_one μ
    (Metric.closedBall center r) kernel gradKernel hmeanGradientC1At hkernelDiff
    (convex_closedBall center r) ⟨center, hcenterInterior⟩
  have hkernel := general_reconstruction_kernel_conditions μ
    (Metric.closedBall center r) kernel gradKernel hessKernel center m
    hpotentialC1 hmeanGradientC1At hkernelDiff (fun x _ => hgradientDiff x)
    hmeanCenterZero hhessianIntegrable hmeanCurvature
  rcases hkernel with ⟨hSc1, hSderiv, hgradSc1, hHS, hcenter, hSlower⟩
  let S : E → ℝ := fun x => ∫ a, kernel x a ∂μ
  let gradS : E → E := fun x => ∫ a, gradKernel x a ∂μ
  let HS : E → E →L[ℝ] E := fun x => ∫ a, hessKernel x a ∂μ
  simpa [S, gradS, HS, mul_assoc, mul_left_comm, mul_comm] using
    theorem21_state_dependent_mobility_from_threshold center r κ p m β B
      gamma a hr hκ hm hβ hB hp V S gradV gradS hessV HS hVcontDiff
      hSc1 hV hSderiv hHV hHS hgradV_C1 hgradSc1 hVlower hSlower hcenter
      hVbound A hA_C1 gamma_pos hcoercive C level hCinterior
      (by simpa [S] using hCsublevel) x₀ hx₀

/-- A closed-ball sublevel of a function continuous on the ball is closed in
the ambient finite-dimensional normed space. The proof views the ball as a
compact subtype, takes a closed preimage there, then maps it back. -/
theorem isClosed_closedBall_sublevel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (center : E) (r level : ℝ) (f : E → ℝ)
    (hf : ContinuousOn f (Metric.closedBall center r)) :
    IsClosed {x | x ∈ Metric.closedBall center r ∧ f x ≤ level} := by
  let U : Set E := Metric.closedBall center r
  let D : Set U := {x | f x.1 ≤ level}
  have hcont : Continuous (fun x : U => f x.1) := by
    exact (continuousOn_iff_continuous_domRestrict.mp (by simpa [U] using hf))
  have hDclosed : IsClosed D := by
    change IsClosed ((fun x : U => f x.1) ⁻¹' Set.Iic level)
    exact isClosed_Iic.preimage hcont
  letI : CompactSpace U :=
    isCompact_iff_compactSpace.mp (by simpa [U] using isCompact_closedBall center r)
  have hDcompact : IsCompact D :=
    isCompact_univ.of_isClosed_subset hDclosed (Set.subset_univ D)
  have himageCompact : IsCompact (Subtype.val '' D) :=
    hDcompact.image continuous_subtype_val
  have hset : {x | x ∈ Metric.closedBall center r ∧ f x ≤ level} =
      Subtype.val '' D := by
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨x, hx⟩, hfx, rfl⟩
    · rintro ⟨⟨y, hy⟩, hfy, rfl⟩
      exact ⟨hy, hfy⟩
  rw [hset]
  exact himageCompact.isClosed

/-- Finite-dimensional exact-sublevel specialization of Theorem 21's four
conclusions. The symbolic measure `μ` on the available branch supplies the
reconstruction potential and support LUB; the information clause uses its own
input law `ν`, as in the paper. Dominated differentiation derives the smooth
mean gradient and Hessian from kernel-level assumptions. The region `C` is the
closed-ball sublevel itself; continuity proves it closed, the assumed strict
energy barrier on the sphere then proves its closure lies in the open ball,
and dissipation derives forward invariance. Membership of the minimizer and
initial state in `C` is assumed only for the initial state; the minimizer's
membership follows from global minimality and the initial sublevel bound. This
is a finite-dimensional specialization with finite goal type, not the
arbitrary invariant-region formulation. -/
theorem theorem21_integral_kernel_and_information
    {L E X G Y : Type*} [CompleteLattice L] [TopologicalSpace L]
    [MeasurableSpace L] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace X]
    [MeasurableSpace Y] [Fintype G]
    (branch : Set L)
    (μ : MeasureTheory.Measure (↥branch))
    [MeasureTheory.IsProbabilityMeasure μ]
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν]
    (_htop : (⊤ : L) ∉ branch)
    (_haddress : sSup (Subtype.val '' μ.support) ∈ branch)
    (center : E) (r κ p m β B gamma a : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V : E → ℝ) (gradV : E → E) (hessV : E → E →L[ℝ] E)
    (kernel : E → ↥branch → ℝ)
    (gradKernel : E → ↥branch → E)
    (hessKernel : E → ↥branch → E →L[ℝ] E)
    (hVcontDiff : ContDiffOn ℝ 1 V (Metric.closedBall center r))
    (hV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hHV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradV (hessV x) x)
    (hgradV_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 gradV x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (hessV x v) v)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (A : E → E →L[ℝ] E)
    (_hAsymmetric : ∀ x ∈ Metric.closedBall center r, ∀ u v : E,
      inner ℝ (A x u) v = inner ℝ u (A x v))
    (hA_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 A x)
    (gamma_pos : 0 < gamma)
    (hcoercive : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (C : Set E) (level : ℝ)
    (x₀ : E) (hx₀ : x₀ ∈ C)
    (hmeanHessianDom : HasDominatedContinuousReconstructionHessian μ hessKernel)
    (hkernelDiff : ∀ x ∈ Metric.closedBall center r,
      HasDominatedReconstructionKernelFDerivAt μ kernel gradKernel x)
    (hgradientDiff : ∀ x : E,
      HasDominatedReconstructionGradientFDerivAt μ gradKernel hessKernel x)
    (hcenterGradientZero : ∀ᵐ z ∂μ, gradKernel center z = 0)
    (hkernelCurvature : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      ∀ᵐ z ∂μ, inner ℝ (hessKernel x z v) v ≤ -m * ‖v‖ ^ 2)
    (hCexact : C = {x | x ∈ Metric.closedBall center r ∧
      V x - κ * p * (∫ z, kernel x z ∂μ) ≤ level})
    (hCboundary : ∀ x, dist x center = r →
      level < V x - κ * p * (∫ z, kernel x z ∂μ))
    (mass : X → G → ℝ) (action : X → G → Y)
    (goalAbstraction : G → L)
    (hgoals_in_branch : ∀ᵐ x ∂ν, ∀ g, 0 < mass x g →
      goalAbstraction g ∈ branch)
    (hmass_nonneg_ae : ∀ᵐ x ∂ν, ∀ g, 0 ≤ mass x g)
    (hmass_sum_one_ae : ∀ᵐ x ∂ν, ∑ g : G, mass x g = 1)
    (hinjective_ae : ∀ᵐ x ∂ν, ∀ g, 0 < mass x g →
      ∀ g', action x g' = action x g → g' = g)
    (_haction_meas : ∀ g, Measurable (fun x => action x g))
    (hmass_meas : ∀ g, MeasureTheory.AEStronglyMeasurable
      (fun x => mass x g) ν)
    (hinput_entropy_positive : 0 < conditionalGoalEntropy ν mass) :
    (∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * (∫ z, kernel x z ∂μ))
        (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * (∫ z, kernel y z ∂μ) =
          V xstar - κ * p * (∫ z, kernel xstar z ∂μ) → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) ∧
      ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
        (∀ t ∈ Set.Ici a, trajectory t ∈ C) ∧
        (∀ t ∈ Set.Ici a,
          V (trajectory t) - κ * p * (∫ z, kernel (trajectory t) z ∂μ) ≤ level) ∧
        (∀ t ∈ Set.Ici a,
          0 ≤ (V (trajectory a) - κ * p *
            (∫ z, kernel (trajectory a) z ∂μ)) -
            (V xstar - κ * p * (∫ z, kernel xstar z ∂μ)) ∧
          (V (trajectory t) - κ * p *
            (∫ z, kernel (trajectory t) z ∂μ)) -
            (V xstar - κ * p * (∫ z, kernel xstar z ∂μ)) ≤
            ((V (trajectory a) - κ * p *
              (∫ z, kernel (trajectory a) z ∂μ)) -
              (V xstar - κ * p * (∫ z, kernel xstar z ∂μ))) *
                Real.exp (-2 * gamma * (κ * p * m - β) * (t - a)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((V (trajectory a) - κ * p *
              (∫ z, kernel (trajectory a) z ∂μ)) -
              (V xstar - κ * p * (∫ z, kernel xstar z ∂μ))) /
                (κ * p * m - β)) *
                Real.exp (-gamma * (κ * p * m - β) * (t - a))) ∧
        (∀ other : ℝ → E, other a = x₀ →
          (∀ t ∈ Set.Ici a, other t ∈ C) →
          (∀ t ∈ Set.Ioi (a - ε), HasDerivAt other
            (-(A (other t) (gradV (other t) - (κ * p) •
              (∫ z, gradKernel (other t) z ∂μ)))) t) →
          ∀ t ∈ Set.Ici a, other t = trajectory t)) ∧
      (conditionalGoalMutualInformation ν mass action =
        conditionalGoalEntropy ν mass ∧
      0 < conditionalGoalMutualInformation ν mass action ∧
      (∀ᵐ x ∂ν, ∀ g, 0 < mass x g → goalAbstraction g ∈ branch)) := by
  have hcenterInterior : center ∈ interior (Metric.closedBall center r) :=
    Metric.ball_subset_interior_closedBall (by
      simpa [Metric.mem_ball] using hr)
  have hmeanHessianContinuous := mean_reconstruction_hessian_continuous_of_dominated
    μ hessKernel hmeanHessianDom
  have hhessianIntegrable : ∀ x ∈ Metric.closedBall center r,
      MeasureTheory.Integrable (hessKernel x) μ := by
    rcases hmeanHessianDom with ⟨bound, hmeas, hbound, hboundIntegrable, _⟩
    have hboundNorm : MeasureTheory.Integrable (fun z => |bound z|) μ := by
      simpa [Real.norm_eq_abs] using hboundIntegrable.norm
    intro x _
    apply hboundNorm.mono' (hmeas x)
    filter_upwards [hbound x] with z hz
    have hbound_nonneg : 0 ≤ bound z := le_trans (norm_nonneg _) hz
    simpa [Real.norm_eq_abs, abs_of_nonneg hbound_nonneg] using hz
  have hmeanCurvature : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ ((∫ z, hessKernel x z ∂μ) v) v ≤ -m * ‖v‖ ^ 2 := by
    intro x hx v
    exact mean_hessian_curvature_of_ae μ (fun z => hessKernel x z) x m v
      (hhessianIntegrable x hx) (hkernelCurvature x hx v)
  rcases hgradientDiff center with
    ⟨_, _, _, _, hcenterGradientIntegrable, _, _, _, _⟩
  have hmeanCenterZero := probability_integral_gradient_eq_zero μ
    (gradKernel center) hcenterGradientIntegrable hcenterGradientZero
  have hmeanGradientC1 : ContDiffOn ℝ 1
      (fun x => ∫ z, gradKernel x z ∂μ) Set.univ :=
    integral_reconstruction_mean_gradient_contDiffOn_one μ Set.univ
      gradKernel hessKernel (fun x _ => hgradientDiff x)
      hmeanHessianContinuous.continuousOn convex_univ ⟨center, by simp⟩
  have hmeanGradientC1At : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => ∫ z, gradKernel y z ∂μ) x := by
    intro x _
    exact hmeanGradientC1.contDiffAt Filter.univ_mem
  have hpotentialC1 := integral_reconstruction_potential_contDiffOn_one μ
    (Metric.closedBall center r) kernel gradKernel hmeanGradientC1At hkernelDiff
    (convex_closedBall center r) ⟨center, hcenterInterior⟩
  have hkernelConditions := general_reconstruction_kernel_conditions μ
    (Metric.closedBall center r) kernel gradKernel hessKernel center m
    hpotentialC1 hmeanGradientC1At hkernelDiff (fun x _ => hgradientDiff x)
    hmeanCenterZero hhessianIntegrable hmeanCurvature
  rcases hkernelConditions with
    ⟨hSc1, hSderiv, hgradSC1, hHS, hcenterGradientZero, hSlower⟩
  let S : E → ℝ := fun x => ∫ z, kernel x z ∂μ
  let gradS : E → E := fun x => ∫ z, gradKernel x z ∂μ
  let hessS : E → E →L[ℝ] E := fun x => ∫ z, hessKernel x z ∂μ
  have hSrepresentation : ∀ x, S x = ∫ z, kernel x z ∂μ := by
    intro x
    rfl
  have hx₀C : x₀ ∈ Metric.closedBall center r ∧
      V x₀ - κ * p * (∫ z, kernel x₀ z ∂μ) ≤ level := by
    simpa only [hCexact, Set.mem_setOf_eq] using hx₀
  refine ⟨?_, ?_⟩
  · have hminimizerInCS : ∀ x, x ∈ Metric.closedBall center r →
        IsMinOn (fun y => V y - κ * p * S y)
          (Metric.closedBall center r) x → x ∈ C := by
      intro x hx hmin
      rw [hCexact]
      refine ⟨hx, ?_⟩
      have hminAtInitial := hmin (a := x₀) (by
        simpa [hSrepresentation] using hx₀C.1)
      have hinitialLevel : V x₀ - κ * p * S x₀ ≤ level := by
        simpa [hSrepresentation] using hx₀C.2
      have hminLevel : V x - κ * p * S x ≤ level := by
        calc
          V x - κ * p * S x ≤ V x₀ - κ * p * S x₀ := by
            simpa [hSrepresentation] using hminAtInitial
          _ ≤ level := hinitialLevel
      simpa [hSrepresentation] using hminLevel
    let geffFlow : E → E := fun x => gradV x - (κ * p) • gradS x
    have hgeffFlowC1 : ∀ x ∈ Metric.closedBall center r,
        ContDiffAt ℝ 1 geffFlow x := by
      intro x hx
      exact (hgradV_C1 x hx).sub
        ((hgradSC1 x hx).const_smul (κ * p))
    have hfieldFlowC1 : ∀ x ∈ Metric.closedBall center r,
        ContDiffAt ℝ 1 (fun y => -(A y (geffFlow y))) x := by
      intro x hx
      exact ((hA_C1 x hx).clm_apply (hgeffFlowC1 x hx)).neg
    have hVeffCont : ContinuousOn (fun x => V x - κ * p * S x)
        (Metric.closedBall center r) := by
      exact hVcontDiff.continuousOn.sub
        (hSc1.continuousOn.const_mul (κ * p))
    have hCclosed : IsClosed C := by
      rw [hCexact]
      simpa [hSrepresentation] using
        (isClosed_closedBall_sublevel center r level
          (fun x => V x - κ * p * S x) hVeffCont)
    have hCinterior : C ⊆ Metric.ball center r := by
      intro x hx
      rw [hCexact] at hx
      apply Metric.mem_ball.mpr
      have hdist_le : dist x center ≤ r := Metric.mem_closedBall.mp hx.1
      by_contra hdist_not_lt
      have hdist_eq : dist x center = r :=
        le_antisymm hdist_le (le_of_not_gt hdist_not_lt)
      exact (not_lt_of_ge hx.2) (hCboundary x hdist_eq)
    have hCclosureInterior : closure C ⊆ Metric.ball center r := by
      rw [hCclosed.closure_eq]
      exact hCinterior
    have hCball : C ⊆ Metric.closedBall center r := by
      intro x hx
      exact Metric.ball_subset_closedBall
        (hCclosureInterior (subset_closure hx))
    have hclosureBall : closure C ⊆ Metric.closedBall center r :=
      closure_minimal hCball Metric.isClosed_closedBall
    have hclosureCompact : IsCompact (closure C) :=
      (isCompact_closedBall center r).of_isClosed_subset isClosed_closure hclosureBall
    have hclosureNonempty : (closure C).Nonempty := ⟨x₀, subset_closure hx₀⟩
    let fieldFlow : E → E := fun x => -(A x (geffFlow x))
    have hregularClosure : ∀ x ∈ closure C, ContDiffAt ℝ 1 fieldFlow x := by
      intro x hx
      exact hfieldFlowC1 x (hclosureBall hx)
    obtain ⟨δ, hδ, hlocalClosure⟩ := exists_uniform_forward_local_trajectory_on_compact
      fieldFlow (closure C) hclosureCompact hclosureNonempty hregularClosure
    have hlocalSolution : ∀ t₀ : ℝ, ∀ x ∈ C,
        ∃ localOrbit : ℝ → E,
          localOrbit t₀ = x ∧
          ∀ t ∈ Set.Icc t₀ (t₀ + δ),
            HasDerivAt localOrbit
              (-(A (localOrbit t) (geffFlow (localOrbit t)))) t := by
      intro t₀ x hx
      obtain ⟨localOrbit, hinit, hflow⟩ :=
        hlocalClosure t₀ x (subset_closure hx)
      exact ⟨localOrbit, hinit, fun t ht => by
        simpa [fieldFlow] using hflow t ht⟩
    have hCexactS : C = {x | x ∈ Metric.closedBall center r ∧
        V x - κ * p * S x ≤ level} := by
      simpa [hSrepresentation] using hCexact
    have hpotentialFlow : ∀ x ∈ Metric.closedBall center r,
        HasFDerivAt (fun y => V y - κ * p * S y)
          (innerSL ℝ (geffFlow x)) x := by
      intro x hx
      have h := (hV x hx).sub ((hSderiv x hx).const_mul (κ * p))
      convert h using 1 <;>
        simp [geffFlow, gradS, innerSL_apply_apply, inner_smul_left]
    have hforwardInvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → E) (x : E),
        0 ≤ d → orbit t₀ = x → x ∈ C →
        (∀ t ∈ Set.Icc t₀ (t₀ + d), HasDerivAt orbit
          (-(A (orbit t) (gradV (orbit t) - (κ * p) • gradS (orbit t)))) t) →
        ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ C := by
      intro t₀ d orbit x hd hinit hx hflow
      apply forward_invariant_sublevel_of_strict_interior_barrier
        orbit (fun y => V y - κ * p * S y) geffFlow A center r gamma
        t₀ (t₀ + d) level gamma_pos (by linarith) C hCexactS hCinterior
        x hx hinit hpotentialFlow
      · exact hflow
      · exact hcoercive
    obtain ⟨L, hL⟩ := exists_lipschitz_constant_on_closedBall_of_contDiffAt
      fieldFlow center r hfieldFlowC1
    obtain ⟨xstar, hxstar, hmin, hunique, hdisp,
      trajectory, ε, hε, hinit, htrajectoryC, hdecay, huniqueODE⟩ :=
      theorem21_state_dependent_mobility_from_threshold_on_invariant_region
        center r κ p m β B gamma a hr hκ hm hβ hB hp V S gradV gradS
        hessV hessS hVcontDiff hSc1 hV hSderiv hHV hHS hgradV_C1
        hgradSC1 hVlower hSlower hcenterGradientZero hVbound A hA_C1 gamma_pos
        hcoercive C hCclosureInterior δ hδ hlocalSolution L hL
        hforwardInvariant
        hminimizerInCS
        x₀ hx₀
    refine ⟨xstar, hxstar, ?_, ?_, hdisp, trajectory, ε, hε, hinit,
      htrajectoryC, ?_, ?_, ?_⟩
    · simpa [hSrepresentation] using hmin
    · intro y hy hEq
      apply hunique y hy
      simpa [hSrepresentation] using hEq
    · intro t ht
      have hmem := htrajectoryC t ht
      rw [hCexact] at hmem
      exact hmem.2
    · intro t ht
      simpa [hSrepresentation] using hdecay t ht
    · intro other hotherInit hotherC hotherFlow t ht
      exact huniqueODE other hotherInit hotherC
        (by simpa [hSrepresentation, gradS] using hotherFlow) t ht
  · have hcapacity := theorem21_general_input_information_capacity ν mass
      action _haction_meas hmass_nonneg_ae hmass_sum_one_ae hinjective_ae hmass_meas
      hinput_entropy_positive
    exact ⟨hcapacity.1, hcapacity.2, hgoals_in_branch⟩

/-- A global solution certificate, matching Theorem 21's conditional ODE
hypothesis. This separates the existence of the closed-loop solution from the
decay estimate, which does not require compactness of the state ball. -/
structure Theorem21GlobalOrbit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (field : E → E) (U C : Set E) (a : ℝ) (x₀ : E) where
  trajectory : ℝ → E
  ε : ℝ
  epsilon_pos : 0 < ε
  initial : trajectory a = x₀
  flow : ∀ t, a - ε < t → HasDerivAt trajectory (field (trajectory t)) t
  nearRegion : ∀ t, a - ε < t → trajectory t ∈ U
  unique : ∀ other : ℝ → E, other a = x₀ →
    (∀ t ∈ Set.Ici a, other t ∈ C) →
    (∀ t, a ≤ t → HasDerivAt other (field (other t)) t) →
    ∀ t ∈ Set.Ici a, other t = trajectory t

/-- Finite-dimensional integral-kernel version of Theorem 21 on an arbitrary
forward-invariant partial sublevel region. The threshold assumptions give the
unique interior minimizer. C¹ regularity of the closed-loop field, compactness
of the closure of the region, and its assumed forward invariance construct a
global trajectory and give uniqueness; strong convexity and coercive mobility
then give the quantitative exponential rate. The minimizer is assumed to lie
in this particular invariant region, as required by the paper's dynamics
clause. The finite-goal information conclusion is proved in the same theorem. -/
theorem theorem21_integral_kernel_and_information_on_invariant_region
    {L E X G Y : Type*} [CompleteLattice L] [TopologicalSpace L]
    [MeasurableSpace L] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace X]
    [MeasurableSpace Y] [Fintype G]
    (branch : Set L)
    (μ : MeasureTheory.Measure (↥branch))
    [MeasureTheory.IsProbabilityMeasure μ]
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν]
    (_htop : (⊤ : L) ∉ branch)
    (_haddress : sSup (Subtype.val '' μ.support) ∈ branch)
    (center : E) (r κ p m β B gamma a : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V : E → ℝ) (gradV : E → E) (hessV : E → E →L[ℝ] E)
    (kernel : E → ↥branch → ℝ)
    (gradKernel : E → ↥branch → E)
    (hessKernel : E → ↥branch → E →L[ℝ] E)
    (hVcontDiff : ContDiffOn ℝ 1 V (Metric.closedBall center r))
    (hV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hHV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradV (hessV x) x)
    (hgradV_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 gradV x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (hessV x v) v)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (A : E → E →L[ℝ] E)
    (_hAsymmetric : ∀ x ∈ Metric.closedBall center r, ∀ u v : E,
      inner ℝ (A x u) v = inner ℝ u (A x v))
    (hA_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 A x)
    (gamma_pos : 0 < gamma)
    (hcoercive : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (C : Set E) (level : ℝ)
    (hCclosureInterior : closure C ⊆ Metric.ball center r)
    (hCsublevel : ∀ x ∈ C,
      V x - κ * p * (∫ z, kernel x z ∂μ) ≤ level)
    (x₀ : E) (hx₀ : x₀ ∈ C)
    (hmeanHessianDom : HasDominatedContinuousReconstructionHessian μ hessKernel)
    (hkernelDiff : ∀ x ∈ Metric.closedBall center r,
      HasDominatedReconstructionKernelFDerivAt μ kernel gradKernel x)
    (hgradientDiff : ∀ x : E,
      HasDominatedReconstructionGradientFDerivAt μ gradKernel hessKernel x)
    (hcenterGradientZero : ∀ᵐ z ∂μ, gradKernel center z = 0)
    (hkernelCurvature : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      ∀ᵐ z ∂μ, inner ℝ (hessKernel x z v) v ≤ -m * ‖v‖ ^ 2)
    (hforwardInvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit t₀ = x → x ∈ C →
      (∀ t ∈ Set.Icc t₀ (t₀ + d),
        HasDerivAt orbit
          (-(A (orbit t) (gradV (orbit t) - (κ * p) •
            (∫ z, gradKernel (orbit t) z ∂μ)))) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ C)
    (hminimizerInC : ∀ x, x ∈ Metric.closedBall center r → IsMinOn
      (fun y => V y - κ * p * (∫ z, kernel y z ∂μ))
      (Metric.closedBall center r) x → x ∈ C)
    (mass : X → G → ℝ) (action : X → G → Y)
    (goalAbstraction : G → L)
    (hgoals_in_branch : ∀ᵐ x ∂ν, ∀ g, 0 < mass x g →
      goalAbstraction g ∈ branch)
    (hmass_nonneg_ae : ∀ᵐ x ∂ν, ∀ g, 0 ≤ mass x g)
    (hmass_sum_one_ae : ∀ᵐ x ∂ν, ∑ g : G, mass x g = 1)
    (hinjective_ae : ∀ᵐ x ∂ν, ∀ g, 0 < mass x g →
      ∀ g', action x g' = action x g → g' = g)
    (_haction_meas : ∀ g, Measurable (fun x => action x g))
    (hmass_meas : ∀ g, MeasureTheory.AEStronglyMeasurable
      (fun x => mass x g) ν)
    (hinput_entropy_positive : 0 < conditionalGoalEntropy ν mass) :
    (∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * (∫ z, kernel x z ∂μ))
        (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * (∫ z, kernel y z ∂μ) =
          V xstar - κ * p * (∫ z, kernel xstar z ∂μ) → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) ∧
      (∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
        (∀ t ∈ Set.Ioi (a - ε),
          HasDerivAt trajectory
            (-(A (trajectory t) (gradV (trajectory t) - (κ * p) •
              (∫ z, gradKernel (trajectory t) z ∂μ)))) t) ∧
        (∀ t ∈ Set.Ici a, trajectory t ∈ C) ∧
        (∀ t ∈ Set.Ici a,
          0 ≤ (V (trajectory a) - κ * p *
            (∫ z, kernel (trajectory a) z ∂μ)) -
            (V xstar - κ * p * (∫ z, kernel xstar z ∂μ)) ∧
          (V (trajectory t) - κ * p *
            (∫ z, kernel (trajectory t) z ∂μ)) -
            (V xstar - κ * p * (∫ z, kernel xstar z ∂μ)) ≤
            ((V (trajectory a) - κ * p *
              (∫ z, kernel (trajectory a) z ∂μ)) -
              (V xstar - κ * p * (∫ z, kernel xstar z ∂μ))) *
                Real.exp (-2 * gamma * (κ * p * m - β) * (t - a)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((V (trajectory a) - κ * p *
              (∫ z, kernel (trajectory a) z ∂μ)) -
              (V xstar - κ * p * (∫ z, kernel xstar z ∂μ))) /
              (κ * p * m - β)) *
                Real.exp (-gamma * (κ * p * m - β) * (t - a))) ∧
        (∀ other : ℝ → E, other a = x₀ →
          (∀ t ∈ Set.Ici a, other t ∈ C) →
          (∀ t ∈ Set.Ioi (a - ε), HasDerivAt other
            (-(A (other t) (gradV (other t) - (κ * p) •
              (∫ z, gradKernel (other t) z ∂μ)))) t) →
          ∀ t ∈ Set.Ici a, other t = trajectory t))) ∧
      (conditionalGoalMutualInformation ν mass action =
        conditionalGoalEntropy ν mass ∧
      0 < conditionalGoalMutualInformation ν mass action ∧
      (∀ᵐ x ∂ν, ∀ g, 0 < mass x g → goalAbstraction g ∈ branch)) := by
  have hcenterInterior : center ∈ interior (Metric.closedBall center r) :=
    Metric.ball_subset_interior_closedBall (by
      simpa [Metric.mem_ball] using hr)
  have hmeanHessianContinuous := mean_reconstruction_hessian_continuous_of_dominated
    μ hessKernel hmeanHessianDom
  have hhessianIntegrable : ∀ x ∈ Metric.closedBall center r,
      MeasureTheory.Integrable (hessKernel x) μ := by
    rcases hmeanHessianDom with ⟨bound, hmeas, hbound, hboundIntegrable, _⟩
    have hboundNorm : MeasureTheory.Integrable (fun z => |bound z|) μ := by
      simpa [Real.norm_eq_abs] using hboundIntegrable.norm
    intro x _
    apply hboundNorm.mono' (hmeas x)
    filter_upwards [hbound x] with z hz
    have hbound_nonneg : 0 ≤ bound z := le_trans (norm_nonneg _) hz
    simpa [Real.norm_eq_abs, abs_of_nonneg hbound_nonneg] using hz
  have hmeanCurvature : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ ((∫ z, hessKernel x z ∂μ) v) v ≤ -m * ‖v‖ ^ 2 := by
    intro x hx v
    exact mean_hessian_curvature_of_ae μ (fun z => hessKernel x z) x m v
      (hhessianIntegrable x hx) (hkernelCurvature x hx v)
  rcases hgradientDiff center with
    ⟨_, _, _, _, hcenterGradientIntegrable, _, _, _, _⟩
  have hmeanCenterZero := probability_integral_gradient_eq_zero μ
    (gradKernel center) hcenterGradientIntegrable hcenterGradientZero
  have hmeanGradientC1 : ContDiffOn ℝ 1
      (fun x => ∫ z, gradKernel x z ∂μ) Set.univ :=
    integral_reconstruction_mean_gradient_contDiffOn_one μ Set.univ
      gradKernel hessKernel (fun x _ => hgradientDiff x)
      hmeanHessianContinuous.continuousOn convex_univ ⟨center, by simp⟩
  have hmeanGradientC1At : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => ∫ z, gradKernel y z ∂μ) x := by
    intro x _
    exact hmeanGradientC1.contDiffAt Filter.univ_mem
  have hpotentialC1 := integral_reconstruction_potential_contDiffOn_one μ
    (Metric.closedBall center r) kernel gradKernel hmeanGradientC1At hkernelDiff
    (convex_closedBall center r) ⟨center, hcenterInterior⟩
  have hkernelConditions := general_reconstruction_kernel_conditions μ
    (Metric.closedBall center r) kernel gradKernel hessKernel center m
    hpotentialC1 hmeanGradientC1At hkernelDiff (fun x _ => hgradientDiff x)
    hmeanCenterZero hhessianIntegrable hmeanCurvature
  rcases hkernelConditions with
    ⟨hSc1, hSderiv, hgradSC1, hHS, hcenterGradientZero, hSlower⟩
  let S : E → ℝ := fun x => ∫ z, kernel x z ∂μ
  let gradS : E → E := fun x => ∫ z, gradKernel x z ∂μ
  let hessS : E → E →L[ℝ] E := fun x => ∫ z, hessKernel x z ∂μ
  have hSrepresentation : ∀ x, S x = ∫ z, kernel x z ∂μ := by
    intro x
    rfl
  have hVcont : ContinuousOn V (Metric.closedBall center r) := hVcontDiff.continuousOn
  have hScont : ContinuousOn S (Metric.closedBall center r) := hSc1.continuousOn
  obtain ⟨xstar, hxinterior, hmin, hunique, hdisplacement⟩ :=
    exists_unique_interior_minimum_of_threshold center r κ p m β B hr hκ hm
      hβ hB hp V S gradV gradS hessV hessS hVcont hScont hV hSderiv hHV hHS
      hVlower hSlower hcenterGradientZero hVbound
  have hxstarBall : xstar ∈ Metric.closedBall center r := interior_subset hxinterior
  have hκm : 0 < κ * m := mul_pos hκ hm
  have hmax : 0 ≤ max β (B / r) := le_trans hβ (le_max_left _ _)
  have hpPos : 0 < p := lt_of_le_of_lt (div_nonneg hmax (le_of_lt hκm)) hp
  have hκp : 0 ≤ κ * p := mul_nonneg hκ.le hpPos.le
  have hc : 0 < κ * p * m - β :=
    (critical_gain_estimates κ m r β B p hκ hm hr hp).1
  let Veff : E → ℝ := fun x => V x - κ * p * S x
  let geff : E → E := fun x => gradV x - (κ * p) • gradS x
  have hconvex : StronglyConvexOn (Metric.closedBall center r) Veff geff
      (κ * p * m - β) :=
    effective_potential_strongly_convex (Metric.closedBall center r)
      V S gradV gradS hessV hessS κ p m β (convex_closedBall center r)
      hV hSderiv hHV hHS hVlower hSlower hκp
  have hpotential : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt Veff (innerSL ℝ (geff x)) x := by
    intro x hx
    have h := (hV x hx).sub ((hSderiv x hx).const_mul (κ * p))
    convert h using 1 <;>
      simp [Veff, geff, gradS, innerSL_apply_apply, inner_smul_left]
  have hpotentialC1 : ContDiffOn ℝ 1 Veff (Metric.closedBall center r) := by
    simpa [Veff, smul_eq_mul] using hVcontDiff.sub (ContDiffOn.const_smul (κ * p) hSc1)
  have hlocal : IsLocalMin Veff xstar := by
    apply hmin.isLocalMin
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hxinterior) interior_subset
  have hstationaryMap := hlocal.hasFDerivAt_eq_zero (hpotential xstar hxstarBall)
  have hstationary : geff xstar = 0 := by
    have heval := congrArg (fun D : E →L[ℝ] ℝ => D (geff xstar)) hstationaryMap
    have hinner : inner ℝ (geff xstar) (geff xstar) = 0 := by
      simpa [innerSL_apply_apply] using heval
    have hnorm : ‖geff xstar‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hinner
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hxstarC : xstar ∈ C := by
    apply hminimizerInC xstar hxstarBall
    simpa [hSrepresentation] using hmin
  have hCsubset : C ⊆ Metric.closedBall center r := by
    intro x hx
    exact Metric.ball_subset_closedBall (hCclosureInterior (subset_closure hx))
  have hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (geff y))) x := by
    intro x hx
    exact ((hA_C1 x hx).clm_apply
      ((hgradV_C1 x hx).sub
        ((hgradSC1 x hx).const_smul (κ * p)))).neg
  obtain ⟨trajectory, ε, hε, hinit, htrajectoryFlow, htrajectoryC,
      hdecay, hODEunique⟩ :=
    theorem21_state_dependent_mobility_global_existence_and_decay
      center r a (κ * p * m - β) gamma hr.le hc gamma_pos Veff geff A
      (Metric.closedBall center r) C xstar x₀ hfieldC1 hCclosureInterior
      hforwardInvariant hCsubset hxstarC hx₀
      (by simpa [geff] using hstationary) hconvex hpotential hpotentialC1
      hcoercive
  refine ⟨?_, ?_⟩
  · refine ⟨xstar, hxinterior, ?_, ?_, hdisplacement, ?_⟩
    · simpa [hSrepresentation] using hmin
    · intro y hy hEq
      apply hunique y hy
      simpa [hSrepresentation] using hEq
    · refine ⟨trajectory, ε, hε, hinit, ?_, htrajectoryC, ?_, ?_⟩
      · intro t ht
        simpa [geff] using htrajectoryFlow t ht
      · intro t ht
        simpa [Veff, hSrepresentation, mul_assoc, mul_left_comm, mul_comm] using
          hdecay t ht
      · intro other hotherInit hotherC hotherFlow
        exact hODEunique other hotherInit hotherC (by
          intro s hs
          simpa [geff] using hotherFlow s hs)
  · have hcapacity := theorem21_general_input_information_capacity ν mass
      action _haction_meas hmass_nonneg_ae hmass_sum_one_ae hinjective_ae hmass_meas
      hinput_entropy_positive
    exact ⟨hcapacity.1, hcapacity.2, hgoals_in_branch⟩


end Tomabechi.Theorem21
