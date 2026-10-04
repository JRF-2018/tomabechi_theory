import Theorem21

/-!
# Theorem 21: concrete model applications

This module collects finite reconstruction-kernel applications of the general
Theorem 21 results and the explicit one-dimensional quadratic example. The
finite-support differentiation and averaging lemmas remain in `Theorem21.lean`
because the general development also uses them.
-/

namespace Tomabechi.Theorem21

open RealInnerProductSpace
open Filter
open scoped Topology NNReal ContDiff

/-- Adapter from the finite weighted reconstruction package to the global
state-dependent-mobility theorem. The package can be obtained from
`finite_reconstruction_kernel_conditions`. -/
theorem theorem21_finite_reconstruction_global_dynamics_from_threshold
    {A E : Type*} [Fintype A] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (center : E) (r κ p m β B gamma a : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V : E → ℝ) (gradV : E → E) (hessV : E → E →L[ℝ] E)
    (kernel : A → E → ℝ) (gradKernel : A → E → E)
    (hessKernel : A → E → E →L[ℝ] E) (weight : A → ℝ)
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
    (hweight : ∀ a, 0 ≤ weight a) (hnorm : ∑ a, weight a = 1)
    (hkernelC2 : ∀ a, ContDiffOn ℝ 2 (kernel a) (Metric.closedBall center r))
    (hkernelGrad : ∀ a x, x ∈ Metric.closedBall center r →
      HasFDerivAt (kernel a) (innerSL ℝ (gradKernel a x)) x)
    (hgradKernelC1 : ∀ a x, x ∈ Metric.closedBall center r →
      ContDiffAt ℝ 1 (gradKernel a) x)
    (hgradHess : ∀ a x, x ∈ Metric.closedBall center r →
      HasFDerivAt (gradKernel a) (hessKernel a x) x)
    (hcenter : ∀ a, gradKernel a center = 0)
    (hbound : ∀ a x, x ∈ Metric.closedBall center r → ∀ v : E,
      inner ℝ (hessKernel a x v) v ≤ -m * ‖v‖ ^ 2)
    (Aop : E → E →L[ℝ] E)
    (hA_C1 : ∀ x ∈ Metric.closedBall center r, ContDiffAt ℝ 1 Aop x)
    (gamma_pos : 0 < gamma)
    (hcoercive : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (Aop x v) v)
    (C : Set E) (level : ℝ) (hCinterior : C ⊆ Metric.ball center r)
    (hCsublevel : C = {x | x ∈ Metric.closedBall center r ∧
      V x - κ * p * finiteReconstructionKernel weight kernel x ≤ level})
    (x₀ : E) (hx₀ : x₀ ∈ C) :
    ∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * finiteReconstructionKernel weight kernel x)
        (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * finiteReconstructionKernel weight kernel y =
          V xstar - κ * p * finiteReconstructionKernel weight kernel xstar → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) ∧
      ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
        (∀ t ∈ Set.Ici a, trajectory t ∈ C) ∧
        (∀ t ∈ Set.Ici a,
          0 ≤ (V (trajectory a) - κ * p *
              finiteReconstructionKernel weight kernel (trajectory a)) -
              (V xstar - κ * p * finiteReconstructionKernel weight kernel xstar) ∧
          (V (trajectory t) - κ * p *
              finiteReconstructionKernel weight kernel (trajectory t)) -
              (V xstar - κ * p * finiteReconstructionKernel weight kernel xstar) ≤
            ((V (trajectory a) - κ * p *
              finiteReconstructionKernel weight kernel (trajectory a)) -
              (V xstar - κ * p * finiteReconstructionKernel weight kernel xstar)) *
                Real.exp (-2 * gamma * (κ * p * m - β) * (t - a)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((V (trajectory a) - κ * p *
              finiteReconstructionKernel weight kernel (trajectory a)) -
              (V xstar - κ * p * finiteReconstructionKernel weight kernel xstar)) /
                (κ * p * m - β)) *
                Real.exp (-gamma * (κ * p * m - β) * (t - a))) := by
  obtain ⟨hSc1, hS, hgradSc1, hHS, hcenterS, hSlower⟩ :=
    finite_reconstruction_kernel_conditions (Metric.closedBall center r)
      weight kernel gradKernel hessKernel center m hweight hnorm hkernelC2
      hkernelGrad hgradKernelC1 hgradHess hcenter hbound
  exact theorem21_state_dependent_mobility_from_threshold center r κ p m β B
    gamma a hr hκ hm hβ hB hp V (finiteReconstructionKernel weight kernel)
    gradV (finiteReconstructionGradient weight gradKernel) hessV
    (finiteReconstructionHessian weight hessKernel) hVcontDiff hSc1 hV hS hHV
    hHS hgradV_C1 hgradSc1 hVlower hSlower hcenterS hVbound Aop hA_C1
    gamma_pos hcoercive C level hCinterior (by simpa using hCsublevel) x₀ hx₀

/-- Finite weighted reconstruction kernels also support the paper's more
general invariant partial sublevel formulation. The kernel assumptions yield
the derivatives and curvature of the averaged potential; compactness supplies
uniform local solutions and a Lipschitz constant for the finite-dimensional
closed-loop field. -/
theorem theorem21_finite_reconstruction_partial_invariant_region
    {A E : Type*} [Fintype A] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (center : E) (r κ p m β B gamma a : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V : E → ℝ) (gradV : E → E) (hessV : E → E →L[ℝ] E)
    (kernel : A → E → ℝ) (gradKernel : A → E → E)
    (hessKernel : A → E → E →L[ℝ] E) (weight : A → ℝ)
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
    (hweight : ∀ a, 0 ≤ weight a) (hnorm : ∑ a, weight a = 1)
    (hkernelC2 : ∀ a, ContDiffOn ℝ 2 (kernel a) (Metric.closedBall center r))
    (hkernelGrad : ∀ a x, x ∈ Metric.closedBall center r →
      HasFDerivAt (kernel a) (innerSL ℝ (gradKernel a x)) x)
    (hgradKernelC1 : ∀ a x, x ∈ Metric.closedBall center r →
      ContDiffAt ℝ 1 (gradKernel a) x)
    (hgradHess : ∀ a x, x ∈ Metric.closedBall center r →
      HasFDerivAt (gradKernel a) (hessKernel a x) x)
    (hcenter : ∀ a, gradKernel a center = 0)
    (hbound : ∀ a x, x ∈ Metric.closedBall center r → ∀ v : E,
      inner ℝ (hessKernel a x v) v ≤ -m * ‖v‖ ^ 2)
    (Aop : E → E →L[ℝ] E)
    (hA_C1 : ∀ x ∈ Metric.closedBall center r, ContDiffAt ℝ 1 Aop x)
    (gamma_pos : 0 < gamma)
    (hcoercive : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (Aop x v) v)
    (C : Set E)
    (hCclosureInterior : closure C ⊆ Metric.ball center r)
    (hforwardInvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit t₀ = x → x ∈ C →
      (∀ t ∈ Set.Icc t₀ (t₀ + d), HasDerivAt orbit
        (-(Aop (orbit t) (gradV (orbit t) - (κ * p) •
          finiteReconstructionGradient weight gradKernel (orbit t)))) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ C)
    (hminimizerInC : ∀ x, x ∈ Metric.closedBall center r → IsMinOn
      (fun y => V y - κ * p * finiteReconstructionKernel weight kernel y)
      (Metric.closedBall center r) x → x ∈ C)
    (x₀ : E) (hx₀ : x₀ ∈ C) :
    ∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * finiteReconstructionKernel weight kernel x)
        (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * finiteReconstructionKernel weight kernel y =
          V xstar - κ * p * finiteReconstructionKernel weight kernel xstar →
          y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) ∧
      ∃ trajectory : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
        (∀ t ∈ Set.Ici a, trajectory t ∈ C) ∧
        (∀ t ∈ Set.Ici a,
          0 ≤ (V (trajectory a) - κ * p *
            finiteReconstructionKernel weight kernel (trajectory a)) -
            (V xstar - κ * p * finiteReconstructionKernel weight kernel xstar) ∧
          (V (trajectory t) - κ * p *
            finiteReconstructionKernel weight kernel (trajectory t)) -
            (V xstar - κ * p * finiteReconstructionKernel weight kernel xstar) ≤
            ((V (trajectory a) - κ * p *
              finiteReconstructionKernel weight kernel (trajectory a)) -
              (V xstar - κ * p * finiteReconstructionKernel weight kernel xstar)) *
                Real.exp (-2 * gamma * (κ * p * m - β) * (t - a)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((V (trajectory a) - κ * p *
              finiteReconstructionKernel weight kernel (trajectory a)) -
              (V xstar - κ * p * finiteReconstructionKernel weight kernel xstar)) /
                (κ * p * m - β)) *
                Real.exp (-gamma * (κ * p * m - β) * (t - a))) ∧
        (∀ other : ℝ → E, other a = x₀ →
          (∀ t ∈ Set.Ici a, other t ∈ C) →
          (∀ t ∈ Set.Ioi (a - ε), HasDerivAt other
            (-(Aop (other t) (gradV (other t) - (κ * p) •
              finiteReconstructionGradient weight gradKernel (other t)))) t) →
          ∀ t ∈ Set.Ici a, other t = trajectory t) := by
  obtain ⟨hSc1, hSderiv, hgradSc1, hHS, hcenterS, hSlower⟩ :=
    finite_reconstruction_kernel_conditions (Metric.closedBall center r)
      weight kernel gradKernel hessKernel center m hweight hnorm hkernelC2
      hkernelGrad hgradKernelC1 hgradHess hcenter hbound
  let S : E → ℝ := finiteReconstructionKernel weight kernel
  let gradS : E → E := finiteReconstructionGradient weight gradKernel
  let HS : E → E →L[ℝ] E := finiteReconstructionHessian weight hessKernel
  have hScontDiff : ContDiffOn ℝ 1 S (Metric.closedBall center r) := by
    simpa [S] using hSc1
  have hS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt S (innerSL ℝ (gradS x)) x := by
    intro x hx
    simpa [S, gradS] using hSderiv x hx
  have hHS' : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x := by
    intro x hx
    simpa [gradS, HS] using hHS x hx
  have hgradS_C1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 gradS x := by
    intro x hx
    exact hgradSc1 x hx
  have hcenterS : gradS center = 0 := by
    simpa [gradS] using hcenterS
  have hSlower' : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2 := by
    intro x hx v
    exact hSlower x hx v
  have hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1
        (fun y => -(Aop y (gradV y - (κ * p) • gradS y))) x := by
    intro x hx
    exact ((hA_C1 x hx).clm_apply
      ((hgradV_C1 x hx).sub ((hgradS_C1 x hx).const_smul (κ * p)))).neg
  have hCball : C ⊆ Metric.closedBall center r := by
    intro x hx
    exact Metric.ball_subset_closedBall (hCclosureInterior (subset_closure hx))
  have hclosureBall : closure C ⊆ Metric.closedBall center r :=
    closure_minimal hCball Metric.isClosed_closedBall
  have hclosureCompact : IsCompact (closure C) :=
    (isCompact_closedBall center r).of_isClosed_subset isClosed_closure hclosureBall
  have hclosureNonempty : (closure C).Nonempty := ⟨x₀, subset_closure hx₀⟩
  let field : E → E := fun x => -(Aop x (gradV x - (κ * p) • gradS x))
  have hregularClosure : ∀ x ∈ closure C, ContDiffAt ℝ 1 field x := by
    intro x hx
    exact hfieldC1 x (hclosureBall hx)
  obtain ⟨δ, hδ, hlocalClosure⟩ := exists_uniform_forward_local_trajectory_on_compact
    field (closure C) hclosureCompact hclosureNonempty hregularClosure
  have hlocal : ∀ t₀ : ℝ, ∀ x ∈ C,
      ∃ localOrbit : ℝ → E,
        localOrbit t₀ = x ∧
        ∀ t ∈ Set.Icc t₀ (t₀ + δ),
          HasDerivAt localOrbit
            (-(Aop (localOrbit t) (gradV (localOrbit t) -
              (κ * p) • gradS (localOrbit t)))) t := by
    intro t₀ x hx
    obtain ⟨localOrbit, hinit, hflow⟩ := hlocalClosure t₀ x (subset_closure hx)
    exact ⟨localOrbit, hinit, fun t ht => by simpa [field] using hflow t ht⟩
  obtain ⟨L, hL⟩ := exists_lipschitz_constant_on_closedBall_of_contDiffAt
    field center r hfieldC1
  exact theorem21_state_dependent_mobility_from_threshold_on_invariant_region
    center r κ p m β B gamma a hr hκ hm hβ hB hp V S gradV gradS hessV HS
    hVcontDiff hScontDiff hV hS hHV hHS' hgradV_C1 hgradS_C1 hVlower hSlower'
    hcenterS hVbound Aop hA_C1 gamma_pos hcoercive C hCclosureInterior
    δ hδ hlocal L hL hforwardInvariant hminimizerInC x₀ hx₀

/-- A concrete one-dimensional quadratic instance of Theorem 21. This is a
special case, not the general theorem: the base potential is zero, the biased
potential is `-x²/2`, the mobility is the identity, and the closed-loop ODE is
`x' = -x`. -/
theorem theorem21_quadratic_identity_special_case
    (a x₀ : ℝ) (hx₀ : x₀ ∈ Metric.closedBall (0 : ℝ) 2) :
    ∃ xstar ∈ interior (Metric.closedBall (0 : ℝ) 2),
      IsMinOn (fun x : ℝ => (0 : ℝ) - 1 * (-(x ^ 2) / 2))
        (Metric.closedBall (0 : ℝ) 2) xstar ∧
      ∃ trajectory : ℝ → ℝ, ∃ ε : ℝ, 0 < ε ∧ trajectory a = x₀ ∧
        (∀ t ∈ Set.Ici a, trajectory t ∈ Metric.closedBall (0 : ℝ) 2) ∧
        (∀ t ∈ Set.Ici a,
          0 ≤ (0 - 1 * (-(trajectory a ^ 2) / 2)) -
              (0 - 1 * (-(xstar ^ 2) / 2)) ∧
          (0 - 1 * (-(trajectory t ^ 2) / 2)) -
              (0 - 1 * (-(xstar ^ 2) / 2)) ≤
            ((0 - 1 * (-(trajectory a ^ 2) / 2)) -
              (0 - 1 * (-(xstar ^ 2) / 2))) * Real.exp (-2 * (t - a)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((0 - 1 * (-(trajectory a ^ 2) / 2)) -
              (0 - 1 * (-(xstar ^ 2) / 2)))) * Real.exp (-(t - a))) := by
  let V : ℝ → ℝ := fun _ => 0
  let S : ℝ → ℝ := fun x => -(x ^ 2) / 2
  let gradV : ℝ → ℝ := fun _ => 0
  let gradS : ℝ → ℝ := fun x => -x
  let HV : ℝ → ℝ →L[ℝ] ℝ := fun _ => 0
  let HS : ℝ → ℝ →L[ℝ] ℝ := fun _ => innerSL ℝ (-1 : ℝ)
  have hVcont : ContDiffOn ℝ 1 V (Metric.closedBall (0 : ℝ) 2) := by
    exact contDiffOn_const
  have hScont : ContDiffOn ℝ 1 S (Metric.closedBall (0 : ℝ) 2) := by
    have hpow : ContDiffOn ℝ 1 (fun x : ℝ => x ^ 2) (Metric.closedBall 0 2) :=
      (contDiff_id.pow 2).contDiffOn
    convert ContDiffOn.const_smul (-(1 / 2 : ℝ)) hpow using 1 <;>
      ext x <;> dsimp [S] <;> ring
  have hV : ∀ x ∈ Metric.closedBall (0 : ℝ) 2,
      HasFDerivAt V (innerSL ℝ (gradV x)) x := by
    intro x hx
    simpa [V, gradV, innerSL_apply_apply] using (hasFDerivAt_const (0 : ℝ) x)
  have hS : ∀ x ∈ Metric.closedBall (0 : ℝ) 2,
      HasFDerivAt S (innerSL ℝ (gradS x)) x := by
    intro x hx
    have h : HasDerivAt S (-x) x := by
      have h' := ((hasDerivAt_id x).pow 2).const_mul (-(1 / 2 : ℝ))
      convert h' using 1 <;> simp [S] <;> ring
    convert h.hasFDerivAt using 1 <;>
      ext y <;> simp [gradS, innerSL_apply_apply, smul_eq_mul] <;> ring
  have hHV : ∀ x ∈ Metric.closedBall (0 : ℝ) 2,
      HasFDerivAt gradV (HV x) x := by
    intro x hx
    simpa [gradV, HV] using (hasFDerivAt_const (0 : ℝ) x)
  have hHS : ∀ x ∈ Metric.closedBall (0 : ℝ) 2,
      HasFDerivAt gradS (HS x) x := by
    intro x hx
    have h : HasDerivAt gradS (-1 : ℝ) x := by
      convert (hasDerivAt_id x).neg using 1 <;>
        simp only [gradS, id_eq]
      funext y
      rfl
    convert h.hasFDerivAt using 1
    ext v
    simp [gradS, HS, innerSL_apply_apply]
  have hVlower : ∀ x ∈ Metric.closedBall (0 : ℝ) 2, ∀ v : ℝ,
      -(0 : ℝ) * ‖v‖ ^ 2 ≤ inner ℝ (HV x v) v := by
    intro x hx v
    simp [HV]
  have hSlower : ∀ x ∈ Metric.closedBall (0 : ℝ) 2, ∀ v : ℝ,
      inner ℝ (HS x v) v ≤ -(1 : ℝ) * ‖v‖ ^ 2 := by
    intro x hx v
    norm_num [HS, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg v]
  have hcenter : gradS 0 = 0 := by simp [gradS]
  have hVbound : ∀ x ∈ Metric.closedBall (0 : ℝ) 2, ‖gradV x‖ ≤ 0 := by
    intro x hx
    simp [gradV]
  have hfield : Continuous (fun x : ℝ => -(gradV x - (1 : ℝ) • gradS x)) := by
    simpa [gradV, gradS] using continuous_neg.comp continuous_id
  have hfieldC1 : ∀ x ∈ Metric.closedBall (0 : ℝ) 2,
      ContDiffAt ℝ 1 (fun y : ℝ => -(gradV y - (1 : ℝ) • gradS y)) x := by
    intro x hx
    simpa [gradV, gradS] using (contDiffAt_id.neg : ContDiffAt ℝ 1 (fun y : ℝ => -y) x)
  simpa [V, S] using
    theorem21_identity_mobility_global_exponential_case
      (0 : ℝ) 2 1 1 1 0 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) V S gradV gradS HV HS
      hVcont hScont hV hS hHV hHS hVlower hSlower hcenter hVbound
      (by simpa [one_mul] using hfield)
      (by simpa [one_mul] using hfieldC1) a x₀ hx₀

end Tomabechi.Theorem21
