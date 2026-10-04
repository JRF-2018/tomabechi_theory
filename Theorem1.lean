import Mathlib

/-!
# Theorem 1: quantitative Lyapunov decay

This file proves the scalar Lyapunov comparison step used by Theorem 1.
The first comparison lemmas assume differentiability and the Lyapunov
differential inequality at every time after `t₀`; this is stronger than an
almost-everywhere inequality for an absolutely continuous trajectory, which is
treated later (`lyapunov_exponential_decay_of_ac_ae_derivative` and the
`..._of_ac_ae_derivative` / `theorem1_*` results).  The distance-to-TCZ estimate
is kept as a separate hypothesis (`distance_decay`, `herror`).
-/

namespace Tomabechi.Theorem1

open Filter
open MeasureTheory
open scoped Topology

/-- The zero-residual Lyapunov function used in the paper. -/
def residual1 (V₀ θ : ℝ) : ℝ := max (V₀ - θ) 0

/-- The residual vanishes exactly on the threshold sublevel set. -/
theorem residual1_eq_zero_iff (V₀ θ : ℝ) :
    residual1 V₀ θ = 0 ↔ V₀ ≤ θ := by
  simp [residual1]

/-- Taking the positive part preserves absolute continuity, since `x ↦ max x 0`
is 1-Lipschitz. -/
theorem residual1_preserves_absolute_continuity
    (vAlong : ℝ → ℝ) (θ a b : ℝ)
    (hv : AbsolutelyContinuousOnInterval vAlong a b) :
    AbsolutelyContinuousOnInterval (fun s => residual1 (vAlong s) θ) a b := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => θ) a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hshift : AbsolutelyContinuousOnInterval (fun s => vAlong s - θ) a b :=
    hv.sub hconst
  have hpositivePart : LipschitzWith 1 (fun x : ℝ => max x 0) :=
    LipschitzWith.id.max_const 0
  have hcomp := hpositivePart.comp_absolutelyContinuousOnInterval hshift
  simpa [residual1, Function.comp_def] using hcomp

/-- A quadratic-growth lower bound on the Lyapunov function supplies the
distance-versus-residual error bound required for TCZ convergence. -/
theorem residual1_error_bound_of_quadratic_growth
    {X : Type*} [PseudoMetricSpace X]
    (x : X) (Z : Set X) (V₀ θ μ : ℝ) (hμ : 0 < μ)
    (hgrowth : θ + μ * (Metric.infDist x Z) ^ 2 ≤ V₀) :
    (Metric.infDist x Z) ^ 2 ≤ residual1 V₀ θ / μ := by
  have hdist_nonneg : 0 ≤ (Metric.infDist x Z) ^ 2 := sq_nonneg _
  have hVθ : θ ≤ V₀ := by nlinarith
  have hres : residual1 V₀ θ = V₀ - θ := by
    simp [residual1, max_eq_left (sub_nonneg.mpr hVθ)]
  rw [le_div_iff₀ hμ, hres]
  nlinarith

/-- A right-sided slope formulation of an upper Dini derivative bound.
For every threshold strictly above `bound`, all sufficiently nearby right
slopes lie below that threshold. -/
def RightSlopeBound (f : ℝ → ℝ) (x bound : ℝ) : Prop :=
  ∀ r, bound < r → ∀ᶠ z in 𝓝[>] x,
    (z - x)⁻¹ * (f z - f x) < r

/-- A pointwise derivative upper bound supplies the corresponding upper
right-slope (upper Dini derivative) bound. This is the interface between
classical differentiable vector-field models and the right-slope Lyapunov
comparison theorem. -/
theorem rightSlopeBound_of_hasDerivWithinAt_le
    (f : ℝ → ℝ) (x f' bound : ℝ)
    (hderiv : HasDerivWithinAt f f' (Set.Ici x) x) (hle : f' ≤ bound) :
    RightSlopeBound f x bound := by
  intro r hr
  have hfr : f' < r := lt_of_le_of_lt hle hr
  have hslope : Tendsto (slope f x) (𝓝[>] x) (𝓝 f') := by
    simpa [hasDerivWithinAt_iff_tendsto_slope] using hderiv
  have heventual : ∀ᶠ z in 𝓝[>] x, slope f x z < r :=
    hslope.eventually (Iio_mem_nhds hfr)
  have heventual' : ∀ᶠ z in 𝓝[>] x,
      (z - x)⁻¹ * (f z - f x) < r := by
    filter_upwards [heventual] with z hz
    have heq : (z - x)⁻¹ * (f z - f x) = slope f x z := by
      rw [slope_def_field, div_eq_mul_inv]
      ring
    rw [heq]
    exact hz
  exact heventual'

theorem rightSlopeBound_of_hasDerivAt_le
    (f : ℝ → ℝ) (x f' bound : ℝ)
    (hderiv : HasDerivAt f f' x) (hle : f' ≤ bound) :
    RightSlopeBound f x bound := by
  have hwithin : HasDerivWithinAt f f' (Set.Ici x) x :=
    hderiv.hasDerivWithinAt
  exact rightSlopeBound_of_hasDerivWithinAt_le f x f' bound hwithin hle

/-- Grönwall decay from a right-sided Dini derivative bound. This avoids
assuming that `phi` is differentiable; it requires continuity and the
upper right-slope bound at every point in the time interval. -/
theorem lyapunov_exponential_decay_of_right_slope_bound
    (phi : ℝ → ℝ) (c t₀ t : ℝ)
    (hc : 0 < c) (ht : t₀ ≤ t)
    (hcontinuous : ContinuousOn phi (Set.Icc t₀ t))
    (hRightSlope : ∀ x ∈ Set.Ico t₀ t,
      RightSlopeBound phi x (-2 * c * phi x)) :
    phi t ≤ phi t₀ * Real.exp (-2 * c * (t - t₀)) := by
  have hright : ∀ x ∈ Set.Ico t₀ t, ∀ r,
      (-2 * c * phi x) < r →
      ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (phi z - phi x) < r := by
    intro x hx r hr
    exact (hRightSlope x hx r hr).frequently
  have hbound : ∀ x ∈ Set.Ico t₀ t,
      (-2 * c * phi x) ≤ (-2 * c) * phi x + 0 := by
    intro x hx
    simp
  have hgronwall := le_gronwallBound_of_liminf_deriv_right_le
    (f := phi) (f' := fun x => -2 * c * phi x)
    (δ := phi t₀) (K := -2 * c) (ε := 0) (a := t₀) (b := t)
    hcontinuous hright le_rfl hbound t ⟨ht, le_rfl⟩
  have hK : -2 * c ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hc)
  rw [gronwallBound_of_K_ne_0 hK] at hgronwall
  simpa [mul_assoc] using hgronwall

/-- Lyapunov decay from the paper's regularity pattern: absolute continuity on
the time interval and an almost-everywhere derivative inequality. The proof
uses Mathlib's fundamental theorem of calculus for absolutely continuous
functions, after multiplying the residual by the integrating factor.
-/
theorem lyapunov_exponential_decay_of_ac_ae_derivative
    (phi : ℝ → ℝ) (c t₀ t : ℝ)
    (_hc : 0 < c) (ht : t₀ ≤ t)
    (hphi_ac : AbsolutelyContinuousOnInterval phi t₀ t)
    (hdecay_ae : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      deriv phi s ≤ -2 * c * phi s) :
    phi t ≤ phi t₀ * Real.exp (-2 * c * (t - t₀)) := by
  let expTerm : ℝ → ℝ := fun s => Real.exp (2 * c * (s - t₀))
  let weighted : ℝ → ℝ := fun s => expTerm s * phi s
  have hexp_ac : AbsolutelyContinuousOnInterval expTerm t₀ t := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hweighted_ac : AbsolutelyContinuousOnInterval weighted t₀ t := by
    exact hexp_ac.mul hphi_ac
  have hphi_diff_ae : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      DifferentiableAt ℝ phi s := by
    filter_upwards [ae_restrict_of_ae hphi_ac.ae_differentiableAt,
      ae_restrict_mem measurableSet_Icc] with s hdiff hs
    exact hdiff (Set.Icc_subset_uIcc hs)
  have hexp_deriv (s : ℝ) : deriv expTerm s = 2 * c * expTerm s := by
    have harg : HasDerivAt (fun y : ℝ => 2 * c * (y - t₀)) (2 * c) s := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (hasDerivAt_id s).sub_const t₀ |>.const_mul (2 * c)
    have h := (HasDerivAt.exp harg).deriv
    simpa [expTerm, mul_comm, mul_left_comm, mul_assoc] using h
  have hweighted_deriv_eq : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      deriv weighted s = deriv expTerm s * phi s + expTerm s * deriv phi s := by
    filter_upwards [hphi_diff_ae] with s hdiff
    have h := deriv_fun_mul (by fun_prop : DifferentiableAt ℝ expTerm s) hdiff
    simpa only [weighted] using h
  have hweighted_deriv_nonpos :
      deriv weighted ≤ᵐ[volume.restrict (Set.Icc t₀ t)] 0 := by
    filter_upwards [hweighted_deriv_eq, hdecay_ae] with s heq hdecay
    have hexp_pos : 0 < expTerm s := by positivity
    have hsum : deriv phi s + 2 * c * phi s ≤ 0 := by linarith
    have hfactor :
        2 * c * expTerm s * phi s + expTerm s * deriv phi s =
          expTerm s * (deriv phi s + 2 * c * phi s) := by ring
    calc
      deriv weighted s = deriv expTerm s * phi s + expTerm s * deriv phi s := heq
      _ = expTerm s * (deriv phi s + 2 * c * phi s) := by rw [hexp_deriv]; ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hexp_pos) hsum
  have hintegral := intervalIntegral.integral_mono_ae_restrict ht
    hweighted_ac.intervalIntegrable_deriv (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume t₀ t)
    hweighted_deriv_nonpos
  have hftc := hweighted_ac.integral_deriv_eq_sub
  have hweighted_drop : weighted t ≤ weighted t₀ := by
    have hInt : (∫ s in t₀..t, deriv weighted s) ≤ 0 := by
      simpa using hintegral
    rw [hftc] at hInt
    linarith
  have hweighted_drop' : expTerm t * phi t ≤ phi t₀ := by
    simpa [weighted, expTerm] using hweighted_drop
  have hfactor : expTerm t * Real.exp (-(2 * c * (t - t₀))) = 1 := by
    change Real.exp (2 * c * (t - t₀)) *
      Real.exp (-(2 * c * (t - t₀))) = 1
    rw [← Real.exp_add]
    simp
  calc
    phi t = (expTerm t * phi t) * Real.exp (-2 * c * (t - t₀)) := by
      calc
        phi t = 1 * phi t := by ring
        _ = (expTerm t * Real.exp (-(2 * c * (t - t₀)))) * phi t := by
          rw [hfactor]
        _ = (expTerm t * phi t) * Real.exp (-(2 * c * (t - t₀))) := by ring
        _ = (expTerm t * phi t) * Real.exp (-2 * c * (t - t₀)) := by
          congr 1 <;> ring
    _ ≤ phi t₀ * Real.exp (-2 * c * (t - t₀)) :=
      mul_le_mul_of_nonneg_right hweighted_drop' (Real.exp_nonneg _)

/-- The same scalar comparison proved through Mathlib's Grönwall lemma.
The differentiability hypothesis turns into the required right-slope condition;
the decay-rate constant is allowed to be negative in the Grönwall bound. -/
theorem lyapunov_exponential_decay_by_mathlib_gronwall
    (phi dPhi : ℝ → ℝ) (c t₀ t : ℝ)
    (hc : 0 < c) (ht : t₀ ≤ t)
    (hphi : ∀ s, HasDerivAt phi (dPhi s) s)
    (hdecay : ∀ s ≥ t₀, dPhi s ≤ -2 * c * phi s) :
    phi t ≤ phi t₀ * Real.exp (-2 * c * (t - t₀)) := by
  have hcontinuous : Continuous phi :=
    continuous_iff_continuousAt.mpr fun s => (hphi s).continuousAt
  have hright : ∀ x ∈ Set.Ico t₀ t, ∀ r, dPhi x < r →
      ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (phi z - phi x) < r := by
    intro x hx r hr
    have hwithin : HasDerivWithinAt phi (dPhi x) (Set.Ici x) x :=
      (hphi x).hasDerivWithinAt.mono (by intro y hy; exact Set.mem_univ y)
    have hslope : Tendsto (slope phi x) (𝓝[>] x) (𝓝 (dPhi x)) := by
      simpa [hasDerivWithinAt_iff_tendsto_slope] using hwithin
    have hev : ∀ᶠ z in 𝓝[>] x, slope phi x z < r :=
      hslope.eventually (Iio_mem_nhds hr)
    have hev' : ∀ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (phi z - phi x) < r := by
      filter_upwards [hev] with z hz
      have heq : (z - x)⁻¹ * (phi z - phi x) = slope phi x z := by
        rw [slope_def_field, div_eq_mul_inv]
        ring
      rw [heq]
      exact hz
    exact hev'.frequently
  have hbound : ∀ x ∈ Set.Ico t₀ t, dPhi x ≤ (-2 * c) * phi x + 0 := by
    intro x hx
    simpa using hdecay x hx.1
  have hgronwall := le_gronwallBound_of_liminf_deriv_right_le
    (f := phi) (f' := dPhi) (δ := phi t₀) (K := -2 * c) (ε := 0)
    (a := t₀) (b := t)
    hcontinuous.continuousOn hright le_rfl hbound
    t ⟨ht, le_rfl⟩
  have hK : -2 * c ≠ 0 := by nlinarith
  rw [gronwallBound_of_K_ne_0 hK] at hgronwall
  simpa [mul_assoc] using hgronwall

/-- If the signed excess `V₀ - θ` satisfies a global differential inequality,
then its positive part has the same exponential decay. This avoids assuming a
chain rule for the nonsmooth positive-part function at the threshold. -/
theorem positive_part_exponential_decay_of_derivative
    (vAlong dV : ℝ → ℝ) (θ c t₀ t : ℝ)
    (hc : 0 < c) (ht : t₀ ≤ t)
    (hv : ∀ s, HasDerivAt vAlong (dV s) s)
    (hdecay : ∀ s ≥ t₀, dV s ≤ -2 * c * (vAlong s - θ)) :
    residual1 (vAlong t) θ ≤
      residual1 (vAlong t₀) θ * Real.exp (-2 * c * (t - t₀)) := by
  let excess : ℝ → ℝ := fun s => vAlong s - θ
  have hexcess_deriv : ∀ s, HasDerivAt excess (dV s) s := by
    intro s
    simpa [excess] using (hv s).sub_const θ
  have hexcess_decay : ∀ s ≥ t₀, dV s ≤ -2 * c * excess s := by
    intro s hs
    simpa [excess] using hdecay s hs
  have hcomparison := lyapunov_exponential_decay_by_mathlib_gronwall
    excess dV c t₀ t hc ht hexcess_deriv hexcess_decay
  have hexp_pos : 0 < Real.exp (-2 * c * (t - t₀)) := Real.exp_pos _
  by_cases hinit : excess t₀ ≤ 0
  · have hcurrent : excess t ≤ 0 := by
      have hmul : excess t₀ * Real.exp (-2 * c * (t - t₀)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hinit (le_of_lt hexp_pos)
      linarith
    have hzero0 : residual1 (vAlong t₀) θ = 0 := by
      simp [residual1, excess, max_eq_right hinit]
    have hzero : residual1 (vAlong t) θ = 0 := by
      simp [residual1, excess, max_eq_right hcurrent]
    rw [hzero, hzero0]
    simp
  · have hinit_pos : 0 < excess t₀ := lt_of_not_ge hinit
    have hres0 : residual1 (vAlong t₀) θ = excess t₀ := by
      simp [residual1, excess, max_eq_left (le_of_lt hinit_pos)]
    have hres : residual1 (vAlong t) θ ≤ excess t₀ *
        Real.exp (-2 * c * (t - t₀)) := by
      have hnonneg : 0 ≤ excess t₀ * Real.exp (-2 * c * (t - t₀)) :=
        le_of_lt (mul_pos hinit_pos hexp_pos)
      simp only [residual1, excess]
      exact max_le hcomparison hnonneg
    rw [hres0]
    exact hres

/-- Pointwise Lyapunov decay implies the quantitative exponential estimate.
This is the regular differentiable version of the scalar step behind
Theorem 1's convergence claim. -/
theorem lyapunov_exponential_decay
    (phi dPhi : ℝ → ℝ) (c t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (hphi : ∀ s, HasDerivAt phi (dPhi s) s)
    (hdecay : ∀ s ≥ t₀, dPhi s ≤ -2 * c * phi s) :
    phi t ≤ phi t₀ * Real.exp (-2 * c * (t - t₀)) := by
  let weighted : ℝ → ℝ := fun s => Real.exp (2 * c * (s - t₀)) * phi s
  have hweighted_deriv : ∀ s, HasDerivAt weighted
      (Real.exp (2 * c * (s - t₀)) * dPhi s +
        (2 * c * Real.exp (2 * c * (s - t₀))) * phi s) s := by
    intro s
    have hexp_arg : HasDerivAt (fun y : ℝ => 2 * c * (y - t₀)) (2 * c) s := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (hasDerivAt_id s).sub_const t₀ |>.const_mul (2 * c)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (2 * c * (y - t₀)))
        (Real.exp (2 * c * (s - t₀)) * (2 * c)) s := by
      convert HasDerivAt.exp hexp_arg using 1
    convert hexp.mul (hphi s) using 1 <;> ring
  have hweighted_antitone : AntitoneOn weighted (Set.Ici t₀) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici t₀)
    · intro s hs
      exact (hweighted_deriv s).continuousAt.continuousWithinAt
    · intro s hs
      exact (hweighted_deriv s).hasDerivWithinAt.mono (Set.subset_univ _)
    · intro s hs
      have hs' : t₀ ≤ s := le_of_lt (by simpa using hs)
      have hderiv := hdecay s hs'
      have hexp_pos : 0 < Real.exp (2 * c * (s - t₀)) := Real.exp_pos _
      have hsum : dPhi s + 2 * c * phi s ≤ 0 := by nlinarith
      have hmul := mul_nonpos_of_nonpos_of_nonneg hsum (le_of_lt hexp_pos)
      nlinarith [hmul]
  have hweight_le : weighted t ≤ weighted t₀ := by
    apply hweighted_antitone
    · simp
    · exact ht
    · exact ht
  have hweight_le' :
      Real.exp (2 * c * (t - t₀)) * phi t ≤ phi t₀ := by
    simpa [weighted] using hweight_le
  have hfactor :
      Real.exp (2 * c * (t - t₀)) * Real.exp (-(2 * c * (t - t₀))) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    phi t = (Real.exp (2 * c * (t - t₀)) * phi t) *
        Real.exp (-2 * c * (t - t₀)) := by
          calc
            phi t = 1 * phi t := by ring
            _ = (Real.exp (2 * c * (t - t₀)) *
                Real.exp (-(2 * c * (t - t₀)))) * phi t := by rw [hfactor]
            _ = (Real.exp (2 * c * (t - t₀)) * phi t) *
                Real.exp (-(2 * c * (t - t₀))) := by ring
            _ = (Real.exp (2 * c * (t - t₀)) * phi t) *
                Real.exp (-2 * c * (t - t₀)) := by congr 1 <;> ring
    _ ≤ phi t₀ * Real.exp (-2 * c * (t - t₀)) := by
      exact mul_le_mul_of_nonneg_right hweight_le' (Real.exp_nonneg _)

/-- Convert Lyapunov decay to distance decay under the reverse error bound
`dist(x(t), TCZ(t))² ≤ C * phi(t)`. This is the quantitative form of the
unified convergence lemma, with the constants made explicit. -/
theorem distance_decay
    (phi distToTarget : ℝ → ℝ) (c C t₀ t : ℝ)
    (hc : 0 < c) (hC : 0 < C) (ht : t₀ ≤ t)
    (hphi : ∀ s, HasDerivAt phi (deriv phi s) s)
    (hphi_nonneg : ∀ s ≥ t₀, 0 ≤ phi s)
    (hdecay : ∀ s ≥ t₀, deriv phi s ≤ -2 * c * phi s)
    (hdist_nonneg : ∀ s ≥ t₀, 0 ≤ distToTarget s)
    (herror : ∀ s ≥ t₀, (distToTarget s) ^ 2 ≤ C * phi s) :
    distToTarget t ≤ Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀)) := by
  have hphi_exp := lyapunov_exponential_decay_by_mathlib_gronwall
    phi (deriv phi) c t₀ t hc ht hphi hdecay
  have hdist_sq :
      (distToTarget t) ^ 2 ≤ (Real.sqrt (C * phi t₀) *
        Real.exp (-c * (t - t₀))) ^ 2 := by
    have herr := herror t ht
    have hdec := mul_le_mul_of_nonneg_left hphi_exp (le_of_lt hC)
    have hexp_sq : Real.exp (-c * (t - t₀)) ^ 2 = Real.exp (-2 * c * (t - t₀)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hsqrt := Real.sq_sqrt (mul_nonneg (le_of_lt hC)
      (hphi_nonneg t₀ le_rfl))
    have hexp_nonneg : 0 ≤ Real.exp (-c * (t - t₀)) := Real.exp_nonneg _
    calc
      (distToTarget t) ^ 2 ≤ C * phi t := herr
      _ ≤ C * (phi t₀ * Real.exp (-2 * c * (t - t₀))) := by nlinarith
      _ = (Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀))) ^ 2 := by
        rw [mul_pow, hsqrt, hexp_sq]
        ring
  have hrhs_nonneg :
      0 ≤ Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀)) := by
    positivity
  exact (sq_le_sq₀ (hdist_nonneg t ht) hrhs_nonneg).mp hdist_sq

/-- Pointwise, quantitative convergence of a closed-loop trajectory to a
time-varying TCZ, assuming the residual decay and distance comparison from
Theorem 1.  The target nonemptiness condition rules out vacuous distance-to-
empty-set cases.  This version assumes differentiability and decay at every
time; the paper's a.e. absolutely-continuous formulation is proved in
`individual_tcz_distance_decay_of_ac_ae_derivative`.
-/
theorem individual_tcz_distance_exponential_decay
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (TCZ : ℝ → Set X) (phi : ℝ → ℝ)
    (c C t₀ t : ℝ)
    (hc : 0 < c) (hC : 0 < C) (ht : t₀ ≤ t)
    (_hTCZ_nonempty : ∀ s ≥ t₀, (TCZ s).Nonempty)
    (hphi : ∀ s, HasDerivAt phi (deriv phi s) s)
    (hphi_nonneg : ∀ s ≥ t₀, 0 ≤ phi s)
    (hdecay : ∀ s ≥ t₀, deriv phi s ≤ -2 * c * phi s)
    (herror : ∀ s ≥ t₀,
      (Metric.infDist (trajectory s) (TCZ s)) ^ 2 ≤ C * phi s) :
    Metric.infDist (trajectory t) (TCZ t) ≤
      Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀)) := by
  exact distance_decay phi (fun s => Metric.infDist (trajectory s) (TCZ s))
    c C t₀ t hc hC ht hphi hphi_nonneg hdecay
    (fun s hs => Metric.infDist_nonneg) herror

/-- TCZ-distance estimate using the right-slope Lyapunov condition instead of
pointwise differentiability. The Dini bound is assumed at every time in the
interval; the almost-everywhere absolutely-continuous version from the paper is
`individual_tcz_distance_decay_of_ac_ae_derivative`. -/
theorem individual_tcz_distance_decay_of_right_slope_bound
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (TCZ : ℝ → Set X) (phi : ℝ → ℝ)
    (c C t₀ t : ℝ)
    (hc : 0 < c) (hC : 0 < C) (ht : t₀ ≤ t)
    (_hTCZ_nonempty : ∀ s ≥ t₀, (TCZ s).Nonempty)
    (hcontinuous : ContinuousOn phi (Set.Icc t₀ t))
    (hphi_nonneg : ∀ s ≥ t₀, 0 ≤ phi s)
    (hRightSlope : ∀ x ∈ Set.Ico t₀ t,
      RightSlopeBound phi x (-2 * c * phi x))
    (herror : ∀ s ∈ Set.Icc t₀ t,
      (Metric.infDist (trajectory s) (TCZ s)) ^ 2 ≤ C * phi s) :
    Metric.infDist (trajectory t) (TCZ t) ≤
      Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀)) := by
  have hphi_exp := lyapunov_exponential_decay_of_right_slope_bound
    phi c t₀ t hc ht hcontinuous hRightSlope
  have hdist_sq :
      (Metric.infDist (trajectory t) (TCZ t)) ^ 2 ≤
        (Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀))) ^ 2 := by
    have herr := herror t ⟨ht, le_rfl⟩
    have hdec := mul_le_mul_of_nonneg_left hphi_exp (le_of_lt hC)
    have hexp_sq : Real.exp (-c * (t - t₀)) ^ 2 = Real.exp (-2 * c * (t - t₀)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hsqrt := Real.sq_sqrt (mul_nonneg (le_of_lt hC)
      (hphi_nonneg t₀ le_rfl))
    calc
      (Metric.infDist (trajectory t) (TCZ t)) ^ 2 ≤ C * phi t := herr
      _ ≤ C * (phi t₀ * Real.exp (-2 * c * (t - t₀))) := by nlinarith
      _ = (Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀))) ^ 2 := by
        rw [mul_pow, hsqrt, hexp_sq]
        ring
  have hrhs_nonneg :
      0 ≤ Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀)) := by
    positivity
  exact (sq_le_sq₀ Metric.infDist_nonneg hrhs_nonneg).mp hdist_sq

/-- The quantitative individual-TCZ convergence conclusion under the
absolutely-continuous, almost-everywhere derivative assumptions. This matches
the regularity pattern of the paper's unified Lyapunov convergence lemma for
real-valued residuals along one trajectory. -/
theorem individual_tcz_distance_decay_of_ac_ae_derivative
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (TCZ : ℝ → Set X) (phi : ℝ → ℝ)
    (c C t₀ t : ℝ)
    (hc : 0 < c) (hC : 0 < C) (ht : t₀ ≤ t)
    (_hTCZ_nonempty : ∀ s ∈ Set.Icc t₀ t, (TCZ s).Nonempty)
    (hphi_ac : AbsolutelyContinuousOnInterval phi t₀ t)
    (hphi_nonneg : ∀ s ∈ Set.Icc t₀ t, 0 ≤ phi s)
    (hdecay_ae : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      deriv phi s ≤ -2 * c * phi s)
    (herror : ∀ s ∈ Set.Icc t₀ t,
      (Metric.infDist (trajectory s) (TCZ s)) ^ 2 ≤ C * phi s) :
    Metric.infDist (trajectory t) (TCZ t) ≤
      Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀)) := by
  have hphi_exp := lyapunov_exponential_decay_of_ac_ae_derivative
    phi c t₀ t hc ht hphi_ac hdecay_ae
  have hdist_sq :
      (Metric.infDist (trajectory t) (TCZ t)) ^ 2 ≤
        (Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀))) ^ 2 := by
    have herr := herror t ⟨ht, le_rfl⟩
    have hdec := mul_le_mul_of_nonneg_left hphi_exp (le_of_lt hC)
    have hexp_sq : Real.exp (-c * (t - t₀)) ^ 2 = Real.exp (-2 * c * (t - t₀)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hsqrt := Real.sq_sqrt (mul_nonneg (le_of_lt hC)
      (hphi_nonneg t₀ ⟨le_rfl, ht⟩))
    calc
      (Metric.infDist (trajectory t) (TCZ t)) ^ 2 ≤ C * phi t := herr
      _ ≤ C * (phi t₀ * Real.exp (-2 * c * (t - t₀))) := by nlinarith
      _ = (Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀))) ^ 2 := by
        rw [mul_pow, hsqrt, hexp_sq]
        ring
  have hrhs_nonneg :
      0 ≤ Real.sqrt (C * phi t₀) * Real.exp (-c * (t - t₀)) := by
    positivity
  exact (sq_le_sq₀ Metric.infDist_nonneg hrhs_nonneg).mp hdist_sq

/-- A nonnegative distance bounded by a decaying exponential on a tail tends
to zero. This analytic wrapper is shared by the theorem-specific TCZ results. -/
theorem tendsto_zero_of_exponential_majorant
    (distance : ℝ → ℝ) (A rate t₀ : ℝ)
    (hbound : ∀ t, t₀ ≤ t → distance t ≤ A * Real.exp (-rate * (t - t₀)))
    (hnonneg : ∀ t, 0 ≤ distance t) (hrate : 0 < rate) :
    Tendsto distance atTop (𝓝 0) := by
  have hmul : Tendsto (fun t : ℝ => -rate * t) atTop atBot := by
    apply (Filter.tendsto_const_mul_atBot_of_neg (l := atTop)
      (f := id) (r := -rate) (by linarith)).2
    exact Filter.tendsto_id
  have harg : Tendsto (fun t : ℝ => -rate * (t - t₀)) atTop atBot := by
    have hshift := Filter.tendsto_atBot_add_const_right atTop (rate * t₀) hmul
    convert hshift using 1 <;> ext t <;> ring
  have hexp : Tendsto (fun t : ℝ => Real.exp (-rate * (t - t₀))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hmajor : Tendsto (fun t : ℝ => A * Real.exp (-rate * (t - t₀)))
      atTop (𝓝 0) := by simpa using hexp.const_mul A
  apply squeeze_zero' (Filter.Eventually.of_forall hnonneg) ?_ hmajor
  filter_upwards [Filter.eventually_atTop.2 ⟨t₀, fun t ht => hbound t ht⟩]
  exact fun t ht => ht

/-- Fixed-policy reachable states from the initial condition, over all finite
nonnegative horizons, followed by closure. `reachableAt` must be generated by
the selected closed-loop policy; this definition does not derive reachability
from optimality. -/
def closedLoopReachableSet {X : Type*} [TopologicalSpace X]
    (reachableAt : ℝ → Set X) : Set X :=
  closure {x | ∃ τ, 0 ≤ τ ∧ x ∈ reachableAt τ}

/-- H-flow data for one selected feedback policy. The structure records the
policy, its global forward trajectory map, initial values, and the restart
law. It does not impose differentiability; this lets reachability arguments
state only the trajectory and restart data they use. -/
structure ClosedLoopPolicyFlow (E U : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  admissible : U → Prop
  feedback : E → ℝ → U
  vectorField : E → U → ℝ → E
  flow : ℝ → E → ℝ → E
  feedback_admissible : ∀ x t, admissible (feedback x t)
  initial : ∀ t₀ x, flow t₀ x t₀ = x
  restart : ∀ t₀ x s t, t₀ ≤ s → s ≤ t →
    flow t₀ x t = flow s (flow t₀ x s) t

/-- A classically differentiable H-flow. `solves` is a strong added regularity
condition: for every real start time `t₀`, every ambient state `x : E`, and
every `t ≥ t₀`, the globally defined trajectory map has an ordinary two-sided
derivative at `t`, including at its initial time. This is stronger than the
usual forward Carathéodory condition (absolute continuity and an a.e. ODE),
and is not derived from Borel feedback or restart. It is used by the Theorem 20
adapter; Theorems 1–4 need only `ClosedLoopPolicyFlow`. -/
structure DifferentiableClosedLoopPolicyFlow (E U : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    extends ClosedLoopPolicyFlow E U where
  solves : ∀ t₀ x t, t₀ ≤ t →
    HasDerivAt (fun s => flow t₀ x s)
      (vectorField (flow t₀ x t) (feedback (flow t₀ x t) t) t) t

/-- States reachable at absolute time `t` from the given initial set at start
time `t₀`, generated by the selected policy's closed-loop solutions. -/
def policyFlowReachableAt {E U : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ClosedLoopPolicyFlow E U) (initialSet : Set E)
    (t₀ t : ℝ) : Set E :=
  {y | t₀ ≤ t ∧ ∃ x ∈ initialSet, y = F.flow t₀ x t}

/-- The flow trajectory from an allowed initial state belongs to the generated
policy reachable set at every nonnegative elapsed time. -/
theorem mem_policyFlowReachableAt_of_flow
    {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ClosedLoopPolicyFlow E U) (initialSet : Set E)
    (t₀ t : ℝ) (x₀ : E) (hx₀ : x₀ ∈ initialSet) (ht : t₀ ≤ t) :
    F.flow t₀ x₀ t ∈ policyFlowReachableAt F initialSet t₀ t := by
  exact ⟨ht, x₀, hx₀, rfl⟩

/-- Restarting from any state reached by the same selected policy produces a
state in the generated reachable set at the summed elapsed time. -/
theorem policyFlowReachableAt_closed_under_restart
    {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ClosedLoopPolicyFlow E U) (initialSet : Set E)
    (t₀ s t : ℝ) (ht₀s : t₀ ≤ s) (hst : s ≤ t)
    {y : E} (hy : y ∈ policyFlowReachableAt F initialSet t₀ s) :
    F.flow s y t ∈ policyFlowReachableAt F initialSet t₀ t := by
  rcases hy with ⟨_, x₀, hx₀, rfl⟩
  refine ⟨le_trans ht₀s hst, x₀, hx₀, ?_⟩
  rw [← F.restart t₀ x₀ s t ht₀s hst]

/-- Every state reached at a nonnegative time belongs to the closed-loop
reachable closure used in the paper's closed-reachable TCZ. -/
theorem mem_closedLoopReachableSet_of_mem_reachableAt
    {X : Type*} [TopologicalSpace X] (reachableAt : ℝ → Set X)
    {τ : ℝ} {x : X}
    (hτ : 0 ≤ τ) (hx : x ∈ reachableAt τ) :
    x ∈ closedLoopReachableSet reachableAt := by
  apply subset_closure
  exact ⟨τ, hτ, hx⟩

/-- Paper-shaped conditional form of Theorem 1. Here `K` is the closed-loop
reachable set, `TCZ t = K ∩ {x | V₀(x,t) ≤ θ}`, and `phi` is exactly the
positive-part residual `[V₀ - θ]₊` along the trajectory. The analytic
assumptions are the descent and error-bound hypotheses in the paper's
unified convergence lemma; optimality of a finite-horizon controller alone
does not establish them.
-/
theorem theorem1_closed_loop_tcz_exponential_decay
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (K : Set X) (V₀ : X → ℝ → ℝ)
    (θ c C t₀ t : ℝ)
    (hTCZ_nonempty : ∀ s ∈ Set.Icc t₀ t,
      {x : X | x ∈ K ∧ V₀ x s ≤ θ}.Nonempty)
    (hresidual_ac : AbsolutelyContinuousOnInterval
      (fun s => residual1 (V₀ (trajectory s) s) θ) t₀ t)
    (hdecay_ae : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      deriv (fun r => residual1 (V₀ (trajectory r) r) θ) s ≤
        -2 * c * residual1 (V₀ (trajectory s) s) θ)
    (herror : ∀ s ∈ Set.Icc t₀ t,
      (Metric.infDist (trajectory s)
        {x : X | x ∈ K ∧ V₀ x s ≤ θ}) ^ 2 ≤
          C * residual1 (V₀ (trajectory s) s) θ)
    (hc : 0 < c) (hC : 0 < C) (ht : t₀ ≤ t) :
    Metric.infDist (trajectory t)
      {x : X | x ∈ K ∧ V₀ x t ≤ θ} ≤
        Real.sqrt (C * residual1 (V₀ (trajectory t₀) t₀) θ) *
          Real.exp (-c * (t - t₀)) := by
  exact individual_tcz_distance_decay_of_ac_ae_derivative trajectory
    (fun s => {x : X | x ∈ K ∧ V₀ x s ≤ θ})
    (fun s => residual1 (V₀ (trajectory s) s) θ)
    c C t₀ t hc hC ht hTCZ_nonempty hresidual_ac
    (fun s hs => le_max_right (V₀ (trajectory s) s - θ) 0)
    hdecay_ae herror

/-- 各有限終端時刻で定理1の残差AC・a.e.散逸・距離誤差を仮定すると、閉ループTCZへの
指数距離評価が全未来時刻で成り立ち、距離はゼロへ収束する。入力は基礎ポテンシャル
そのもののACでなく、原文どおり正部分残差のAC。 -/
theorem theorem1_closed_loop_tcz_distance_tendsto_zero
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (K : Set X) (V₀ : X → ℝ → ℝ)
    (θ c C t₀ : ℝ)
    (hTCZ_nonempty : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      {x : X | x ∈ K ∧ V₀ x s ≤ θ}.Nonempty)
    (hresidual_ac : ∀ T, t₀ ≤ T →
      AbsolutelyContinuousOnInterval
        (fun s => residual1 (V₀ (trajectory s) s) θ) t₀ T)
    (hdecay_ae : ∀ T, t₀ ≤ T →
      ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
        deriv (fun r => residual1 (V₀ (trajectory r) r) θ) s ≤
          -2 * c * residual1 (V₀ (trajectory s) s) θ)
    (herror : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (Metric.infDist (trajectory s)
        {x : X | x ∈ K ∧ V₀ x s ≤ θ}) ^ 2 ≤
          C * residual1 (V₀ (trajectory s) s) θ)
    (hc : 0 < c) (hC : 0 < C) :
    Filter.Tendsto (fun t => Metric.infDist (trajectory t)
      {x : X | x ∈ K ∧ V₀ x t ≤ θ}) atTop (𝓝 0) := by
  let distance : ℝ → ℝ := fun t => Metric.infDist (trajectory t)
    {x : X | x ∈ K ∧ V₀ x t ≤ θ}
  have hbound : ∀ T, t₀ ≤ T →
      distance T ≤ Real.sqrt (C * residual1 (V₀ (trajectory t₀) t₀) θ) *
        Real.exp (-c * (T - t₀)) := by
    intro T hT
    exact theorem1_closed_loop_tcz_exponential_decay trajectory K V₀ θ c C
      t₀ T (hTCZ_nonempty T hT) (hresidual_ac T hT) (hdecay_ae T hT)
      (herror T hT) hc hC hT
  exact tendsto_zero_of_exponential_majorant distance
    (Real.sqrt (C * residual1 (V₀ (trajectory t₀) t₀) θ)) c t₀
    hbound (fun t => Metric.infDist_nonneg) hc

/-- Theorem 1 with its target set built from the selected policy's reachable
sets. 非空条件は閉到達集合内のTCZに課し、有限時間での閾値到達を要求しない。
Reachability of the closed-loop trajectory and nonempty target slices
are supplied from the policy dynamics; the residual descent and error bound
remain independent hypotheses, as in the source's unified Lyapunov lemma. -/
theorem theorem1_reachable_tcz_distance_tendsto_zero
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (reachableAt : ℝ → Set X)
    (V₀ : X → ℝ → ℝ) (θ c C t₀ : ℝ)
    (htrajectory_reachable : ∀ t, t₀ ≤ t → trajectory t ∈ reachableAt t)
    (hreachable_tcz_nonempty : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      {y | y ∈ closedLoopReachableSet reachableAt ∧ V₀ y s ≤ θ}.Nonempty)
    (hresidual_ac : ∀ T, t₀ ≤ T →
      AbsolutelyContinuousOnInterval
        (fun s => residual1 (V₀ (trajectory s) s) θ) t₀ T)
    (hdecay_ae : ∀ T, t₀ ≤ T →
      ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
        deriv (fun r => residual1 (V₀ (trajectory r) r) θ) s ≤
          -2 * c * residual1 (V₀ (trajectory s) s) θ)
    (herror : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (Metric.infDist (trajectory s)
        {x | x ∈ closedLoopReachableSet reachableAt ∧ V₀ x s ≤ θ}) ^ 2 ≤
          C * residual1 (V₀ (trajectory s) s) θ)
    (ht₀ : 0 ≤ t₀) (hc : 0 < c) (hC : 0 < C) :
    (∀ t, t₀ ≤ t → trajectory t ∈ closedLoopReachableSet reachableAt) ∧
      (∀ t, t₀ ≤ t → Metric.infDist (trajectory t)
        {x | x ∈ closedLoopReachableSet reachableAt ∧ V₀ x t ≤ θ} ≤
          Real.sqrt (C * residual1 (V₀ (trajectory t₀) t₀) θ) *
            Real.exp (-c * (t - t₀))) ∧
      Filter.Tendsto (fun t => Metric.infDist (trajectory t)
        {x | x ∈ closedLoopReachableSet reachableAt ∧ V₀ x t ≤ θ})
        atTop (𝓝 0) := by
  have hquantitative : ∀ t, t₀ ≤ t →
      Metric.infDist (trajectory t)
        {x | x ∈ closedLoopReachableSet reachableAt ∧ V₀ x t ≤ θ} ≤
          Real.sqrt (C * residual1 (V₀ (trajectory t₀) t₀) θ) *
            Real.exp (-c * (t - t₀)) := by
    intro t ht
    exact theorem1_closed_loop_tcz_exponential_decay trajectory
      (closedLoopReachableSet reachableAt) V₀ θ c C t₀ t
      (hreachable_tcz_nonempty t ht) (hresidual_ac t ht) (hdecay_ae t ht)
      (herror t ht) hc hC ht
  have hlimit := tendsto_zero_of_exponential_majorant
    (fun t => Metric.infDist (trajectory t)
      {x | x ∈ closedLoopReachableSet reachableAt ∧ V₀ x t ≤ θ})
    (Real.sqrt (C * residual1 (V₀ (trajectory t₀) t₀) θ)) c t₀
    hquantitative (fun t => Metric.infDist_nonneg) hc
  constructor
  · intro t ht
    exact mem_closedLoopReachableSet_of_mem_reachableAt reachableAt
      (le_trans ht₀ ht) (htrajectory_reachable t ht)
  · exact ⟨hquantitative, hlimit⟩

/-- A useful sufficient-condition version of Theorem 1: the error bound is
derived from quadratic growth of `V₀` away from the time-varying TCZ. -/
theorem theorem1_closed_loop_tcz_exponential_decay_of_quadratic_growth
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (K : Set X) (V₀ : X → ℝ → ℝ)
    (θ μ c t₀ t : ℝ)
    (hTCZ_nonempty : ∀ s ∈ Set.Icc t₀ t,
      {x : X | x ∈ K ∧ V₀ x s ≤ θ}.Nonempty)
    (hresidual_ac : AbsolutelyContinuousOnInterval
      (fun s => residual1 (V₀ (trajectory s) s) θ) t₀ t)
    (hdecay_ae : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      deriv (fun r => residual1 (V₀ (trajectory r) r) θ) s ≤
        -2 * c * residual1 (V₀ (trajectory s) s) θ)
    (hgrowth : ∀ s ∈ Set.Icc t₀ t,
      θ + μ * (Metric.infDist (trajectory s)
        {x : X | x ∈ K ∧ V₀ x s ≤ θ}) ^ 2 ≤ V₀ (trajectory s) s)
    (hc : 0 < c) (hμ : 0 < μ) (ht : t₀ ≤ t) :
    Metric.infDist (trajectory t)
      {x : X | x ∈ K ∧ V₀ x t ≤ θ} ≤
        Real.sqrt (residual1 (V₀ (trajectory t₀) t₀) θ / μ) *
          Real.exp (-c * (t - t₀)) := by
  have hcore := theorem1_closed_loop_tcz_exponential_decay
    trajectory K V₀ θ c (1 / μ) t₀ t hTCZ_nonempty hresidual_ac hdecay_ae
    (fun s hs => by
      have hbound := residual1_error_bound_of_quadratic_growth
        (trajectory s) {x : X | x ∈ K ∧ V₀ x s ≤ θ}
        (V₀ (trajectory s) s) θ μ hμ (hgrowth s hs)
      simpa [div_eq_mul_inv, mul_comm] using hbound)
    hc (div_pos one_pos hμ) ht
  convert hcore using 1
  congr 2
  ring

/-- Combined differentiable sufficient-condition form: a differential
inequality for the signed excess `V₀ - θ`, together with quadratic growth
toward the TCZ, gives the explicit exponential distance estimate directly. -/
theorem theorem1_closed_loop_tcz_decay_from_v_derivative_and_quadratic_growth
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (K : Set X) (V₀ : X → ℝ → ℝ)
    (θ μ c t₀ t : ℝ)
    (_hTCZ_nonempty : ∀ s ∈ Set.Icc t₀ t,
      {x : X | x ∈ K ∧ V₀ x s ≤ θ}.Nonempty)
    (dV : ℝ → ℝ)
    (hV₀_deriv : ∀ s, HasDerivAt (fun r => V₀ (trajectory r) r) (dV s) s)
    (hV₀_decay : ∀ s ≥ t₀,
      dV s ≤ -2 * c * (V₀ (trajectory s) s - θ))
    (hgrowth : ∀ s ∈ Set.Icc t₀ t,
      θ + μ * (Metric.infDist (trajectory s)
        {x : X | x ∈ K ∧ V₀ x s ≤ θ}) ^ 2 ≤ V₀ (trajectory s) s)
    (hc : 0 < c) (hμ : 0 < μ) (ht : t₀ ≤ t) :
    Metric.infDist (trajectory t)
      {x : X | x ∈ K ∧ V₀ x t ≤ θ} ≤
        Real.sqrt (residual1 (V₀ (trajectory t₀) t₀) θ / μ) *
          Real.exp (-c * (t - t₀)) := by
  let vAlong : ℝ → ℝ := fun s => V₀ (trajectory s) s
  let target : Set X := {x : X | x ∈ K ∧ V₀ x t ≤ θ}
  have hresidual := positive_part_exponential_decay_of_derivative
    vAlong dV θ c t₀ t hc ht hV₀_deriv hV₀_decay
  have herror := residual1_error_bound_of_quadratic_growth
    (trajectory t) target (vAlong t) θ μ hμ (by
      simpa [target, vAlong] using hgrowth t ⟨ht, le_rfl⟩)
  have hdistance_sq :
      (Metric.infDist (trajectory t) target) ^ 2 ≤
        (Real.sqrt (residual1 (vAlong t₀) θ / μ) *
          Real.exp (-c * (t - t₀))) ^ 2 := by
    have hresidual_nonneg : 0 ≤ residual1 (vAlong t₀) θ :=
      le_max_right _ _
    have hexp_sq : Real.exp (-c * (t - t₀)) ^ 2 =
        Real.exp (-2 * c * (t - t₀)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hsqrt := Real.sq_sqrt (div_nonneg hresidual_nonneg (le_of_lt hμ))
    calc
      (Metric.infDist (trajectory t) target) ^ 2 ≤
          residual1 (vAlong t) θ / μ := herror
      _ ≤ (residual1 (vAlong t₀) θ *
          Real.exp (-2 * c * (t - t₀))) / μ :=
        div_le_div_of_nonneg_right hresidual (le_of_lt hμ)
      _ = (Real.sqrt (residual1 (vAlong t₀) θ / μ) *
          Real.exp (-c * (t - t₀))) ^ 2 := by
        rw [mul_pow, hsqrt, hexp_sq]
        ring
  have hrhs_nonneg : 0 ≤ Real.sqrt (residual1 (vAlong t₀) θ / μ) *
      Real.exp (-c * (t - t₀)) := by positivity
  have hdist_nonneg : 0 ≤ Metric.infDist (trajectory t) target :=
    Metric.infDist_nonneg
  have hresult := (sq_le_sq₀ hdist_nonneg hrhs_nonneg).mp hdistance_sq
  simpa [vAlong, target] using hresult

end Tomabechi.Theorem1

#print axioms Tomabechi.Theorem1.theorem1_closed_loop_tcz_exponential_decay
#print axioms Tomabechi.Theorem1.theorem1_closed_loop_tcz_distance_tendsto_zero
#print axioms Tomabechi.Theorem1.theorem1_reachable_tcz_distance_tendsto_zero
