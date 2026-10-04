import theorem1_example
import Theorem1

open Real

/-!
# Theorem 1 applied to the one-dimensional example

This file keeps the example's full `theta ≥ 0` conclusion. It applies the
general Theorem 1 result first to the zero-threshold set `{0}`, then uses
`{0} ⊆ TCZ theta`. The comparison is valid because the example's TCZ always
contains zero. This is still the one-dimensional linear example, not a proof
that finite-horizon optimality implies Theorem 1's descent hypotheses.
-/

theorem convergence_to_TCZ_via_Theorem1
    (x0 lam theta : ℝ)
    (hlam : 0 < lam)
    (htheta : 0 ≤ theta) :
    ExponentiallyConvergesToTCZ (x_traj x0 lam) (TCZ theta) lam := by
  constructor
  · exact hlam
  · refine ⟨|x0| + 1, add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one, ?_⟩
    intro t ht
    let trajectory : ℝ → ℝ := x_traj x0 lam
    let zeroTCZ : Set ℝ := {x | x ∈ Set.univ ∧ V x ≤ 0}
    have hzero_mem : (0 : ℝ) ∈ zeroTCZ := by
      simp [zeroTCZ, V]
    have hzero_nonempty : ∀ s ∈ Set.Icc 0 t, zeroTCZ.Nonempty := by
      intro s hs
      exact ⟨0, hzero_mem⟩
    let dV : ℝ → ℝ := fun s => -lam * (trajectory s) ^ 2
    have hVderiv : ∀ s, HasDerivAt
        (fun r => V (trajectory r)) (dV s) s := by
      intro s
      have hx := x_traj_is_sol x0 lam s
      have hsq : HasDerivAt (fun r => (trajectory r) ^ 2)
          (2 * trajectory s * pi_c lam (trajectory s)) s := by
        convert hx.pow 2 using 1 <;> dsimp [trajectory] <;> ring
      unfold V
      convert hsq.const_mul 0.5 using 1 <;> dsimp [dV, pi_c] <;> ring
    have hVdecay : ∀ s ≥ 0,
        dV s ≤ -2 * lam * (V (trajectory s) - 0) := by
      intro s hs
      dsimp [dV, V]
      nlinarith
    have hgrowth : ∀ s ∈ Set.Icc 0 t,
        (0 : ℝ) + (1 / 2 : ℝ) *
            (Metric.infDist (trajectory s) zeroTCZ) ^ 2 ≤
          V (trajectory s) := by
      intro s hs
      have hdist := Metric.infDist_le_dist_of_mem
        (x := trajectory s) (y := 0) hzero_mem
      rw [Real.dist_eq, sub_zero] at hdist
      have hdist_nonneg := Metric.infDist_nonneg (x := trajectory s) (s := zeroTCZ)
      dsimp [V]
      nlinarith [sq_abs (trajectory s)]
    have hzero_bound :=
      Tomabechi.Theorem1.theorem1_closed_loop_tcz_decay_from_v_derivative_and_quadratic_growth
        trajectory Set.univ (fun x _ => V x) 0 (1 / 2) lam 0 t
        hzero_nonempty dV hVderiv hVdecay hgrowth hlam (by norm_num) ht
    have hsubset : zeroTCZ ⊆ TCZ theta := by
      intro x hx
      change V x ≤ theta
      have hxV : V x ≤ 0 := hx.2
      linarith
    have hdist_subset : Metric.infDist (trajectory t) (TCZ theta) ≤
        Metric.infDist (trajectory t) zeroTCZ :=
      Metric.infDist_le_infDist_of_subset hsubset ⟨0, hzero_mem⟩
    have hArg :
        Tomabechi.Theorem1.residual1 (V x0) 0 * 2 = x0 ^ 2 := by
      simp [Tomabechi.Theorem1.residual1, V,
        max_eq_left (show 0 ≤ (0.5 : ℝ) * x0 ^ 2 by positivity)]
      ring
    have hsqrt : Real.sqrt
        (Tomabechi.Theorem1.residual1 (V x0) 0) * Real.sqrt 2 = |x0| := by
      simp only [Tomabechi.Theorem1.residual1]
      rw [← Real.sqrt_mul (le_max_right _ _) 2]
      have hArg' : max (V x0 - 0) 0 * 2 = x0 ^ 2 := by
        simpa [Tomabechi.Theorem1.residual1] using hArg
      rw [hArg', Real.sqrt_sq_eq_abs]
    have hzero_bound' :
        Metric.infDist (trajectory t) zeroTCZ ≤
          |x0| * Real.exp (-(lam * t)) := by
      simpa [trajectory, zeroTCZ, x_traj_init, hsqrt, sub_zero] using hzero_bound
    have hconstant : |x0| * Real.exp (-(lam * t)) ≤
        (|x0| + 1) * Real.exp (-(lam * t)) := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · positivity
    exact hdist_subset.trans (hzero_bound'.trans hconstant)
