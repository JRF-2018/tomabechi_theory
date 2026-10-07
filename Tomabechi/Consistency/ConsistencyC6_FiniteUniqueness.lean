import Tomabechi.Consistency.ConsistencyC6_Acceptance

/-!
# C6：原文受入入力から二主体全状態の一意性を導く

半差の一意性だけでなく、平均の保存を競合ODEから導き、二主体状態全体を同定する。
全可測有界ゲイン・全初期状態・全有限前向き区間を保つ。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus
open MeasureTheory

/-- Mの同じC1制御場で動く絶対連続な二主体競合解は、実D軌道に一致する。 -/
theorem OriginalPremises.finite_control_unique {M : ModelSignature}
    (h : OriginalPremises M) (k : ℕ) (u : C1GainSignal) (x : AgentState)
    (a b : ℝ) (hab : a ≤ b) (y : ℝ → AgentState)
    (hyAC : AbsolutelyContinuousOnInterval y a b) (hyInitial : y a = x)
    (hyODE : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      HasDerivAt y (M.c1.selectedFlow.vectorField (y t) (u.1 t) t) t) :
    y b = M.data.trajectory (some k) u x a b := by
  let proj (i : Fin 2) : AgentState →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hac (i : Fin 2) : AbsolutelyContinuousOnInterval (fun t => y t i) a b :=
    (proj i).lipschitz.comp_absolutelyContinuousOnInterval hyAC
  have hode (i : Fin 2) : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      HasDerivAt (fun s => y s i) (M.c1.selectedFlow.vectorField (y t) (u.1 t) t i) t := by
    filter_upwards [hyODE] with t ht
    exact (proj i).hasFDerivAt.comp_hasDerivAt t ht
  have hmAC : AbsolutelyContinuousOnInterval (fun t => meanState (y t)) a b :=
    by simpa [meanState, div_eq_mul_inv, mul_comm] using
      AbsolutelyContinuousOnInterval.const_mul (1 / 2 : ℝ) ((hac 0).add (hac 1))
  have hdAC : AbsolutelyContinuousOnInterval (fun t => halfDifference (y t)) a b :=
    by simpa [halfDifference, div_eq_mul_inv, mul_comm] using
      AbsolutelyContinuousOnInterval.const_mul (1 / 2 : ℝ) ((hac 0).sub (hac 1))
  have hmODE : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      HasDerivAt (fun s => meanState (y s)) 0 t := by
    filter_upwards [hode 0, hode 1] with t h0 h1
    have hh := (h0.add h1).div_const 2
    rw [M.c1.selectedFlow_eq_rate3] at hh
    simpa [meanState, consensusOptimalFlow] using hh
  have hdODE : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      HasDerivAt (fun s => halfDifference (y s)) (-(u.1 t) * halfDifference (y t)) t := by
    filter_upwards [hode 0, hode 1] with t h0 h1
    have hh := (h0.sub h1).div_const 2
    rw [M.c1.selectedFlow_eq_rate3] at hh
    convert hh using 1 <;> simp [halfDifference, consensusOptimalFlow] <;> ring
  have hm : meanState (y b) = meanState x := by
    have hd : (fun t => deriv (fun s => meanState (y s)) t) =ᵐ[
        volume.restrict (Set.uIcc a b)] (fun _ => (0 : ℝ)) := by
      rw [Set.uIcc_of_le hab]
      filter_upwards [hmODE] with t ht
      exact ht.deriv
    have hint := intervalIntegral.integral_congr_ae_restrict
      (ae_restrict_of_ae_restrict_of_subset Set.uIoc_subset_uIcc hd)
    rw [hmAC.integral_deriv_eq_sub] at hint
    simp only [intervalIntegral.integral_zero, hyInitial] at hint
    linarith
  have hd := h.finite_disagreement_unique k u x a b
    (fun t => halfDifference (y t)) hab hdAC (by rw [hyInitial]) hdODE
  have hmD : meanState (M.data.trajectory (some k) u x a b) = meanState x := by
    rw [h.finite_control_solution]
    simp [meanState, controlledConsensusState]
  ext i
  fin_cases i
  · change y b 0 = M.data.trajectory (some k) u x a b 0
    dsimp [meanState, halfDifference] at hm hmD hd
    linarith
  · change y b 1 = M.data.trajectory (some k) u x a b 1
    dsimp [meanState, halfDifference] at hm hmD hd
    linarith

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.OriginalPremises.finite_control_unique
