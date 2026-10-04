import Theorem24_26_Model

/-!
# A parameterized family of scalar models for Theorem 24 → 26

For positive decay rate `lam`, discount rate `ρ`, and cost coefficient `q`,
the scalar system `x' = -lam x` with running cost `q x²` has discounted
value `q/(ρ + 2lam) * x²`. Its zero-value target is `{0}`, and `W(x)=x²`
verifies the Lyapunov and value-distance clauses of condition 26-A with decay
rate `2lam`.
This generalizes the fixed-rate examples, while remaining a one-dimensional
linear special case rather than a construction of the paper's general model.
-/

namespace Tomabechi.Theorem24_26_LinearFamily

open MeasureTheory Set
open Tomabechi.Theorem24_26
open Tomabechi.Theorem24_26_Model

/-- Closed-loop solution of `x' = -lamx` starting from `x` at time `T`. -/
noncomputable def flow (lam x T s : ℝ) : ℝ := x * Real.exp (-lam * (s - T))

/-- The running cost scale makes the discounted infinite-horizon value equal
to the squared distance from the equilibrium. -/
def runningCost (_lam _ρ q x _s : ℝ) : ℝ := q * x ^ 2

noncomputable def discountedIntegrand (lam ρ q x T s : ℝ) : ℝ :=
  theorem26DiscountWeight ρ T s * runningCost lam ρ q (flow lam x T s) s

noncomputable def value (lam ρ q x T : ℝ) : ℝ :=
  ∫ s, discountedIntegrand lam ρ q x T s ∂futureLebesgueMeasure T

theorem discountedIntegrand_eq (lam ρ q x T s : ℝ) :
    discountedIntegrand lam ρ q x T s = q * x ^ 2 *
      Real.exp (-(ρ + 2 * lam) * (s - T)) := by
  rw [discountedIntegrand, theorem26DiscountWeight, runningCost, flow]
  calc
    Real.exp (-ρ * (s - T)) *
        (q * (x * Real.exp (-lam * (s - T))) ^ 2) =
        q * x ^ 2 *
          (Real.exp (-ρ * (s - T)) * Real.exp (-lam * (s - T)) *
            Real.exp (-lam * (s - T))) := by ring
    _ = q * x ^ 2 *
        Real.exp ((-ρ * (s - T) + -lam * (s - T)) + -lam * (s - T)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ = q * x ^ 2 *
        Real.exp (-(ρ + 2 * lam) * (s - T)) := by
      rw [show (-ρ * (s - T) + -lam * (s - T)) + -lam * (s - T) =
        -(ρ + 2 * lam) * (s - T) by ring]

theorem discountedIntegrand_integrable (lam ρ q x T : ℝ)
    (hlam : 0 < lam) (hρ : 0 < ρ) :
    Integrable (discountedIntegrand lam ρ q x T)
      (futureLebesgueMeasure T) := by
  let c := ρ + 2 * lam
  have hc : 0 < c := by dsimp [c]; linarith
  change Integrable (discountedIntegrand lam ρ q x T)
    (volume.restrict (Set.Ici T))
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-c * s)) (Set.Ioi T) :=
    integrableOn_exp_mul_Ioi (by dsimp [c]; linarith) T
  have hbaseIci : IntegrableOn (fun s : ℝ => Real.exp (-c * s)) (Set.Ici T) :=
    integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.2 hbase
  have hscaled : IntegrableOn
      (fun s : ℝ => (q * x ^ 2 * Real.exp (c * T)) * Real.exp (-c * s))
      (Set.Ici T) := hbaseIci.const_mul _
  have heq : (fun s => discountedIntegrand lam ρ q x T s) =ᵐ[
      volume.restrict (Set.Ici T)]
      (fun s => (q * x ^ 2 * Real.exp (c * T)) * Real.exp (-c * s)) := by
    filter_upwards with s
    rw [discountedIntegrand_eq]
    dsimp [c]
    rw [show -(ρ + 2 * lam) * (s - T) =
      (ρ + 2 * lam) * T + (-(ρ + 2 * lam) * s) by ring, Real.exp_add]
    ring
  exact hscaled.congr heq.symm

/-- Exact discounted value formula for every positive discount and decay rate. -/
theorem value_eq_formula (lam ρ q x T : ℝ)
    (hlam : 0 < lam) (hρ : 0 < ρ) :
    value lam ρ q x T = q / (ρ + 2 * lam) * x ^ 2 := by
  let c := ρ + 2 * lam
  have hc : 0 < c := by dsimp [c]; linarith
  unfold value
  change (∫ s in Set.Ici T, discountedIntegrand lam ρ q x T s ∂volume) =
    q / c * x ^ 2
  rw [integral_Ici_eq_integral_Ioi]
  have heq : (fun s : ℝ => discountedIntegrand lam ρ q x T s) =ᵐ[
      volume.restrict (Set.Ioi T)]
      (fun s => (q * x ^ 2 * Real.exp (c * T)) * Real.exp (-c * s)) := by
    filter_upwards with s
    rw [discountedIntegrand_eq]
    dsimp [c]
    rw [show -(ρ + 2 * lam) * (s - T) =
      (ρ + 2 * lam) * T + (-(ρ + 2 * lam) * s) by ring, Real.exp_add]
    ring
  rw [integral_congr_ae heq, integral_const_mul,
    integral_exp_mul_Ioi (a := -c) (by linarith) T]
  rw [show -Real.exp (-c * T) / -c = Real.exp (-c * T) / c by ring]
  have hexp : Real.exp (c * T) * Real.exp (-c * T) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    q * x ^ 2 * Real.exp (c * T) * (Real.exp (-c * T) / c) =
        q / c * x ^ 2 * (Real.exp (c * T) * Real.exp (-c * T)) := by field_simp
    _ = q / c * x ^ 2 := by rw [hexp]; ring

def zeroTarget (lam ρ q T : ℝ) : Set ℝ :=
  theorem26ZeroValueTarget Set.univ (value lam ρ q) T

theorem zeroTarget_eq_singleton (lam ρ q T : ℝ) (hlam : 0 < lam)
    (hρ : 0 < ρ) (hq : 0 < q) :
    zeroTarget lam ρ q T = ({0} : Set ℝ) := by
  ext x
  simp only [zeroTarget, theorem26ZeroValueTarget, Set.mem_inter_iff,
    Set.mem_univ, true_and, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [value_eq_formula lam ρ q x T hlam hρ]
  constructor
  · intro hzero
    have hcoef : 0 < q / (ρ + 2 * lam) := by positivity
    by_contra hx
    have hxpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    nlinarith
  · intro hx
    rw [hx]
    simp

noncomputable def WAlong (lam x T s : ℝ) : ℝ := (flow lam x T s) ^ 2

theorem flow_hasDerivAt (lam x T s : ℝ) :
    HasDerivAt (flow lam x T) (-lam * flow lam x T s) s := by
  have harg : HasDerivAt (fun u : ℝ => -lam * (u - T)) (-lam) s := by
    convert (hasDerivAt_id s |>.sub_const T).const_mul (-lam) using 1
    · funext u
      dsimp [id]
    · ring
  have hexp := (Real.hasDerivAt_exp (-lam * (s - T))).comp s harg
  have hmul := (hasDerivAt_const s x).mul hexp
  change HasDerivAt (fun u => x * Real.exp (-lam * (u - T)))
    (-lam * (x * Real.exp (-lam * (s - T)))) s
  convert hmul using 1
  · funext u
    simp
  · simp only [Function.comp_apply, zero_mul, add_zero]
    ring

theorem WAlong_hasDerivAt (lam x T s : ℝ) :
    HasDerivAt (WAlong lam x T) (-2 * lam * WAlong lam x T s) s := by
  have hsq := (flow_hasDerivAt lam x T s).pow 2
  change HasDerivAt (fun u => (flow lam x T u) ^ 2)
    (-2 * lam * (flow lam x T s) ^ 2) s
  convert hsq using 1 <;> simp only [pow_one, Nat.cast_ofNat] <;> ring

theorem sq_flow_abs_eq (lam x T s : ℝ) :
    (|flow lam x T s|) ^ 2 = (flow lam x T s) ^ 2 := sq_abs _

theorem infDist_zeroTarget_sq (lam ρ q x T : ℝ) (hlam : 0 < lam)
    (hρ : 0 < ρ) (hq : 0 < q) :
    (Metric.infDist (flow lam x T T) (zeroTarget lam ρ q T)) ^ 2 = x ^ 2 := by
  rw [zeroTarget_eq_singleton lam ρ q T hlam hρ hq, Metric.infDist_singleton]
  simp [flow, Real.dist_eq, sq_abs]

/-- The parameterized scalar family gives all clauses needed by the general
theorem-26 convergence result: alive invariance, a nonempty closed target,
exact quadratic distance comparison, Dini exponential decay, and (26.C). -/
theorem full_convergence (lam ρ q x T : ℝ)
    (hlam : 0 < lam) (hρ : 0 < ρ) (hq : 0 < q) :
    (∀ s ≥ T,
      WAlong lam x T s ≤ WAlong lam x T T * Real.exp (-2 * lam * (s - T)) ∧
        Metric.infDist (flow lam x T s) (zeroTarget lam ρ q s) ≤
          Real.sqrt (WAlong lam x T T) * Real.exp (-lam * (s - T))) ∧
    Filter.Tendsto (fun s => value lam ρ q (flow lam x T s) s)
      Filter.atTop (nhds 0) ∧
    (∀ s ≥ T, WAlong lam x T s = 0 ↔
      flow lam x T s ∈ zeroTarget lam ρ q s) := by
  have hglobal := theorem26_full_conditional_convergence_of_rightSlopeBound
    (fun s => flow lam x T s) Set.univ (value lam ρ q) (WAlong lam x T)
    (fun r => q / (ρ + 2 * lam) * r ^ 2)
    1 1 (2 * lam) T (by norm_num) (by norm_num) (by linarith)
    (fun _ _ => Set.mem_univ _)
    (fun s _ => by
      change (zeroTarget lam ρ q s).Nonempty
      rw [zeroTarget_eq_singleton lam ρ q s hlam hρ hq]
      exact Set.singleton_nonempty 0)
    (fun s _ => by
      change IsClosed (zeroTarget lam ρ q s)
      rw [zeroTarget_eq_singleton lam ρ q s hlam hρ hq]
      exact isClosed_singleton)
    (fun s hs => by
      have hcont : Continuous (fun u : ℝ =>
          (x * Real.exp (-lam * (u - T))) ^ 2) := by fun_prop
      change ContinuousOn (fun u : ℝ => (flow lam x T u) ^ 2) (Set.Icc T s)
      exact hcont.continuousOn)
    (fun s hs => sq_nonneg _)
    (fun s hs u hu => by
      apply Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
        (WAlong lam x T) u (-2 * lam * WAlong lam x T u)
        (-(2 * lam) * WAlong lam x T u)
      · simpa [neg_mul] using WAlong_hasDerivAt lam x T u
      · have hcoeff : -2 * lam = -(2 * lam) := by ring
        rw [hcoeff])
    (fun s hs => by
      change 1 * (Metric.infDist (flow lam x T s)
        (zeroTarget lam ρ q s)) ^ 2 ≤
        WAlong lam x T s
      rw [zeroTarget_eq_singleton lam ρ q s hlam hρ hq, Metric.infDist_singleton]
      simp only [Real.dist_eq, sub_zero]
      simpa [WAlong] using le_of_eq (sq_flow_abs_eq lam x T s))
    (fun s hs => by
      change WAlong lam x T s ≤ 1 *
        (Metric.infDist (flow lam x T s) (zeroTarget lam ρ q s)) ^ 2
      rw [zeroTarget_eq_singleton lam ρ q s hlam hρ hq, Metric.infDist_singleton]
      simp only [Real.dist_eq, sub_zero]
      simpa [WAlong] using le_of_eq (sq_flow_abs_eq lam x T s).symm)
    (by fun_prop) (by simp)
    (fun s hs => by
      constructor
      · rw [value_eq_formula lam ρ q (flow lam x T s) s hlam hρ]
        positivity
      · rw [value_eq_formula lam ρ q (flow lam x T s) s hlam hρ]
        change q / (ρ + 2 * lam) * (flow lam x T s) ^ 2 ≤
          q / (ρ + 2 * lam) *
            (Metric.infDist (flow lam x T s) (zeroTarget lam ρ q s)) ^ 2
        rw [zeroTarget_eq_singleton lam ρ q s hlam hρ hq, Metric.infDist_singleton]
        simp only [Real.dist_eq, sub_zero]
        rw [sq_flow_abs_eq])
  rcases hglobal with ⟨_, hbounds, hvalue, hzero⟩
  refine ⟨?_, hvalue, ?_⟩
  · intro s hs
    have h := hbounds s hs
    simpa [zeroTarget, div_one] using h
  · intro s hs
    simpa [zeroTarget] using hzero s hs

/-- The theorem-24 lower-abstraction obstruction and the theorem-26
quantitative convergence statement hold together for every member of this
linear family. This is a verified bridge for a scalar model family; its lower
layer is the explicit constant-cost Unit model. -/
theorem theorem24_to26_bridge (lam ρ q x T : ℝ)
    (hlam : 0 < lam) (hρ : 0 < ρ) (hq : 0 < q) :
    (¬ FeedbackPZS lowerAdmissible
        (fun t => futureLebesgueMeasure t)
        (fun _π _x _T s => lowerRunningCost () s) () T) ∧
      0 < lowerValue T ∧
      (∀ s ≥ T,
        WAlong lam x T s ≤ WAlong lam x T T *
            Real.exp (-2 * lam * (s - T)) ∧
          Metric.infDist (flow lam x T s) (zeroTarget lam ρ q s) ≤
            Real.sqrt (WAlong lam x T T) * Real.exp (-lam * (s - T))) ∧
      Filter.Tendsto (fun s => value lam ρ q (flow lam x T s) s)
        Filter.atTop (nhds 0) ∧
      (∀ s ≥ T, WAlong lam x T s = 0 ↔
        flow lam x T s ∈ zeroTarget lam ρ q s) := by
  have h24 := lower_model_theorem24 T
  have hnoPZS := theorem24_no_feedbackPZS_of_condition24A
    (fun t => futureLebesgueMeasure t)
    (fun _π _x _T s => lowerRunningCost () s)
    lowerAdmissible () T (fun π hπ => h24.1 π hπ)
  exact ⟨hnoPZS, h24.2.2, full_convergence lam ρ q x T hlam hρ hq⟩

end Tomabechi.Theorem24_26_LinearFamily
