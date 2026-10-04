import Theorem24_26_LinearFamily
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# A continuum of scalar Markov feedbacks for Theorem 24 → 26

Controls are linear Markov laws `u=αx`, with `α>0`; the state equation is
`x'=-u` and the cost is `q x²+r u²`. Given `m>0`, choosing
`q=r*m*(m+ρ)` makes `α=m` the unique cost-coefficient minimizer among this
continuous policy class, and the unique value minimizer for every nonzero
initial state. This is a nontrivial model, though still restricted
to constant linear gains rather than arbitrary measurable controls.
-/

namespace Tomabechi.Theorem24_26_GainControl

open MeasureTheory Set
open Tomabechi.Theorem24_26
open Tomabechi.Theorem24_26_LinearFamily
open Tomabechi.Theorem24_26_Model

abbrev Gain := {a : ℝ // 0 < a}

/-- A positive gain induces the Borel Markov feedback `(t,x) ↦ a*x`. -/
def feedback (a : Gain) : BorelMarkovFeedback ℝ ℝ :=
  ⟨fun p => a.1 * p.2, by fun_prop⟩

theorem feedback_action (a : Gain) (t x : ℝ) :
    (feedback a).action (t, x) = a.1 * x := rfl

def controlOutput (a : Gain) (x : ℝ) : ℝ := (feedback a).action (0, x)

theorem controlOutput_eq (a : Gain) (x : ℝ) :
    controlOutput a x = a.1 * x := rfl

noncomputable def trajectory (a : Gain) (x T s : ℝ) : ℝ :=
  Tomabechi.Theorem24_26_LinearFamily.flow a.1 x T s

theorem trajectory_hasDerivAt (a : Gain) (x T s : ℝ) :
    HasDerivAt (trajectory a x T) (-controlOutput a (trajectory a x T s)) s := by
  change HasDerivAt (Tomabechi.Theorem24_26_LinearFamily.flow a.1 x T)
    (-controlOutput a (Tomabechi.Theorem24_26_LinearFamily.flow a.1 x T s)) s
  rw [controlOutput_eq]
  simpa [neg_mul] using
    Tomabechi.Theorem24_26_LinearFamily.flow_hasDerivAt a.1 x T s

def runningCost (m ρ r : ℝ) (a : Gain) (x : ℝ) : ℝ :=
  r * m * (m + ρ) * x ^ 2 + r * (controlOutput a x) ^ 2

theorem runningCost_eq_coeff (m ρ r : ℝ) (a : Gain) (x : ℝ) :
    runningCost m ρ r a x =
      (r * m * (m + ρ) + r * a.1 ^ 2) * x ^ 2 := by
  rw [runningCost, controlOutput_eq]
  ring

/-- Running cost as a function of an arbitrary instantaneous input, before
restricting to a linear gain policy. -/
def inputRunningCost (m ρ r x u : ℝ) : ℝ :=
  r * m * (m + ρ) * x ^ 2 + r * u ^ 2

def candidateValue (m r x : ℝ) : ℝ := r * m * x ^ 2

def candidateValueGradient (m r x : ℝ) : ℝ := 2 * r * m * x

/-- Time-state form of the quadratic candidate used to instantiate the
joint-Fréchet verification theorem. -/
def gainJointValue (m r : ℝ) (z : ℝ × ℝ) : ℝ :=
  candidateValue m r z.1

/-- Joint derivative of `gainJointValue`; its time component is zero. -/
def gainJointDerivative (m r : ℝ) (z : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  (r * m) • ((2 • z.1) • ContinuousLinearMap.fst ℝ ℝ ℝ)

theorem gainJointValue_hasFDerivAt (m r : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (gainJointValue m r)
      (gainJointDerivative m r z) z := by
  change HasFDerivAt (fun y : ℝ × ℝ => r * m * y.1 ^ 2)
    (gainJointDerivative m r z) z
  simpa [gainJointDerivative, pow_one, mul_smul] using
    ((hasFDerivAt_fst (p := z)).pow 2).const_mul (r * m)

/-- The HJB residual for the candidate value `r*m*x²` is exactly a square for
every real control input, not only for the linear gain policies. -/
theorem hamiltonian_gap_eq_square (m ρ r x u : ℝ) :
    inputRunningCost m ρ r x u +
        candidateValueGradient m r x * (-u) -
        ρ * candidateValue m r x = r * (u - m * x) ^ 2 := by
  unfold inputRunningCost candidateValue candidateValueGradient
  ring

/-- The same square identity in the joint-Fréchet state-time notation used by
the general time-dependent HJB verifier. -/
theorem gainJoint_hjb_residual_eq_square (m ρ r x u : ℝ) :
    inputRunningCost m ρ r x u +
      gainJointDerivative m r (x, 0) (-u, 1) -
      ρ * gainJointValue m r (x, 0) = r * (u - m * x) ^ 2 := by
  simp [gainJointDerivative, gainJointValue, candidateValue]
  unfold inputRunningCost
  ring

theorem hamiltonian_gap_nonneg (m ρ r x u : ℝ) (hr : 0 ≤ r) :
    0 ≤ inputRunningCost m ρ r x u +
      candidateValueGradient m r x * (-u) - ρ * candidateValue m r x := by
  rw [hamiltonian_gap_eq_square]
  exact mul_nonneg hr (sq_nonneg (u - m * x))

/-- For positive effort weight the Hamiltonian is minimized uniquely by
`u=m*x`, over the full real action space. -/
theorem hamiltonian_minimizer_unique (m ρ r x u : ℝ) (hr : 0 < r)
    (hmin : inputRunningCost m ρ r x u +
      candidateValueGradient m r x * (-u) - ρ * candidateValue m r x = 0) :
    u = m * x := by
  rw [hamiltonian_gap_eq_square] at hmin
  have hsquare : (u - m * x) ^ 2 = 0 :=
    (mul_eq_zero.mp hmin).resolve_left (ne_of_gt hr)
  nlinarith [sq_nonneg (u - m * x)]

theorem optimalFeedback_hamiltonian_is_minimizing (m ρ r x : ℝ) (hm : 0 < m) :
    inputRunningCost m ρ r x (controlOutput ⟨m, hm⟩ x) +
      candidateValueGradient m r x *
        (-controlOutput ⟨m, hm⟩ x) -
      ρ * candidateValue m r x = 0 := by
  rw [controlOutput_eq, hamiltonian_gap_eq_square]
  simp

noncomputable def discountedInputCost (m ρ r T : ℝ)
    (x u : ℝ → ℝ) (s : ℝ) : ℝ :=
  theorem26DiscountWeight ρ T s * inputRunningCost m ρ r (x s) (u s)

noncomputable def discountedInputEffort (r ρ T : ℝ)
    (u : ℝ → ℝ) (s : ℝ) : ℝ :=
  theorem26DiscountWeight ρ T s * (r * (u s) ^ 2)

theorem discountedInputCost_integrable_of_boundedState_and_effort
    (m ρ r T B : ℝ) (x u : ℝ → ℝ)
    (hρ : 0 < ρ) (hB : 0 ≤ B) (hx : Measurable x)
    (hbounded : ∀ s, T ≤ s → ‖x s‖ ≤ B)
    (heffort : Integrable (discountedInputEffort r ρ T u)
      (futureLebesgueMeasure T)) :
    Integrable (discountedInputCost m ρ r T x u)
      (futureLebesgueMeasure T) := by
  have hweightIoi : IntegrableOn (theorem26DiscountWeight ρ T)
      (Set.Ioi T) volume := by
    have hbase : IntegrableOn (fun s : ℝ => Real.exp (-ρ * s))
        (Set.Ioi T) volume := by
      simpa [mul_comm] using exp_neg_integrableOn_Ioi T hρ
    have heq : (fun s : ℝ => theorem26DiscountWeight ρ T s) =ᵐ[
        volume.restrict (Set.Ioi T)]
        (fun s => Real.exp (ρ * T) * Real.exp (-ρ * s)) := by
      filter_upwards with s
      rw [theorem26DiscountWeight, show -ρ * (s - T) = ρ * T + (-ρ * s) by ring,
        Real.exp_add]
    exact (hbase.const_mul (Real.exp (ρ * T))).congr heq.symm
  have hweightIci : IntegrableOn (theorem26DiscountWeight ρ T)
      (Set.Ici T) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hweightIoi
  have hstateMeas : Measurable (fun s =>
      theorem26DiscountWeight ρ T s * (x s) ^ 2) := by
    change Measurable (fun s => Real.exp (-ρ * (s - T)) * (x s) ^ 2)
    fun_prop
  have hstateDom : ∀ᵐ s ∂futureLebesgueMeasure T,
      ‖theorem26DiscountWeight ρ T s * (x s) ^ 2‖ ≤
        ‖B ^ 2 * theorem26DiscountWeight ρ T s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have hxbound : ‖x s‖ ≤ B := hbounded s hs
    have hxNormSq : ‖x s‖ ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ (norm_nonneg (x s)) hB).2 hxbound
    have hxSq : (x s) ^ 2 ≤ B ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs] using hxNormSq
    have hw : 0 ≤ theorem26DiscountWeight ρ T s := by
      rw [theorem26DiscountWeight]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _)),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw)]
    calc
      theorem26DiscountWeight ρ T s * (x s) ^ 2 ≤
          theorem26DiscountWeight ρ T s * B ^ 2 :=
        mul_le_mul_of_nonneg_left hxSq hw
      _ = B ^ 2 * theorem26DiscountWeight ρ T s := by ring
  have hstateBase : Integrable (fun s => B ^ 2 * theorem26DiscountWeight ρ T s)
      (futureLebesgueMeasure T) := by
    change IntegrableOn (fun s => B ^ 2 * theorem26DiscountWeight ρ T s)
      (Set.Ici T) volume
    exact hweightIci.const_mul (B ^ 2)
  have hstate : Integrable (fun s =>
      theorem26DiscountWeight ρ T s * (x s) ^ 2)
      (futureLebesgueMeasure T) :=
    hstateBase.mono hstateMeas.aestronglyMeasurable hstateDom
  let q : ℝ := r * m * (m + ρ)
  have hcostDecomp : discountedInputCost m ρ r T x u =ᵐ[
      futureLebesgueMeasure T]
      (fun s => q * (theorem26DiscountWeight ρ T s * (x s) ^ 2) +
        discountedInputEffort r ρ T u s) := by
    filter_upwards with s
    dsimp [discountedInputCost, discountedInputEffort, inputRunningCost, q]
    ring
  exact ((hstate.const_mul q).add heffort).congr hcostDecomp.symm

noncomputable def discountedSquareGap (m ρ r T : ℝ)
    (x u : ℝ → ℝ) (s : ℝ) : ℝ :=
  theorem26DiscountWeight ρ T s * (r * (u s - m * x s) ^ 2)

theorem inputSquareGap_le_twice_runningCost
    (m ρ r x u : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    r * (u - m * x) ^ 2 ≤
      2 * inputRunningCost m ρ r x u := by
  have hquad : (u - m * x) ^ 2 ≤ 2 * u ^ 2 + 2 * m ^ 2 * x ^ 2 := by
    nlinarith [sq_nonneg (u + m * x)]
  have hcoef : 2 * r * m ^ 2 ≤ 2 * (r * m * (m + ρ)) := by
    have hprod : 0 ≤ (r * m) * ρ := mul_nonneg (mul_nonneg hr.le hm.le) hρ.le
    nlinarith [hprod]
  have hquad' := mul_le_mul_of_nonneg_left hquad hr.le
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)
  unfold inputRunningCost
  nlinarith

/-- The squared HJB residual is integrable whenever the nonnegative quadratic
running cost is integrable; its coefficient is bounded by twice that cost. -/
theorem discountedSquareGap_integrable_of_inputCost_integrable
    (m ρ r T : ℝ) (x u : ℝ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r)
    (hx : Measurable x) (hu : Measurable u)
    (hcost : Integrable (discountedInputCost m ρ r T x u)
      (futureLebesgueMeasure T)) :
    Integrable (discountedSquareGap m ρ r T x u)
      (futureLebesgueMeasure T) := by
  have hgapMeas : Measurable (discountedSquareGap m ρ r T x u) := by
    change Measurable (fun s => Real.exp (-ρ * (s - T)) *
      (r * (u s - m * x s) ^ 2))
    fun_prop
  have hgapNonneg : ∀ s, 0 ≤ discountedSquareGap m ρ r T x u s := by
    intro s
    dsimp [discountedSquareGap, theorem26DiscountWeight]
    positivity
  have hcostNonneg : ∀ s, 0 ≤ discountedInputCost m ρ r T x u s := by
    intro s
    dsimp [discountedInputCost, theorem26DiscountWeight, inputRunningCost]
    positivity
  have hdom : ∀ᵐ s ∂futureLebesgueMeasure T,
      ‖discountedSquareGap m ρ r T x u s‖ ≤
        ‖2 * discountedInputCost m ρ r T x u s‖ := by
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (hgapNonneg s),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (hcostNonneg s))]
    have hpoint := inputSquareGap_le_twice_runningCost m ρ r (x s) (u s)
      hm hρ hr
    have hweighted := mul_le_mul_of_nonneg_left hpoint
      (le_of_lt (Real.exp_pos (-ρ * (s - T))))
    change Real.exp (-ρ * (s - T)) * (r * (u s - m * x s) ^ 2) ≤
      2 * (Real.exp (-ρ * (s - T)) *
        inputRunningCost m ρ r (x s) (u s))
    calc
      _ ≤ Real.exp (-ρ * (s - T)) *
          (2 * inputRunningCost m ρ r (x s) (u s)) := hweighted
      _ = _ := by ring
  have hscaled : Integrable
      (fun s => 2 * discountedInputCost m ρ r T x u s)
      (futureLebesgueMeasure T) := hcost.const_mul 2
  exact hscaled.mono hgapMeas.aestronglyMeasurable hdom

theorem discountedSquareGap_intervalIntegrable_of_inputCost_integrable
    (m ρ r T S : ℝ) (x u : ℝ → ℝ) (hTS : T ≤ S)
    (hgap : Integrable (discountedSquareGap m ρ r T x u)
      (futureLebesgueMeasure T)) :
    IntervalIntegrable (discountedSquareGap m ρ r T x u) volume T S := by
  have hIci : IntegrableOn (discountedSquareGap m ρ r T x u)
      (Set.Ici T) volume := by
    change Integrable (discountedSquareGap m ρ r T x u)
      (volume.restrict (Set.Ici T))
    exact hgap
  have hIoc : IntegrableOn (discountedSquareGap m ρ r T x u)
      (Set.Ioc T S) volume :=
    hIci.mono_set (fun s hs => le_of_lt hs.1)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hTS).2 hIoc

theorem discountedInputCost_intervalIntegrable_of_integrable
    (m ρ r T S : ℝ) (x u : ℝ → ℝ) (hTS : T ≤ S)
    (hcost : Integrable (discountedInputCost m ρ r T x u)
      (futureLebesgueMeasure T)) :
    IntervalIntegrable (discountedInputCost m ρ r T x u) volume T S := by
  have hIci : IntegrableOn (discountedInputCost m ρ r T x u)
      (Set.Ici T) volume := by
    change Integrable (discountedInputCost m ρ r T x u)
      (volume.restrict (Set.Ici T))
    exact hcost
  have hIoc : IntegrableOn (discountedInputCost m ρ r T x u)
      (Set.Ioc T S) volume :=
    hIci.mono_set (fun s hs => le_of_lt hs.1)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hTS).2 hIoc

noncomputable def discountedCandidateValue (m ρ r T : ℝ)
    (x : ℝ → ℝ) (s : ℝ) : ℝ :=
  theorem26DiscountWeight ρ T s * candidateValue m r (x s)

/-- Finite discounted quadratic running cost controls the discounted
candidate value in `L¹`. This is the candidate-integrability premise needed
by the joint Fréchet HJB verifier. -/
theorem discountedCandidateValue_integrable_of_inputCost_integrable
    (m ρ r T : ℝ) (x u : ℝ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r)
    (hx : Measurable x)
    (hcost : Integrable (discountedInputCost m ρ r T x u)
      (futureLebesgueMeasure T)) :
    Integrable (discountedCandidateValue m ρ r T x)
      (futureLebesgueMeasure T) := by
  let q : ℝ := r * m * (m + ρ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hFmeas : Measurable (discountedCandidateValue m ρ r T x) := by
    change Measurable (fun s => Real.exp (-ρ * (s - T)) *
      (r * m * (x s) ^ 2))
    fun_prop
  have hdom : ∀ᵐ s ∂futureLebesgueMeasure T,
      ‖discountedCandidateValue m ρ r T x s‖ ≤
        ‖(r * m / q) * discountedInputCost m ρ r T x u s‖ := by
    filter_upwards with s
    have hw : 0 ≤ theorem26DiscountWeight ρ T s := by
      dsimp [theorem26DiscountWeight]; positivity
    have hF : 0 ≤ discountedCandidateValue m ρ r T x s := by
      dsimp [discountedCandidateValue, theorem26DiscountWeight, candidateValue]
      positivity
    have hcost' : 0 ≤ discountedInputCost m ρ r T x u s := by
      dsimp [discountedInputCost, theorem26DiscountWeight, inputRunningCost]
      positivity
    have hstate : q * (x s) ^ 2 ≤ inputRunningCost m ρ r (x s) (u s) := by
      dsimp [inputRunningCost, q]
      nlinarith [sq_nonneg (u s), mul_nonneg hr.le (sq_nonneg (u s))]
    rw [Real.norm_eq_abs, abs_of_nonneg hF, Real.norm_eq_abs, abs_of_nonneg]
    · have hc : 0 ≤ r * m / q := div_nonneg (mul_nonneg hr.le hm.le) hq.le
      have hh := mul_le_mul_of_nonneg_left hstate hc
      have hcancel : (r * m / q) * q = r * m := by
        dsimp [q]
        field_simp
      have hbase : r * m * (x s) ^ 2 ≤
          (r * m / q) * inputRunningCost m ρ r (x s) (u s) := by
        calc
          r * m * (x s) ^ 2 = (r * m / q) * (q * (x s) ^ 2) := by
            rw [← mul_assoc, hcancel]
          _ ≤ _ := hh
      dsimp [discountedCandidateValue, discountedInputCost,
        theorem26DiscountWeight, candidateValue]
      have hweighted := mul_le_mul_of_nonneg_left hbase hw
      simpa [theorem26DiscountWeight, mul_assoc, mul_left_comm, mul_comm] using hweighted
    · exact mul_nonneg (div_nonneg (mul_nonneg hr.le hm.le) hq.le) hcost'
  have hFint : Integrable (discountedCandidateValue m ρ r T x)
      (futureLebesgueMeasure T) := by
    have hs : Integrable
        (fun s => (r * m / q) * discountedInputCost m ρ r T x u s)
        (futureLebesgueMeasure T) := hcost.const_mul (r * m / q)
    exact hs.mono hFmeas.aestronglyMeasurable hdom
  exact hFint

/-- Positive discount makes the candidate terminal value vanish whenever the
state remains bounded on the future half-line. -/
theorem discountedCandidateValue_tendsto_zero_of_bounded_state
    (m ρ r T B : ℝ) (x : ℝ → ℝ) (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hbounded : ∀ s, T ≤ s → ‖x s‖ ≤ B) :
    Filter.Tendsto (discountedCandidateValue m ρ r T x)
      (Filter.atTop : Filter ℝ) (nhds 0) := by
  have hweight : Filter.Tendsto (theorem26DiscountWeight ρ T)
      (Filter.atTop : Filter ℝ) (nhds 0) := by
    have hneg : Filter.Tendsto (fun s : ℝ => -s)
        (Filter.atTop : Filter ℝ) Filter.atBot := Filter.tendsto_neg_atTop_atBot
    have hlinear : Filter.Tendsto (fun s : ℝ => -ρ * s)
        (Filter.atTop : Filter ℝ) Filter.atBot := by
      convert hneg.const_mul_atBot hρ using 1 <;> ring
    have harg : Filter.Tendsto (fun s : ℝ => -ρ * (s - T))
        (Filter.atTop : Filter ℝ) Filter.atBot := by
      convert Filter.tendsto_atBot_add_const_right _ (ρ * T) hlinear using 1 <;>
        ext s <;> ring
    change Filter.Tendsto (fun s : ℝ => Real.exp (-ρ * (s - T)))
      (Filter.atTop : Filter ℝ) (nhds 0)
    exact Real.tendsto_exp_atBot.comp harg
  let C : ℝ := |r * m| * B ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hupper : Filter.Tendsto (fun s : ℝ => C * theorem26DiscountWeight ρ T s)
      (Filter.atTop : Filter ℝ) (nhds 0) := by
    simpa using hweight.const_mul C
  have hboundedEventually : ∀ᶠ s : ℝ in Filter.atTop, |x s| ≤ B := by
    filter_upwards [Filter.eventually_ge_atTop T] with s hs
    simpa [Real.norm_eq_abs] using hbounded s hs
  have hcomparison : ∀ᶠ s : ℝ in Filter.atTop,
      -(C * theorem26DiscountWeight ρ T s) ≤
          discountedCandidateValue m ρ r T x s ∧
        discountedCandidateValue m ρ r T x s ≤
          C * theorem26DiscountWeight ρ T s := by
    filter_upwards [hboundedEventually] with s hs
    have hxsq : x s ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg (x s)) hB).2 hs
    have hbase : |r * m * x s ^ 2| ≤ |r * m| * B ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (x s))]
      exact mul_le_mul_of_nonneg_left hxsq (abs_nonneg (r * m))
    have hw : 0 ≤ theorem26DiscountWeight ρ T s := by
      rw [theorem26DiscountWeight]
      positivity
    have hweighted :
        |theorem26DiscountWeight ρ T s * (r * m * x s ^ 2)| ≤
          C * theorem26DiscountWeight ρ T s := by
      calc
        |theorem26DiscountWeight ρ T s * (r * m * x s ^ 2)| =
            theorem26DiscountWeight ρ T s * |r * m * x s ^ 2| := by
              rw [abs_mul, abs_of_nonneg hw]
        _ ≤ theorem26DiscountWeight ρ T s * (|r * m| * B ^ 2) :=
              mul_le_mul_of_nonneg_left hbase hw
        _ = C * theorem26DiscountWeight ρ T s := by
              dsimp [C]
              ring
    have hbounds := abs_le.mp hweighted
    simpa [discountedCandidateValue, candidateValue,
      theorem26DiscountWeight] using hbounds
  have hlower : Filter.Tendsto (fun s : ℝ =>
      -(C * theorem26DiscountWeight ρ T s))
      (Filter.atTop : Filter ℝ) (nhds 0) := by
    simpa using hupper.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower hupper (hcomparison.mono fun s hs => hs.1)
      (hcomparison.mono fun s hs => hs.2)

/-- For an integrable discounted cost on the future half-line, integrals over
any exhausting sequence of finite horizons converge to the actual future
Lebesgue integral. This supplies the cost-limit hypothesis in the infinite-
horizon verification theorem from ordinary integrability. -/
theorem discountedInputCost_interval_tendsto_futureIntegral
    (m ρ r T : ℝ) (x u : ℝ → ℝ) (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (hint : Integrable (discountedInputCost m ρ r T x u)
      (futureLebesgueMeasure T)) :
    Filter.Tendsto
      (fun n => ∫ s in T..horizon n, discountedInputCost m ρ r T x u s)
      (Filter.atTop : Filter ℕ)
      (nhds (∫ s, discountedInputCost m ρ r T x u s
        ∂futureLebesgueMeasure T)) := by
  have hIci : IntegrableOn (discountedInputCost m ρ r T x u)
      (Set.Ici T) volume := by
    change Integrable (discountedInputCost m ρ r T x u)
      (volume.restrict (Set.Ici T))
    exact hint
  have hIoi : IntegrableOn (discountedInputCost m ρ r T x u)
      (Set.Ioi T) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mp hIci
  have hlimit := intervalIntegral_tendsto_integral_Ioi (a := T)
    (b := horizon) (l := Filter.atTop) hIoi hhorizon
  have htarget : (∫ s in Set.Ioi T,
      discountedInputCost m ρ r T x u s ∂volume) =
      ∫ s, discountedInputCost m ρ r T x u s ∂futureLebesgueMeasure T := by
    unfold futureLebesgueMeasure
    rw [← integral_Ici_eq_integral_Ioi]
  rw [← htarget]
  exact hlimit

/-- An integrable function on the future half-line is interval-integrable on
every finite forward interval. -/
theorem integrable_future_intervalIntegrable
    (T S : ℝ) (g : ℝ → ℝ) (hTS : T ≤ S)
    (hg : Integrable g (futureLebesgueMeasure T)) :
    IntervalIntegrable g volume T S := by
  have hIci : IntegrableOn g (Set.Ici T) volume := by
    change Integrable g (volume.restrict (Set.Ici T))
    exact hg
  have hIoc : IntegrableOn g (Set.Ioc T S) volume :=
    hIci.mono_set (fun s hs => le_of_lt hs.1)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hTS).2 hIoc

/-- Integrability on the future half-line makes finite-interval integrals
along any exhausting horizon converge to the actual future Lebesgue integral. -/
theorem integrable_future_interval_tendsto_integral
    (T : ℝ) (g : ℝ → ℝ) (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (hg : Integrable g (futureLebesgueMeasure T)) :
    Filter.Tendsto (fun n => ∫ s in T..horizon n, g s)
      (Filter.atTop : Filter ℕ)
      (nhds (∫ s, g s ∂futureLebesgueMeasure T)) := by
  have hIci : IntegrableOn g (Set.Ici T) volume := by
    change Integrable g (volume.restrict (Set.Ici T))
    exact hg
  have hIoi : IntegrableOn g (Set.Ioi T) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mp hIci
  have hlimit := intervalIntegral_tendsto_integral_Ioi
    (a := T) (b := horizon) (l := Filter.atTop) hIoi hhorizon
  have htarget : (∫ s in Set.Ioi T, g s ∂volume) =
      ∫ s, g s ∂futureLebesgueMeasure T := by
    unfold futureLebesgueMeasure
    rw [← integral_Ici_eq_integral_Ioi]
  rw [← htarget]
  exact hlimit

/-- An integrable discounted candidate whose derivative is integrable on the
future half-line satisfies the transversality limit. This packages the
analytic step needed to replace a separately assumed terminal condition. -/
theorem integrable_future_tendsto_zero_of_hasDerivAt
    (T : ℝ) (F : ℝ → ℝ)
    (hF : Integrable F (futureLebesgueMeasure T))
    (hF' : Integrable (deriv F) (futureLebesgueMeasure T))
    (hderiv : ∀ s, HasDerivAt F (deriv F s) s) :
    Filter.Tendsto F (Filter.atTop : Filter ℝ) (nhds 0) := by
  have hF'oi : IntegrableOn F (Set.Ioi T) volume := by
    change Integrable F (volume.restrict (Set.Ici T)) at hF
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mp hF
  have hderiv' : IntegrableOn (deriv F) (Set.Ioi T) volume := by
    change Integrable (deriv F) (volume.restrict (Set.Ici T)) at hF'
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mp hF'
  exact MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (a := T) (fun s _ => hderiv s) hderiv' hF'oi

/-- Differentiating the discounted candidate value along the controlled
scalar dynamics `x'=-u` gives the derivative used in the verification identity. -/
theorem discountedCandidateValue_hasDerivAt
    (m ρ r T : ℝ) (x u : ℝ → ℝ) (s : ℝ)
    (hx : HasDerivAt x (-u s) s) :
    HasDerivAt (discountedCandidateValue m ρ r T x)
      (theorem26DiscountWeight ρ T s *
        (candidateValueGradient m r (x s) * (-u s) -
          ρ * candidateValue m r (x s))) s := by
  have harg : HasDerivAt (fun y : ℝ => -ρ * (y - T)) (-ρ) s := by
    convert ((hasDerivAt_id s).const_mul (-ρ)).add_const (ρ * T) using 1
    · funext y
      simp only [id_eq]
      ring
    · ring
  have hw := (Real.hasDerivAt_exp (-ρ * (s - T))).comp s harg
  have hx2 : HasDerivAt (fun y => x y ^ 2) (2 * x s * (-u s)) s := by
    convert hx.pow 2 using 1 <;> ring
  have hv := hx2.const_mul (r * m)
  have hprod := hw.mul hv
  convert hprod using 1
  · funext y
    simp [discountedCandidateValue, theorem26DiscountWeight, candidateValue]
  · simp [theorem26DiscountWeight, candidateValue,
      candidateValueGradient]
    ring

/-- Finite discounted quadratic cost supplies transversality: the discounted
candidate value and its derivative are integrable on the future half-line. -/
theorem discountedCandidateValue_tendsto_zero_of_integrable_inputCost
    (m ρ r T : ℝ) (x u : ℝ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r)
    (hx : Measurable x) (hu : Measurable u)
    (hODE : ∀ s, HasDerivAt x (-u s) s)
    (hcost : Integrable (discountedInputCost m ρ r T x u)
      (futureLebesgueMeasure T)) :
    Filter.Tendsto (discountedCandidateValue m ρ r T x)
      (Filter.atTop : Filter ℝ) (nhds 0) := by
  let q : ℝ := r * m * (m + ρ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hFmeas : Measurable (discountedCandidateValue m ρ r T x) := by
    change Measurable (fun s => Real.exp (-ρ * (s - T)) *
      (r * m * (x s) ^ 2))
    fun_prop
  have hdom : ∀ᵐ s ∂futureLebesgueMeasure T,
      ‖discountedCandidateValue m ρ r T x s‖ ≤
        ‖(r * m / q) * discountedInputCost m ρ r T x u s‖ := by
    filter_upwards with s
    have hw : 0 ≤ theorem26DiscountWeight ρ T s := by
      dsimp [theorem26DiscountWeight]; positivity
    have hF : 0 ≤ discountedCandidateValue m ρ r T x s := by
      dsimp [discountedCandidateValue, theorem26DiscountWeight, candidateValue]
      positivity
    have hcost : 0 ≤ discountedInputCost m ρ r T x u s := by
      dsimp [discountedInputCost, theorem26DiscountWeight, inputRunningCost]
      positivity
    have hstate : q * (x s) ^ 2 ≤ inputRunningCost m ρ r (x s) (u s) := by
      dsimp [inputRunningCost, q]
      nlinarith [sq_nonneg (u s), mul_nonneg hr.le (sq_nonneg (u s))]
    rw [Real.norm_eq_abs, abs_of_nonneg hF, Real.norm_eq_abs, abs_of_nonneg]
    · have hc : 0 ≤ r * m / q := div_nonneg (mul_nonneg hr.le hm.le) hq.le
      have hh := mul_le_mul_of_nonneg_left hstate hc
      have hcancel : (r * m / q) * q = r * m := by
        dsimp [q]
        field_simp
      have hbase : r * m * (x s) ^ 2 ≤
          (r * m / q) * inputRunningCost m ρ r (x s) (u s) := by
        calc
          r * m * (x s) ^ 2 = (r * m / q) * (q * (x s) ^ 2) := by
            rw [← mul_assoc, hcancel]
          _ ≤ _ := hh
      dsimp [discountedCandidateValue, discountedInputCost,
        theorem26DiscountWeight, candidateValue]
      have hweighted := mul_le_mul_of_nonneg_left hbase hw
      simpa [theorem26DiscountWeight, mul_assoc, mul_left_comm, mul_comm] using hweighted
    · exact mul_nonneg (div_nonneg (mul_nonneg hr.le hm.le) hq.le) hcost
  have hFint : Integrable (discountedCandidateValue m ρ r T x)
      (futureLebesgueMeasure T) := by
    have hs : Integrable
        (fun s => (r * m / q) * discountedInputCost m ρ r T x u s)
        (futureLebesgueMeasure T) := hcost.const_mul (r * m / q)
    exact hs.mono hFmeas.aestronglyMeasurable hdom
  have hgap := discountedSquareGap_integrable_of_inputCost_integrable
    m ρ r T x u hm hρ hr hx hu hcost
  have hderiv_eq : deriv (discountedCandidateValue m ρ r T x) =
      fun s => discountedSquareGap m ρ r T x u s -
        discountedInputCost m ρ r T x u s := by
    funext s
    have hFd := (discountedCandidateValue_hasDerivAt m ρ r T x u s
      (hODE s)).deriv
    rw [hFd]
    have hham := hamiltonian_gap_eq_square m ρ r (x s) (u s)
    unfold inputRunningCost candidateValueGradient candidateValue at hham
    have hweighted := congrArg
      (fun z => theorem26DiscountWeight ρ T s * z) hham
    dsimp [discountedSquareGap, discountedInputCost, theorem26DiscountWeight,
      candidateValueGradient, candidateValue, inputRunningCost]
    nlinarith
  have hderivInt : Integrable (deriv (discountedCandidateValue m ρ r T x))
      (futureLebesgueMeasure T) := by
    rw [hderiv_eq]
    exact hgap.sub hcost
  have hFint' : IntegrableOn (discountedCandidateValue m ρ r T x)
      (Set.Ioi T) volume := by
    change Integrable (discountedCandidateValue m ρ r T x)
      (volume.restrict (Set.Ici T)) at hFint
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mp hFint
  have hderivInt' : IntegrableOn (deriv (discountedCandidateValue m ρ r T x))
      (Set.Ioi T) volume := by
    change Integrable (deriv (discountedCandidateValue m ρ r T x))
      (volume.restrict (Set.Ici T)) at hderivInt
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mp hderivInt
  have hderivInt'' : IntegrableOn
      (fun s => theorem26DiscountWeight ρ T s *
        (candidateValueGradient m r (x s) * (-u s) -
          ρ * candidateValue m r (x s))) (Set.Ioi T) volume := by
    convert hderivInt' using 1
    funext s
    exact (discountedCandidateValue_hasDerivAt m ρ r T x u s (hODE s)).deriv.symm
  exact MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (a := T) (fun s _ => discountedCandidateValue_hasDerivAt m ρ r T x u s
      (hODE s)) hderivInt'' hFint'

/-- Finite-horizon verification identity for an arbitrary input trajectory.
The derivative hypothesis says that `F` is the discounted candidate value
along a state satisfying `x'=-u`. The cost exceeds the decrease in `F` by
the integral of the nonnegative square gap. -/
theorem finiteHorizon_verification_identity
    (m ρ r T S : ℝ) (x u F : ℝ → ℝ)
    (hF : ∀ s ∈ Set.uIcc T S, HasDerivAt F
      (theorem26DiscountWeight ρ T s *
        (candidateValueGradient m r (x s) * (-u s) -
          ρ * candidateValue m r (x s))) s)
    (hderiv : IntervalIntegrable (deriv F) volume T S)
    (hgap : IntervalIntegrable (discountedSquareGap m ρ r T x u)
      volume T S) :
    ∫ s in T..S, discountedInputCost m ρ r T x u s =
      F T - F S + ∫ s in T..S, discountedSquareGap m ρ r T x u s := by
  have hpoint : ∀ s ∈ Set.uIcc T S,
      discountedInputCost m ρ r T x u s =
        -deriv F s + discountedSquareGap m ρ r T x u s := by
    intro s hs
    have hFd := (hF s hs).deriv
    dsimp [discountedInputCost, discountedSquareGap]
    rw [hFd]
    have hgapEq := hamiltonian_gap_eq_square m ρ r (x s) (u s)
    unfold inputRunningCost candidateValueGradient candidateValue at hgapEq
    have hgapWeighted := congrArg
      (fun z => theorem26DiscountWeight ρ T s * z) hgapEq
    dsimp [inputRunningCost, candidateValueGradient, candidateValue]
    nlinarith
  calc
    ∫ s in T..S, discountedInputCost m ρ r T x u s =
        ∫ s in T..S, (-deriv F s + discountedSquareGap m ρ r T x u s) := by
          apply intervalIntegral.integral_congr; intro s hs
          exact hpoint s hs
    _ = -(∫ s in T..S, deriv F s) +
        ∫ s in T..S, discountedSquareGap m ρ r T x u s := by
          rw [intervalIntegral.integral_add]
          · rw [intervalIntegral.integral_neg]
          · exact hderiv.neg
          · exact hgap
    _ = F T - F S +
        ∫ s in T..S, discountedSquareGap m ρ r T x u s := by
          rw [intervalIntegral.integral_deriv_eq_sub
            (fun s hs => (hF s hs).differentiableAt) hderiv]
          ring

/-- Generic finite-horizon verification inequality. Whenever the discounted
cost integrand is the negative derivative of a candidate value plus a
nonnegative residual, accumulated cost dominates the candidate-value drop.
This is the core comparison step independently of any quadratic model or
particular Hamiltonian completion. -/
theorem finiteHorizon_cost_ge_candidateDrop_general
    (T S : ℝ) (cost F residual : ℝ → ℝ)
    (hTS : T ≤ S)
    (hF : ∀ s ∈ Set.uIcc T S, HasDerivAt F (deriv F s) s)
    (hpoint : ∀ s ∈ Set.uIcc T S,
      cost s = -deriv F s + residual s)
    (hderiv : IntervalIntegrable (deriv F) volume T S)
    (hresidual : IntervalIntegrable residual volume T S)
    (hresidual_nonneg : ∀ s ∈ Set.uIcc T S, 0 ≤ residual s) :
    F T - F S ≤ ∫ s in T..S, cost s := by
  have hidentity : ∫ s in T..S, cost s =
      F T - F S + ∫ s in T..S, residual s := by
    calc
      ∫ s in T..S, cost s =
          ∫ s in T..S, (-deriv F s + residual s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            exact hpoint s hs
      _ = -(∫ s in T..S, deriv F s) +
          ∫ s in T..S, residual s := by
            rw [intervalIntegral.integral_add]
            · rw [intervalIntegral.integral_neg]
            · exact hderiv.neg
            · exact hresidual
      _ = F T - F S + ∫ s in T..S, residual s := by
            rw [intervalIntegral.integral_deriv_eq_sub
              (fun s hs => (hF s hs).differentiableAt) hderiv]
            ring
  have hnonneg : 0 ≤ ∫ s in T..S, residual s :=
    intervalIntegral.integral_nonneg hTS (fun s hs =>
      hresidual_nonneg s (Icc_subset_uIcc hs))
  linarith

/-- General exponentially discounted cost along a scalar state/control path. -/
noncomputable def discountedGeneralCost (ρ T : ℝ)
    (L : ℝ → ℝ → ℝ) (x u : ℝ → ℝ) (s : ℝ) : ℝ :=
  theorem26DiscountWeight ρ T s * L (x s) (u s)

/-- Discounted candidate value along a scalar state path. -/
noncomputable def discountedGeneralCandidate (ρ T : ℝ)
    (V : ℝ → ℝ) (x : ℝ → ℝ) (s : ℝ) : ℝ :=
  theorem26DiscountWeight ρ T s * V (x s)

/-- Discounted HJB residual for dynamics `x' = f(x,u)`, running cost `L`,
and differentiable candidate value `V`. -/
noncomputable def discountedGeneralHJBResidual (ρ T : ℝ)
    (L f : ℝ → ℝ → ℝ) (V : ℝ → ℝ)
    (x u : ℝ → ℝ) (s : ℝ) : ℝ :=
  theorem26DiscountWeight ρ T s *
    (L (x s) (u s) + deriv V (x s) * f (x s) (u s) - ρ * V (x s))

/-- Finite-horizon HJB verification for arbitrary scalar dynamics and running
cost. If the Hamiltonian residual of a differentiable candidate value is
nonnegative along the competitor trajectory, its discounted cost dominates
the candidate-value drop. This generalizes the preceding quadratic example
without assuming a square-completion formula. -/
theorem finiteHorizon_hjb_cost_ge_candidateDrop
    (ρ T S : ℝ) (L f : ℝ → ℝ → ℝ) (V : ℝ → ℝ)
    (x u : ℝ → ℝ) (hTS : T ≤ S)
    (hV : ∀ y, HasDerivAt V (deriv V y) y)
    (hODE : ∀ s, HasDerivAt x (f (x s) (u s)) s)
    (hHJB : ∀ s ∈ Set.Icc T S,
      0 ≤ L (x s) (u s) + deriv V (x s) * f (x s) (u s) - ρ * V (x s))
    (hderiv : IntervalIntegrable
      (deriv (discountedGeneralCandidate ρ T V x)) volume T S)
    (hresidual : IntervalIntegrable
      (discountedGeneralHJBResidual ρ T L f V x u) volume T S) :
    discountedGeneralCandidate ρ T V x T -
        discountedGeneralCandidate ρ T V x S ≤
      ∫ s in T..S, discountedGeneralCost ρ T L x u s := by
  have hF : ∀ s ∈ Set.uIcc T S,
      HasDerivAt (discountedGeneralCandidate ρ T V x)
        (theorem26DiscountWeight ρ T s *
          (deriv V (x s) * f (x s) (u s) - ρ * V (x s))) s := by
    intro s hs
    have harg : HasDerivAt (fun y : ℝ => -ρ * (y - T)) (-ρ) s := by
      convert ((hasDerivAt_id s).const_mul (-ρ)).add_const (ρ * T) using 1
      · funext y
        simp only [id_eq]
        ring
      · ring
    have hw := (Real.hasDerivAt_exp (-ρ * (s - T))).comp s harg
    have hVx := (hV (x s)).comp s (hODE s)
    have hprod := hw.mul hVx
    convert hprod using 1
    · funext y
      simp [discountedGeneralCandidate, theorem26DiscountWeight]
    · simp [discountedGeneralCandidate, theorem26DiscountWeight]
      ring
  have hF' : ∀ s ∈ Set.uIcc T S,
      HasDerivAt (discountedGeneralCandidate ρ T V x)
        (deriv (discountedGeneralCandidate ρ T V x) s) s := by
    intro s hs
    have hd := hF s hs
    convert hd using 1
    exact hd.deriv
  have hpoint : ∀ s ∈ Set.uIcc T S,
      discountedGeneralCost ρ T L x u s =
        -deriv (discountedGeneralCandidate ρ T V x) s +
          discountedGeneralHJBResidual ρ T L f V x u s := by
    intro s hs
    have hd := (hF s hs).deriv
    dsimp [discountedGeneralCost, discountedGeneralHJBResidual]
    rw [hd]
    ring
  apply finiteHorizon_cost_ge_candidateDrop_general T S
    (discountedGeneralCost ρ T L x u)
    (discountedGeneralCandidate ρ T V x)
    (discountedGeneralHJBResidual ρ T L f V x u) hTS hF'
    hpoint hderiv hresidual ?_
  intro s hs
  have hs' : s ∈ Set.Icc T S := by
    simpa [Set.uIcc_of_le hTS] using hs
  have hexp : 0 < theorem26DiscountWeight ρ T s := by
    dsimp [theorem26DiscountWeight]
    exact Real.exp_pos _
  exact mul_nonneg hexp.le (hHJB s hs')

/-- Finite-horizon HJB verification on an arbitrary real normed state space.
The candidate value is Fréchet differentiable, and the controlled trajectory
has a classical derivative. This is the state-space-general form used when
the source model is not one-dimensional. -/
theorem finiteHorizon_hjb_cost_ge_candidateDrop_normed
    {State Control : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ T S : ℝ) (L : State → Control → ℝ)
    (f : State → Control → State) (V : State → ℝ)
    (DV : State → State →L[ℝ] ℝ)
    (x : ℝ → State) (u : ℝ → Control) (hTS : T ≤ S)
    (hV : ∀ y, HasFDerivAt V (DV y) y)
    (hODE : ∀ s, HasDerivAt x (f (x s) (u s)) s)
    (hHJB : ∀ s ∈ Set.Icc T S,
      0 ≤ L (x s) (u s) + DV (x s) (f (x s) (u s)) - ρ * V (x s))
    (hderiv : IntervalIntegrable
      (deriv (fun s => theorem26DiscountWeight ρ T s * V (x s))) volume T S)
    (hresidual : IntervalIntegrable
      (fun s => theorem26DiscountWeight ρ T s *
        (L (x s) (u s) + DV (x s) (f (x s) (u s)) - ρ * V (x s)))
      volume T S) :
    theorem26DiscountWeight ρ T T * V (x T) -
        theorem26DiscountWeight ρ T S * V (x S) ≤
      ∫ s in T..S, theorem26DiscountWeight ρ T s * L (x s) (u s) := by
  let F : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s * V (x s)
  let C : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s * L (x s) (u s)
  let R : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s *
    (L (x s) (u s) + DV (x s) (f (x s) (u s)) - ρ * V (x s))
  have hFderiv : ∀ s, HasDerivAt F
      (theorem26DiscountWeight ρ T s *
        (DV (x s) (f (x s) (u s)) - ρ * V (x s))) s := by
    intro s
    have harg : HasDerivAt (fun y : ℝ => -ρ * (y - T)) (-ρ) s := by
      convert ((hasDerivAt_id s).const_mul (-ρ)).add_const (ρ * T) using 1
      · funext y
        simp only [id_eq]
        ring
      · ring
    have hw := (Real.hasDerivAt_exp (-ρ * (s - T))).comp s harg
    have hVx := (hV (x s)).comp_hasDerivAt s (hODE s)
    have hprod := hw.mul hVx
    convert hprod using 1
    · change (fun y => theorem26DiscountWeight ρ T y * V (x y)) = F
      rfl
    · dsimp [theorem26DiscountWeight]
      ring
  have hFderiv' : ∀ s, HasDerivAt F (deriv F s) s := by
    intro s
    have hd := hFderiv s
    convert hd using 1
    exact hd.deriv
  have hpoint : ∀ s ∈ Set.uIcc T S, C s = -deriv F s + R s := by
    intro s hs
    have hd := (hFderiv s).deriv
    dsimp [C, R]
    rw [hd]
    ring
  apply finiteHorizon_cost_ge_candidateDrop_general T S C F R hTS
    (fun s _ => hFderiv' s) hpoint hderiv hresidual ?_
  intro s hs
  have hs' : s ∈ Set.Icc T S := by
    simpa [Set.uIcc_of_le hTS] using hs
  have hexp : 0 < theorem26DiscountWeight ρ T s := Real.exp_pos _
  dsimp [R]
  exact mul_nonneg hexp.le (hHJB s hs')

/-- The quadratic HJB-square residual gives the concrete instance of the
generic finite-horizon verification inequality. -/
theorem finiteHorizon_cost_ge_candidateDrop
    (m ρ r T S : ℝ) (x u F : ℝ → ℝ)
    (hTS : T ≤ S) (hr : 0 ≤ r)
    (hF : ∀ s ∈ Set.uIcc T S, HasDerivAt F
      (theorem26DiscountWeight ρ T s *
        (candidateValueGradient m r (x s) * (-u s) -
          ρ * candidateValue m r (x s))) s)
    (hderiv : IntervalIntegrable (deriv F) volume T S)
    (hgap : IntervalIntegrable (discountedSquareGap m ρ r T x u)
      volume T S) :
    F T - F S ≤ ∫ s in T..S, discountedInputCost m ρ r T x u s := by
  apply finiteHorizon_cost_ge_candidateDrop_general T S
    (discountedInputCost m ρ r T x u) F
    (discountedSquareGap m ρ r T x u) hTS
    (fun s hs => by
      have hd := hF s hs
      convert hd using 1
      exact hd.deriv)
    ?_ hderiv hgap ?_
  · intro s hs
    have hFd := (hF s hs).deriv
    dsimp [discountedInputCost, discountedSquareGap]
    rw [hFd]
    have hgapEq := hamiltonian_gap_eq_square m ρ r (x s) (u s)
    unfold inputRunningCost candidateValueGradient candidateValue at hgapEq
    have hgapWeighted := congrArg
      (fun z => theorem26DiscountWeight ρ T s * z) hgapEq
    dsimp [inputRunningCost, candidateValueGradient, candidateValue]
    nlinarith
  · intro s hs
    dsimp [discountedSquareGap, theorem26DiscountWeight]
    positivity

/-- Generic passage from finite-horizon verification inequalities to the
infinite-horizon cost. The candidate value must vanish along the exhausting
terminal horizons, and the truncated costs must converge to the actual total
cost. -/
theorem infiniteHorizon_cost_ge_initialValue
    (T initialValue J : ℝ) (cost F : ℝ → ℝ) (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (hfinite : ∀ n, initialValue - F (horizon n) ≤
      ∫ s in T..horizon n, cost s)
    (htransversality : Filter.Tendsto F (Filter.atTop : Filter ℝ) (nhds 0))
    (hcost : Filter.Tendsto
      (fun n => ∫ s in T..horizon n, cost s)
      (Filter.atTop : Filter ℕ) (nhds J)) :
    initialValue ≤ J := by
  have hterminal : Filter.Tendsto (fun n => F (horizon n))
      (Filter.atTop : Filter ℕ) (nhds 0) := htransversality.comp hhorizon
  have hleft : Filter.Tendsto (fun n => initialValue - F (horizon n))
      (Filter.atTop : Filter ℕ) (nhds initialValue) := by
    simpa using tendsto_const_nhds.sub hterminal
  exact @le_of_tendsto_of_tendsto ℝ ℕ inferInstance inferInstance inferInstance
    (fun n => initialValue - F (horizon n))
    (fun n => ∫ s in T..horizon n, cost s)
    (Filter.atTop : Filter ℕ) initialValue J Filter.atTop_neBot hleft hcost
    (Filter.Eventually.of_forall hfinite)

/-- Infinite-horizon verification for the quadratic controlled model, using
the model-independent limit theorem above. -/
theorem infiniteHorizon_cost_ge_candidateValue
    (m ρ r T initialValue J : ℝ) (x u : ℝ → ℝ)
    (F : ℝ → ℝ) (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (hfinite : ∀ n, initialValue - F (horizon n) ≤
      ∫ s in T..horizon n, discountedInputCost m ρ r T x u s)
    (htransversality : Filter.Tendsto F (Filter.atTop : Filter ℝ) (nhds 0))
    (hcost : Filter.Tendsto
      (fun n => ∫ s in T..horizon n, discountedInputCost m ρ r T x u s)
      (Filter.atTop : Filter ℕ) (nhds J)) :
    initialValue ≤ J := by
  exact infiniteHorizon_cost_ge_initialValue T initialValue J
    (discountedInputCost m ρ r T x u) F horizon hhorizon hfinite
    htransversality hcost

/-- Infinite-horizon verification for arbitrary scalar dynamics and running
cost. The HJB inequality and local interval integrability give each finite
comparison; transversality and convergence of total cost then pass it to the
infinite horizon. -/
theorem infiniteHorizon_hjb_cost_ge_candidate
    (ρ T J : ℝ) (L f : ℝ → ℝ → ℝ) (V : ℝ → ℝ)
    (x u : ℝ → ℝ) (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hV : ∀ y, HasDerivAt V (deriv V y) y)
    (hODE : ∀ s, HasDerivAt x (f (x s) (u s)) s)
    (hHJB : ∀ s, T ≤ s →
      0 ≤ L (x s) (u s) + deriv V (x s) * f (x s) (u s) - ρ * V (x s))
    (hderiv : ∀ n, IntervalIntegrable
      (deriv (discountedGeneralCandidate ρ T V x)) volume T (horizon n))
    (hresidual : ∀ n, IntervalIntegrable
      (discountedGeneralHJBResidual ρ T L f V x u) volume T (horizon n))
    (htransversality : Filter.Tendsto
      (discountedGeneralCandidate ρ T V x) (Filter.atTop : Filter ℝ) (nhds 0))
    (hcost : Filter.Tendsto
      (fun n => ∫ s in T..horizon n, discountedGeneralCost ρ T L x u s)
      (Filter.atTop : Filter ℕ)
      (nhds (∫ s, discountedGeneralCost ρ T L x u s
        ∂futureLebesgueMeasure T))) :
    V (x T) ≤ ∫ s, discountedGeneralCost ρ T L x u s
      ∂futureLebesgueMeasure T := by
  have hfinite : ∀ n, discountedGeneralCandidate ρ T V x T -
      discountedGeneralCandidate ρ T V x (horizon n) ≤
        ∫ s in T..horizon n, discountedGeneralCost ρ T L x u s := by
    intro n
    apply finiteHorizon_hjb_cost_ge_candidateDrop ρ T (horizon n)
      L f V x u (horizon_after_start n) hV hODE
      (fun s hs => hHJB s hs.1) (hderiv n) (hresidual n)
  have hlimit := infiniteHorizon_cost_ge_initialValue T
    (discountedGeneralCandidate ρ T V x T)
    (∫ s, discountedGeneralCost ρ T L x u s
      ∂futureLebesgueMeasure T)
    (discountedGeneralCost ρ T L x u)
    (discountedGeneralCandidate ρ T V x) horizon hhorizon hfinite
    htransversality hcost
  have hinitial : discountedGeneralCandidate ρ T V x T = V (x T) := by
    simp [discountedGeneralCandidate, theorem26DiscountWeight]
  rw [hinitial] at hlimit
  exact hlimit

/-- Infinite-horizon HJB verification on an arbitrary real normed state
space. It combines the Fréchet-derivative finite-horizon theorem with the
model-independent exhausting-horizon limit argument. -/
theorem infiniteHorizon_hjb_cost_ge_candidate_normed
    {State Control : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ T : ℝ) (L : State → Control → ℝ)
    (f : State → Control → State) (V : State → ℝ)
    (DV : State → State →L[ℝ] ℝ)
    (x : ℝ → State) (u : ℝ → Control) (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hV : ∀ y, HasFDerivAt V (DV y) y)
    (hODE : ∀ s, HasDerivAt x (f (x s) (u s)) s)
    (hHJB : ∀ s, T ≤ s →
      0 ≤ L (x s) (u s) + DV (x s) (f (x s) (u s)) - ρ * V (x s))
    (hderiv : ∀ n, IntervalIntegrable
      (deriv (fun s => theorem26DiscountWeight ρ T s * V (x s)))
      volume T (horizon n))
    (hresidual : ∀ n, IntervalIntegrable
      (fun s => theorem26DiscountWeight ρ T s *
        (L (x s) (u s) + DV (x s) (f (x s) (u s)) - ρ * V (x s)))
      volume T (horizon n))
    (htransversality : Filter.Tendsto
      (fun s => theorem26DiscountWeight ρ T s * V (x s))
      (Filter.atTop : Filter ℝ) (nhds 0))
    (hcost : Filter.Tendsto
      (fun n => ∫ s in T..horizon n,
        theorem26DiscountWeight ρ T s * L (x s) (u s))
      (Filter.atTop : Filter ℕ)
      (nhds (∫ s, theorem26DiscountWeight ρ T s * L (x s) (u s)
        ∂futureLebesgueMeasure T))) :
    V (x T) ≤ ∫ s, theorem26DiscountWeight ρ T s * L (x s) (u s)
      ∂futureLebesgueMeasure T := by
  let F : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s * V (x s)
  let C : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s * L (x s) (u s)
  have hfinite : ∀ n, F T - F (horizon n) ≤
      ∫ s in T..horizon n, C s := by
    intro n
    simpa [F, C] using finiteHorizon_hjb_cost_ge_candidateDrop_normed
      ρ T (horizon n) L f V DV x u (horizon_after_start n)
      hV hODE (fun s hs => hHJB s hs.1) (hderiv n) (hresidual n)
  have hlimit := infiniteHorizon_cost_ge_initialValue T (F T)
    (∫ s, C s ∂futureLebesgueMeasure T) C F horizon hhorizon hfinite
    htransversality (by simpa [C] using hcost)
  have hinitial : F T = V (x T) := by
    simp [F, theorem26DiscountWeight]
  rw [hinitial] at hlimit
  exact hlimit

/-- Discounted cost of a Borel Markov feedback along a supplied closed-loop
trajectory in a normed state space. -/
noncomputable def normedMarkovTrajectoryCost
    {State Control : Type*} [MeasurableSpace State] [MeasurableSpace Control]
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ : ℝ) (L : State → Control → ℝ)
    (trajectory : BorelMarkovFeedback State Control → State → ℝ → ℝ → State)
    (π : BorelMarkovFeedback State Control) (x : State) (T : ℝ) : ℝ :=
  ∫ s, theorem26DiscountWeight ρ T s *
    L (trajectory π x T s) (π.action (s, trajectory π x T s))
      ∂futureLebesgueMeasure T

/-- A common Borel Markov feedback is optimal at any initial pair where its
cost attains a smooth candidate value and every admissible competitor
satisfies the general HJB verification hypotheses. The same `πstar` is used
for every initial pair to which this theorem is applied. -/
theorem commonMarkovFeedback_optimal_at_pair
    {State Control : Type*} [MeasurableSpace State] [MeasurableSpace Control]
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ T : ℝ) (L : State → Control → ℝ)
    (f : State → Control → State) (V : State → ℝ)
    (DV : State → State →L[ℝ] ℝ)
    (trajectory : BorelMarkovFeedback State Control → State → ℝ → ℝ → State)
    (admissible : BorelMarkovFeedback State Control → State → ℝ → Prop)
    (πstar π : BorelMarkovFeedback State Control) (x : State)
    (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hstar_attains : normedMarkovTrajectoryCost ρ L trajectory πstar x T = V x)
    (hinitial : trajectory π x T T = x)
    (_hπ : admissible π x T)
    (hV : ∀ y, HasFDerivAt V (DV y) y)
    (hODE : ∀ s, HasDerivAt (trajectory π x T)
      (f (trajectory π x T s) (π.action (s, trajectory π x T s))) s)
    (hHJB : ∀ s, T ≤ s →
      0 ≤ L (trajectory π x T s) (π.action (s, trajectory π x T s)) +
        DV (trajectory π x T s)
          (f (trajectory π x T s) (π.action (s, trajectory π x T s))) -
        ρ * V (trajectory π x T s))
    (hderiv : ∀ n, IntervalIntegrable
      (deriv (fun s => theorem26DiscountWeight ρ T s *
        V (trajectory π x T s))) volume T (horizon n))
    (hresidual : ∀ n, IntervalIntegrable
      (fun s => theorem26DiscountWeight ρ T s *
        (L (trajectory π x T s) (π.action (s, trajectory π x T s)) +
          DV (trajectory π x T s)
            (f (trajectory π x T s) (π.action (s, trajectory π x T s))) -
          ρ * V (trajectory π x T s))) volume T (horizon n))
    (htransversality : Filter.Tendsto
      (fun s => theorem26DiscountWeight ρ T s * V (trajectory π x T s))
      (Filter.atTop : Filter ℝ) (nhds 0))
    (hcost : Filter.Tendsto
      (fun n => ∫ s in T..horizon n, theorem26DiscountWeight ρ T s *
        L (trajectory π x T s) (π.action (s, trajectory π x T s)))
      (Filter.atTop : Filter ℕ)
      (nhds (normedMarkovTrajectoryCost ρ L trajectory π x T))) :
    normedMarkovTrajectoryCost ρ L trajectory πstar x T ≤
      normedMarkovTrajectoryCost ρ L trajectory π x T := by
  rw [hstar_attains]
  have hcompare := infiniteHorizon_hjb_cost_ge_candidate_normed
    ρ T L f V DV (trajectory π x T)
    (fun s => π.action (s, trajectory π x T s)) horizon hhorizon
    horizon_after_start hV hODE hHJB hderiv hresidual htransversality
    (by simpa [normedMarkovTrajectoryCost] using hcost)
  simpa only [hinitial, normedMarkovTrajectoryCost] using hcompare

/-- Discounted cost for a possibly time-dependent running value. -/
noncomputable def normedMarkovTrajectoryCostTimeDependent
    {State Control : Type*} [MeasurableSpace State] [MeasurableSpace Control]
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ : ℝ) (L : State → Control → ℝ → ℝ)
    (trajectory : BorelMarkovFeedback State Control → State → ℝ → ℝ → State)
    (π : BorelMarkovFeedback State Control) (x : State) (T : ℝ) : ℝ :=
  ∫ s, theorem26DiscountWeight ρ T s *
    L (trajectory π x T s) (π.action (s, trajectory π x T s)) s
      ∂futureLebesgueMeasure T

/-- Chain rule for a jointly Fréchet differentiable time-dependent value
along a solution of a nonautonomous controlled ODE. -/
theorem jointValueAlongTrajectory_hasDerivAt
    {State Control : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (V : State × ℝ → ℝ)
    (DV : (State × ℝ) → (State × ℝ) →L[ℝ] ℝ)
    (f : State → Control → ℝ → State) (x : ℝ → State) (u : ℝ → Control)
    (s : ℝ) (hV : ∀ z, HasFDerivAt V (DV z) z)
    (hODE : HasDerivAt x (f (x s) (u s) s) s) :
    HasDerivAt (fun t => V (x t, t))
      (DV (x s, s) (f (x s) (u s) s, 1)) s := by
  have hpair : HasDerivAt (fun t => (x t, t))
      (f (x s) (u s) s, 1) s := hODE.prodMk (hasDerivAt_id s)
  have hcomp := HasFDerivAt.comp_hasDerivAt
    (l := V) (l' := DV (x s, s)) (f := fun t => (x t, t)) (x := s)
    (hV (x s, s)) hpair
  simpa only [Function.comp_def] using hcomp

/-- Infinite-horizon HJB verification for time-dependent costs and candidate
values along supplied controlled trajectories. `G` is the derivative of
`V(x(t),t)` along that trajectory; callers establish it from their
nonautonomous closed-loop equation and regularity assumptions. The HJB
inequality is `L + G - ρ V ≥ 0`. -/
theorem infiniteHorizon_hjb_cost_ge_candidate_timeDependent
    {State Control : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ T : ℝ) (L : State → Control → ℝ → ℝ)
    (V : State → ℝ → ℝ) (G : State → Control → ℝ → ℝ)
    (x : ℝ → State) (u : ℝ → Control) (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hpathDeriv : ∀ s, HasDerivAt (fun t => V (x t) t) (G (x s) (u s) s) s)
    (hHJB : ∀ s, T ≤ s →
      0 ≤ L (x s) (u s) s + G (x s) (u s) s - ρ * V (x s) s)
    (hderiv : ∀ n, IntervalIntegrable
      (deriv (fun s => theorem26DiscountWeight ρ T s * V (x s) s))
      volume T (horizon n))
    (hresidual : ∀ n, IntervalIntegrable
      (fun s => theorem26DiscountWeight ρ T s *
        (L (x s) (u s) s + G (x s) (u s) s - ρ * V (x s) s))
      volume T (horizon n))
    (htransversality : Filter.Tendsto
      (fun s => theorem26DiscountWeight ρ T s * V (x s) s)
      (Filter.atTop : Filter ℝ) (nhds 0))
    (hcost : Filter.Tendsto
      (fun n => ∫ s in T..horizon n, theorem26DiscountWeight ρ T s *
        L (x s) (u s) s)
      (Filter.atTop : Filter ℕ)
      (nhds (∫ s, theorem26DiscountWeight ρ T s * L (x s) (u s) s
        ∂futureLebesgueMeasure T))) :
    V (x T) T ≤ ∫ s, theorem26DiscountWeight ρ T s * L (x s) (u s) s
      ∂futureLebesgueMeasure T := by
  let F : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s * V (x s) s
  let C : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s * L (x s) (u s) s
  let R : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s *
    (L (x s) (u s) s + G (x s) (u s) s - ρ * V (x s) s)
  have hFderiv : ∀ s, HasDerivAt F
      (theorem26DiscountWeight ρ T s * (G (x s) (u s) s - ρ * V (x s) s)) s := by
    intro s
    have harg : HasDerivAt (fun t : ℝ => -ρ * (t - T)) (-ρ) s := by
      convert ((hasDerivAt_id s).const_mul (-ρ)).add_const (ρ * T) using 1
      · funext t
        simp only [id_eq]
        ring
      · ring
    have hw := (Real.hasDerivAt_exp (-ρ * (s - T))).comp s harg
    have hprod := hw.mul (hpathDeriv s)
    convert hprod using 1
    · change (fun t => theorem26DiscountWeight ρ T t * V (x t) t) = F
      rfl
    · dsimp [theorem26DiscountWeight]
      ring
  have hFderiv' : ∀ s, HasDerivAt F (deriv F s) s := by
    intro s
    have hd := hFderiv s
    convert hd using 1
    exact hd.deriv
  have hfinite : ∀ n, F T - F (horizon n) ≤ ∫ s in T..horizon n, C s := by
    intro n
    apply finiteHorizon_cost_ge_candidateDrop_general T (horizon n) C F R
      (horizon_after_start n) (fun s _ => hFderiv' s)
      (by
        intro s hs
        have hd := (hFderiv s).deriv
        dsimp [C, R]
        rw [hd]
        ring)
      (hderiv n) (hresidual n) ?_
    intro s hs
    have hs' : s ∈ Set.Icc T (horizon n) := by
      simpa [Set.uIcc_of_le (horizon_after_start n)] using hs
    have hexp : 0 < theorem26DiscountWeight ρ T s := Real.exp_pos _
    dsimp [R]
    exact mul_nonneg hexp.le (hHJB s hs'.1)
  have hlimit := infiniteHorizon_cost_ge_initialValue T (F T)
    (∫ s, C s ∂futureLebesgueMeasure T) C F horizon hhorizon hfinite
    htransversality (by simpa [C] using hcost)
  have hinitial : F T = V (x T) T := by
    simp [F, theorem26DiscountWeight]
  rw [hinitial] at hlimit
  exact hlimit

/-- A single Borel Markov feedback is optimal at this initial pair in the
nonautonomous model when it attains the candidate value and every admissible
competitor satisfies the time-dependent HJB verification conditions. -/
theorem commonMarkovFeedback_optimal_at_pair_timeDependent
    {State Control : Type*} [MeasurableSpace State] [MeasurableSpace Control]
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ T : ℝ) (L : State → Control → ℝ → ℝ)
    (V : State → ℝ → ℝ) (G : State → Control → ℝ → ℝ)
    (trajectory : BorelMarkovFeedback State Control → State → ℝ → ℝ → State)
    (admissible : BorelMarkovFeedback State Control → State → ℝ → Prop)
    (πstar π : BorelMarkovFeedback State Control) (x : State)
    (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hstar_attains : normedMarkovTrajectoryCostTimeDependent
      ρ L trajectory πstar x T = V x T)
    (hinitial : trajectory π x T T = x)
    (_hπ : admissible π x T)
    (hpathDeriv : ∀ s, HasDerivAt
      (fun t => V (trajectory π x T t) t)
      (G (trajectory π x T s) (π.action (s, trajectory π x T s)) s) s)
    (hHJB : ∀ s, T ≤ s →
      0 ≤ L (trajectory π x T s) (π.action (s, trajectory π x T s)) s +
        G (trajectory π x T s) (π.action (s, trajectory π x T s)) s -
        ρ * V (trajectory π x T s) s)
    (hderiv : ∀ n, IntervalIntegrable
      (deriv (fun s => theorem26DiscountWeight ρ T s *
        V (trajectory π x T s) s)) volume T (horizon n))
    (hresidual : ∀ n, IntervalIntegrable
      (fun s => theorem26DiscountWeight ρ T s *
        (L (trajectory π x T s) (π.action (s, trajectory π x T s)) s +
          G (trajectory π x T s) (π.action (s, trajectory π x T s)) s -
          ρ * V (trajectory π x T s) s)) volume T (horizon n))
    (htransversality : Filter.Tendsto
      (fun s => theorem26DiscountWeight ρ T s *
        V (trajectory π x T s) s) (Filter.atTop : Filter ℝ) (nhds 0))
    (hcost : Filter.Tendsto
      (fun n => ∫ s in T..horizon n, theorem26DiscountWeight ρ T s *
        L (trajectory π x T s) (π.action (s, trajectory π x T s)) s)
      (Filter.atTop : Filter ℕ)
      (nhds (normedMarkovTrajectoryCostTimeDependent ρ L trajectory π x T))) :
    normedMarkovTrajectoryCostTimeDependent ρ L trajectory πstar x T ≤
      normedMarkovTrajectoryCostTimeDependent ρ L trajectory π x T := by
  rw [hstar_attains]
  have hcompare := infiniteHorizon_hjb_cost_ge_candidate_timeDependent
    ρ T L V G (trajectory π x T)
    (fun s => π.action (s, trajectory π x T s)) horizon hhorizon
    horizon_after_start hpathDeriv hHJB hderiv hresidual
    htransversality (by
      simpa [normedMarkovTrajectoryCostTimeDependent] using hcost)
  simpa only [hinitial, normedMarkovTrajectoryCostTimeDependent] using hcompare

/-- Infinite-horizon HJB verification with a jointly Fréchet differentiable
time-and-state value. The total derivative in the HJB residual is obtained
from the nonautonomous ODE and the joint Fréchet derivative, rather than
being supplied as an unrelated trajectory hypothesis. -/
theorem infiniteHorizon_hjb_cost_ge_candidate_joint
    {State Control : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ T : ℝ) (L : State → Control → ℝ → ℝ)
    (f : State → Control → ℝ → State)
    (V : State × ℝ → ℝ)
    (DV : (State × ℝ) → (State × ℝ) →L[ℝ] ℝ)
    (x : ℝ → State) (u : ℝ → Control) (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hV : ∀ z, HasFDerivAt V (DV z) z)
    (hODE : ∀ s, HasDerivAt x (f (x s) (u s) s) s)
    (hHJB : ∀ s, T ≤ s →
      0 ≤ L (x s) (u s) s + DV (x s, s) (f (x s) (u s) s, 1) -
        ρ * V (x s, s))
    (hderiv : ∀ n, IntervalIntegrable
      (deriv (fun s => theorem26DiscountWeight ρ T s * V (x s, s)))
      volume T (horizon n))
    (hresidual : ∀ n, IntervalIntegrable
      (fun s => theorem26DiscountWeight ρ T s *
        (L (x s) (u s) s + DV (x s, s) (f (x s) (u s) s, 1) -
          ρ * V (x s, s))) volume T (horizon n))
    (htransversality : Filter.Tendsto
      (fun s => theorem26DiscountWeight ρ T s * V (x s, s))
      (Filter.atTop : Filter ℝ) (nhds 0))
    (hcost : Filter.Tendsto
      (fun n => ∫ s in T..horizon n, theorem26DiscountWeight ρ T s *
        L (x s) (u s) s)
      (Filter.atTop : Filter ℕ)
      (nhds (∫ s, theorem26DiscountWeight ρ T s * L (x s) (u s) s
        ∂futureLebesgueMeasure T))) :
    V (x T, T) ≤ ∫ s, theorem26DiscountWeight ρ T s * L (x s) (u s) s
      ∂futureLebesgueMeasure T := by
  let Vc : State → ℝ → ℝ := fun y t => V (y, t)
  let Gc : State → Control → ℝ → ℝ := fun y v t =>
    DV (y, t) (f y v t, 1)
  have hpath : ∀ s, HasDerivAt (fun t => Vc (x t) t)
      (Gc (x s) (u s) s) s := by
    intro s
    simpa [Vc, Gc] using
      jointValueAlongTrajectory_hasDerivAt V DV f x u s hV (hODE s)
  have hbase := infiniteHorizon_hjb_cost_ge_candidate_timeDependent
    ρ T L Vc Gc x u horizon hhorizon horizon_after_start hpath
    (by intro s hs; simpa [Vc, Gc] using hHJB s hs)
    (by simpa [Vc] using hderiv)
    (by simpa [Vc, Gc] using hresidual)
    (by simpa [Vc] using htransversality)
    (by simpa [Vc] using hcost)
  simpa [Vc] using hbase

/-- Joint-Fréchet HJB verification with all limiting hypotheses derived from
half-line integrability. The candidate value, HJB residual, and running cost
are required to be integrable on `[T,∞)`; these imply transversality, local
interval integrability, and convergence of the truncated costs. -/
theorem infiniteHorizon_hjb_cost_ge_candidate_joint_of_integrable
    {State Control : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ T : ℝ) (L : State → Control → ℝ → ℝ)
    (f : State → Control → ℝ → State)
    (V : State × ℝ → ℝ)
    (DV : (State × ℝ) → (State × ℝ) →L[ℝ] ℝ)
    (x : ℝ → State) (u : ℝ → Control)
    (hV : ∀ z, HasFDerivAt V (DV z) z)
    (hODE : ∀ s, HasDerivAt x (f (x s) (u s) s) s)
    (hHJB : ∀ s, T ≤ s →
      0 ≤ L (x s) (u s) s + DV (x s, s) (f (x s) (u s) s, 1) -
        ρ * V (x s, s))
    (hCandidate : Integrable
      (fun s => theorem26DiscountWeight ρ T s * V (x s, s))
      (futureLebesgueMeasure T))
    (hResidual : Integrable
      (fun s => theorem26DiscountWeight ρ T s *
        (L (x s) (u s) s + DV (x s, s) (f (x s) (u s) s, 1) -
          ρ * V (x s, s))) (futureLebesgueMeasure T))
    (hCost : Integrable
      (fun s => theorem26DiscountWeight ρ T s * L (x s) (u s) s)
      (futureLebesgueMeasure T)) :
    V (x T, T) ≤ ∫ s, theorem26DiscountWeight ρ T s * L (x s) (u s) s
      ∂futureLebesgueMeasure T := by
  let horizon : ℕ → ℝ := fun n => T + (n : ℝ)
  have hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ) := by
    dsimp [horizon]
    simpa [add_comm] using
      Filter.atTop.tendsto_atTop_add_const_right T tendsto_natCast_atTop_atTop
  have hafter : ∀ n, T ≤ horizon n := by
    intro n
    dsimp [horizon]
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  let F : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s * V (x s, s)
  let C : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s * L (x s) (u s) s
  let R : ℝ → ℝ := fun s => theorem26DiscountWeight ρ T s *
    (L (x s) (u s) s + DV (x s, s) (f (x s) (u s) s, 1) -
      ρ * V (x s, s))
  have hpath : ∀ s, HasDerivAt (fun t => V (x t, t))
      (DV (x s, s) (f (x s) (u s) s, 1)) s := by
    intro s
    exact jointValueAlongTrajectory_hasDerivAt V DV f x u s hV (hODE s)
  have hFderiv : ∀ s, HasDerivAt F
      (theorem26DiscountWeight ρ T s *
        (DV (x s, s) (f (x s) (u s) s, 1) - ρ * V (x s, s))) s := by
    intro s
    have harg : HasDerivAt (fun t : ℝ => -ρ * (t - T)) (-ρ) s := by
      convert ((hasDerivAt_id s).const_mul (-ρ)).add_const (ρ * T) using 1
      · funext t
        simp only [id_eq]
        ring
      · ring
    have hw := (Real.hasDerivAt_exp (-ρ * (s - T))).comp s harg
    have hprod := hw.mul (hpath s)
    convert hprod using 1
    · change (fun t => theorem26DiscountWeight ρ T t * V (x t, t)) = F
      rfl
    · dsimp [theorem26DiscountWeight]
      ring
  have hderiv_eq : ∀ s, deriv F s = R s - C s := by
    intro s
    have hd := (hFderiv s).deriv
    rw [hd]
    dsimp [R, C]
    ring
  have hFderiv' : ∀ s, HasDerivAt F (deriv F s) s := by
    intro s
    have hd := hFderiv s
    convert hd using 1
    exact hd.deriv
  have hF' : Integrable (deriv F) (futureLebesgueMeasure T) := by
    have hEq : deriv F =ᵐ[futureLebesgueMeasure T] fun s => R s - C s :=
      Filter.Eventually.of_forall hderiv_eq
    exact (hResidual.sub hCost).congr hEq.symm
  have htrans := integrable_future_tendsto_zero_of_hasDerivAt T F
    (by simpa [F] using hCandidate) hF' hFderiv'
  have hderiv : ∀ n, IntervalIntegrable (deriv F) volume T (horizon n) := by
    intro n
    exact integrable_future_intervalIntegrable T (horizon n) (deriv F)
      (hafter n) hF'
  have hresidual : ∀ n, IntervalIntegrable R volume T (horizon n) := by
    intro n
    exact integrable_future_intervalIntegrable T (horizon n) R (hafter n)
      (by simpa [R] using hResidual)
  have hcost : Filter.Tendsto (fun n => ∫ s in T..horizon n, C s)
      (Filter.atTop : Filter ℕ)
      (nhds (∫ s, C s ∂futureLebesgueMeasure T)) :=
    integrable_future_interval_tendsto_integral T C horizon hhorizon
      (by simpa [C] using hCost)
  have hbase := infiniteHorizon_hjb_cost_ge_candidate_joint
    ρ T L f V DV x u horizon hhorizon hafter hV hODE hHJB
    (by simpa [F] using hderiv) (by simpa [R] using hresidual)
    (by simpa [F] using htrans) (by simpa [C] using hcost)
  exact hbase

/-- The scalar quadratic control model is an instance of the joint-Fréchet
infinite-horizon HJB verifier. Finite discounted running cost supplies
candidate-value integrability, residual integrability, transversality, and
the limiting cost integral. -/
theorem gainModel_jointHJB_candidate_le_cost_of_integrable
    (m ρ r T : ℝ) (x u : ℝ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r)
    (hODE : ∀ s, HasDerivAt x (-u s) s)
    (hx : Measurable x) (hu : Measurable u)
    (hcost : Integrable (discountedInputCost m ρ r T x u)
      (futureLebesgueMeasure T)) :
    gainJointValue m r (x T, T) ≤
      ∫ s, discountedInputCost m ρ r T x u s ∂futureLebesgueMeasure T := by
  let L : ℝ → ℝ → ℝ → ℝ := fun y v _ => inputRunningCost m ρ r y v
  let f : ℝ → ℝ → ℝ → ℝ := fun _ v _ => -v
  have hV : ∀ z, HasFDerivAt (gainJointValue m r)
      (gainJointDerivative m r z) z := fun z => gainJointValue_hasFDerivAt m r z
  have hHJB : ∀ s, T ≤ s →
      0 ≤ L (x s) (u s) s +
        gainJointDerivative m r (x s, s) (f (x s) (u s) s, 1) -
          ρ * gainJointValue m r (x s, s) := by
    intro s _
    have hsq := gainJoint_hjb_residual_eq_square m ρ r (x s) (u s)
    have hsq' : L (x s) (u s) s +
        gainJointDerivative m r (x s, s) (f (x s) (u s) s, 1) -
          ρ * gainJointValue m r (x s, s) = r * (u s - m * x s) ^ 2 := by
      simpa [L, f, gainJointValue, gainJointDerivative, candidateValue,
        inputRunningCost] using hsq
    rw [hsq']
    exact mul_nonneg hr.le (sq_nonneg (u s - m * x s))
  have hCandidate : Integrable
      (fun s => theorem26DiscountWeight ρ T s * gainJointValue m r (x s, s))
      (futureLebesgueMeasure T) := by
    convert discountedCandidateValue_integrable_of_inputCost_integrable
      m ρ r T x u hm hρ hr hx hcost using 1 <;>
      funext s <;> simp [discountedCandidateValue, gainJointValue,
        candidateValue]
  have hgap := discountedSquareGap_integrable_of_inputCost_integrable
    m ρ r T x u hm hρ hr hx hu hcost
  have hResidual : Integrable
      (fun s => theorem26DiscountWeight ρ T s *
        (L (x s) (u s) s +
          gainJointDerivative m r (x s, s) (f (x s) (u s) s, 1) -
            ρ * gainJointValue m r (x s, s))) (futureLebesgueMeasure T) := by
    have hEq : (fun s => theorem26DiscountWeight ρ T s *
        (L (x s) (u s) s +
          gainJointDerivative m r (x s, s) (f (x s) (u s) s, 1) -
            ρ * gainJointValue m r (x s, s))) =ᵐ[futureLebesgueMeasure T]
        discountedSquareGap m ρ r T x u := by
      filter_upwards with s
      have hsq := gainJoint_hjb_residual_eq_square m ρ r (x s) (u s)
      have hsq' : L (x s) (u s) s +
          gainJointDerivative m r (x s, s) (f (x s) (u s) s, 1) -
            ρ * gainJointValue m r (x s, s) = r * (u s - m * x s) ^ 2 := by
        simpa [L, f, gainJointValue, gainJointDerivative, candidateValue,
          inputRunningCost] using hsq
      simp [discountedSquareGap, theorem26DiscountWeight, hsq']
    exact hgap.congr hEq.symm
  have hCost : Integrable
      (fun s => theorem26DiscountWeight ρ T s * L (x s) (u s) s)
      (futureLebesgueMeasure T) := by
    convert hcost using 1
    funext s
    simp [L, discountedInputCost, theorem26DiscountWeight, inputRunningCost]
  have hcompare := infiniteHorizon_hjb_cost_ge_candidate_joint_of_integrable
    ρ T L f (gainJointValue m r) (gainJointDerivative m r) x u hV hODE
    hHJB hCandidate hResidual hCost
  simpa [gainJointValue, candidateValue, discountedInputCost,
    theorem26DiscountWeight, inputRunningCost, L] using hcompare

/-- The common-feedback verification theorem where the pathwise candidate
derivative is derived from a jointly Fréchet differentiable value and the
nonautonomous closed-loop ODE. -/
theorem commonMarkovFeedback_optimal_at_pair_joint
    {State Control : Type*} [MeasurableSpace State] [MeasurableSpace Control]
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ T : ℝ) (L : State → Control → ℝ → ℝ)
    (f : State → Control → ℝ → State)
    (V : State × ℝ → ℝ)
    (DV : (State × ℝ) → (State × ℝ) →L[ℝ] ℝ)
    (trajectory : BorelMarkovFeedback State Control → State → ℝ → ℝ → State)
    (admissible : BorelMarkovFeedback State Control → State → ℝ → Prop)
    (πstar π : BorelMarkovFeedback State Control) (x : State)
    (horizon : ℕ → ℝ)
    (hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hstar_attains : normedMarkovTrajectoryCostTimeDependent
      ρ L trajectory πstar x T = V (x, T))
    (hinitial : trajectory π x T T = x)
    (_hπ : admissible π x T)
    (hV : ∀ z, HasFDerivAt V (DV z) z)
    (hODE : ∀ s, HasDerivAt (trajectory π x T)
      (f (trajectory π x T s) (π.action (s, trajectory π x T s)) s) s)
    (hHJB : ∀ s, T ≤ s →
      0 ≤ L (trajectory π x T s) (π.action (s, trajectory π x T s)) s +
        DV (trajectory π x T s, s)
          (f (trajectory π x T s) (π.action (s, trajectory π x T s)) s, 1) -
        ρ * V (trajectory π x T s, s))
    (hderiv : ∀ n, IntervalIntegrable
      (deriv (fun s => theorem26DiscountWeight ρ T s *
        V (trajectory π x T s, s))) volume T (horizon n))
    (hresidual : ∀ n, IntervalIntegrable
      (fun s => theorem26DiscountWeight ρ T s *
        (L (trajectory π x T s) (π.action (s, trajectory π x T s)) s +
          DV (trajectory π x T s, s)
            (f (trajectory π x T s) (π.action (s, trajectory π x T s)) s, 1) -
          ρ * V (trajectory π x T s, s))) volume T (horizon n))
    (htransversality : Filter.Tendsto
      (fun s => theorem26DiscountWeight ρ T s *
        V (trajectory π x T s, s)) (Filter.atTop : Filter ℝ) (nhds 0))
    (hcost : Filter.Tendsto
      (fun n => ∫ s in T..horizon n, theorem26DiscountWeight ρ T s *
        L (trajectory π x T s) (π.action (s, trajectory π x T s)) s)
      (Filter.atTop : Filter ℕ)
      (nhds (normedMarkovTrajectoryCostTimeDependent ρ L trajectory π x T))) :
    normedMarkovTrajectoryCostTimeDependent ρ L trajectory πstar x T ≤
      normedMarkovTrajectoryCostTimeDependent ρ L trajectory π x T := by
  let Vc : State → ℝ → ℝ := fun y t => V (y, t)
  let Gc : State → Control → ℝ → ℝ := fun y v t => DV (y, t) (f y v t, 1)
  have hpath : ∀ s, HasDerivAt
      (fun t => Vc (trajectory π x T t) t)
      (Gc (trajectory π x T s) (π.action (s, trajectory π x T s)) s) s := by
    intro s
    simpa [Vc, Gc] using jointValueAlongTrajectory_hasDerivAt V DV f
      (trajectory π x T) (fun t => π.action (t, trajectory π x T t))
      s hV (hODE s)
  have hresult := commonMarkovFeedback_optimal_at_pair_timeDependent
    ρ T L Vc Gc trajectory admissible πstar π x horizon hhorizon
    horizon_after_start (by simpa [Vc] using hstar_attains) hinitial _hπ
    hpath (by intro s hs; simpa [Vc, Gc] using hHJB s hs)
    (by simpa [Vc] using hderiv)
    (by simpa [Vc, Gc] using hresidual)
    (by simpa [Vc] using htransversality)
    (by simpa [normedMarkovTrajectoryCostTimeDependent] using hcost)
  simpa [Vc, normedMarkovTrajectoryCostTimeDependent] using hresult

/-- Pairwise optimality for one common Borel Markov feedback when the
competitor's candidate, residual, and cost are integrable on the future
half-line. This derives the transversality and horizon limits internally. -/
theorem commonMarkovFeedback_optimal_at_pair_joint_of_integrable
    {State Control : Type*} [MeasurableSpace State] [MeasurableSpace Control]
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ρ T : ℝ) (L : State → Control → ℝ → ℝ)
    (f : State → Control → ℝ → State)
    (V : State × ℝ → ℝ)
    (DV : (State × ℝ) → (State × ℝ) →L[ℝ] ℝ)
    (trajectory : BorelMarkovFeedback State Control → State → ℝ → ℝ → State)
    (admissible : BorelMarkovFeedback State Control → State → ℝ → Prop)
    (πstar π : BorelMarkovFeedback State Control) (x₀ : State)
    (hstar_attains : normedMarkovTrajectoryCostTimeDependent
      ρ L trajectory πstar x₀ T = V (x₀, T))
    (hinitial : trajectory π x₀ T T = x₀)
    (_hπ : admissible π x₀ T)
    (hV : ∀ z, HasFDerivAt V (DV z) z)
    (hODE : ∀ s, HasDerivAt (trajectory π x₀ T)
      (f (trajectory π x₀ T s) (π.action (s, trajectory π x₀ T s)) s) s)
    (hHJB : ∀ s, T ≤ s →
      0 ≤ L (trajectory π x₀ T s) (π.action (s, trajectory π x₀ T s)) s +
        DV (trajectory π x₀ T s, s)
          (f (trajectory π x₀ T s) (π.action (s, trajectory π x₀ T s)) s, 1) -
        ρ * V (trajectory π x₀ T s, s))
    (hCandidate : Integrable
      (fun s => theorem26DiscountWeight ρ T s *
        V (trajectory π x₀ T s, s)) (futureLebesgueMeasure T))
    (hResidual : Integrable
      (fun s => theorem26DiscountWeight ρ T s *
        (L (trajectory π x₀ T s) (π.action (s, trajectory π x₀ T s)) s +
          DV (trajectory π x₀ T s, s)
            (f (trajectory π x₀ T s) (π.action (s, trajectory π x₀ T s)) s, 1) -
          ρ * V (trajectory π x₀ T s, s))) (futureLebesgueMeasure T))
    (hCost : Integrable
      (fun s => theorem26DiscountWeight ρ T s *
        L (trajectory π x₀ T s) (π.action (s, trajectory π x₀ T s)) s)
      (futureLebesgueMeasure T)) :
    normedMarkovTrajectoryCostTimeDependent ρ L trajectory πstar x₀ T ≤
      normedMarkovTrajectoryCostTimeDependent ρ L trajectory π x₀ T := by
  have hcompare := infiniteHorizon_hjb_cost_ge_candidate_joint_of_integrable
    ρ T L f V DV (trajectory π x₀ T)
    (fun s => π.action (s, trajectory π x₀ T s)) hV hODE hHJB
    hCandidate hResidual hCost
  rw [hinitial] at hcompare
  rw [hstar_attains]
  simpa [normedMarkovTrajectoryCostTimeDependent] using hcompare


noncomputable def discountedIntegrand (m ρ r : ℝ) (a : Gain)
    (x T s : ℝ) : ℝ :=
  theorem26DiscountWeight ρ T s * runningCost m ρ r a (trajectory a x T s)

noncomputable def policyValue (m ρ r : ℝ) (a : Gain) (x T : ℝ) : ℝ :=
  ∫ s, discountedIntegrand m ρ r a x T s ∂futureLebesgueMeasure T

def admissible (_a : Gain) (_x : ℝ) (_T : ℝ) : Prop := True

noncomputable def modelRunningValue (m ρ r : ℝ) (a : Gain)
    (x t s : ℝ) : ℝ := runningCost m ρ r a (trajectory a x t s)

def optimalValue (m ρ r : ℝ) (x t : ℝ) : ℝ := r * m * x ^ 2

theorem discountedFeedbackValue_eq_policyValue (m ρ r : ℝ) (a : Gain)
    (x T : ℝ) :
    discountedFeedbackValue (fun t => futureLebesgueMeasure t)
      (theorem26DiscountWeight ρ) (modelRunningValue m ρ r)
      a x T = policyValue m ρ r a x T := rfl

theorem discountedIntegrand_eq_linearFamily (m ρ r : ℝ) (a : Gain)
    (x T s : ℝ) :
    discountedIntegrand m ρ r a x T s =
      Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand a.1 ρ
        (r * m * (m + ρ) + r * a.1 ^ 2) x T s := by
  unfold discountedIntegrand
  rw [runningCost_eq_coeff]
  change theorem26DiscountWeight ρ T s *
      ((r * m * (m + ρ) + r * a.1 ^ 2) *
        (Tomabechi.Theorem24_26_LinearFamily.flow a.1 x T s) ^ 2) = _
  rw [Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand,
    Tomabechi.Theorem24_26_LinearFamily.runningCost]

theorem policyValue_eq_linearValue (m ρ r : ℝ) (a : Gain) (x T : ℝ) :
    policyValue m ρ r a x T =
      Tomabechi.Theorem24_26_LinearFamily.value a.1 ρ
        (r * m * (m + ρ) + r * a.1 ^ 2) x T := by
  unfold policyValue Tomabechi.Theorem24_26_LinearFamily.value
  rw [integral_congr_ae]
  filter_upwards with s
  exact discountedIntegrand_eq_linearFamily m ρ r a x T s

theorem policyValue_eq_formula (m ρ r : ℝ) (a : Gain) (x T : ℝ)
    (hρ : 0 < ρ) :
    policyValue m ρ r a x T =
      ((r * m * (m + ρ) + r * a.1 ^ 2) / (ρ + 2 * a.1)) * x ^ 2 := by
  rw [policyValue_eq_linearValue]
  exact value_eq_formula a.1 ρ (r * m * (m + ρ) + r * a.1 ^ 2)
    x T a.2 hρ

/-- Completing the square gives the cost gap over the selected gain `m`. -/
theorem costCoefficient_sub_optimal (m ρ r a : ℝ)
    (hρ : 0 < ρ) (ha : 0 < a) :
    (r * m * (m + ρ) + r * a ^ 2) / (ρ + 2 * a) - r * m =
      r * (a - m) ^ 2 / (ρ + 2 * a) := by
  field_simp [ne_of_gt (show 0 < ρ + 2 * a by linarith)]
  ring

theorem costCoefficient_minimal (m ρ r a : ℝ)
    (hρ : 0 < ρ) (hr : 0 < r) (ha : 0 < a) :
    r * m ≤ (r * m * (m + ρ) + r * a ^ 2) / (ρ + 2 * a) := by
  have hdenom : 0 < ρ + 2 * a := by linarith
  rw [← sub_nonneg, costCoefficient_sub_optimal m ρ r a hρ ha]
  exact div_nonneg (mul_nonneg hr.le (sq_nonneg (a - m))) hdenom.le

theorem optimalGain_attains (m ρ r x T : ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    policyValue m ρ r ⟨m, hm⟩ x T = r * m * x ^ 2 := by
  rw [policyValue_eq_formula m ρ r ⟨m, hm⟩ x T hρ]
  have hcoef :
      (r * m * (m + ρ) + r * m ^ 2) / (ρ + 2 * m) = r * m := by
    field_simp [ne_of_gt (show 0 < ρ + 2 * m by linarith)]
    ring
  rw [hcoef]

/-- Verification theorem against arbitrary real-valued controls.
Any input/state pair satisfying the discounted candidate-value derivative
identity, finite-horizon integrability, and the transversality condition has
cost at least that of the optimal gain feedback. This no longer restricts
competitors to constant linear gains. -/
theorem optimalGain_minimal_among_transversalInputs
    (m ρ r x₀ T : ℝ) (x u : ℝ → ℝ) (horizon : ℕ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r)
    (hxinitial : x T = x₀)
    (horizon_tendsto : Filter.Tendsto horizon
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hODE : ∀ s, HasDerivAt x (-u s) s)
    (htransversality : Filter.Tendsto (discountedCandidateValue m ρ r T x)
      (Filter.atTop : Filter ℝ) (nhds 0))
    (hcost_integrable : Integrable (discountedInputCost m ρ r T x u)
      (futureLebesgueMeasure T)) :
    policyValue m ρ r ⟨m, hm⟩ x₀ T ≤
      ∫ s, discountedInputCost m ρ r T x u s ∂futureLebesgueMeasure T := by
  have hinitial : discountedCandidateValue m ρ r T x T = r * m * x₀ ^ 2 := by
    rw [discountedCandidateValue, theorem26DiscountWeight, candidateValue, hxinitial]
    simp
  have hF : ∀ n s, s ∈ Set.uIcc T (horizon n) → HasDerivAt
      (discountedCandidateValue m ρ r T x)
      (theorem26DiscountWeight ρ T s *
        (candidateValueGradient m r (x s) * (-u s) -
          ρ * candidateValue m r (x s))) s := by
    intro n s hs
    exact discountedCandidateValue_hasDerivAt m ρ r T x u s (hODE s)
  have hxmeas : Measurable x := by
    apply Continuous.measurable
    exact continuous_iff_continuousAt.mpr (fun s => (hODE s).continuousAt)
  have hu_eq : u = fun s => -deriv x s := by
    funext s
    have hd := (hODE s).deriv
    linarith
  have humeas : Measurable u := by
    rw [hu_eq]
    exact (measurable_deriv x).neg
  have hgapIntegrable := discountedSquareGap_integrable_of_inputCost_integrable
    m ρ r T x u hm hρ hr hxmeas humeas hcost_integrable
  have hderiv_eq : deriv (discountedCandidateValue m ρ r T x) =
      fun s => discountedSquareGap m ρ r T x u s -
        discountedInputCost m ρ r T x u s := by
    funext s
    have hFd := (discountedCandidateValue_hasDerivAt m ρ r T x u s
      (hODE s)).deriv
    rw [hFd]
    have hham := hamiltonian_gap_eq_square m ρ r (x s) (u s)
    unfold inputRunningCost candidateValueGradient candidateValue at hham
    have hweighted := congrArg
      (fun z => theorem26DiscountWeight ρ T s * z) hham
    dsimp [discountedSquareGap, discountedInputCost, theorem26DiscountWeight,
      candidateValueGradient, candidateValue, inputRunningCost]
    nlinarith
  have hfinite : ∀ n, discountedCandidateValue m ρ r T x T -
      discountedCandidateValue m ρ r T x (horizon n) ≤
      ∫ s in T..horizon n, discountedInputCost m ρ r T x u s := by
    intro n
    have hgapInterval := discountedSquareGap_intervalIntegrable_of_inputCost_integrable
      m ρ r T (horizon n) x u (horizon_after_start n) hgapIntegrable
    have hcostInterval := discountedInputCost_intervalIntegrable_of_integrable
      m ρ r T (horizon n) x u (horizon_after_start n) hcost_integrable
    have hderivInterval : IntervalIntegrable
        (deriv (discountedCandidateValue m ρ r T x)) volume T (horizon n) := by
      rw [hderiv_eq]
      exact hgapInterval.sub hcostInterval
    exact finiteHorizon_cost_ge_candidateDrop m ρ r T (horizon n) x u
      (discountedCandidateValue m ρ r T x) (horizon_after_start n) hr.le
      (hF n) hderivInterval hgapInterval
  have hcost := discountedInputCost_interval_tendsto_futureIntegral
    m ρ r T x u horizon horizon_tendsto hcost_integrable
  have hlower := infiniteHorizon_cost_ge_candidateValue m ρ r T
    (discountedCandidateValue m ρ r T x T)
    (∫ s, discountedInputCost m ρ r T x u s ∂futureLebesgueMeasure T) x u
    (discountedCandidateValue m ρ r T x) horizon horizon_tendsto hfinite
    htransversality hcost
  calc
    policyValue m ρ r ⟨m, hm⟩ x₀ T = r * m * x₀ ^ 2 :=
      optimalGain_attains m ρ r x₀ T hm hρ hr
    _ = discountedCandidateValue m ρ r T x T := hinitial.symm
    _ ≤ ∫ s, discountedInputCost m ρ r T x u s
        ∂futureLebesgueMeasure T := hlower

/-- A finite discounted cost itself implies transversality, so no separate
bounded-state hypothesis is needed for arbitrary measurable input paths. -/
theorem optimalGain_minimal_among_integrableInputs
    (m ρ r x₀ T : ℝ) (x u : ℝ → ℝ) (_horizon : ℕ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r)
    (hxinitial : x T = x₀)
    (_horizon_tendsto : Filter.Tendsto _horizon
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ))
    (_horizon_after_start : ∀ n, T ≤ _horizon n)
    (hODE : ∀ s, HasDerivAt x (-u s) s)
    (hcost_integrable : Integrable (discountedInputCost m ρ r T x u)
      (futureLebesgueMeasure T)) :
    policyValue m ρ r ⟨m, hm⟩ x₀ T ≤
      ∫ s, discountedInputCost m ρ r T x u s ∂futureLebesgueMeasure T := by
  have hxmeas : Measurable x := by
    apply Continuous.measurable
    exact continuous_iff_continuousAt.mpr (fun s => (hODE s).continuousAt)
  have hu_eq : u = fun s => -deriv x s := by
    funext s
    have hd := (hODE s).deriv
    linarith
  have humeas : Measurable u := by
    rw [hu_eq]
    exact (measurable_deriv x).neg
  have hcompare := gainModel_jointHJB_candidate_le_cost_of_integrable
    m ρ r T x u hm hρ hr hODE hxmeas humeas hcost_integrable
  calc
    policyValue m ρ r ⟨m, hm⟩ x₀ T = candidateValue m r x₀ := by
      rw [optimalGain_attains m ρ r x₀ T hm hρ hr]
      rfl
    _ = gainJointValue m r (x T, T) := by
      simp [gainJointValue, candidateValue, hxinitial]
    _ ≤ ∫ s, discountedInputCost m ρ r T x u s
        ∂futureLebesgueMeasure T := by
      simpa [gainJointValue, candidateValue] using hcompare

/-- Bounded future state is a concrete sufficient condition for the
transversality hypothesis in the arbitrary-input verification theorem. -/
theorem optimalGain_minimal_among_boundedInputs
    (m ρ r x₀ T B : ℝ) (x u : ℝ → ℝ) (horizon : ℕ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) (hB : 0 ≤ B)
    (hxinitial : x T = x₀)
    (hbounded : ∀ s, T ≤ s → ‖x s‖ ≤ B)
    (horizon_tendsto : Filter.Tendsto horizon
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hODE : ∀ s, HasDerivAt x (-u s) s)
    (heffort_integrable : Integrable (discountedInputEffort r ρ T u)
      (futureLebesgueMeasure T)) :
    policyValue m ρ r ⟨m, hm⟩ x₀ T ≤
      ∫ s, discountedInputCost m ρ r T x u s ∂futureLebesgueMeasure T := by
  apply optimalGain_minimal_among_transversalInputs m ρ r x₀ T x u horizon
    hm hρ hr hxinitial horizon_tendsto horizon_after_start hODE
    (discountedCandidateValue_tendsto_zero_of_bounded_state
      m ρ r T B x hρ hB hbounded)
    (discountedInputCost_integrable_of_boundedState_and_effort
      m ρ r T B x u hρ hB
      (Continuous.measurable (continuous_iff_continuousAt.mpr
        (fun s => (hODE s).continuousAt))) hbounded heffort_integrable)

/-- Control chosen by a Borel Markov feedback along a given state trajectory. -/
def markovFeedbackInput (π : BorelMarkovFeedback ℝ ℝ)
    (x : ℝ → ℝ) (s : ℝ) : ℝ := π.action (s, x s)

noncomputable def markovTrajectoryCost (m ρ r T : ℝ)
    (π : BorelMarkovFeedback ℝ ℝ) (x : ℝ → ℝ) : ℝ :=
  ∫ s, theorem26DiscountWeight ρ T s *
    inputRunningCost m ρ r (x s) (markovFeedbackInput π x s)
      ∂futureLebesgueMeasure T

/-- The coefficient policy's integral value is exactly the cost generated by
its single global Borel Markov map along the corresponding closed-loop flow. -/
theorem markovTrajectoryCost_feedback_eq_policyValue
    (m ρ r : ℝ) (a : Gain) (x₀ T : ℝ) :
    markovTrajectoryCost m ρ r T (feedback a) (trajectory a x₀ T) =
      policyValue m ρ r a x₀ T := by
  unfold markovTrajectoryCost policyValue
  rw [integral_congr_ae]
  filter_upwards with s
  simp only [discountedIntegrand, markovFeedbackInput, feedback_action]
  rw [runningCost_eq_coeff]
  dsimp [trajectory, inputRunningCost]
  ring

/-- The common Borel Markov feedback attains the candidate optimal value as
its actual trajectory integral, not only as the gain-family `policyValue`. -/
theorem optimalGain_markovFeedback_attains_value
    (m ρ r x₀ T : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    markovTrajectoryCost m ρ r T (feedback ⟨m, hm⟩)
      (trajectory ⟨m, hm⟩ x₀ T) = optimalValue m ρ r x₀ T := by
  rw [markovTrajectoryCost_feedback_eq_policyValue]
  simpa [optimalValue] using optimalGain_attains m ρ r x₀ T hm hρ hr

/-- An admissible finite-cost Markov trajectory records one global feedback,
its classical closed-loop path from the specified initial pair, and finite
discounted running cost. -/
def FiniteCostMarkovTrajectory (m ρ r x₀ T : ℝ)
    (π : BorelMarkovFeedback ℝ ℝ) (x : ℝ → ℝ) : Prop :=
  x T = x₀ ∧
  (∀ s, HasDerivAt x (-markovFeedbackInput π x s) s) ∧
  Integrable (discountedInputCost m ρ r T x (markovFeedbackInput π x))
    (futureLebesgueMeasure T)

/-- The set of all finite discounted costs attained by admissible classical
closed-loop trajectories from a fixed initial pair in the Borel Markov class.
-/
def finiteCostMarkovTrajectoryValues (m ρ r x₀ T : ℝ) : Set ℝ :=
  {J | ∃ (π : BorelMarkovFeedback ℝ ℝ) (x : ℝ → ℝ),
    FiniteCostMarkovTrajectory m ρ r x₀ T π x ∧
      J = markovTrajectoryCost m ρ r T π x}

/-- Any Borel Markov feedback whose closed-loop trajectory has bounded state
and finite discounted input effort cannot cost less than the common optimal
linear feedback, for this initial pair. -/
theorem optimalGain_minimal_among_boundedMarkovFeedback
    (m ρ r x₀ T B : ℝ) (π : BorelMarkovFeedback ℝ ℝ)
    (x : ℝ → ℝ) (horizon : ℕ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) (hB : 0 ≤ B)
    (hxinitial : x T = x₀)
    (hbounded : ∀ s, T ≤ s → ‖x s‖ ≤ B)
    (horizon_tendsto : Filter.Tendsto horizon
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hODE : ∀ s, HasDerivAt x (-markovFeedbackInput π x s) s)
    (heffort_integrable : Integrable
      (discountedInputEffort r ρ T (markovFeedbackInput π x))
      (futureLebesgueMeasure T)) :
    policyValue m ρ r ⟨m, hm⟩ x₀ T ≤
      markovTrajectoryCost m ρ r T π x := by
  have hcompare := optimalGain_minimal_among_boundedInputs
    m ρ r x₀ T B x (markovFeedbackInput π x) horizon
    hm hρ hr hB hxinitial hbounded horizon_tendsto horizon_after_start
    hODE heffort_integrable
  simpa [markovTrajectoryCost, discountedInputCost] using hcompare

/-- Every Borel Markov feedback with a classical closed-loop trajectory and
finite discounted running cost is dominated by the optimal linear feedback.
No boundedness assumption on the competing trajectory is needed. -/
theorem optimalGain_minimal_among_integrableMarkovFeedback
    (m ρ r x₀ T : ℝ) (π : BorelMarkovFeedback ℝ ℝ)
    (x : ℝ → ℝ) (horizon : ℕ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r)
    (hxinitial : x T = x₀)
    (horizon_tendsto : Filter.Tendsto horizon
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ))
    (horizon_after_start : ∀ n, T ≤ horizon n)
    (hODE : ∀ s, HasDerivAt x (-markovFeedbackInput π x s) s)
    (hcost_integrable : Integrable
      (discountedInputCost m ρ r T x (markovFeedbackInput π x))
      (futureLebesgueMeasure T)) :
    policyValue m ρ r ⟨m, hm⟩ x₀ T ≤
      markovTrajectoryCost m ρ r T π x := by
  have hcompare := optimalGain_minimal_among_integrableInputs
    m ρ r x₀ T x (markovFeedbackInput π x) horizon hm hρ hr hxinitial
    horizon_tendsto horizon_after_start hODE hcost_integrable
  simpa [markovTrajectoryCost, discountedInputCost] using hcompare

/-- One and the same Borel Markov feedback is optimal at every initial
state-time pair in the scalar model, against every competing Borel Markov
feedback whose closed-loop classical trajectory has finite discounted cost.
The competitor's existence assumptions may vary with the pair and feedback;
the minimizing feedback `feedback ⟨m, hm⟩` does not. -/
theorem optimalGain_commonMarkovFeedback_all_initial_pairs
    (m ρ r : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    ∀ (x₀ T : ℝ) (π : BorelMarkovFeedback ℝ ℝ) (x : ℝ → ℝ),
      x T = x₀ →
      (∀ s, HasDerivAt x (-markovFeedbackInput π x s) s) →
      Integrable
        (discountedInputCost m ρ r T x (markovFeedbackInput π x))
        (futureLebesgueMeasure T) →
      markovTrajectoryCost m ρ r T (feedback ⟨m, hm⟩)
        (trajectory ⟨m, hm⟩ x₀ T) ≤ markovTrajectoryCost m ρ r T π x := by
  intro x₀ T π x hxinitial hODE hcost
  let horizon : ℕ → ℝ := fun n => T + (n : ℝ)
  have hhorizon : Filter.Tendsto horizon (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter ℝ) := by
    dsimp [horizon]
    simpa [add_comm] using
      Filter.atTop.tendsto_atTop_add_const_right T tendsto_natCast_atTop_atTop
  have hafter : ∀ n, T ≤ horizon n := by
    intro n
    dsimp [horizon]
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hoptimal := optimalGain_minimal_among_integrableMarkovFeedback
    m ρ r x₀ T π x horizon hm hρ hr hxinitial hhorizon hafter hODE hcost
  rw [← markovTrajectoryCost_feedback_eq_policyValue m ρ r ⟨m, hm⟩ x₀ T]
    at hoptimal
  exact hoptimal

/-- `optimalValue` is the least member of the actual attained-cost set for
finite-cost classical closed-loop Borel Markov trajectories at this initial
pair. The minimum is attained by the single linear feedback. -/
theorem optimalValue_isLeast_finiteCostMarkovTrajectories
    (m ρ r x₀ T : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    IsLeast (finiteCostMarkovTrajectoryValues m ρ r x₀ T)
      (optimalValue m ρ r x₀ T) := by
  constructor
  · refine ⟨feedback ⟨m, hm⟩, trajectory ⟨m, hm⟩ x₀ T, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [trajectory, Tomabechi.Theorem24_26_LinearFamily.flow]
      · intro s
        convert trajectory_hasDerivAt ⟨m, hm⟩ x₀ T s using 1 <;>
          simp [markovFeedbackInput, feedback_action, controlOutput_eq]
      · have hEq : (fun s => discountedInputCost m ρ r T
            (trajectory ⟨m, hm⟩ x₀ T)
            (fun s => markovFeedbackInput (feedback ⟨m, hm⟩)
              (trajectory ⟨m, hm⟩ x₀ T) s) s) =ᵐ[futureLebesgueMeasure T]
            Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand m ρ
              (r * m * (m + ρ) + r * m ^ 2) x₀ T := by
          filter_upwards with s
          calc
            discountedInputCost m ρ r T
                (trajectory ⟨m, hm⟩ x₀ T)
                (fun t => markovFeedbackInput (feedback ⟨m, hm⟩)
                  (trajectory ⟨m, hm⟩ x₀ T) t) s =
                discountedIntegrand m ρ r ⟨m, hm⟩ x₀ T s := by
                  simp only [discountedInputCost, discountedIntegrand,
                    markovFeedbackInput, feedback_action]
                  rw [runningCost_eq_coeff]
                  dsimp [inputRunningCost, trajectory]
                  ring
            _ = Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand m ρ
                (r * m * (m + ρ) + r * m ^ 2) x₀ T s := by
                  exact discountedIntegrand_eq_linearFamily m ρ r
                    ⟨m, hm⟩ x₀ T s
        exact (Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand_integrable
          m ρ (r * m * (m + ρ) + r * m ^ 2) x₀ T hm hρ).congr hEq.symm
    · exact (optimalGain_markovFeedback_attains_value m ρ r x₀ T hm hρ hr).symm
  · intro J hJ
    rcases hJ with ⟨π, x, hpath, hJ⟩
    rcases hpath with ⟨hinitial, hODE, hcost⟩
    rw [hJ]
    have hminimum := optimalGain_commonMarkovFeedback_all_initial_pairs
      m ρ r hm hρ hr x₀ T π x hinitial hODE hcost
    rw [optimalGain_markovFeedback_attains_value m ρ r x₀ T hm hρ hr]
      at hminimum
    exact hminimum

/-- For every finite-cost classical closed-loop Borel Markov trajectory,
zero discounted cost is equivalent to zero instantaneous control cost almost
everywhere. The positive exponential discount cannot hide a nonzero cost. -/
theorem markovTrajectoryCost_eq_zero_iff_ae_zero_runningCost
    (m ρ r T : ℝ) (π : BorelMarkovFeedback ℝ ℝ) (x : ℝ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r)
    (hcost : Integrable
      (discountedInputCost m ρ r T x (markovFeedbackInput π x))
      (futureLebesgueMeasure T)) :
    markovTrajectoryCost m ρ r T π x = 0 ↔
      (fun s => inputRunningCost m ρ r (x s)
        (markovFeedbackInput π x s)) =ᵐ[futureLebesgueMeasure T] 0 := by
  have hIntegrable : Integrable
      (fun s => theorem26DiscountWeight ρ T s *
        inputRunningCost m ρ r (x s) (markovFeedbackInput π x s))
      (futureLebesgueMeasure T) := by
    change Integrable (fun s => theorem26DiscountWeight ρ T s *
      inputRunningCost m ρ r (x s) (markovFeedbackInput π x s))
      (futureLebesgueMeasure T) at hcost
    exact hcost
  unfold markovTrajectoryCost
  exact nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero
    (theorem26DiscountWeight ρ T)
    (fun s => inputRunningCost m ρ r (x s) (markovFeedbackInput π x s))
    (theorem26DiscountWeight_pos_ae ρ T)
    (by
      filter_upwards with s
      simp only [inputRunningCost]
      positivity)
    hIntegrable

/-- In the scalar quadratic model, the optimal value is zero exactly when
some finite-cost classical closed-loop Borel Markov policy is permanently
zero-cost a.e. This connects the actual arbitrary-feedback comparison class
to the PZS definition; existence of a classical finite-cost trajectory is
explicit in the witness, as required for a general Borel feedback. -/
theorem optimalValue_eq_zero_iff_exists_finiteCostMarkovPZS
    (m ρ r x₀ T : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    optimalValue m ρ r x₀ T = 0 ↔
      ∃ (π : BorelMarkovFeedback ℝ ℝ) (x : ℝ → ℝ),
        FiniteCostMarkovTrajectory m ρ r x₀ T π x ∧
        (fun s => inputRunningCost m ρ r (x s)
          (markovFeedbackInput π x s)) =ᵐ[futureLebesgueMeasure T] 0 := by
  let hleast := optimalValue_isLeast_finiteCostMarkovTrajectories
    m ρ r x₀ T hm hρ hr
  constructor
  · intro hzero
    rcases hleast.1 with ⟨π, x, htrajectory, hvalue⟩
    refine ⟨π, x, htrajectory, ?_⟩
    apply (markovTrajectoryCost_eq_zero_iff_ae_zero_runningCost
      m ρ r T π x hm hρ hr htrajectory.2.2).1
    rw [← hvalue, hzero]
  · rintro ⟨π, x, htrajectory, hpzs⟩
    have hcostZero := (markovTrajectoryCost_eq_zero_iff_ae_zero_runningCost
      m ρ r T π x hm hρ hr htrajectory.2.2).2 hpzs
    have hcostMem : markovTrajectoryCost m ρ r T π x ∈
        finiteCostMarkovTrajectoryValues m ρ r x₀ T :=
      ⟨π, x, htrajectory, rfl⟩
    have hminimal := hleast.2 hcostMem
    have hnonneg : 0 ≤ optimalValue m ρ r x₀ T := by
      simp [optimalValue]
      positivity
    exact le_antisymm (by simpa [hcostZero] using hminimal) hnonneg

/-- Condition 24-A is derived for every Borel Markov feedback trajectory in
the scalar model whenever the initial state is nonzero. Even if a feedback
drives the state to zero later, continuity and the positive state-cost term
force strictly positive running cost on an initial interval of positive
measure. -/
theorem finiteCostMarkovTrajectory_satisfies_condition24A
    (m ρ r x₀ T : ℝ) (π : BorelMarkovFeedback ℝ ℝ) (x : ℝ → ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r)
    (hxinitial : x T = x₀) (hx₀ : x₀ ≠ 0)
    (hODE : ∀ s, HasDerivAt x (-markovFeedbackInput π x s) s) :
    ¬ (fun s => inputRunningCost m ρ r (x s)
      (markovFeedbackInput π x s)) =ᵐ[futureLebesgueMeasure T] 0 := by
  let q : ℝ := r * m * (m + ρ)
  let f : ℝ → ℝ := fun s => q * (x s) ^ 2
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hxcontinuous : Continuous x :=
    continuous_iff_continuousAt.mpr fun s => (hODE s).continuousAt
  have hfcontinuous : Continuous f := by
    dsimp [f]
    fun_prop
  have hfT : 0 < f T := by
    change 0 < q * (x T) ^ 2
    rw [hxinitial]
    exact mul_pos hq (sq_pos_of_ne_zero hx₀)
  have heventually : ∀ᶠ s in nhds T, f s > f T / 2 :=
    hfcontinuous.continuousAt.eventually
      (Ioi_mem_nhds (by linarith : f T / 2 < f T))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp heventually
  let window : Set ℝ := Set.Ioc T (T + δ / 2)
  let μwindow : MeasureTheory.Measure ℝ := volume.restrict window
  have hwindowPositive : ∀ᵐ s ∂μwindow,
      inputRunningCost m ρ r (x s) (markovFeedbackInput π x s) > 0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    have hsleft : T < s := hs.1
    have hsright : s ≤ T + δ / 2 := hs.2
    have hdist : dist s T < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hsleft)]
      have hsmall : s - T ≤ δ / 2 := by linarith
      linarith
    have hnear : s ∈ Metric.ball T δ := Metric.mem_ball.mpr hdist
    have hstate : f s > 0 := by
      have hlarge : f s > f T / 2 := hball hnear
      linarith [hfT]
    have hstateLower : f s ≤
        inputRunningCost m ρ r (x s) (markovFeedbackInput π x s) := by
      dsimp [f, q, inputRunningCost]
      nlinarith [sq_nonneg (markovFeedbackInput π x s)]
    exact lt_of_lt_of_le hstate hstateLower
  have hμwindow : μwindow Set.univ ≠ 0 := by
    change (volume.restrict window) Set.univ ≠ 0
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
    rw [Set.univ_inter]
    rw [Real.volume_Ioc]
    apply ENNReal.ofReal_ne_zero_iff.mpr
    linarith
  have hwindowLe : μwindow ≤ futureLebesgueMeasure T := by
    dsimp [μwindow, window, futureLebesgueMeasure]
    apply MeasureTheory.Measure.restrict_mono
    · intro s hs
      exact le_of_lt hs.1
    · exact le_rfl
  intro hzero
  have hzeroWindow : (fun s => inputRunningCost m ρ r (x s)
      (markovFeedbackInput π x s)) =ᵐ[μwindow] 0 := by
    exact hzero.filter_mono (MeasureTheory.ae_mono hwindowLe)
  have hnotzero := not_ae_zero_of_ae_strictlyPositive
    μwindow (fun s => inputRunningCost m ρ r (x s)
      (markovFeedbackInput π x s)) hμwindow hwindowPositive
  exact hnotzero hzeroWindow

/-- Theorem 24's strict-positive optimal-value conclusion now applies to the
whole finite-cost classical Borel Markov trajectory class in this model.
For every nonzero initial state, condition 24-A is derived above for each
competitor, while the attained common feedback is globally minimal. -/
theorem optimalValue_pos_of_nonzero_initial_via_condition24A
    (m ρ r x₀ T : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r)
    (hx₀ : x₀ ≠ 0) :
    0 < optimalValue m ρ r x₀ T := by
  let Policy := {p : BorelMarkovFeedback ℝ ℝ × (ℝ → ℝ) //
    FiniteCostMarkovTrajectory m ρ r x₀ T p.1 p.2}
  let runningValue : Policy → Unit → ℝ → ℝ → ℝ := fun p _ _ s =>
    inputRunningCost m ρ r (p.1.2 s)
      (markovFeedbackInput p.1.1 p.1.2 s)
  let admissible : Policy → Unit → ℝ → Prop := fun _ _ _ => True
  let μ : ℝ → MeasureTheory.Measure ℝ := fun _ => futureLebesgueMeasure T
  let weight : ℝ → ℝ → ℝ := fun _ s => theorem26DiscountWeight ρ T s
  have hleast := optimalValue_isLeast_finiteCostMarkovTrajectories
    m ρ r x₀ T hm hρ hr
  rcases hleast.1 with ⟨π₀, x₀path, hpath₀, hvalue₀⟩
  let policy₀ : Policy := ⟨(π₀, x₀path), hpath₀⟩
  have hnonneg : ∀ p, admissible p () T →
      ∀ᵐ s ∂(μ T), 0 ≤ runningValue p () T s := by
    intro p hp
    filter_upwards with s
    dsimp [runningValue]
    unfold inputRunningCost
    positivity
  have hint : ∀ p, admissible p () T →
      Integrable (fun s => weight T s * runningValue p () T s) (μ T) := by
    intro p hp
    change Integrable (discountedInputCost m ρ r T p.1.2
      (markovFeedbackInput p.1.1 p.1.2)) (futureLebesgueMeasure T)
    exact p.2.2.2
  have hattains : optimalValue m ρ r x₀ T =
      discountedFeedbackValue μ weight runningValue policy₀ () T := by
    simpa [μ, weight, runningValue, policy₀, Policy,
      discountedFeedbackValue, markovTrajectoryCost, discountedInputCost] using hvalue₀
  have hminimal : ∀ p, admissible p () T →
      optimalValue m ρ r x₀ T ≤
        discountedFeedbackValue μ weight runningValue p () T := by
    intro p hp
    have hmem : markovTrajectoryCost m ρ r T p.1.1 p.1.2 ∈
        finiteCostMarkovTrajectoryValues m ρ r x₀ T :=
      ⟨p.1.1, p.1.2, p.2, rfl⟩
    have hmin := hleast.2 hmem
    simpa [μ, weight, runningValue, discountedFeedbackValue,
      markovTrajectoryCost, discountedInputCost] using hmin
  have hcondition24A : ∀ p, admissible p () T →
      ¬ runningValue p () T =ᵐ[μ T] 0 := by
    intro p hp
    exact finiteCostMarkovTrajectory_satisfies_condition24A
      m ρ r x₀ T p.1.1 p.1.2 hm hρ hr p.2.1 hx₀ p.2.2.1
  exact theorem24_positive_optimal_value_of_condition24A
    μ weight runningValue admissible policy₀ () T
    (optimalValue m ρ r x₀ T)
    (theorem26DiscountWeight_pos_ae ρ T)
    hnonneg hint trivial hattains hminimal hcondition24A

/-- Existence of a permanent-zero-suffering policy among all finite-cost
classical closed-loop Borel Markov trajectories from a fixed initial pair. -/
def HasFiniteCostMarkovPZS (m ρ r x₀ T : ℝ) : Prop :=
  ∃ (π : BorelMarkovFeedback ℝ ℝ) (x : ℝ → ℝ),
    FiniteCostMarkovTrajectory m ρ r x₀ T π x ∧
    (fun s => inputRunningCost m ρ r (x s)
      (markovFeedbackInput π x s)) =ᵐ[futureLebesgueMeasure T] 0

/-- In the full finite-cost classical Markov trajectory class, permanent zero
suffering is exactly membership in the zero-optimal-value target. The forward
and reverse implications use optimal-cost comparison/attainment and positivity
of the discounted weight. -/
theorem finiteCostMarkovPZS_iff_mem_zeroTarget
    (m ρ r x₀ T : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    HasFiniteCostMarkovPZS m ρ r x₀ T ↔
      x₀ ∈ zeroTarget m ρ (r * m * (m + ρ) + r * m ^ 2) T := by
  rw [HasFiniteCostMarkovPZS,
    ← optimalValue_eq_zero_iff_exists_finiteCostMarkovPZS
      m ρ r x₀ T hm hρ hr]
  rw [zeroTarget_eq_singleton m ρ
    (r * m * (m + ρ) + r * m ^ 2) T hm hρ (by positivity)]
  change optimalValue m ρ r x₀ T = 0 ↔ x₀ = 0
  simp only [optimalValue]
  constructor
  · intro h
    have hcoef : 0 < r * m := mul_pos hr hm
    have hsquare : x₀ ^ 2 = 0 := (mul_eq_zero.mp h).resolve_left (ne_of_gt hcoef)
    nlinarith [sq_nonneg x₀]
  · intro h
    rw [h]
    simp

theorem optimalGain_is_minimal (m ρ r a : ℝ) (x T : ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) (ha : 0 < a) :
    policyValue m ρ r ⟨m, hm⟩ x T ≤ policyValue m ρ r ⟨a, ha⟩ x T := by
  rw [optimalGain_attains m ρ r x T hm hρ hr,
    policyValue_eq_formula m ρ r ⟨a, ha⟩ x T hρ]
  have hcoeff := costCoefficient_minimal m ρ r a hρ hr ha
  nlinarith [sq_nonneg x]

/-- The upper-layer permanent-zero-value policy is exactly the zero-value
target for the continuous gain-controlled problem. -/
theorem optimalGain_PZS_iff_zeroTarget (m ρ r x T : ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    FeedbackPZS admissible (fun t => futureLebesgueMeasure t)
      (modelRunningValue m ρ r) x T ↔
        x ∈ zeroTarget m ρ (r * m * (m + ρ) + r * m ^ 2) T := by
  have hweight := theorem26DiscountWeight_pos_ae
    (μ := futureLebesgueMeasure T) ρ T
  have hnonneg : ∀ a, admissible a x T →
      ∀ᵐ s ∂futureLebesgueMeasure T, 0 ≤ modelRunningValue m ρ r a x T s := by
    intro a ha
    filter_upwards with s
    rw [modelRunningValue, runningCost_eq_coeff]
    positivity
  have hint : ∀ a, admissible a x T →
      Integrable (fun s => theorem26DiscountWeight ρ T s *
        modelRunningValue m ρ r a x T s) (futureLebesgueMeasure T) := by
    intro a ha
    have hEq : (fun s => theorem26DiscountWeight ρ T s *
        modelRunningValue m ρ r a x T s) =ᵐ[futureLebesgueMeasure T]
        Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand a.1 ρ
          (r * m * (m + ρ) + r * a.1 ^ 2) x T := by
      filter_upwards with s
      rw [← discountedIntegrand_eq_linearFamily]
      rfl
    exact (Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand_integrable
      a.1 ρ (r * m * (m + ρ) + r * a.1 ^ 2) x T a.2 hρ).congr hEq.symm
  have hattains : optimalValue m ρ r x T =
      discountedFeedbackValue (fun t => futureLebesgueMeasure t)
        (theorem26DiscountWeight ρ) (modelRunningValue m ρ r)
        ⟨m, hm⟩ x T := by
    rw [discountedFeedbackValue_eq_policyValue,
      optimalGain_attains m ρ r x T hm hρ hr]
    rfl
  have hminimal : ∀ a, admissible a x T →
      optimalValue m ρ r x T ≤
    discountedFeedbackValue (fun t => futureLebesgueMeasure t)
          (theorem26DiscountWeight ρ) (modelRunningValue m ρ r) a x T := by
    intro a ha
    rw [optimalValue, discountedFeedbackValue_eq_policyValue]
    rw [← optimalGain_attains m ρ r x T hm hρ hr]
    exact optimalGain_is_minimal m ρ r a.1 x T hm hρ hr a.2
  have hclassification := feedbackPZS_iff_mem_theorem26ZeroValueTarget
    (fun t => futureLebesgueMeasure t) (theorem26DiscountWeight ρ)
    (modelRunningValue m ρ r) admissible ⟨m, hm⟩ Set.univ
    (optimalValue m ρ r) x T hweight hnonneg hint trivial hattains hminimal
    (Set.mem_univ x)
  have hmodelTarget : theorem26ZeroValueTarget Set.univ
      (optimalValue m ρ r) T = ({0} : Set ℝ) := by
    ext y
    simp only [theorem26ZeroValueTarget, Set.mem_inter_iff, Set.mem_univ,
      true_and, Set.mem_setOf_eq, Set.mem_singleton_iff, optimalValue]
    constructor
    · intro hy
      have hcoef : 0 < r * m := mul_pos hr hm
      have hySq : y ^ 2 = 0 := (mul_eq_zero.mp hy).resolve_left (ne_of_gt hcoef)
      by_contra hyNe
      have hpos : 0 < y ^ 2 := sq_pos_of_ne_zero hyNe
      linarith
    · intro hy
      rw [hy]
      simp
  have hzeroTarget := zeroTarget_eq_singleton m ρ
    (r * m * (m + ρ) + r * m ^ 2) T hm hρ (by positivity)
  simpa [hmodelTarget, hzeroTarget] using hclassification

/-- The selected gain is the unique minimizer whenever another gain has the
same minimum cost coefficient. -/
theorem optimalGain_unique (m ρ r a : ℝ)
    (hρ : 0 < ρ) (hr : 0 < r) (ha : 0 < a)
    (hcost :
      (r * m * (m + ρ) + r * a ^ 2) / (ρ + 2 * a) = r * m) :
    a = m := by
  have hgap := costCoefficient_sub_optimal m ρ r a hρ ha
  rw [hcost] at hgap
  have hzero : r * (a - m) ^ 2 / (ρ + 2 * a) = 0 := by linarith
  have hden : ρ + 2 * a ≠ 0 := by linarith
  field_simp [hden] at hzero
  have hzero' : r * (a - m) ^ 2 = 0 := by simpa using hzero
  have hsquare : (a - m) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero').resolve_left (ne_of_gt hr)
  have hdiff : a - m = 0 := by nlinarith [sq_nonneg (a - m)]
  linarith

/-- The optimal feedback's closed loop inherits all conditional theorem-26
conclusions from the verified positive-rate linear family. -/
theorem optimalGain_full_convergence (m ρ r x T : ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    (∀ s ≥ T,
      WAlong m x T s ≤ WAlong m x T T * Real.exp (-2 * m * (s - T)) ∧
        Metric.infDist (flow m x T s)
          (zeroTarget m ρ (r * m * (m + ρ) + r * m ^ 2) s) ≤
          Real.sqrt (WAlong m x T T) * Real.exp (-m * (s - T))) ∧
    Filter.Tendsto
      (fun s => policyValue m ρ r ⟨m, hm⟩ (flow m x T s) s)
      Filter.atTop (nhds 0) ∧
    (∀ s ≥ T, WAlong m x T s = 0 ↔
      flow m x T s ∈ zeroTarget m ρ
        (r * m * (m + ρ) + r * m ^ 2) s) := by
  have hfamily := full_convergence m ρ
    (r * m * (m + ρ) + r * m ^ 2) x T hm hρ (by positivity)
  refine ⟨hfamily.1, ?_, hfamily.2.2⟩
  have hcost : (fun s => policyValue m ρ r ⟨m, hm⟩
      (flow m x T s) s) =
    (fun s => value m ρ (r * m * (m + ρ) + r * m ^ 2)
      (flow m x T s) s) := by
    funext s
    exact policyValue_eq_linearValue m ρ r ⟨m, hm⟩
      (flow m x T s) s
  simpa only [hcost] using hfamily.2.1

/-- The moving target defined by the gain model's actual optimal value. -/
def gainOptimalZeroTarget (m ρ r : ℝ) (s : ℝ) : Set ℝ :=
  theorem26ZeroValueTarget Set.univ (optimalValue m ρ r) s

theorem gainOptimalZeroTarget_eq_singleton (m ρ r s : ℝ)
    (hm : 0 < m) (hr : 0 < r) :
    gainOptimalZeroTarget m ρ r s = ({0} : Set ℝ) := by
  ext y
  simp only [gainOptimalZeroTarget, theorem26ZeroValueTarget,
    Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_setOf_eq,
    Set.mem_singleton_iff, optimalValue]
  constructor
  · intro hy
    have hc : 0 < r * m := mul_pos hr hm
    have hy2 : y ^ 2 = 0 := (mul_eq_zero.mp hy).resolve_left (ne_of_gt hc)
    nlinarith [sq_nonneg y]
  · intro hy
    rw [hy]
    simp

/-- Direct verification of the Lyapunov, target, and value-modulus clauses
of condition 26-A for the actual optimal Borel feedback of the quadratic
model. Here `W=|x|²`, the target is the zero set of the proved optimal value,
and `ω(d)=r*m*d²`; both distance comparisons hold with constants one. -/
theorem optimalGain_satisfies_condition26A
    (m ρ r x T : ℝ) (hm : 0 < m) (_hρ : 0 < ρ) (hr : 0 < r) :
    (∀ s ≥ T, flow m x T s ∈ (Set.univ : Set ℝ)) ∧
    (∀ s ≥ T,
      gainOptimalZeroTarget m ρ r s = ({0} : Set ℝ) ∧
      IsClosed (gainOptimalZeroTarget m ρ r s) ∧
      (gainOptimalZeroTarget m ρ r s).Nonempty) ∧
    (∀ s ≥ T,
      (Metric.infDist (flow m x T s) (gainOptimalZeroTarget m ρ r s)) ^ 2 =
        Tomabechi.Theorem24_26_LinearFamily.WAlong m x T s ∧
      Tomabechi.Theorem1.RightSlopeBound
        (Tomabechi.Theorem24_26_LinearFamily.WAlong m x T) s
        (-2 * m * Tomabechi.Theorem24_26_LinearFamily.WAlong m x T s) ∧
      optimalValue m ρ r (flow m x T s) s =
        r * m * (Metric.infDist (flow m x T s)
          (gainOptimalZeroTarget m ρ r s)) ^ 2) ∧
    ContinuousAt (fun d : ℝ => r * m * d ^ 2) 0 ∧
    (fun d : ℝ => r * m * d ^ 2) 0 = 0 := by
  refine ⟨(fun _ _ => Set.mem_univ _), ?_, ?_, by fun_prop, by simp⟩
  · intro s hs
    refine ⟨gainOptimalZeroTarget_eq_singleton m ρ r s hm hr, ?_, ?_⟩
    · rw [gainOptimalZeroTarget_eq_singleton m ρ r s hm hr]
      exact isClosed_singleton
    · rw [gainOptimalZeroTarget_eq_singleton m ρ r s hm hr]
      exact Set.singleton_nonempty 0
  · intro s hs
    refine ⟨?_, ?_, ?_⟩
    · rw [gainOptimalZeroTarget_eq_singleton m ρ r s hm hr,
        Metric.infDist_singleton]
      simp [Real.dist_eq, Tomabechi.Theorem24_26_LinearFamily.WAlong, sq_abs]
    · apply Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
        (Tomabechi.Theorem24_26_LinearFamily.WAlong m x T) s
        (-2 * m * Tomabechi.Theorem24_26_LinearFamily.WAlong m x T s)
        (-2 * m * Tomabechi.Theorem24_26_LinearFamily.WAlong m x T s)
      · exact Tomabechi.Theorem24_26_LinearFamily.WAlong_hasDerivAt m x T s
      · exact le_rfl
    · rw [optimalValue]
      rw [gainOptimalZeroTarget_eq_singleton m ρ r s hm hr,
        Metric.infDist_singleton]
      simp [Real.dist_eq, sq_abs]

/-- Re-derive all dynamic conclusions by feeding the model-derived 26-A
package into the general theorem-26 theorem. This verifies the intended
dependency direction: the convergence result uses the proved source clauses,
not a separate linear-family convergence shortcut. -/
theorem optimalGain_full_convergence_from_condition26A
    (m ρ r x T : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    (∀ s ≥ T,
      Tomabechi.Theorem24_26_LinearFamily.WAlong m x T s ≤
          Tomabechi.Theorem24_26_LinearFamily.WAlong m x T T *
            Real.exp (-2 * m * (s - T)) ∧
        Metric.infDist (flow m x T s)
          (zeroTarget m ρ (r * m * (m + ρ) + r * m ^ 2) s) ≤
          Real.sqrt (Tomabechi.Theorem24_26_LinearFamily.WAlong m x T T) *
            Real.exp (-m * (s - T))) ∧
    Filter.Tendsto
      (fun s => policyValue m ρ r ⟨m, hm⟩ (flow m x T s) s)
      Filter.atTop (nhds 0) ∧
    (∀ s ≥ T,
      Tomabechi.Theorem24_26_LinearFamily.WAlong m x T s = 0 ↔
        flow m x T s ∈ zeroTarget m ρ
          (r * m * (m + ρ) + r * m ^ 2) s) := by
  let ω : ℝ → ℝ := fun d => r * m * d ^ 2
  rcases optimalGain_satisfies_condition26A m ρ r x T hm hρ hr with
    ⟨hAlive, hTargets, hClauses, hωcontinuous, hωzero⟩
  have hq : 0 < r * m * (m + ρ) + r * m ^ 2 := by positivity
  have htargetEq (s : ℝ) : gainOptimalZeroTarget m ρ r s =
      zeroTarget m ρ (r * m * (m + ρ) + r * m ^ 2) s := by
    rw [gainOptimalZeroTarget_eq_singleton m ρ r s hm hr,
      zeroTarget_eq_singleton m ρ (r * m * (m + ρ) + r * m ^ 2) s hm hρ hq]
  have hglobal := theorem26_full_conditional_convergence_of_rightSlopeBound
    (fun s => flow m x T s) Set.univ (optimalValue m ρ r)
    (Tomabechi.Theorem24_26_LinearFamily.WAlong m x T) ω 1 1 (2 * m) T
    (by norm_num) (by norm_num) (by positivity) hAlive
    (fun s hs => (hTargets s hs).2.2)
    (fun s hs => (hTargets s hs).2.1)
    (fun s hs => by
      change ContinuousOn
        (fun u : ℝ => (x * Real.exp (-m * (u - T))) ^ 2) (Set.Icc T s)
      fun_prop)
    (fun s hs => sq_nonneg (flow m x T s))
    (fun s hs u hu =>
      by simpa [neg_mul] using (hClauses u hu.1).2.1)
    (fun s hs => by
      change 1 * (Metric.infDist (flow m x T s)
        (gainOptimalZeroTarget m ρ r s)) ^ 2 ≤
        Tomabechi.Theorem24_26_LinearFamily.WAlong m x T s
      rw [(hClauses s hs).1]
      exact le_of_eq (by ring))
    (fun s hs => by
      change Tomabechi.Theorem24_26_LinearFamily.WAlong m x T s ≤ 1 *
        (Metric.infDist (flow m x T s)
          (gainOptimalZeroTarget m ρ r s)) ^ 2
      rw [(hClauses s hs).1]
      exact le_of_eq (by ring))
    hωcontinuous hωzero
    (fun s hs => by
      have heq := (hClauses s hs).2.2
      refine ⟨?_, ?_⟩
      · rw [heq]
        positivity
      · change optimalValue m ρ r (flow m x T s) s ≤
          r * m * (Metric.infDist (flow m x T s)
            (gainOptimalZeroTarget m ρ r s)) ^ 2
        rw [heq])
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    rcases hglobal.2.1 s hs with ⟨hW, hdist⟩
    change Metric.infDist (flow m x T s)
        (gainOptimalZeroTarget m ρ r s) ≤ _ at hdist
    rw [htargetEq s] at hdist
    constructor
    · simpa using hW
    · simpa [div_one, show (2 * m) / 2 = m by ring] using hdist
  · have hcost : (fun s => policyValue m ρ r ⟨m, hm⟩
      (flow m x T s) s) =
      (fun s => optimalValue m ρ r (flow m x T s) s) := by
        funext s
        rw [optimalGain_attains m ρ r (flow m x T s) s hm hρ hr]
        rfl
    simpa only [hcost] using hglobal.2.2.1
  · intro s hs
    have hzero := hglobal.2.2.2 s hs
    change Tomabechi.Theorem24_26_LinearFamily.WAlong m x T s = 0 ↔
      flow m x T s ∈ gainOptimalZeroTarget m ρ r s at hzero
    rw [htargetEq s] at hzero
    exact hzero

/-- Joint result of theorem 24 at the lower layer and theorem 26 at the
upper scalar model, including PZS equivalence and quantitative convergence. -/
def theorem24To26GainControlStatement (m ρ r x T : ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) : Prop :=
      (¬ FeedbackPZS lowerAdmissible
        (fun t => futureLebesgueMeasure t)
        (fun _π _x _T s => lowerRunningCost () s) () T) ∧
      0 < lowerValue T ∧
      (FeedbackPZS admissible (fun t => futureLebesgueMeasure t)
        (modelRunningValue m ρ r) x T ↔
        x ∈ zeroTarget m ρ (r * m * (m + ρ) + r * m ^ 2) T) ∧
      (∀ s ≥ T,
        WAlong m x T s ≤ WAlong m x T T * Real.exp (-2 * m * (s - T)) ∧
          Metric.infDist (flow m x T s)
            (zeroTarget m ρ (r * m * (m + ρ) + r * m ^ 2) s) ≤
            Real.sqrt (WAlong m x T T) * Real.exp (-m * (s - T))) ∧
      Filter.Tendsto
        (fun s => policyValue m ρ r ⟨m, hm⟩ (flow m x T s) s)
        Filter.atTop (nhds 0) ∧
      (∀ s ≥ T, WAlong m x T s = 0 ↔
        flow m x T s ∈ zeroTarget m ρ
          (r * m * (m + ρ) + r * m ^ 2) s)

theorem theorem24_to26_gain_control_bridge (m ρ r x T : ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
      theorem24To26GainControlStatement m ρ r x T hm hρ hr := by
  have h24 := lower_model_theorem24 T
  have hnoPZS := theorem24_no_feedbackPZS_of_condition24A
    (fun t => futureLebesgueMeasure t)
    (fun _π _x _T s => lowerRunningCost () s)
    lowerAdmissible () T (fun π hπ => h24.1 π hπ)
  exact ⟨hnoPZS, h24.2.2,
    optimalGain_PZS_iff_zeroTarget m ρ r x T hm hρ hr,
    optimalGain_full_convergence_from_condition26A m ρ r x T hm hρ hr⟩

/-- Full theorem-24-to-26 bridge for the scalar gain model at every initial
pair, including minimization by one concrete feedback map against all
finite-cost classical Markov competitors. -/
theorem theorem24_to26_gain_control_bridge_all_initial_pairs
    (m ρ r : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    ∀ (x T : ℝ),
      theorem24To26GainControlStatement m ρ r x T hm hρ hr ∧
      (markovTrajectoryCost m ρ r T (feedback ⟨m, hm⟩)
        (trajectory ⟨m, hm⟩ x T) = optimalValue m ρ r x T ∧
       ∀ (π : BorelMarkovFeedback ℝ ℝ) (xcompetitor : ℝ → ℝ),
        xcompetitor T = x →
        (∀ s, HasDerivAt xcompetitor
          (-markovFeedbackInput π xcompetitor s) s) →
        Integrable
          (discountedInputCost m ρ r T xcompetitor
            (markovFeedbackInput π xcompetitor)) (futureLebesgueMeasure T) →
        optimalValue m ρ r x T ≤
          markovTrajectoryCost m ρ r T π xcompetitor) := by
  intro x T
  refine ⟨theorem24_to26_gain_control_bridge m ρ r x T hm hρ hr, ?_⟩
  constructor
  · exact optimalGain_markovFeedback_attains_value m ρ r x T hm hρ hr
  · intro π xcompetitor hinitial hODE hcost
    have hcompare := optimalGain_commonMarkovFeedback_all_initial_pairs
      m ρ r hm hρ hr x T π xcompetitor hinitial hODE hcost
    rw [optimalGain_markovFeedback_attains_value m ρ r x T hm hρ hr]
      at hcompare
    exact hcompare

/-- Integrated theorem-24-to-26 result for the scalar quadratic control
model. The lower layer satisfies 24-A; at the upper layer every nonzero
initial state has positive optimal value, arbitrary finite-cost classical
Borel Markov PZS exists exactly on the zero-value target, the same feedback
is optimal at every initial pair, and the model-derived 26-A conditions give
quantitative convergence. -/
theorem theorem24_to26_gain_control_full_classification
    (m ρ r : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hr : 0 < r) :
    ∀ (x T : ℝ),
      (∀ π, lowerAdmissible π () T →
        ¬ (fun s => lowerRunningCost () s) =ᵐ[futureLebesgueMeasure T] 0) ∧
      0 < lowerValue T ∧
      (x ≠ 0 → 0 < optimalValue m ρ r x T) ∧
      (HasFiniteCostMarkovPZS m ρ r x T ↔
        x ∈ zeroTarget m ρ (r * m * (m + ρ) + r * m ^ 2) T) ∧
      theorem24To26GainControlStatement m ρ r x T hm hρ hr ∧
      (markovTrajectoryCost m ρ r T (feedback ⟨m, hm⟩)
          (trajectory ⟨m, hm⟩ x T) = optimalValue m ρ r x T ∧
        ∀ (π : BorelMarkovFeedback ℝ ℝ) (xcompetitor : ℝ → ℝ),
          xcompetitor T = x →
          (∀ s, HasDerivAt xcompetitor
            (-markovFeedbackInput π xcompetitor s) s) →
          Integrable
            (discountedInputCost m ρ r T xcompetitor
              (markovFeedbackInput π xcompetitor))
            (futureLebesgueMeasure T) →
          optimalValue m ρ r x T ≤
            markovTrajectoryCost m ρ r T π xcompetitor) := by
  intro x T
  have h24 := lower_model_theorem24 T
  have h26 := theorem24_to26_gain_control_bridge_all_initial_pairs
    m ρ r hm hρ hr x T
  refine ⟨h24.1, h24.2.2,
    (fun hx => optimalValue_pos_of_nonzero_initial_via_condition24A
      m ρ r x T hm hρ hr hx),
    finiteCostMarkovPZS_iff_mem_zeroTarget m ρ r x T hm hρ hr,
    h26.1, h26.2⟩

/-! ### Direct interface to the general nonnegative-time theorem -/

abbrev GainSourceAbstraction := Bool

abbrev GainSourceState : GainSourceAbstraction → Type
  | false => Unit
  | true => ℝ

abbrev GainSourceFeedback : GainSourceAbstraction → Type
  | false => PUnit
  | true => NonnegativeTimeBorelMarkovFeedback ℝ ℝ

def gainSourcePolicy (a : Gain) : NonnegativeTimeBorelMarkovFeedback ℝ ℝ where
  action := fun p => a.1 * p.2
  measurable_action := by fun_prop

theorem gainSourcePolicy_injective {a b : Gain}
    (h : gainSourcePolicy a = gainSourcePolicy b) : a = b := by
  have hval := congrArg
    (fun ψ : NonnegativeTimeBorelMarkovFeedback ℝ ℝ =>
      ψ.action (⟨⟨0, by norm_num⟩, 1⟩)) h
  apply Subtype.ext
  simpa [gainSourcePolicy] using hval

def gainSourceAdmissible (π : NonnegativeTimeBorelMarkovFeedback ℝ ℝ)
    (_x : ℝ) (_T : ℝ) : Prop :=
  ∃ a : Gain, π = gainSourcePolicy a

noncomputable def gainSourcePolicyGain (m : ℝ) (hm : 0 < m)
    (π : NonnegativeTimeBorelMarkovFeedback ℝ ℝ) : Gain :=
  if h : 0 < π.action (⟨⟨0, by norm_num⟩, 1⟩) then
    ⟨π.action (⟨⟨0, by norm_num⟩, 1⟩), h⟩
  else ⟨m, hm⟩

theorem gainSourcePolicyGain_eq (m : ℝ) (hm : 0 < m)
    (π : NonnegativeTimeBorelMarkovFeedback ℝ ℝ) (x T : ℝ)
    (hπ : gainSourceAdmissible π x T) :
    gainSourcePolicyGain m hm π = Classical.choose hπ := by
  change ∃ a : Gain, π = gainSourcePolicy a at hπ
  have hpolicy : π = gainSourcePolicy (Classical.choose hπ) :=
    Classical.choose_spec hπ
  have hval : π.action (⟨⟨0, by norm_num⟩, 1⟩) = (Classical.choose hπ).1 := by
    have h := congrArg (fun ψ : NonnegativeTimeBorelMarkovFeedback ℝ ℝ =>
      ψ.action (⟨⟨0, by norm_num⟩, 1⟩)) hpolicy
    simpa [gainSourcePolicy] using h
  have hpos : 0 < π.action (⟨⟨0, by norm_num⟩, 1⟩) := by
    rw [hval]
    exact (Classical.choose hπ).2
  unfold gainSourcePolicyGain
  rw [dif_pos hpos]
  apply Subtype.ext
  exact hval

theorem gainSourcePolicyGain_of_policy (m : ℝ) (hm : 0 < m)
    (a : Gain) : gainSourcePolicyGain m hm (gainSourcePolicy a) = a := by
  have hval : (gainSourcePolicy a).action (⟨⟨0, by norm_num⟩, 1⟩) = a.1 := by
    simp [gainSourcePolicy]
  have hpos : 0 < (gainSourcePolicy a).action (⟨⟨0, by norm_num⟩, 1⟩) := by
    rw [hval]
    exact a.2
  unfold gainSourcePolicyGain
  rw [dif_pos hpos]
  apply Subtype.ext
  exact hval

noncomputable def gainSourceTrajectory (m : ℝ) (hm : 0 < m) :
    (a : GainSourceAbstraction) → GainSourceFeedback a → GainSourceState a →
      ℝ → ℝ → GainSourceState a
  | false, _, x, _, _ => x
  | true, π, x, T, s => trajectory (gainSourcePolicyGain m hm π) x T s

def gainSourceRunningCost (m ρ r : ℝ) :
    (a : GainSourceAbstraction) → GainSourceFeedback a →
      GainSourceState a → ℝ → ℝ
  | false, _, _, _ => 1
  | true, π, x, t => inputRunningCost m ρ r x
      (π.action (⟨⟨max t 0, le_max_right t 0⟩, x⟩))

noncomputable def gainSourceOptimalValue (m ρ r : ℝ) :
    (a : GainSourceAbstraction) → GainSourceState a → ℝ → ℝ
  | false, _, _ => ρ⁻¹
  | true, x, T => optimalValue m ρ r x T

def gainSourceOptimalPolicy (m : ℝ) (hm : 0 < m) :
    (a : GainSourceAbstraction) → (x : GainSourceState a) → ℝ → GainSourceFeedback a
  | false, _, _ => PUnit.unit
  | true, _, _ => gainSourcePolicy ⟨m, hm⟩

def gainSourceIsAdmissible : (a : GainSourceAbstraction) →
    GainSourceFeedback a → GainSourceState a → ℝ → Prop
  | false, _, _, _ => True
  | true, π, x, T => gainSourceAdmissible π x T

theorem gainSourceLowerIntegrand_integrable (ρ T : ℝ) (hρ : 0 < ρ) :
    Integrable (theorem26DiscountWeight ρ T) (futureLebesgueMeasure T) := by
  change IntegrableOn (theorem26DiscountWeight ρ T) (Set.Ici T) volume
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-ρ * s)) (Set.Ioi T) :=
    integrableOn_exp_mul_Ioi (by linarith) T
  have hbaseIci : IntegrableOn (fun s : ℝ => Real.exp (-ρ * s)) (Set.Ici T) :=
    integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.2 hbase
  have hscaled : IntegrableOn
      (fun s : ℝ => Real.exp (ρ * T) * Real.exp (-ρ * s)) (Set.Ici T) :=
    hbaseIci.const_mul (Real.exp (ρ * T))
  have heq : (fun s => theorem26DiscountWeight ρ T s) =ᵐ[
      volume.restrict (Set.Ici T)]
      (fun s => Real.exp (ρ * T) * Real.exp (-ρ * s)) := by
    filter_upwards with s
    rw [theorem26DiscountWeight, show -ρ * (s - T) = ρ * T + (-ρ * s) by ring,
      Real.exp_add]
  exact hscaled.congr heq.symm

theorem gainSourceLowerValue_integral (ρ T : ℝ) (hρ : 0 < ρ) :
    ρ⁻¹ = ∫ s, theorem26DiscountWeight ρ T s ∂futureLebesgueMeasure T := by
  simpa [theorem26DiscountWeight] using (future_exp_integral hρ T).symm

theorem gainSourceIntegrand_eq_gainIntegrand (m ρ r : ℝ) (hm : 0 < m)
    (a : Gain) (π : NonnegativeTimeBorelMarkovFeedback ℝ ℝ)
    (hπ : π = gainSourcePolicy a) (x T s : ℝ)
    (hT : 0 ≤ T) (hTs : T ≤ s) :
    theorem26DiscountWeight ρ T s *
        gainSourceRunningCost m ρ r true π
          (gainSourceTrajectory m hm true π x T s) s =
      discountedIntegrand m ρ r a x T s := by
  have hs : 0 ≤ s := le_trans hT hTs
  have htrajectory :
      gainSourceTrajectory m hm true π x T s = trajectory a x T s := by
    rw [hπ]
    simp [gainSourceTrajectory, gainSourcePolicyGain_of_policy]
  rw [htrajectory, hπ]
  unfold gainSourceRunningCost inputRunningCost discountedIntegrand
  simp [gainSourcePolicy, max_eq_left hs, runningCost, controlOutput_eq,
    trajectory]

noncomputable def gainSourceData (m ρ r : ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hr : 0 < r) :
    Theorem24NonnegativeTimeData GainSourceState GainSourceFeedback where
  rho := ρ
  rho_pos := hρ
  trajectory := gainSourceTrajectory m hm
  runningCost := gainSourceRunningCost m ρ r
  admissible := gainSourceIsAdmissible
  optimalValue := gainSourceOptimalValue m ρ r
  optimalPolicy := gainSourceOptimalPolicy m hm
  trajectory_initial := by
    intro a π x T hT hπ
    cases a with
    | false => rfl
    | true =>
        change gainSourceAdmissible π x T at hπ
        rcases hπ with ⟨g, hπ⟩
        rw [hπ, gainSourceTrajectory, gainSourcePolicyGain_of_policy]
        simp [trajectory, Tomabechi.Theorem24_26_LinearFamily.flow]
  runningCost_nonnegative := by
    intro a π x t
    cases a with
    | false => norm_num [gainSourceRunningCost]
    | true =>
        unfold gainSourceRunningCost inputRunningCost
        positivity
  measurable_cost := by
    intro a x T π hT hπ
    cases a with
    | false => fun_prop [gainSourceRunningCost, theorem26DiscountWeight]
    | true =>
        let g := gainSourcePolicyGain m hm π
        have htraj : Measurable (fun s : ℝ => trajectory g x T s) := by
          unfold trajectory Tomabechi.Theorem24_26_LinearFamily.flow
          fun_prop
        have hcontrol : Measurable (fun s : ℝ =>
            π.action (⟨⟨max s 0, le_max_right s 0⟩, trajectory g x T s⟩)) := by
          apply π.measurable_action.comp
          fun_prop
        change Measurable (fun s => ENNReal.ofReal
          (theorem26DiscountWeight ρ T s *
            gainSourceRunningCost m ρ r true π
              (gainSourceTrajectory m hm true π x T s) s))
        simp only [gainSourceTrajectory, gainSourceRunningCost, inputRunningCost]
        fun_prop [theorem26DiscountWeight]
  optimal_cost_integrable := by
    intro a x T hT
    cases a with
    | false =>
        simpa [gainSourceRunningCost, gainSourceTrajectory,
          gainSourceOptimalPolicy] using gainSourceLowerIntegrand_integrable ρ T hρ
    | true =>
        have hbase := Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand_integrable
          m ρ (r * m * (m + ρ) + r * m ^ 2) x T hm hρ
        have hEq : (fun s => Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand
              m ρ (r * m * (m + ρ) + r * m ^ 2) x T s) =ᵐ[
                futureLebesgueMeasure T]
            (fun s => theorem26DiscountWeight ρ T s *
              gainSourceRunningCost m ρ r true (gainSourcePolicy ⟨m, hm⟩)
                (gainSourceTrajectory m hm true (gainSourcePolicy ⟨m, hm⟩) x T s) s) := by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
          have hs' : T ≤ s := hs
          have hsource := gainSourceIntegrand_eq_gainIntegrand
            m ρ r hm ⟨m, hm⟩ (gainSourcePolicy ⟨m, hm⟩) rfl x T s hT hs'
          calc
            _ = discountedIntegrand m ρ r ⟨m, hm⟩ x T s :=
              (discountedIntegrand_eq_linearFamily m ρ r ⟨m, hm⟩ x T s).symm
            _ = _ := hsource.symm
        exact hbase.congr hEq
  optimal_policy_admissible := by
    intro a x T hT
    cases a with
    | false => trivial
    | true => exact ⟨⟨m, hm⟩, rfl⟩
  optimal_value_attained := by
    intro a x T hT
    cases a with
    | false =>
        simpa [gainSourceOptimalValue, gainSourceRunningCost,
          gainSourceOptimalPolicy, gainSourceTrajectory] using
          (gainSourceLowerValue_integral ρ T hρ)
    | true =>
        simp only [gainSourceOptimalValue, gainSourceOptimalPolicy]
        change optimalValue m ρ r x T =
          ∫ s, theorem26DiscountWeight ρ T s *
            gainSourceRunningCost m ρ r true (gainSourcePolicy ⟨m, hm⟩)
              (gainSourceTrajectory m hm true (gainSourcePolicy ⟨m, hm⟩) x T s) s
              ∂futureLebesgueMeasure T
        have hcost : (fun s => theorem26DiscountWeight ρ T s *
            gainSourceRunningCost m ρ r true (gainSourcePolicy ⟨m, hm⟩)
              (gainSourceTrajectory m hm true (gainSourcePolicy ⟨m, hm⟩) x T s) s) =ᵐ[
                futureLebesgueMeasure T]
              discountedIntegrand m ρ r ⟨m, hm⟩ x T := by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
          have hs' : T ≤ s := hs
          exact gainSourceIntegrand_eq_gainIntegrand m ρ r hm ⟨m, hm⟩
            (gainSourcePolicy ⟨m, hm⟩) rfl x T s hT hs'
        rw [integral_congr_ae hcost]
        simpa [policyValue, optimalValue] using
          (optimalGain_attains m ρ r x T hm hρ hr).symm
  optimal_value_minimal := by
    intro a x T π hT hπ
    cases a with
    | false =>
        simp only [gainSourceOptimalValue, gainSourceRunningCost,
          gainSourceTrajectory] at ⊢
        have hI := gainSourceLowerIntegrand_integrable ρ T hρ
        have hnonneg : 0 ≤ᵐ[futureLebesgueMeasure T]
            theorem26DiscountWeight ρ T := by
          filter_upwards with s
          exact (Real.exp_pos _).le
        have hlin := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI hnonneg
        calc
          ENNReal.ofReal (ρ⁻¹) = ENNReal.ofReal
              (∫ s, theorem26DiscountWeight ρ T s ∂futureLebesgueMeasure T) := by
                exact congrArg ENNReal.ofReal (gainSourceLowerValue_integral ρ T hρ)
          _ = ∫⁻ s, ENNReal.ofReal (theorem26DiscountWeight ρ T s)
                ∂futureLebesgueMeasure T := hlin
          _ ≤ ∫⁻ s, ENNReal.ofReal (theorem26DiscountWeight ρ T s * 1)
                ∂futureLebesgueMeasure T := by
                  apply MeasureTheory.lintegral_mono_ae
                  filter_upwards with s
                  rw [mul_one]
    | true =>
        simp only [gainSourceOptimalValue]
        change gainSourceAdmissible π x T at hπ
        rcases hπ with ⟨g, hpolicy⟩
        have hcost : (fun s => theorem26DiscountWeight ρ T s *
            gainSourceRunningCost m ρ r true π
              (gainSourceTrajectory m hm true π x T s) s) =ᵐ[
                futureLebesgueMeasure T]
              discountedIntegrand m ρ r g x T := by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
          have hs' : T ≤ s := hs
          exact gainSourceIntegrand_eq_gainIntegrand m ρ r hm g π hpolicy
            x T s hT hs'
        have hI := Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand_integrable
          g.1 ρ (r * m * (m + ρ) + r * g.1 ^ 2) x T g.2 hρ
        have hEqLinear : (fun s =>
            Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand g.1 ρ
              (r * m * (m + ρ) + r * g.1 ^ 2) x T s) =ᵐ[
                futureLebesgueMeasure T]
            (fun s => theorem26DiscountWeight ρ T s *
              gainSourceRunningCost m ρ r true π
                (gainSourceTrajectory m hm true π x T s) s) := by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
          have hs' : T ≤ s := hs
          calc
            _ = discountedIntegrand m ρ r g x T s :=
              (discountedIntegrand_eq_linearFamily m ρ r g x T s).symm
            _ = _ := (gainSourceIntegrand_eq_gainIntegrand m ρ r hm g π
              hpolicy x T s hT hs').symm
        have hsourceI : Integrable
            (fun s => theorem26DiscountWeight ρ T s *
              gainSourceRunningCost m ρ r true π
                (gainSourceTrajectory m hm true π x T s) s)
            (futureLebesgueMeasure T) := by
          exact hI.congr hEqLinear
        have hsourceNonnegative :
            0 ≤ᵐ[futureLebesgueMeasure T]
              (fun s => theorem26DiscountWeight ρ T s *
                gainSourceRunningCost m ρ r true π
                  (gainSourceTrajectory m hm true π x T s) s) := by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
          have hrun : 0 ≤ gainSourceRunningCost m ρ r true π
              (gainSourceTrajectory m hm true π x T s) s := by
            unfold gainSourceRunningCost inputRunningCost
            positivity
          apply mul_nonneg
          · exact (Real.exp_pos _).le
          · exact hrun
        have hlin := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          hsourceI hsourceNonnegative
        have hreal : optimalValue m ρ r x T ≤ policyValue m ρ r g x T :=
          by
            have hmin := optimalGain_is_minimal m ρ r g.1 x T hm hρ hr g.2
            rw [optimalGain_attains m ρ r x T hm hρ hr] at hmin
            simpa [optimalValue] using hmin
        calc
          ENNReal.ofReal (optimalValue m ρ r x T) ≤
              ENNReal.ofReal (policyValue m ρ r g x T) :=
            ENNReal.ofReal_le_ofReal hreal
          _ = ENNReal.ofReal (∫ s, theorem26DiscountWeight ρ T s *
                gainSourceRunningCost m ρ r true π
                  (gainSourceTrajectory m hm true π x T s) s
                  ∂(futureLebesgueMeasure T)) := by
              congr 1
              unfold policyValue
              exact integral_congr_ae hcost.symm
          _ = ∫⁻ s, ENNReal.ofReal (theorem26DiscountWeight ρ T s *
                gainSourceRunningCost m ρ r true π
                  (gainSourceTrajectory m hm true π x T s) s)
                ∂(futureLebesgueMeasure T) := hlin
  condition24A := by
    intro a ha x T hT π hπ
    cases a with
    | false =>
        simpa [gainSourceRunningCost, gainSourceTrajectory, lowerRunningCost] using
          lower_condition24A () T
    | true => exact (lt_irrefl (⊤ : GainSourceAbstraction) ha).elim

@[simp] theorem gainSourceData_top_optimalValue (m ρ r : ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hr : 0 < r) (x T : ℝ) :
    (gainSourceData m ρ r hm hρ hr).optimalValue (⊤ : GainSourceAbstraction) x T =
      optimalValue m ρ r x T := rfl

theorem gainSourceData_top_optimalTrajectory (m ρ r : ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hr : 0 < r) (x T s : ℝ) :
    (gainSourceData m ρ r hm hρ hr).trajectory (⊤ : GainSourceAbstraction)
      (gainSourcePolicy ⟨m, hm⟩) x T s = trajectory ⟨m, hm⟩ x T s := by
  simp [gainSourceData, gainSourceTrajectory, gainSourcePolicyGain_of_policy]

theorem gainSourceData_true_optimalTrajectory (m ρ r : ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hr : 0 < r) (x T s : ℝ) :
    (gainSourceData m ρ r hm hρ hr).trajectory true
      (gainSourcePolicy ⟨m, hm⟩) x T s = trajectory ⟨m, hm⟩ x T s := by
  simpa [GainSourceAbstraction] using
    gainSourceData_top_optimalTrajectory m ρ r hm hρ hr x T s

theorem gainSourceData_target_eq (m ρ r : ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hr : 0 < r) (T : ℝ) :
    theorem26ZeroValueTarget Set.univ
      ((gainSourceData m ρ r hm hρ hr).optimalValue ⊤) T =
        Tomabechi.Theorem24_26_LinearFamily.zeroTarget m ρ
          (r * m * (m + ρ) + r * m ^ 2) T := by
  have hq : 0 < r * m * (m + ρ) + r * m ^ 2 := by positivity
  rw [Tomabechi.Theorem24_26_LinearFamily.zeroTarget_eq_singleton
    m ρ (r * m * (m + ρ) + r * m ^ 2) T hm hρ hq]
  ext x
  simp only [theorem26ZeroValueTarget, Set.mem_inter_iff, Set.mem_univ,
    true_and, Set.mem_setOf_eq, gainSourceData_top_optimalValue]
  simp [optimalValue, (mul_pos hr hm).ne']

local instance gainSourceTopPseudoMetric :
    PseudoMetricSpace (GainSourceState (⊤ : GainSourceAbstraction)) :=
  Real.pseudoMetricSpace

local instance gainSourceTopMeasurableSpace :
    MeasurableSpace (GainSourceState (⊤ : GainSourceAbstraction)) := by
  change MeasurableSpace ℝ
  infer_instance

local instance gainSourceTopBorelSpace :
    BorelSpace (GainSourceState (⊤ : GainSourceAbstraction)) := by
  change BorelSpace ℝ
  infer_instance

local instance gainSourceTopProductBorelSpace :
    BorelSpace (Set.Ici (0 : ℝ) ×
      GainSourceState (⊤ : GainSourceAbstraction)) := by
  change BorelSpace (Set.Ici (0 : ℝ) × ℝ)
  infer_instance

theorem gainSourceNormedMetric_eq_real :
    SeminormedAddCommGroup.toPseudoMetricSpace (E := ℝ) =
      Real.pseudoMetricSpace := by
  apply PseudoMetricSpace.ext
  ext x y
  simp [Real.dist_eq]

set_option maxHeartbeats 400000 in
noncomputable def gainSourceDynamics (m ρ r : ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hr : 0 < r) :
    Theorem26NonnegativeTimeDynamics
      (gainSourceData m ρ r hm hρ hr) ℝ where
  policyEquiv := Equiv.refl _
  feedback := gainSourcePolicy ⟨m, hm⟩
  alive := Set.univ
  feedback_attains_optimum := by
    intro x T hT hx
    have hEq : gainSourceOptimalPolicy m hm
        (⊤ : GainSourceAbstraction) x T = gainSourcePolicy ⟨m, hm⟩ := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [← hEq]
      exact (gainSourceData m ρ r hm hρ hr).optimal_policy_admissible
        (⊤ : GainSourceAbstraction) x T hT
    · rw [← hEq]
      exact (gainSourceData m ρ r hm hρ hr).optimal_cost_integrable
        (⊤ : GainSourceAbstraction) x T hT
    · rw [← hEq]
      exact (gainSourceData m ρ r hm hρ hr).optimal_value_attained
        (⊤ : GainSourceAbstraction) x T hT
  W := fun x _ => x ^ 2
  ω := fun d => (r * m) * d ^ 2
  c₁ := 1
  c₂ := 1
  rate := 2 * m
  c₁_pos := by norm_num
  c₂_pos := by norm_num
  rate_pos := by positivity
  trajectory_alive := by intro x T s hT hx hTs; exact Set.mem_univ _
  target_nonempty := by
    intro T hT
    have hq : 0 < r * m * (m + ρ) + r * m ^ 2 := by positivity
    rw [gainSourceData_target_eq m ρ r hm hρ hr,
      zeroTarget_eq_singleton m ρ (r * m * (m + ρ) + r * m ^ 2)
        T hm hρ hq]
    exact Set.singleton_nonempty 0
  target_closed := by
    intro T hT
    have hq : 0 < r * m * (m + ρ) + r * m ^ 2 := by positivity
    rw [gainSourceData_target_eq m ρ r hm hρ hr,
      zeroTarget_eq_singleton m ρ (r * m * (m + ρ) + r * m ^ 2)
        T hm hρ hq]
    exact isClosed_singleton
  target_invariant := by
    intro x T s hT hmem hTs
    have hq : 0 < r * m * (m + ρ) + r * m ^ 2 := by positivity
    rw [gainSourceData_target_eq m ρ r hm hρ hr,
      zeroTarget_eq_singleton m ρ (r * m * (m + ρ) + r * m ^ 2)
        T hm hρ hq] at hmem
    have hx : x = 0 := by simpa using hmem
    rw [gainSourceData_target_eq m ρ r hm hρ hr,
      zeroTarget_eq_singleton m ρ (r * m * (m + ρ) + r * m ^ 2)
        s hm hρ hq]
    rw [gainSourceData_top_optimalTrajectory m ρ r hm hρ hr x T s]
    simp [trajectory, Tomabechi.Theorem24_26_LinearFamily.flow, hx]
  W_absolutelyContinuous := by
    intro x T s hT hx hTs
    have hregular : ContDiffOn ℝ 1
        (Tomabechi.Theorem24_26_LinearFamily.WAlong m x T) (Set.uIcc T s) := by
      have hglobal : ContDiff ℝ 1
          (Tomabechi.Theorem24_26_LinearFamily.WAlong m x T) := by
        unfold Tomabechi.Theorem24_26_LinearFamily.WAlong
          Tomabechi.Theorem24_26_LinearFamily.flow
        fun_prop
      exact hglobal.contDiffOn
    have hac := hregular.absolutelyContinuousOnInterval
    rw [gainSourceNormedMetric_eq_real] at hac
    convert hac using 1
    funext u
    rw [gainSourceData_top_optimalTrajectory m ρ r hm hρ hr x T u]
    rfl
  W_nonnegative := by
    intro x T s hT hx hTs
    rw [gainSourceData_top_optimalTrajectory]
    exact sq_nonneg _
  W_rightSlope := by
    intro x T u hT hx hTu
    have hpath : (fun s =>
        (gainSourceData m ρ r hm hρ hr).trajectory ⊤
          (gainSourcePolicy ⟨m, hm⟩) x T s ^ 2) =
        Tomabechi.Theorem24_26_LinearFamily.WAlong m x T := by
      funext s
      rw [gainSourceData_top_optimalTrajectory m ρ r hm hρ hr x T s]
      rfl
    rw [hpath]
    rw [gainSourceData_top_optimalTrajectory m ρ r hm hρ hr x T u]
    apply Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
      (Tomabechi.Theorem24_26_LinearFamily.WAlong m x T) u
      (-(2 * m) * Tomabechi.Theorem24_26_LinearFamily.WAlong m x T u)
      (-(2 * m) * Tomabechi.Theorem24_26_LinearFamily.WAlong m x T u)
    · convert Tomabechi.Theorem24_26_LinearFamily.WAlong_hasDerivAt
        m x T u using 1 <;> ring
    · exact le_rfl
  W_lower_distance_bound := by
    intro x T s hT hx hTs
    have hq : 0 < r * m * (m + ρ) + r * m ^ 2 := by positivity
    rw [gainSourceData_top_optimalTrajectory,
      gainSourceData_target_eq m ρ r hm hρ hr,
      zeroTarget_eq_singleton m ρ (r * m * (m + ρ) + r * m ^ 2)
        s hm hρ hq,
      Metric.infDist_singleton]
    simp [Real.dist_eq, sq_abs]
  W_upper_distance_bound := by
    intro x T s hT hx hTs
    have hq : 0 < r * m * (m + ρ) + r * m ^ 2 := by positivity
    rw [gainSourceData_top_optimalTrajectory,
      gainSourceData_target_eq m ρ r hm hρ hr,
      zeroTarget_eq_singleton m ρ (r * m * (m + ρ) + r * m ^ 2)
        s hm hρ hq,
      Metric.infDist_singleton]
    simp [Real.dist_eq, sq_abs]
  ω_continuous := by fun_prop
  ω_zero := by simp
  ω_nonnegative := by intro d hd; positivity
  ω_monotone_on_nonnegative := by
    intro d₁ d₂ hd₁ hd₁₂
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hr.le hm.le)
    nlinarith [sq_nonneg (d₂ - d₁)]
  value_distance_bound := by
    intro y t ht hy
    have hq : 0 < r * m * (m + ρ) + r * m ^ 2 := by positivity
    rw [gainSourceData_top_optimalValue,
      gainSourceData_target_eq m ρ r hm hρ hr,
      zeroTarget_eq_singleton m ρ (r * m * (m + ρ) + r * m ^ 2)
        t hm hρ hq,
      Metric.infDist_singleton]
    constructor
    · exact mul_nonneg (mul_nonneg hr.le hm.le) (sq_nonneg y)
    · simp [optimalValue, Real.dist_eq, sq_abs]

/-- Direct application of the general source-time theorem to the continuous
positive-gain model. The result contains lower-layer theorem 24 positivity
and PZS exclusion, upper-layer PZS classification, quantitative exponential
convergence, zero-set equivalence, and forward invariance. -/
def gainSource_general_bridge (m ρ r : ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hr : 0 < r) :=
  theorem24_to26_from_nonnegativeTimeData
    (gainSourceData m ρ r hm hρ hr)
    (gainSourceDynamics m ρ r hm hρ hr)

end Tomabechi.Theorem24_26_GainControl
