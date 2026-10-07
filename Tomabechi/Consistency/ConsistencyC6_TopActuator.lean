import Tomabechi.Consistency.ConsistencyC6_SharedExperiment

/-!
# C6：同じ層別D/Eの頂点から得る27-Aの全運用入力

有限層はC1二主体状態、頂点はC5 Euclidean状態という依存型を保持する。
既存27運用入口はこの依存型を受け取れるので、同じD/Eから全入力を構成する。
基準入力・自然ドリフトは全状態上の固定した場であり、軌道ごとに相殺則を変えない。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Examples.Theorem27
open Tomabechi.Examples.Theorem27Op
open Tomabechi.Theorem24_26
open Tomabechi.Theorem24_26_Model
open Tomabechi.Theorem24_26_27
open MeasureTheory Filter
open scoped Topology

abbrev C6TopState := Tomabechi.Examples.Theorem27Op.E2

def c6TopPath (x : C6TopState) (T t : ℝ) : C6TopState :=
  c6CommonLayerData.trajectory ⊤ c6CommonLayerDynamics.feedback x T t

def c6TopNaturalDrift (y : C6TopState) : C6TopState := (-mu * y 0) • e0
def c6TopReferenceField (y : C6TopState) : C6TopState := (mu * y 0) • e0 + omg • e1
def c6TopGradientField (y : C6TopState) : C6TopState := (2 * y 0) • e0
def c6TopAllowedInput : Set C6TopState := Set.univ

theorem c6TopPath_eq_flow (x : C6TopState) (T t : ℝ) (hT : 0 ≤ T) (ht : T ≤ t) :
    c6TopPath x T t = flowE x T t :=
  vectorSourceDataTrajectory_eq_flowE x T t hT ht

/-- 27-A2の相殺は全状態で成立するので、各軌道点の近傍にも同じ場を使う。 -/
theorem c6Top_referenceCancellation_all_states (y : C6TopState) :
    inner ℝ (c6TopGradientField y) (c6TopNaturalDrift y + GE (c6TopReferenceField y)) = 0 :=
  Tomabechi.Consistency.C5.reference_cancellation_on_neighborhood y

theorem c6Top_reference_on_path (x : C6TopState) (T t : ℝ) (hT : 0 ≤ T) (ht : T ≤ t) :
    c6TopReferenceField (c6TopPath x T t) = utrE x T t := by
  rw [c6TopPath_eq_flow x T t hT ht]
  exact Tomabechi.Consistency.C5.reference_law_on_flow x T t

theorem c6Top_drift_on_path (x : C6TopState) (T t : ℝ) (hT : 0 ≤ T) (ht : T ≤ t) :
    c6TopNaturalDrift (c6TopPath x T t) = driftE x T t := by
  rw [c6TopPath_eq_flow x T t hT ht]
  exact Tomabechi.Consistency.C5.natural_drift_on_flow x T t

/-- 共通Eが実際に実行するfeedbackの入力を元27のu0へ同定する。 -/
theorem c6Top_feedback_input (x : C6TopState) (T t : ℝ) (hT : 0 ≤ T) (ht : T ≤ t) :
    u0E x T t = (c6CommonLayerDynamics.policyEquiv c6CommonLayerDynamics.feedback).action
      ⟨⟨t, hT.trans ht⟩, c6TopPath x T t⟩ := by
  rw [c6TopPath_eq_flow x T t hT ht]
  change u0E x T t = vectorMaximalPolicy.action ⟨⟨t, hT.trans ht⟩, flowE x T t⟩
  calc
    _ = measurableGainInput
        Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain t
          (flowE x T t 0) := (maximal_measurable_input_eq_u0E x T t).symm
    _ = _ := (measurableGainVectorPolicy_action
      Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain
      ⟨t, hT.trans ht⟩ (flowE x T t)).symm

/-- 同じD/Eの頂点を参照する全運用入力の証拠。dW/grad/u0は元27のものを保持する。 -/
structure C6TopActuatorInputs (x : C6TopState) (T : ℝ) (hT : 0 ≤ T) : Prop where
  restart : ∀ (y : C6TopState) (a s t : ℝ), 0 ≤ a → a ≤ s → s ≤ t →
    c6TopPath (c6TopPath y a s) s t = c6TopPath y a t
  ode : ∀ᵐ t ∂futureLebesgueMeasure T,
    HasDerivAt (c6TopPath x T) (driftE x T t + GE (u0E x T t)) t
  state_gradient : ∀ t z, dWE x T t (0, z) = inner ℝ (gradWE x T t) z
  reference_cancellation : ∀ t,
    dWE x T t (1, 0) + inner ℝ (gradWE x T t) (driftE x T t + GE (utrE x T t)) = 0
  residual_locally_lipschitz : LocallyLipschitzOn (Set.Ici T)
    (fun s => c6CommonLayerDynamics.W (c6TopPath x T s) s)
  w_derivative : ∀ᵐ t ∂futureLebesgueMeasure T,
    HasFDerivAt (fun p : ℝ × C6TopState => c6CommonLayerDynamics.W p.2 p.1)
      (dWE x T t) (t, c6TopPath x T t)
  w_contDiff : ContDiff ℝ 1 (fun p : ℝ × C6TopState => c6CommonLayerDynamics.W p.2 p.1)
  adjoint_bound : ∀ᵐ t ∂futureLebesgueMeasure T, ∀ v : C6TopState,
    |inner ℝ (gradWE x T t) (GE v)| ≤ (2 * |x 0| + 1) * ‖v‖
  feedback_input : ∀ t (ht : T ≤ t), u0E x T t =
    (c6CommonLayerDynamics.policyEquiv c6CommonLayerDynamics.feedback).action
      ⟨⟨t, hT.trans ht⟩, c6TopPath x T t⟩
  drift_field : ∀ t, T ≤ t → c6TopNaturalDrift (c6TopPath x T t) = driftE x T t
  reference_field : ∀ t, T ≤ t → c6TopReferenceField (c6TopPath x T t) = utrE x T t
  neighborhood_cancellation : ∀ y, inner ℝ (c6TopGradientField y)
    (c6TopNaturalDrift y + GE (c6TopReferenceField y)) = 0
  actuator_difference_measurable : Measurable (fun t : Set.Ici T =>
    GE (u0E x T t.1 - c6TopReferenceField (c6TopPath x T t.1)))
  reference_allowed : ∀ y, c6TopReferenceField y ∈ c6TopAllowedInput
  actual_allowed : ∀ t, T ≤ t → u0E x T t ∈ c6TopAllowedInput

/-- 外部から未充足の入力条件を受け取らず、全初期状態・開始時刻で構成する。 -/
theorem c6TopActuatorInputs (x : C6TopState) (T : ℝ) (hT : 0 ≤ T) :
    C6TopActuatorInputs x T hT := by
  refine {
    restart := ?_
    ode := ?_
    state_gradient := stateGrad x T
    reference_cancellation := reference_cancellation x T
    residual_locally_lipschitz := ?_
    w_derivative := ?_
    w_contDiff := Tomabechi.Consistency.C5.W_is_contDiff
    adjoint_bound := ?_
    feedback_input := fun t ht => c6Top_feedback_input x T t hT ht
    drift_field := fun t ht => c6Top_drift_on_path x T t hT ht
    reference_field := fun t ht => c6Top_reference_on_path x T t hT ht
    neighborhood_cancellation := c6Top_referenceCancellation_all_states
    actuator_difference_measurable := ?_
    reference_allowed := fun _ => Set.mem_univ _
    actual_allowed := fun _ _ => Set.mem_univ _ }
  · intro y a s t ha has hst
    rw [c6TopPath_eq_flow y a s ha has,
      c6TopPath_eq_flow _ s t (ha.trans has) hst,
      c6TopPath_eq_flow y a t ha (has.trans hst)]
    exact flowE_semigroup y a s t
  · letI : NullSingletonClass (futureLebesgueMeasure T) := by
      unfold futureLebesgueMeasure
      infer_instance
    filter_upwards [Measure.ae_ne (futureLebesgueMeasure T) T,
      ae_restrict_mem (μ := volume) measurableSet_Ici] with t hne ht
    have hlt : T < t := lt_of_le_of_ne ht hne.symm
    apply (hasDerivAt_flowE x T t).congr_of_eventuallyEq
    filter_upwards [Ici_mem_nhds hlt] with s hs
    exact c6TopPath_eq_flow x T s hT hs
  · intro t ht
    obtain ⟨K, U, hU, hLip⟩ := locallyLipschitz_W x T ht
    refine ⟨K, U ∩ Set.Ici T, Filter.inter_mem hU self_mem_nhdsWithin, ?_⟩
    intro a ha b hb
    change edist (W3 (c6TopPath x T a) a) (W3 (c6TopPath x T b) b) ≤ _
    rw [c6TopPath_eq_flow x T a hT ha.2, c6TopPath_eq_flow x T b hT hb.2]
    exact hLip ha.1 hb.1
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with t ht
    rw [c6TopPath_eq_flow x T t hT ht]
    exact hasFDerivAt_W x T t
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with t ht v
    rw [show GE v = v from rfl, inner_gradWE]
    have hr : |flow (x 0) T t| ≤ |x 0| := by
      unfold flow
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (T - t) ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr ht)
      nlinarith [abs_nonneg (x 0)]
    have hv : |v 0| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v 0
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg (v 0), abs_nonneg (flow (x 0) T t), norm_nonneg v,
      mul_le_mul hr hv (abs_nonneg _) (abs_nonneg _)]
  · have heq : (fun t : Set.Ici T => GE (u0E x T t.1 -
        c6TopReferenceField (c6TopPath x T t.1))) =
        fun t : Set.Ici T => GE (u0E x T t.1 - utrE x T t.1) := by
      funext t
      rw [c6Top_reference_on_path x T t.1 hT t.2]
    rw [heq]
    unfold u0E utrE GE flow
    fun_prop

/-- 同じ共通D/Eを既存の依存層状態型を許す27運用入口へ直接渡す。
結論の移送だけでなく、全入力を今回構成した証拠から供給する。 -/
theorem c6CommonLayerData_theorem27_from_topInputs
    (x : C6TopState) (T : ℝ) (hT : 0 ≤ T) : c6LayeredTheorem27Conclusion x T hT := by
  have P := c6TopActuatorInputs x T hT
  have hK := theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae
    (A := CommonLayer) (State := C6LayeredState) (Feedback := C6LayeredPolicy)
    (Control := C6TopState) rfl rfl
    c6CommonLayerData c6CommonLayerDynamics x T hT (Set.mem_univ x)
    (fun y a s t ha has hst _ => P.restart y a s t ha has hst)
    (dWE x T) (gradWE x T) (driftE x T) (u0E x T) (utrE x T) (fun _ => GE)
    P.ode (Eventually.of_forall P.state_gradient)
    (Eventually.of_forall P.reference_cancellation)
    P.residual_locally_lipschitz P.w_derivative P.feedback_input
    (2 * |x 0| + 1) (by positivity)
    (by filter_upwards [P.adjoint_bound] with t ht _; exact ht)
  refine ⟨hK.1, ?_, ?_⟩
  · filter_upwards [hK.2.1] with t ht
    intro htt
    rw [vectorSourceReferenceInput_eq_operational x T t hT htt]
    exact ht htt
  · filter_upwards [hK.2.2, ae_restrict_mem (μ := volume) measurableSet_Ici] with t ht htt
    rw [vectorSourceReferenceInput_eq_operational x T t hT htt]
    exact ht

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.c6TopActuatorInputs
#print axioms Tomabechi.Consistency.C6.c6CommonLayerData_theorem27_from_topInputs
