import Theorem22_InvariantRegion
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# H-stage不変領域の範囲拡張を示す一次元モデル

このモデルは一般定理の代替ではない。初期値で定まる全部分準位集合が
局所球の内部障壁を満たさない一方、より小さい前向き不変区間は障壁を
満たす、という入力範囲の差を解析的に確認する。
-/

open RealInnerProductSpace
open MeasureTheory
open scoped Topology

namespace Tomabechi.Theorem22InvariantRegionModel

noncomputable def toyBackground (x : ℝ) : ℝ := x / 2

noncomputable def toyMeanField (x : ℝ) : ℝ := -(x ^ 2) / 2

noncomputable def toyPotential (x : ℝ) : ℝ := toyBackground x - toyMeanField x

def toyInvariantRegion : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

noncomputable def toyClosedLoopField (x : ℝ) : ℝ := -(x + 1 / 2)

theorem toy_initial_mem : (1 / 2 : ℝ) ∈ toyInvariantRegion := by
  norm_num [toyInvariantRegion]

theorem toy_valley_mem : (-(1 / 2 : ℝ)) ∈ toyInvariantRegion := by
  norm_num [toyInvariantRegion]

theorem toy_threshold_strict :
    (1 : ℝ) > max 0 ((1 / 2 : ℝ) / 1) := by
  norm_num

theorem toy_potential_square_completion (x : ℝ) :
    toyPotential x = (x + 1 / 2) ^ 2 / 2 - 1 / 8 := by
  simp [toyPotential, toyBackground, toyMeanField]
  ring

theorem toy_valley_unique_on_unit_ball :
    IsMinOn toyPotential (Metric.closedBall (0 : ℝ) 1) (-(1 / 2 : ℝ)) ∧
      (∀ y ∈ Metric.closedBall (0 : ℝ) 1,
        toyPotential y = toyPotential (-(1 / 2 : ℝ)) → y = -(1 / 2 : ℝ)) := by
  constructor
  · intro y hy
    change toyPotential (-(1 / 2 : ℝ)) ≤ toyPotential y
    rw [toy_potential_square_completion, toy_potential_square_completion]
    nlinarith [sq_nonneg (y + 1 / 2)]
  · intro y hy heq
    rw [toy_potential_square_completion, toy_potential_square_completion] at heq
    nlinarith [sq_nonneg (y + 1 / 2)]

noncomputable def toyAveragePresentation :
    Tomabechi.Theorem22.MeanFieldAveragePresentation ℝ := by
  classical
  refine
    { Atom := Bool
      atomOrder := inferInstance
      abstractTop := true
      abstractTop_greatest := ?_
      sourceLayer := {false}
      abstractTop_not_in_sourceLayer := by simp
      atomTopology := inferInstance
      atomMeasurableSpace := inferInstance
      atomMeasure := Measure.dirac false
      atomMeasure_probability := inferInstance
      measureSupport := {false}
      measureSupport_eq_topological_support := ?_
      measureSupport_measurable := by simp
      measureSupport_full := ?_
      measureSupport_subset_sourceLayer := by simp
      supportLub := false
      supportLub_upper := ?_
      supportLub_least := ?_
      supportLub_mem_sourceLayer := by simp
      centerRepresentation := fun _ => 0
      reconstructionKernel := fun x _ => toyMeanField x
      reconstructionKernel_integrable := ?_ }
  · intro a
    cases a <;> simp
  · ext a
    cases a
    · rw [Measure.mem_support_iff_forall]
      constructor
      · intro _ U hU
        have hfalse : false ∈ U := mem_of_mem_nhds hU
        simp [hfalse]
      · intro _
        simp
    · rw [Measure.mem_support_iff_forall]
      constructor
      · simp
      · intro h
        have hpos := h {true} (by simp)
        norm_num at hpos
  · simp
  · intro a ha
    have : a = false := by simpa using ha
    simpa [this]
  · intro b hb
    simpa using hb false (by simp)
  · intro x
    exact integrable_const _

theorem toy_mean_field_has_average_presentation (x : ℝ) :
    toyMeanField x = toyAveragePresentation.integralValue x := by
  change toyMeanField x = ∫ _ : Bool, toyMeanField x ∂Measure.dirac false
  rw [integral_dirac]

/-- Every differentiable solution of this scalar closed-loop equation that
starts in the interval remains in it for any finite forward time interval. -/
theorem toy_closed_loop_interval_invariant
    (a d : ℝ) (_hd : 0 ≤ d) (orbit : ℝ → ℝ)
    (hinitial : orbit a ∈ toyInvariantRegion)
    (hode : ∀ t ∈ Set.Icc a (a + d),
      HasDerivAt orbit (toyClosedLoopField (orbit t)) t) :
    ∀ t ∈ Set.Icc a (a + d), orbit t ∈ toyInvariantRegion := by
  intro t ht
  let f : ℝ → ℝ := fun s => Real.exp (s - a) * (orbit s + 1 / 2)
  have horbitContinuous : ContinuousOn orbit (Set.Icc a (a + d)) := by
    apply HasDerivAt.continuousOn
    intro s hs
    exact hode s hs
  have hfcont : ContinuousOn f (Set.Icc a (a + d)) := by
    change ContinuousOn (fun s => Real.exp (s - a) * (orbit s + 1 / 2)) _
    exact (continuousOn_id.sub continuousOn_const).rexp |>.mul
      (horbitContinuous.add continuousOn_const)
  have hfderiv : ∀ s ∈ Set.Ico a (a + d),
      HasDerivWithinAt f 0 (Set.Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Set.Icc a (a + d) := ⟨hs.1, hs.2.le⟩
    have hExp : HasDerivAt (fun z : ℝ => Real.exp (z - a))
        (Real.exp (s - a)) s := by
      have hlin : HasDerivAt (fun z : ℝ => z - a) 1 s := by
        simpa using (hasDerivAt_id s).sub_const a
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (s - a)).comp s hlin
    have hOrbit := hode s hsIcc
    have hsum : HasDerivAt (fun z : ℝ => orbit z + 1 / 2)
        (toyClosedLoopField (orbit s)) s := by
      simpa [toyClosedLoopField] using hOrbit.add_const (1 / 2)
    have hprod := hExp.mul hsum
    have hprodZero : HasDerivAt f 0 s := by
      convert hprod using 1 <;> simp [f, toyClosedLoopField] <;> ring
    exact hprodZero.hasDerivWithinAt.mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hconstant := constant_of_has_deriv_right_zero hfcont hfderiv
  have hvalue := hconstant t ht
  have hvalue' : Real.exp (t - a) * (orbit t + 1 / 2) =
      orbit a + 1 / 2 := by
    simpa [f, Real.exp_zero] using hvalue
  have hform : orbit t + 1 / 2 =
      (orbit a + 1 / 2) * Real.exp (-(t - a)) := by
    have hexp : Real.exp (t - a) ≠ 0 := ne_of_gt (Real.exp_pos _)
    calc
      orbit t + 1 / 2 = (orbit a + 1 / 2) / Real.exp (t - a) := by
        apply (eq_div_iff hexp).2
        nlinarith [hvalue']
      _ = (orbit a + 1 / 2) * (Real.exp (t - a))⁻¹ := by ring
      _ = (orbit a + 1 / 2) * Real.exp (-(t - a)) := by
        rw [Real.exp_neg]
  rcases hinitial with ⟨hlo, hhi⟩
  have hfactor_nonneg : 0 ≤ orbit a + 1 / 2 := by linarith
  have hfactor_le : orbit a + 1 / 2 ≤ 1 := by linarith
  have htime_nonneg : 0 ≤ t - a := by linarith [ht.1]
  have hexp_le : Real.exp (-(t - a)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hexp_nonneg : 0 ≤ Real.exp (-(t - a)) := (Real.exp_pos _).le
  constructor
  · linarith [mul_nonneg hfactor_nonneg hexp_nonneg]
  · have hmul : (orbit a + 1 / 2) * Real.exp (-(t - a)) ≤ 1 :=
      calc
        (orbit a + 1 / 2) * Real.exp (-(t - a)) ≤
            1 * Real.exp (-(t - a)) :=
          mul_le_mul_of_nonneg_right hfactor_le hexp_nonneg
        _ ≤ 1 := by simpa using hexp_le
    linarith [hform]

/-- At the initial point `1/2`, the full energy sublevel reaches the boundary
point `-1` of the unit ball, so its closure is not contained in the open ball. -/
theorem toy_initial_sublevel_reaches_ball_boundary :
    toyPotential (-1) ≤ toyPotential (1 / 2) := by
  norm_num [toyPotential, toyBackground, toyMeanField]

theorem toy_old_sublevel_barrier_fails :
    ¬ closure {x : ℝ | x ∈ Metric.closedBall (0 : ℝ) 1 ∧
        toyPotential x ≤ toyPotential (1 / 2)} ⊆ Metric.ball (0 : ℝ) 1 := by
  intro hbarrier
  have hpoint : (-1 : ℝ) ∈
      {x : ℝ | x ∈ Metric.closedBall (0 : ℝ) 1 ∧
        toyPotential x ≤ toyPotential (1 / 2)} := by
    constructor
    · rw [Metric.mem_closedBall, Real.dist_eq]
      norm_num
    · exact toy_initial_sublevel_reaches_ball_boundary
  have hclosure : (-1 : ℝ) ∈ closure
      {x : ℝ | x ∈ Metric.closedBall (0 : ℝ) 1 ∧
        toyPotential x ≤ toyPotential (1 / 2)} := subset_closure hpoint
  have hball : (-1 : ℝ) ∈ Metric.ball (0 : ℝ) 1 := hbarrier hclosure
  rw [Metric.mem_ball, Real.dist_eq] at hball
  norm_num at hball

/-- The selected invariant region is strictly inside the unit ball. -/
theorem toy_invariant_region_closure_inside_ball :
    closure toyInvariantRegion ⊆ Metric.ball (0 : ℝ) 1 := by
  have hclosure : closure toyInvariantRegion = toyInvariantRegion :=
    isClosed_Icc.closure_eq
  rw [hclosure]
  intro x hx
  rw [Metric.mem_ball, Real.dist_eq]
  rcases hx with ⟨hlo, hhi⟩
  rw [abs_lt]
  constructor <;> linarith

noncomputable def toyNegativeIdentity : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ

noncomputable def toyIdentity : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- A complete relaxed H-stage record for the one-dimensional model. -/
noncomputable def toyInvariantRegionStage :
    Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput ℝ := by
  classical
  refine
    { center := 0
      radius := 1
      gain := 1
      presenceGain := 1
      curvature := 1
      backgroundCurvature := 0
      gradientBound := 1 / 2
      gamma := 1
      startTime := 0
      background := toyBackground
      meanField := toyMeanField
      averagePresentation := toyAveragePresentation
      center_eq_supportLub_representation := rfl
      meanField_eq_integral := toy_mean_field_has_average_presentation
      backgroundGradient := fun _ => 1 / 2
      meanFieldGradient := fun x => -x
      backgroundHessian := fun _ => 0
      meanFieldHessian := fun _ => toyNegativeIdentity
      mobility := fun _ => toyIdentity
      sublevel := toyInvariantRegion
      initial := 1 / 2
      radius_pos := by norm_num
      gain_pos := by norm_num
      curvature_pos := by norm_num
      backgroundCurvature_nonneg := by norm_num
      gradientBound_nonneg := by norm_num
      gain_threshold := by norm_num
      background_c2_at := ?_
      meanField_c2_at := ?_
      background_gradient_representation := ?_
      meanField_gradient_representation := ?_
      background_gradient_deriv := ?_
      meanField_gradient_deriv := ?_
      mobility_c1 := ?_
      mobility_symmetric := ?_
      background_hessian_lower := ?_
      meanField_hessian_upper := ?_
      meanField_center_stationary := by norm_num
      background_gradient_bound := ?_
      initial_mem := toy_initial_mem
      sublevel_barrier := toy_invariant_region_closure_inside_ball
      gamma_pos := by norm_num
      mobility_coercive := ?_
      minimizer_in_sublevel := ?_
      forward_invariant := ?_ }
  · intro x hx
    change ContDiffAt ℝ 2 (fun y : ℝ => y / 2) x
    fun_prop
  · intro x hx
    change ContDiffAt ℝ 2 (fun y : ℝ => -(y ^ 2) / 2) x
    fun_prop
  · intro x
    have hderiv : HasDerivAt toyBackground (1 / 2) x := by
      convert (hasDerivAt_id x).const_mul (1 / 2) using 1
      · ext y
        simp [toyBackground, div_eq_mul_inv]
        ring
      · ring
    have hfrechet := hderiv.hasFDerivAt
    rw [hfrechet.fderiv]
    ext y
    simp [innerSL_apply_apply, real_inner_comm]
  · intro x
    have hderiv : HasDerivAt toyMeanField (-x) x := by
      convert (((hasDerivAt_id x).pow 2).neg.div_const 2) using 1
      · funext y
        simp [toyMeanField]
      · simp [Function.id_def]
        ring
    have hfrechet := hderiv.hasFDerivAt
    rw [hfrechet.fderiv]
    ext y
    simp [innerSL_apply_apply, real_inner_comm]
  · intro x hx
    exact hasFDerivAt_const (1 / 2 : ℝ) x
  · intro x hx
    convert (hasFDerivAt_id x).neg using 1
    · funext y
      rfl
    · rfl
  · intro x hx
    fun_prop
  · intro x hx v w
    simp [toyIdentity]
  · intro x hx w
    norm_num
  · intro x hx w
    simp [toyNegativeIdentity, real_inner_self_eq_norm_sq]
    nlinarith
  · intro x hx
    norm_num
  · intro x hx w
    simp [toyIdentity, real_inner_self_eq_norm_sq]
  · intro x hx hmin
    have hleft : toyPotential x ≤ toyPotential (-(1 / 2 : ℝ)) := by
      have hvalleyBall : (-(1 / 2 : ℝ)) ∈ Metric.closedBall (0 : ℝ) 1 := by
        rw [Metric.mem_closedBall, Real.dist_eq]
        norm_num
      have hmin' := hmin (a := -(1 / 2 : ℝ)) hvalleyBall
      simpa [toyPotential, toyBackground, toyMeanField] using hmin'
    have hright : toyPotential (-(1 / 2 : ℝ)) ≤ toyPotential x :=
      (toy_valley_unique_on_unit_ball.1) (a := x) hx
    have heq : toyPotential x = toyPotential (-(1 / 2 : ℝ)) :=
      le_antisymm hleft hright
    have hxvalley := toy_valley_unique_on_unit_ball.2 x hx heq
    simpa [hxvalley] using toy_valley_mem
  · intro a d orbit x hd hstart hx hode t ht
    have horbit : orbit a ∈ toyInvariantRegion := by
      rw [hstart]
      exact hx
    have hode' : ∀ s ∈ Set.Icc a (a + d),
        HasDerivAt orbit (toyClosedLoopField (orbit s)) s := by
      intro s hs
      have h := hode s hs
      convert h using 1 <;> simp [toyIdentity, toyClosedLoopField] <;> ring
    exact toy_closed_loop_interval_invariant a d hd orbit horbit hode' t ht

theorem toy_invariant_region_is_strictly_smaller_than_initial_sublevel :
    toyInvariantRegionStage.sublevel ≠
      {x : ℝ | x ∈ Metric.closedBall toyInvariantRegionStage.center
          toyInvariantRegionStage.radius ∧
        toyInvariantRegionStage.background x -
            toyInvariantRegionStage.gain * toyInvariantRegionStage.presenceGain *
              toyInvariantRegionStage.meanField x ≤
          toyInvariantRegionStage.background toyInvariantRegionStage.initial -
            toyInvariantRegionStage.gain * toyInvariantRegionStage.presenceGain *
              toyInvariantRegionStage.meanField toyInvariantRegionStage.initial} := by
  intro heq
  have hboundary : (-1 : ℝ) ∈
      {x : ℝ | x ∈ Metric.closedBall toyInvariantRegionStage.center
          toyInvariantRegionStage.radius ∧
        toyInvariantRegionStage.background x -
            toyInvariantRegionStage.gain * toyInvariantRegionStage.presenceGain *
              toyInvariantRegionStage.meanField x ≤
          toyInvariantRegionStage.background toyInvariantRegionStage.initial -
            toyInvariantRegionStage.gain * toyInvariantRegionStage.presenceGain *
              toyInvariantRegionStage.meanField toyInvariantRegionStage.initial} := by
    norm_num [toyInvariantRegionStage, toyPotential, toyBackground, toyMeanField,
      Metric.mem_closedBall, Real.dist_eq]
  have hnew : (-1 : ℝ) ∉ toyInvariantRegion := by
    norm_num [toyInvariantRegion]
  have hsublevel : (-1 : ℝ) ∈ toyInvariantRegionStage.sublevel := by
    rw [heq]
    exact hboundary
  exact hnew (by simpa [toyInvariantRegionStage] using hsublevel)

theorem toy_model_supplies_relaxed_mean_field_stage :
    Nonempty (Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput ℝ) :=
  ⟨toyInvariantRegionStage⟩

noncomputable def toyModelWitness :
    Tomabechi.Theorem22InvariantRegion.InvariantRegionStageWitness
      toyInvariantRegionStage :=
  Tomabechi.Theorem22InvariantRegion.chooseInvariantRegionStageWitness
    toyInvariantRegionStage

theorem toy_model_has_general_quantitative_orbit :
    toyModelWitness.orbit toyInvariantRegionStage.startTime =
        toyInvariantRegionStage.initial ∧
      toyModelWitness.decayRate = 1 ∧
      ∀ t ∈ Set.Ici toyInvariantRegionStage.startTime,
        dist (toyModelWitness.orbit t) toyModelWitness.minimizer ≤
          toyModelWitness.decayAmplitude *
            Real.exp (-toyModelWitness.decayRate *
              (t - toyInvariantRegionStage.startTime)) := by
  refine ⟨toyModelWitness.initial_condition, ?_, ?_⟩
  · simp [toyModelWitness,
      Tomabechi.Theorem22InvariantRegion.InvariantRegionStageWitness.decayRate,
      toyInvariantRegionStage]
  · intro t ht
    exact toyModelWitness.distance_decay t ht

end Tomabechi.Theorem22InvariantRegionModel
