import Theorem22
import Tomabechi.Dynamics.StageSwitching

/-!
# 定理23-B：平行移動二次谷の全入力

ここでは一変数の二次谷を使い、段階中心・厳密な凍結軌道・有限の正の待ち時間を
具体化する。 -/

namespace Tomabechi.Examples.Theorem23B

open Filter
open scoped Topology

noncomputable def quadraticStage (center initial start : ℝ) :
    Tomabechi.Theorem22.StageValleySpec ℝ := by
  let d : ℝ := |initial - center|
  let R : ℝ := d + 1
  refine
    { center := center
      radius := R
      gain := 1
      presenceGain := 1
      curvature := 1
      backgroundCurvature := 0
      gradientBound := 0
      gamma := 1
      startTime := start
      background := fun _ => 0
      presence := fun x => -(1 / 2 : ℝ) * (x - center) ^ 2
      backgroundGradient := fun _ => 0
      presenceGradient := fun x => -(x - center)
      backgroundHessian := fun _ => 0
      presenceHessian := fun _ => -(ContinuousLinearMap.id ℝ ℝ)
      mobility := fun _ => ContinuousLinearMap.id ℝ ℝ
      sublevel := Metric.closedBall center d
      initial := initial
      radius_pos := by dsimp [R]; positivity
      gain_pos := by norm_num
      curvature_pos := by norm_num
      backgroundCurvature_nonneg := by norm_num
      gradientBound_nonneg := by norm_num
      gain_threshold := by norm_num [R]
      background_c2_at := by intro x hx; fun_prop
      presence_c2_at := by intro x hx; fun_prop
      background_gradient_representation := by intro x; simp
      presence_gradient_representation := by
        intro x
        have hshift : HasFDerivAt (fun y : ℝ => y - center)
            (ContinuousLinearMap.id ℝ ℝ) x := by
          simpa using (hasFDerivAt_id x).sub_const center
        have hpres : HasFDerivAt
            (fun y : ℝ => -(1 / 2 : ℝ) * (y - center) ^ 2)
            ((-(1 / 2 : ℝ)) • ((2 : ℝ) • (x - center) • ContinuousLinearMap.id ℝ ℝ)) x := by
          convert (hshift.pow 2).const_smul (-(1 / 2 : ℝ)) using 1 <;>
            ext z <;> simp [mul_assoc, mul_left_comm, mul_comm]
        have hfd := hpres.fderiv
        rw [hfd]
        ext z
        simp [innerSL_apply_apply, Real.inner_apply, mul_comm]
      background_gradient_deriv := by intro x hx; simpa using hasFDerivAt_const (0 : ℝ) x
      presence_gradient_deriv := by
        intro x hx
        have hshift : HasFDerivAt (fun y : ℝ => y - center)
            (ContinuousLinearMap.id ℝ ℝ) x := by
          simpa using (hasFDerivAt_id x).sub_const center
        convert hshift.const_smul (-1 : ℝ) using 1 <;> ext y <;>
          simp [smul_eq_mul] <;> ring
      mobility_c1 := by intro x hx; fun_prop
      mobility_symmetric := by intro x hx v w; simp [real_inner_comm]
      background_hessian_lower := by intro x hx w; simp
      presence_hessian_upper := by
        intro x hx w
        simp [Real.inner_apply, real_inner_self_eq_norm_sq]
        simpa [pow_two]
      presence_center_stationary := by simp
      background_gradient_bound := by intro x hx; simp
      initial_mem := by
        dsimp [d]
        simp [dist_eq_norm, Real.norm_eq_abs]
      sublevel_barrier := by
        dsimp [d, R]
        have hclosed : IsClosed (Metric.closedBall center |initial - center|) :=
          Metric.isClosed_closedBall
        have hclosure : closure (Metric.closedBall center |initial - center|) =
            Metric.closedBall center |initial - center| := hclosed.closure_eq
        rw [hclosure]
        intro x hx
        apply Metric.mem_ball.mpr
        have hx' := Metric.mem_closedBall.mp hx
        linarith
      sublevel_eq := by
        dsimp [d, R, Tomabechi.Theorem22.stageEffectivePotential]
        ext x
        simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs]
        constructor
        · intro hx
          have hxSq : (x - center) ^ 2 ≤ (initial - center) ^ 2 :=
            (sq_le_sq).2 (by simpa [abs_abs] using hx)
          refine ⟨?_, ?_⟩
          · calc
              |x - center| ≤ |initial - center| := hx
              _ ≤ |initial - center| + 1 := by linarith
          · nlinarith [hxSq]
        · rintro ⟨hxball, henergy⟩
          have hsq : (x - center) ^ 2 ≤ (initial - center) ^ 2 := by nlinarith
          have habs : |x - center| ≤ |initial - center| := (sq_le_sq).1 hsq
          simpa [abs_abs] using habs
      gamma_pos := by norm_num
      mobility_coercive := by intro x hx w; simp [real_inner_self_eq_norm_sq] }

/-- 二次谷の厳密な凍結軌道：初期誤差が指数率1で減衰する。 -/
noncomputable def quadraticFrozenOrbit (center initial start t : ℝ) : ℝ :=
  center + (initial - center) * Real.exp (-(t - start))

theorem continuous_quadraticFrozenOrbit (center initial start : ℝ) :
    Continuous (quadraticFrozenOrbit center initial start) := by
  fun_prop [quadraticFrozenOrbit]

theorem hasDerivAt_quadraticFrozenOrbit (center initial start t : ℝ) :
    HasDerivAt (quadraticFrozenOrbit center initial start)
      (-(quadraticFrozenOrbit center initial start t - center)) t := by
  have harg : HasDerivAt (fun y : ℝ => -(y - start)) (-1) t := by
    convert ((hasDerivAt_id t).sub_const start).const_smul (-1 : ℝ) using 1
    · funext y
      simp [smul_eq_mul]
    · simp [smul_eq_mul]
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(y - start)))
      (-Real.exp (-(t - start))) t := by
    convert (Real.hasDerivAt_exp (-(t - start))).comp t harg using 1 <;>
      simp [Function.comp_def, neg_sub, smul_eq_mul, mul_comm]
  have hmul := hexp.const_mul (initial - center)
  have hadd := hmul.const_add center
  convert hadd using 1
  · rfl
  · simp [quadraticFrozenOrbit]

theorem quadraticFrozenOrbit_distance_formula (center initial start t : ℝ) :
    dist (quadraticFrozenOrbit center initial start t) center =
      |initial - center| * Real.exp (-(t - start)) := by
  rw [dist_eq_norm, Real.norm_eq_abs, quadraticFrozenOrbit]
  have hform : center + (initial - center) * Real.exp (-(t - start)) - center =
      (initial - center) * Real.exp (-(t - start)) := by ring
  rw [hform, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- 閉形式の軌道は初期時刻で指定した初期値を取り、全ての後時刻で
   初期 sublevel 内に留まる。 -/
theorem quadraticFrozenOrbit_initial_and_in_sublevel
    (center initial start t : ℝ) (ht : start ≤ t) :
    quadraticFrozenOrbit center initial start start = initial ∧
      quadraticFrozenOrbit center initial start t ∈
        Metric.closedBall center |initial - center| := by
  constructor
  · simp [quadraticFrozenOrbit]
  · rw [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs]
    change |quadraticFrozenOrbit center initial start t - center| ≤
      |initial - center|
    rw [quadraticFrozenOrbit]
    have hexp_pos : 0 < Real.exp (-(t - start)) := Real.exp_pos _
    have hexp_le : Real.exp (-(t - start)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hform : center + (initial - center) * Real.exp (-(t - start)) - center =
        (initial - center) * Real.exp (-(t - start)) := by ring
    rw [hform]
    rw [abs_mul, abs_of_pos hexp_pos]
    calc
      |initial - center| * Real.exp (-(t - start)) ≤
          |initial - center| * 1 := by
            exact mul_le_mul_of_nonneg_left hexp_le (abs_nonneg _)
      _ = |initial - center| := by ring

/-- 指定した閉形式軌道は二次谷のODEを解く。 -/
theorem quadraticFrozenOrbit_solves_stage
    (center initial start t : ℝ) :
    HasDerivAt (quadraticFrozenOrbit center initial start)
      (-(Tomabechi.Theorem22.stageEffectiveGradient
        (quadraticStage center initial start)
        (quadraticFrozenOrbit center initial start t))) t := by
  have h := hasDerivAt_quadraticFrozenOrbit center initial start t
  convert h using 1 <;>
    simp [quadraticStage, quadraticFrozenOrbit,
      Tomabechi.Theorem22.stageEffectiveGradient]

/-- 一般の段階証人が選ぶ軌道は、ここで与えた厳密解と一致する。 -/
theorem quadraticFrozenOrbit_eq_witness_orbit
    (center initial start t : ℝ) (ht : start ≤ t) :
    quadraticFrozenOrbit center initial start t =
      (Tomabechi.Theorem22.chooseStageValley
        (quadraticStage center initial start)).orbit t := by
  let s := quadraticStage center initial start
  let w := Tomabechi.Theorem22.chooseStageValley s
  have hinit : quadraticFrozenOrbit center initial start s.startTime = s.initial := by
    exact (quadraticFrozenOrbit_initial_and_in_sublevel center initial start start le_rfl).1
  have hsub : ∀ r ∈ Set.Ici s.startTime,
      quadraticFrozenOrbit center initial start r ∈ s.sublevel := by
    intro r hr
    exact (quadraticFrozenOrbit_initial_and_in_sublevel center initial start r hr).2
  have hode : ∀ r ∈ Set.Ioi (s.startTime - w.local_extension),
      HasDerivAt (quadraticFrozenOrbit center initial start)
        (-(s.mobility (quadraticFrozenOrbit center initial start r)
          (s.backgroundGradient (quadraticFrozenOrbit center initial start r) -
            (s.gain * s.presenceGain) •
              s.presenceGradient (quadraticFrozenOrbit center initial start r)))) r := by
    intro r hr
    simpa [s, quadraticStage, Tomabechi.Theorem22.stageEffectiveGradient,
      ContinuousLinearMap.id_apply] using
      quadraticFrozenOrbit_solves_stage center initial start r
  have heq := w.orbit_unique (quadraticFrozenOrbit center initial start)
    (by simpa [s] using hinit) (by simpa [s] using hsub)
    (by simpa [s] using hode)
  exact heq t (by simpa [s, quadraticStage] using ht)

/-- 二次谷の定理22証人が選ぶ唯一の最小点は、指定した谷の中心である。 -/
theorem chooseQuadraticStage_minimizer (center initial start : ℝ) :
    (Tomabechi.Theorem22.chooseStageValley
      (quadraticStage center initial start)).minimizer = center := by
  let s := quadraticStage center initial start
  let w := Tomabechi.Theorem22.chooseStageValley s
  have hcenter : center ∈ Metric.closedBall s.center s.radius := by
    simp [s, quadraticStage, Metric.mem_closedBall]
    positivity
  have hcenterValue :
      Tomabechi.Theorem22.stageEffectivePotential s center = 0 := by
    simp [Tomabechi.Theorem22.stageEffectivePotential, s, quadraticStage]
  have hminNonneg :
      0 ≤ Tomabechi.Theorem22.stageEffectivePotential s w.minimizer := by
    simp [Tomabechi.Theorem22.stageEffectivePotential, s, quadraticStage]
    positivity
  have hminLe :
      Tomabechi.Theorem22.stageEffectivePotential s w.minimizer ≤ 0 := by
    rw [← hcenterValue]
    exact w.minimizer_is_min hcenter
  have hminValue :
      Tomabechi.Theorem22.stageEffectivePotential s w.minimizer = 0 := le_antisymm hminLe hminNonneg
  have hsame :
      Tomabechi.Theorem22.stageEffectivePotential s center =
        Tomabechi.Theorem22.stageEffectivePotential s w.minimizer := by
    rw [hcenterValue, hminValue]
  exact (w.minimizer_unique center hcenter hsame).symm

/-- 二次谷の一意最小点を中心として読む。 -/
noncomputable def quadraticNext (n : ℕ) (initial start : ℝ) :
    Tomabechi.Theorem22.StageValleySpec ℝ :=
  quadraticStage (n + 1 : ℝ) initial start

theorem quadraticNext_initial (n : ℕ) (x t : ℝ) :
    (quadraticNext n x t).initial = x := rfl

theorem quadraticNext_start (n : ℕ) (x t : ℝ) :
    (quadraticNext n x t).startTime = t := rfl

noncomputable def quadraticFirst : Tomabechi.Theorem22.StageValleySpec ℝ :=
  quadraticStage 0 (-1) 0

def quadraticDuration (_ : ℕ) : ℝ := 10

def quadraticTime (n : ℕ) : ℝ := 10 * n

noncomputable def quadraticStages : ℕ → Tomabechi.Theorem22.StageValleySpec ℝ :=
  Tomabechi.Theorem23.endpointCompatibleStageSequence
    quadraticFirst quadraticNext quadraticNext_initial quadraticNext_start
    quadraticTime quadraticDuration

theorem quadraticStages_center (n : ℕ) : (quadraticStages n).center = n := by
  induction n with
  | zero =>
      simp [quadraticStages, quadraticFirst, quadraticStage,
        Tomabechi.Theorem23.endpointCompatibleStageSequence]
  | succ n ih =>
      simp [quadraticStages, quadraticNext, quadraticStage,
        Tomabechi.Theorem23.endpointCompatibleStageSequence]

theorem quadraticStages_shape (n : ℕ) :
    quadraticStages n = quadraticStage (n : ℝ)
      (quadraticStages n).initial (quadraticStages n).startTime := by
  induction n with
  | zero =>
      simp [quadraticStages, quadraticFirst, quadraticStage,
        Tomabechi.Theorem23.endpointCompatibleStageSequence]
  | succ n ih =>
      simp [quadraticStages, quadraticNext, quadraticStage,
        Tomabechi.Theorem23.endpointCompatibleStageSequence]

theorem quadraticStage_decayRate (center initial start : ℝ) :
    (Tomabechi.Theorem22.chooseStageValley
      (quadraticStage center initial start)).decayRate = 1 := by
  simp [Tomabechi.Theorem22.StageValleyWitness.decayRate, quadraticStage]

theorem quadraticStage_decayAmplitude (center initial start : ℝ) :
    (Tomabechi.Theorem22.chooseStageValley
      (quadraticStage center initial start)).decayAmplitude = |initial - center| := by
  let w := Tomabechi.Theorem22.chooseStageValley
    (quadraticStage center initial start)
  change w.decayAmplitude = |initial - center|
  rw [Tomabechi.Theorem22.StageValleyWitness.decayAmplitude]
  rw [w.initial_condition, chooseQuadraticStage_minimizer]
  simp only [quadraticStage]
  have hsq : 2 * (0 - 1 * 1 * (-(1 / 2 : ℝ) * (initial - center) ^ 2) -
      (0 - 1 * 1 * (-(1 / 2 : ℝ) * (center - center) ^ 2))) /
      (1 * 1 * 1 - 0) = (initial - center) ^ 2 := by ring
  rw [hsq]
  exact Real.sqrt_sq_eq_abs _

def quadraticU (n : ℕ) : WithTop ℕ := n

def quadraticV (n : ℕ) : WithTop ℕ := n

def quadraticRepresentation : WithTop ℕ → ℝ
  | ⊤ => -1
  | (n : ℕ) => n

theorem quadraticRepresentation_injective : Function.Injective quadraticRepresentation := by
  intro a b hab
  cases a with
  | top =>
      cases b with
      | top => rfl
      | coe b =>
          have h : (b : ℝ) = -1 := by simpa [quadraticRepresentation] using hab.symm
          have hn : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
          linarith
  | coe a =>
      cases b with
      | top =>
          have h : (a : ℝ) = -1 := by simpa [quadraticRepresentation] using hab
          have hn : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
          linarith
      | coe b =>
          simp only [quadraticRepresentation] at hab
          exact_mod_cast hab

theorem quadraticU_update (n : ℕ) :
  quadraticU (n + 1) = quadraticU n ⊔ quadraticV (n + 1) := by
  simp [quadraticU, quadraticV, Nat.cast_succ]

theorem quadraticU_below_top (n : ℕ) : quadraticU n < ⊤ := by
  simp [quadraticU]

theorem quadraticV_new (n : ℕ) : ¬ quadraticV (n + 1) ≤ quadraticU n := by
  intro h
  change ((n + 1 : ℕ) : WithTop ℕ) ≤ (n : WithTop ℕ) at h
  have hnat : n + 1 ≤ n := by exact_mod_cast h
  exact (Nat.not_succ_le_self n) hnat

theorem quadraticStages_start (n : ℕ) :
    (quadraticStages n).startTime = quadraticTime n := by
  exact Tomabechi.Theorem23.endpointCompatibleStageSequence_startTime
    quadraticFirst quadraticNext quadraticNext_initial quadraticNext_start
    quadraticTime quadraticDuration (by simp [quadraticFirst, quadraticStage, quadraticTime]) n

theorem quadraticStages_transition (n : ℕ) :
    (quadraticStages (n + 1)).initial =
      (Tomabechi.Theorem22.chooseStageValley (quadraticStages n)).orbit
        (quadraticTime n + quadraticDuration n) := by
  exact Tomabechi.Theorem23.endpointCompatibleStageSequence_transition
    quadraticFirst quadraticNext quadraticNext_initial quadraticNext_start
    quadraticTime quadraticDuration n

theorem quadraticTime_recurrence (n : ℕ) :
    quadraticTime (n + 1) = quadraticTime n + quadraticDuration n := by
  simp [quadraticTime, quadraticDuration]
  ring

theorem quadraticDuration_positive (n : ℕ) : 0 < quadraticDuration n := by
  norm_num [quadraticDuration]

theorem quadraticTime_unbounded (B : ℝ) :
    ∃ n, B < ∑ k ∈ Finset.range n, quadraticDuration k := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / 10)
  refine ⟨n, ?_⟩
  simp [quadraticDuration]
  nlinarith

theorem quadraticTime_tendsto_unbounded (B : ℝ) : ∃ n, B < quadraticTime n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / 10)
  refine ⟨n, ?_⟩
  simp [quadraticTime]
  nlinarith

theorem quadraticEndpoint_distance_bound (x c : ℝ)
    (hd : |x - c| ≤ 11 / 10) :
    |c + (x - c) * Real.exp (-10) - (c + 1)| ≤ 11 / 10 := by
  have hexp10 : 11 ≤ Real.exp 10 := by
    have h := Real.add_one_le_exp (10 : ℝ)
    norm_num at h ⊢
    linarith
  have hq : Real.exp (-10) ≤ 1 / 11 := by
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hexp10
  have hqpos : 0 < Real.exp (-10) := Real.exp_pos _
  calc
    |c + (x - c) * Real.exp (-10) - (c + 1)| =
        |(x - c) * Real.exp (-10) + (-1)| := by congr 1 <;> ring
    _ ≤ |(x - c) * Real.exp (-10)| + |-1| := abs_add_le _ _
    _ = |x - c| * Real.exp (-10) + 1 := by
      rw [abs_mul, abs_of_pos hqpos]
      norm_num
    _ ≤ (11 / 10) * (1 / 11) + 1 := by
      exact add_le_add
        (mul_le_mul hd hq (by positivity) (by norm_num)) (by norm_num)
    _ ≤ 11 / 10 := by norm_num

theorem quadraticStages_initial_distance_bound :
    ∀ n, |(quadraticStages n).initial - (n : ℝ)| ≤ 11 / 10 := by
  intro n
  induction n with
  | zero =>
      simp [quadraticStages, quadraticFirst, quadraticStage,
        Tomabechi.Theorem23.endpointCompatibleStageSequence]
      norm_num
  | succ n ih =>
      rw [quadraticStages_transition]
      rw [quadraticStages_shape n]
      rw [← quadraticFrozenOrbit_eq_witness_orbit
        (center := (n : ℝ)) (initial := (quadraticStages n).initial)
        (start := (quadraticStages n).startTime)
        (t := quadraticTime n + quadraticDuration n)]
      · rw [quadraticStages_start]
        simp only [quadraticDuration]
        have hdelta : quadraticTime n + 10 - quadraticTime n = 10 := by
          simp [quadraticTime]
        simp only [quadraticFrozenOrbit]
        rw [hdelta]
        simpa using
          quadraticEndpoint_distance_bound
            (x := (quadraticStages n).initial) (c := (n : ℝ)) ih
      · rw [quadraticStages_start]
        simp [quadraticTime, quadraticDuration]

theorem quadraticStages_initial_le_previous_center :
    ∀ n, (quadraticStages n).initial ≤ (n : ℝ) - 1 := by
  intro n
  induction n with
  | zero => norm_num [quadraticStages, quadraticFirst, quadraticStage,
      Tomabechi.Theorem23.endpointCompatibleStageSequence]
  | succ n ih =>
      rw [quadraticStages_transition, quadraticStages_shape n]
      rw [← quadraticFrozenOrbit_eq_witness_orbit
        (center := (n : ℝ)) (initial := (quadraticStages n).initial)
        (start := (quadraticStages n).startTime)
        (t := quadraticTime n + quadraticDuration n)]
      · rw [quadraticStages_start]
        simp only [quadraticDuration, quadraticFrozenOrbit]
        have hdelta : quadraticTime n + 10 - quadraticTime n = 10 := by
          simp [quadraticTime]
        have hq : 0 ≤ Real.exp (-10) := (Real.exp_pos _).le
        have herror : (quadraticStages n).initial - (n : ℝ) ≤ -1 := by
          linarith
        have hprod : ((quadraticStages n).initial - (n : ℝ)) *
            Real.exp (-10) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (by linarith) hq
        rw [hdelta]
        norm_num [Nat.cast_succ]
        linarith
      · rw [quadraticStages_start]
        simp [quadraticTime, quadraticDuration]

theorem quadraticStages_radius_gt_one (n : ℕ) :
    1 < (quadraticStages n).radius := by
  rw [quadraticStages_shape]
  simp only [quadraticStage]
  have hdist : 1 ≤ |(quadraticStages n).initial - (n : ℝ)| := by
    rw [abs_of_nonpos (by linarith [quadraticStages_initial_le_previous_center n])]
    linarith [quadraticStages_initial_le_previous_center n]
  linarith

theorem quadraticStages_decayAmplitude_bound (n : ℕ) :
    (Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).decayAmplitude ≤
      11 / 10 := by
  rw [Tomabechi.Theorem22.chooseAllStageValleys,
    quadraticStages_shape, quadraticStage_decayAmplitude]
  exact quadraticStages_initial_distance_bound n

theorem quadraticStages_decayRate (n : ℕ) :
    (Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).decayRate = 1 := by
  rw [Tomabechi.Theorem22.chooseAllStageValleys,
    quadraticStages_shape, quadraticStage_decayRate]

noncomputable def quadraticTheta (_ : ℕ) : ℝ := 1 / 4

noncomputable def quadraticEpsilon (_ : ℕ) : ℝ := 1 / 8

theorem quadraticEpsilon_positive (n : ℕ) : 0 < quadraticEpsilon n := by
  norm_num [quadraticEpsilon]

theorem quadraticStages_wait_bound (n : ℕ) :
    max 0
      (1 / (Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).decayRate *
        Real.log ((Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).decayAmplitude /
          quadraticEpsilon n)) ≤ quadraticDuration n := by
  rw [quadraticStages_decayRate]
  simp only [quadraticDuration, quadraticEpsilon]
  have hamp := quadraticStages_decayAmplitude_bound n
  have hexp : 11 ≤ Real.exp 10 := by
    have h := Real.add_one_le_exp (10 : ℝ)
    norm_num at h ⊢
    linarith
  have hratio :
      (Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).decayAmplitude /
        (1 / 8 : ℝ) ≤ Real.exp 10 := by
    calc
      _ ≤ (11 / 10) / (1 / 8) := (div_le_div_of_nonneg_right hamp (by norm_num))
      _ ≤ 11 := by norm_num
      _ ≤ Real.exp 10 := hexp
  have hlog : Real.log
      ((Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).decayAmplitude /
        (1 / 8 : ℝ)) ≤ 10 := by
    have ha := Tomabechi.Theorem22.StageValleyWitness.decayAmplitude_nonneg
      (Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n)
    by_cases hp : 0 <
      (Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).decayAmplitude
    · apply (Real.log_le_iff_le_exp (by positivity)).2
      exact hratio
    · have hz :
        (Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).decayAmplitude = 0 :=
          le_antisymm (le_of_not_gt hp) ha
      simp [hz]
  have hmax : max 0 (Real.log
      ((Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).decayAmplitude /
        (1 / 8 : ℝ))) ≤ 10 := max_le (by norm_num) hlog
  simpa using hmax

theorem quadraticStages_minimizer (n : ℕ) :
    (Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).minimizer = n := by
  rw [Tomabechi.Theorem22.chooseAllStageValleys, quadraticStages_shape]
  exact chooseQuadraticStage_minimizer (n : ℝ)
    (quadraticStages n).initial (quadraticStages n).startTime

theorem quadraticStages_segment_in_next_ball (n : ℕ) :
    segment ℝ
        (Tomabechi.Theorem22.chooseAllStageValleys quadraticStages n).minimizer
        (Tomabechi.Theorem22.chooseAllStageValleys quadraticStages (n + 1)).minimizer ⊆
      Metric.closedBall (quadraticStages (n + 1)).center
        (quadraticStages (n + 1)).radius := by
  rw [quadraticStages_minimizer, quadraticStages_minimizer,
    Nat.cast_add, Nat.cast_one,
    segment_eq_Icc (by norm_num : (n : ℝ) ≤ n + 1)]
  intro x hx
  have hdist : |x - ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  rw [quadraticStages_center]
  rw [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs]
  have hradius : 1 ≤ (quadraticStages (n + 1)).radius := by
    rw [quadraticStages_shape]
    simp [quadraticStage]
  simpa [Nat.cast_add, Nat.cast_one] using hdist.trans hradius

set_option linter.defProp false in
/-- 二次谷列の全入力を、定理23-Bの一般切替核へ渡す。 -/
noncomputable def quadraticStages_give_condition23B_core :=
  Tomabechi.Theorem23.theorem22_stage_specs_and_switches_give_condition23B_core
    quadraticU quadraticV quadraticU_update quadraticU_below_top quadraticV_new
    quadraticStages quadraticRepresentation quadraticRepresentation_injective
    (by
      intro n
      rw [quadraticStages_center]
      simp [quadraticU, quadraticRepresentation])
    quadraticTheta
    (by intro n; norm_num [quadraticTheta])
    (by
      intro n
      rw [quadraticStages_minimizer (n + 1), quadraticStages_minimizer n]
      rw [quadraticStages_shape (n + 1)]
      norm_num [quadraticTheta, quadraticStage])
    quadraticStages_segment_in_next_ball
    quadraticTime quadraticDuration quadraticEpsilon
    quadraticStages_start quadraticStages_transition quadraticTime_recurrence
    quadraticDuration_positive quadraticTime_unbounded quadraticEpsilon_positive
    quadraticStages_wait_bound

end Tomabechi.Examples.Theorem23B
