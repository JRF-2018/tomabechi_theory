import Theorem22
import Tomabechi.Dynamics.GlobalFlow
import Tomabechi.Dynamics.StageSwitching
import Tomabechi.Examples.Gaussian

/-!
# 定理22の有限ガウス階段：実軌道

Python の A/C の中心列を保ち、半径 5/4 の局所ガウス谷を StageValleySpec に接続する。
-/

namespace Tomabechi.Examples.Theorem22GaussianStages

open Tomabechi.Theorem22
open Tomabechi.Theorem23
open Tomabechi.Theorem21
open Tomabechi.Examples.Gaussian
open Filter
open scoped Topology

/-- 半径 5/4 の局所球では、ガウス谷の曲率は一様に 1/8 以上。 -/
theorem ddwell_lower_on_quarter_ball (c x : ℝ) (hx : |x - c| ≤ 5 / 4) :
    1 / 8 ≤ ddwell 2 (3 / 2) c x := by
  have hsq : (x - c) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := by
    have hx' : -(5 / 4 : ℝ) ≤ x - c ∧ x - c ≤ 5 / 4 := by
      simpa [abs_le] using hx
    rcases hx' with ⟨hl, hr⟩
    nlinarith
  have hfactor : 11 / 36 ≤ 1 - (x - c) ^ 2 / (3 / 2 : ℝ) ^ 2 := by
    norm_num
    nlinarith [hsq]
  have harg : (x - c) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2) ≤ 25 / 72 := by
    norm_num
    nlinarith [hsq]
  have hexp : 47 / 72 ≤ Real.exp (-((x - c) ^ 2 /
      (2 * (3 / 2 : ℝ) ^ 2))) := by
    have h := Real.add_one_le_exp (-((x - c) ^ 2 /
      (2 * (3 / 2 : ℝ) ^ 2)))
    norm_num at h ⊢
    linarith
  rw [show ddwell 2 (3 / 2) c x =
    (8 / 9 : ℝ) * (1 - (x - c) ^ 2 / (3 / 2 : ℝ) ^ 2) *
      Real.exp (-((x - c) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2))) by
        simp [ddwell] <;> ring]
  calc
    1 / 8 ≤ (8 / 9 : ℝ) * (11 / 36) * (47 / 72) := by norm_num
    _ ≤ (8 / 9 : ℝ) * (1 - (x - c) ^ 2 / (3 / 2 : ℝ) ^ 2) *
        Real.exp (-((x - c) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2))) := by
      gcongr

/-- ガウス勾配は半径5/4内で、中心からのずれに少なくとも1/2の線形係数を持つ。 -/
theorem gaussian_dwell_energy_lower (c x : ℝ) (hx : |x - c| ≤ 5 / 4) :
    (x - c) * dwell 2 (3 / 2) c x ≥ (1 / 2 : ℝ) * (x - c) ^ 2 := by
  have hsq : (x - c) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := by
    have hx' : -(5 / 4 : ℝ) ≤ x - c ∧ x - c ≤ 5 / 4 := by
      simpa [abs_le] using hx
    rcases hx' with ⟨hl, hr⟩
    nlinarith
  have harg : (x - c) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2) ≤ 25 / 72 := by
    norm_num
    nlinarith [hsq]
  have hexp : 47 / 72 ≤ Real.exp (-((x - c) ^ 2 /
      (2 * (3 / 2 : ℝ) ^ 2))) := by
    have h := Real.add_one_le_exp (-((x - c) ^ 2 /
      (2 * (3 / 2 : ℝ) ^ 2)))
    norm_num at h ⊢
    linarith
  rw [show dwell 2 (3 / 2) c x = (8 / 9 : ℝ) * (x - c) *
      Real.exp (-((x - c) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2))) by
        simp [dwell] <;> ring]
  have hcoeff : (1 / 2 : ℝ) ≤ (8 / 9 : ℝ) *
      Real.exp (-((x - c) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2))) := by
    calc
      (1 / 2 : ℝ) ≤ (8 / 9 : ℝ) * (47 / 72) := by norm_num
      _ ≤ (8 / 9 : ℝ) * Real.exp (-((x - c) ^ 2 /
          (2 * (3 / 2 : ℝ) ^ 2))) := by gcongr
  nlinarith [sq_nonneg (x - c)]

/-- ガウス谷のエネルギー部分準位は中心からの距離で記述できる。 -/
theorem gaussian_well_le_iff_abs_le (c x initial : ℝ) :
    well 2 (3 / 2) c x ≤ well 2 (3 / 2) c initial ↔
      |x - c| ≤ |initial - c| := by
  constructor
  · intro h
    have hexp : Real.exp (-((initial - c) ^ 2 /
        (2 * (3 / 2 : ℝ) ^ 2))) ≤
        Real.exp (-((x - c) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2))) := by
      unfold well at h
      simp only [neg_div] at h
      nlinarith
    have harg := (Real.exp_le_exp.mp hexp)
    apply (sq_le_sq).1
    norm_num at harg ⊢
    nlinarith
  · intro h
    have hsquare : (x - c) ^ 2 ≤ (initial - c) ^ 2 := (sq_le_sq).2 h
    have hexp : Real.exp (-((initial - c) ^ 2 /
        (2 * (3 / 2 : ℝ) ^ 2))) ≤
        Real.exp (-((x - c) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2))) :=
      Real.exp_le_exp.mpr (by
        have hdiv : (x - c) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2) ≤
            (initial - c) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hsquare (by positivity)
        exact neg_le_neg hdiv)
    unfold well
    simp only [neg_div]
    nlinarith

/-- 半径5/4・曲率1/8の局所ガウス段階を、初期部分準位の障壁つきで作る。 -/
noncomputable def gaussianStage (c initial start : ℝ)
    (hinitial : |initial - c| < 5 / 4) : StageValleySpec ℝ := by
  let d := |initial - c|
  refine
    { center := c
      radius := 5 / 4
      gain := 1
      presenceGain := 1
      curvature := 1 / 8
      backgroundCurvature := 0
      gradientBound := 0
      gamma := 1
      startTime := start
      background := fun _ => 0
      presence := fun x => -well 2 (3 / 2) c x
      backgroundGradient := fun _ => 0
      presenceGradient := fun x => -dwell 2 (3 / 2) c x
      backgroundHessian := fun _ => 0
      presenceHessian := fun x => (-(ddwell 2 (3 / 2) c x)) • ContinuousLinearMap.id ℝ ℝ
      mobility := fun _ => ContinuousLinearMap.id ℝ ℝ
      sublevel := Metric.closedBall c d
      initial := initial
      radius_pos := by norm_num
      gain_pos := by norm_num
      curvature_pos := by norm_num
      backgroundCurvature_nonneg := by norm_num
      gradientBound_nonneg := by norm_num
      gain_threshold := by norm_num
      background_c2_at := by intro x hx; fun_prop
      presence_c2_at := by intro x hx; fun_prop [well]
      background_gradient_representation := by intro x; simp
      presence_gradient_representation := by
        intro x
        have hderiv := (hasDerivAt_well 2 (3 / 2) c x (by norm_num)).neg
        have hfd := hderiv.hasFDerivAt
        rw [show (fun z : ℝ => -well 2 (3 / 2) c z) =
          -well 2 (3 / 2) c by rfl, hfd.fderiv]
        ext y
        simp [innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply]
      background_gradient_deriv := by
        intro x hx
        exact hasFDerivAt_const (0 : ℝ) x
      presence_gradient_deriv := by
        intro x hx
        have hderiv := (hasDerivAt_dwell 2 (3 / 2) c x (by norm_num)).neg
        convert hderiv.hasFDerivAt using 1
        · ext y
          simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      mobility_c1 := by intro x hx; fun_prop
      mobility_symmetric := by intro x hx v w; simp [real_inner_comm]
      background_hessian_lower := by intro x hx w; simp
      presence_hessian_upper := by
        intro x hx w
        have hcurv := ddwell_lower_on_quarter_ball c x (Metric.mem_closedBall.mp hx)
        simp [inner_smul_left, real_inner_comm]
        nlinarith [sq_nonneg w]
      presence_center_stationary := by simp [dwell]
      background_gradient_bound := by intro x hx; simp
      initial_mem := by
        simp [d, dist_eq_norm, Real.norm_eq_abs]
      sublevel_barrier := by
        dsimp [d]
        have hclosed : IsClosed (Metric.closedBall c |initial - c|) :=
          Metric.isClosed_closedBall
        rw [hclosed.closure_eq]
        intro x hx
        rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
        have hx' := Metric.mem_closedBall.mp hx
        change |x - c| < 5 / 4
        exact lt_of_le_of_lt hx' hinitial
      sublevel_eq := by
        dsimp [d, stageEffectivePotential]
        ext x
        simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs]
        constructor
        · intro hdist
          refine ⟨by linarith [hinitial], ?_⟩
          have h := (gaussian_well_le_iff_abs_le c x initial).2 hdist
          linarith
        · rintro ⟨_, hpot⟩
          have h := (gaussian_well_le_iff_abs_le c x initial).1 (by linarith)
          exact h
      gamma_pos := by norm_num
      mobility_coercive := by intro x hx w; simp [real_inner_self_eq_norm_sq] }

/-! ## 実軌道の局所評価 -/

/-- 選択したガウス谷軌道は、開始時刻以後にスカラーのガウスODEを満たす。 -/
theorem gaussianStage_orbit_ode {c initial start : ℝ}
    (hinitial : |initial - c| < 5 / 4)
    (w : StageValleyWitness (gaussianStage c initial start hinitial))
    (t : ℝ) (ht : start ≤ t) :
    HasDerivAt w.orbit (-dwell 2 (3 / 2) c (w.orbit t)) t := by
  have h := w.orbit_ode_forward t (by simpa [gaussianStage] using ht)
  simpa [gaussianStage, stageEffectiveGradient] using h

/-- 同じ初期値から始まり、同じ部分準位を保って同じODEを満たす解は一致する。 -/
theorem gaussianStage_orbit_unique {c initial start : ℝ}
    (hinitial : |initial - c| < 5 / 4)
    (w : StageValleyWitness (gaussianStage c initial start hinitial))
    (other : ℝ → ℝ) (hstart : other start = initial)
    (hsublevel : ∀ t ∈ Set.Ici start,
      other t ∈ (gaussianStage c initial start hinitial).sublevel)
    (hode : ∀ t ∈ Set.Ioi (start - w.local_extension),
      HasDerivAt other (-dwell 2 (3 / 2) c (other t)) t) :
    ∀ t ∈ Set.Ici start, other t = w.orbit t := by
  apply w.orbit_unique other hstart hsublevel
  intro t ht
  simpa [gaussianStage, stageEffectiveGradient] using hode t ht

/-- ガウス段階では、中心からの二乗距離が段の時間とともに単調に減る。 -/
theorem gaussianStage_squared_error_antitone {c initial start : ℝ}
    (hinitial : |initial - c| < 5 / 4)
    (w : StageValleyWitness (gaussianStage c initial start hinitial))
    {T : ℝ} (_hT : 0 ≤ T) :
    AntitoneOn (fun t => (w.orbit t - c) ^ 2) (Set.Icc start (start + T)) := by
  have hderiv : ∀ t ∈ Set.Icc start (start + T),
      HasDerivAt (fun u => (w.orbit u - c) ^ 2)
        (2 * (w.orbit t - c) * (-dwell 2 (3 / 2) c (w.orbit t))) t := by
    intro t ht
    have horbit := gaussianStage_orbit_ode hinitial w t ht.1
    have hsq := (horbit.sub_const c).pow 2
    convert hsq using 1 <;> simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  apply antitoneOn_of_deriv_nonpos (convex_Icc start (start + T))
  · intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hderiv t (interior_subset ht)).deriv]
    have hball := w.orbit_in_sublevel t (interior_subset ht).1
    have hdist : |w.orbit t - c| ≤ |initial - c| := by
      simpa [gaussianStage, Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hball
    have hlocal : |w.orbit t - c| ≤ 5 / 4 := le_trans hdist hinitial.le
    have henergy := gaussian_dwell_energy_lower c (w.orbit t) hlocal
    nlinarith

/-- ガウス固有の半径評価により、重み付き二乗距離は減少する。 -/
theorem gaussianStage_weighted_square_nonincreasing {c initial start : ℝ}
    (hinitial : |initial - c| < 5 / 4)
    (w : StageValleyWitness (gaussianStage c initial start hinitial))
    {T : ℝ} (hT : 0 ≤ T) :
    Real.exp T * (w.orbit (start + T) - c) ^ 2 ≤ (initial - c) ^ 2 := by
  let q : ℝ → ℝ := fun t => Real.exp (t - start) * (w.orbit t - c) ^ 2
  have hderiv : ∀ t ∈ Set.Icc start (start + T), HasDerivAt q
      (Real.exp (t - start) *
        ((w.orbit t - c) ^ 2 - 2 * (w.orbit t - c) *
          dwell 2 (3 / 2) c (w.orbit t))) t := by
    intro t ht
    have horbit := gaussianStage_orbit_ode hinitial w t ht.1
    have hy := horbit.sub_const c
    have hsq := hy.pow 2
    have hexp := (Real.hasDerivAt_exp (t - start)).comp t
      ((hasDerivAt_id t).sub_const start)
    have hprod := hexp.mul hsq
    convert hprod using 1
    · funext u
      simp [q, sub_eq_add_neg, add_comm]
    · simp [smul_eq_mul, mul_add, mul_sub, mul_assoc, mul_left_comm, mul_comm]
      ring
  have hderiv_nonpos : ∀ t ∈ interior (Set.Icc start (start + T)),
      deriv q t ≤ 0 := by
    intro t ht
    have ht' : t ∈ Set.Icc start (start + T) := interior_subset ht
    rw [(hderiv t ht').deriv]
    have horbitball := w.orbit_in_sublevel t ht'.1
    have hmem : w.orbit t ∈ Metric.closedBall c |initial - c| := by
      change w.orbit t ∈ (gaussianStage c initial start hinitial).sublevel
      exact horbitball
    have hdist : |w.orbit t - c| ≤ |initial - c| := by
      simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hmem
    have hlocal : |w.orbit t - c| ≤ 5 / 4 := le_trans hdist hinitial.le
    have henergy := gaussian_dwell_energy_lower c (w.orbit t) hlocal
    have hexp_pos : 0 < Real.exp (t - start) := Real.exp_pos _
    have hsq_nonneg : 0 ≤ (w.orbit t - c) ^ 2 := sq_nonneg _
    nlinarith
  have hanti : AntitoneOn q (Set.Icc start (start + T)) :=
    antitoneOn_of_deriv_nonpos (convex_Icc start (start + T))
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      hderiv_nonpos
  have hvalues := hanti ⟨le_rfl, le_add_of_nonneg_right hT⟩
    ⟨le_add_of_nonneg_right hT, le_rfl⟩ (by linarith)
  have hinit : w.orbit start = initial := by
    simpa [gaussianStage] using w.initial_condition
  simpa [q, hinit] using hvalues

/-- 許容される初期誤差が9/8以下なら、12秒後の誤差は1/8以下になる。
この時間はPythonの段階切替で使う長さである。 -/
theorem gaussianStage_endpoint_error_12 {c initial start : ℝ}
    (hinitial : |initial - c| < 5 / 4)
    (w : StageValleyWitness (gaussianStage c initial start hinitial))
    (hinitial_bound : |initial - c| ≤ 9 / 8) :
    |w.orbit (start + 12) - c| ≤ 1 / 8 := by
  have hdecay := gaussianStage_weighted_square_nonincreasing hinitial w
    (T := 12) (by norm_num)
  have h4 : 5 ≤ Real.exp (4 : ℝ) := by
    have h := Real.add_one_le_exp (4 : ℝ)
    norm_num at h ⊢
    linarith
  have hexp12 : 81 ≤ Real.exp (12 : ℝ) := by
    rw [show (12 : ℝ) = 4 + 4 + 4 by norm_num, Real.exp_add, Real.exp_add]
    calc
      (81 : ℝ) ≤ 125 := by norm_num
      _ ≤ Real.exp 4 * Real.exp 4 * Real.exp 4 := by
        have hpos : 0 ≤ Real.exp (4 : ℝ) := le_of_lt (Real.exp_pos _)
        nlinarith [sq_nonneg (Real.exp (4 : ℝ) - 5)]
  have hinitial_sq : (initial - c) ^ 2 ≤ (9 / 8 : ℝ) ^ 2 := by
    have habs : |initial - c| ^ 2 ≤ (9 / 8 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hinitial_bound
    simpa [sq_abs] using habs
  have herror_sq : (w.orbit (start + 12) - c) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    have hexppos : 0 < Real.exp (12 : ℝ) := Real.exp_pos _
    have hmul : 81 * (w.orbit (start + 12) - c) ^ 2 ≤
        Real.exp 12 * (w.orbit (start + 12) - c) ^ 2 := by
      gcongr
    have hbound : Real.exp 12 * (w.orbit (start + 12) - c) ^ 2 ≤ 81 / 64 := by
      calc
        _ ≤ (initial - c) ^ 2 := hdecay
        _ ≤ (9 / 8 : ℝ) ^ 2 := hinitial_sq
        _ = 81 / 64 := by norm_num
    have hsquare : (w.orbit (start + 12) - c) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
      nlinarith
    exact hsquare
  have habsSq : |w.orbit (start + 12) - c| ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    simpa [sq_abs] using herror_sq
  exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).1 habsSq

/-- ガウス階段の一段と、前後の段をつなぐための実軌道データ。 -/
structure GaussianStageRun where
  center : ℝ
  initial : ℝ
  start : ℝ
  initial_error_bound : |initial - center| ≤ 9 / 8
  initial_local : |initial - center| < 5 / 4
  witness : StageValleyWitness (gaussianStage center initial start initial_local)

/-- 状態0から始まる最初の段を作る。 -/
noncomputable def firstGaussianStageRun (center : ℝ)
    (hcenter : |(0 : ℝ) - center| ≤ 9 / 8) : GaussianStageRun := by
  have hlocal : |(0 : ℝ) - center| < 5 / 4 := by
    have : (9 / 8 : ℝ) < 5 / 4 := by norm_num
    exact lt_of_le_of_lt hcenter this
  exact ⟨center, 0, 0, hcenter, hlocal,
    chooseStageValley (gaussianStage center 0 0 hlocal)⟩

/-- 次の段を追加する。前段の終点誤差1/8以下と中心移動量1以下から、
次段の初期状態が中心から半径5/4以内にあることを保証する。 -/
noncomputable def nextGaussianStageRun (run : GaussianStageRun)
    (nextCenter : ℝ) (hcenterStep : |run.center - nextCenter| ≤ 1) :
    GaussianStageRun := by
  let nextInitial := run.witness.orbit (run.start + 12)
  have herror : |nextInitial - nextCenter| ≤ 9 / 8 := by
    have hprev := gaussianStage_endpoint_error_12 run.initial_local
      run.witness run.initial_error_bound
    calc
      |nextInitial - nextCenter| ≤
          |nextInitial - run.center| + |run.center - nextCenter| := abs_sub_le _ _ _
      _ ≤ 1 / 8 + 1 := add_le_add hprev hcenterStep
      _ = 9 / 8 := by norm_num
  have hlocal : |nextInitial - nextCenter| < 5 / 4 := by
    have hstrict : (9 / 8 : ℝ) < 5 / 4 := by norm_num
    exact lt_of_le_of_lt herror hstrict
  exact ⟨nextCenter, nextInitial, run.start + 12, herror, hlocal,
    chooseStageValley (gaussianStage nextCenter nextInitial (run.start + 12) hlocal)⟩

/-- 段軌道のガウス固有の強い評価を示す。この評価で(22.4)を確認し、
続いてスカラーの待ち時間条件(22.5)を適用できる。 -/
theorem gaussianStage_distance_decay {c initial start : ℝ}
    (hinitial : |initial - c| < 5 / 4)
    (w : StageValleyWitness (gaussianStage c initial start hinitial))
    {T : ℝ} (hT : 0 ≤ T) :
    dist (w.orbit (start + T)) c ≤ |initial - c| * Real.exp (-(1 / 2 : ℝ) * T) := by
  have hsq := gaussianStage_weighted_square_nonincreasing hinitial w hT
  have hExp : Real.exp (-(1 / 2 : ℝ) * T) ^ 2 = Real.exp (-T) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdistSq : dist (w.orbit (start + T)) c ^ 2 ≤
      (|initial - c| * Real.exp (-(1 / 2 : ℝ) * T)) ^ 2 := by
    rw [dist_eq_norm, Real.norm_eq_abs]
    have hdiv : (w.orbit (start + T) - c) ^ 2 ≤
        (initial - c) ^ 2 / Real.exp T := by
      apply (le_div_iff₀ (Real.exp_pos T)).2
      simpa [mul_comm] using hsq
    have hright : (|initial - c| * Real.exp (-(1 / 2 : ℝ) * T)) ^ 2 =
        (initial - c) ^ 2 / Real.exp T := by
      rw [mul_pow, sq_abs, hExp, Real.exp_neg]
      ring
    rw [hright]
    simpa [sq_abs] using hdiv
  exact (sq_le_sq₀ (dist_nonneg) (by positivity)).1 hdistSq

/-- 切替ごとの中心移動が1以下なら、実際の段データを再帰的に作る。
各段の実軌道終点を次段の初期値に使い、別に選んだ状態を代入しない。 -/
noncomputable def gaussianStageRunsAux (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) :
    (n : ℕ) → {run : GaussianStageRun // run.center = target n}
  | 0 => ⟨firstGaussianStageRun (target 0) hfirst, by simp [firstGaussianStageRun]⟩
  | n + 1 => by
      let prev := gaussianStageRunsAux target hfirst hstep n
      have hmove : |prev.val.center - target (n + 1)| ≤ 1 := by
        rw [prev.property]
        exact hstep n
      exact ⟨nextGaussianStageRun prev.val (target (n + 1)) hmove,
        by simp [nextGaussianStageRun, prev.property]⟩

noncomputable def gaussianStageRuns (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) : ℕ → GaussianStageRun :=
  fun n => (gaussianStageRunsAux target hfirst hstep n).val

theorem gaussianStageRuns_center (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) (n : ℕ) :
    (gaussianStageRuns target hfirst hstep n).center = target n := by
  exact (gaussianStageRunsAux target hfirst hstep n).property

noncomputable def gaussianStageRunTime (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) (n : ℕ) :
    ℝ := (gaussianStageRuns target hfirst hstep n).start

theorem gaussianStageRuns_time_recurrence (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) (n : ℕ) :
    gaussianStageRunTime target hfirst hstep (n + 1) =
      gaussianStageRunTime target hfirst hstep n + 12 := by
  simp [gaussianStageRunTime, gaussianStageRuns, gaussianStageRunsAux,
    nextGaussianStageRun]

/-- Aの目標中心列。1,2,3,4と進み、その後は4で一定にする。 -/
def targetA (n : ℕ) : ℝ := ((min (n + 1) 4 : ℕ) : ℝ)

theorem targetA_first : |(0 : ℝ) - targetA 0| ≤ 9 / 8 := by
  norm_num [targetA]

theorem targetA_step (n : ℕ) : |targetA n - targetA (n + 1)| ≤ 1 := by
  have hmono : min (n + 1) 4 ≤ min (n + 2) 4 := by omega
  have hgap : min (n + 2) 4 ≤ min (n + 1) 4 + 1 := by omega
  have hmonoR : targetA n ≤ targetA (n + 1) := by
    dsimp [targetA]
    exact_mod_cast hmono
  have hgapR : targetA (n + 1) ≤ targetA n + 1 := by
    dsimp [targetA]
    exact_mod_cast hgap
  rw [abs_of_nonpos (sub_nonpos.mpr hmonoR)]
  linarith

/-- Cの目標中心列。1,1,2と進み、その後は2で一定にする。 -/
def targetC (n : ℕ) : ℝ := if n < 2 then 1 else 2

theorem targetC_first : |(0 : ℝ) - targetC 0| ≤ 9 / 8 := by
  norm_num [targetC]

theorem targetC_step (n : ℕ) : |targetC n - targetC (n + 1)| ≤ 1 := by
  by_cases h : n < 2
  · have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with rfl | rfl <;> norm_num [targetC]
  · have hn : ¬ n + 1 < 2 := by omega
    simp [targetC, h, hn]

noncomputable def runsA : ℕ → GaussianStageRun :=
  gaussianStageRuns targetA targetA_first targetA_step

noncomputable def runsC : ℕ → GaussianStageRun :=
  gaussianStageRuns targetC targetC_first targetC_step

theorem runsA_centers (n : ℕ) : (runsA n).center = targetA n :=
  gaussianStageRuns_center targetA targetA_first targetA_step n

theorem runsC_centers (n : ℕ) : (runsC n).center = targetC n :=
  gaussianStageRuns_center targetC targetC_first targetC_step n

theorem runsA_endpoint_error (n : ℕ) :
    |(runsA n).witness.orbit ((runsA n).start + 12) - (runsA n).center| ≤ 1 / 8 :=
  gaussianStage_endpoint_error_12 (runsA n).initial_local (runsA n).witness
    (runsA n).initial_error_bound

theorem runsC_endpoint_error (n : ℕ) :
    |(runsC n).witness.orbit ((runsC n).start + 12) - (runsC n).center| ≤ 1 / 8 :=
  gaussianStage_endpoint_error_12 (runsC n).initial_local (runsC n).witness
    (runsC n).initial_error_bound

noncomputable def runsStages (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) :
    ℕ → StageValleySpec ℝ := fun n =>
      gaussianStage (gaussianStageRuns target hfirst hstep n).center
        (gaussianStageRuns target hfirst hstep n).initial
        (gaussianStageRuns target hfirst hstep n).start
        (gaussianStageRuns target hfirst hstep n).initial_local

noncomputable def runsWitnesses (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) :
    ∀ n, StageValleyWitness (runsStages target hfirst hstep n) :=
  fun n => (gaussianStageRuns target hfirst hstep n).witness

def gaussianStageRunDuration (_n : ℕ) : ℝ := 12

theorem gaussianStageRunDuration_pos (n : ℕ) : 0 < gaussianStageRunDuration n := by
  norm_num [gaussianStageRunDuration]

theorem gaussianStageRunDuration_diverges (B : ℝ) :
    ∃ n, B < ∑ k ∈ Finset.range n, gaussianStageRunDuration k := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / 12)
  refine ⟨n, ?_⟩
  have hsum : (∑ k ∈ Finset.range n, gaussianStageRunDuration k) = (n : ℝ) * 12 := by
    simp [gaussianStageRunDuration]
  rw [hsum]
  nlinarith

noncomputable def runsActive (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) : ℝ → ℕ := by
  let timing := switching_times_unbounded gaussianStageRunDuration
    (gaussianStageRunTime target hfirst hstep)
    (fun n => gaussianStageRunDuration_pos n)
    (fun n => gaussianStageRuns_time_recurrence target hfirst hstep n)
    gaussianStageRunDuration_diverges
  exact canonicalSwitchStageIndex (gaussianStageRunTime target hfirst hstep)
    (strictMono_nat_of_lt_succ timing.2) timing.1

noncomputable def runsTrajectory (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) : ℝ → ℝ :=
  stitchedStageOrbit (runsStages target hfirst hstep)
    (runsWitnesses target hfirst hstep) (runsActive target hfirst hstep)

theorem runsStage_start (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) (n : ℕ) :
    (runsStages target hfirst hstep n).startTime =
      gaussianStageRunTime target hfirst hstep n := rfl

theorem gaussianStageRuns_transition (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) (n : ℕ) :
    (gaussianStageRuns target hfirst hstep (n + 1)).initial =
      (gaussianStageRuns target hfirst hstep n).witness.orbit
        (gaussianStageRunTime target hfirst hstep n + 12) := by
  simp [gaussianStageRunTime, gaussianStageRuns, gaussianStageRunsAux,
    nextGaussianStageRun]

theorem runsStage_transition (target : ℕ → ℝ)
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) (n : ℕ) :
    (runsStages target hfirst hstep (n + 1)).initial =
      (runsWitnesses target hfirst hstep n).orbit
        (gaussianStageRunTime target hfirst hstep n + gaussianStageRunDuration n) := by
  simpa [runsStages, runsWitnesses, gaussianStageRunTime,
    gaussianStageRunDuration, gaussianStage] using gaussianStageRuns_transition target hfirst hstep n

theorem runs_stage_agreement {target : ℕ → ℝ}
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) (n : ℕ) :
    Set.EqOn (runsTrajectory target hfirst hstep)
        (runsWitnesses target hfirst hstep n).orbit
        (Set.Icc (gaussianStageRunTime target hfirst hstep n)
          (gaussianStageRunTime target hfirst hstep n + gaussianStageRunDuration n)) ∧
      ContinuousOn (runsTrajectory target hfirst hstep)
        (Set.Icc (gaussianStageRunTime target hfirst hstep n)
          (gaussianStageRunTime target hfirst hstep n + gaussianStageRunDuration n)) ∧
      (∀ t ∈ Set.Ico (gaussianStageRunTime target hfirst hstep n)
          (gaussianStageRunTime target hfirst hstep n + gaussianStageRunDuration n),
        runsTrajectory target hfirst hstep t ∈
          Metric.closedBall (runsStages target hfirst hstep n).center
            (runsStages target hfirst hstep n).radius) ∧
      (∀ t ∈ Set.Ico (gaussianStageRunTime target hfirst hstep n)
          (gaussianStageRunTime target hfirst hstep n + gaussianStageRunDuration n),
        HasDerivWithinAt (runsTrajectory target hfirst hstep)
          (-((runsStages target hfirst hstep n).mobility
              (runsTrajectory target hfirst hstep t)
              (stageEffectiveGradient (runsStages target hfirst hstep n)
                (runsTrajectory target hfirst hstep t))))
          (Set.Ici t) t) := by
  let duration := gaussianStageRunDuration
  let time := gaussianStageRunTime target hfirst hstep
  let stages := runsStages target hfirst hstep
  let witnesses := runsWitnesses target hfirst hstep
  let timing := switching_times_unbounded duration time
    (fun k => gaussianStageRunDuration_pos k)
    (fun k => gaussianStageRuns_time_recurrence target hfirst hstep k)
    gaussianStageRunDuration_diverges
  let timeStrict : StrictMono time := strictMono_nat_of_lt_succ timing.2
  have hactive : ∀ k t, t ∈ Set.Ico (time k) (time k + duration k) →
      runsActive target hfirst hstep t = k := by
    intro k t ht
    change canonicalSwitchStageIndex time timeStrict timing.1 t = k
    exact canonicalSwitchStageIndex_eq_on_dwell time duration timeStrict timing.1
      (fun j => gaussianStageRuns_time_recurrence target hfirst hstep j) k ht
  have hactiveEnd : ∀ k, runsActive target hfirst hstep (time k + duration k) = k + 1 := by
    intro k
    have hrecur := gaussianStageRuns_time_recurrence target hfirst hstep k
    change canonicalSwitchStageIndex time timeStrict timing.1
      (gaussianStageRunTime target hfirst hstep k + 12) = k + 1
    rw [← hrecur]
    exact canonicalSwitchStageIndex_eq_next_at_endpoint time timeStrict timing.1 k
  have hstart : ∀ k, (stages k).startTime = time k := fun k => rfl
  have htransition : ∀ k, (stages (k + 1)).initial =
      (witnesses k).orbit (time k + duration k) := by
    intro k
    simpa [stages, witnesses, time, duration, runsStages, runsWitnesses,
      gaussianStageRunTime, gaussianStageRunDuration, gaussianStage] using
      runsStage_transition target hfirst hstep k
  have hsolution := stitched_stage_orbits_form_a_switching_solution
    stages witnesses (runsActive target hfirst hstep) time duration hstart
    (fun k => gaussianStageRuns_time_recurrence target hfirst hstep k)
    hactive hactiveEnd htransition
  refine ⟨hsolution.1 n, hsolution.2.1 n, hsolution.2.2.1 n, ?_⟩
  intro t ht
  simpa [runsTrajectory, stages, witnesses, stitchedStageOrbit,
    stageEffectiveGradient] using hsolution.2.2.2 n t ht

/-- 接合した各ガウス段は、実際の段初期誤差を係数とする指数評価(22.4)を
収束率1/2で満たす。 -/
theorem runs_actual_exponential_decay {target : ℕ → ℝ}
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) (n : ℕ)
    {T : ℝ} (hT0 : 0 ≤ T) (hT : T ≤ gaussianStageRunDuration n) :
    dist (runsTrajectory target hfirst hstep
      (gaussianStageRunTime target hfirst hstep n + T))
        (gaussianStageRuns target hfirst hstep n).center ≤
      |(gaussianStageRuns target hfirst hstep n).initial -
          (gaussianStageRuns target hfirst hstep n).center| *
        Real.exp (-(1 / 2 : ℝ) * T) := by
  have hagree := (runs_stage_agreement hfirst hstep n).1
  have hmem : gaussianStageRunTime target hfirst hstep n + T ∈
      Set.Icc (gaussianStageRunTime target hfirst hstep n)
        (gaussianStageRunTime target hfirst hstep n + gaussianStageRunDuration n) :=
    ⟨le_add_of_nonneg_right hT0, by
      calc
        _ = T + gaussianStageRunTime target hfirst hstep n := by ring
        _ ≤ gaussianStageRunDuration n + gaussianStageRunTime target hfirst hstep n := by
          simpa [add_comm] using
            add_le_add_left hT (gaussianStageRunTime target hfirst hstep n)
        _ = _ := by ring⟩
  rw [hagree hmem]
  simpa [runsStages, runsWitnesses, gaussianStageRunTime] using
    gaussianStage_distance_decay
      (gaussianStageRuns target hfirst hstep n).initial_local
      (gaussianStageRuns target hfirst hstep n).witness hT0

/-- C=9/8、ε=1/8、収束率1/2の場合に、Pythonの段時間T=12が
スカラーの対数型待ち時間条件(22.5)を満たす。 -/
theorem gaussian_python_wait_12 :
    max 0 (2 * Real.log (9 : ℝ)) ≤ 12 := by
  have h3 : 4 ≤ Real.exp (3 : ℝ) := by
    have h := Real.add_one_le_exp (3 : ℝ)
    norm_num at h ⊢
    linarith
  have h6 : 9 ≤ Real.exp (6 : ℝ) := by
    rw [show (6 : ℝ) = 3 + 3 by norm_num, Real.exp_add]
    have hpos : 0 ≤ Real.exp (3 : ℝ) := le_of_lt (Real.exp_pos _)
    nlinarith [sq_nonneg (Real.exp (3 : ℝ) - 4)]
  have hlog : Real.log (9 : ℝ) ≤ 6 :=
    (Real.log_le_iff_le_exp (by norm_num)).2 h6
  exact (max_le_iff).2 ⟨by norm_num, by nlinarith⟩

/-- ガウスの鋭い評価(22.4)に待ち時間条件(22.5)を適用する。
Pythonの段時間12秒後、実際の切替軌道の終点誤差は1/8以内になる。 -/
theorem runs_actual_endpoint_error_via_22_5 {target : ℕ → ℝ}
    (hfirst : |(0 : ℝ) - target 0| ≤ 9 / 8)
    (hstep : ∀ n, |target n - target (n + 1)| ≤ 1) (n : ℕ) :
    dist (runsTrajectory target hfirst hstep
      (gaussianStageRunTime target hfirst hstep n + 12))
        (gaussianStageRuns target hfirst hstep n).center ≤ 1 / 8 := by
  apply exponential_distance_reaches_error_after_dwell
    (runsTrajectory target hfirst hstep)
    (gaussianStageRuns target hfirst hstep n).center
    (gaussianStageRunTime target hfirst hstep n) 12 (9 / 8) (1 / 8) (1 / 2) 1
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hratio : (9 / 8 : ℝ) / (1 / 8) = 9 := by norm_num
    rw [hratio]
    convert gaussian_python_wait_12 using 1 <;> norm_num
  · have hdecay := runs_actual_exponential_decay hfirst hstep n
      (T := 12) (by norm_num) (by norm_num [gaussianStageRunDuration])
    have hC := (gaussianStageRuns target hfirst hstep n).initial_error_bound
    have hexp_nonneg : 0 ≤ Real.exp (-(1 / 2 : ℝ) * 12) := le_of_lt (Real.exp_pos _)
    apply le_trans hdecay
    convert mul_le_mul_of_nonneg_right hC hexp_nonneg using 1 <;> ring

theorem targetA_python_prefix :
    targetA 0 = 1 ∧ targetA 1 = 2 ∧ targetA 2 = 3 ∧ targetA 3 = 4 ∧
      targetA 4 = 4 := by
  norm_num [targetA]

theorem targetC_python_prefix :
    targetC 0 = 1 ∧ targetC 1 = 1 ∧ targetC 2 = 2 ∧ targetC 3 = 2 := by
  norm_num [targetC]

noncomputable def caseBField (x : ℝ) : ℝ := -dwell 2 (3 / 2) 6 x

/-- PythonのケースAにある4つの増加する中心を、実際の連続接合軌道で表す。
各段は段内ODEを満たし、12秒後に指定した終点誤差1/8以内へ入る。 -/
theorem caseA_actual_stage_endpoint (n : ℕ) :
    dist (runsTrajectory targetA targetA_first targetA_step
      (gaussianStageRunTime targetA targetA_first targetA_step n + 12))
        (runsA n).center ≤ 1 / 8 := by
  simpa [runsA] using
    runs_actual_endpoint_error_via_22_5 targetA_first targetA_step n

/-- PythonのケースCでは中心が変わらない段も含めて、同じ接合軌道構成と
終点誤差評価を使う。中心移動が0の切替も扱う。 -/
theorem caseC_actual_stage_endpoint (n : ℕ) :
    dist (runsTrajectory targetC targetC_first targetC_step
      (gaussianStageRunTime targetC targetC_first targetC_step n + 12))
        (runsC n).center ≤ 1 / 8 := by
  simpa [runsC] using
    runs_actual_endpoint_error_via_22_5 targetC_first targetC_step n

/-- Bのベクトル場は全域で滑らかである。初期状態を含むコンパクトな
エネルギー部分準位集合を使い、初期値が次段の局所強凸球の外にあっても
前向きのグローバル解が存在することを示す。 -/
theorem exists_caseB_actual_flow :
    ∃ orbit : ℝ → ℝ, ∃ ε : ℝ, 0 < ε ∧ orbit 0 = 0 ∧
      (∀ t ∈ Set.Ici (0 : ℝ), orbit t ∈ Metric.closedBall 6 6) ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit
        (-dwell 2 (3 / 2) 6 (orbit t)) t) := by
  let K : Set ℝ := Metric.closedBall 6 6
  have hregular : ∀ x ∈ Metric.closedBall (6 : ℝ) 7,
      ContDiffAt ℝ 1 caseBField x := by
    intro x hx
    change ContDiffAt ℝ 1 (fun y => -dwell 2 (3 / 2) 6 y) x
    fun_prop [dwell]
  have hKcompact : IsCompact K := by
    exact isCompact_closedBall (6 : ℝ) 6
  have hKsubset : K ⊆ Metric.closedBall (6 : ℝ) 7 := by
    intro x hx
    have hdist : dist x 6 ≤ 6 := Metric.mem_closedBall.mp hx
    exact Metric.mem_closedBall.mpr (by linarith)
  have hKinterior : K ⊆ Metric.ball (6 : ℝ) 7 := by
    intro x hx
    have hdist : dist x 6 ≤ 6 := Metric.mem_closedBall.mp hx
    exact Metric.mem_ball.mpr (by linarith)
  have hinvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → ℝ) (x : ℝ),
      0 ≤ d → orbit t₀ = x → x ∈ K →
      (∀ t ∈ Set.Icc t₀ (t₀ + d), HasDerivAt orbit (caseBField (orbit t)) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ K := by
    intro t₀ d orbit x hd horbit hx hflow t ht
    have hpotential_deriv : ∀ s ∈ Set.Icc t₀ (t₀ + d),
        HasDerivAt (fun u => well 2 (3 / 2) 6 (orbit u))
          (dwell 2 (3 / 2) 6 (orbit s) * caseBField (orbit s)) s := by
      intro s hs
      exact (hasDerivAt_well 2 (3 / 2) 6 (orbit s) (by norm_num)).comp s
        (by simpa [caseBField] using (hflow s hs))
    have hpotential_anti : AntitoneOn
        (fun u => well 2 (3 / 2) 6 (orbit u)) (Set.Icc t₀ (t₀ + d)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ (t₀ + d))
      · intro s hs
        exact (hpotential_deriv s hs).continuousAt.continuousWithinAt
      · intro s hs
        exact (hpotential_deriv s (interior_subset hs)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [(hpotential_deriv s (interior_subset hs)).deriv]
        simp [caseBField]
        nlinarith [sq_nonneg (dwell 2 (3 / 2) 6 (orbit s))]
    have henergy : well 2 (3 / 2) 6 (orbit t) ≤ well 2 (3 / 2) 6 x := by
      have ht₀ : t₀ ∈ Set.Icc t₀ (t₀ + d) := ⟨le_rfl, by linarith⟩
      simpa [horbit] using hpotential_anti ht₀ ht ht.1
    have hdist : |orbit t - 6| ≤ |x - 6| :=
      (gaussian_well_le_iff_abs_le 6 (orbit t) x).1 henergy
    have hxDist : |x - 6| ≤ 6 := by
      have := Metric.mem_closedBall.mp hx
      simpa [dist_eq_norm, Real.norm_eq_abs] using this
    have hresult := hdist.trans hxDist
    simpa [K, Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hresult
  obtain ⟨orbit, ε, hε, hinitial, hforward, hflow, _hball⟩ :=
    exists_global_forward_trajectory_of_compact_forward_invariant_set
      caseBField K (6 : ℝ) 7 (by norm_num) hregular hKcompact hKsubset hKinterior
      hinvariant 0 (by
        change (0 : ℝ) ∈ Metric.closedBall 6 6
        norm_num [Metric.mem_closedBall, dist_eq_norm]) 0
  refine ⟨orbit, ε, hε, ?_, ?_, ?_⟩
  · simpa using hinitial
  · exact hforward
  · intro t ht
    have ht' : t ∈ Set.Ioi (0 - ε) := by simpa using ht
    simpa [caseBField] using hflow t ht'

/-- ガウス谷の尾部では、状態が[0,1]にあるときB段の速度は1/24以下。 -/
theorem caseB_speed_bound_on_unit_interval (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖caseBField x‖ ≤ 1 / 24 := by
  have hylo : 5 ≤ |x - 6| := by
    rw [abs_of_nonpos (by linarith : x - 6 ≤ 0)]
    linarith
  have hyhi : |x - 6| ≤ 6 := by
    rw [abs_of_nonpos (by linarith : x - 6 ≤ 0)]
    linarith
  have hysq : 25 ≤ (x - 6) ^ 2 := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|x - 6| - 5)]
  have hbase : 23 / 18 ≤ Real.exp (5 / 18 : ℝ) := by
    have h := Real.add_one_le_exp (5 / 18 : ℝ)
    norm_num at h ⊢
    linarith
  have hpow : (23 / 18 : ℝ) ^ 20 ≤ Real.exp (50 / 9 : ℝ) := by
    rw [show (50 / 9 : ℝ) = (20 : ℕ) * (5 / 18) by norm_num, Real.exp_nat_mul]
    gcongr
  have h128 : (128 : ℝ) ≤ Real.exp (50 / 9 : ℝ) := by
    have hnum : (128 : ℝ) ≤ (23 / 18 : ℝ) ^ 20 := by norm_num
    exact hnum.trans hpow
  have harg : (50 / 9 : ℝ) ≤ (x - 6) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2) := by
    norm_num
    nlinarith [hysq]
  have hexp : Real.exp (-((x - 6) ^ 2 /
      (2 * (3 / 2 : ℝ) ^ 2))) ≤ (1 / 128 : ℝ) := by
    have htail : Real.exp (-(50 / 9 : ℝ)) ≤ 1 / 128 := by
      have hinv : 1 / Real.exp (50 / 9 : ℝ) ≤ 1 / 128 := by
        rw [div_le_iff₀ (Real.exp_pos _)]
        nlinarith [h128]
      simpa [Real.exp_neg, one_div] using hinv
    exact (Real.exp_le_exp.mpr (neg_le_neg harg)).trans htail
  have hformula : |dwell 2 (3 / 2) 6 x| =
      (8 / 9 : ℝ) * |x - 6| *
        Real.exp (-((x - 6) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2))) := by
    have hcoeff : (2 : ℝ) * (x - 6) / (3 / 2 : ℝ) ^ 2 =
        (8 / 9 : ℝ) * (x - 6) := by ring
    rw [dwell, hcoeff]
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : 0 < (8 / 9 : ℝ)),
      abs_of_pos (Real.exp_pos _)]
    ring
  rw [Real.norm_eq_abs, caseBField, abs_neg, hformula]
  calc
    (8 / 9 : ℝ) * |x - 6| *
        Real.exp (-((x - 6) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2))) ≤
      (8 / 9 : ℝ) * 6 * (1 / 128 : ℝ) := by gcongr
    _ ≤ 1 / 24 := by norm_num

theorem caseBField_c1_on_large_ball : ∀ x ∈ Metric.closedBall (6 : ℝ) 7,
    ContDiffAt ℝ 1 caseBField x := by
  intro x hx
  change ContDiffAt ℝ 1 (fun y => -dwell 2 (3 / 2) 6 y) x
  fun_prop [dwell]

/-- B軌道が有限時刻で平衡点に到達したと仮定すると、逆向きのODE一意性から
それ以前の解も定数になってしまう。 -/
theorem caseB_orbit_never_hits_center (orbit : ℝ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hinit : orbit 0 = 0)
    (hforward : ∀ t ∈ Set.Ici (0 : ℝ), orbit t ∈ Metric.closedBall 6 6)
    (hflow : ∀ t ∈ Set.Ioi (-ε),
      HasDerivAt orbit (caseBField (orbit t)) t) :
    ∀ t ∈ Set.Ici (0 : ℝ), orbit t ≠ 6 := by
  intro t ht hhit
  by_cases hzero : t = 0
  · subst t
    rw [hinit] at hhit
    norm_num at hhit
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    obtain ⟨L, hL⟩ := exists_lipschitz_constant_on_closedBall_of_contDiffAt
      caseBField 6 7 caseBField_c1_on_large_ball
    have hflowIcc : ∀ s ∈ Set.Icc 0 t,
        HasDerivAt orbit (caseBField (orbit s)) s := by
      intro s hs
      have hs' : s ∈ Set.Ioi (-ε) := by change -ε < s; linarith [hs.1, hε]
      exact hflow s hs'
    have hballOrbit : ∀ s ∈ Set.Icc 0 t,
        orbit s ∈ Metric.closedBall (6 : ℝ) 7 := by
      intro s hs
      have hball := hforward s hs.1
      have hdist : dist (orbit s) 6 ≤ 6 := Metric.mem_closedBall.mp hball
      exact Metric.mem_closedBall.mpr (by linarith)
    have hEq := ODE_solution_unique_of_mem_Icc_left
      (v := fun _ : ℝ => caseBField) (s := fun _ => Metric.closedBall (6 : ℝ) 7)
      (K := L) (a := 0) (b := t) (fun _ _ => hL)
      (HasDerivAt.continuousOn fun s hs => hflowIcc s hs)
      (fun s hs => (hflowIcc s ⟨le_of_lt hs.1, hs.2⟩).hasDerivWithinAt.mono (Set.subset_univ _))
      (fun s hs => hballOrbit s ⟨le_of_lt hs.1, hs.2⟩)
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (6 : ℝ)) (Set.Icc 0 t))
      (fun s hs => by
        have hconst : HasDerivAt (fun _ : ℝ => (6 : ℝ)) (0 : ℝ) s :=
          hasDerivAt_const s 6
        have hzeroField : caseBField 6 = 0 := by simp [caseBField, dwell]
        simpa [hzeroField] using hconst.hasDerivWithinAt.mono (Set.subset_univ _))
      (fun _ _ => Metric.mem_closedBall.mpr (by simp)) hhit
    have hstart := hEq ⟨le_rfl, le_of_lt htpos⟩
    have : orbit 0 = 6 := hstart
    linarith [hinit]

/-- B軌道は任意の有限な前向き時刻で平衡点より左側にある。 -/
theorem caseB_orbit_lt_center (orbit : ℝ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hinit : orbit 0 = 0)
    (hflow : ∀ t ∈ Set.Ioi (-ε),
      HasDerivAt orbit (caseBField (orbit t)) t) (t : ℝ) (ht : 0 ≤ t)
    (hnever : ∀ s ∈ Set.Ici (0 : ℝ), orbit s ≠ 6) : orbit t < 6 := by
  by_contra h
  have h6le : 6 ≤ orbit t := le_of_not_gt h
  have hcont : ContinuousOn orbit (Set.Icc 0 t) := by
    apply HasDerivAt.continuousOn
    intro s hs
    have hs' : s ∈ Set.Ioi (-ε) := by change -ε < s; linarith [hs.1, hε]
    exact hflow s hs'
  have himage := intermediate_value_Icc ht hcont
  have hval : 6 ∈ Set.Icc (orbit 0) (orbit t) := by
    rw [hinit]
    exact ⟨by norm_num, h6le⟩
  obtain ⟨s, hs, hhit⟩ := himage hval
  exact (hnever s hs.1) hhit

/-- 平衡点より左では、B段のベクトル場は右向きである。 -/
theorem caseBField_pos_of_lt_center (x : ℝ) (hx : x < 6) : 0 < caseBField x := by
  rw [show caseBField x = (8 / 9 : ℝ) * (6 - x) *
      Real.exp (-((x - 6) ^ 2 / (2 * (3 / 2 : ℝ) ^ 2))) by
        simp [caseBField, dwell] <;> ring]
  positivity

/-- B軌道は平衡点の左側にとどまり、そこでベクトル場が正なので、
任意の有限区間で単調増加する。 -/
theorem caseB_orbit_monotoneOn (orbit : ℝ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hinit : orbit 0 = 0)
    (hflow : ∀ t ∈ Set.Ioi (-ε),
      HasDerivAt orbit (caseBField (orbit t)) t)
    (hnever : ∀ s ∈ Set.Ici (0 : ℝ), orbit s ≠ 6) (T : ℝ) (hT : 0 ≤ T) :
    MonotoneOn orbit (Set.Icc 0 T) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
  · exact HasDerivAt.continuousOn fun t ht => by
      have ht' : t ∈ Set.Ioi (-ε) := by change -ε < t; linarith [ht.1, hε]
      exact hflow t ht'
  · intro t ht
    have ht' : t ∈ Set.Ioi (-ε) := by
      change -ε < t
      have hti : t ∈ Set.Icc 0 T := interior_subset ht
      linarith [hti.1, hε]
    exact (hflow t ht').differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioi (-ε) := by
      change -ε < t
      have hti : t ∈ Set.Icc 0 T := interior_subset ht
      linarith [hti.1, hε]
    rw [(hflow t ht').deriv]
    exact (caseBField_pos_of_lt_center (orbit t)
      (caseB_orbit_lt_center orbit ε hε hinit hflow t (by
        have hti : t ∈ Set.Icc 0 T := interior_subset ht
        exact hti.1) hnever)).le

/-- B軌道は時刻12までに中心6から距離5以内へ入らない。
[0,1]での尾部速度が1/24以下であるため、距離1を進むにも12秒より長い
時間が必要となる。 -/
theorem caseB_orbit_outside_target_at_12 (orbit : ℝ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hinit : orbit 0 = 0)
    (hflow : ∀ t ∈ Set.Ioi (-ε),
      HasDerivAt orbit (caseBField (orbit t)) t)
    (hnever : ∀ s ∈ Set.Ici (0 : ℝ), orbit s ≠ 6) :
    dist (orbit 12) 6 > 5 := by
  have hmono := caseB_orbit_monotoneOn orbit ε hε hinit hflow hnever 12 (by norm_num)
  have hcont : ContinuousOn orbit (Set.Icc 0 12) := by
    exact HasDerivAt.continuousOn fun t ht => by
      have ht' : t ∈ Set.Ioi (-ε) := by change -ε < t; linarith [ht.1, hε]
      exact hflow t ht'
  have hcontS : ContinuousOn orbit (Set.Icc 0 12) := hcont
  have hlt : orbit 12 < 1 := by
    by_contra hn
    have hge : 1 ≤ orbit 12 := le_of_not_gt hn
    have hval : 1 ∈ Set.Icc (orbit 0) (orbit 12) := by
      rw [hinit]
      exact ⟨by norm_num, hge⟩
    obtain ⟨s, hs, hhit⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 12) hcont hval
    have hmono_segment := hmono (show 0 ∈ Set.Icc 0 12 by norm_num)
      (show s ∈ Set.Icc 0 12 from hs) hs.1
    have hderiv : ∀ u ∈ Set.Ico 0 s,
        HasDerivWithinAt orbit (caseBField (orbit u)) (Set.Ici u) u := by
      intro u hu
      have hu' : u ∈ Set.Ioi (-ε) := by change -ε < u; linarith [hu.1, hε]
      exact (hflow u hu').hasDerivWithinAt.mono (Set.subset_univ _)
    have hbound : ∀ u ∈ Set.Ico 0 s, ‖caseBField (orbit u)‖ ≤ 1 / 24 := by
      intro u hu
      have hmem : u ∈ Set.Icc 0 s := ⟨hu.1, le_of_lt hu.2⟩
      have huT : u ∈ Set.Icc 0 12 := ⟨hmem.1, le_trans hmem.2 hs.2⟩
      have hlow : 0 ≤ orbit u := by
        have hle := hmono (show 0 ∈ Set.Icc 0 12 by norm_num) huT huT.1
        rw [hinit] at hle
        exact hle
      have hhigh : orbit u ≤ 1 := by
        have hle := hmono huT hs hmem.2
        rw [hhit] at hle
        exact hle
      exact caseB_speed_bound_on_unit_interval (orbit u) hlow hhigh
    have hcontToS : ContinuousOn orbit (Set.Icc 0 s) := hcont.mono (Set.Icc_subset_Icc_right hs.2)
    have hdisp := norm_image_sub_le_of_norm_deriv_right_le_segment hcontToS hderiv hbound s
      (show s ∈ Set.Icc 0 s from ⟨by linarith [hs.1], le_rfl⟩)
    have hdistEq : |orbit s - orbit 0| = 1 := by rw [hhit, hinit]; norm_num
    have hdisp' : 1 ≤ (1 / 24 : ℝ) * s := by
      rw [Real.norm_eq_abs, hdistEq] at hdisp
      linarith
    have hsle : s ≤ 12 := hs.2
    nlinarith
  have hlt6 := caseB_orbit_lt_center orbit ε hε hinit hflow 12 (by norm_num) hnever
  have hdist : dist (orbit 12) 6 = 6 - orbit 12 := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    ring
  rw [hdist]
  linarith

/-- Bの最初の段の実軌道は、次の中心8の局所球に入らない。
中心6へ向かう最初の段を12秒動かしても終点は1未満なので、次の中心8から
7より大きく離れている。 -/
theorem exists_caseB_actual_switch_outside_next_ball :
    ∃ orbit : ℝ → ℝ, orbit 0 = 0 ∧ dist (orbit 12) 8 > 5 / 4 := by
  obtain ⟨orbit, ε, hε, hinit, hforward, hflow⟩ := exists_caseB_actual_flow
  have hnever : ∀ s ∈ Set.Ici (0 : ℝ), orbit s ≠ 6 :=
    caseB_orbit_never_hits_center orbit ε hε hinit hforward hflow
  have hdist6 := caseB_orbit_outside_target_at_12 orbit ε hε hinit hflow hnever
  have hlt6 := caseB_orbit_lt_center orbit ε hε hinit hflow 12 (by norm_num) hnever
  have hlt1 : orbit 12 < 1 := by
    have hdistEq : dist (orbit 12) 6 = 6 - orbit 12 := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      ring
    rw [hdistEq] at hdist6
    linarith
  have hdist8 : dist (orbit 12) 8 = 8 - orbit 12 := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    ring
  refine ⟨orbit, hinit, ?_⟩
  rw [hdist8]
  linarith


/-- 初期値0から中心6へ向かう実際のガウス勾配流が、12秒後にも次中心8の
局所球の外にあることを、ODEと同じ軌道について結論する。 -/
theorem exists_caseB_actual_switch_outside_next_ball_with_ode :
    ∃ (orbit : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ orbit 0 = 0 ∧
      dist (orbit 12) 8 > 5 / 4 ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit
        (-dwell 2 (3 / 2) 6 (orbit t)) t) := by
  obtain ⟨orbit, ε, hε, hinit, hforward, hflow⟩ := exists_caseB_actual_flow
  have hnever : ∀ s ∈ Set.Ici (0 : ℝ), orbit s ≠ 6 :=
    caseB_orbit_never_hits_center orbit ε hε hinit hforward hflow
  have hdist6 := caseB_orbit_outside_target_at_12 orbit ε hε hinit hflow hnever
  have hlt6 := caseB_orbit_lt_center orbit ε hε hinit hflow 12 (by norm_num) hnever
  have hlt1 : orbit 12 < 1 := by
    have hdistEq : dist (orbit 12) 6 = 6 - orbit 12 := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      ring
    rw [hdistEq] at hdist6
    linarith
  have hdist8 : dist (orbit 12) 8 = 8 - orbit 12 := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    ring
  refine ⟨orbit, ε, hε, hinit, ?_, hflow⟩
  rw [hdist8]
  linarith

end Tomabechi.Examples.Theorem22GaussianStages
