import Tomabechi.Consistency.ConsistencyR1_C3LayerConnection
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Defs.Induced

/-!
# R1: 横方向にも曲率を持つ二次H-stage

既存H-stageのスカラー平均場を対角上で保ちながら、二次元Euclidean空間の
両方向に負の曲率を持つ平均場入力を作る。段の原子法則は対応する共通束層の
Dirac lawであり、しきい値・初期sublevel・障壁・移動度も入力recordに含める。
-/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Tomabechi.Consistency.R1

abbrev LiftedStageState := EuclideanSpace ℝ (Fin 2)
abbrev LiftedStageAtom := Tomabechi.Consistency.C3.Atom

def liftedStageCenter (c : ℝ) : LiftedStageState :=
  WithLp.toLp 2 (fun _ : Fin 2 => c / Real.sqrt 2)

def liftedStageMeanField (c : ℝ) (x : LiftedStageState) : ℝ :=
  (-(1 / 2 : ℝ)) • ‖x - liftedStageCenter c‖ ^ 2

theorem liftedStageCenter_difference_norm_sq (x y : ℝ) :
    ‖liftedStageCenter x - liftedStageCenter y‖ ^ 2 = (x - y) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [liftedStageCenter, Real.norm_eq_abs]
  field_simp
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem liftedStageCenter_difference_norm (x y : ℝ) :
    ‖liftedStageCenter x - liftedStageCenter y‖ = |x - y| := by
  have hsq := liftedStageCenter_difference_norm_sq x y
  have hn : 0 ≤ ‖liftedStageCenter x - liftedStageCenter y‖ := norm_nonneg _
  have ha : 0 ≤ |x - y| := abs_nonneg _
  nlinarith [hsq, sq_abs (x - y)]

theorem liftedStage_closedBall_mem_iff (c x₀ x : ℝ) :
    liftedStageCenter x ∈ Metric.closedBall (liftedStageCenter c)
        ‖liftedStageCenter x₀ - liftedStageCenter c‖ ↔
      x ∈ Metric.closedBall c |x₀ - c| := by
  simp only [Metric.mem_closedBall, dist_eq_norm]
  rw [liftedStageCenter_difference_norm x c,
    liftedStageCenter_difference_norm x₀ c]
  simp [Real.norm_eq_abs]

def liftedStageMeanFieldGradient (c : ℝ) (x : LiftedStageState) : LiftedStageState :=
  (-1 : ℝ) • (x - liftedStageCenter c)

def liftedStageMeanFieldHessian (_c : ℝ) (_x : LiftedStageState) :
    LiftedStageState →L[ℝ] LiftedStageState :=
  (-1 : ℝ) • ContinuousLinearMap.id ℝ LiftedStageState

def liftedStageMobility (_x : LiftedStageState) :
    LiftedStageState →L[ℝ] LiftedStageState :=
  (1 : ℝ) • ContinuousLinearMap.id ℝ LiftedStageState

/-- Explicit gradient-flow orbit for the lifted quadratic field. -/
def liftedStageOrbit (c : ℝ) (initial : LiftedStageState) (start t : ℝ) :
    LiftedStageState :=
  liftedStageCenter c + Real.exp (-(t - start)) •
    (initial - liftedStageCenter c)

theorem liftedStageOrbit_hasDerivAt (c : ℝ) (initial : LiftedStageState)
    (start t : ℝ) :
    HasDerivAt (liftedStageOrbit c initial start)
      (-(liftedStageOrbit c initial start t - liftedStageCenter c)) t := by
  have harg : HasDerivAt (fun u : ℝ => -(u - start)) (-1) t := by
    convert ((hasDerivAt_id t).sub_const start).neg using 1
    · funext u
      simp
  have hexp := (Real.hasDerivAt_exp (-(t - start))).comp t harg
  have hsmul := hexp.smul_const (initial - liftedStageCenter c)
  have hsum := (hasDerivAt_const t (liftedStageCenter c)).add hsmul
  convert hsum using 1 <;> ext i <;> simp [liftedStageOrbit, smul_eq_mul] <;> ring

theorem liftedStageOrbit_distance (c : ℝ) (initial : LiftedStageState)
    (start t : ℝ) :
    dist (liftedStageOrbit c initial start t) (liftedStageCenter c) =
      Real.exp (-(t - start)) * dist initial (liftedStageCenter c) := by
  rw [dist_eq_norm, liftedStageOrbit]
  simp only [add_sub_cancel_left]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), dist_eq_norm]

theorem liftedStageOrbit_mem_closedBall (c : ℝ) (initial : LiftedStageState)
    (start t radius : ℝ) (ht : start ≤ t)
    (hinitial : initial ∈ Metric.closedBall (liftedStageCenter c) radius) :
    liftedStageOrbit c initial start t ∈ Metric.closedBall
      (liftedStageCenter c) radius := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  rw [liftedStageOrbit]
  simp only [add_sub_cancel_left]
  rw [norm_smul, Real.norm_eq_abs]
  have hexp : 0 ≤ Real.exp (-(t - start)) := le_of_lt (Real.exp_pos _)
  have hexp_le : Real.exp (-(t - start)) ≤ 1 := by
    apply (Real.exp_le_one_iff).2
    linarith
  have hdist := Metric.mem_closedBall.mp hinitial
  calc
    |Real.exp (-(t - start))| * ‖initial - liftedStageCenter c‖ ≤
        ‖initial - liftedStageCenter c‖ := by
      rw [abs_of_nonneg hexp]
      nlinarith [norm_nonneg (initial - liftedStageCenter c)]
    _ ≤ radius := by simpa [dist_eq_norm] using hdist

/-- The 2D average presentation uses the same atomic index and representation
as the original H-stage, with a Dirac measure at the stage's LUB atom. -/
def liftedStageAveragePresentation (n : ℕ) :
    Tomabechi.Theorem22.MeanFieldAveragePresentation LiftedStageState := by
  classical
  letI : TopologicalSpace LiftedStageAtom := ⊥
  letI : DiscreteTopology LiftedStageAtom := ⟨rfl⟩
  letI : MeasurableSpace LiftedStageAtom := ⊤
  let p : LiftedStageAtom := (n + 1 : ℕ)
  let μ : Measure LiftedStageAtom := Measure.dirac p
  refine
    { Atom := LiftedStageAtom
      atomOrder := inferInstance
      abstractTop := ⊤
      abstractTop_greatest := fun _ => le_top
      sourceLayer := {p}
      abstractTop_not_in_sourceLayer := by
        change (⊤ : WithTop ℕ) ≠ WithTop.some (n + 1)
        intro h
        cases h
      atomTopology := inferInstance
      atomMeasurableSpace := inferInstance
      atomMeasure := μ
      atomMeasure_probability := inferInstance
      measureSupport := {p}
      measureSupport_eq_topological_support := by
        dsimp [μ]
        rw [Measure.support_eq_forall_isOpen]
        ext a
        change a = p ↔ (∀ U : Set LiftedStageAtom, a ∈ U → IsOpen U → 0 < μ U)
        by_cases ha : a = p
        · subst a
          constructor
          · intro _ U hmem _
            rw [Measure.dirac_apply_of_mem hmem]
            exact zero_lt_one
          · intro _
            rfl
        · constructor
          · intro heq
            exact (ha heq).elim
          · intro h
            have hopen : IsOpen ({a} : Set LiftedStageAtom) := isOpen_discrete _
            have hpa : p ≠ a := fun h => ha h.symm
            have hz : μ ({a} : Set LiftedStageAtom) = 0 := by
              dsimp [μ]
              rw [Measure.dirac_apply]
              simp [hpa]
            have hp := h {a} (by simp) hopen
            rw [hz] at hp
            exact False.elim ((lt_irrefl 0) hp)
      measureSupport_measurable := by simp
      measureSupport_full := by dsimp [μ, p]; simp
      measureSupport_subset_sourceLayer := by
        intro a ha
        simp only [Set.mem_singleton_iff] at ha
        have hne : p ≠ (⊤ : LiftedStageAtom) := by simp [p]
        simpa [ha] using hne
      supportLub := p
      supportLub_upper := by
        intro a ha
        have hap : a = p := Set.mem_singleton_iff.mp ha
        subst a
        exact le_rfl
      supportLub_least := by
        intro b hb
        exact hb p (by simp)
      supportLub_mem_sourceLayer := by simp [p]
      centerRepresentation := fun a => liftedStageCenter (Tomabechi.Consistency.C3.representation a)
      reconstructionKernel := fun x a => liftedStageMeanField
        (Tomabechi.Consistency.C3.representation a) x
      reconstructionKernel_integrable := by
        intro x
        simpa [μ] using (integrable_dirac
          (f := fun a => liftedStageMeanField
            (Tomabechi.Consistency.C3.representation a) x) (by simp)) }

theorem liftedStageAveragePresentation_integral (n : ℕ) (x : LiftedStageState) :
    (liftedStageAveragePresentation n).integralValue x =
      liftedStageMeanField
        (Tomabechi.Consistency.C3.representation ((n + 1 : ℕ) : LiftedStageAtom)) x := by
  classical
  letI : MeasurableSpace LiftedStageAtom := ⊤
  unfold Tomabechi.Theorem22.MeanFieldAveragePresentation.integralValue
    liftedStageAveragePresentation
  dsimp
  rw [integral_dirac]

/-- One complete, two-dimensional H-stage input. The selected centers and
initial states are the diagonal lifts of the original stage's data. -/
noncomputable def liftedHStageInput (n : ℕ) :
    Tomabechi.Theorem22.MeanFieldStageInput LiftedStageState := by
  let c : ℝ := Tomabechi.Consistency.C3.representation (n + 1)
  let x₀ : ℝ := (Tomabechi.Consistency.C3.hStageSequence n).initial
  let center := liftedStageCenter c
  let initial : LiftedStageState := liftedStageCenter x₀
  let d : ℝ := ‖initial - center‖
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
      startTime := Tomabechi.Consistency.C3.stageTime n
      background := fun _ => 0
      meanField := liftedStageMeanField c
      averagePresentation := liftedStageAveragePresentation n
      center_eq_supportLub_representation := ?_
      meanField_eq_integral := ?_
      backgroundGradient := fun _ => 0
      meanFieldGradient := liftedStageMeanFieldGradient c
      backgroundHessian := fun _ => 0
      meanFieldHessian := liftedStageMeanFieldHessian c
      mobility := liftedStageMobility
      sublevel := Metric.closedBall center d
      initial := initial
      radius_pos := by dsimp [R]; positivity
      gain_pos := by norm_num
      curvature_pos := by norm_num
      backgroundCurvature_nonneg := by norm_num
      gradientBound_nonneg := by norm_num
      gain_threshold := by norm_num [R]
      background_c2_at := by intro y hy; fun_prop
      meanField_c2_at := by
        intro y hy
        have hid : ContDiffAt ℝ 2 (fun z : LiftedStageState => z) y := contDiffAt_id
        have hc : ContDiffAt ℝ 2 (fun _ : LiftedStageState => center) y := contDiffAt_const
        have hdiff : ContDiffAt ℝ 2 (fun z : LiftedStageState => z - center) y := by
          simpa using hid.sub hc
        have hnorm : ContDiffAt ℝ 2
            (fun z : LiftedStageState => ‖z - center‖ ^ 2) y :=
          ContDiffAt.norm_sq (𝕜 := ℝ) hdiff
        change ContDiffAt ℝ 2 (fun z : LiftedStageState =>
          (-(1 / 2 : ℝ)) • ‖z - center‖ ^ 2) y
        exact hnorm.const_smul (-(1 / 2 : ℝ))
      background_gradient_representation := by intro y; simp
      meanField_gradient_representation := ?_
      background_gradient_deriv := by intro y hy; simpa using hasFDerivAt_const (0 : LiftedStageState) y
      meanField_gradient_deriv := ?_
      mobility_c1 := by intro y hy; fun_prop [liftedStageMobility]
      mobility_symmetric := ?_
      background_hessian_lower := by intro y hy w; simp
      meanField_hessian_upper := ?_
      meanField_center_stationary := by simp [liftedStageMeanFieldGradient, center]
      background_gradient_bound := by intro y hy; simp
      initial_mem := by
        dsimp [d]
        simp [dist_eq_norm]
      sublevel_barrier := ?_
      gamma_pos := by norm_num
      mobility_coercive := ?_
      sublevel_eq := ?_ }
  · change liftedStageCenter c =
      liftedStageCenter
        (Tomabechi.Consistency.C3.representation
          ((n + 1 : ℕ) : LiftedStageAtom))
    rfl
  · intro y
    rw [liftedStageAveragePresentation_integral]
    rfl
  · intro y
    have hshift : HasFDerivAt (fun z : LiftedStageState => z - center)
        (ContinuousLinearMap.id ℝ LiftedStageState) y := by
      simpa using (hasFDerivAt_id y).sub_const center
    have hpres := hshift.norm_sq.const_smul (-(1 / 2 : ℝ))
    change innerSL ℝ ((-1 : ℝ) • (y - center)) =
      fderiv ℝ ((-(1 / 2 : ℝ)) • fun z : LiftedStageState =>
        ‖z - center‖ ^ 2) y
    have hfd := hpres.fderiv
    rw [hfd]
    ext w
    simp [liftedStageMeanFieldGradient, innerSL_apply_apply,
      real_inner_comm, smul_eq_mul]
  · intro y hy
    have hshift : HasFDerivAt (fun z : LiftedStageState => z - center)
        (ContinuousLinearMap.id ℝ LiftedStageState) y := by
      simpa using (hasFDerivAt_id y).sub_const center
    change HasFDerivAt (fun z : LiftedStageState =>
      (-1 : ℝ) • (z - center))
      ((-1 : ℝ) • ContinuousLinearMap.id ℝ LiftedStageState) y
    exact hshift.const_smul (-1 : ℝ)
  · intro y hy v w
    simp [liftedStageMobility, real_inner_smul_left, real_inner_smul_right]
  · intro y hy w
    simp [liftedStageMeanFieldHessian, real_inner_self_eq_norm_sq,
      real_inner_smul_left]
  · have hclosed : IsClosed (Metric.closedBall center d) := Metric.isClosed_closedBall
    rw [hclosed.closure_eq]
    intro y hy
    apply Metric.mem_ball.mpr
    have hdist := Metric.mem_closedBall.mp hy
    have hR : d < d + 1 := by linarith
    exact lt_of_le_of_lt hdist hR
  · intro y hy w
    simp [liftedStageMobility, real_inner_self_eq_norm_sq,
      real_inner_smul_left]
  · dsimp [d, R, Tomabechi.Theorem22.stageEffectivePotential,
      liftedStageMeanField]
    ext y
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm]
    constructor
    · intro h
      have hd : d = ‖initial - center‖ := rfl
      constructor
      · linarith [norm_nonneg (y - center)]
      · have hsq : ‖y - center‖ ^ 2 ≤ ‖initial - center‖ ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 h
        norm_num
        nlinarith [hsq]
    · rintro ⟨_, henergy⟩
      norm_num at henergy
      have hysq : ‖y - liftedStageCenter c‖ ^ 2 ≤
          ‖initial - liftedStageCenter c‖ ^ 2 := by nlinarith
      have hysq' : ‖y - center‖ ^ 2 ≤ ‖initial - center‖ ^ 2 := by
        simpa [center] using hysq
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hysq'

/-- The lifted mean field retains the exact original H-stage average field
on the diagonal subspace. -/
theorem liftedHStageInput_orbit_derivative (n : ℕ)
    (initial : LiftedStageState) (t : ℝ) :
    HasDerivAt
      (liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
        initial (Tomabechi.Consistency.C3.stageTime n))
      (-(liftedHStageInput n).mobility
          (liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
            initial (Tomabechi.Consistency.C3.stageTime n) t)
          ((liftedHStageInput n).backgroundGradient
              (liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
                initial (Tomabechi.Consistency.C3.stageTime n) t) -
            ((liftedHStageInput n).gain * (liftedHStageInput n).presenceGain) •
              (liftedHStageInput n).meanFieldGradient
                (liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
                  initial (Tomabechi.Consistency.C3.stageTime n) t))) t := by
  have h := liftedStageOrbit_hasDerivAt
    (Tomabechi.Consistency.C3.representation (n + 1)) initial
    (Tomabechi.Consistency.C3.stageTime n) t
  simpa [liftedHStageInput, liftedStageMobility,
    liftedStageMeanFieldGradient, smul_eq_mul] using h

theorem liftedHStageInput_orbit_forwardInvariant (n : ℕ)
    (initial : LiftedStageState)
    (hinitial : initial ∈ (liftedHStageInput n).sublevel)
    (t : ℝ) (ht : (liftedHStageInput n).startTime ≤ t) :
    liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
      initial (Tomabechi.Consistency.C3.stageTime n) t ∈
        (liftedHStageInput n).sublevel := by
  change initial ∈ Metric.closedBall
      (liftedStageCenter (Tomabechi.Consistency.C3.representation (n + 1))) _ at hinitial
  change liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
      initial (Tomabechi.Consistency.C3.stageTime n) t ∈ Metric.closedBall
        (liftedStageCenter (Tomabechi.Consistency.C3.representation (n + 1))) _
  apply liftedStageOrbit_mem_closedBall
    (Tomabechi.Consistency.C3.representation (n + 1)) initial
    (Tomabechi.Consistency.C3.stageTime n) t _
  · simpa [liftedHStageInput] using ht
  · exact hinitial

theorem liftedStageOrbit_eq_liftedScalarOrbit
    (c initial start t : ℝ) :
    liftedStageOrbit c (liftedStageCenter initial) start t =
      liftedStageCenter
        (Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit c initial start t) := by
  ext i
  fin_cases i <;>
    simp [liftedStageOrbit, liftedStageCenter,
      Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit, smul_eq_mul] <;>
    field_simp <;> ring

/-- The stagewise valley witness selected by the existing Theorem 21/22 API. -/
noncomputable def liftedHStageValleyWitness (n : ℕ) :
    Tomabechi.Theorem22.StageValleyWitness
      ((liftedHStageInput n).toStageValleySpec) :=
  Tomabechi.Theorem22.chooseStageValley
    ((liftedHStageInput n).toStageValleySpec)

/-- The minimizer selected by Theorem 21/22 is exactly the lifted shared
stage center; this identifies the switching core's valley points with the
CommonConcept-addressed representation. -/
theorem liftedHStageValleyWitness_minimizer_eq_center (n : ℕ) :
    (liftedHStageValleyWitness n).minimizer =
      liftedStageCenter (Tomabechi.Consistency.C3.representation (n + 1)) := by
  let s := liftedHStageInput n
  let q := s.toStageValleySpec
  let w := liftedHStageValleyWitness n
  have hcenter : q.center ∈ Metric.closedBall q.center q.radius := by
    change dist q.center q.center ≤ q.radius
    simpa using q.radius_pos.le
  have hpotential : Tomabechi.Theorem22.stageEffectivePotential q q.center = 0 := by
    simp [q, s, liftedHStageInput, Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
      Tomabechi.Theorem22.stageEffectivePotential, liftedStageMeanField]
  have hmin := w.minimizer_is_min hcenter
  change Tomabechi.Theorem22.stageEffectivePotential q w.minimizer ≤
    Tomabechi.Theorem22.stageEffectivePotential q q.center at hmin
  have hmin_nonneg : 0 ≤ Tomabechi.Theorem22.stageEffectivePotential q w.minimizer := by
    simp [q, s, liftedHStageInput, Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
      Tomabechi.Theorem22.stageEffectivePotential, liftedStageMeanField]
  have hmin_zero : Tomabechi.Theorem22.stageEffectivePotential q w.minimizer = 0 := by
    rw [hpotential] at hmin
    linarith
  have heq : Tomabechi.Theorem22.stageEffectivePotential q q.center =
      Tomabechi.Theorem22.stageEffectivePotential q w.minimizer := by
    rw [hpotential, hmin_zero]
  have huniq := w.minimizer_unique q.center hcenter heq
  exact huniq.symm

theorem liftedStageOrbit_eq_selectedOrbit (n : ℕ) (t : ℝ)
    (ht : ((liftedHStageInput n).toStageValleySpec).startTime ≤ t) :
    liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
        ((liftedHStageInput n).toStageValleySpec).initial
        ((liftedHStageInput n).toStageValleySpec).startTime t =
      (liftedHStageValleyWitness n).orbit t := by
  let s := liftedHStageInput n
  let q := s.toStageValleySpec
  let w := liftedHStageValleyWitness n
  have hinit : liftedStageOrbit
      (Tomabechi.Consistency.C3.representation (n + 1)) q.initial q.startTime q.startTime =
      q.initial := by
    simp [liftedStageOrbit]
  have hsub : ∀ u ∈ Set.Ici q.startTime,
      liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
        q.initial q.startTime u ∈ q.sublevel := by
    intro u hu
    have hu' : (liftedHStageInput n).startTime ≤ u := by
      change (liftedHStageInput n).startTime ≤ u at hu
      exact hu
    simpa [q, s, liftedHStageInput,
      Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec] using
      liftedHStageInput_orbit_forwardInvariant n s.initial s.initial_mem u hu'
  have hode : ∀ u ∈ Set.Ioi (q.startTime - w.local_extension),
      HasDerivAt
        (liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
          q.initial q.startTime)
        (-(q.mobility
          (liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
            q.initial q.startTime u)
          (Tomabechi.Theorem22.stageEffectiveGradient q
            (liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
              q.initial q.startTime u)))) u := by
    intro u hu
    simpa [q, s, liftedHStageInput, Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
      Tomabechi.Theorem22.stageEffectiveGradient] using
      liftedHStageInput_orbit_derivative n s.initial u
  have heq := w.orbit_unique
    (liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1)) q.initial q.startTime)
    (by simpa [q, s, w, liftedHStageValleyWitness, liftedHStageInput,
      Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec] using hinit)
    (by simpa [q, s, liftedHStageInput, Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec] using hsub)
    (by simpa [q, s, liftedHStageInput,
      Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
      Tomabechi.Theorem22.stageEffectiveGradient,
      ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul] using hode)
  exact heq t (by simpa [q, s, liftedHStageInput, Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec] using ht)

/-- On each original stage's forward time range, the selected lifted witness
orbit is exactly the isometric lift of the original scalar H-stage witness. -/
theorem liftedHStageValleyWitness_orbit_eq_liftedOriginal (n : ℕ) (t : ℝ)
    (ht : Tomabechi.Consistency.C3.stageTime n ≤ t) :
    (liftedHStageValleyWitness n).orbit t =
      liftedStageCenter ((Tomabechi.Consistency.C3.hStageSequenceValleys n).orbit t) := by
  let c := Tomabechi.Consistency.C3.representation (n + 1)
  let x₀ := (Tomabechi.Consistency.C3.hStageSequence n).initial
  have htLifted : ((liftedHStageInput n).toStageValleySpec).startTime ≤ t := by
    simpa [liftedHStageInput, Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec] using ht
  have hlifted := liftedStageOrbit_eq_selectedOrbit n t htLifted
  have hformula :
      liftedStageOrbit c (liftedStageCenter x₀)
          (Tomabechi.Consistency.C3.stageTime n) t =
        liftedStageCenter
          (Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit c x₀
            (Tomabechi.Consistency.C3.stageTime n) t) := by
    exact liftedStageOrbit_eq_liftedScalarOrbit c x₀
      (Tomabechi.Consistency.C3.stageTime n) t
  have hvalleyShape := Tomabechi.Consistency.C3.valleySequence_shape n
  have hshape :
      (Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec =
        Tomabechi.Examples.Theorem23B.quadraticStage c
          (Tomabechi.Consistency.C3.valleySequence n).initial
          (Tomabechi.Consistency.C3.valleySequence n).startTime := by
    rw [Tomabechi.Consistency.C3.hStageSequence_toStageValleySpec n, hvalleyShape]
    simp [c, Tomabechi.Examples.Theorem23B.quadraticStage]
  have hstart : (Tomabechi.Consistency.C3.valleySequence n).startTime =
      Tomabechi.Consistency.C3.stageTime n := by
    change (Tomabechi.Consistency.C3.valleySequence n).startTime = _
    exact Tomabechi.Consistency.C3.hStageSequence_start n
  have hchosen :
      (Tomabechi.Consistency.C3.hStageSequenceValleys n).orbit t =
        (Tomabechi.Theorem22.chooseStageValley
          (Tomabechi.Examples.Theorem23B.quadraticStage c
            (Tomabechi.Consistency.C3.valleySequence n).initial
            (Tomabechi.Consistency.C3.valleySequence n).startTime)).orbit t := by
    change (Tomabechi.Theorem22.chooseStageValley
      ((Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec)).orbit t = _
    rw [hshape]
  have htOriginal : (Tomabechi.Consistency.C3.valleySequence n).startTime ≤ t := by
    rw [hstart]
    exact ht
  have hquadratic :=
    Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit_eq_witness_orbit
      c (Tomabechi.Consistency.C3.valleySequence n).initial
      (Tomabechi.Consistency.C3.valleySequence n).startTime t htOriginal
  have hquadratic' :
      Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit c x₀
          (Tomabechi.Consistency.C3.stageTime n) t =
        (Tomabechi.Consistency.C3.hStageSequenceValleys n).orbit t := by
    rw [show x₀ = (Tomabechi.Consistency.C3.valleySequence n).initial by
      rfl, ← hstart, hquadratic, hchosen]
  have hlifted' :
      liftedStageOrbit c (liftedStageCenter x₀)
          (Tomabechi.Consistency.C3.stageTime n) t =
        (liftedHStageValleyWitness n).orbit t := by
    simpa [c, x₀, liftedHStageInput,
      Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec] using hlifted
  rw [← hlifted', hformula, hquadratic']

/-- Lift the canonical scalar 23-B trajectory into the same two-coordinate
state space as the CommonConcept H-stage inputs. -/
noncomputable def liftedHStageStitchedTrajectory : ℝ → LiftedStageState :=
  fun t => liftedStageCenter
    (Tomabechi.Consistency.C3.hStageSequenceStitchedTrajectory t)

/-- On every switching dwell interval, the lifted canonical trajectory is the
selected lifted Theorem 21/22 valley orbit for that stage. -/
theorem liftedHStageStitchedTrajectory_eq_stageOrbit (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc
      (Tomabechi.Consistency.C3.stageTime n)
      (Tomabechi.Consistency.C3.stageTime n +
        Tomabechi.Consistency.C3.stageDuration n)) :
    liftedHStageStitchedTrajectory t = (liftedHStageValleyWitness n).orbit t := by
  have hswitch :=
    (Tomabechi.Consistency.C3.hStageSequence_switching_certificate
      ).stitched_dwell_and_endpoint_error n
  have htstage : Tomabechi.Consistency.C3.stageTime n ≤ t := ht.1
  calc
    liftedHStageStitchedTrajectory t =
        liftedStageCenter
          ((Tomabechi.Consistency.C3.hStageSequenceValleys n).orbit t) := by
      unfold liftedHStageStitchedTrajectory
      exact congrArg liftedStageCenter (hswitch.1 ht)
    _ = (liftedHStageValleyWitness n).orbit t :=
      (liftedHStageValleyWitness_orbit_eq_liftedOriginal n t htstage).symm

theorem liftedStageCenter_dist (x y : ℝ) :
    dist (liftedStageCenter x) (liftedStageCenter y) = dist x y := by
  simp [dist_eq_norm, Real.norm_eq_abs, liftedStageCenter_difference_norm]

theorem liftedStageCenter_isometry : Isometry liftedStageCenter := by
  intro x y
  rw [edist_dist, edist_dist, liftedStageCenter_dist]

theorem liftedStageCenter_isClosedEmbedding :
    Topology.IsClosedEmbedding liftedStageCenter :=
  liftedStageCenter_isometry.isClosedEmbedding

/-- The closure of the lifted frozen-orbit range is exactly the lift of the
original scalar reachable closure. This uses the closed isometric embedding,
so no points transverse to the lifted diagonal are introduced by closure. -/
theorem liftedHStageReachable_eq_liftedScalarImage (n : ℕ) :
    closure ((liftedHStageValleyWitness n).orbit ''
        Set.Ici (liftedHStageInput n).startTime) =
      liftedStageCenter '' closure
        ((Tomabechi.Consistency.C3.hStageSequenceValleys n).orbit ''
          Set.Ici (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).startTime) := by
  have htime : (liftedHStageInput n).startTime =
      (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).startTime := by
    change Tomabechi.Consistency.C3.stageTime n =
      (Tomabechi.Consistency.C3.hStageSequence n).startTime
    exact (Tomabechi.Consistency.C3.hStageSequence_start n).symm
  have himage :
      (liftedHStageValleyWitness n).orbit ''
          Set.Ici (liftedHStageInput n).startTime =
        liftedStageCenter ''
          ((Tomabechi.Consistency.C3.hStageSequenceValleys n).orbit ''
            Set.Ici (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).startTime) := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(Tomabechi.Consistency.C3.hStageSequenceValleys n).orbit t,
        ⟨t, ?_, rfl⟩, ?_⟩
      · rw [← htime]
        exact ht
      · exact liftedHStageValleyWitness_orbit_eq_liftedOriginal n t
          (by simpa [liftedHStageInput] using ht) |>.symm
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ?_, ?_⟩
      · rw [htime]
        exact ht
      · have htLift : Tomabechi.Consistency.C3.stageTime n ≤ t := by
          calc
            Tomabechi.Consistency.C3.stageTime n = (liftedHStageInput n).startTime := rfl
            _ = (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).startTime := htime
            _ ≤ t := ht
        exact liftedHStageValleyWitness_orbit_eq_liftedOriginal n t htLift
  rw [himage]
  exact liftedStageCenter_isClosedEmbedding.closure_image_eq _

theorem liftedHStageInput_meanField_on_diagonal (n : ℕ) (x : ℝ) :
    (liftedHStageInput n).meanField (liftedStageCenter x) =
      (Tomabechi.Consistency.C3.hStageSequence n).meanField x := by
  change liftedStageMeanField
      (Tomabechi.Consistency.C3.representation ((n + 1 : ℕ) : LiftedStageAtom))
      (liftedStageCenter x) = _
  rw [liftedStageMeanField, liftedStageCenter_difference_norm_sq]
  have hc : Tomabechi.Consistency.C3.representation
      ((n + 1 : ℕ) : LiftedStageAtom) =
      (Tomabechi.Consistency.C3.hStageSequence n).center := by
    rw [Tomabechi.Consistency.R1.hStageSequence_center_eq_commonDiagonal_coordinate]
    exact Tomabechi.Consistency.R1.representation_eq_commonDiagonal_coordinate (n + 1)
  rw [hc]
  rw [Tomabechi.Consistency.R1.hStageSequence_meanField_matches_liftedPotential,
    liftedHStagePotential_on_diagonal]
  simp [smul_eq_mul]

/-- The lifted and scalar stage effective potentials agree on the embedded
diagonal, including their normalization. -/
theorem liftedHStageInput_effectivePotential_on_diagonal (n : ℕ) (x : ℝ) :
    Tomabechi.Theorem22.stageEffectivePotential
        ((liftedHStageInput n).toStageValleySpec) (liftedStageCenter x) =
      Tomabechi.Theorem22.stageEffectivePotential
        (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n) x := by
  rw [Tomabechi.Theorem22.stageEffectivePotential,
    Tomabechi.Theorem22.stageEffectivePotential]
  change 0 - 1 * 1 * (liftedHStageInput n).meanField (liftedStageCenter x) =
    0 - 1 * 1 * (Tomabechi.Consistency.C3.hStageSequence n).meanField x
  rw [liftedHStageInput_meanField_on_diagonal]

/-- The lifted H-stage radius is the same as the original scalar stage radius;
the construction adds one to the isometric initial displacement in both. -/
theorem liftedHStageInput_radius_eq_scalar (n : ℕ) :
    ((liftedHStageInput n).toStageValleySpec).radius =
      (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).radius := by
  simp [liftedHStageInput,
    Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
    Tomabechi.Consistency.C3.hStageSequenceStageSpecs,
    Tomabechi.Theorem22.meanFieldStageSequence,
    Tomabechi.Consistency.C3.hStageSequence,
    Tomabechi.Consistency.C3.packageQuadraticStage,
    Tomabechi.Examples.Theorem23B.quadraticStage,
    liftedStageCenter_difference_norm]

theorem liftedHStageInput_center_eq_lifted_scalar (n : ℕ) :
    ((liftedHStageInput n).toStageValleySpec).center =
      liftedStageCenter
        (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).center := by
  simp [liftedHStageInput, Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
    Tomabechi.Consistency.C3.hStageSequenceStageSpecs,
    Tomabechi.Theorem22.meanFieldStageSequence,
    Tomabechi.Consistency.C3.hStageSequence_center, Nat.cast_add]

theorem liftedStageCenter_closedBall_mem_iff (c r x : ℝ) :
    liftedStageCenter x ∈ Metric.closedBall (liftedStageCenter c) r ↔
      x ∈ Metric.closedBall c r := by
  rw [Metric.mem_closedBall, Metric.mem_closedBall, liftedStageCenter_dist]

theorem liftedHStageValleyWitness_minimizer_eq_lifted_scalar (n : ℕ) :
    (liftedHStageValleyWitness n).minimizer =
      liftedStageCenter
        (Tomabechi.Consistency.C3.hStageSequenceValleys n).minimizer := by
  have hOld :
      (Tomabechi.Consistency.C3.hStageSequenceValleys n).minimizer =
        Tomabechi.Consistency.C3.representation (n + 1) := by
    change (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys
      Tomabechi.Consistency.C3.hStageSequence n).minimizer = _
    exact Tomabechi.Consistency.C3.hStageSequence_minimizer n
  rw [liftedHStageValleyWitness_minimizer_eq_center, hOld]

/-- The 23-B TCZ built from the lifted H-stage inputs, using the same stage
thresholds and the closures of the selected lifted orbit ranges. -/
noncomputable def liftedHStageTCZ (n : ℕ) : Set LiftedStageState :=
  Tomabechi.Theorem23.stageTCZ
    (fun k x => Tomabechi.Theorem22.stageEffectivePotential
      ((liftedHStageInput k).toStageValleySpec) x)
    (fun k => (liftedHStageValleyWitness k).minimizer)
    Tomabechi.Consistency.C3.stageTheta
    (fun k => Metric.closedBall
      ((liftedHStageInput k).toStageValleySpec).center
      ((liftedHStageInput k).toStageValleySpec).radius)
    (fun k => closure ((liftedHStageValleyWitness k).orbit ''
      Set.Ici (liftedHStageInput k).startTime)) n

/-- The complete 23-B stage TCZ is preserved by the lifted diagonal
isometry, not just its reachable-closure component. -/
theorem liftedHStageTCZ_eq_lifted_scalar_image (n : ℕ) :
    liftedHStageTCZ n =
      liftedStageCenter '' Tomabechi.Consistency.C3.hStageSequenceTCZ n := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hregion, ⟨hreachable, hpotential⟩⟩
    change z ∈ closure ((liftedHStageValleyWitness n).orbit ''
      Set.Ici (liftedHStageInput n).startTime) at hreachable
    rw [liftedHStageReachable_eq_liftedScalarImage n] at hreachable
    rcases hreachable with ⟨x, hxreachable, hzx⟩
    subst z
    refine ⟨x, ?_, rfl⟩
    have hOldRegion : x ∈ Metric.closedBall
        (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).center
        (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).radius := by
      have hcenter := liftedHStageInput_center_eq_lifted_scalar n
      have hradius := liftedHStageInput_radius_eq_scalar n
      have hreg : liftedStageCenter x ∈ Metric.closedBall
          (liftedStageCenter
            (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).center)
          (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).radius := by
        simpa [hcenter, hradius] using hregion
      exact (liftedStageCenter_closedBall_mem_iff _ _ _).mp hreg
    have hpotential' := hpotential
    change Tomabechi.Theorem22.stageEffectivePotential
          ((liftedHStageInput n).toStageValleySpec) (liftedStageCenter x) -
        Tomabechi.Theorem22.stageEffectivePotential
          ((liftedHStageInput n).toStageValleySpec)
            (liftedHStageValleyWitness n).minimizer ≤
          Tomabechi.Consistency.C3.stageTheta n at hpotential'
    have hOldPotential :
        Tomabechi.Theorem22.stageEffectivePotential
            (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n) x -
          Tomabechi.Theorem22.stageEffectivePotential
            (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n)
              ((Tomabechi.Consistency.C3.hStageSequenceValleys n).minimizer) ≤
          Tomabechi.Consistency.C3.stageTheta n := by
      rw [liftedHStageValleyWitness_minimizer_eq_lifted_scalar] at hpotential'
      rw [liftedHStageInput_effectivePotential_on_diagonal,
        liftedHStageInput_effectivePotential_on_diagonal] at hpotential'
      exact hpotential'
    exact ⟨hOldRegion, ⟨hxreachable, hOldPotential⟩⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hregion, ⟨hreachable, hpotential⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · have hcenter := liftedHStageInput_center_eq_lifted_scalar n
      have hradius := liftedHStageInput_radius_eq_scalar n
      have hreg : x ∈ Metric.closedBall
          (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).center
          (Tomabechi.Consistency.C3.hStageSequenceStageSpecs n).radius := hregion
      have hreg' := (liftedStageCenter_closedBall_mem_iff _ _ _).mpr hreg
      simpa [hcenter, hradius] using hreg'
    · change liftedStageCenter x ∈ closure
        ((liftedHStageValleyWitness n).orbit ''
          Set.Ici (liftedHStageInput n).startTime)
      rw [liftedHStageReachable_eq_liftedScalarImage n]
      exact Set.mem_image_of_mem _ hreachable
    · change Tomabechi.Theorem22.stageEffectivePotential
          ((liftedHStageInput n).toStageValleySpec) (liftedStageCenter x) -
        Tomabechi.Theorem22.stageEffectivePotential
          ((liftedHStageInput n).toStageValleySpec)
            (liftedHStageValleyWitness n).minimizer ≤
          Tomabechi.Consistency.C3.stageTheta n
      rw [liftedHStageValleyWitness_minimizer_eq_lifted_scalar,
        liftedHStageInput_effectivePotential_on_diagonal,
        liftedHStageInput_effectivePotential_on_diagonal]
      exact hpotential

/-- Closedness of the scalar stage TCZ transfers to its lifted image because
the diagonal stage-center map is a closed embedding. -/
theorem liftedHStageTCZ_closed (n : ℕ) : IsClosed (liftedHStageTCZ n) := by
  rw [liftedHStageTCZ_eq_lifted_scalar_image]
  exact (liftedStageCenter_isClosedEmbedding).isClosed_iff_image_isClosed.mp
    (Tomabechi.Consistency.C3.hStageSequence_switching_certificate.tcz_closed n)

/-- Nonemptiness of every original stage TCZ transfers to the lifted TCZ. -/
theorem liftedHStageTCZ_nonempty (n : ℕ) : (liftedHStageTCZ n).Nonempty := by
  rw [liftedHStageTCZ_eq_lifted_scalar_image]
  exact (Tomabechi.Consistency.C3.hStageSequence_switching_certificate.tcz_nonempty n).image
    liftedStageCenter

/-- Adjacent lifted stage TCZs remain distinct, since the lift is injective. -/
theorem liftedHStageTCZ_adjacent_distinct (n : ℕ) :
    liftedHStageTCZ (n + 1) ≠ liftedHStageTCZ n := by
  intro hEq
  have hImage : liftedStageCenter ''
      Tomabechi.Consistency.C3.hStageSequenceTCZ (n + 1) =
      liftedStageCenter '' Tomabechi.Consistency.C3.hStageSequenceTCZ n := by
    rw [← liftedHStageTCZ_eq_lifted_scalar_image (n + 1),
      ← liftedHStageTCZ_eq_lifted_scalar_image n]
    exact hEq
  exact Tomabechi.Consistency.C3.hStageSequence_switching_certificate.adjacent_tcz_distinct n
    ((liftedStageCenter_isClosedEmbedding.injective.image_injective).eq_iff.mp hImage)

/-- The positive separation of adjacent scalar valley minimizers is preserved
exactly by the isometric stage-center lift. -/
theorem liftedHStageValleyWitness_adjacent_minimizers_separated (n : ℕ) :
    0 < dist (liftedHStageValleyWitness (n + 1)).minimizer
      (liftedHStageValleyWitness n).minimizer := by
  rw [liftedHStageValleyWitness_minimizer_eq_lifted_scalar,
    liftedHStageValleyWitness_minimizer_eq_lifted_scalar]
  rw [liftedStageCenter_dist, dist_eq_norm]
  exact (Tomabechi.Consistency.C3.hStageSequence_switching_certificate
    ).adjacent_valleys_distinct n

/-- The lifted path reaches a selected lifted valley orbit on a whole dwell
interval after every finite starting time. -/
theorem liftedHStageStitchedTrajectory_covers_every_finite_time (t : ℝ)
    (ht : Tomabechi.Consistency.C3.stageTime 0 ≤ t) :
    ∃ n, t ∈ Set.Ico
        (Tomabechi.Consistency.C3.stageTime n)
        (Tomabechi.Consistency.C3.stageTime n +
          Tomabechi.Consistency.C3.stageDuration n) ∧
      liftedHStageStitchedTrajectory t = (liftedHStageValleyWitness n).orbit t := by
  obtain ⟨n, hn⟩ :=
    (Tomabechi.Consistency.C3.hStageSequence_switching_certificate
      ).every_finite_time_in_a_dwell t ht
  refine ⟨n, hn, ?_⟩
  apply liftedHStageStitchedTrajectory_eq_stageOrbit n t
  exact ⟨hn.1, hn.2.le⟩

/-- At every finite forward time, the selected lifted switching path is the
isometric image of the original canonical scalar stitched path. -/
theorem liftedHStageStitchedTrajectory_eq_lifted_scalar (t : ℝ)
    (ht : Tomabechi.Consistency.C3.stageTime 0 ≤ t) :
    liftedHStageStitchedTrajectory t =
      liftedStageCenter (Tomabechi.Consistency.C3.hStageSequenceStitchedTrajectory t) := by
  obtain ⟨n, htime, hOrbit⟩ :=
    liftedHStageStitchedTrajectory_covers_every_finite_time t ht
  have hScalar :=
    (Tomabechi.Consistency.C3.hStageSequence_switching_certificate
      ).stitched_dwell_and_endpoint_error n
  have hScalarAt := hScalar.1 ⟨htime.1, htime.2.le⟩
  have hOrbitLift := liftedHStageValleyWitness_orbit_eq_liftedOriginal n t htime.1
  rw [hOrbit, hOrbitLift, hScalarAt]

/-- The original endpoint tolerance is preserved exactly by the isometric
lift, measured against the minimizer selected in the lifted stage. -/
theorem liftedHStageStitchedTrajectory_endpoint_error (n : ℕ) :
    dist
      (liftedHStageStitchedTrajectory
        (Tomabechi.Consistency.C3.stageTime n +
          Tomabechi.Consistency.C3.stageDuration n))
      (liftedHStageValleyWitness n).minimizer ≤
      Tomabechi.Consistency.C3.errorTolerance n := by
  have hcert :=
    (Tomabechi.Consistency.C3.hStageSequence_switching_certificate
      ).stitched_dwell_and_endpoint_error n
  have hpath := liftedHStageStitchedTrajectory_eq_stageOrbit n
    (Tomabechi.Consistency.C3.stageTime n +
      Tomabechi.Consistency.C3.stageDuration n) ⟨le_add_of_nonneg_right
        (Tomabechi.Consistency.C3.stageDuration_pos n).le, le_rfl⟩
  have hminOld :
      (Tomabechi.Consistency.C3.hStageSequenceValleys n).minimizer =
        Tomabechi.Consistency.C3.representation (n + 1) := by
    change (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys
      Tomabechi.Consistency.C3.hStageSequence n).minimizer = _
    exact Tomabechi.Consistency.C3.hStageSequence_minimizer n
  have hminNew := liftedHStageValleyWitness_minimizer_eq_center n
  calc
    dist (liftedHStageStitchedTrajectory
        (Tomabechi.Consistency.C3.stageTime n +
          Tomabechi.Consistency.C3.stageDuration n))
        (liftedHStageValleyWitness n).minimizer =
      dist (liftedStageCenter
          (Tomabechi.Consistency.C3.hStageSequenceStitchedTrajectory
            (Tomabechi.Consistency.C3.stageTime n +
              Tomabechi.Consistency.C3.stageDuration n)))
        (liftedStageCenter
          ((Tomabechi.Consistency.C3.hStageSequenceValleys n).minimizer)) := by
      rw [show liftedHStageStitchedTrajectory
          (Tomabechi.Consistency.C3.stageTime n +
            Tomabechi.Consistency.C3.stageDuration n) =
          liftedStageCenter
            (Tomabechi.Consistency.C3.hStageSequenceStitchedTrajectory
              (Tomabechi.Consistency.C3.stageTime n +
                Tomabechi.Consistency.C3.stageDuration n)) by rfl,
        hcert.1 ⟨le_add_of_nonneg_right
          (Tomabechi.Consistency.C3.stageDuration_pos n).le, le_rfl⟩,
        hminOld, hminNew]
    _ = dist
        (Tomabechi.Consistency.C3.hStageSequenceStitchedTrajectory
          (Tomabechi.Consistency.C3.stageTime n +
            Tomabechi.Consistency.C3.stageDuration n))
        ((Tomabechi.Consistency.C3.hStageSequenceValleys n).minimizer) :=
      liftedStageCenter_dist _ _
    _ ≤ Tomabechi.Consistency.C3.errorTolerance n := hcert.2

theorem liftedStageSelectedOrbit_distance (n : ℕ) (t : ℝ)
    (ht : (liftedHStageInput n).startTime ≤ t) :
    dist ((liftedHStageValleyWitness n).orbit t)
        (liftedStageCenter (Tomabechi.Consistency.C3.representation (n + 1))) =
      Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) *
        dist (liftedHStageInput n).initial
          (liftedStageCenter (Tomabechi.Consistency.C3.representation (n + 1))) := by
  rw [← liftedStageOrbit_eq_selectedOrbit n t ht]
  exact liftedStageOrbit_distance _ _ _ _

theorem liftedHStageInput_selected_transition (n : ℕ) :
    (liftedHStageInput (n + 1)).initial =
      (liftedHStageValleyWitness n).orbit
        (Tomabechi.Consistency.C3.stageTime n +
          Tomabechi.Consistency.C3.stageDuration n) := by
  have ht : (liftedHStageInput n).startTime ≤
      Tomabechi.Consistency.C3.stageTime n +
        Tomabechi.Consistency.C3.stageDuration n := by
    change Tomabechi.Consistency.C3.stageTime n ≤ _
    exact le_add_of_nonneg_right (Tomabechi.Consistency.C3.stageDuration_pos n).le
  rw [← liftedStageOrbit_eq_selectedOrbit n
    (Tomabechi.Consistency.C3.stageTime n +
      Tomabechi.Consistency.C3.stageDuration n) ht]
  change liftedStageCenter
      (Tomabechi.Consistency.C3.hStageSequence (n + 1)).initial =
    liftedStageOrbit (Tomabechi.Consistency.C3.representation (n + 1))
      (liftedStageCenter (Tomabechi.Consistency.C3.hStageSequence n).initial)
      (Tomabechi.Consistency.C3.stageTime n)
      (Tomabechi.Consistency.C3.stageTime n +
        Tomabechi.Consistency.C3.stageDuration n)
  rw [liftedStageOrbit_eq_liftedScalarOrbit]
  congr 1
  rw [Tomabechi.Consistency.C3.hStageSequence_initial_recurrence]
  rw [Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit]
  have htime : Tomabechi.Consistency.C3.stageTime n +
      Tomabechi.Consistency.C3.stageDuration n -
        Tomabechi.Consistency.C3.stageTime n =
      Tomabechi.Consistency.C3.stageDuration n := by ring
  rw [htime]
  norm_num [Nat.cast_add]

/-- Address-indexed H-stage data. The former top address has no finite
H-stage in the original sequence, so this total extension assigns stage zero
there; the CommonConcept family below then uses the lattice projection. -/
noncomputable def liftedHStageDataOnOldAddress : WithTop ℕ →
    Tomabechi.Theorem22.MeanFieldStageInput LiftedStageState
  | ⊤ => liftedHStageInput 0
  | (n : ℕ) => liftedHStageInput n

/-- A complete H-stage input is assigned to every point of the shared
complete lattice by pulling back the address-indexed stage data. -/
noncomputable def commonConceptHStageInput (x : Tomabechi.Consistency.R1.CommonConcept) :
    Tomabechi.Theorem22.MeanFieldStageInput LiftedStageState :=
  Tomabechi.Consistency.R1.extendLayerData liftedHStageDataOnOldAddress x

theorem commonConceptHStageInput_eq_projected (x : Tomabechi.Consistency.R1.CommonConcept) :
    commonConceptHStageInput x =
      liftedHStageDataOnOldAddress (Tomabechi.Consistency.R1.layerProjection x) := rfl

theorem commonConceptHStageInput_at_properPoint
    (x : Tomabechi.Consistency.R1.CommonConcept) (hx : x < ⊤) :
    commonConceptHStageInput x =
      liftedHStageInput ((Tomabechi.Consistency.R1.layerProjection x).untopD 0) := by
  have hp := Tomabechi.Consistency.R1.layerProjection_lt_top_of_lt_top hx
  cases hproj : Tomabechi.Consistency.R1.layerProjection x with
  | top =>
    have htop : (⊤ : WithTop ℕ) < ⊤ := by simpa [hproj] using hp
    exact (lt_irrefl (⊤ : WithTop ℕ) htop).elim
  | coe n => simp [commonConceptHStageInput_eq_projected, hproj,
      liftedHStageDataOnOldAddress, WithTop.untopD, WithTop.recTopCoe]

theorem commonConceptHStageInput_center
    (x : Tomabechi.Consistency.R1.CommonConcept) :
    (commonConceptHStageInput x).center =
      liftedStageCenter (Tomabechi.Consistency.C3.representation
        ((((Tomabechi.Consistency.R1.layerProjection x).untopD 0 + 1 : ℕ) : LiftedStageAtom))) := by
  rw [commonConceptHStageInput_eq_projected]
  cases hproj : Tomabechi.Consistency.R1.layerProjection x with
  | top =>
    change liftedStageCenter (Tomabechi.Consistency.C3.representation
      (1 : LiftedStageAtom)) = _
    rfl
  | coe n =>
    change liftedStageCenter (Tomabechi.Consistency.C3.representation
      ((n + 1 : ℕ) : LiftedStageAtom)) = _
    congr 1

theorem commonConceptHStageInput_at_oldAddress (a : WithTop ℕ) :
    commonConceptHStageInput (Tomabechi.Consistency.R1.layerAddressEmbedding a) =
      liftedHStageDataOnOldAddress a := by
  exact Tomabechi.Consistency.R1.extendLayerData_on_oldAddress
    liftedHStageDataOnOldAddress a

theorem commonConceptHStageInput_at_finiteAddress (n : ℕ) :
    commonConceptHStageInput (Tomabechi.Consistency.R1.layerAddressEmbedding n) =
      liftedHStageInput n := by
  rw [commonConceptHStageInput_at_oldAddress]
  rfl

theorem commonConceptHStageInput_at_top :
    commonConceptHStageInput (⊤ : Tomabechi.Consistency.R1.CommonConcept) =
      liftedHStageInput 0 := by
  have hp : Tomabechi.Consistency.R1.layerProjection
      (⊤ : Tomabechi.Consistency.R1.CommonConcept) = ⊤ := by
    simpa [Tomabechi.Consistency.R1.layerAddressEmbedding,
      Tomabechi.Consistency.R1.layerAddress_top] using
      (Tomabechi.Consistency.R1.layerProjection_layerAddress (⊤ : WithTop ℕ))
  rw [commonConceptHStageInput_eq_projected, hp]
  rfl

/-- The lifted switching region assigned at a CommonConcept point is the
stage TCZ at the index selected by the same lattice projection as its H-stage
input. -/
noncomputable def commonConceptHStageTCZ
    (x : Tomabechi.Consistency.R1.CommonConcept) : Set LiftedStageState :=
  liftedHStageTCZ ((Tomabechi.Consistency.R1.layerProjection x).untopD 0)

theorem commonConceptHStageTCZ_eq_projected
    (x : Tomabechi.Consistency.R1.CommonConcept) :
    commonConceptHStageTCZ x =
      liftedHStageTCZ ((Tomabechi.Consistency.R1.layerProjection x).untopD 0) := rfl

/-- On every embedded old address, the H-stage TCZ uses the same old-layer
index as the corresponding CommonConcept H-stage input. -/
theorem commonConceptHStageTCZ_at_oldAddress (a : WithTop ℕ) :
    commonConceptHStageTCZ (Tomabechi.Consistency.R1.layerAddressEmbedding a) =
      liftedHStageTCZ (a.untopD 0) := by
  simp [commonConceptHStageTCZ, Tomabechi.Consistency.R1.layerAddressEmbedding]

/-- The lattice top is assigned the initial lifted H-stage TCZ. -/
theorem commonConceptHStageTCZ_at_top :
    commonConceptHStageTCZ (⊤ : Tomabechi.Consistency.R1.CommonConcept) =
      liftedHStageTCZ 0 := by
  rw [commonConceptHStageTCZ_eq_projected]
  have hp : Tomabechi.Consistency.R1.layerProjection
      (⊤ : Tomabechi.Consistency.R1.CommonConcept) = ⊤ := by
    simpa [Tomabechi.Consistency.R1.layerAddressEmbedding,
      Tomabechi.Consistency.R1.layerAddress_top] using
      (Tomabechi.Consistency.R1.layerProjection_layerAddress (⊤ : WithTop ℕ))
  rw [hp]
  simp

/-- Every CommonConcept point receives a closed, nonempty lifted stage TCZ,
because its projected H-stage has those properties. -/
theorem commonConceptHStageTCZ_closed_nonempty
    (x : Tomabechi.Consistency.R1.CommonConcept) :
    IsClosed (commonConceptHStageTCZ x) ∧ (commonConceptHStageTCZ x).Nonempty := by
  exact ⟨liftedHStageTCZ_closed _, liftedHStageTCZ_nonempty _⟩

theorem liftedHStageInput_diagonal_sublevel (n : ℕ) (x : ℝ) :
    liftedStageCenter x ∈ (liftedHStageInput n).sublevel ↔
      x ∈ (Tomabechi.Consistency.C3.hStageSequence n).sublevel := by
  change liftedStageCenter x ∈ Metric.closedBall
      (liftedStageCenter (Tomabechi.Consistency.C3.representation (n + 1)))
      ‖liftedStageCenter (Tomabechi.Consistency.C3.hStageSequence n).initial -
        liftedStageCenter (Tomabechi.Consistency.C3.representation (n + 1))‖ ↔
    x ∈ Metric.closedBall (Tomabechi.Consistency.C3.representation (n + 1))
      |(Tomabechi.Consistency.C3.hStageSequence n).initial -
        Tomabechi.Consistency.C3.representation (n + 1)|
  exact liftedStage_closedBall_mem_iff _ _ _

end Tomabechi.Consistency.R1

end
