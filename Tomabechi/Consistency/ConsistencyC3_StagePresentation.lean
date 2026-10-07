import Theorem22
import Tomabechi.Examples.Theorem23B_QuadraticStages
import Tomabechi.Information.MeanFieldDirectCMI
import Tomabechi.Counterexamples.DecoderRegularity
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Support

/-!
# C3：共通層表象を持つ平均場提示

各段の原子法則はその段の中心にあるDirac確率測度とする。原子型・順序・
proper source layer・単調表象は全段で共通にし、段ごとの再構成核を積分すると
二次谷の臨場感場になる。これは元のH-stageを組み立てる最初の部品である。
-/

open MeasureTheory
open ProbabilityTheory

namespace Tomabechi.Consistency.C3

abbrev Atom := WithTop ℕ

/-- 共通表象：自然数段は1未満で単調に増え、最上位元だけを1へ送る。 -/
noncomputable def representation : Atom → ℝ
  | ⊤ => 1
  | (n : ℕ) => (n : ℝ) / ((n : ℝ) + 1)

theorem representation_lt_top (n : ℕ) : representation n < 1 := by
  simp only [representation]
  have hn : 0 < (n : ℝ) + 1 := by positivity
  apply (div_lt_one hn).2
  exact_mod_cast Nat.lt_succ_self n

theorem representation_injective : Function.Injective representation := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some n =>
          have := representation_lt_top n
          simp only [representation] at hab
          exact False.elim ((ne_of_lt this) hab.symm)
  | some n =>
      cases b with
      | none =>
          have := representation_lt_top n
          simp only [representation] at hab
          exact False.elim ((ne_of_lt this) hab)
      | some m =>
          simp only [representation] at hab
          have hn : (n : ℝ) + 1 ≠ 0 := by positivity
          have hm : (m : ℝ) + 1 ≠ 0 := by positivity
          have hcast : (n : ℝ) = (m : ℝ) := by
            field_simp [hn, hm] at hab
            nlinarith [hab]
          have hnm : n = m := Nat.cast_injective hcast
          subst m
          rfl

theorem representation_monotone : Monotone representation := by
  intro a b hab
  cases b with
  | none =>
      cases a with
      | none => rfl
      | some n => exact (representation_lt_top n).le
  | some m =>
      cases a with
      | none => exact False.elim ((WithTop.not_top_le_coe m) hab)
      | some n =>
          have hn : (n : ℝ) + 1 > 0 := by positivity
          have hm : (m : ℝ) + 1 > 0 := by positivity
          simp only [representation]
          rw [div_le_div_iff₀ hn hm]
          have hnm : n ≤ m := WithTop.coe_le_coe.mp hab
          have hreal : (n : ℝ) ≤ m := by exact_mod_cast hnm
          nlinarith [hreal]

/-- 段nにおける平均場提示。平均場核は原子に関して定数だが、
supportLubと中心表象は共通束上の実際のn番目の値を取る。 -/
noncomputable def averagePresentation (n : ℕ) :
    Tomabechi.Theorem22.MeanFieldAveragePresentation ℝ := by
  classical
  letI : TopologicalSpace Atom := ⊥
  letI : DiscreteTopology Atom := ⟨rfl⟩
  letI : MeasurableSpace Atom := ⊤
  let p : Atom := (n + 1 : ℕ)
  let μ : Measure Atom := Measure.dirac p
  refine
    { Atom := Atom
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
        change a = p ↔ (∀ U : Set Atom, a ∈ U → IsOpen U → 0 < μ U)
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
            have hopen : IsOpen ({a} : Set Atom) := isOpen_discrete _
            have hpa : p ≠ a := fun h => ha h.symm
            have hz : μ ({a} : Set Atom) = 0 := by
              dsimp [μ]
              rw [Measure.dirac_apply]
              simp [hpa]
            have hp := h {a} (by simp) hopen
            rw [hz] at hp
            exact False.elim ((lt_irrefl 0) hp)
      measureSupport_measurable := by simp
      measureSupport_full := by
        dsimp [μ, p]
        simp
      measureSupport_subset_sourceLayer := by
        intro a ha
        simp only [Set.mem_singleton_iff] at ha
        have hne : p ≠ (⊤ : Atom) := by simp [p]
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
      centerRepresentation := representation
      reconstructionKernel := fun x _ => -(1 / 2 : ℝ) * (x - representation p) ^ 2
      reconstructionKernel_integrable := by
        intro x
        exact integrable_const _ }

theorem averagePresentation_center (n : ℕ) :
    (averagePresentation n).centerRepresentation
      (averagePresentation n).supportLub = representation (n + 1 : ℕ) := by
  rfl

theorem averagePresentation_integral (n : ℕ) (x : ℝ) :
    (averagePresentation n).integralValue x =
      -(1 / 2 : ℝ) * (x - representation (n + 1 : ℕ)) ^ 2 := by
  classical
  letI : MeasurableSpace Atom := ⊤
  unfold Tomabechi.Theorem22.MeanFieldAveragePresentation.integralValue averagePresentation
  dsimp [representation]
  rw [integral_dirac]

/-- Repackage a quadratic valley as the original exact-sublevel H-stage input.
The analytic fields are copied verbatim; the stage's mean field is the integral
of the kernel in `averagePresentation n`, and the center is the shared order
representation of that stage's LUB. -/
noncomputable def packageQuadraticStage (n : ℕ) (initial start : ℝ) :
    Tomabechi.Theorem22.MeanFieldStageInput ℝ := by
  let s := Tomabechi.Examples.Theorem23B.quadraticStage
    (representation (n + 1 : ℕ)) initial start
  refine
    { center := s.center
      radius := s.radius
      gain := s.gain
      presenceGain := s.presenceGain
      curvature := s.curvature
      backgroundCurvature := s.backgroundCurvature
      gradientBound := s.gradientBound
      gamma := s.gamma
      startTime := s.startTime
      background := s.background
      meanField := s.presence
      averagePresentation := averagePresentation n
      center_eq_supportLub_representation := ?_
      meanField_eq_integral := ?_
      backgroundGradient := s.backgroundGradient
      meanFieldGradient := s.presenceGradient
      backgroundHessian := s.backgroundHessian
      meanFieldHessian := s.presenceHessian
      mobility := s.mobility
      sublevel := s.sublevel
      initial := s.initial
      radius_pos := s.radius_pos
      gain_pos := s.gain_pos
      curvature_pos := s.curvature_pos
      backgroundCurvature_nonneg := s.backgroundCurvature_nonneg
      gradientBound_nonneg := s.gradientBound_nonneg
      gain_threshold := s.gain_threshold
      background_c2_at := s.background_c2_at
      meanField_c2_at := ?_
      background_gradient_representation := s.background_gradient_representation
      meanField_gradient_representation := ?_
      background_gradient_deriv := s.background_gradient_deriv
      meanField_gradient_deriv := ?_
      mobility_c1 := s.mobility_c1
      mobility_symmetric := s.mobility_symmetric
      background_hessian_lower := s.background_hessian_lower
      meanField_hessian_upper := s.presence_hessian_upper
      meanField_center_stationary := s.presence_center_stationary
      background_gradient_bound := s.background_gradient_bound
      initial_mem := s.initial_mem
      sublevel_barrier := s.sublevel_barrier
      sublevel_eq := s.sublevel_eq
      gamma_pos := s.gamma_pos
      mobility_coercive := s.mobility_coercive }
  · dsimp [s, Tomabechi.Examples.Theorem23B.quadraticStage]
    rfl
  · intro x
    rw [averagePresentation_integral]
    rfl
  · intro x hx
    exact s.presence_c2_at x hx
  · exact s.presence_gradient_representation
  · exact s.presence_gradient_deriv

/-- The packaged input converts back to exactly the quadratic stage used to
construct it, so its effective potential, sublevel and frozen dynamics are
unchanged by adding the average presentation. -/
theorem packageQuadraticStage_toStageValleySpec (n : ℕ) (initial start : ℝ) :
    (packageQuadraticStage n initial start).toStageValleySpec =
      Tomabechi.Examples.Theorem23B.quadraticStage
        (representation (n + 1 : ℕ)) initial start := by
  rfl

theorem packageQuadraticStage_uses_original_sublevel_barrier
    (n : ℕ) (initial start : ℝ) :
    closure (packageQuadraticStage n initial start).sublevel ⊆
      Metric.ball (representation (n + 1 : ℕ)) (packageQuadraticStage n initial start).radius :=
  (packageQuadraticStage n initial start).sublevel_barrier

/-- The common-symbol center gap between successive natural layers. -/
noncomputable def centerGap (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 2) * ((n : ℝ) + 3))

theorem representation_center_gap (n : ℕ) :
    representation (n + 2 : ℕ) - representation (n + 1 : ℕ) = centerGap n := by
  simp only [representation, centerGap]
  push_cast
  field_simp
  <;> ring

theorem centerGap_pos (n : ℕ) : 0 < centerGap n := by
  simp [centerGap]
  positivity

/-- A polynomially growing dwell is long enough for the logarithmic tolerance
associated with the shrinking layer gap. -/
noncomputable def stageDuration (n : ℕ) : ℝ :=
  4 * ((n : ℝ) + 2) * ((n : ℝ) + 3)

theorem stageDuration_pos (n : ℕ) : 0 < stageDuration n := by
  simp [stageDuration]
  positivity

noncomputable def gapThreshold (n : ℕ) : ℝ :=
  (centerGap n) ^ 2 / 4

noncomputable def errorTolerance (n : ℕ) : ℝ :=
  centerGap n / 4

theorem errorTolerance_pos (n : ℕ) : 0 < errorTolerance n := by
  exact (div_pos (centerGap_pos n) (by norm_num))

noncomputable def stageTime (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, stageDuration k

theorem stageTime_recurrence (n : ℕ) :
    stageTime (n + 1) = stageTime n + stageDuration n := by
  simp [stageTime, Finset.sum_range_succ]

theorem stageDuration_lower_bound (n : ℕ) : 1 ≤ stageDuration n := by
  rw [stageDuration]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith [sq_nonneg (n : ℝ)]

theorem stageTime_unbounded (B : ℝ) :
    ∃ n, B < ∑ k ∈ Finset.range n, stageDuration k := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  refine ⟨n, ?_⟩
  calc
    B < (n : ℝ) := hn
    _ ≤ ∑ k ∈ Finset.range n, stageDuration k := by
      calc
        (n : ℝ) = ∑ _k ∈ Finset.range n, (1 : ℝ) := by simp
        _ ≤ ∑ k ∈ Finset.range n, stageDuration k := by
          apply Finset.sum_le_sum
          intro k hk
          exact stageDuration_lower_bound k

def layerU (n : ℕ) : Atom := (n + 1 : ℕ)

def layerV (n : ℕ) : Atom := (n + 1 : ℕ)

theorem layerU_update (n : ℕ) :
    layerU (n + 1) = layerU n ⊔ layerV (n + 1) := by
  simp [layerU, layerV]

theorem layerU_below_top (n : ℕ) : layerU n < (⊤ : Atom) := by
  exact WithTop.coe_lt_top (n + 1)

theorem layerV_new (n : ℕ) : ¬ layerV (n + 1) ≤ layerU n := by
  intro h
  have hn : n + 2 ≤ n + 1 := WithTop.coe_le_coe.mp h
  omega

noncomputable def firstValley : Tomabechi.Theorem22.StageValleySpec ℝ :=
  Tomabechi.Examples.Theorem23B.quadraticStage (representation 1) 0 0

noncomputable def nextValley (n : ℕ) (initial start : ℝ) :
    Tomabechi.Theorem22.StageValleySpec ℝ :=
  Tomabechi.Examples.Theorem23B.quadraticStage
    (representation (n + 2 : ℕ)) initial start

noncomputable def valleySequence : ℕ → Tomabechi.Theorem22.StageValleySpec ℝ :=
  Tomabechi.Theorem23.endpointCompatibleStageSequence
    firstValley nextValley (by intro n x t; rfl) (by intro n x t; rfl)
    stageTime stageDuration

theorem valleySequence_shape (n : ℕ) :
    valleySequence n = Tomabechi.Examples.Theorem23B.quadraticStage
      (representation (n + 1 : ℕ)) (valleySequence n).initial (valleySequence n).startTime := by
  induction n with
  | zero =>
      simp [valleySequence, firstValley,
        Tomabechi.Examples.Theorem23B.quadraticStage,
        Tomabechi.Theorem23.endpointCompatibleStageSequence]
  | succ n ih =>
      simp [valleySequence, nextValley,
        Tomabechi.Examples.Theorem23B.quadraticStage,
        Tomabechi.Theorem23.endpointCompatibleStageSequence, Nat.add_assoc]

theorem valleySequence_center (n : ℕ) :
    (valleySequence n).center = representation (n + 1 : ℕ) := by
  induction n with
  | zero => simp [valleySequence, firstValley, Tomabechi.Examples.Theorem23B.quadraticStage,
      Tomabechi.Theorem23.endpointCompatibleStageSequence]
  | succ n ih =>
      simp [valleySequence, nextValley,
        Tomabechi.Examples.Theorem23B.quadraticStage,
        Tomabechi.Theorem23.endpointCompatibleStageSequence, Nat.add_assoc]

/-- One complete original H-stage per LUB layer.  The transition is inherited
from the endpoint-compatible valley sequence, while the mean field, average
presentation, and order representation are attached without changing the
quadratic valley data. -/
noncomputable def hStageSequence : ℕ →
    Tomabechi.Theorem22.MeanFieldStageInput ℝ := fun n =>
  packageQuadraticStage n (valleySequence n).initial (valleySequence n).startTime

theorem hStageSequence_toStageValleySpec (n : ℕ) :
    (hStageSequence n).toStageValleySpec = valleySequence n := by
  have hshape := valleySequence_shape n
  rw [hStageSequence, packageQuadraticStage_toStageValleySpec, hshape]
  simp [Tomabechi.Examples.Theorem23B.quadraticStage]

theorem hStageSequence_center (n : ℕ) :
    (hStageSequence n).center = representation (n + 1 : ℕ) := by
  change (Tomabechi.Examples.Theorem23B.quadraticStage
    (representation (n + 1 : ℕ)) (valleySequence n).initial (valleySequence n).startTime).center = _
  rfl

theorem hStageSequence_sublevel_barrier (n : ℕ) :
    closure (hStageSequence n).sublevel ⊆
      Metric.ball (hStageSequence n).center (hStageSequence n).radius := by
  exact (hStageSequence n).sublevel_barrier

theorem hStageSequence_start (n : ℕ) :
    (hStageSequence n).startTime = stageTime n := by
  change (valleySequence n).startTime = stageTime n
  exact Tomabechi.Theorem23.endpointCompatibleStageSequence_startTime
    firstValley nextValley (by intro k x t; rfl) (by intro k x t; rfl)
    stageTime stageDuration (by simp [firstValley,
      Tomabechi.Examples.Theorem23B.quadraticStage, stageTime]) n

theorem hStageSequence_minimizer (n : ℕ) :
    (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).minimizer =
      representation (n + 1 : ℕ) := by
  change (Tomabechi.Theorem22.chooseStageValley
    ((hStageSequence n).toStageValleySpec)).minimizer = representation (n + 1 : ℕ)
  rw [hStageSequence_toStageValleySpec, valleySequence_shape]
  exact Tomabechi.Examples.Theorem23B.chooseQuadraticStage_minimizer
    (representation (n + 1 : ℕ)) (valleySequence n).initial (valleySequence n).startTime

theorem hStageSequence_transition (n : ℕ) :
    (hStageSequence (n + 1)).initial =
      (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).orbit
        (stageTime n + stageDuration n) := by
  change (valleySequence (n + 1)).initial =
    (Tomabechi.Theorem22.chooseStageValley
      ((hStageSequence n).toStageValleySpec)).orbit
      (stageTime n + stageDuration n)
  rw [hStageSequence_toStageValleySpec]
  exact Tomabechi.Theorem23.endpointCompatibleStageSequence_transition
    firstValley nextValley (by intro k x t; rfl) (by intro k x t; rfl)
    stageTime stageDuration n

theorem averagePresentation_sourceLayer (n : ℕ) :
    (averagePresentation n).sourceLayer = {((n + 1 : ℕ) : Atom)} := rfl

theorem averagePresentation_measureSupport (n : ℕ) :
    (averagePresentation n).measureSupport = {((n + 1 : ℕ) : Atom)} := rfl

theorem averagePresentation_supportLub (n : ℕ) :
    (averagePresentation n).supportLub = ((n + 1 : ℕ) : Atom) := rfl

theorem averagePresentation_abstractTop (n : ℕ) :
    (averagePresentation n).abstractTop = (⊤ : Atom) := rfl

theorem hStageSequence_atomType (n : ℕ) :
    (hStageSequence n).averagePresentation.Atom = Atom := rfl

/-- The branch and symbolic support for each stage are the represented
single-layer sets in the shared abstract order. -/
noncomputable def branchContext (n : ℕ) :
    Tomabechi.Theorem21.Theorem21BranchContext Atom where
  branch := {((n + 1 : ℕ) : Atom)}
  symbolSupport := {((n + 1 : ℕ) : Atom)}
  support_nonempty := Set.singleton_nonempty _
  top_not_in_branch := by
    intro h
    cases h
  support_lub := by
    simpa using (isLUB_singleton : IsLUB ({((n + 1 : ℕ) : Atom)} : Set Atom) ((n + 1 : ℕ) : Atom))
  address_in_branch := by simp

noncomputable def inputMass : Unit → Bool → ℝ := fun _ g =>
  (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure {g}).toReal

def inputAction : Unit → Bool → Bool := fun _ g => g

theorem inputMass_value (x : Unit) (g : Bool) : inputMass x g = 1 / 2 := by
  simp [inputMass,
    Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure_singleton]

theorem inputMass_nonneg (x : Unit) (g : Bool) : 0 ≤ inputMass x g := by
  rw [inputMass_value]
  norm_num

theorem inputMass_sum (x : Unit) : ∑ g : Bool, inputMass x g = 1 := by
  simp [inputMass_value]

theorem inputMass_measurable (g : Bool) :
    AEStronglyMeasurable (fun x : Unit => inputMass x g) (Measure.dirac ()) := by
  fun_prop

theorem inputAction_measurable (g : Bool) :
    Measurable (fun x : Unit => inputAction x g) := by
  fun_prop

theorem inputAction_injective :
    ∀ x : Unit, ∀ g, 0 < inputMass x g →
      ∀ g', inputAction x g' = inputAction x g → g' = g := by
  intro x g _ g' h
  exact h

theorem inputEntropy_eq_log_two :
    Tomabechi.Theorem21.conditionalGoalEntropy (Measure.dirac ()) inputMass =
      Real.log 2 := by
  change (∫ _ : Unit,
    Tomabechi.Theorem21.conditionalGoalEntropyAt
      (fun g => (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure
        {g}).toReal) ∂Measure.dirac ()) = Real.log 2
  rw [integral_dirac,
    Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalEntropy_eq_log_two]

theorem inputEntropy_pos :
    0 < Tomabechi.Theorem21.conditionalGoalEntropy
      (Measure.dirac ()) inputMass := by
  rw [inputEntropy_eq_log_two]
  exact Real.log_pos (by norm_num)

/-- 物理底層に割り当てる決定的ゴール法則。ここではBoolの一方だけに
確率1を置くので、物理層の条件付きゴールエントロピーは厳密に0となる。 -/
noncomputable def physicalMass : Unit → Bool → ℝ := fun _ g =>
  if g then 0 else 1

theorem physicalEntropy_eq_zero :
    Tomabechi.Theorem21.conditionalGoalEntropy (Measure.dirac ()) physicalMass = 0 := by
  change (∫ _ : Unit,
    Tomabechi.Theorem21.conditionalGoalEntropyAt (physicalMass ()) ∂Measure.dirac ()) = 0
  rw [integral_dirac]
  simp [Tomabechi.Theorem21.conditionalGoalEntropyAt, physicalMass,
    Tomabechi.Theorem21.finiteConditionalEntropyTerm]

/-- The physical-layer law has both a deterministic goal and deterministic
output. Its joint law is already the conditional-independence reference law,
so it is a finite CMI law with score zero. -/
noncomputable def physicalLayerLaw :
    Tomabechi.Theorem22.ConditionalMutualInformationLaw Unit Bool Bool := by
  let input : Measure Unit := Measure.dirac ()
  let goal : Kernel Unit Bool := Kernel.const Unit (Measure.dirac false)
  let output : Kernel Unit Bool := Kernel.const Unit (Measure.dirac false)
  refine {
    input := input
    inputProbability := by dsimp [input]; infer_instance
    goalGivenInput := goal
    goalKernelMarkov := by dsimp [goal]; infer_instance
    actionGivenInput := output
    actionKernelMarkov := by dsimp [output]; infer_instance
    joint := input ⊗ₘ ((goal ∥ₖ output) ∘ₖ Kernel.copy Unit)
    jointGoalMarginal := ?_
    jointActionMarginal := ?_ }
  · letI : IsProbabilityMeasure input := by dsimp [input]; infer_instance
    letI : ProbabilityTheory.IsMarkovKernel goal := by dsimp [goal]; infer_instance
    letI : ProbabilityTheory.IsMarkovKernel output := by dsimp [output]; infer_instance
    calc
      (input ⊗ₘ ((goal ∥ₖ output) ∘ₖ Kernel.copy Unit)).map
          (fun z : Unit × (Bool × Bool) => (z.1, z.2.1)) =
          (input ⊗ₘ (goal ×ₖ output)).map (Prod.map id Prod.fst) := by
            rw [Kernel.parallelComp_comp_copy]
            rfl
      _ = input ⊗ₘ ((goal ×ₖ output).map Prod.fst) :=
        (Measure.compProd_map measurable_fst).symm
      _ = input ⊗ₘ goal := by rw [← Kernel.fst_eq, Kernel.fst_prod]
  · letI : IsProbabilityMeasure input := by dsimp [input]; infer_instance
    letI : ProbabilityTheory.IsMarkovKernel goal := by dsimp [goal]; infer_instance
    letI : ProbabilityTheory.IsMarkovKernel output := by dsimp [output]; infer_instance
    calc
      (input ⊗ₘ ((goal ∥ₖ output) ∘ₖ Kernel.copy Unit)).map
          (fun z : Unit × (Bool × Bool) => (z.1, z.2.2)) =
          (input ⊗ₘ (goal ×ₖ output)).map (Prod.map id Prod.snd) := by
            rw [Kernel.parallelComp_comp_copy]
            rfl
      _ = input ⊗ₘ ((goal ×ₖ output).map Prod.snd) :=
        (Measure.compProd_map measurable_snd).symm
      _ = input ⊗ₘ output := by rw [← Kernel.snd_eq, Kernel.snd_prod]

theorem physicalLayerLaw_goalMass_matches (g : Bool) :
    (physicalLayerLaw.goalGivenInput () {g}).toReal = physicalMass () g := by
  cases g <;> norm_num [physicalLayerLaw, physicalMass,
    Measure.dirac_apply, ProbabilityTheory.Kernel.const_apply]

theorem physicalLayerLaw_joint_eq_reference :
    physicalLayerLaw.joint = physicalLayerLaw.referenceMeasure := rfl

noncomputable def physicalLayerFiniteLaw :
    Tomabechi.Theorem22.FiniteConditionalMutualInformationLaw Unit Bool Bool := by
  refine ⟨physicalLayerLaw, ?_⟩
  letI : IsProbabilityMeasure physicalLayerLaw.input := physicalLayerLaw.inputProbability
  letI : ProbabilityTheory.IsMarkovKernel physicalLayerLaw.goalGivenInput :=
    physicalLayerLaw.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel physicalLayerLaw.actionGivenInput :=
    physicalLayerLaw.actionKernelMarkov
  letI : IsProbabilityMeasure physicalLayerLaw.joint :=
    physicalLayerLaw.joint_isProbabilityMeasure
  rw [← physicalLayerLaw_joint_eq_reference, InformationTheory.klDiv_self]
  norm_num

theorem physicalLayerFiniteLaw_score_zero :
    Tomabechi.Theorem22.finiteKLDivergenceScore
      physicalLayerFiniteLaw.toFiniteKLLaw = 0 := by
  change (InformationTheory.klDiv physicalLayerLaw.joint
    physicalLayerLaw.referenceMeasure).toReal = 0
  letI : IsProbabilityMeasure physicalLayerLaw.joint :=
    physicalLayerLaw.joint_isProbabilityMeasure
  rw [← physicalLayerLaw_joint_eq_reference, InformationTheory.klDiv_self]
  norm_num

/-- Capacity examples retain the complete joint/reference pair, so an
embedding can be audited for equality of laws rather than only equality of
the resulting real score. -/
structure C3CMIPair where
  joint : Measure ((Unit × Bool) × Bool)
  reference : Measure ((Unit × Bool) × Bool)

noncomputable def physicalCMIPair : C3CMIPair := by
  letI : IsProbabilityMeasure physicalLayerLaw.joint :=
    physicalLayerLaw.joint_isProbabilityMeasure
  exact ⟨Tomabechi.Theorem19_22.directActionGoalJoint physicalLayerLaw.joint,
    Tomabechi.Theorem19_22.directCMIReference physicalLayerLaw.joint⟩

noncomputable def upperJoint : Measure (Unit × (Bool × Bool)) :=
  by
    letI : IsProbabilityMeasure (Measure.dirac () : Measure Unit) := inferInstance
    exact Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint
      (Measure.dirac ()) inputMass inputMass_measurable
      (by filter_upwards with x; exact fun g => inputMass_nonneg x g)
      (by filter_upwards with x; exact inputMass_sum x)
      inputAction inputAction_measurable

theorem upperJoint_isProbability : IsProbabilityMeasure upperJoint := by
  letI : IsProbabilityMeasure (Measure.dirac () : Measure Unit) := inferInstance
  exact Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_isProbability
    (Measure.dirac ()) inputMass inputMass_measurable
    (by filter_upwards with x; exact fun g => inputMass_nonneg x g)
    (by filter_upwards with x; exact inputMass_sum x)
    inputAction inputAction_measurable

noncomputable def upperCMIPair : C3CMIPair := by
  letI : IsProbabilityMeasure upperJoint := upperJoint_isProbability
  exact ⟨Tomabechi.Theorem19_22.directActionGoalJoint upperJoint,
    Tomabechi.Theorem19_22.directCMIReference upperJoint⟩

noncomputable def cmiPairForProblem (q : Bool) : C3CMIPair :=
  if q then upperCMIPair else physicalCMIPair

noncomputable def cmiPairScore (p : C3CMIPair) : ℝ :=
  (InformationTheory.klDiv p.joint p.reference).toReal

theorem physicalCMIPair_score_zero : cmiPairScore physicalCMIPair = 0 := by
  letI : IsProbabilityMeasure physicalLayerLaw.joint :=
    physicalLayerLaw.joint_isProbabilityMeasure
  change (InformationTheory.klDiv
    (Tomabechi.Theorem19_22.directActionGoalJoint physicalLayerLaw.joint)
    (Tomabechi.Theorem19_22.directCMIReference physicalLayerLaw.joint)).toReal = 0
  rw [Tomabechi.Theorem19_22.directCMI_kl_eq_existing physicalLayerLaw]
  exact physicalLayerFiniteLaw_score_zero

theorem physicalCMIPair_kl_finite :
    InformationTheory.klDiv physicalCMIPair.joint physicalCMIPair.reference ≠ ⊤ := by
  letI : IsProbabilityMeasure physicalLayerLaw.joint :=
    physicalLayerLaw.joint_isProbabilityMeasure
  have hkl := Tomabechi.Theorem19_22.directCMI_kl_eq_existing physicalLayerLaw
  have hphysical : InformationTheory.klDiv physicalLayerLaw.joint
      physicalLayerLaw.referenceMeasure = 0 := by
    rw [← physicalLayerLaw_joint_eq_reference, InformationTheory.klDiv_self]
  have hpairzero : InformationTheory.klDiv physicalCMIPair.joint
      physicalCMIPair.reference = 0 := by
    change InformationTheory.klDiv
      (Tomabechi.Theorem19_22.directActionGoalJoint physicalLayerLaw.joint)
      (Tomabechi.Theorem19_22.directCMIReference physicalLayerLaw.joint) = 0
    exact hkl.trans hphysical
  rw [hpairzero]
  exact ENNReal.zero_ne_top

noncomputable def physicalCMIPairFiniteLaw :
    Tomabechi.Theorem22.FiniteKLDivergenceLaw ((Unit × Bool) × Bool) :=
  ⟨physicalCMIPair.joint, physicalCMIPair.reference, physicalCMIPair_kl_finite⟩

/-- All four Theorem 21 conclusions, including direct KL CMI, use the same
mean-field input's atom law and the same upper-layer information law. -/
noncomputable def stageInformation (n : ℕ) :=
  Tomabechi.Theorem22.meanField_stage_theorem21_four_conclusions_directKL
    (packageQuadraticStage n (valleySequence n).initial (valleySequence n).startTime)
    (branchContext n)
    (Measure.dirac ()) inputMass inputAction (fun _ => ((n + 1 : ℕ) : Atom))
    inputAction_measurable
    (by
      filter_upwards with x
      intro g hg
      change ((n + 1 : ℕ) : Atom) ∈ {((n + 1 : ℕ) : Atom)}
      simp)
    (by
      filter_upwards with x
      intro g
      exact inputMass_nonneg x g)
    (by
      filter_upwards with x
      exact inputMass_sum x)
    (by
      filter_upwards with x
      intro g hg g' h
      exact inputAction_injective x g hg g' h)
    inputMass_measurable
    inputEntropy_pos
    (fun a : Atom => a) (by intro a b h; exact h)
    (by intro a b hab; exact hab)
    (by
      change {((n + 1 : ℕ) : Atom)} = (fun a : Atom => a) '' {((n + 1 : ℕ) : Atom)}
      simp)
    (by
      change {((n + 1 : ℕ) : Atom)} = (fun a : Atom => a) '' {((n + 1 : ℕ) : Atom)}
      simp)
    (by
      change (⊤ : Atom) = ⊤
      rfl)
    (by
      change ((n + 1 : ℕ) : Atom) = sSup {((n + 1 : ℕ) : Atom)}
      simp)

theorem stageInformation_uses_hStageSequence (n : ℕ) :
    packageQuadraticStage n (valleySequence n).initial (valleySequence n).startTime =
      hStageSequence n := rfl

theorem upperCMIPair_score_log_two : cmiPairScore upperCMIPair = Real.log 2 := by
  letI : IsProbabilityMeasure upperJoint := upperJoint_isProbability
  have hstage := stageInformation 0
  rcases hstage with ⟨_w, _minimum, _displacement, _orbit, hinfo⟩
  have hscore :
      cmiPairScore upperCMIPair =
        Tomabechi.Theorem21.conditionalGoalEntropy (Measure.dirac ()) inputMass := by
    change Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_directCMIScore
      (Measure.dirac ()) inputMass inputMass_measurable
      (by filter_upwards with x; exact fun g => inputMass_nonneg x g)
      (by filter_upwards with x; exact inputMass_sum x)
      inputAction inputAction_measurable (by infer_instance) = _
    exact hinfo.1
  calc
    cmiPairScore upperCMIPair =
        Tomabechi.Theorem21.conditionalGoalEntropy (Measure.dirac ()) inputMass := hscore
    _ = Real.log 2 := inputEntropy_eq_log_two

theorem upperCMIPair_kl_finite :
    InformationTheory.klDiv upperCMIPair.joint upperCMIPair.reference ≠ ⊤ := by
  intro htop
  have hscore := upperCMIPair_score_log_two
  change (InformationTheory.klDiv upperCMIPair.joint upperCMIPair.reference).toReal =
    Real.log 2 at hscore
  have hz : (0 : ℝ) = Real.log 2 := by simpa [htop] using hscore
  exact (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))) hz.symm

noncomputable def upperCMIPairFiniteLaw :
    Tomabechi.Theorem22.FiniteKLDivergenceLaw ((Unit × Bool) × Bool) :=
  ⟨upperCMIPair.joint, upperCMIPair.reference, upperCMIPair_kl_finite⟩

/-- The physical problem persists at every order layer. A distinct upper
problem carries the exact joint/reference pair generated by Theorem 21's
`μ/mass/action`; only its admissibility begins above the physical bottom. -/
def c3ProblemAdmissible (a : Atom) : Set Bool :=
  if a = (0 : Atom) then {false} else Set.univ

theorem c3Problem_false_admissible (a : Atom) : false ∈ c3ProblemAdmissible a := by
  by_cases h : a = (0 : Atom) <;> simp [c3ProblemAdmissible, h]

noncomputable def c3CapacityScore (a : Atom) (q : Bool) : ℝ :=
  cmiPairScore (cmiPairForProblem q)

theorem c3ProblemScores_bounded (a : Atom) :
    BddAbove (c3CapacityScore a '' c3ProblemAdmissible a) := by
  refine ⟨Real.log 2, ?_⟩
  rintro r ⟨q, hq, rfl⟩
  cases q <;> simp [c3CapacityScore, cmiPairForProblem,
    physicalCMIPair_score_zero, upperCMIPair_score_log_two]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

noncomputable def c3LayerCapacity (a : Atom) : ℝ :=
  Tomabechi.Theorem19.dependentLayerCapacity (fun _ : Atom => Bool)
    c3ProblemAdmissible c3CapacityScore a

/-- The identity embedding preserves both measures of each complete CMI pair. -/
theorem c3ProblemPair_preserved
    {a b : Atom} (hab : a ≤ b) (q : Bool) (hq : q ∈ c3ProblemAdmissible a) :
    cmiPairForProblem q = cmiPairForProblem q := rfl

theorem c3ProblemJoint_preserved
    {a b : Atom} (hab : a ≤ b) (q : Bool) (hq : q ∈ c3ProblemAdmissible a) :
    (cmiPairForProblem q).joint = (cmiPairForProblem q).joint := rfl

theorem c3ProblemReference_preserved
    {a b : Atom} (hab : a ≤ b) (q : Bool) (hq : q ∈ c3ProblemAdmissible a) :
    (cmiPairForProblem q).reference = (cmiPairForProblem q).reference := rfl

theorem c3LayerCapacity_nondecreasing : Monotone c3LayerCapacity := by
  intro a b hab
  unfold c3LayerCapacity
  exact Tomabechi.Theorem19.dependentCapacity_nondecreasing_of_scorePreservingEmbedding
    (fun _ : Atom => Bool) c3ProblemAdmissible c3CapacityScore
    (fun x => ⟨false, c3Problem_false_admissible x⟩)
    c3ProblemScores_bounded
    (fun {_ _} _ q => q)
    (by intro a' b' hab' q₁ q₂ h; exact h)
    (by
      intro a' b' hab' q hq
      by_cases ha : a' = (0 : Atom)
      · have hq' : q = false := by simpa [c3ProblemAdmissible, ha] using hq
        subst q
        exact c3Problem_false_admissible b'
      · have hb : b' ≠ (0 : Atom) := by
          intro hb
          apply ha
          have hab0 : a' ≤ (0 : Atom) := by simpa [hb] using hab'
          exact le_antisymm hab0 bot_le
        simp [c3ProblemAdmissible, hb])
    (by
      intro a' b' hab' q hq
      have hpair := c3ProblemPair_preserved hab' q hq
      exact congrArg cmiPairScore hpair)
    a b hab

theorem c3LayerCapacity_bottom_eq_zero : c3LayerCapacity ⊥ = 0 := by
  unfold c3LayerCapacity Tomabechi.Theorem19.dependentLayerCapacity
  have himage : c3CapacityScore ⊥ '' c3ProblemAdmissible ⊥ = {0} := by
    ext r
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqfalse : q = false := by simpa [c3ProblemAdmissible] using hq
      subst q
      simpa [c3CapacityScore, cmiPairForProblem] using physicalCMIPair_score_zero
    · intro hr
      refine ⟨false, ?_, ?_⟩
      · simpa [c3ProblemAdmissible]
      · simpa [c3CapacityScore, cmiPairForProblem, physicalCMIPair_score_zero] using
          (Set.mem_singleton_iff.mp hr).symm
  rw [himage]
  simp

theorem c3LayerCapacity_top_positive : 0 < c3LayerCapacity ⊤ := by
  unfold c3LayerCapacity
  have hscore : c3CapacityScore ⊤ true = Real.log 2 := by
    simp [c3CapacityScore, cmiPairForProblem, upperCMIPair_score_log_two]
  have hmem : c3CapacityScore ⊤ true ∈
      c3CapacityScore ⊤ '' c3ProblemAdmissible ⊤ := by
    exact ⟨true, by simp [c3ProblemAdmissible], rfl⟩
  have hle := le_csSup (c3ProblemScores_bounded ⊤) hmem
  rw [hscore] at hle
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hle

theorem layerU_monotone : Monotone layerU := by
  intro n m hnm
  simp only [layerU]
  exact_mod_cast Nat.add_le_add_right hnm 1

theorem c3LayerCapacity_along_stages_monotone :
    Monotone (fun n => c3LayerCapacity (layerU n)) :=
  c3LayerCapacity_nondecreasing.comp layerU_monotone

theorem hStageSequence_initial_recurrence (n : ℕ) :
    (hStageSequence (n + 1)).initial = representation (n + 1 : ℕ) +
      ((hStageSequence n).initial - representation (n + 1 : ℕ)) *
        Real.exp (-stageDuration n) := by
  rw [hStageSequence_transition n]
  have horbit := Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit_eq_witness_orbit
    (center := representation (n + 1 : ℕ)) (initial := (valleySequence n).initial)
    (start := (valleySequence n).startTime)
    (t := stageTime n + stageDuration n) (by
      have hs : (valleySequence n).startTime = stageTime n := by
        change (valleySequence n).startTime = stageTime n
        exact hStageSequence_start n
      rw [hs]
      exact le_add_of_nonneg_right (stageDuration_pos n).le)
  have hshape := valleySequence_shape n
  have hstageShape : (hStageSequence n).toStageValleySpec =
      Tomabechi.Examples.Theorem23B.quadraticStage
        (representation (n + 1 : ℕ)) (valleySequence n).initial (valleySequence n).startTime := by
    rw [hStageSequence_toStageValleySpec n, hshape]
    simp [Tomabechi.Examples.Theorem23B.quadraticStage]
  have horbit' :
      Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit
          (representation (n + 1 : ℕ)) (valleySequence n).initial (stageTime n)
          (stageTime n + stageDuration n) =
        (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).orbit
          (stageTime n + stageDuration n) := by
    have hs : (valleySequence n).startTime = stageTime n := by
      change (valleySequence n).startTime = stageTime n
      exact hStageSequence_start n
    have hchosen :
        (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).orbit
            (stageTime n + stageDuration n) =
          (Tomabechi.Theorem22.chooseStageValley
            (Tomabechi.Examples.Theorem23B.quadraticStage
              (representation (n + 1 : ℕ)) (valleySequence n).initial
              (valleySequence n).startTime)).orbit
            (stageTime n + stageDuration n) := by
      change (Tomabechi.Theorem22.chooseStageValley
        ((hStageSequence n).toStageValleySpec)).orbit _ = _
      rw [hstageShape]
    calc
      _ = Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit
          (representation (n + 1 : ℕ)) (valleySequence n).initial (valleySequence n).startTime
          (stageTime n + stageDuration n) := by rw [hs]
      _ = (Tomabechi.Theorem22.chooseStageValley
          (Tomabechi.Examples.Theorem23B.quadraticStage
            (representation (n + 1 : ℕ)) (valleySequence n).initial
            (valleySequence n).startTime)).orbit
          (stageTime n + stageDuration n) := horbit
      _ = _ := hchosen.symm
  rw [← horbit']
  rw [Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit]
  have htime : stageTime n + stageDuration n - stageTime n = stageDuration n := by ring
  rw [htime]
  change representation (n + 1 : ℕ) +
    ((valleySequence n).initial - representation (n + 1 : ℕ)) *
    Real.exp (-stageDuration n) = _
  rfl

theorem hStageSequence_initial_between_centers (n : ℕ) :
    0 ≤ (hStageSequence n).initial ∧
      (hStageSequence n).initial ≤ representation (n + 1 : ℕ) := by
  induction n with
  | zero =>
      change 0 ≤ 0 ∧ 0 ≤ representation 1
      constructor
      · norm_num
      · have hp : 0 ≤ representation 1 := by norm_num [representation]
        exact hp
  | succ n ih =>
      rw [hStageSequence_initial_recurrence n]
      have hp : 0 ≤ representation (n + 1 : ℕ) := by
        simp only [representation]
        exact div_nonneg (Nat.cast_nonneg _) (by positivity)
      have hnext : representation (n + 1 : ℕ) ≤ representation (n + 2 : ℕ) := by
        apply representation_monotone
        exact_mod_cast Nat.le_succ (n + 1)
      have he : 0 < Real.exp (-stageDuration n) := Real.exp_pos (-stageDuration n)
      have he1 : Real.exp (-stageDuration n) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith [stageDuration_pos n]
      constructor
      · have hconv : 0 ≤ (1 - Real.exp (-stageDuration n)) * representation (n + 1 : ℕ) :=
          mul_nonneg (by linarith) hp
        have hconv' : 0 ≤ Real.exp (-stageDuration n) * (hStageSequence n).initial :=
          mul_nonneg he.le ih.1
        have hid :
            representation (n + 1 : ℕ) +
              ((hStageSequence n).initial - representation (n + 1 : ℕ)) *
              Real.exp (-stageDuration n) =
                (1 - Real.exp (-stageDuration n)) * representation (n + 1 : ℕ) +
                  Real.exp (-stageDuration n) * (hStageSequence n).initial := by ring
        rw [hid]
        exact add_nonneg hconv hconv'
      · have hscaled :
          Real.exp (-stageDuration n) * (hStageSequence n).initial ≤
          Real.exp (-stageDuration n) * representation (n + 1 : ℕ) :=
          mul_le_mul_of_nonneg_left ih.2 he.le
        have hid :
            representation (n + 1 : ℕ) +
              ((hStageSequence n).initial - representation (n + 1 : ℕ)) *
              Real.exp (-stageDuration n) =
                (1 - Real.exp (-stageDuration n)) * representation (n + 1 : ℕ) +
                  Real.exp (-stageDuration n) * (hStageSequence n).initial := by ring
        rw [hid]
        have hid' : (1 - Real.exp (-stageDuration n)) * representation (n + 1 : ℕ) +
            Real.exp (-stageDuration n) * representation (n + 1 : ℕ) =
              representation (n + 1 : ℕ) := by ring
        linarith

theorem hStageSequence_amplitude_le_one (n : ℕ) :
    (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).decayAmplitude ≤ 1 := by
  rw [Tomabechi.Theorem22.chooseAllMeanFieldStageValleys,
    Tomabechi.Theorem22.chooseAllStageValleys,
    Tomabechi.Theorem22.meanFieldStageSequence]
  rw [hStageSequence_toStageValleySpec n, valleySequence_shape,
    Tomabechi.Examples.Theorem23B.quadraticStage_decayAmplitude]
  have hp : representation (n + 1 : ℕ) < 1 := representation_lt_top (n + 1)
  have hi : 0 ≤ (valleySequence n).initial ∧
      (valleySequence n).initial ≤ representation (n + 1 : ℕ) := by
    change 0 ≤ (valleySequence n).initial ∧
      (valleySequence n).initial ≤ representation (n + 1 : ℕ)
    exact hStageSequence_initial_between_centers n
  have hnonneg : 0 ≤ representation (n + 1 : ℕ) - (valleySequence n).initial := by linarith
  calc
    |(valleySequence n).initial - representation (n + 1 : ℕ)| =
        |representation (n + 1 : ℕ) - (valleySequence n).initial| := abs_sub_comm _ _
    _ = representation (n + 1 : ℕ) - (valleySequence n).initial := abs_of_nonneg hnonneg
    _ ≤ 1 := by linarith

theorem hStageSequence_wait_bound (n : ℕ) :
    max 0
      (1 / (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).decayRate *
        Real.log ((Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).decayAmplitude /
          errorTolerance n)) ≤ stageDuration n := by
  have hrate :
      (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).decayRate = 1 := by
    rw [Tomabechi.Theorem22.chooseAllMeanFieldStageValleys,
      Tomabechi.Theorem22.chooseAllStageValleys,
      Tomabechi.Theorem22.meanFieldStageSequence,
      hStageSequence_toStageValleySpec n, valleySequence_shape]
    exact Tomabechi.Examples.Theorem23B.quadraticStage_decayRate _ _ _
  have heps := errorTolerance_pos n
  have hamp := hStageSequence_amplitude_le_one n
  have hratio :
      (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).decayAmplitude /
          errorTolerance n ≤ stageDuration n := by
    rw [errorTolerance, centerGap, stageDuration]
    calc
      _ ≤ 1 / (1 / (((n : ℝ) + 2) * ((n : ℝ) + 3)) / 4) := by
        exact div_le_div_of_nonneg_right hamp (by positivity)
      _ = 4 * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by field_simp
  have hlog : Real.log
      ((Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).decayAmplitude /
        errorTolerance n) ≤ stageDuration n := by
    have ha := Tomabechi.Theorem22.StageValleyWitness.decayAmplitude_nonneg
      (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n)
    exact (Real.log_le_self (div_nonneg ha (le_of_lt heps))).trans hratio
  rw [hrate]
  simpa [hrate] using (max_le (stageDuration_pos n).le hlog)

noncomputable def stageTheta (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | k + 1 => gapThreshold k

theorem stageTheta_nonneg (n : ℕ) : 0 ≤ stageTheta n := by
  cases n with
  | zero => simp [stageTheta]
  | succ k =>
      simp only [stageTheta, gapThreshold]
      positivity

theorem hStageSequence_gap_threshold (n : ℕ) :
    stageTheta (n + 1) <
      ((hStageSequence (n + 1)).gain *
          (hStageSequence (n + 1)).presenceGain *
          (hStageSequence (n + 1)).curvature -
        (hStageSequence (n + 1)).backgroundCurvature) / 2 *
        ‖(Tomabechi.Theorem22.chooseAllMeanFieldStageValleys
              hStageSequence (n + 1)).minimizer -
          (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys
              hStageSequence n).minimizer‖ ^ 2 := by
  rw [hStageSequence_minimizer (n + 1), hStageSequence_minimizer]
  rw [representation_center_gap n]
  have hgap := centerGap_pos n
  have hspec :
      (hStageSequence (n + 1)).gain = 1 ∧
      (hStageSequence (n + 1)).presenceGain = 1 ∧
      (hStageSequence (n + 1)).curvature = 1 ∧
      (hStageSequence (n + 1)).backgroundCurvature = 0 := by
    simp [hStageSequence, packageQuadraticStage,
      Tomabechi.Examples.Theorem23B.quadraticStage]
  rw [hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2]
  simp only [stageTheta, gapThreshold]
  rw [Real.norm_eq_abs, abs_of_pos hgap]
  nlinarith [sq_pos_of_pos hgap]

theorem hStageSequence_segment_in_next_ball (n : ℕ) :
    segment ℝ
        (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence n).minimizer
        (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys hStageSequence (n + 1)).minimizer ⊆
      Metric.closedBall (hStageSequence (n + 1)).center
        (hStageSequence (n + 1)).radius := by
  rw [hStageSequence_minimizer, hStageSequence_minimizer, hStageSequence_center]
  have horder : representation (n + 1 : ℕ) ≤ representation (n + 2 : ℕ) := by
    apply representation_monotone
    exact_mod_cast Nat.le_succ (n + 1)
  rw [segment_eq_Icc horder]
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs]
  have hxabs : |x - representation (n + 2 : ℕ)| ≤ centerGap n := by
    rw [abs_le]
    constructor
    · nlinarith [hx.1, representation_center_gap n]
    · nlinarith [hx.2, representation_center_gap n]
  have hradius : 1 ≤ (hStageSequence (n + 1)).radius := by
    simp [hStageSequence, packageQuadraticStage,
      Tomabechi.Examples.Theorem23B.quadraticStage]
  have hgap_lt_one : centerGap n ≤ 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hden : 1 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 3) := by
      nlinarith [sq_nonneg (n : ℝ)]
    rw [centerGap]
    calc
      1 / (((n : ℝ) + 2) * ((n : ℝ) + 3)) ≤ 1 / 1 :=
        one_div_le_one_div_of_le (by norm_num) hden
      _ = 1 := by norm_num
  exact hxabs.trans (hgap_lt_one.trans hradius)

/-- The same average-field column supplies the H-stage hypotheses consumed by
the 21/22/23-B switching core.  The core returns the original, non-relaxed
Condition 23-B conclusions for the explicit common representation and dwell
schedule. -/
noncomputable def hStageSequence_condition23B :=
  Tomabechi.Theorem23.meanField_stage_specs_and_switches_give_condition23B_core
    layerU layerV layerU_update layerU_below_top layerV_new
    hStageSequence representation representation_injective hStageSequence_center
    stageTheta stageTheta_nonneg hStageSequence_gap_threshold
    hStageSequence_segment_in_next_ball
    stageTime stageDuration errorTolerance hStageSequence_start
    hStageSequence_transition stageTime_recurrence stageDuration_pos
    stageTime_unbounded errorTolerance_pos hStageSequence_wait_bound

/-- Named forms of the original scalar 23-B output, so the complete switching
certificate can be stored and reviewed without unfolding the core's nested
conjunction each time. -/
noncomputable def hStageSequenceStageSpecs :=
  Tomabechi.Theorem22.meanFieldStageSequence hStageSequence

noncomputable def hStageSequenceValleys :=
  Tomabechi.Theorem22.chooseAllStageValleys hStageSequenceStageSpecs

noncomputable def hStageSequenceTCZ (n : ℕ) :=
  Tomabechi.Theorem23.stageTCZ
    (fun k x => Tomabechi.Theorem22.stageEffectivePotential
      (hStageSequenceStageSpecs k) x)
    (fun k => (hStageSequenceValleys k).minimizer)
    stageTheta
    (fun k => Metric.closedBall (hStageSequenceStageSpecs k).center
      (hStageSequenceStageSpecs k).radius)
    (fun k => closure ((hStageSequenceValleys k).orbit ''
      Set.Ici (hStageSequenceStageSpecs k).startTime)) n

noncomputable def hStageSequenceStitchedTrajectory :=
  Tomabechi.Theorem23.canonicalStageTrajectory hStageSequenceStageSpecs
    stageTime stageDuration stageDuration_pos stageTime_recurrence stageTime_unbounded

/-- The full explicit 23-B output for the original H-stage sequence. The
certificate records every switching conclusion used downstream. -/
structure HStageSwitchingCertificate : Prop where
  layer_progress :
    (∀ n, layerU n < ⊤) ∧ Monotone layerU ∧
      (∀ n, layerU n < layerU (n + 1)) ∧
      (∀ B : ℝ, ∃ n, B < stageTime n) ∧
      (∀ n, stageTime n < stageTime (n + 1))
  adjacent_centers_distinct : ∀ n,
    (hStageSequenceStageSpecs n).center ≠
      (hStageSequenceStageSpecs (n + 1)).center
  adjacent_valleys_distinct : ∀ n,
    0 < ‖(hStageSequenceValleys (n + 1)).minimizer -
      (hStageSequenceValleys n).minimizer‖
  tcz_closed : ∀ n, IsClosed (hStageSequenceTCZ n)
  adjacent_tcz_distinct : ∀ n,
    hStageSequenceTCZ (n + 1) ≠ hStageSequenceTCZ n
  tcz_nonempty : ∀ n, (hStageSequenceTCZ n).Nonempty
  stitched_dwell_and_endpoint_error : ∀ n,
    Set.EqOn hStageSequenceStitchedTrajectory (hStageSequenceValleys n).orbit
      (Set.Icc (stageTime n) (stageTime n + stageDuration n)) ∧
    dist (hStageSequenceStitchedTrajectory (stageTime n + stageDuration n))
      (hStageSequenceValleys n).minimizer ≤ errorTolerance n
  every_finite_time_in_a_dwell : ∀ t, stageTime 0 ≤ t →
    ∃ n, t ∈ Set.Ico (stageTime n) (stageTime n + stageDuration n)
  switches_beyond_every_time_and_stage : ∀ T K, ∃ n, K ≤ n ∧ T < stageTime n

theorem hStageSequence_switching_certificate : HStageSwitchingCertificate := by
  have h := hStageSequence_condition23B
  refine ⟨h.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hStageSequenceStageSpecs] using h.2.1
  · simpa [hStageSequenceValleys, hStageSequenceStageSpecs] using h.2.2.1
  · simpa [hStageSequenceTCZ, hStageSequenceValleys, hStageSequenceStageSpecs] using
      h.2.2.2.1
  · simpa [hStageSequenceTCZ, hStageSequenceValleys, hStageSequenceStageSpecs] using
      h.2.2.2.2.1
  · simpa [hStageSequenceTCZ, hStageSequenceValleys, hStageSequenceStageSpecs] using
      h.2.2.2.2.2.1
  · simpa [hStageSequenceStitchedTrajectory, hStageSequenceValleys,
      hStageSequenceStageSpecs] using h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2

/-- One reviewable certificate collecting the law-preserving monotone capacity
with its physical and positive endpoints. `stageInformation` and
`hStageSequence_condition23B` are the separate same-sequence stage witnesses. -/
theorem c3_sharedWitness :
    Monotone c3LayerCapacity ∧
      c3LayerCapacity ⊥ = 0 ∧ 0 < c3LayerCapacity ⊤ := by
  exact ⟨c3LayerCapacity_nondecreasing, c3LayerCapacity_bottom_eq_zero,
    c3LayerCapacity_top_positive⟩

end Tomabechi.Consistency.C3

#print axioms Tomabechi.Consistency.C3.averagePresentation_integral
#print axioms Tomabechi.Consistency.C3.packageQuadraticStage_toStageValleySpec
#print axioms Tomabechi.Consistency.C3.physicalLayerLaw_goalMass_matches
#print axioms Tomabechi.Consistency.C3.physicalLayerFiniteLaw_score_zero
#print axioms Tomabechi.Consistency.C3.physicalCMIPair_kl_finite
#print axioms Tomabechi.Consistency.C3.upperCMIPair_kl_finite
#print axioms Tomabechi.Consistency.C3.stageInformation
#print axioms Tomabechi.Consistency.C3.hStageSequence_condition23B
#print axioms Tomabechi.Consistency.C3.hStageSequence_switching_certificate
#print axioms Tomabechi.Consistency.C3.c3_sharedWitness
#print axioms Tomabechi.Consistency.C3.c3LayerCapacity_nondecreasing
#print axioms Tomabechi.Consistency.C3.c3LayerCapacity_bottom_eq_zero
#print axioms Tomabechi.Consistency.C3.c3LayerCapacity_top_positive
#print axioms Tomabechi.Consistency.C3.c3LayerCapacity_along_stages_monotone
