import Theorem21_P13
import Theorem22_InvariantRegion

set_option maxHeartbeats 1000000

/-!
# H-stage緩和入力の定理21第4結論（直接KL型CMI）接続

既存P13の情報論的条件をそのまま用いながら、谷・軌道の結論を
初期全sublevel等式のない不変領域証人へ接続する。
-/

open MeasureTheory
open Tomabechi.Theorem21
open Tomabechi.Theorem19_22
open Tomabechi.Theorem22InvariantRegion

namespace Tomabechi.Theorem22InvariantRegionP13

/-- Relaxed mean-field stages retain the first three quantitative conclusions
and the same generated-joint direct KL-type CMI conclusion as P13. The
branch/support/LUB correspondence remains explicit. -/
theorem invariantRegion_meanField_stage_theorem21_four_conclusions_directKL
    {L X G Y : Type*} [CompleteLattice L] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] [StandardBorelSpace Y]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (D : Tomabechi.Theorem21.Theorem21BranchContext L)
    (μ : Measure X) (mass : X → G → ℝ)
    (action : X → G → Y) (goalAbstraction : G → L)
    (haction_meas : ∀ g, Measurable (fun x => action x g))
    (hgoals_in_branch : ∀ᵐ x ∂μ, ∀ g, 0 < mass x g →
      goalAbstraction g ∈ D.branch)
    (hmass_nonneg_ae : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hmass_sum_one_ae : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (hinjective_ae : ∀ᵐ x ∂μ, ∀ g, 0 < mass x g →
      ∀ g', action x g' = action x g → g' = g)
    (hmass_meas : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    [IsProbabilityMeasure μ]
    (hinput_entropy_positive : 0 < conditionalGoalEntropy μ mass)
    (branchRepresentation : s.averagePresentation.Atom → L)
    (hbranchRepresentation_injective : Function.Injective branchRepresentation)
    (hbranchRepresentation_monotone : ∀ a b,
      s.averagePresentation.atomOrder.le a b →
        branchRepresentation a ≤ branchRepresentation b)
    (hbranch_eq_image : D.branch =
      branchRepresentation '' s.averagePresentation.sourceLayer)
    (hsymbolSupport_eq_image : D.symbolSupport =
      branchRepresentation '' s.averagePresentation.measureSupport)
    (hbranch_top :
      branchRepresentation s.averagePresentation.abstractTop = ⊤)
    (hbranch_lub :
      branchRepresentation s.averagePresentation.supportLub = sSup D.symbolSupport) :
    ∃ w : InvariantRegionStageWitness s,
      (w.minimizer ∈ interior (Metric.closedBall s.center s.radius) ∧
        IsMinOn (fun x => s.background x - s.gain * s.presenceGain * s.meanField x)
          (Metric.closedBall s.center s.radius) w.minimizer ∧
        (∀ y ∈ Metric.closedBall s.center s.radius,
          s.background y - s.gain * s.presenceGain * s.meanField y =
            s.background w.minimizer - s.gain * s.presenceGain *
              s.meanField w.minimizer → y = w.minimizer)) ∧
      (‖w.minimizer - s.center‖ ≤
          s.gradientBound / (s.gain * s.presenceGain * s.curvature -
            s.backgroundCurvature) ∧
        s.backgroundGradient w.minimizer - (s.gain * s.presenceGain) •
          s.meanFieldGradient w.minimizer = 0 ∧
        0 < s.gain * s.presenceGain * s.curvature - s.backgroundCurvature) ∧
      (w.orbit s.startTime = s.initial ∧
        (∀ t ∈ Set.Ici s.startTime,
          w.orbit t ∈ s.sublevel ∧
            dist (w.orbit t) w.minimizer ≤
              w.decayAmplitude * Real.exp (-w.decayRate * (t - s.startTime))) ∧
        (∀ t, s.startTime ≤ t →
          HasDerivAt w.orbit
            (-(s.mobility (w.orbit t)
              (s.backgroundGradient (w.orbit t) -
                (s.gain * s.presenceGain) • s.meanFieldGradient (w.orbit t)))) t)) ∧
      (finiteGoalActionGeneratedJoint_directCMIScore
          μ mass hmass_meas hmass_nonneg_ae hmass_sum_one_ae action haction_meas
          (finiteGoal_nonempty_of_conditionalGoalEntropy_pos μ mass
            hinput_entropy_positive) = conditionalGoalEntropy μ mass ∧
        0 < finiteGoalActionGeneratedJoint_directCMIScore
          μ mass hmass_meas hmass_nonneg_ae hmass_sum_one_ae action haction_meas
          (finiteGoal_nonempty_of_conditionalGoalEntropy_pos μ mass
            hinput_entropy_positive) ∧
        (∀ᵐ x ∂μ, ∀ g, 0 < mass x g → goalAbstraction g ∈ D.branch)) ∧
      (Function.Injective branchRepresentation ∧
        (∀ a b, s.averagePresentation.atomOrder.le a b →
          branchRepresentation a ≤ branchRepresentation b) ∧
        D.branch = branchRepresentation '' s.averagePresentation.sourceLayer ∧
        D.symbolSupport =
          branchRepresentation '' s.averagePresentation.measureSupport ∧
        branchRepresentation s.averagePresentation.abstractTop = ⊤ ∧
        branchRepresentation s.averagePresentation.supportLub =
          sSup D.symbolSupport) := by
  let w := chooseInvariantRegionStageWitness s
  have hinfo := finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy
    μ mass hmass_meas hmass_nonneg_ae hmass_sum_one_ae action haction_meas
    hinjective_ae hinput_entropy_positive
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨w.minimizer_interior, w.minimizer_is_min, w.minimizer_unique⟩
  · exact ⟨w.displacement_bound, w.stationary, w.positive_margin⟩
  · refine ⟨w.initial_condition, ?_, ?_⟩
    · intro t ht
      exact ⟨w.orbit_in_region t ht, w.distance_decay t ht⟩
    · intro t ht
      exact w.orbit_ode_forward t ht
  · exact ⟨hinfo.1, hinfo.2, hgoals_in_branch⟩
  · exact ⟨hbranchRepresentation_injective, hbranchRepresentation_monotone,
      hbranch_eq_image, hsymbolSupport_eq_image, hbranch_top, hbranch_lub⟩

end Tomabechi.Theorem22InvariantRegionP13
