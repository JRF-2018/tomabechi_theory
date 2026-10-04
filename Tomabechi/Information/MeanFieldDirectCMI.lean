import Theorem19_22

/-!
# 定理21の第4結論：生成jointの直接KL型CMIへの接続

定理22の平均場段階入力から得られる谷・変位・指数軌道の三結論を保ち、
第4結論だけを同じ `μ/mass/action` が生成するjointの直接KL型CMIで返す。
joint、事前kernel、条件付きエントロピーは別の法則へ置き換えず、
`Theorem19_22` の生成・disintegration同定を通じて一致させる。
-/

namespace Tomabechi.Theorem22

open MeasureTheory
open Tomabechi.Theorem21
open Tomabechi.Theorem19_22

/-- The four Theorem 21 conclusion groups for one mean-field stage, with the
fourth group expressed using the direct KL-type conditional mutual information
of the joint generated from the same input law, goal mass, and action. The
stage's branch, support, and LUB correspondence remain part of the result. -/
theorem meanField_stage_theorem21_four_conclusions_directKL
    {L X G Y : Type*} [CompleteLattice L] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] [StandardBorelSpace Y]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (s : MeanFieldStageInput E) (D : Theorem21BranchContext L)
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
      s.averagePresentation.atomOrder.le a b → branchRepresentation a ≤ branchRepresentation b)
    (hbranch_eq_image : D.branch =
      branchRepresentation '' s.averagePresentation.sourceLayer)
    (hsymbolSupport_eq_image : D.symbolSupport =
      branchRepresentation '' s.averagePresentation.measureSupport)
    (hbranch_top : branchRepresentation s.averagePresentation.abstractTop = ⊤)
    (hbranch_lub : branchRepresentation s.averagePresentation.supportLub =
      sSup D.symbolSupport) :
    ∃ w : StageValleyWitness s.toStageValleySpec,
      (w.minimizer ∈ interior (Metric.closedBall s.center s.radius) ∧
        IsMinOn (stageEffectivePotential s.toStageValleySpec)
          (Metric.closedBall s.center s.radius) w.minimizer ∧
        (∀ y ∈ Metric.closedBall s.center s.radius,
          stageEffectivePotential s.toStageValleySpec y =
            stageEffectivePotential s.toStageValleySpec w.minimizer → y = w.minimizer)) ∧
      (‖w.minimizer - s.center‖ ≤
          s.gradientBound /
            (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature) ∧
        (s.backgroundGradient w.minimizer -
          (s.gain * s.presenceGain) • s.meanFieldGradient w.minimizer = 0) ∧
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
          (finiteGoal_nonempty_of_conditionalGoalEntropy_pos μ mass hinput_entropy_positive) =
            conditionalGoalEntropy μ mass ∧
        0 < finiteGoalActionGeneratedJoint_directCMIScore
          μ mass hmass_meas hmass_nonneg_ae hmass_sum_one_ae action haction_meas
          (finiteGoal_nonempty_of_conditionalGoalEntropy_pos μ mass hinput_entropy_positive) ∧
        (∀ᵐ x ∂μ, ∀ g, 0 < mass x g → goalAbstraction g ∈ D.branch)) := by
  have hstage := meanField_stage_theorem21_four_conclusions s D μ mass action
    goalAbstraction haction_meas hgoals_in_branch hmass_nonneg_ae
    hmass_sum_one_ae hinjective_ae hmass_meas hinput_entropy_positive
    branchRepresentation hbranchRepresentation_injective
    hbranchRepresentation_monotone hbranch_eq_image hsymbolSupport_eq_image
    hbranch_top hbranch_lub
  rcases hstage with ⟨w, hminimum, hdisplacement, horbit, _hfiniteInformation⟩
  have hdirect := finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy
    μ mass hmass_meas hmass_nonneg_ae hmass_sum_one_ae action haction_meas
    hinjective_ae hinput_entropy_positive
  refine ⟨w, hminimum, hdisplacement, horbit, ?_⟩
  exact ⟨hdirect.1, hdirect.2, hgoals_in_branch⟩

end Tomabechi.Theorem22

#print axioms Tomabechi.Theorem19_22.finiteGoal_nonempty_of_conditionalGoalEntropy_pos
#print axioms Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_isProbability
#print axioms Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_fst
#print axioms Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_goalMarginal
#print axioms Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_priorKernel_ae_eq
#print axioms Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_directPriorEntropy_eq
#print axioms Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_directCMIScore
#print axioms Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy
#print axioms Tomabechi.Theorem22.meanField_stage_theorem21_four_conclusions_directKL
