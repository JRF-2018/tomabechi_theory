import Theorem1
import Theorem2
import Theorem3
import Theorem4

/-!
# H-flow adapters for Theorems 1 and 4

These interfaces construct the policy trajectory and its time-indexed
reachable sets from one `ClosedLoopPolicyFlow`. The Lyapunov regularity,
descent, target nonemptiness, and error-bound hypotheses remain explicit.
-/

namespace Tomabechi.Theorem1

open MeasureTheory Filter
open scoped Topology

/-- Theorem 1 with both the evaluated orbit and its reachable target generated
by one selected policy flow. Forward invariance is retained as an explicit
source condition; finite-horizon optimality alone does not supply it. -/
theorem theorem1_policy_flow_reachable_tcz_distance_tendsto_zero
    {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ClosedLoopPolicyFlow E U) (initialSet : Set E)
    (x₀ : E) (hx₀ : x₀ ∈ initialSet) (V₀ : E → ℝ → ℝ)
    (θ c C t₀ : ℝ)
    (hTCZ_nonempty : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      {y | y ∈ closedLoopReachableSet
        (policyFlowReachableAt F initialSet t₀) ∧ V₀ y s ≤ θ}.Nonempty)
    (hresidual_ac : ∀ T, t₀ ≤ T →
      AbsolutelyContinuousOnInterval
        (fun s => residual1 (V₀ (F.flow t₀ x₀ s) s) θ) t₀ T)
    (hdecay_ae : ∀ T, t₀ ≤ T →
      ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
        deriv (fun r => residual1 (V₀ (F.flow t₀ x₀ r) r) θ) s ≤
          -2 * c * residual1 (V₀ (F.flow t₀ x₀ s) s) θ)
    (herror : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (Metric.infDist (F.flow t₀ x₀ s)
        {y | y ∈ closedLoopReachableSet
          (policyFlowReachableAt F initialSet t₀) ∧ V₀ y s ≤ θ}) ^ 2 ≤
          C * residual1 (V₀ (F.flow t₀ x₀ s) s) θ)
    (_hforwardInvariant : ∀ y ∈ closedLoopReachableSet
        (policyFlowReachableAt F initialSet t₀),
      ∀ t, t₀ ≤ t → F.flow t₀ y t ∈ closedLoopReachableSet
        (policyFlowReachableAt F initialSet t₀))
    (ht₀ : 0 ≤ t₀) (hc : 0 < c) (hC : 0 < C) :
    (∀ t, t₀ ≤ t → F.flow t₀ x₀ t ∈ closedLoopReachableSet
      (policyFlowReachableAt F initialSet t₀)) ∧
    (∀ t, t₀ ≤ t → Metric.infDist (F.flow t₀ x₀ t)
      {y | y ∈ closedLoopReachableSet
        (policyFlowReachableAt F initialSet t₀) ∧ V₀ y t ≤ θ} ≤
      Real.sqrt (C * residual1 (V₀ (F.flow t₀ x₀ t₀) t₀) θ) *
        Real.exp (-c * (t - t₀))) ∧
    Filter.Tendsto (fun t => Metric.infDist (F.flow t₀ x₀ t)
      {y | y ∈ closedLoopReachableSet
        (policyFlowReachableAt F initialSet t₀) ∧ V₀ y t ≤ θ}) atTop (𝓝 0) := by
  apply theorem1_reachable_tcz_distance_tendsto_zero
    (fun t => F.flow t₀ x₀ t) (policyFlowReachableAt F initialSet t₀)
    V₀ θ c C t₀
    (fun t ht => mem_policyFlowReachableAt_of_flow F initialSet t₀ t x₀ hx₀ ht)
    hTCZ_nonempty hresidual_ac hdecay_ae herror ht₀ hc hC

end Tomabechi.Theorem1

namespace Tomabechi.Theorem4

open MeasureTheory Filter
open scoped Topology

/-- Theorem 4 with the same selected policy flow generating the evaluated
orbit and the reachable set used in its weighted TCZ. -/
theorem weighted_policy_flow_reachable_tcz_distance_tendsto_zero
    {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Tomabechi.Theorem1.ClosedLoopPolicyFlow E U)
    (initialSet : Set E) (x₀ : E) (hx₀ : x₀ ∈ initialSet)
    (V₀ P Q : E → ℝ → ℝ) (κ θP c C t₀ : ℝ)
    (hTCZ_nonempty : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (weightedTCZ (Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀))
        V₀ P Q κ θP s).Nonempty)
    (hresidual_ac : ∀ T, t₀ ≤ T →
      AbsolutelyContinuousOnInterval
        (fun s => residual4 (V₀ (F.flow t₀ x₀ s) s) (P (F.flow t₀ x₀ s) s)
          (Q (F.flow t₀ x₀ s) s) κ θP) t₀ T)
    (hdecay_ae : ∀ T, t₀ ≤ T →
      ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
        deriv (fun r => residual4 (V₀ (F.flow t₀ x₀ r) r)
          (P (F.flow t₀ x₀ r) r) (Q (F.flow t₀ x₀ r) r) κ θP) s ≤
          -2 * c * residual4 (V₀ (F.flow t₀ x₀ s) s)
            (P (F.flow t₀ x₀ s) s) (Q (F.flow t₀ x₀ s) s) κ θP)
    (herror : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (Metric.infDist (F.flow t₀ x₀ s)
        (weightedTCZ (Tomabechi.Theorem1.closedLoopReachableSet
          (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀))
          V₀ P Q κ θP s)) ^ 2 ≤
          C * residual4 (V₀ (F.flow t₀ x₀ s) s) (P (F.flow t₀ x₀ s) s)
            (Q (F.flow t₀ x₀ s) s) κ θP)
    (_hforwardInvariant : ∀ y ∈ Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀),
      ∀ t, t₀ ≤ t → F.flow t₀ y t ∈ Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀))
    (ht₀ : 0 ≤ t₀) (hc : 0 < c) (hC : 0 < C) :
    (∀ t, t₀ ≤ t → F.flow t₀ x₀ t ∈ Tomabechi.Theorem1.closedLoopReachableSet
      (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀)) ∧
    (∀ t, t₀ ≤ t → Metric.infDist (F.flow t₀ x₀ t)
      (weightedTCZ (Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀))
        V₀ P Q κ θP t) ≤
      Real.sqrt (C * residual4 (V₀ (F.flow t₀ x₀ t₀) t₀)
        (P (F.flow t₀ x₀ t₀) t₀) (Q (F.flow t₀ x₀ t₀) t₀) κ θP) *
        Real.exp (-c * (t - t₀))) ∧
    Filter.Tendsto (fun t => Metric.infDist (F.flow t₀ x₀ t)
      (weightedTCZ (Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀))
        V₀ P Q κ θP t)) atTop (𝓝 0) := by
  apply weighted_reachable_tcz_distance_tendsto_zero
    (fun t => F.flow t₀ x₀ t) (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀)
    V₀ P Q κ θP c C t₀
    (fun t ht => Tomabechi.Theorem1.mem_policyFlowReachableAt_of_flow
      F initialSet t₀ t x₀ hx₀ ht)
    hTCZ_nonempty hresidual_ac hdecay_ae herror ht₀ hc hC

end Tomabechi.Theorem4

namespace Tomabechi.Theorem2.StatePairResidualSystem

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
variable (D : StatePairResidualSystem I E)

/-- Theorem 2 adapter: the joint closed-loop policy flow generates both the
multi-agent trajectory and the reachable set used by the shared TCZ. -/
theorem policy_flow_reachable_quantitative_conclusion
    {U : Type*} [∀ i, PseudoMetricSpace (D.State i)]
    [NormedAddCommGroup (∀ i, D.State i)] [NormedSpace ℝ (∀ i, D.State i)]
    (F : Tomabechi.Theorem1.ClosedLoopPolicyFlow (∀ i, D.State i) U)
    (initialSet : Set (∀ i, D.State i)) (x₀ : ∀ i, D.State i)
    (hx₀ : x₀ ∈ initialSet)
    (connected : ∀ i j, Relation.ReflTransGen
      (fun a b => ∃ e, ((D.endpoint e).1 = a ∧ (D.endpoint e).2 = b) ∨
        ((D.endpoint e).1 = b ∧ (D.endpoint e).2 = a)) i j)
    (c C t₀ : ℝ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 ≤ t₀)
    (hshared_nonempty : ∀ s ≥ t₀,
      (D.sharedTCZ (Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀)) s).Nonempty)
    (hphi_ac : ∀ T ≥ t₀, AbsolutelyContinuousOnInterval
      (fun s => D.potential (F.flow t₀ x₀ s) s) t₀ T)
    (hphi_decay : ∀ T ≥ t₀, ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc t₀ T),
      deriv (fun s => D.potential (F.flow t₀ x₀ s) s) s ≤
        -2 * c * D.potential (F.flow t₀ x₀ s) s)
    (hdistance_error : ∀ s ≥ t₀,
      (Metric.infDist (F.flow t₀ x₀ s)
        (D.sharedTCZ (Tomabechi.Theorem1.closedLoopReachableSet
          (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀)) s)) ^ 2 ≤
        C * D.potential (F.flow t₀ x₀ s) s)
    (_hforwardInvariant : ∀ y ∈ Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀),
      ∀ t, t₀ ≤ t → F.flow t₀ y t ∈ Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀)) :
    ReachableStatePairConclusion D
      (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀)
      (F.flow t₀ x₀) connected c C t₀ := by
  apply D.theorem2_reachable_state_pair_quantitative_conclusion
    (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀)
    (F.flow t₀ x₀) connected c C t₀ hc hC ht₀
    (fun s hs => Tomabechi.Theorem1.mem_policyFlowReachableAt_of_flow
      F initialSet t₀ s x₀ hx₀ hs)
    hshared_nonempty hphi_ac hphi_decay hdistance_error

end Tomabechi.Theorem2.StatePairResidualSystem

namespace Tomabechi.Theorem3.AbstractSharedSystem

variable {I Lattice : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [CompleteLattice Lattice]
variable {m : ℕ} (D : AbstractSharedSystem I Lattice m)

/-- Theorem 3/P2 adapter: one joint policy flow supplies the product-state
orbit and the reachable set; the same explicit state map connects that orbit
to the Theorem 2 residual system. -/
theorem policy_flow_reachable_state_tcz_from_statePairSystem
    {G U : Type*} [Fintype G] [DecidableEq G]
    (D₂ : Tomabechi.Theorem2.StatePairResidualSystem I G)
    (stateMap : ∀ i, D.State i → D₂.State i)
    [∀ i, PseudoMetricSpace (D.State i)]
    [NormedAddCommGroup (∀ i, D.State i)] [NormedSpace ℝ (∀ i, D.State i)]
    (F : Tomabechi.Theorem1.ClosedLoopPolicyFlow (∀ i, D.State i) U)
    (initialSet : Set (∀ i, D.State i)) (x₀ : ∀ i, D.State i)
    (hx₀ : x₀ ∈ initialSet) (η : I → ℝ) (i : I) (c C t₀ : ℝ)
    (hη : ∀ j, 0 < η j) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 ≤ t₀)
    (hTCZ_nonempty : ∀ s ≥ t₀,
      (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀))
        (D.statePairSharedPotential D₂ stateMap) η s).Nonempty)
    (hpotential_ac : ∀ T ≥ t₀,
      AbsolutelyContinuousOnInterval
        (fun s => D.statePotential (D.statePairSharedPotential D₂ stateMap) η
          (F.flow t₀ x₀ s) s) t₀ T)
    (hpotential_decay : ∀ T ≥ t₀,
      ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc t₀ T),
        deriv (fun r => D.statePotential (D.statePairSharedPotential D₂ stateMap) η
          (F.flow t₀ x₀ r) r) s ≤
          -2 * c * D.statePotential (D.statePairSharedPotential D₂ stateMap) η
            (F.flow t₀ x₀ s) s)
    (hdistance_error : ∀ s ≥ t₀,
      (Metric.infDist (F.flow t₀ x₀ s)
        (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet
          (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀))
          (D.statePairSharedPotential D₂ stateMap) η s)) ^ 2 ≤
        C * D.statePotential (D.statePairSharedPotential D₂ stateMap) η
          (F.flow t₀ x₀ s) s)
    (_hforwardInvariant : ∀ y ∈ Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀),
      ∀ t, t₀ ≤ t → F.flow t₀ y t ∈ Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀)) :
    (∀ s ≥ t₀, F.flow t₀ x₀ s ∈ Tomabechi.Theorem1.closedLoopReachableSet
      (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀)) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist (F.flow t₀ x₀ t)
        (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet
          (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀))
          (D.statePairSharedPotential D₂ stateMap) η t) ≤
          Real.sqrt (C * D.statePotential (D.statePairSharedPotential D₂ stateMap) η
            (F.flow t₀ x₀ t₀) t₀) * Real.exp (-c * (t - t₀)) ∧
      euclideanCoordinateNorm
        (D.ι (D.abstraction i ((F.flow t₀ x₀ t) i)) - D.ι (D.lub)) ≤
          Real.sqrt (D.statePotential (D.statePairSharedPotential D₂ stateMap) η
            (F.flow t₀ x₀ t₀) t₀ / η i) * Real.exp (-c * (t - t₀))) ∧
    (Filter.Tendsto (fun s => Metric.infDist (F.flow t₀ x₀ s)
        (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet
          (Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀))
          (D.statePairSharedPotential D₂ stateMap) η s)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun s => euclideanCoordinateNorm
          (D.ι (D.abstraction i ((F.flow t₀ x₀ s) i)) - D.ι (D.lub)))
        Filter.atTop (nhds 0)) := by
  let reachable := Tomabechi.Theorem1.policyFlowReachableAt F initialSet t₀
  let trajectory : ∀ j, ℝ → D.State j := fun j s => (F.flow t₀ x₀ s) j
  have hresult := D.theorem3_reachable_state_tcz_from_statePairSystem
    D₂ stateMap reachable trajectory η i c C t₀ hη hc hC ht₀
    (fun s hs => by
      simpa [trajectory] using Tomabechi.Theorem1.mem_policyFlowReachableAt_of_flow
        F initialSet t₀ s x₀ hx₀ hs)
    hTCZ_nonempty hpotential_ac hpotential_decay hdistance_error
  simpa [reachable, trajectory] using hresult

end Tomabechi.Theorem3.AbstractSharedSystem

#print axioms Tomabechi.Theorem1.theorem1_policy_flow_reachable_tcz_distance_tendsto_zero
#print axioms Tomabechi.Theorem4.weighted_policy_flow_reachable_tcz_distance_tendsto_zero
#print axioms Tomabechi.Theorem2.StatePairResidualSystem.policy_flow_reachable_quantitative_conclusion
#print axioms Tomabechi.Theorem3.AbstractSharedSystem.policy_flow_reachable_state_tcz_from_statePairSystem
