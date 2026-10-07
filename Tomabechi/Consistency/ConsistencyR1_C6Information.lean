import Tomabechi.Consistency.ConsistencyC6_ModelSignature
import Tomabechi.Consistency.ConsistencyC6_EntropyInputs
import Tomabechi.Consistency.ConsistencyR1_C1Information

/-!
# R1: 共通束上の情報lawと同じSCM実験を接続

共通束の底は物理情報lawへ、それ以外は正情報を持つ旧Nat層へ送る。
旧正層アドレスでは層番号を保ち、底以外の新しい点では最小の正層を使う。
実験の情報・自己過程marginalとSCM介入jointを、同じModelSignatureから読む。
-/

noncomputable section

namespace Tomabechi.Consistency.R1

open MeasureTheory
open Filter
open scoped Topology
open Tomabechi.Consistency.C6
open Tomabechi.Consistency.ConsistencyC1Consensus

/-- C2 positive entropy layer `p` occupies the same CommonConcept address as
the corresponding C3/C6 upper information layer. The physical address zero
remains separate. -/
def commonConceptPositiveEntropyAddress (p : C2.PositiveLayer) : CommonConcept :=
  layerAddressEmbedding (entropyLayerAddress p)

@[simp] theorem entropyLayerAddress_eq_succ (p : C2.PositiveLayer) :
    entropyLayerAddress p = ((p + 1 : ℕ) : WithTop ℕ) := by
  simp [entropyLayerAddress, C2.originalPositiveIndex]

theorem commonConceptPositiveEntropyAddress_law_eq
    (M : ModelSignature) (h : CommonDataCouplings M) (p : C2.PositiveLayer) :
    commonConceptInformationLaw (commonConceptPositiveEntropyAddress p) =
      M.informationLaw (p + 1) := by
  rw [commonConceptPositiveEntropyAddress, entropyLayerAddress_eq_succ,
    commonConceptInformationLaw_recovers_upper_address]
  exact (h.stage_information p).symm

theorem commonConceptPositiveEntropyAddress_weight_eq
    (M : ModelSignature) (h : CommonDataCouplings M) (p : C2.PositiveLayer) :
    commonEntropyWeight (entropyLayerAddress p) = M.weight p := by
  rw [h.layer_weight]
  exact commonEntropyWeight_matches_C2 p

theorem commonConceptPositiveEntropyAddress_ne_bottom (p : C2.PositiveLayer) :
    commonConceptPositiveEntropyAddress p ≠ ⊥ := by
  rw [commonConceptPositiveEntropyAddress, entropyLayerAddress_eq_succ]
  exact layerAddress_succ_ne_bottom p

/-- 底は物理lawの番号0へ、非底は正情報を持つ有限番号へ送る。 -/
def commonConceptInformationIndex (a : CommonConcept) : ℕ :=
  if a = ⊥ then 0 else max 1 ((layerProjection a).untopD 1)

/-- One CommonConcept-indexed observation on the original complete state.
Bottom reads the physical coordinate; positive addresses read their C2 layer. -/
def commonConceptCompleteStateObservation (M : ModelSignature)
    (a : CommonConcept) (z : C2.CompleteState) : ℝ :=
  if a = ⊥ then M.physicalObservation z
  else M.layerObservation (commonConceptInformationIndex a - 1) z

@[simp] theorem commonConceptInformationIndex_bottom :
    commonConceptInformationIndex (⊥ : CommonConcept) = 0 := by
  simp [commonConceptInformationIndex]

theorem commonConceptInformationIndex_positive_of_ne_bottom
    {a : CommonConcept} (ha : a ≠ ⊥) :
    0 < commonConceptInformationIndex a := by
  simp [commonConceptInformationIndex, ha]

@[simp] theorem commonConceptInformationIndex_old_zero :
    commonConceptInformationIndex
      (layerAddressEmbedding (0 : WithTop ℕ)) = 0 := by
  rw [layerAddress_zero_eq_bottom]
  simp

@[simp] theorem commonConceptInformationIndex_old_positive (n : ℕ) :
    commonConceptInformationIndex
      (layerAddressEmbedding ((n + 1 : ℕ) : WithTop ℕ)) = n + 1 := by
  have hne := layerAddress_succ_ne_bottom n
  unfold commonConceptInformationIndex
  rw [if_neg hne]
  change max 1 (WithTop.untopD 1 (layerProjection (layerAddress ((n + 1 : ℕ) : WithTop ℕ)))) = n + 1
  rw [layerProjection_layerAddress]
  change max 1 (n + 1) = n + 1
  exact Nat.max_eq_right (by omega)

@[simp] theorem commonConceptInformationIndex_top :
    commonConceptInformationIndex (⊤ : CommonConcept) = 1 := by
  have hproj : layerProjection (⊤ : CommonConcept) = ⊤ := by
    rw [← layerProjection_layerAddress (⊤ : WithTop ℕ), layerAddress_top]
  have hne : (⊤ : CommonConcept) ≠ ⊥ := by simp
  simp [commonConceptInformationIndex, hne, hproj]

theorem commonConceptCompleteStateObservation_positive_address
    (M : ModelSignature) (p : C2.PositiveLayer) (z : C2.CompleteState) :
    commonConceptCompleteStateObservation M
        (commonConceptPositiveEntropyAddress p) z = M.layerObservation p z := by
  have hindex : commonConceptInformationIndex
      (commonConceptPositiveEntropyAddress p) = p + 1 := by
    rw [commonConceptPositiveEntropyAddress, entropyLayerAddress_eq_succ]
    exact commonConceptInformationIndex_old_positive p
  have hbottom := commonConceptPositiveEntropyAddress_ne_bottom p
  simp [commonConceptCompleteStateObservation, hindex, hbottom]

theorem commonConceptCompleteStateObservation_bottom
    (M : ModelSignature) (z : C2.CompleteState) :
    commonConceptCompleteStateObservation M ⊥ z = M.physicalObservation z := by
  simp [commonConceptCompleteStateObservation]

/-- Reindexing every positive entropy observation by its CommonConcept
address preserves the full 15→23 entropy balance along the shared complete
path. -/
theorem commonConceptEntropyBalanceAlongPath (t : ℝ) :
    commonModel.physicalObservation (commonModel.completePath t) +
      ∑' p : C2.PositiveLayer,
        commonEntropyWeight (entropyLayerAddress p) *
          commonConceptCompleteStateObservation commonModel
            (commonConceptPositiveEntropyAddress p) (commonModel.completePath t) =
      1 + 3 * t := by
  simp_rw [commonConceptPositiveEntropyAddress_weight_eq commonModel
      commonModel_couplings,
    commonConceptCompleteStateObservation_positive_address]
  exact commonModel_couplings.entropy_observation t

theorem commonConceptPositiveLayerPathObservation_eq
    (M : ModelSignature) (p : C2.PositiveLayer) :
    (fun t : ℝ => commonConceptCompleteStateObservation M
      (commonConceptPositiveEntropyAddress p) (M.completePath t)) =
    (fun t : ℝ => M.layerObservation p (M.completePath t)) := by
  funext t
  exact commonConceptCompleteStateObservation_positive_address M p (M.completePath t)

theorem commonConceptPositiveLayerPath_absolutelyContinuous
    (M : ModelSignature) (h : EntropyBalanceInputs M)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (p : C2.PositiveLayer) :
    AbsolutelyContinuousOnInterval
      (fun t => commonConceptCompleteStateObservation M
        (commonConceptPositiveEntropyAddress p) (M.completePath t)) a b := by
  rw [commonConceptPositiveLayerPathObservation_eq]
  exact h.layer_ac a b ha hab p

theorem commonConceptPhysicalPath_absolutelyContinuous
    (M : ModelSignature) (h : EntropyBalanceInputs M)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    AbsolutelyContinuousOnInterval
      (fun t => commonConceptCompleteStateObservation M ⊥ (M.completePath t)) a b := by
  rw [show (fun t : ℝ => commonConceptCompleteStateObservation M ⊥ (M.completePath t)) =
      fun t => M.physicalObservation (M.completePath t) from by
        funext t
        exact commonConceptCompleteStateObservation_bottom M (M.completePath t)]
  exact h.physical_ac a b ha hab

theorem commonConceptPositiveLayerPath_endpoint_summable
    (M : ModelSignature) (hc : CommonDataCouplings M) (h : EntropyBalanceInputs M)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    Summable (fun p : C2.PositiveLayer => commonEntropyWeight (entropyLayerAddress p) *
      commonConceptCompleteStateObservation M (commonConceptPositiveEntropyAddress p)
        (M.completePath a)) ∧
    Summable (fun p : C2.PositiveLayer => commonEntropyWeight (entropyLayerAddress p) *
      commonConceptCompleteStateObservation M (commonConceptPositiveEntropyAddress p)
        (M.completePath b)) := by
  have hleft : (fun p : C2.PositiveLayer => commonEntropyWeight (entropyLayerAddress p) *
      commonConceptCompleteStateObservation M (commonConceptPositiveEntropyAddress p)
        (M.completePath a)) = fun p => M.weight p * M.layerObservation p (M.completePath a) := by
    funext p
    rw [commonConceptPositiveEntropyAddress_weight_eq M hc p,
      commonConceptCompleteStateObservation_positive_address]
  have hright : (fun p : C2.PositiveLayer => commonEntropyWeight (entropyLayerAddress p) *
      commonConceptCompleteStateObservation M (commonConceptPositiveEntropyAddress p)
        (M.completePath b)) = fun p => M.weight p * M.layerObservation p (M.completePath b) := by
    funext p
    rw [commonConceptPositiveEntropyAddress_weight_eq M hc p,
      commonConceptCompleteStateObservation_positive_address]
  rw [hleft, hright]
  exact h.endpoint_summable a b ha hab

theorem commonConceptPositiveLayerPath_all_finite_ui
    (M : ModelSignature) (hc : CommonDataCouplings M) (h : EntropyBalanceInputs M)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    UniformIntegrable
      (fun (s : Finset C2.PositiveLayer) t => ∑ p ∈ s,
        commonEntropyWeight (entropyLayerAddress p) *
          deriv (fun u => commonConceptCompleteStateObservation M
            (commonConceptPositiveEntropyAddress p) (M.completePath u)) t)
      1 (volume.restrict (Set.uIoc a b)) := by
  have hsum : (fun (s : Finset C2.PositiveLayer) t => ∑ p ∈ s,
      commonEntropyWeight (entropyLayerAddress p) *
        deriv (fun u => commonConceptCompleteStateObservation M
          (commonConceptPositiveEntropyAddress p) (M.completePath u)) t) =
      fun s t => ∑ p ∈ s, M.weight p *
        deriv (fun u => M.layerObservation p (M.completePath u)) t := by
    funext s t
    apply Finset.sum_congr rfl
    intro p hp
    rw [commonConceptPositiveEntropyAddress_weight_eq M hc p]
    have hderiv := congrArg (fun f : ℝ → ℝ => deriv f t)
      (commonConceptPositiveLayerPathObservation_eq M p)
    rw [hderiv]
  rw [hsum]
  exact h.all_finite_ui a b ha hab

theorem commonConceptPositiveLayerPath_prefix_tendsto
    (M : ModelSignature) (hc : CommonDataCouplings M) (h : EntropyBalanceInputs M)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      Tendsto (fun k => ∑ i : Fin k,
        commonEntropyWeight
          (entropyLayerAddress
            (Tomabechi.Theorem15_23.countableLayerEnumeration C2.PositiveLayer i.val)) *
          deriv (fun u => commonConceptCompleteStateObservation M
            (commonConceptPositiveEntropyAddress
              (Tomabechi.Theorem15_23.countableLayerEnumeration C2.PositiveLayer i.val))
            (M.completePath u)) t) atTop
        (𝓝 (∑' p : C2.PositiveLayer, commonEntropyWeight (entropyLayerAddress p) *
          deriv (fun u => commonConceptCompleteStateObservation M
            (commonConceptPositiveEntropyAddress p) (M.completePath u)) t)) := by
  have hterm (p : C2.PositiveLayer) (t : ℝ) :
      commonEntropyWeight (entropyLayerAddress p) *
        deriv (fun u => commonConceptCompleteStateObservation M
          (commonConceptPositiveEntropyAddress p) (M.completePath u)) t =
      M.weight p * deriv (fun u => M.layerObservation p (M.completePath u)) t := by
    rw [commonConceptPositiveEntropyAddress_weight_eq M hc p]
    exact congrArg (fun f : ℝ → ℝ => M.weight p * deriv f t)
      (commonConceptPositiveLayerPathObservation_eq M p)
  have hprefix (t : ℝ) :
      (fun k => ∑ i : Fin k,
        commonEntropyWeight
          (entropyLayerAddress
            (Tomabechi.Theorem15_23.countableLayerEnumeration C2.PositiveLayer i.val)) *
          deriv (fun u => commonConceptCompleteStateObservation M
            (commonConceptPositiveEntropyAddress
              (Tomabechi.Theorem15_23.countableLayerEnumeration C2.PositiveLayer i.val))
            (M.completePath u)) t) =
      fun k => ∑ i : Fin k,
        M.weight (Tomabechi.Theorem15_23.countableLayerEnumeration C2.PositiveLayer i.val) *
          deriv (fun u => M.layerObservation
            (Tomabechi.Theorem15_23.countableLayerEnumeration C2.PositiveLayer i.val)
            (M.completePath u)) t := by
    funext k
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm _ t
  have hsum (t : ℝ) :
      (∑' p : C2.PositiveLayer, commonEntropyWeight (entropyLayerAddress p) *
        deriv (fun u => commonConceptCompleteStateObservation M
          (commonConceptPositiveEntropyAddress p) (M.completePath u)) t) =
      ∑' p : C2.PositiveLayer, M.weight p *
        deriv (fun u => M.layerObservation p (M.completePath u)) t := by
    apply tsum_congr
    intro p
    exact hterm p t
  filter_upwards [h.prefix_tendsto a b ha hab] with t ht
  rw [hprefix t, hsum t]
  exact ht

theorem commonConceptA7_balance
    (M : ModelSignature) (hc : CommonDataCouplings M) (h : EntropyBalanceInputs M)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      deriv (fun u => commonConceptCompleteStateObservation M ⊥ (M.completePath u)) t =
        -(∑' p : C2.PositiveLayer, commonEntropyWeight (entropyLayerAddress p) *
          deriv (fun u => commonConceptCompleteStateObservation M
            (commonConceptPositiveEntropyAddress p) (M.completePath u)) t) + 3 := by
  have hphysical :
      deriv (fun u => commonConceptCompleteStateObservation M ⊥ (M.completePath u)) =
        deriv (fun u => M.physicalObservation (M.completePath u)) := by
    congr 1
    funext u
    exact commonConceptCompleteStateObservation_bottom M (M.completePath u)
  have hsum : ∀ t,
      (∑' p : C2.PositiveLayer, commonEntropyWeight (entropyLayerAddress p) *
        deriv (fun u => commonConceptCompleteStateObservation M
          (commonConceptPositiveEntropyAddress p) (M.completePath u)) t) =
      ∑' p : C2.PositiveLayer, M.weight p *
        deriv (fun u => M.layerObservation p (M.completePath u)) t := by
    intro t
    apply tsum_congr
    intro p
    rw [commonConceptPositiveEntropyAddress_weight_eq M hc p]
    exact congrArg (fun f : ℝ → ℝ => M.weight p * deriv f t)
      (commonConceptPositiveLayerPathObservation_eq M p)
  filter_upwards [h.a7_balance a b ha hab] with t ht
  rw [hphysical, hsum t]
  exact ht

/-- 共通概念点を読むとき、ModelSignatureの情報lawが新しいlawと一致する。 -/
theorem commonConceptInformationLaw_eq_modelLaw
    (M : ModelSignature) (hM : CommonDataCouplings M) (a : CommonConcept) :
    M.informationLaw (commonConceptInformationIndex a) =
      commonConceptInformationLaw a := by
  by_cases ha : a = ⊥
  · subst a
    rw [commonConceptInformationIndex_bottom, commonConceptInformationLaw_bottom,
      hM.physical_information]
  · have hk := commonConceptInformationIndex_positive_of_ne_bottom ha
    have hsucc : commonConceptInformationIndex a =
        commonConceptInformationIndex a - 1 + 1 := by omega
    rw [hsucc, hM.stage_information (commonConceptInformationIndex a - 1),
      commonConceptInformationLaw_of_ne_bottom ha]

/-- Reindexed input sample law: one original SCM exogenous law times the
information law belonging to this common-concept point. -/
def commonConceptExperimentInputLaw (M : ModelSignature) (a : CommonConcept) :
    Measure C6ExperimentInput :=
  M.scm.model.scm.exogenousLaw.toMeasure.prod
    (M.informationLaw (commonConceptInformationIndex a))

/-- The experiment output is exactly the existing ModelSignature experiment
at the address selected above. -/
def commonConceptExperimentLaw (M : ModelSignature) (d h : Bool)
    (a : CommonConcept) (x : AgentState) (T t : ℝ) : Measure C6ExperimentObservation :=
  M.experimentLaw d h (commonConceptInformationIndex a) x T t

/-- New-lattice SCM bridge, parameterized by the very same model couplings and
its intervention-joint invariant. -/
structure CommonConceptInformationExperimentBridge (M : ModelSignature) : Prop where
  law_matches_model : ∀ a,
    M.informationLaw (commonConceptInformationIndex a) = commonConceptInformationLaw a
  input_exogenous_marginal : ∀ a,
    (commonConceptExperimentInputLaw M a).map Prod.fst =
      M.scm.model.scm.exogenousLaw.toMeasure
  input_information_marginal : ∀ a,
    (commonConceptExperimentInputLaw M a).map Prod.snd =
      commonConceptInformationLaw a
  experiment_information_marginal : ∀ d h a x T t,
    (commonConceptExperimentLaw M d h a x T t).map (fun z => z.1.2) =
      commonConceptInformationLaw a
  experiment_self_marginal : ∀ d h a x T t,
    (commonConceptExperimentLaw M d h a x T t).map (fun z => z.2.1) =
      (M.scm.model.scm.exogenousLaw.toMeasure).map
        (M.baselineSelfObservation d h
          (some (commonConceptInformationIndex a)))
  experiment_state_cost_marginal : ∀ d h a x T t,
    (commonConceptExperimentLaw M d h a x T t).map (fun z => z.2.2) =
      (commonConceptExperimentInputLaw M a).map (fun w =>
        let policy := M.informationPolicy w.2.2.2
        let state := M.data.trajectory (some (commonConceptInformationIndex a))
          policy x T t
        (state, M.data.runningCost (some (commonConceptInformationIndex a)) policy state t))
  intervention_joint_invariant : ∀ d (a : CommonConcept) h s,
    M.scm.model.scm.exogenousLaw.map
      (fun u => (M.scm.model.scm.stateEquation d
          (some (commonConceptInformationIndex a)) h u,
        M.scm.model.scm.outputEquation d
          (some (commonConceptInformationIndex a)) h u s)) =
    M.scm.model.scm.exogenousLaw.map
      (fun u => (M.scm.model.scm.stateEquation d
          (some (commonConceptInformationIndex a)) h u,
        M.scm.model.scm.outputEquation d
          (some (commonConceptInformationIndex a)) h u
          (M.scm.model.scm.candidateVariable d
            (some (commonConceptInformationIndex a)) u)))
  old_physical_address :
    commonConceptInformationIndex
      (layerAddressEmbedding (0 : WithTop ℕ)) = 0
  old_positive_addresses : ∀ n,
    commonConceptInformationIndex
      (layerAddressEmbedding ((n + 1 : ℕ) : WithTop ℕ)) = n + 1

theorem commonConceptInformationExperimentBridge_of_couplings
    (M : ModelSignature) (hM : CommonDataCouplings M)
    (hinv : ∀ d a h s,
      M.scm.model.scm.exogenousLaw.map
        (fun u => (M.scm.model.scm.stateEquation d a h u,
          M.scm.model.scm.outputEquation d a h u s)) =
      M.scm.model.scm.exogenousLaw.map
        (fun u => (M.scm.model.scm.stateEquation d a h u,
          M.scm.model.scm.outputEquation d a h u
            (M.scm.model.scm.candidateVariable d a u)))) :
    CommonConceptInformationExperimentBridge M := by
  refine {
    law_matches_model := commonConceptInformationLaw_eq_modelLaw M hM
    input_exogenous_marginal := ?_
    input_information_marginal := ?_
    experiment_information_marginal := ?_
    experiment_self_marginal := ?_
    experiment_state_cost_marginal := ?_
    intervention_joint_invariant := ?_
    old_physical_address := commonConceptInformationIndex_old_zero
    old_positive_addresses := commonConceptInformationIndex_old_positive }
  · intro a
    letI := commonConceptInformationLaw_isProbability a
    unfold commonConceptExperimentInputLaw
    rw [Measure.map_fst_prod]
    have hmass : (M.informationLaw (commonConceptInformationIndex a)) Set.univ = 1 := by
      rw [commonConceptInformationLaw_eq_modelLaw M hM a]
      simp
    rw [hmass]
    simp
  · intro a
    unfold commonConceptExperimentInputLaw
    rw [Measure.map_snd_prod, commonConceptInformationLaw_eq_modelLaw M hM]
    simp
  · intro d h a x T t
    rw [commonConceptExperimentLaw, hM.experiment_information]
    exact commonConceptInformationLaw_eq_modelLaw M hM a
  · intro d h a x T t
    rw [commonConceptExperimentLaw, hM.experiment_self]
  · intro d h a x T t
    change ((M.experimentInputLaw (commonConceptInformationIndex a)).map
      (M.experimentObservation d h (commonConceptInformationIndex a) x T t)).map
        (fun z => z.2.2) = _
    rw [Measure.map_map
      (show Measurable (fun z : C6ExperimentObservation => z.2.2) from
        measurable_snd.comp measurable_snd)
      (measurable_of_finite _)]
    rfl
  · intro d a h s
    exact hinv d (some (commonConceptInformationIndex a)) h s

end Tomabechi.Consistency.R1

end
