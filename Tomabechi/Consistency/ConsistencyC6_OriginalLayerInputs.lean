import Tomabechi.Consistency.ConsistencyC6_EntropyInputs

/-!
# C6：同じ完全状態上の定理15 A1/A3/A4

原文の層添字は自然数の実数像で、物理層0と正層n+1を区別する。
物理層の観測にはMの物理観測を採用し、正層列挙へは入れない。
状態領域・射影は完全状態上で固定し、共通束の頂点を実数添字へ写さない。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Consistency.C2
open Tomabechi.Consistency.ConsistencyC1
open MeasureTheory

/-- 原文の全層観測。物理層0は同じ収支の物理観測、正層aは正層列挙a-1。 -/
def ModelSignature.originalEntropy (M : ModelSignature) (a : ℕ) (z : CompleteState) : ℝ :=
  if a = 0 then M.physicalObservation z else M.layerObservation (a - 1) z

/-- O04–O06の全層入力。A2/A5/A6′/A7はEntropyBalanceInputsと組み合わせる。 -/
structure OriginalLayerInputs (M : ModelSignature) : Prop where
  carrier_countable : originalLayerIndexSet.Countable
  carrier_nonnegative : originalLayerIndexSet ⊆ Set.Ici (0 : ℝ)
  physical_zero_mem : (0 : ℝ) ∈ originalLayerIndexSet
  positive_indices : ∀ n : PositiveLayer, originalPositiveRealIndex n ∈ originalLayerIndexSet
  all_positive_indices : ∀ r : ℝ, r ∈ originalLayerIndexSet → 0 < r →
    ∃ n : PositiveLayer, r = originalPositiveRealIndex n
  domain_measurable : ∀ _a : ℕ, MeasurableSet (Set.univ : Set CompleteState)
  observation_measurable : ∀ a : ℕ, Measurable (M.originalEntropy a)
  physical_observation : ∀ z, M.originalEntropy 0 z = M.physicalObservation z
  positive_observation : ∀ n z,
    M.originalEntropy (originalPositiveIndex n) z = M.layerObservation n z
  trajectory_measurable : Measurable (fun t : Set.Ici (0 : ℝ) => M.completePath t.1)
  direct_sum_measurable : Measurable
    (fun t : Set.Ici (0 : ℝ) => fun _a : ℕ => M.completePath t.1)
  projection_measurable : ∀ α β : ℕ, ∀ h : β ≤ α, Measurable (originalProjection α β h)
  projection_reflexive : ∀ α z, originalProjection α α le_rfl z = z
  projection_compose : ∀ α β γ : ℕ, ∀ h₁ : β ≤ α, ∀ h₂ : γ ≤ β, ∀ z,
    originalProjection β γ h₂ (originalProjection α β h₁ z) =
      originalProjection α γ (h₂.trans h₁) z
  coarse_graining : ∀ α β : ℕ, 0 < α → 0 < β → ∀ h : β < α, ∀ z,
    M.originalEntropy β (originalProject α β h z) ≥ M.originalEntropy α z ∧
    (M.originalEntropy β (originalProject α β h z) = M.originalEntropy α z →
      ∃ y, originalProject α β h y = z)

/-- 元段の完全pathを、全実数連続なC1積分軌道の認知射影へ、非負時間域で結ぶ。
物理座標は同じ状態の収支式から回収する。新しい時計は追加しない。 -/
theorem commonModel_completePath_measurable :
    Measurable (fun t : Set.Ici (0 : ℝ) => commonModel.completePath t.1) := by
  let q : ℝ → ℝ := fun t => c1ControlledState 1 0 0 c3A7StitchedC1Gain t
  have hqcont : Continuous q := by
    change Continuous (fun t => 1 + c1ControlledOrbit (0 - 1) 0 c3A7StitchedC1Gain t)
    exact continuous_const.add (c1ControlledOrbit_continuous _ _ _)
  have hq : Measurable (fun t : Set.Ici (0 : ℝ) => q t.1) :=
    hqcont.measurable.comp measurable_subtype_coe
  have heq : (fun t : Set.Ici (0 : ℝ) => commonModel.completePath t.1) =
      fun t => (q t.1, 3 * t.1 - (q t.1) ^ 2) := by
    funext t
    have hc := c3A7StitchedC1Gain_matches_global_C1_trajectory t.1 t.2
    have hs := c3A7StitchedTrajectory_entropyObserved t.1
    apply Prod.ext
    · exact hc.symm
    · change (c3A7StitchedTrajectory t.1).2 = 3 * t.1 - (q t.1) ^ 2
      change (c3A7StitchedTrajectory t.1).2 +
        (cognitiveCoordinate (c3A7StitchedTrajectory t.1)) ^ 2 = 3 * t.1 at hs
      change q t.1 = cognitiveCoordinate (c3A7StitchedTrajectory t.1) at hc
      rw [← hc] at hs
      linarith
  rw [heq]
  exact hq.prodMk ((measurable_const.mul measurable_subtype_coe).sub (hq.pow_const 2))

/-- 全層可測性と原文射影条件を同じcommonModelの観測/完全pathで構成する。 -/
theorem commonModel_originalLayerInputs : OriginalLayerInputs commonModel := by
  refine {
    carrier_countable := c6Theorem15LayerAdapter.carrier_countable
    carrier_nonnegative := c6Theorem15LayerAdapter.carrier_nonnegative
    physical_zero_mem := c6Theorem15LayerAdapter.physical_zero_mem
    positive_indices := c6Theorem15LayerAdapter.positive_layer_mem
    all_positive_indices := c6Theorem15LayerAdapter.every_positive_index_is_positive_layer
    domain_measurable := fun _ => MeasurableSet.univ
    observation_measurable := ?_
    physical_observation := by intro z; simp [ModelSignature.originalEntropy]
    positive_observation := ?_
    trajectory_measurable := commonModel_completePath_measurable
    direct_sum_measurable := Measurable.of_eval (fun _ => commonModel_completePath_measurable)
    projection_measurable := originalProjection_measurable
    projection_reflexive := originalProjection_reflexive
    projection_compose := originalProjection_compose
    coarse_graining := ?_ }
  · intro a
    by_cases ha : a = 0
    · subst a
      change Measurable (fun z : CompleteState => if (0 : ℕ) = 0 then z.2 else _)
      simp only [↓reduceIte]
      exact measurable_snd
    · change Measurable (fun z : CompleteState =>
        if a = 0 then physicalEntropy z else layerEntropy (a - 1) z)
      simp only [ha, ↓reduceIte]
      exact measurable_const.add (measurable_fst.pow_const 2)
  · intro n z
    simp [ModelSignature.originalEntropy, originalPositiveIndex]
  · intro α β hα hβ h z
    constructor
    · simp [ModelSignature.originalEntropy, Nat.ne_of_gt hα, Nat.ne_of_gt hβ,
        commonModel, layerEntropy, originalProject]
    · intro _
      exact ⟨z, rfl⟩

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.commonModel_originalLayerInputs
