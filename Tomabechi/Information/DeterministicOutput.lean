import Tomabechi.Information.FiniteMeasureEntropy
import Tomabechi.Dynamics.MeanFieldReconstruction

/-! 定理21の有限ゴール・決定論的出力情報結論。-/

namespace Tomabechi.Theorem21

/-- Residual conditional entropy density after observing a deterministic
action at one input. -/
noncomputable def residualGoalEntropyAt
    {G Y : Type*} [Fintype G] (mass : G → ℝ) (action : G → Y) : ℝ := by
  classical
  exact ∑ g : G, finiteConditionalEntropyTerm (mass g)
    (∑ g' : G, if action g' = action g then mass g' else 0)

/-- If a deterministic action distinguishes all positive-mass goals, then the
conditional entropy remaining after observing it is zero at that input. -/
theorem residualGoalEntropyAt_eq_zero_of_injective_on_support
    {G Y : Type*} [Fintype G]
    (mass : G → ℝ) (action : G → Y)
    (hmass_nonneg : ∀ g, 0 ≤ mass g)
    (hinjective : ∀ g, 0 < mass g → ∀ g', action g' = action g → g' = g) :
    residualGoalEntropyAt mass action = 0 := by
  classical
  unfold residualGoalEntropyAt
  apply Finset.sum_eq_zero
  intro g _
  by_cases hzero : mass g = 0
  · simp [finiteConditionalEntropyTerm, hzero]
  · have hpos : 0 < mass g := lt_of_le_of_ne (hmass_nonneg g) (Ne.symm hzero)
    have hfiber :
        (∑ g' : G, if action g' = action g then mass g' else 0) = mass g := by
      rw [Finset.sum_eq_single g]
      · simp
      · intro g' _ hne
        by_cases hact : action g' = action g
        · have heq := hinjective g hpos g' hact
          exact (hne heq).elim
        · simp [hact]
      · intro hnot
        exact (hnot (Finset.mem_univ g)).elim
    simp [finiteConditionalEntropyTerm, hzero, hfiber, div_self (ne_of_gt hpos)]

/-- Conditional entropy remaining after a deterministic action, integrated
over a general input distribution. -/
noncomputable def residualGoalEntropy
    {X G Y : Type*} [MeasurableSpace X] [Fintype G]
    (μ : MeasureTheory.Measure X) (mass : X → G → ℝ)
    (action : X → G → Y) : ℝ :=
  ∫ x, residualGoalEntropyAt (mass x) (action x) ∂μ

/-- Conditional mutual information for finite goals and deterministic output,
defined as `H(G|X) - H(G|X,Y)` over the input measure.
日本語監査注：ここでの残余エントロピーは出力の等値ファイバーから計算する。
Yの可測構造を使うKL型CMIとは別定義であり、この宣言自体は同定を主張しない。
確定H-info（標準Borel出力）下での同じ生成lawへの接続は
`Tomabechi.Theorem22.meanField_stage_theorem21_four_conclusions_directKL`
（`Tomabechi/Information/MeanFieldDirectCMI.lean`）を参照。 -/
noncomputable def conditionalGoalMutualInformation
    {X G Y : Type*} [MeasurableSpace X] [Fintype G]
    (μ : MeasureTheory.Measure X) (mass : X → G → ℝ)
    (action : X → G → Y) : ℝ :=
  conditionalGoalEntropy μ mass - residualGoalEntropy μ mass action

/-- The information-capacity conclusion with a general measurable input
space. The goal space is finite, while the action type is unrestricted. The
input-entropy integrability and conditional-probability assumptions make the
input entropy a genuine finite conditional entropy. The residual entropy is
proved zero almost everywhere and needs no separate integrability premise. -/
theorem theorem21_general_input_information_capacity
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype G]
    (μ : MeasureTheory.Measure X) (mass : X → G → ℝ)
    (action : X → G → Y)
    (_haction_meas : ∀ g, Measurable (fun x => action x g))
    (hmass_nonneg_ae : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (_hmass_sum_one_ae : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (hinjective_ae : ∀ᵐ x ∂μ, ∀ g, 0 < mass x g →
      ∀ g', action x g' = action x g → g' = g)
    (hmass_meas : ∀ g, MeasureTheory.AEStronglyMeasurable
      (fun x => mass x g) μ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (hinput_entropy_positive : 0 < conditionalGoalEntropy μ mass) :
    conditionalGoalMutualInformation μ mass action =
        conditionalGoalEntropy μ mass ∧
      0 < conditionalGoalMutualInformation μ mass action := by
  have hinput_meas := conditionalGoalEntropyAt_aestronglyMeasurable μ mass
    hmass_meas
  have _hinput_integrable := conditionalGoalEntropy_integrable_of_ae_probability
    μ mass hinput_meas hmass_nonneg_ae _hmass_sum_one_ae
  have hresidual_ae :
      (fun x => residualGoalEntropyAt (mass x) (action x)) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hmass_nonneg_ae, hinjective_ae] with x hnonneg hinj
    exact residualGoalEntropyAt_eq_zero_of_injective_on_support
      (mass x) (action x) hnonneg hinj
  have hresidual_eq : residualGoalEntropy μ mass action = 0 := by
    unfold residualGoalEntropy
    rw [MeasureTheory.integral_congr_ae hresidual_ae]
    simp
  constructor
  · simp [conditionalGoalMutualInformation, hresidual_eq]
  · simpa [conditionalGoalMutualInformation, hresidual_eq] using
      hinput_entropy_positive

/-- The information conclusion of published Theorem 21 with its biased-branch
restriction made explicit. Positive-mass goals lie in the branch carried by
the order-theoretic support context, while a deterministic action separates
those goals almost everywhere in the input. -/
theorem theorem21_branch_constrained_information_capacity
    {L X G Y : Type*} [CompleteLattice L] [MeasurableSpace X]
    [MeasurableSpace Y] [Fintype G]
    (D : Theorem21BranchContext L)
    (μ : MeasureTheory.Measure X) (mass : X → G → ℝ)
    (action : X → G → Y) (goalAbstraction : G → L)
    (_haction_meas : ∀ g, Measurable (fun x => action x g))
    (hgoals_in_branch : ∀ᵐ x ∂μ, ∀ g, 0 < mass x g →
      goalAbstraction g ∈ D.branch)
    (hmass_nonneg_ae : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hmass_sum_one_ae : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (hinjective_ae : ∀ᵐ x ∂μ, ∀ g, 0 < mass x g →
      ∀ g', action x g' = action x g → g' = g)
    (hmass_meas : ∀ g, MeasureTheory.AEStronglyMeasurable
      (fun x => mass x g) μ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (hinput_entropy_positive : 0 < conditionalGoalEntropy μ mass) :
    conditionalGoalMutualInformation μ mass action =
        conditionalGoalEntropy μ mass ∧
      0 < conditionalGoalMutualInformation μ mass action ∧
      (∀ᵐ x ∂μ, ∀ g, 0 < mass x g → goalAbstraction g ∈ D.branch) := by
  have hcapacity := theorem21_general_input_information_capacity μ mass action
    _haction_meas
    hmass_nonneg_ae hmass_sum_one_ae hinjective_ae hmass_meas
    hinput_entropy_positive
  exact ⟨hcapacity.1, hcapacity.2, hgoals_in_branch⟩

/-- Finite-input branch-capacity specialization. The normalized weights build
both the discrete probability measure and the order-theoretic support context;
the information-capacity result then uses that same measure. -/
theorem theorem21_finite_input_branch_capacity
    {A L G Y : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [CompleteLattice L] [Fintype G]
    [MeasurableSpace Y]
    (weight : A → ℝ) (embedding : A → L) (branch : Set L)
    (hweight : ∀ a, 0 ≤ weight a) (hnorm : ∑ a, weight a = 1)
    (htop : (⊤ : L) ∉ branch)
    (hpositive_atoms_in_branch : ∀ a, 0 < weight a → embedding a ∈ branch)
    (hbranch_sSup : ∀ s : Set L,
      (∀ x ∈ s, x ∈ branch) → sSup s ∈ branch)
    (mass : A → G → ℝ) (action : A → G → Y) (goalAbstraction : G → L)
    (_haction_meas : ∀ g, Measurable (fun a => action a g))
    (hgoals_in_branch : ∀ᵐ a ∂finiteReconstructionMeasure weight,
      ∀ g, 0 < mass a g → goalAbstraction g ∈ branch)
    (hmass_nonneg_ae : ∀ᵐ a ∂finiteReconstructionMeasure weight,
      ∀ g, 0 ≤ mass a g)
    (hmass_sum_one_ae : ∀ᵐ a ∂finiteReconstructionMeasure weight,
      ∑ g : G, mass a g = 1)
    (hinjective_ae : ∀ᵐ a ∂finiteReconstructionMeasure weight,
      ∀ g, 0 < mass a g → ∀ g', action a g' = action a g → g' = g)
    (hmass_meas : ∀ g, MeasureTheory.AEStronglyMeasurable
      (fun a => mass a g) (finiteReconstructionMeasure weight))
    (hinput_entropy_positive :
      0 < conditionalGoalEntropy (finiteReconstructionMeasure weight) mass) :
    conditionalGoalMutualInformation (finiteReconstructionMeasure weight)
        mass action =
        conditionalGoalEntropy (finiteReconstructionMeasure weight) mass ∧
      0 < conditionalGoalMutualInformation (finiteReconstructionMeasure weight)
        mass action ∧
      (∀ᵐ a ∂finiteReconstructionMeasure weight,
        ∀ g, 0 < mass a g → goalAbstraction g ∈ branch) := by
  let D : Theorem21BranchContext L := finiteWeightedBranchContext
    weight embedding branch hweight hnorm htop hpositive_atoms_in_branch
    hbranch_sSup
  let μ : MeasureTheory.Measure A := finiteReconstructionMeasure weight
  letI : MeasureTheory.IsProbabilityMeasure μ :=
    finite_reconstruction_measure_isProbabilityMeasure weight hweight hnorm
  exact theorem21_branch_constrained_information_capacity D μ mass action
    goalAbstraction _haction_meas hgoals_in_branch hmass_nonneg_ae hmass_sum_one_ae
    hinjective_ae hmass_meas hinput_entropy_positive


end Tomabechi.Theorem21
