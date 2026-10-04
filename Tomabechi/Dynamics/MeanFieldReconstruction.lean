import Theorem1

/-! # 定理21の分岐支持と有限再構成平均場

旧 `Theorem21.lean` の分岐支持コンテキスト、有限再構成測度、有限平均場核の積分・微分API。
強凸最適化とODE存在論から独立させ、宣言namespace・名前と証明本文を保持する。
-/

namespace Tomabechi.Theorem21

open RealInnerProductSpace
open Filter
open scoped Topology NNReal ContDiff

/-! ### Finite-support reconstruction-kernel specialization

The paper writes the reconstruction kernel as an integral against a
probability measure. The following algebraic lemmas cover a finite support
measure, represented by nonnegative weights summing to one. They do not assert
differentiation under a general integral. -/

/-! ### Order-theoretic support context

The published Theorem 21 also locates the symbolic support's least upper
bound inside a proper information branch. The context below formalizes those
order assumptions. Both a general-measure constructor and a finite discrete
constructor connect the order support to an actual measure support. -/

/-- Order-theoretic data attached to Theorem 21's biased information branch. -/
structure Theorem21BranchContext (L : Type*) [CompleteLattice L] where
  branch : Set L
  symbolSupport : Set L
  support_nonempty : symbolSupport.Nonempty
  top_not_in_branch : (⊤ : L) ∉ branch
  support_lub : IsLUB symbolSupport (sSup symbolSupport)
  address_in_branch : sSup symbolSupport ∈ branch

namespace Theorem21BranchContext

variable {L : Type*} [CompleteLattice L] (D : Theorem21BranchContext L)

/-- Construct the branch context from the actual topological support of a
probability measure. Nonemptiness and containment of the support in the
available branch are explicit; closure of the branch under suprema then puts
the support address inside the branch. -/
def fromMeasureSupport
    [TopologicalSpace L] [MeasurableSpace L]
    (μ : MeasureTheory.Measure L) [MeasureTheory.IsProbabilityMeasure μ]
    (branch : Set L) (htop : (⊤ : L) ∉ branch)
    (hsupport_nonempty : μ.support.Nonempty)
    (hsupport_branch : ∀ x ∈ μ.support, x ∈ branch)
    (hbranch_sSup : ∀ s : Set L,
      (∀ x ∈ s, x ∈ branch) → sSup s ∈ branch) :
    Theorem21BranchContext L :=
  { branch := branch
    symbolSupport := μ.support
    support_nonempty := hsupport_nonempty
    top_not_in_branch := htop
    support_lub := isLUB_sSup _
    address_in_branch := hbranch_sSup μ.support hsupport_branch }

/-- A probability measure on a hereditarily Lindelöf space has nonempty
topological support. -/
theorem probability_measure_support_nonempty
    {L : Type*} [TopologicalSpace L] [MeasurableSpace L]
    [HereditarilyLindelofSpace L]
    (μ : MeasureTheory.Measure L) [MeasureTheory.IsProbabilityMeasure μ] :
    μ.support.Nonempty := by
  apply MeasureTheory.Measure.nonempty_support
  apply (MeasureTheory.Measure.measure_univ_pos).mp
  rw [MeasureTheory.isProbabilityMeasure_iff.mp inferInstance]
  norm_num

/-- Specialize the support context to a probability measure. On a
hereditarily Lindelöf state space, support nonemptiness follows from total mass
one. -/
def fromProbabilityMeasure
    {L : Type*} [CompleteLattice L] [TopologicalSpace L]
    [MeasurableSpace L] [HereditarilyLindelofSpace L]
    (μ : MeasureTheory.Measure L) [MeasureTheory.IsProbabilityMeasure μ]
    (branch : Set L) (htop : (⊤ : L) ∉ branch)
    (hsupport_branch : ∀ x ∈ μ.support, x ∈ branch)
    (hbranch_sSup : ∀ s : Set L,
      (∀ x ∈ s, x ∈ branch) → sSup s ∈ branch) :
    Theorem21BranchContext L :=
  fromMeasureSupport μ branch htop
    (probability_measure_support_nonempty μ) hsupport_branch hbranch_sSup

/-- Construct the order context when the symbol distribution is defined on
the branch itself. Its support is mapped from the subtype into the ambient
complete lattice, so support containment in the branch is automatic. -/
def fromBranchMeasure
    {L : Type*} [CompleteLattice L] [TopologicalSpace L]
    [MeasurableSpace L] (branch : Set L)
    (μ : MeasureTheory.Measure (↥branch))
    [MeasureTheory.IsProbabilityMeasure μ]
    [HereditarilyLindelofSpace (↥branch)]
    (htop : (⊤ : L) ∉ branch)
    (hbranch_sSup : ∀ s : Set L,
      (∀ x ∈ s, x ∈ branch) → sSup s ∈ branch) :
    Theorem21BranchContext L :=
  { branch := branch
    symbolSupport := Subtype.val '' μ.support
    support_nonempty := by
      obtain ⟨a, ha⟩ := probability_measure_support_nonempty μ
      exact ⟨a.1, ⟨a, ha, rfl⟩⟩
    top_not_in_branch := htop
    support_lub := isLUB_sSup _
    address_in_branch := hbranch_sSup _ (by
      intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      exact a.2) }

/-- Construct the branch context from a measure on the branch when the
support LUB is known to belong to the branch. This states exactly the order
condition used by Theorem 21 and does not require the branch to be closed
under suprema of unrelated subsets. -/
def fromBranchMeasureOfLUB
    {L : Type*} [CompleteLattice L] [TopologicalSpace L]
    [MeasurableSpace L] (branch : Set L)
    (μ : MeasureTheory.Measure (↥branch))
    [MeasureTheory.IsProbabilityMeasure μ]
    (htop : (⊤ : L) ∉ branch)
    (hsupport_nonempty : μ.support.Nonempty)
    (haddress : sSup (Subtype.val '' μ.support) ∈ branch) :
    Theorem21BranchContext L :=
  { branch := branch
    symbolSupport := Subtype.val '' μ.support
    support_nonempty := by
      obtain ⟨a, ha⟩ := hsupport_nonempty
      exact ⟨a.1, ⟨a, ha, rfl⟩⟩
    top_not_in_branch := htop
    support_lub := isLUB_sSup _
    address_in_branch := haddress }

/-- Excluding the top element makes the available branch a proper subset of
the full abstraction lattice. -/
theorem branch_isProperSubset : D.branch ⊂ (Set.univ : Set L) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro hfull
  exact D.top_not_in_branch (hfull (Set.mem_univ (⊤ : L)))

/-- The support LUB is strictly below the global top because it belongs to the
branch, which excludes that top. -/
theorem address_ne_top : sSup D.symbolSupport ≠ (⊤ : L) := by
  intro htop
  apply D.top_not_in_branch
  rw [← htop]
  exact D.address_in_branch

/-- The support LUB is below every upper bound for that support. -/
theorem address_le_of_support_le (u : L)
    (hu : ∀ a ∈ D.symbolSupport, a ≤ u) : sSup D.symbolSupport ≤ u :=
  D.support_lub.2 hu

end Theorem21BranchContext

/-- A finite weighted reconstruction kernel. -/
def finiteReconstructionKernel {A E : Type*} [Fintype A]
    (weight : A → ℝ) (kernel : A → E → ℝ) (x : E) : ℝ :=
  ∑ a, weight a * kernel a x

/-- The algebraic support of a finite weighted input distribution consists
of the atoms with strictly positive mass. -/
def finitePositiveWeightSupport {A : Type*} (weight : A → ℝ) : Set A :=
  {a | 0 < weight a}

/-- A normalized nonnegative finite distribution has nonempty algebraic
support. -/
theorem finite_positive_weight_support_nonempty
    {A : Type*} [Fintype A] (weight : A → ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hnorm : ∑ a, weight a = 1) :
    (finitePositiveWeightSupport weight).Nonempty := by
  by_contra h
  have hzero : ∀ a, weight a = 0 := by
    intro a
    have hnot : ¬ 0 < weight a := by
      intro ha
      exact h ⟨a, ha⟩
    linarith [hweight a]
  have hsum : ∑ a, weight a = 0 := by simp [hzero]
  linarith

/-- Build the order-theoretic branch context from a finite probability
distribution and an abstraction map. The support nonemptiness and LUB facts
are derived; membership of the resulting address in the branch remains the
substantive branch hypothesis. -/
def finiteWeightedBranchContext
    {A L : Type*} [Fintype A] [CompleteLattice L]
    (weight : A → ℝ) (embedding : A → L) (branch : Set L)
    (hweight : ∀ a, 0 ≤ weight a) (hnorm : ∑ a, weight a = 1)
    (htop : (⊤ : L) ∉ branch)
    (hpositive_atoms_in_branch : ∀ a, 0 < weight a → embedding a ∈ branch)
    (hbranch_sSup : ∀ s : Set L,
      (∀ x ∈ s, x ∈ branch) → sSup s ∈ branch) :
    Theorem21BranchContext L :=
  { branch := branch
    symbolSupport := embedding '' finitePositiveWeightSupport weight
    support_nonempty := by
      obtain ⟨a, ha⟩ := finite_positive_weight_support_nonempty weight hweight hnorm
      exact ⟨embedding a, Set.mem_image_of_mem embedding ha⟩
    top_not_in_branch := htop
    support_lub := isLUB_sSup _
    address_in_branch := hbranch_sSup _ (by
      intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      exact hpositive_atoms_in_branch a ha) }

/-- Finite discrete probability input represented by its weighted Dirac
masses. -/
noncomputable def finiteReconstructionMeasure {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (weight : A → ℝ) :
    MeasureTheory.Measure A :=
  MeasureTheory.Measure.sum (fun a : A =>
    ENNReal.ofReal (weight a) • MeasureTheory.Measure.dirac a)

/-- Normalized nonnegative weights make the finite discrete input measure a
probability measure. -/
theorem finite_reconstruction_measure_isProbabilityMeasure
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (weight : A → ℝ) (hweight : ∀ a, 0 ≤ weight a)
    (hnorm : ∑ a, weight a = 1) :
    MeasureTheory.IsProbabilityMeasure (finiteReconstructionMeasure weight) := by
  rw [MeasureTheory.isProbabilityMeasure_iff]
  rw [finiteReconstructionMeasure, MeasureTheory.Measure.sum_fintype]
  simp [MeasureTheory.Measure.dirac_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hweight _), hnorm]
  simp

/-- In the finite Dirac mixture, the mass of an atom is its assigned weight. -/
theorem finite_reconstruction_measure_apply_singleton
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (weight : A → ℝ) (hweight : ∀ a, 0 ≤ weight a) (a : A) :
    finiteReconstructionMeasure weight {a} = ENNReal.ofReal (weight a) := by
  classical
  rw [finiteReconstructionMeasure,
    MeasureTheory.Measure.sum_apply _ (MeasurableSet.singleton a)]
  simp [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply,
    ENNReal.smul_def, Set.indicator_apply, Set.mem_singleton_iff,
    tsum_fintype, Finset.sum_ite_eq']

/-- For a finite discrete input space, the topological support of the
reconstruction measure is exactly the set of atoms with positive weight. -/
theorem finite_reconstruction_measure_support_eq_positive_weight_support
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A]
    (weight : A → ℝ) (hweight : ∀ a, 0 ≤ weight a) :
    (finiteReconstructionMeasure weight).support = finitePositiveWeightSupport weight := by
  ext a
  rw [MeasureTheory.Measure.mem_support_iff_forall]
  constructor
  · intro h
    have hsingle := h {a} (by simp [nhds_discrete])
    rw [finite_reconstruction_measure_apply_singleton weight hweight a] at hsingle
    exact ENNReal.ofReal_pos.mp hsingle
  · intro ha U hU
    have hau : a ∈ U := by simpa [nhds_discrete] using hU
    have hsubset : ({a} : Set A) ⊆ U := by
      intro x hx
      simpa using hx ▸ hau
    have hsingle : 0 < finiteReconstructionMeasure weight {a} := by
      rw [finite_reconstruction_measure_apply_singleton weight hweight a]
      exact ENNReal.ofReal_pos.mpr ha
    exact lt_of_lt_of_le hsingle (MeasureTheory.measure_mono hsubset)

/-- Pushing the finite measure support through an abstraction map gives the
same ordered support used by `finiteWeightedBranchContext`. -/
theorem finite_reconstruction_order_support_eq
    {A L : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A]
    (weight : A → ℝ) (embedding : A → L)
    (hweight : ∀ a, 0 ≤ weight a) :
    embedding '' (finiteReconstructionMeasure weight).support =
      embedding '' finitePositiveWeightSupport weight := by
  rw [finite_reconstruction_measure_support_eq_positive_weight_support
    weight hweight]

/-- Integrating over the finite discrete input measure is exactly the weighted
finite reconstruction sum. -/
theorem integral_finite_reconstruction_measure
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (weight : A → ℝ) (hweight : ∀ a, 0 ≤ weight a) (kernel : A → ℝ) :
    ∫ a, kernel a ∂finiteReconstructionMeasure weight =
      ∑ a, weight a * kernel a := by
  rw [finiteReconstructionMeasure, MeasureTheory.integral_sum_dirac]
  · simp [ENNReal.toReal_ofReal (hweight _), Finset.mul_sum]
  · intro a
    exact ENNReal.ofReal_ne_top

/-- The finite Dirac-mixture integral identity for finite-dimensional
vector-valued functions. This extends the scalar reconstruction identity to
the gradient and Hessian fields. -/
theorem integral_finite_reconstruction_measure_vector
    {A F : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (weight : A → ℝ) (hweight : ∀ a, 0 ≤ weight a) (f : A → F) :
    ∫ a, f a ∂finiteReconstructionMeasure weight = ∑ a, weight a • f a := by
  rw [finiteReconstructionMeasure, MeasureTheory.integral_sum_dirac]
  · simp [ENNReal.toReal_ofReal (hweight _)]
  · intro a
    exact ENNReal.ofReal_ne_top

/-- Differentiate a general-measure reconstruction integral under an explicit
integrable domination hypothesis. The neighborhood and derivative bound are
uniform in the integration variable almost everywhere; these hypotheses are
the measure-theoretic conditions needed to pass from component gradients to
the gradient of the integral. -/
theorem integral_reconstruction_kernel_hasFDerivAt
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : MeasureTheory.Measure X) (kernel : E → X → ℝ)
    (gradKernel : E → X → E) (x₀ : E) (s : Set E) (bound : X → ℝ)
    (hs : s ∈ 𝓝 x₀)
    (hkernel_meas : ∀ᶠ x in 𝓝 x₀,
      MeasureTheory.AEStronglyMeasurable (kernel x) μ)
    (hkernel_integrable : MeasureTheory.Integrable (kernel x₀) μ)
    (hgrad_meas : MeasureTheory.AEStronglyMeasurable
      (fun a => innerSL ℝ (gradKernel x₀ a)) μ)
    (hgrad_bound : ∀ᵐ a ∂μ, ∀ x ∈ s,
      ‖gradKernel x a‖ ≤ bound a)
    (hbound_integrable : MeasureTheory.Integrable bound μ)
    (hcomponent_deriv : ∀ᵐ a ∂μ, ∀ x ∈ s,
      HasFDerivAt (fun y => kernel y a) (innerSL ℝ (gradKernel x a)) x)
    (hgrad_integrable : MeasureTheory.Integrable (gradKernel x₀) μ) :
    HasFDerivAt (fun x => ∫ a, kernel x a ∂μ)
      (innerSL ℝ (∫ a, gradKernel x₀ a ∂μ)) x₀ := by
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := μ) (s := s) hs hkernel_meas hkernel_integrable hgrad_meas
    (h_bound := by
      filter_upwards [hgrad_bound] with a ha x hx
      rw [innerSL_apply_norm]
      exact ha x hx)
    hbound_integrable hcomponent_deriv
  have hcommute :
      (∫ a, innerSL ℝ (gradKernel x₀ a) ∂μ) =
        innerSL ℝ (∫ a, gradKernel x₀ a ∂μ) := by
    exact (innerSL ℝ).integral_comp_comm hgrad_integrable
  rw [hcommute] at hderiv
  exact hderiv

/-- The same dominated-differentiation theorem applies to the gradient field:
if its component Hessians have an integrable local bound, the gradient of the
integrated reconstruction kernel has the integrated Hessian as derivative. -/
theorem integral_reconstruction_gradient_hasFDerivAt
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (μ : MeasureTheory.Measure X) (gradKernel : E → X → E)
    (hessKernel : E → X → E →L[ℝ] E) (x₀ : E) (s : Set E)
    (bound : X → ℝ) (hs : s ∈ 𝓝 x₀)
    (hgrad_meas : ∀ᶠ x in 𝓝 x₀,
      MeasureTheory.AEStronglyMeasurable (gradKernel x) μ)
    (hgrad_integrable : MeasureTheory.Integrable (gradKernel x₀) μ)
    (hhess_meas : MeasureTheory.AEStronglyMeasurable (hessKernel x₀) μ)
    (hhess_bound : ∀ᵐ a ∂μ, ∀ x ∈ s,
      ‖hessKernel x a‖ ≤ bound a)
    (hbound_integrable : MeasureTheory.Integrable bound μ)
    (hcomponent_deriv : ∀ᵐ a ∂μ, ∀ x ∈ s,
      HasFDerivAt (fun y => gradKernel y a) (hessKernel x a) x) :
    HasFDerivAt (fun x => ∫ a, gradKernel x a ∂μ)
      (∫ a, hessKernel x₀ a ∂μ) x₀ :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ)
    (s := s) hs hgrad_meas hgrad_integrable hhess_meas hhess_bound
    hbound_integrable hcomponent_deriv

/-- A probability average preserves a common almost-everywhere zero gradient
and a uniform negative Hessian bound. This is the measure-valued counterpart
of the finite-mixture curvature lemma. -/
theorem probability_integral_hessian_bound
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ]
    (hessian : X → E →L[ℝ] E) (v : E) (m : ℝ)
    (hessian_integrable : MeasureTheory.Integrable hessian μ)
    (hbound : ∀ᵐ a ∂μ,
      inner ℝ (hessian a v) v ≤ -m * ‖v‖ ^ 2) :
    inner ℝ ((∫ a, hessian a ∂μ) v) v ≤ -m * ‖v‖ ^ 2 := by
  let evalV : (E →L[ℝ] E) →L[ℝ] E :=
    ContinuousLinearMap.apply ℝ E v
  have hvector_integrable : MeasureTheory.Integrable
      (fun a => hessian a v) μ := evalV.integrable_comp hessian_integrable
  have hscalar_int : MeasureTheory.Integrable
      (fun a => inner ℝ (hessian a v) v) μ := by
    have h := (innerSL ℝ v).integrable_comp hvector_integrable
    exact h.congr (Filter.Eventually.of_forall fun a => real_inner_comm _ _)
  have hmono := MeasureTheory.integral_mono_ae hscalar_int
    (MeasureTheory.integrable_const (-m * ‖v‖ ^ 2)) hbound
  have hleft : (∫ a, inner ℝ (hessian a v) v ∂μ) =
      inner ℝ ((∫ a, hessian a ∂μ) v) v := by
    calc
      (∫ a, inner ℝ (hessian a v) v ∂μ) =
          ∫ a, inner ℝ v (hessian a v) ∂μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with a
            exact real_inner_comm _ _
      _ = inner ℝ v (∫ a, hessian a v ∂μ) :=
          (innerSL ℝ v).integral_comp_comm hvector_integrable
      _ = inner ℝ v ((∫ a, hessian a ∂μ) v) := by
          rw [← ContinuousLinearMap.integral_apply hessian_integrable v]
      _ = inner ℝ ((∫ a, hessian a ∂μ) v) v := real_inner_comm _ _
  rw [hleft] at hmono
  simpa using hmono

/-- Integrating an almost-everywhere zero gradient gives a zero mean gradient. -/
theorem probability_integral_gradient_eq_zero
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : MeasureTheory.Measure X)
    (gradient : X → E) (hgradient_integrable : MeasureTheory.Integrable gradient μ)
    (hzero : ∀ᵐ a ∂μ, gradient a = 0) :
    (∫ a, gradient a ∂μ) = 0 := by
  calc
    (∫ a, gradient a ∂μ) = ∫ _a, (0 : E) ∂μ :=
      MeasureTheory.integral_congr_ae hzero
    _ = 0 := by simp

/-- Explicit pointwise package of hypotheses for differentiating a scalar
reconstruction integral with respect to its state variable. -/
def HasDominatedReconstructionKernelFDerivAt
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (μ : MeasureTheory.Measure X)
    (kernel : E → X → ℝ) (gradKernel : E → X → E) (x : E) : Prop :=
  ∃ s : Set E, ∃ bound : X → ℝ,
    s ∈ 𝓝 x ∧
    (∀ᶠ y in 𝓝 x, MeasureTheory.AEStronglyMeasurable (kernel y) μ) ∧
    MeasureTheory.Integrable (kernel x) μ ∧
    MeasureTheory.AEStronglyMeasurable
      (fun a => innerSL ℝ (gradKernel x a)) μ ∧
    (∀ᵐ a ∂μ, ∀ y ∈ s, ‖gradKernel y a‖ ≤ bound a) ∧
    MeasureTheory.Integrable bound μ ∧
    (∀ᵐ a ∂μ, ∀ y ∈ s,
      HasFDerivAt (fun z => kernel z a) (innerSL ℝ (gradKernel y a)) y) ∧
    MeasureTheory.Integrable (gradKernel x) μ

/-- Explicit pointwise package of hypotheses for differentiating an integrated
gradient field into its integrated Hessian. -/
def HasDominatedReconstructionGradientFDerivAt
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : MeasureTheory.Measure X)
    (gradKernel : E → X → E) (hessKernel : E → X → E →L[ℝ] E)
    (x : E) : Prop :=
  ∃ s : Set E, ∃ bound : X → ℝ,
    s ∈ 𝓝 x ∧
    (∀ᶠ y in 𝓝 x, MeasureTheory.AEStronglyMeasurable (gradKernel y) μ) ∧
    MeasureTheory.Integrable (gradKernel x) μ ∧
    MeasureTheory.AEStronglyMeasurable (hessKernel x) μ ∧
    (∀ᵐ a ∂μ, ∀ y ∈ s, ‖hessKernel y a‖ ≤ bound a) ∧
    MeasureTheory.Integrable bound μ ∧
    (∀ᵐ a ∂μ, ∀ y ∈ s,
      HasFDerivAt (fun z => gradKernel z a) (hessKernel y a) y)

/-- Global dominated-continuity data for the averaged reconstruction Hessian.
This is a kernel-level condition: a single integrable bound controls all
states, and almost every component Hessian is continuous in the state. -/
def HasDominatedContinuousReconstructionHessian
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (μ : MeasureTheory.Measure X) (hessKernel : E → X → E →L[ℝ] E) : Prop :=
  ∃ bound : X → ℝ,
    (∀ x, MeasureTheory.AEStronglyMeasurable (hessKernel x) μ) ∧
    (∀ x, ∀ᵐ a ∂μ, ‖hessKernel x a‖ ≤ bound a) ∧
    MeasureTheory.Integrable bound μ ∧
    (∀ᵐ a ∂μ, Continuous (fun x => hessKernel x a))

/-- A global integrable majorant and almost-everywhere continuity of the
component Hessians imply continuity of their Bochner integral. -/
theorem mean_reconstruction_hessian_continuous_of_dominated
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    [FirstCountableTopology E]
    (μ : MeasureTheory.Measure X) (hessKernel : E → X → E →L[ℝ] E)
    (hdom : HasDominatedContinuousReconstructionHessian μ hessKernel) :
    Continuous (fun x => ∫ a, hessKernel x a ∂μ) := by
  rcases hdom with ⟨bound, hmeas, hbound, hboundIntegrable, hcontinuous⟩
  exact MeasureTheory.continuous_of_dominated hmeas hbound hboundIntegrable
    hcontinuous

/-- Curvature bounds that hold for almost every reconstruction input pass
through the Bochner integral of the Hessian. -/
theorem mean_hessian_curvature_of_ae
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (hessKernel : X → E →L[ℝ] E)
    (x : E) (m : ℝ) (v : E)
    (hintegrable : MeasureTheory.Integrable (hessKernel ·) μ)
    (hcurvature : ∀ᵐ a ∂μ,
      inner ℝ (hessKernel a v) v ≤ -m * ‖v‖ ^ 2) :
    inner ℝ ((∫ a, hessKernel a ∂μ) v) v ≤ -m * ‖v‖ ^ 2 := by
  let q : (E →L[ℝ] E) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v)
  have hq (a : X) : q (hessKernel a) = inner ℝ (hessKernel a v) v := by
    simp [q, ContinuousLinearMap.comp_apply, real_inner_comm]
  have hcurvature' : ∀ᵐ a ∂μ,
      q (hessKernel a) ≤ -m * ‖v‖ ^ 2 := by
    filter_upwards [hcurvature] with a ha
    simpa [hq, real_inner_comm] using ha
  calc
    inner ℝ ((∫ a, hessKernel a ∂μ) v) v =
        q (∫ a, hessKernel a ∂μ) := by
          simp [q, ContinuousLinearMap.comp_apply, real_inner_comm]
    _ = ∫ a, q (hessKernel a) ∂μ := by
      rw [← q.integral_comp_comm hintegrable]
    _ ≤ ∫ _a : X, (-m * ‖v‖ ^ 2) ∂μ :=
      MeasureTheory.integral_mono_ae (q.integrable_comp hintegrable)
        (MeasureTheory.integrable_const _) hcurvature'
    _ = -m * ‖v‖ ^ 2 := by simp

/-- Finite input spaces admit a common integrable Hessian majorant whenever
each input Hessian is globally bounded. This constructs the dominated
continuity package used by the general-measure dynamics theorem. -/
theorem finite_input_dominated_continuous_reconstruction_hessian
    {X E : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (hessKernel : E → X → E →L[ℝ] E)
    (hmeas : ∀ x, MeasureTheory.AEStronglyMeasurable (hessKernel x) μ)
    (hcontinuous : ∀ a, Continuous (fun x => hessKernel x a))
    (hbounded : ∀ a, ∃ C : ℝ, ∀ x, ‖hessKernel x a‖ ≤ C) :
    HasDominatedContinuousReconstructionHessian μ hessKernel := by
  classical
  let C : X → ℝ := fun a => Classical.choose (hbounded a)
  have hCbound : ∀ a x, ‖hessKernel x a‖ ≤ C a := fun a x =>
    Classical.choose_spec (hbounded a) x
  have hCnonneg : ∀ a, 0 ≤ C a := by
    intro a
    have h := hCbound a 0
    exact le_trans (norm_nonneg _) h
  let bound : X → ℝ := fun _ => ∑ a, C a
  have hbound : ∀ x, ∀ᵐ a ∂μ, ‖hessKernel x a‖ ≤ bound a := by
    intro x
    filter_upwards [] with a
    dsimp [bound]
    exact le_trans (hCbound a x)
      (Finset.single_le_sum (s := Finset.univ) (fun b hb => hCnonneg b)
        (Finset.mem_univ a))
  refine ⟨bound, hmeas, hbound, ?_, ?_⟩
  · exact MeasureTheory.integrable_const _
  · filter_upwards [] with a
    exact hcontinuous a

/-- On a finite measurable input space, the integral of component Hessians is
a finite weighted sum. Componentwise continuity therefore gives continuity
of the mean Hessian without requiring a global majorant over the state space. -/
theorem finite_input_mean_reconstruction_hessian_continuous
    {X E : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : MeasureTheory.Measure X) (hessKernel : E → X → E →L[ℝ] E)
    (hintegrable : ∀ x, MeasureTheory.Integrable (hessKernel x) μ)
    (hcontinuous : ∀ a, Continuous (fun x => hessKernel x a)) :
    Continuous (fun x => ∫ a, hessKernel x a ∂μ) := by
  have hrepr : (fun x => ∫ a, hessKernel x a ∂μ) =
      fun x => ∑ a, μ.real {a} • hessKernel x a := by
    funext x
    exact MeasureTheory.integral_fintype (hintegrable x)
  rw [hrepr]
  apply continuous_finsetSum
  intro a ha
  fun_prop

/-- General-measure reconstruction kernel assumptions imply the analytic
conditions used by the state-dependent local-valley threshold theorem. The
remaining smoothness assumptions are explicit: C¹ regularity of the integral
potential and its mean gradient on the region. -/
theorem general_reconstruction_kernel_conditions
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Set E) (kernel : E → X → ℝ) (gradKernel : E → X → E)
    (hessKernel : E → X → E →L[ℝ] E) (center : E) (m : ℝ)
    (hpotentialC1 : ContDiffOn ℝ 1 (fun x => ∫ a, kernel x a ∂μ) U)
    (hmeanGradientC1 : ∀ x ∈ U,
      ContDiffAt ℝ 1 (fun y => ∫ a, gradKernel y a ∂μ) x)
    (hkernelDiff : ∀ x ∈ U,
      HasDominatedReconstructionKernelFDerivAt μ kernel gradKernel x)
    (hgradientDiff : ∀ x ∈ U,
      HasDominatedReconstructionGradientFDerivAt μ gradKernel hessKernel x)
    (hmeanCenterZero : (∫ a, gradKernel center a ∂μ) = 0)
    (hhessianIntegrable : ∀ x ∈ U,
      MeasureTheory.Integrable (hessKernel x) μ)
    (hmeanCurvature : ∀ x ∈ U, ∀ v : E,
      inner ℝ ((∫ a, hessKernel x a ∂μ) v) v ≤ -m * ‖v‖ ^ 2) :
    ContDiffOn ℝ 1 (fun x => ∫ a, kernel x a ∂μ) U ∧
    (∀ x ∈ U, HasFDerivAt (fun y => ∫ a, kernel y a ∂μ)
      (innerSL ℝ (∫ a, gradKernel x a ∂μ)) x) ∧
    (∀ x ∈ U, ContDiffAt ℝ 1 (fun y => ∫ a, gradKernel y a ∂μ) x) ∧
    (∀ x ∈ U, HasFDerivAt (fun y => ∫ a, gradKernel y a ∂μ)
      (∫ a, hessKernel x a ∂μ) x) ∧
    (∫ a, gradKernel center a ∂μ) = 0 ∧
    (∀ x ∈ U, ∀ v : E,
      inner ℝ ((∫ a, hessKernel x a ∂μ) v) v ≤ -m * ‖v‖ ^ 2) := by
  refine ⟨hpotentialC1, ?_, hmeanGradientC1, ?_, ?_, ?_⟩
  · intro x hx
    rcases hkernelDiff x hx with
      ⟨s, bound, hs, hmeas, hint, hderivMeas, hderivBound, hboundInt,
        hderiv, hgradInt⟩
    exact integral_reconstruction_kernel_hasFDerivAt μ kernel gradKernel x s
      bound hs hmeas hint hderivMeas hderivBound hboundInt hderiv hgradInt
  · intro x hx
    rcases hgradientDiff x hx with
      ⟨s, bound, hs, hmeas, hint, hderivMeas, hderivBound, hboundInt, hderiv⟩
    exact integral_reconstruction_gradient_hasFDerivAt μ gradKernel hessKernel x
      s bound hs hmeas hint hderivMeas hderivBound hboundInt hderiv
  · exact hmeanCenterZero
  · intro x hx v
    exact hmeanCurvature x hx v

/-- A continuous derivative field on a convex set with nonempty interior
upgrades pointwise Fréchet differentiability to `C¹` regularity on that set. -/
theorem contDiffOn_one_of_hasFDerivAt_continuousOn_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Set E) (f : E → F) (df : E → E →L[ℝ] F)
    (hconvex : Convex ℝ U) (hint : (interior U).Nonempty)
    (hf : ∀ x ∈ U, HasFDerivAt f (df x) x)
    (hdf : ContinuousOn df U) :
    ContDiffOn ℝ 1 f U := by
  have huniq : UniqueDiffOn ℝ U := uniqueDiffOn_convex hconvex hint
  rw [show (1 : ℕ∞ω) = 0 + 1 by rfl,
    contDiffOn_succ_iff_fderivWithin huniq]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (hf x hx).differentiableAt.differentiableWithinAt
  · simp
  · apply contDiffOn_zero.mpr
    apply hdf.congr
    intro x hx
    exact (hf x hx).hasFDerivWithinAt.fderivWithin (huniq x hx)

/-- Dominated differentiation of the integral kernel, together with `C¹`
regularity of its mean gradient, proves `C¹` regularity of the integral
potential. This removes the need to assume smoothness of the averaged
potential separately. -/
theorem integral_reconstruction_potential_contDiffOn_one
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : MeasureTheory.Measure X) (U : Set E)
    (kernel : E → X → ℝ) (gradKernel : E → X → E)
    (hmeanGradientC1 : ∀ x ∈ U,
      ContDiffAt ℝ 1 (fun y => ∫ a, gradKernel y a ∂μ) x)
    (hkernelDiff : ∀ x ∈ U,
      HasDominatedReconstructionKernelFDerivAt μ kernel gradKernel x)
    (hconvex : Convex ℝ U) (hint : (interior U).Nonempty) :
    ContDiffOn ℝ 1 (fun x => ∫ a, kernel x a ∂μ) U := by
  let df : E → E →L[ℝ] ℝ :=
    fun x => innerSL ℝ (∫ a, gradKernel x a ∂μ)
  have hderiv : ∀ x ∈ U,
      HasFDerivAt (fun y => ∫ a, kernel y a ∂μ) (df x) x := by
    intro x hx
    rcases hkernelDiff x hx with
      ⟨s, bound, hs, hkernel_meas, hkernel_integrable, hgrad_meas,
        hgrad_bound, hbound_integrable, hcomponent_deriv, hgrad_integrable⟩
    exact integral_reconstruction_kernel_hasFDerivAt μ kernel gradKernel x
      s bound hs hkernel_meas hkernel_integrable hgrad_meas hgrad_bound
      hbound_integrable hcomponent_deriv hgrad_integrable
  have hdf : ContinuousOn df U := by
    intro x hx
    exact ((innerSL ℝ).continuous.continuousAt.comp
      (hmeanGradientC1 x hx).continuousAt).continuousWithinAt
  exact contDiffOn_one_of_hasFDerivAt_continuousOn_derivative U
    (fun x => ∫ a, kernel x a ∂μ) df hconvex hint hderiv hdf

/-- The integrated Hessian is a continuous derivative field for the mean
gradient. Thus continuity of that field, together with dominated
differentiation, gives C¹ regularity of the mean gradient without assuming
that regularity separately. -/
theorem integral_reconstruction_mean_gradient_contDiffOn_one
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : MeasureTheory.Measure X) (U : Set E)
    (gradKernel : E → X → E) (hessKernel : E → X → E →L[ℝ] E)
    (hgradientDiff : ∀ x ∈ U,
      HasDominatedReconstructionGradientFDerivAt μ gradKernel hessKernel x)
    (hHessianContinuous : ContinuousOn (fun x => ∫ a, hessKernel x a ∂μ) U)
    (hconvex : Convex ℝ U) (hint : (interior U).Nonempty) :
    ContDiffOn ℝ 1 (fun x => ∫ a, gradKernel x a ∂μ) U := by
  let df : E → E →L[ℝ] E := fun x => ∫ a, hessKernel x a ∂μ
  have hderiv : ∀ x ∈ U,
      HasFDerivAt (fun y => ∫ a, gradKernel y a ∂μ) (df x) x := by
    intro x hx
    rcases hgradientDiff x hx with
      ⟨s, bound, hs, hmeas, hint', hderivMeas, hderivBound, hboundInt, hderiv'⟩
    exact integral_reconstruction_gradient_hasFDerivAt μ gradKernel hessKernel x
      s bound hs hmeas hint' hderivMeas hderivBound hboundInt hderiv'
  have hdf : ContinuousOn df U := by
    simpa only [df] using hHessianContinuous
  exact contDiffOn_one_of_hasFDerivAt_continuousOn_derivative U
    (fun x => ∫ a, gradKernel x a ∂μ) df hconvex hint hderiv hdf

/-- Finite-input continuity of the mean Hessian combines with dominated
component differentiation to give C¹ regularity of the mean gradient. This
is the finite-sum route into the local-valley regularity hypotheses. -/
theorem finite_input_mean_gradient_contDiffOn_one
    {X E : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : MeasureTheory.Measure X) (U : Set E)
    (gradKernel : E → X → E) (hessKernel : E → X → E →L[ℝ] E)
    (hgradientDiff : ∀ x ∈ U,
      HasDominatedReconstructionGradientFDerivAt μ gradKernel hessKernel x)
    (hintegrable : ∀ x, MeasureTheory.Integrable (hessKernel x) μ)
    (hcontinuous : ∀ a, Continuous (fun x => hessKernel x a))
    (hconvex : Convex ℝ U) (hint : (interior U).Nonempty) :
    ContDiffOn ℝ 1 (fun x => ∫ a, gradKernel x a ∂μ) U := by
  exact integral_reconstruction_mean_gradient_contDiffOn_one μ U gradKernel
    hessKernel hgradientDiff
    (finite_input_mean_reconstruction_hessian_continuous μ hessKernel
      hintegrable hcontinuous).continuousOn hconvex hint

/-- The gradient of a finite weighted reconstruction kernel. -/
def finiteReconstructionGradient {A E : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weight : A → ℝ) (gradKernel : A → E → E) (x : E) : E :=
  ∑ a, weight a • gradKernel a x

/-- The Hessian operator of a finite weighted reconstruction kernel. -/
def finiteReconstructionHessian {A E : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weight : A → ℝ) (hessKernel : A → E → E →L[ℝ] E) (x : E) :
    E →L[ℝ] E := ∑ a, weight a • hessKernel a x

/-- For a finite reconstruction measure, integrating the state-dependent
kernel, gradient, and Hessian gives exactly the finite weighted definitions.
Thus the finite-measure and finite-sum routes describe one model. -/
theorem finite_reconstruction_measure_kernel_gradient_hessian_eq_weighted
    {A E : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (weight : A → ℝ) (hweight : ∀ a, 0 ≤ weight a)
    (kernel : A → E → ℝ) (gradKernel : A → E → E)
    (hessKernel : A → E → E →L[ℝ] E) :
    (∀ x, ∫ a, kernel a x ∂finiteReconstructionMeasure weight =
      finiteReconstructionKernel weight kernel x) ∧
    (∀ x, ∫ a, gradKernel a x ∂finiteReconstructionMeasure weight =
      finiteReconstructionGradient weight gradKernel x) ∧
    (∀ x, ∫ a, hessKernel a x ∂finiteReconstructionMeasure weight =
      finiteReconstructionHessian weight hessKernel x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact integral_finite_reconstruction_measure weight hweight (fun a => kernel a x)
  · intro x
    simpa [finiteReconstructionGradient] using
      integral_finite_reconstruction_measure_vector weight hweight
        (fun a => gradKernel a x)
  · intro x
    simpa [finiteReconstructionHessian] using
      integral_finite_reconstruction_measure_vector weight hweight
        (fun a => hessKernel a x)

/-- Finite sums commute with differentiation, so the weighted reconstruction
kernel has the weighted component gradient as its derivative. This lemma is
restricted to a finite index type; no differentiation under a general measure
integral is claimed. -/
theorem finite_reconstruction_kernel_hasFDerivAt
    {A E : Type*} [Fintype A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weight : A → ℝ) (kernel : A → E → ℝ) (gradKernel : A → E → E)
    (x : E) (hkernel : ∀ a, HasFDerivAt (kernel a)
      (innerSL ℝ (gradKernel a x)) x) :
    HasFDerivAt (finiteReconstructionKernel weight kernel)
      (innerSL ℝ (finiteReconstructionGradient weight gradKernel x)) x := by
  unfold finiteReconstructionKernel finiteReconstructionGradient
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun a _ =>
    (hkernel a).const_mul (weight a))
  convert hsum using 1
  · funext y
    simp [finiteReconstructionKernel]
  · ext v
    simp [finiteReconstructionGradient, inner_sum, inner_smul_left, mul_comm]

/-- If each component gradient has the stated Hessian, the gradient of the
finite reconstruction kernel has the weighted Hessian. -/
theorem finite_reconstruction_gradient_hasFDerivAt
    {A E : Type*} [Fintype A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weight : A → ℝ) (gradKernel : A → E → E)
    (hessKernel : A → E → E →L[ℝ] E) (x : E)
    (hgradient : ∀ a, HasFDerivAt (gradKernel a) (hessKernel a x) x) :
    HasFDerivAt (finiteReconstructionGradient weight gradKernel)
      (finiteReconstructionHessian weight hessKernel x) x := by
  unfold finiteReconstructionGradient finiteReconstructionHessian
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun a _ =>
    (hgradient a).const_smul (weight a))
  convert hsum using 1
  · funext y
    simp [finiteReconstructionGradient]

/-- A finite mixture preserves a common zero gradient. -/
theorem finite_reconstruction_gradient_eq_zero
    {A E : Type*} [Fintype A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weight : A → ℝ) (gradKernel : A → E → E) (center : E)
    (hgrad : ∀ a, gradKernel a center = 0) :
    finiteReconstructionGradient weight gradKernel center = 0 := by
  unfold finiteReconstructionGradient
  simp [hgrad]

/-- A finite probability mixture preserves a uniform negative Hessian bound.
This is the quadratic-form part of the finite-support specialization. -/
theorem finite_reconstruction_hessian_bound
    {A E : Type*} [Fintype A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weight : A → ℝ) (hessian : A → E →L[ℝ] E) (v : E) (m : ℝ)
    (hweight : ∀ a, 0 ≤ weight a)
    (hnorm : ∑ a, weight a = 1)
    (hbound : ∀ a, inner ℝ (hessian a v) v ≤ -m * ‖v‖ ^ 2) :
    inner ℝ ((∑ a, weight a • hessian a) v) v ≤ -m * ‖v‖ ^ 2 := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun a (_ : a ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hbound a) (hweight a))
  have hleft : ∑ a, weight a * inner ℝ (hessian a v) v =
      inner ℝ ((∑ a, weight a • hessian a) v) v := by
    simp [inner_sum, sum_inner, inner_smul_left, mul_comm]
  rw [← hleft]
  calc
    ∑ a, weight a * inner ℝ (hessian a v) v ≤
        ∑ a, weight a * (-m * ‖v‖ ^ 2) := hsum
    _ = -m * ‖v‖ ^ 2 := by rw [← Finset.sum_mul, hnorm, one_mul]

/-- Package the finite-mixture facts needed by the local-valley theorem. If
each component kernel is C², its derivative is represented by the supplied
component gradient, and that gradient has the supplied Hessian, then the
finite reconstruction kernel satisfies the corresponding C¹, gradient,
Hessian, center, and uniform curvature conditions. This makes the finite
support specialization directly usable in the threshold theorem. -/
theorem finite_reconstruction_kernel_conditions
    {A E : Type*} [Fintype A] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (U : Set E) (weight : A → ℝ)
    (kernel : A → E → ℝ) (gradKernel : A → E → E)
    (hessKernel : A → E → E →L[ℝ] E) (center : E) (m : ℝ)
    (hweight : ∀ a, 0 ≤ weight a)
    (hnorm : ∑ a, weight a = 1)
    (hkernelC2 : ∀ a, ContDiffOn ℝ 2 (kernel a) U)
    (hkernelGrad : ∀ a x, x ∈ U → HasFDerivAt (kernel a)
      (innerSL ℝ (gradKernel a x)) x)
    (hgradKernelC1 : ∀ a x, x ∈ U → ContDiffAt ℝ 1 (gradKernel a) x)
    (hgradHess : ∀ a x, x ∈ U →
      HasFDerivAt (gradKernel a) (hessKernel a x) x)
    (hcenter : ∀ a, gradKernel a center = 0)
    (hbound : ∀ a x, x ∈ U → ∀ v : E,
      inner ℝ (hessKernel a x v) v ≤ -m * ‖v‖ ^ 2) :
    ContDiffOn ℝ 1 (finiteReconstructionKernel weight kernel) U ∧
    (∀ x ∈ U, HasFDerivAt (finiteReconstructionKernel weight kernel)
      (innerSL ℝ (finiteReconstructionGradient weight gradKernel x)) x) ∧
    (∀ x ∈ U, ContDiffAt ℝ 1 (finiteReconstructionGradient weight gradKernel) x) ∧
    (∀ x ∈ U, HasFDerivAt (finiteReconstructionGradient weight gradKernel)
      (finiteReconstructionHessian weight hessKernel x) x) ∧
    finiteReconstructionGradient weight gradKernel center = 0 ∧
    (∀ x ∈ U, ∀ v : E,
      inner ℝ (finiteReconstructionHessian weight hessKernel x v) v ≤
        -m * ‖v‖ ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold finiteReconstructionKernel
    have hsum : ContDiffOn ℝ 1
        (fun x => ∑ a, weight a * kernel a x) U := by
      apply ContDiffOn.sum
      intro a ha
      exact ((hkernelC2 a).of_le (by norm_num)).const_smul
        (weight a)
    simpa [smul_eq_mul] using hsum
  · intro x hx
    exact finite_reconstruction_kernel_hasFDerivAt weight kernel gradKernel x
      (fun a => hkernelGrad a x hx)
  · intro x hx
    unfold finiteReconstructionGradient
    have hsum : ContDiffAt ℝ 1 (fun y => ∑ a, weight a • gradKernel a y) x := by
      apply ContDiffAt.sum (s := Finset.univ)
      intro a ha
      exact (hgradKernelC1 a x hx).const_smul (weight a)
    simpa using hsum
  · intro x hx
    exact finite_reconstruction_gradient_hasFDerivAt weight gradKernel
      hessKernel x (fun a => hgradHess a x hx)
  · exact finite_reconstruction_gradient_eq_zero weight gradKernel center hcenter
  · intro x hx v
    exact finite_reconstruction_hessian_bound weight
      (fun a => hessKernel a x) v m hweight hnorm
      (fun a => hbound a x hx v)

/-- Transfer the finite weighted local-valley package to the equivalent
finite Dirac-mixture integral. This gives the integral formulation without
invoking general differentiation-under-the-integral assumptions. -/
theorem finite_measure_reconstruction_kernel_conditions
    {A E : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (U : Set E) (weight : A → ℝ)
    (kernel : A → E → ℝ) (gradKernel : A → E → E)
    (hessKernel : A → E → E →L[ℝ] E) (center : E) (m : ℝ)
    (hweight : ∀ a, 0 ≤ weight a) (hnorm : ∑ a, weight a = 1)
    (hkernelC2 : ∀ a, ContDiffOn ℝ 2 (kernel a) U)
    (hkernelGrad : ∀ a x, x ∈ U →
      HasFDerivAt (kernel a) (innerSL ℝ (gradKernel a x)) x)
    (hgradKernelC1 : ∀ a x, x ∈ U → ContDiffAt ℝ 1 (gradKernel a) x)
    (hgradHess : ∀ a x, x ∈ U →
      HasFDerivAt (gradKernel a) (hessKernel a x) x)
    (hcenter : ∀ a, gradKernel a center = 0)
    (hbound : ∀ a x, x ∈ U → ∀ v : E,
      inner ℝ (hessKernel a x v) v ≤ -m * ‖v‖ ^ 2) :
    ContDiffOn ℝ 1
        (fun x => ∫ a, kernel a x ∂finiteReconstructionMeasure weight) U ∧
    (∀ x ∈ U, HasFDerivAt
      (fun y => ∫ a, kernel a y ∂finiteReconstructionMeasure weight)
      (innerSL ℝ (∫ a, gradKernel a x ∂finiteReconstructionMeasure weight)) x) ∧
    (∀ x ∈ U, ContDiffAt ℝ 1
      (fun y => ∫ a, gradKernel a y ∂finiteReconstructionMeasure weight) x) ∧
    (∀ x ∈ U, HasFDerivAt
      (fun y => ∫ a, gradKernel a y ∂finiteReconstructionMeasure weight)
      (∫ a, hessKernel a x ∂finiteReconstructionMeasure weight) x) ∧
    (∫ a, gradKernel a center ∂finiteReconstructionMeasure weight) = 0 ∧
    (∀ x ∈ U, ∀ v : E,
      inner ℝ ((∫ a, hessKernel a x ∂finiteReconstructionMeasure weight) v) v ≤
        -m * ‖v‖ ^ 2) := by
  obtain ⟨hSc1, hS, hgradSc1, hHS, hcenterS, hSlower⟩ :=
    finite_reconstruction_kernel_conditions U weight kernel gradKernel hessKernel
      center m hweight hnorm hkernelC2 hkernelGrad hgradKernelC1 hgradHess
      hcenter hbound
  obtain ⟨hkernelEq, hgradEq, hHessEq⟩ :=
    finite_reconstruction_measure_kernel_gradient_hessian_eq_weighted weight
      hweight kernel gradKernel hessKernel
  have hgradFunEq :
      (fun x => ∫ a, gradKernel a x ∂finiteReconstructionMeasure weight) =
        finiteReconstructionGradient weight gradKernel := funext hgradEq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hkernelFunEq :
        (fun x => ∫ a, kernel a x ∂finiteReconstructionMeasure weight) =
          finiteReconstructionKernel weight kernel := funext hkernelEq
    rw [hkernelFunEq]
    exact hSc1
  · intro x hx
    have hderivEq : innerSL ℝ (finiteReconstructionGradient weight gradKernel x) =
        innerSL ℝ (∫ a, gradKernel a x ∂finiteReconstructionMeasure weight) := by
      rw [← hgradEq x]
    exact (hS x hx).congr_fderiv hderivEq |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall hkernelEq)
  · simpa only [hgradFunEq] using hgradSc1
  · intro x hx
    have hderivEq : finiteReconstructionHessian weight hessKernel x =
        ∫ a, hessKernel a x ∂finiteReconstructionMeasure weight := by
      rw [← hHessEq x]
    exact (hHS x hx).congr_fderiv hderivEq |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall hgradEq)
  · simpa only [hgradEq center] using hcenterS
  · intro x hx v
    simpa only [hHessEq x] using hSlower x hx v

end Tomabechi.Theorem21
