import Theorem19
import Tomabechi.Information.Capacity
import Tomabechi.Information.FiniteCMI
import Tomabechi.Information.MeasureCMI

open Tomabechi.Theorem22
open MeasureTheory ProbabilityTheory

/-! 一般測度CMI法則を依存型容量へ接続するAPI。-/

namespace Tomabechi.Theorem19_22

/-- 層ごとの異なる問題型・方策対を束ねる共通Σ型。 -/
abbrev ProblemPool (L : Type*) (A : L → Type*) := Σ a, A a

/-- 指定層で許容される要素をΣ型の共通プール上に埋め込んだ集合。 -/
def pooledAdmissible {L : Type*} (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (a : L) : Set (ProblemPool L A) :=
  {q | ∃ x : A a, q = ⟨a, x⟩ ∧ x ∈ admissible a}

/-- 問題が属する層に応じて有限ゴールCMIを採点するΣ型上のスコア。 -/
noncomputable def pooledFiniteGoalScore
    {L X G Y : Type*} [Fintype X] [Fintype G]
    (A : L → Type*) (mass : ∀ a, A a → X → G → ℝ)
    (policy : ∀ a, A a → X → G → Y) : ProblemPool L A → ℝ :=
  fun q => Tomabechi.Theorem21.finiteConditionalMutualInformation
    (mass q.1 q.2) (policy q.1 q.2)

/-- 定理19の依存型容量は、Σ型で束ねた定理22容量と一致する。
これは問題型の束ね方による表現同定で、確率モデルの存在を仮定から導く主張ではない。 -/
theorem dependentCapacity_eq_pooledLayerCapacity
    {L X G Y : Type*} [Preorder L] [Fintype X] [Fintype G]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (mass : ∀ a, A a → X → G → ℝ)
    (policy : ∀ a, A a → X → G → Y) (a : L) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun b x => Tomabechi.Theorem21.finiteConditionalMutualInformation
        (mass b x) (policy b x)) a =
      layerCapacity (pooledAdmissible A admissible)
        (pooledFiniteGoalScore A mass policy) a := by
  classical
  unfold Tomabechi.Theorem19.dependentLayerCapacity layerCapacity
    pooledAdmissible pooledFiniteGoalScore
  congr 1
  ext r
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨a, x⟩, ⟨x, rfl, hx⟩, rfl⟩
  · rintro ⟨⟨b, x⟩, ⟨y, hq, hy⟩, hr⟩
    cases hq
    exact ⟨y, hy, hr⟩

/-- 定理19の層別埋め込みが許容性と誘導同時法則を保つとき、Σ型プール上の
定理22有限ゴール容量は単調である。単射性も原文条件として保持する。 -/
theorem dependent_finite_goal_capacity_nondecreasing
    {L X G Y : Type*} [Preorder L] [Fintype X] [Fintype G] [Fintype Y]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (mass : ∀ a, A a → X → G → ℝ)
    (policy : ∀ a, A a → X → G → Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun x => Tomabechi.Theorem21.finiteConditionalMutualInformation
        (mass a x) (policy a x)) '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hlaw : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      finiteGoalJointLaw (mass b (embedding hab x)) (policy b (embedding hab x)) =
        finiteGoalJointLaw (mass a x) (policy a x))
    (a b : L) (hab : a ≤ b) :
    layerCapacity (pooledAdmissible A admissible)
        (pooledFiniteGoalScore A mass policy) a ≤
      layerCapacity (pooledAdmissible A admissible)
        (pooledFiniteGoalScore A mass policy) b := by
  rw [← dependentCapacity_eq_pooledLayerCapacity A admissible mass policy a,
    ← dependentCapacity_eq_pooledLayerCapacity A admissible mass policy b]
  apply Tomabechi.Theorem19.dependentCapacity_nondecreasing_of_scorePreservingEmbedding
    A admissible
    (fun c x => Tomabechi.Theorem21.finiteConditionalMutualInformation
      (mass c x) (policy c x))
    hnonempty hbounded embedding hinjective hmapsTo
  intro c d hcd x hx
  have hjoint := hlaw hcd hx
  calc
    Tomabechi.Theorem21.finiteConditionalMutualInformation
        (mass d (embedding hcd x)) (policy d (embedding hcd x)) =
        finiteConditionalMutualInformationOfJointLaw
          (finiteGoalJointLaw (mass d (embedding hcd x))
            (policy d (embedding hcd x))) :=
      finiteConditionalMutualInformation_factors_through_jointLaw
        (mass d (embedding hcd x)) (policy d (embedding hcd x))
    _ = finiteConditionalMutualInformationOfJointLaw
          (finiteGoalJointLaw (mass c x) (policy c x)) := by rw [hjoint]
    _ = Tomabechi.Theorem21.finiteConditionalMutualInformation
          (mass c x) (policy c x) :=
      (finiteConditionalMutualInformation_factors_through_jointLaw
        (mass c x) (policy c x)).symm
  exact hab

/-- 定理22のLUB更新式 `u(n+1)=u(n)⊔v(n+1)` の下で、前定理の定理19由来容量橋を
各隣接段階へ適用し、Σ型で束ねた依存型問題族の有限CMI容量が単調となることを示す。 -/
theorem dependent_finite_goal_capacity_monotone_along_lub_stages
    {L X G Y : Type*} [SemilatticeSup L]
    [Fintype X] [Fintype G] [Fintype Y]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (mass : ∀ a, A a → X → G → ℝ)
    (policy : ∀ a, A a → X → G → Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun x => Tomabechi.Theorem21.finiteConditionalMutualInformation
        (mass a x) (policy a x)) '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hlaw : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      finiteGoalJointLaw (mass b (embedding hab x)) (policy b (embedding hab x)) =
        finiteGoalJointLaw (mass a x) (policy a x))
    (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone (fun n => layerCapacity (pooledAdmissible A admissible)
      (pooledFiniteGoalScore A mass policy) (u n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hupdate n]
  exact dependent_finite_goal_capacity_nondecreasing
    A admissible mass policy hnonempty hbounded embedding hinjective
    hmapsTo hlaw (u n) (u n ⊔ v (n + 1)) le_sup_left

end Tomabechi.Theorem19_22

namespace Tomabechi.Theorem19_22

/-- General measurable-space CMI score on the dependent problem pool. The
finite law explicitly carries its joint law, conditional kernels, reference
law, and finite-KL certificate. The goal alphabet is finite, while the input
and output alphabets may be infinite and the output may be stochastic. -/
noncomputable def pooledMeasureCMIScore
    {L X G Y : Type*} [Fintype G] [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y]
    (A : L → Type*)
    (law : ∀ a, A a → FiniteConditionalMutualInformationLaw X G Y) :
    ProblemPool L A → ℝ :=
  fun q => finiteKLDivergenceScore (law q.1 q.2).toFiniteKLLaw

/-- The dependent capacity and its Σ-pooled general measurable-space CMI
capacity are the same score supremum, with no finiteness restriction on the
context or action spaces. -/
theorem dependentMeasureCMICapacity_eq_pooledLayerCapacity
    {L X G Y : Type*} [Preorder L]
    [Fintype G]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (law : ∀ a, A a → FiniteConditionalMutualInformationLaw X G Y)
    (a : L) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun b x => finiteKLDivergenceScore (law b x).toFiniteKLLaw) a =
      layerCapacity (pooledAdmissible A admissible)
        (pooledMeasureCMIScore A law) a := by
  classical
  unfold Tomabechi.Theorem19.dependentLayerCapacity layerCapacity
    pooledAdmissible pooledMeasureCMIScore
  congr 1
  ext r
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨a, x⟩, ⟨x, rfl, hx⟩, rfl⟩
  · rintro ⟨⟨b, x⟩, ⟨y, hq, hy⟩, hr⟩
    cases hq
    exact ⟨y, hy, hr⟩

/-- Joint-law-preserving cross-layer embeddings preserve the general CMI score
when conditional kernels are unique on the relevant generated spaces. This
gives Theorem 19's dependent capacity monotonicity without finite `X`/`Y` or
deterministic policies. The finite goal alphabet is represented by its
measurable space. -/
theorem dependent_measure_cmi_capacity_nondecreasing
    {L X G Y : Type*} [Preorder L]
    [Fintype G]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X G]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (law : ∀ a, A a → FiniteConditionalMutualInformationLaw X G Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hjointPreserving : ∀ {a b : L} (hab : a ≤ b) {x},
      x ∈ admissible a →
        (law b (embedding hab x)).distribution.joint =
          (law a x).distribution.joint)
    (a b : L) (hab : a ≤ b) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) a ≤
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) b := by
  apply Tomabechi.Theorem19.dependentCapacity_nondecreasing_of_scorePreservingEmbedding
    A admissible
    (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw)
    hnonempty hbounded embedding hinjective hmapsTo
  intro c d hcd x hx
  let law₁ := (law d (embedding hcd x)).distribution
  let law₂ := (law c x).distribution
  have hjoint := hjointPreserving hcd hx
  have href := ConditionalMutualInformationLaw.referenceMeasure_eq_of_joint_eq
    law₁ law₂ hjoint
  change finiteKLDivergenceScore (law d (embedding hcd x)).toFiniteKLLaw =
    finiteKLDivergenceScore (law c x).toFiniteKLLaw
  simp only [finiteKLDivergenceScore,
    FiniteConditionalMutualInformationLaw.toFiniteKLLaw]
  change (InformationTheory.klDiv law₁.joint law₁.referenceMeasure).toReal =
    (InformationTheory.klDiv law₂.joint law₂.referenceMeasure).toReal
  rw [hjoint, href]
  exact hab

/-- On completely general measurable spaces, preserving the complete KL pair
(joint law and conditional-independence reference law) is enough for capacity
monotonicity. This variant removes the countable-generation hypothesis; the
joint-law-only theorem above derives reference preservation under that
regularity assumption. -/
theorem dependent_measure_cmi_capacity_nondecreasing_of_pair_preserving
    {L X G Y : Type*} [Preorder L]
    [Fintype G]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (law : ∀ a, A a → FiniteConditionalMutualInformationLaw X G Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hpairPreserving : ∀ {a b : L} (hab : a ≤ b) {x},
      x ∈ admissible a →
        (law b (embedding hab x)).toFiniteKLLaw = (law a x).toFiniteKLLaw)
    (a b : L) (hab : a ≤ b) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) a ≤
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) b := by
  apply Tomabechi.Theorem19.dependentCapacity_nondecreasing_of_scorePreservingEmbedding
    A admissible
    (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw)
    hnonempty hbounded embedding hinjective hmapsTo
  intro c d hcd x hx
  rw [hpairPreserving hcd hx]
  exact hab

/-- The pooled general-measure CMI capacity is nonnegative because its score
is a real finite-KL value. Nonemptiness and boundedness are the explicit
capacity hypotheses from Theorem 19. -/
theorem dependent_measure_cmi_capacity_nonnegative
    {L X G Y : Type*} [Preorder L] [Fintype G]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (law : ∀ a, A a → FiniteConditionalMutualInformationLaw X G Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a))
    (a : L) :
    0 ≤ Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) a := by
  obtain ⟨x, hx⟩ := hnonempty a
  change 0 ≤ sSup
    ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a)
  calc
    0 ≤ finiteKLDivergenceScore (law a x).toFiniteKLLaw := ENNReal.toReal_nonneg
    _ ≤ sSup
        ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a) :=
      le_csSup (hbounded a) ⟨x, hx, rfl⟩

/-- Conditional independence makes the joint law equal its designated reference
law, hence the measure-CMI score is zero. This theorem records the exact
measure-level condition; deriving it from an informal independence predicate
remains a separate law-construction task. -/
theorem finite_measure_cmi_score_eq_zero_of_joint_eq_reference
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y]
    (law : FiniteConditionalMutualInformationLaw X G Y)
    (hindependent : law.distribution.joint = law.distribution.referenceMeasure) :
    finiteKLDivergenceScore law.toFiniteKLLaw = 0 := by
  letI : MeasureTheory.IsProbabilityMeasure law.distribution.joint :=
    law.distribution.joint_isProbabilityMeasure
  letI : MeasureTheory.IsProbabilityMeasure law.distribution.referenceMeasure :=
    law.distribution.referenceMeasure_isProbabilityMeasure
  have hkl : InformationTheory.klDiv law.distribution.joint
      law.distribution.referenceMeasure = 0 := by
    rw [hindependent]
    exact InformationTheory.klDiv_self _
  simp [finiteKLDivergenceScore, FiniteConditionalMutualInformationLaw.toFiniteKLLaw,
    hkl]

/-- If every admissible problem has a joint law equal to its conditional-
independence reference law, then the dependent measure-CMI capacity is zero.
Nonemptiness and boundedness are retained as the hypotheses of the source
capacity API. -/
theorem dependent_measure_cmi_capacity_eq_zero_of_independence
    {L X G Y : Type*} [Preorder L] [Fintype G]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (law : ∀ a, A a → FiniteConditionalMutualInformationLaw X G Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a))
    (hindependent : ∀ a x, x ∈ admissible a →
      (law a x).distribution.joint = (law a x).distribution.referenceMeasure)
    (a : L) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) a = 0 := by
  obtain ⟨x₀, hx₀⟩ := hnonempty a
  change sSup
    ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a) = 0
  apply le_antisymm
  · apply csSup_le ((hnonempty a).image
      (fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw))
    rintro z ⟨x, hx, rfl⟩
    change finiteKLDivergenceScore (law a x).toFiniteKLLaw ≤ 0
    rw [finite_measure_cmi_score_eq_zero_of_joint_eq_reference (law a x)
      (hindependent a x hx)]
  · have hmem : finiteKLDivergenceScore (law a x₀).toFiniteKLLaw ∈
      (fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a :=
        ⟨x₀, hx₀, rfl⟩
    have hscore0 := finite_measure_cmi_score_eq_zero_of_joint_eq_reference
      (law a x₀) (hindependent a x₀ hx₀)
    have hmem0 : 0 ∈
        (fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a := by
      rw [← hscore0]
      exact hmem
    exact le_csSup (hbounded a) hmem0

/-- The dependent capacity has the zero-conditional-entropy conclusion when
the measure-CMI score is bounded above by the supplied entropy functional.
The score-to-entropy inequality is explicit input here; this adapter does not
claim that the general measure-theoretic inequality has been derived. -/
theorem dependent_measure_cmi_capacity_eq_zero_of_zero_entropy_bound
    {L X G Y : Type*} [Preorder L] [Fintype G]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (law : ∀ a, A a → FiniteConditionalMutualInformationLaw X G Y)
    (goalEntropy : ∀ a, A a → ℝ)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a))
    (hscoreLeEntropy : ∀ a x, x ∈ admissible a →
      finiteKLDivergenceScore (law a x).toFiniteKLLaw ≤ goalEntropy a x)
    (hentropyZero : ∀ a x, x ∈ admissible a → goalEntropy a x = 0)
    (a : L) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) a = 0 := by
  obtain ⟨x₀, hx₀⟩ := hnonempty a
  change sSup
    ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a) = 0
  apply le_antisymm
  · apply csSup_le ((hnonempty a).image
      (fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw))
    rintro z ⟨x, hx, rfl⟩
    calc
      finiteKLDivergenceScore (law a x).toFiniteKLLaw ≤ goalEntropy a x :=
        hscoreLeEntropy a x hx
      _ = 0 := hentropyZero a x hx
  · have hscoreNonneg :
        0 ≤ finiteKLDivergenceScore (law a x₀).toFiniteKLLaw :=
      ENNReal.toReal_nonneg
    have hmem : finiteKLDivergenceScore (law a x₀).toFiniteKLLaw ∈
        (fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a :=
      ⟨x₀, hx₀, rfl⟩
    exact hscoreNonneg.trans (le_csSup (hbounded a) hmem)

/-- If the zero-entropy endpoint has capacity zero and the top endpoint has
positive capacity, the existing affine normalization fixes those endpoints
to 0 and 1. -/
theorem dependent_measure_cmi_endpoint_normalization_values
    {L X G Y : Type*} [CompleteLattice L] [Fintype G]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (law : ∀ a, A a → FiniteConditionalMutualInformationLaw X G Y)
    (hbottomZero : Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊥ = 0)
    (htopPositive : 0 < Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊤) :
    Tomabechi.Theorem19.endpointNormalization
        (Tomabechi.Theorem19.dependentLayerCapacity A admissible
          (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊥)
        (Tomabechi.Theorem19.dependentLayerCapacity A admissible
          (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊤)
        (Tomabechi.Theorem19.dependentLayerCapacity A admissible
          (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊥) = 0 ∧
      Tomabechi.Theorem19.endpointNormalization
        (Tomabechi.Theorem19.dependentLayerCapacity A admissible
          (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊥)
        (Tomabechi.Theorem19.dependentLayerCapacity A admissible
          (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊤)
        (Tomabechi.Theorem19.dependentLayerCapacity A admissible
          (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊤) = 1 := by
  have hbottomTop :
      Tomabechi.Theorem19.dependentLayerCapacity A admissible
        (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊥ <
      Tomabechi.Theorem19.dependentLayerCapacity A admissible
        (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊤ := by
    rw [hbottomZero]
    exact htopPositive
  exact Tomabechi.Theorem19.endpointNormalization_values
    (Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊥)
    (Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) ⊤)
    hbottomTop

/-- General measurable-space CMI capacity iterated along the LUB recurrence
`u(n+1)=u(n)⊔v(n+1)`, conditional on the joint-law-preserving embeddings and
finite-KL certificates supplied by each law. -/
theorem dependent_measure_cmi_capacity_monotone_along_lub_stages
    {L X G Y : Type*} [SemilatticeSup L]
    [Fintype G]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X G]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (law : ∀ a, A a → FiniteConditionalMutualInformationLaw X G Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hjointPreserving : ∀ {a b : L} (hab : a ≤ b) {x},
      x ∈ admissible a →
        (law b (embedding hab x)).distribution.joint =
          (law a x).distribution.joint)
    (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone (fun n => Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) (u n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hupdate n]
  exact dependent_measure_cmi_capacity_nondecreasing A admissible law
    hnonempty hbounded embedding hinjective hmapsTo hjointPreserving
    (u n) (u n ⊔ v (n + 1)) le_sup_left

end Tomabechi.Theorem19_22


namespace Tomabechi.Theorem19_22

/-- 指定層aの全許容問題でH(G|X)=0なら、その層の容量は零。
他層の零エントロピーやCMI上界を入力せず、非空性と法則だけから証明する。
原文19の物理層への適用ではa=⊥とする。 -/
theorem dependent_measure_cmi_capacity_eq_zero_of_inputGoalEntropy_zero
    {L X G Y : Type*} [Preorder L] [Fintype G]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [MeasurableSingletonClass G]
    (A : L → Type*) (admissible : ∀ a, Set (A a))
    (law : ∀ a, A a → FiniteConditionalMutualInformationLaw X G Y)
    (a : L) (hnonempty : (admissible a).Nonempty)
    (hentropyZero : ∀ x, x ∈ admissible a →
      inputGoalEntropy (law a x).distribution = 0) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => finiteKLDivergenceScore (law c x).toFiniteKLLaw) a = 0 := by
  have himage : ((fun x => finiteKLDivergenceScore (law a x).toFiniteKLLaw) ''
      admissible a) = {0} := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Set.mem_singleton_iff.mpr
        (finite_measure_cmi_score_eq_zero_of_inputGoalEntropy_zero
          (law a x) (hentropyZero x hx))
    · intro hr
      obtain ⟨x, hx⟩ := hnonempty
      have hscore := finite_measure_cmi_score_eq_zero_of_inputGoalEntropy_zero
        (law a x) (hentropyZero x hx)
      exact ⟨x, hx, hscore.trans (Set.mem_singleton_iff.mp hr).symm⟩
  unfold Tomabechi.Theorem19.dependentLayerCapacity
  rw [himage]
  simp

/-- 問題ごとにX/G/Yが異なる直接CMI容量の零エントロピー結論。
原文の実数化前KL上限有限から各許容問題の有限性を取り出す。
非許容問題の有限性、各問題のY|X核、出力標準Borel性は要求しない。 -/
theorem heterogeneous_directCMI_capacity_eq_zero
    {Q : Type*} (X G Y : Q → Type*)
    [∀ q, MeasurableSpace (X q)] [∀ q, MeasurableSpace (G q)]
    [∀ q, MeasurableSpace (Y q)] [∀ q, Fintype (G q)]
    [∀ q, MeasurableSingletonClass (G q)]
    (joint : ∀ q, Measure (X q × (G q × Y q)))
    [∀ q, IsProbabilityMeasure (joint q)]
    (admissible : Set Q) (hnonempty : admissible.Nonempty)
    (hfinite : sSup ((fun q => InformationTheory.klDiv
      (directActionGoalJoint (joint q)) (directCMIReference (joint q))) '' admissible) ≠ ⊤)
    (hentropy : ∀ q ∈ admissible,
      (∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel (joint q)) x
        ∂(joint q).map Prod.fst) = 0) :
    sSup ((fun q => (InformationTheory.klDiv
      (directActionGoalJoint (joint q)) (directCMIReference (joint q))).toReal) '' admissible) = 0 := by
  let score := fun q => (InformationTheory.klDiv
    (directActionGoalJoint (joint q)) (directCMIReference (joint q))).toReal
  have hle : ∀ q ∈ admissible, score q ≤ 0 := by
    intro q hq
    have hqfinite : InformationTheory.klDiv
        (directActionGoalJoint (joint q)) (directCMIReference (joint q)) ≠ ⊤ :=
      ne_top_of_le_ne_top hfinite (le_sSup ⟨q, hq, rfl⟩)
    have h := directCMI_le_inputGoalEntropy_of_finite (joint q) hqfinite
    rw [hentropy q hq] at h
    exact h
  have hbounded : BddAbove (score '' admissible) := by
    refine ⟨0, ?_⟩
    rintro z ⟨q, hq, rfl⟩
    exact hle q hq
  exact Tomabechi.Theorem19.zeroCapacity_of_zeroGoalEntropy admissible score
    (fun _ => 0) hnonempty hbounded (fun _ _ => ENNReal.toReal_nonneg)
    hle (fun _ _ => rfl)


end Tomabechi.Theorem19_22
