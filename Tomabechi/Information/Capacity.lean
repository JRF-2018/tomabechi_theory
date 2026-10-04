import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! # 情報容量と一般測度CMIの共有核

定理22の抽象容量・KLスコア・条件付き相互情報量法則と、その層間保存補題。
LUB段階列や段階ODEを参照しない情報理論APIを、既存のnamespaceと宣言名のまま分離する。
-/

open Filter
open scoped Topology ProbabilityTheory

namespace Tomabechi.Theorem22

/-- Abstract capacity of the admissible goal-policy family at one LUB layer.
The score can be instantiated by the conditional mutual information used in
Theorem 19.
日本語要約：LUB段階ごとに許容される問題・方策のスコアの上限を容量として定義する。 -/
noncomputable def layerCapacity {L A : Type*}
    (admissible : L → Set A) (score : A → ℝ) (a : L) : ℝ :=
  sSup (score '' admissible a)

/-- The capacity conclusion (22.6). A higher-layer embedding must preserve the
score of every lower-layer admissible problem/policy pair; nonemptiness and
boundedness make the supremum finite. Taking score to be conditional mutual
information gives the paper's distribution-preserving embedding condition.
This interface isolates the score-preservation consequence of the Theorem 19
embedding instead of assuming capacity monotonicity itself. The companion
`capacity_nondecreasing_of_injective_law_preserving_embedding` retains the
full injective, joint-law-preserving hypothesis and derives this score-level
condition when the score factors through that law.
日本語要約：低層の各許容項目を高層へ移すスコア保存条件から、上限で定義した容量の単調性を示す。 -/
theorem capacity_nondecreasing_of_embedding_condition
    {L A : Type*} [Preorder L]
    (admissible : L → Set A) (score : A → ℝ)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove (score '' admissible a))
    (hembedding : ∀ {a b : L}, a ≤ b → ∀ x ∈ admissible a,
      ∃ y ∈ admissible b, score y = score x)
    (a b : L) (hab : a ≤ b) : layerCapacity admissible score a ≤
      layerCapacity admissible score b := by
  let Ia := score '' admissible a
  let Ib := score '' admissible b
  have hneIa : Ia.Nonempty := (hnonempty a).image score
  have hneIb : Ib.Nonempty := (hnonempty b).image score
  have hIa : IsLUB Ia (sSup Ia) :=
    isLUB_csSup hneIa (by simpa [Ia] using hbounded a)
  have hIb : IsLUB Ib (sSup Ib) :=
    isLUB_csSup hneIb (by simpa [Ib] using hbounded b)
  have hbound : ∀ x ∈ Ia, x ≤ sSup Ib := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hscore⟩ := hembedding hab x hx
    calc
      score x = score y := hscore.symm
      _ ≤ sSup Ib := hIb.1 ⟨y, hy, rfl⟩
  change sSup Ia ≤ sSup Ib
  exact hIa.2 hbound

/-- The full embedding form of (22.6): higher-layer injections preserve the
joint law of each admissible problem/policy pair, and the score is a function
of that law. The previously stated score-realizability lemma is the small
order-theoretic core; this version retains Theorem 19's injectivity and
distribution-preservation condition explicitly.
日本語要約：単射かつ同時分布を保存する層間写像とスコアの分布依存性から (22.6) を証明する。 -/
theorem capacity_nondecreasing_of_injective_law_preserving_embedding
    {L A Law : Type*} [Preorder L]
    (admissible : L → Set A) (jointLaw : A → Law)
    (scoreOfLaw : Law → ℝ) (score : A → ℝ)
    (hscore : ∀ x, score x = scoreOfLaw (jointLaw x))
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove (score '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A → A)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x : A},
      x ∈ admissible a → embedding hab x ∈ admissible b)
    (hlawPreserving : ∀ {a b : L} (hab : a ≤ b) {x : A},
      x ∈ admissible a → jointLaw (embedding hab x) = jointLaw x)
    (a b : L) (hab : a ≤ b) :
    layerCapacity admissible score a ≤ layerCapacity admissible score b := by
  apply capacity_nondecreasing_of_embedding_condition
    admissible score hnonempty hbounded
  intro a b hab x hx
  refine ⟨embedding hab x, hmapsTo hab hx, ?_⟩
  calc
    score (embedding hab x) = scoreOfLaw (jointLaw (embedding hab x)) :=
      hscore (embedding hab x)
    _ = scoreOfLaw (jointLaw x) := congrArg scoreOfLaw (hlawPreserving hab hx)
    _ = score x := (hscore x).symm
  · exact hab

/-- A finite-measure KL score together with its finiteness certificate.
For conditional mutual information, `joint` is the joint law and `reference`
must be the conditional-independence reference law
`P_X ⊗ P_{G|X} ⊗ P_{Y|X}`. The structure itself deliberately does not claim
that arbitrary measures have this interpretation.
日本語要約：有限な測度KLダイバージェンスをスコア化するデータ。条件付き相互情報量として使う場合の参照法則の意味も明示する。-/
structure FiniteKLDivergenceLaw (Ω : Type*) [MeasurableSpace Ω] where
  joint : MeasureTheory.Measure Ω
  reference : MeasureTheory.Measure Ω
  finite : InformationTheory.klDiv joint reference ≠ ⊤

/-- Real-valued KL score of a finite-measure law pair. -/
noncomputable def finiteKLDivergenceScore {Ω : Type*} [MeasurableSpace Ω]
    (law : FiniteKLDivergenceLaw Ω) : ℝ :=
  (InformationTheory.klDiv law.joint law.reference).toReal

/-- The capacity monotonicity theorem specialized to general measurable-space
KL scores. The embedding preserves both measures in the KL pair (and thus the
source joint law and its designated reference law). With the conditional-
independence reference from `FiniteKLDivergenceLaw`, this is a measure-theoretic
conditional-mutual-information instance of (22.6); constructing that reference
from conditional kernels and proving its preservation remain separate tasks.
日本語要約：一般可測空間の有限KLスコアについて、単射かつKL法則対を保存する埋め込みから容量単調性を示す。条件付き独立参照法則の構成は別条件として区別する。-/
theorem capacity_nondecreasing_of_finite_kl_preserving_embedding
    {L A Ω : Type*} [Preorder L] [MeasurableSpace Ω]
    (admissible : L → Set A)
    (law : A → FiniteKLDivergenceLaw Ω)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a,
      BddAbove (finiteKLDivergenceScore ∘ law '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A → A)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x : A},
      x ∈ admissible a → embedding hab x ∈ admissible b)
    (hlawPreserving : ∀ {a b : L} (hab : a ≤ b) {x : A},
      x ∈ admissible a → law (embedding hab x) = law x)
    (a b : L) (hab : a ≤ b) :
    layerCapacity admissible (finiteKLDivergenceScore ∘ law) a ≤
      layerCapacity admissible (finiteKLDivergenceScore ∘ law) b := by
  exact capacity_nondecreasing_of_injective_law_preserving_embedding
    admissible law finiteKLDivergenceScore (finiteKLDivergenceScore ∘ law)
    (fun _ => rfl) hnonempty hbounded embedding hinjective hmapsTo
    hlawPreserving a b hab

/-- A joint law on `X × (G × Y)` with kernels giving its conditional
marginals `G | X` and `Y | X`. The compatibility fields say that the two
pairwise marginals are the corresponding kernel compositions with the input
law. This is the data needed to construct the conditional-independence
reference measure used in the KL definition of `I(G;Y | X)`.
日本語要約：同時法則と二つの条件付き周辺核をもち、周辺法則との整合性を明示する条件付き相互情報量の測度データ。-/
structure ConditionalMutualInformationLaw
    (X G Y : Type*) [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    where
  input : MeasureTheory.Measure X
  inputProbability : MeasureTheory.IsProbabilityMeasure input
  goalGivenInput : ProbabilityTheory.Kernel X G
  goalKernelMarkov : ProbabilityTheory.IsMarkovKernel goalGivenInput
  actionGivenInput : ProbabilityTheory.Kernel X Y
  actionKernelMarkov : ProbabilityTheory.IsMarkovKernel actionGivenInput
  joint : MeasureTheory.Measure (X × (G × Y))
  jointGoalMarginal :
    joint.map (fun z : X × (G × Y) => (z.1, z.2.1)) =
      input ⊗ₘ goalGivenInput
  jointActionMarginal :
    joint.map (fun z : X × (G × Y) => (z.1, z.2.2)) =
      input ⊗ₘ actionGivenInput

/-- The joint law is itself a probability measure: its `(X,G)` marginal is a
probability measure because it is the composition of the input probability
law with a Markov kernel. Thus the consistency field rules out arbitrary
infinite-mass measures from being called a joint distribution.
日本語要約：入力確率測度と確率核の合成が確率測度であり、それが同時法則の周辺であることから同時法則自体も確率測度と分かる。-/
theorem ConditionalMutualInformationLaw.joint_isProbabilityMeasure
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y] (law : ConditionalMutualInformationLaw X G Y) :
    MeasureTheory.IsProbabilityMeasure law.joint := by
  letI : MeasureTheory.IsProbabilityMeasure law.input := law.inputProbability
  letI : ProbabilityTheory.IsMarkovKernel law.goalGivenInput :=
    law.goalKernelMarkov
  have hmarginal : MeasureTheory.IsProbabilityMeasure
      (law.joint.map (fun z : X × (G × Y) => (z.1, z.2.1))) := by
    rw [law.jointGoalMarginal]
    infer_instance
  exact MeasureTheory.Measure.isProbabilityMeasure_of_map
    (by fun_prop : AEMeasurable
      (fun z : X × (G × Y) => (z.1, z.2.1)) law.joint)

/-- Conditional-independence reference measure
`P_X(dx) P_{G|X}(dg|x) P_{Y|X}(dy|x)`, constructed by taking the parallel
product of the two conditional kernels along the diagonal copy of `X`.
日本語要約：条件付き相互情報量のKL参照測度を、Xを共有する条件付き核の独立積として構成する。-/
noncomputable def ConditionalMutualInformationLaw.referenceMeasure
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y] (law : ConditionalMutualInformationLaw X G Y) :
    MeasureTheory.Measure (X × (G × Y)) := by
  letI : MeasureTheory.IsProbabilityMeasure law.input := law.inputProbability
  letI : ProbabilityTheory.IsMarkovKernel law.goalGivenInput :=
    law.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law.actionGivenInput :=
    law.actionKernelMarkov
  exact law.input ⊗ₘ
    ((law.goalGivenInput ∥ₖ law.actionGivenInput) ∘ₖ ProbabilityTheory.Kernel.copy X)

theorem ConditionalMutualInformationLaw.referenceMeasure_fst
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y] (law : ConditionalMutualInformationLaw X G Y) :
    law.referenceMeasure.fst = law.input := by
  letI : MeasureTheory.IsProbabilityMeasure law.input := law.inputProbability
  letI : ProbabilityTheory.IsMarkovKernel law.goalGivenInput := law.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law.actionGivenInput := law.actionKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel
      (law.goalGivenInput ∥ₖ law.actionGivenInput) := inferInstance
  simp [ConditionalMutualInformationLaw.referenceMeasure]

theorem ConditionalMutualInformationLaw.referenceMeasure_isProbabilityMeasure
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y] (law : ConditionalMutualInformationLaw X G Y) :
    MeasureTheory.IsProbabilityMeasure law.referenceMeasure := by
  letI : MeasureTheory.IsProbabilityMeasure law.input := law.inputProbability
  letI : ProbabilityTheory.IsMarkovKernel law.goalGivenInput := law.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law.actionGivenInput := law.actionKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel
      (law.goalGivenInput ∥ₖ law.actionGivenInput) := inferInstance
  letI : ProbabilityTheory.IsMarkovKernel
      ((law.goalGivenInput ∥ₖ law.actionGivenInput) ∘ₖ ProbabilityTheory.Kernel.copy X) :=
    inferInstance
  rw [MeasureTheory.isProbabilityMeasure_iff]
  simp [ConditionalMutualInformationLaw.referenceMeasure,
    MeasureTheory.Measure.compProd_apply_univ]

theorem ConditionalMutualInformationLaw.referenceMeasure_goalMarginal
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y] (law : ConditionalMutualInformationLaw X G Y) :
    law.referenceMeasure.map (fun z : X × (G × Y) => (z.1, z.2.1)) =
      law.input ⊗ₘ law.goalGivenInput := by
  letI : MeasureTheory.IsProbabilityMeasure law.input := law.inputProbability
  letI : ProbabilityTheory.IsMarkovKernel law.goalGivenInput := law.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law.actionGivenInput := law.actionKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel
      (law.goalGivenInput ×ₖ law.actionGivenInput) := inferInstance
  have hmap : (law.goalGivenInput ×ₖ law.actionGivenInput).map Prod.fst =
      law.goalGivenInput := by
    rw [← ProbabilityTheory.Kernel.fst_eq,
      ProbabilityTheory.Kernel.fst_prod]
  calc
    law.referenceMeasure.map (fun z : X × (G × Y) => (z.1, z.2.1)) =
        (law.input ⊗ₘ (law.goalGivenInput ×ₖ law.actionGivenInput)).map
          (Prod.map id Prod.fst) := by
            change (law.input ⊗ₘ
              ((law.goalGivenInput ∥ₖ law.actionGivenInput) ∘ₖ
                ProbabilityTheory.Kernel.copy X)).map
              (fun z : X × (G × Y) => (z.1, z.2.1)) = _
            rw [ProbabilityTheory.Kernel.parallelComp_comp_copy]
            rfl
    _ = law.input ⊗ₘ
        ((law.goalGivenInput ×ₖ law.actionGivenInput).map Prod.fst) := by
          rw [MeasureTheory.Measure.compProd_map measurable_fst]
    _ = law.input ⊗ₘ law.goalGivenInput := by rw [hmap]

theorem ConditionalMutualInformationLaw.referenceMeasure_actionMarginal
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y] (law : ConditionalMutualInformationLaw X G Y) :
    law.referenceMeasure.map (fun z : X × (G × Y) => (z.1, z.2.2)) =
      law.input ⊗ₘ law.actionGivenInput := by
  letI : MeasureTheory.IsProbabilityMeasure law.input := law.inputProbability
  letI : ProbabilityTheory.IsMarkovKernel law.goalGivenInput := law.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law.actionGivenInput := law.actionKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel
      (law.goalGivenInput ×ₖ law.actionGivenInput) := inferInstance
  have hmap : (law.goalGivenInput ×ₖ law.actionGivenInput).map Prod.snd =
      law.actionGivenInput := by
    rw [← ProbabilityTheory.Kernel.snd_eq,
      ProbabilityTheory.Kernel.snd_prod]
  calc
    law.referenceMeasure.map (fun z : X × (G × Y) => (z.1, z.2.2)) =
        (law.input ⊗ₘ (law.goalGivenInput ×ₖ law.actionGivenInput)).map
          (Prod.map id Prod.snd) := by
            change (law.input ⊗ₘ
              ((law.goalGivenInput ∥ₖ law.actionGivenInput) ∘ₖ
                ProbabilityTheory.Kernel.copy X)).map
              (fun z : X × (G × Y) => (z.1, z.2.2)) = _
            rw [ProbabilityTheory.Kernel.parallelComp_comp_copy]
            rfl
    _ = law.input ⊗ₘ
        ((law.goalGivenInput ×ₖ law.actionGivenInput).map Prod.snd) := by
          rw [MeasureTheory.Measure.compProd_map measurable_snd]
    _ = law.input ⊗ₘ law.actionGivenInput := by rw [hmap]

theorem ConditionalMutualInformationLaw.referenceMeasure_eq_of_kernels_ae_eq
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y]
    (law₁ law₂ : ConditionalMutualInformationLaw X G Y)
    (hinput : law₁.input = law₂.input)
    (hgoal : law₁.goalGivenInput =ᵐ[law₁.input] law₂.goalGivenInput)
    (haction : law₁.actionGivenInput =ᵐ[law₁.input] law₂.actionGivenInput) :
    law₁.referenceMeasure = law₂.referenceMeasure := by
  letI : MeasureTheory.IsProbabilityMeasure law₁.input := law₁.inputProbability
  letI : MeasureTheory.IsProbabilityMeasure law₂.input := law₂.inputProbability
  letI : ProbabilityTheory.IsMarkovKernel law₁.goalGivenInput := law₁.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law₁.actionGivenInput := law₁.actionKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law₂.goalGivenInput := law₂.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law₂.actionGivenInput := law₂.actionKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel
      (law₁.goalGivenInput ×ₖ law₁.actionGivenInput) := inferInstance
  letI : ProbabilityTheory.IsMarkovKernel
      (law₂.goalGivenInput ×ₖ law₂.actionGivenInput) := inferInstance
  have hprod : law₁.goalGivenInput ×ₖ law₁.actionGivenInput =ᵐ[law₁.input]
      law₂.goalGivenInput ×ₖ law₂.actionGivenInput := by
    filter_upwards [hgoal, haction] with x hg ha
    rw [ProbabilityTheory.Kernel.prod_apply,
      ProbabilityTheory.Kernel.prod_apply, hg, ha]
  change law₁.input ⊗ₘ (law₁.goalGivenInput ×ₖ law₁.actionGivenInput) =
    law₂.input ⊗ₘ (law₂.goalGivenInput ×ₖ law₂.actionGivenInput)
  rw [hinput]
  exact MeasureTheory.Measure.compProd_congr (by simpa [hinput] using hprod)

theorem ConditionalMutualInformationLaw.referenceMeasure_eq_of_joint_eq
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X G]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (law₁ law₂ : ConditionalMutualInformationLaw X G Y)
    (hjoint : law₁.joint = law₂.joint) :
    law₁.referenceMeasure = law₂.referenceMeasure := by
  letI : MeasureTheory.IsProbabilityMeasure law₁.input := law₁.inputProbability
  letI : MeasureTheory.IsProbabilityMeasure law₂.input := law₂.inputProbability
  letI : ProbabilityTheory.IsMarkovKernel law₁.goalGivenInput := law₁.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law₁.actionGivenInput := law₁.actionKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law₂.goalGivenInput := law₂.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law₂.actionGivenInput := law₂.actionKernelMarkov
  have hgoalLaw : law₁.input ⊗ₘ law₁.goalGivenInput =
      law₂.input ⊗ₘ law₂.goalGivenInput := by
    calc
      law₁.input ⊗ₘ law₁.goalGivenInput =
          law₁.joint.map (fun z : X × (G × Y) => (z.1, z.2.1)) :=
        law₁.jointGoalMarginal.symm
      _ = law₂.joint.map (fun z : X × (G × Y) => (z.1, z.2.1)) := by rw [hjoint]
      _ = law₂.input ⊗ₘ law₂.goalGivenInput := law₂.jointGoalMarginal
  have hactionLaw : law₁.input ⊗ₘ law₁.actionGivenInput =
      law₂.input ⊗ₘ law₂.actionGivenInput := by
    calc
      law₁.input ⊗ₘ law₁.actionGivenInput =
          law₁.joint.map (fun z : X × (G × Y) => (z.1, z.2.2)) :=
        law₁.jointActionMarginal.symm
      _ = law₂.joint.map (fun z : X × (G × Y) => (z.1, z.2.2)) := by rw [hjoint]
      _ = law₂.input ⊗ₘ law₂.actionGivenInput := law₂.jointActionMarginal
  have hinput : law₁.input = law₂.input := by
    have hfst := congrArg MeasureTheory.Measure.fst hgoalLaw
    simpa using hfst
  have hgoalLaw' := hgoalLaw
  rw [← hinput] at hgoalLaw'
  have hactionLaw' := hactionLaw
  rw [← hinput] at hactionLaw'
  have hgoal : law₁.goalGivenInput =ᵐ[law₁.input] law₂.goalGivenInput :=
    ProbabilityTheory.Kernel.ae_eq_of_compProd_eq hgoalLaw'
  have haction : law₁.actionGivenInput =ᵐ[law₁.input] law₂.actionGivenInput :=
    ProbabilityTheory.Kernel.ae_eq_of_compProd_eq hactionLaw'
  exact ConditionalMutualInformationLaw.referenceMeasure_eq_of_kernels_ae_eq
    law₁ law₂ hinput hgoal haction

/-- The measure-theoretic definition of conditional mutual information as
`klDiv(P_{XGY}, P_X ⊗ P_{G|X} ⊗ P_{Y|X})`, when that KL divergence is finite.
The conditional kernels and their agreement with the joint law are explicit
data, so no regular-conditional-probability existence theorem is silently
assumed here.
日本語要約：条件付き核から構成した参照法則に対する有限KLダイバージェンスとして条件付き相互情報量を表す。-/
structure FiniteConditionalMutualInformationLaw
    (X G Y : Type*) [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    where
  distribution : ConditionalMutualInformationLaw X G Y
  finite : InformationTheory.klDiv distribution.joint
      distribution.referenceMeasure ≠ ⊤

/-- Forget the conditional-probability interpretation while retaining the
joint/reference measure pair and finite-KL certificate used by the general
capacity theorem.
日本語要約：条件付き相互情報量データを一般有限KL容量APIの測度対へ変換する。-/
noncomputable def FiniteConditionalMutualInformationLaw.toFiniteKLLaw
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y]
    (law : FiniteConditionalMutualInformationLaw X G Y) :
    FiniteKLDivergenceLaw (X × (G × Y)) := by
  letI : MeasureTheory.IsProbabilityMeasure law.distribution.input :=
    law.distribution.inputProbability
  letI : ProbabilityTheory.IsMarkovKernel law.distribution.goalGivenInput :=
    law.distribution.goalKernelMarkov
  letI : ProbabilityTheory.IsMarkovKernel law.distribution.actionGivenInput :=
    law.distribution.actionKernelMarkov
  exact ⟨law.distribution.joint, law.distribution.referenceMeasure, law.finite⟩

/-- Theorem 19/22 capacity monotonicity specialized to the KL definition of
conditional mutual information on measurable spaces. Each layer embedding
preserves the induced joint law and its conditional-independence reference
measure (packaged as equality of the resulting finite KL laws). A common
measurable alphabet is used across layers. The companion theorem
`capacity_nondecreasing_of_joint_preserving_conditional_mutual_information_embedding`
derives reference-measure preservation from joint-law preservation when the
input/output pair spaces are countably generated; construction of the kernels
from a given joint law remains a separate regularity/disintegration question.
日本語要約：条件付き独立参照測度をもつ一般測度CMIについて、KL法則対を保存する単射埋め込みから容量単調性を示す。-/
theorem capacity_nondecreasing_of_conditional_mutual_information_embedding
    {L A X G Y : Type*} [Preorder L]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (admissible : L → Set A)
    (law : A → FiniteConditionalMutualInformationLaw X G Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw) ''
        admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A → A)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x : A},
      x ∈ admissible a → embedding hab x ∈ admissible b)
    (hconditionalLawPreserving : ∀ {a b : L} (hab : a ≤ b) {x : A},
      x ∈ admissible a →
        (law (embedding hab x)).toFiniteKLLaw = (law x).toFiniteKLLaw)
    (a b : L) (hab : a ≤ b) :
    layerCapacity admissible
      (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw)) a ≤
    layerCapacity admissible
      (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw)) b := by
  exact capacity_nondecreasing_of_finite_kl_preserving_embedding
    admissible (fun x => (law x).toFiniteKLLaw) hnonempty hbounded embedding
    hinjective hmapsTo hconditionalLawPreserving a b hab

/-- If layers preserve the full joint law, then on countably generated input/output
spaces the conditional kernels are unique almost everywhere, so the induced
conditional-independence reference law and the CMI score are preserved too.
This derives the reference-law part of (22.6) rather than requiring it as an
independent embedding hypothesis.
日本語要約：可算生成性の下で条件付き核のほとんど至る所の一意性を使い、同時法則保存だけから条件付き独立参照法則とCMI容量スコアの保存を導く。-/
theorem capacity_nondecreasing_of_joint_preserving_conditional_mutual_information_embedding
    {L A X G Y : Type*} [Preorder L]
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X G]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (admissible : L → Set A)
    (law : A → FiniteConditionalMutualInformationLaw X G Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw) ''
        admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A → A)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x : A},
      x ∈ admissible a → embedding hab x ∈ admissible b)
    (hjointPreserving : ∀ {a b : L} (hab : a ≤ b) {x : A},
      x ∈ admissible a →
        (law (embedding hab x)).distribution.joint = (law x).distribution.joint)
    (a b : L) (hab : a ≤ b) :
    layerCapacity admissible
      (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw)) a ≤
    layerCapacity admissible
      (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw)) b := by
  let score : A → ℝ := fun x =>
    finiteKLDivergenceScore ((law x).toFiniteKLLaw)
  refine capacity_nondecreasing_of_embedding_condition
    admissible score hnonempty hbounded ?_ a b hab
  intro c d hcd x hx
  refine ⟨embedding hcd x, hmapsTo hcd hx, ?_⟩
  have hjoint := hjointPreserving hcd hx
  have href := ConditionalMutualInformationLaw.referenceMeasure_eq_of_joint_eq
    (law (embedding hcd x)).distribution (law x).distribution hjoint
  change (InformationTheory.klDiv
    (law (embedding hcd x)).distribution.joint
    (law (embedding hcd x)).distribution.referenceMeasure).toReal =
    (InformationTheory.klDiv (law x).distribution.joint
      (law x).distribution.referenceMeasure).toReal
  rw [hjoint, href]


end Tomabechi.Theorem22
