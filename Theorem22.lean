import Theorem21
import Tomabechi.Dynamics.StageData
import Tomabechi.Information.Capacity
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# 定理22：LUBの段階的蓄積と局所谷の帰結

本ファイルでは、順序論的な更新則と、各段階で必要となる解析・制御仮定を
分けて扱う。冒頭の補題はLUB更新を直接証明し、段階間の分離結果は定理23で
使う強凸性の帰結を与える。再利用する局所最小点・指数減衰の結果は定理21
からimportし、ここでは重複して証明しない。

切替状態が次段階の吸引域に入ること、切替軌道の存在・一意性、定理19の
容量埋め込みは明示的な接続条件として残す。これらはLUBの漸化式だけからは
従わない。
-/

open Tomabechi.Theorem21 RealInnerProductSpace Filter
open scoped Topology NNReal ProbabilityTheory

namespace Tomabechi.Theorem22

/-- A join update never removes previously accumulated information.
日本語要約：結合更新 (u\vee v) は既存情報 (u) を下回らない。 -/
theorem lub_update_is_monotone {L : Type*} [SemilatticeSup L]
    (u v : L) : u ≤ u ⊔ v := le_sup_left

/-- A genuinely new element makes the join update strictly increase.
日本語要約：新情報 (v\not\le u) があれば結合更新は厳密に上昇する。 -/
theorem lub_update_is_strict {L : Type*} [SemilatticeSup L]
    (u v : L) (hnew : ¬ v ≤ u) : u < u ⊔ v := by
  apply lt_of_le_of_ne le_sup_left
  intro heq
  apply hnew
  rw [heq]
  exact le_sup_right

/-- The converse identifies exactly when a join update is strict.
日本語要約：結合更新の厳密上昇と、新情報が既存LUBに包摂されないことは同値である。 -/
theorem lub_update_strict_iff {L : Type*} [SemilatticeSup L]
    (u v : L) : u < u ⊔ v ↔ ¬ v ≤ u := by
  constructor
  · intro h huv
    have heq : u ⊔ v = u := sup_eq_left.mpr huv
    apply (not_le_of_gt h)
    rw [heq]
  · exact lub_update_is_strict u v

/-- The indexed form of the order conclusion (22.3), including the trivial
upper bound by the lattice top.
日本語要約：更新式 (22.1) から段階順序、新情報による厳密上昇、最大元による上界を示す。 -/
theorem indexed_lub_step_order {L : Type*} [SemilatticeSup L] [OrderTop L]
    (u v : ℕ → L) (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1))
    (n : ℕ) :
    u n ≤ u (n + 1) ∧ u (n + 1) ≤ ⊤ ∧
      (¬ v (n + 1) ≤ u n → u n < u (n + 1)) := by
  rw [hupdate n]
  exact ⟨le_sup_left, le_top, fun hnew => lub_update_is_strict _ _ hnew⟩

/-- The join updates in (22.1) form a monotone sequence.
日本語要約：結合更新によりLUB段階列が単調であることを示す。 -/
theorem lub_stages_monotone {L : Type*} [SemilatticeSup L]
    (u v : ℕ → L) (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone u := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hupdate n]
  exact le_sup_left

/-- A monotone sequence is directed as a set.
日本語要約：単調列の値域は有向集合であることを証明する。 -/
theorem lub_stages_directed {L : Type*} [Preorder L]
    (u : ℕ → L) (hmono : Monotone u) :
    DirectedOn (· ≤ ·) (Set.range u) := by
  rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
  refine ⟨u (max i j), ⟨max i j, rfl⟩, ?_, ?_⟩
  · exact hmono (Nat.le_max_left i j)
  · exact hmono (Nat.le_max_right i j)

/-- In a directed-complete partial order with a top element, the increasing
LUB ladder has a least upper bound below top. This uses only directed
completeness, matching the source's weaker hypothesis rather than a complete
lattice assumption.
lattice assumption.
日本語要約：有向完備半順序では単調な段階列に上限が存在し、その上限は最大元以下である。 -/
theorem lub_stages_have_supremum_below_top {L : Type*}
    [CompletePartialOrder L] [OrderTop L] (u : ℕ → L)
    (hmono : Monotone u) :
    IsLUB (Set.range u) (sSup (Set.range u)) ∧ sSup (Set.range u) ≤ ⊤ := by
  have hdir := lub_stages_directed u hmono
  exact ⟨hdir.isLUB_sSup, le_top⟩

/-- The (22.1) join recurrence and Theorem 19's injective,
joint-law-preserving layer embeddings together make the capacity sequence
monotone. This is the indexed form of (22.6), rather than only a comparison
for one arbitrary pair of ordered layers.
日本語要約：(22.1) の全段階列について、各段の容量が単調非減少であることを示す。 -/
theorem capacity_monotone_along_lub_stages
    {L A Law : Type*} [SemilatticeSup L]
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
    (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone (fun n => layerCapacity admissible score (u n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hupdate n]
  exact capacity_nondecreasing_of_injective_law_preserving_embedding
    admissible jointLaw scoreOfLaw score hscore hnonempty hbounded
    embedding hinjective hmapsTo hlawPreserving (u n) (u n ⊔ v (n + 1))
    le_sup_left

/-- The measure-KL specialization of the indexed capacity statement (22.6).
For every join stage, the embedding preserves the joint and reference
measures of each admissible item; the resulting real KL-capacity is monotone.
日本語要約：LUB更新列に沿い、KL対保存埋め込みのもとで一般測度KL容量が単調となる。-/
theorem finite_kl_capacity_monotone_along_lub_stages
    {L A Ω : Type*} [SemilatticeSup L] [MeasurableSpace Ω]
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
    (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone (fun n =>
      layerCapacity admissible (finiteKLDivergenceScore ∘ law) (u n)) := by
  exact capacity_monotone_along_lub_stages
    admissible law finiteKLDivergenceScore (finiteKLDivergenceScore ∘ law)
    (fun _ => rfl) hnonempty hbounded embedding hinjective hmapsTo
    hlawPreserving u v hupdate

/-- The countably generated measure-CMI capacity is monotone along the full
join/LUB stage sequence under embeddings that preserve only the joint law.
Reference-law preservation is derived at each stage by conditional-kernel
uniqueness, then the pairwise monotonicity result is iterated over (22.1).
日本語要約：可算生成条件の下で同時法則保存のみから、(22.1) のLUB段階列に沿う一般測度CMI容量の単調性を示す。-/
theorem conditional_mutual_information_capacity_monotone_along_lub_stages
    {L A X G Y : Type*} [SemilatticeSup L]
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
    (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone (fun n => layerCapacity admissible
      (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw)) (u n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hupdate n]
  exact capacity_nondecreasing_of_joint_preserving_conditional_mutual_information_embedding
    admissible law hnonempty hbounded embedding hinjective hmapsTo hjointPreserving
    (u n) (u n ⊔ v (n + 1)) le_sup_left

/-- The order, capacity, and supremum conclusions of Theorem 22 specialized
to measure-theoretic conditional mutual information. This packages the join
stage order and the countably generated joint-law-preserving CMI capacity
monotonicity into one result.
日本語要約：可算生成条件の下、同時法則保存による一般測度CMI容量を用いて、定理22の段階順序・容量単調性・列上限を一括して示す。-/
theorem theorem22_order_conditional_mutual_information_and_supremum
    {L A X G Y : Type*} [CompleteLattice L]
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
    (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone u ∧
      (∀ n, u n ≤ u (n + 1) ∧
        (¬ v (n + 1) ≤ u n → u n < u (n + 1)) ∧
        u (n + 1) ≤ ⊤) ∧
      Monotone (fun n => layerCapacity admissible
        (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw)) (u n)) ∧
      IsLUB (Set.range u) (sSup (Set.range u)) ∧
      sSup (Set.range u) ≤ ⊤ := by
  have hmono : Monotone u := lub_stages_monotone u v hupdate
  have hcapacity := conditional_mutual_information_capacity_monotone_along_lub_stages
    admissible law hnonempty hbounded embedding hinjective hmapsTo hjointPreserving
    u v hupdate
  have hsup := lub_stages_have_supremum_below_top u hmono
  refine ⟨hmono, ?_, hcapacity, hsup.1, hsup.2⟩
  intro n
  have hstep := indexed_lub_step_order u v hupdate n
  exact ⟨hstep.1, hstep.2.2, hstep.2.1⟩

/-- The exact order-theoretic hypothesis stated in Theorem 22 is directed
completeness, not a complete lattice. This variant takes the binary join as
explicit data together with its least-upper-bound property, then combines the
LUB recurrence, measure-CMI capacity monotonicity, and the supremum of the
stage sequence under only a directed-complete partial order with top.
日本語要約：有向完備半順序と最大元、および最小上界として指定した二項結合の下で、更新・CMI容量単調性・列全体の上限を統合する。-/
theorem theorem22_order_conditional_mutual_information_and_supremum_of_dcpo
    {L A X G Y : Type*} [CompletePartialOrder L] [OrderTop L]
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
    (join : L → L → L)
    (hjoin : ∀ a b, IsLUB ({a, b} : Set L) (join a b))
    (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = join (u n) (v (n + 1))) :
    Monotone u ∧
      (∀ n, u n ≤ u (n + 1) ∧
        (¬ v (n + 1) ≤ u n → u n < u (n + 1)) ∧
        u (n + 1) ≤ ⊤) ∧
      Monotone (fun n => layerCapacity admissible
        (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw)) (u n)) ∧
      IsLUB (Set.range u) (sSup (Set.range u)) ∧
      sSup (Set.range u) ≤ ⊤ := by
  have hmono : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hupdate n]
    exact (hjoin (u n) (v (n + 1))).1 (by simp)
  have hcapacity : Monotone (fun n => layerCapacity admissible
      (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw)) (u n)) := by
    apply monotone_nat_of_le_succ
    intro n
    exact capacity_nondecreasing_of_joint_preserving_conditional_mutual_information_embedding
      admissible law hnonempty hbounded embedding hinjective hmapsTo hjointPreserving
      (u n) (u (n + 1)) (hmono (Nat.le_succ n))
  have hsup := lub_stages_have_supremum_below_top u hmono
  refine ⟨hmono, ?_, hcapacity, hsup.1, hsup.2⟩
  intro n
  have hjoin' := hjoin (u n) (v (n + 1))
  rw [hupdate n]
  have hleft : u n ≤ join (u n) (v (n + 1)) := hjoin'.1 (by simp)
  have hright : v (n + 1) ≤ join (u n) (v (n + 1)) := hjoin'.1 (by simp)
  refine ⟨hleft, ?_, le_top⟩
  intro hnew
  apply lt_of_le_of_ne hleft
  intro heq
  apply hnew
  have hright' : v (n + 1) ≤ u n := by
    rw [← heq] at hright
    exact hright
  exact hright'

/-- Order, capacity, and limiting-LUB conclusions of Theorem 22 in one
interface. The join recurrence gives (22.3); injective law-preserving
embeddings give the monotonicity in (22.6); directed completeness supplies
the supremum of the whole stage sequence, bounded above by `⊤`. No claim that
the supremum equals `⊤` is made without an additional cofinality assumption.
日本語要約：LUBの単調列、情報容量の単調性、列全体の上限が最大元以下にあることを統合する。最大元への到達は結論しない。 -/
theorem theorem22_order_capacity_and_supremum
    {L A Law : Type*} [CompleteLattice L]
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
    (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone u ∧
      (∀ n, u n ≤ u (n + 1) ∧
        (¬ v (n + 1) ≤ u n → u n < u (n + 1)) ∧
        u (n + 1) ≤ ⊤) ∧
      Monotone (fun n => layerCapacity admissible score (u n)) ∧
      IsLUB (Set.range u) (sSup (Set.range u)) ∧
      sSup (Set.range u) ≤ ⊤ := by
  have hmono : Monotone u := lub_stages_monotone u v hupdate
  have hcapacity := capacity_monotone_along_lub_stages
    admissible jointLaw scoreOfLaw score hscore hnonempty hbounded
    embedding hinjective hmapsTo hlawPreserving u v hupdate
  have hsup := lub_stages_have_supremum_below_top u hmono
  refine ⟨hmono, ?_, hcapacity, hsup.1, hsup.2⟩
  intro n
  have hstep := indexed_lub_step_order u v hupdate n
  exact ⟨hstep.1, hstep.2.2, hstep.2.1⟩

/-- Nonnegative scores give nonnegative layer capacity. Together with the
boundedness premise of the monotonicity theorem, this records the `[0,∞)`
value range required for the capacity in Theorem 19.
日本語要約：許容スコアが非負ならスコア上限としての容量も非負である。 -/
theorem layerCapacity_nonnegative_of_score_nonnegative
    {L A : Type*} (admissible : L → Set A) (score : A → ℝ)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove (score '' admissible a))
    (hscore_nonnegative : ∀ a x, x ∈ admissible a → 0 ≤ score x)
    (a : L) : 0 ≤ layerCapacity admissible score a := by
  obtain ⟨x, hx⟩ := hnonempty a
  change 0 ≤ sSup (score '' admissible a)
  calc
    0 ≤ score x := hscore_nonnegative a x hx
    _ ≤ sSup (score '' admissible a) :=
      le_csSup (hbounded a) ⟨x, hx, rfl⟩

/-- A finite-KL score is nonnegative because `klDiv` takes values in
`ℝ≥0∞`; finiteness makes its real-valued score meaningful, and the nonempty,
bounded score family then gives the nonnegative capacity required in (22.6).
日本語要約：有限KLスコアの非負性から、一般測度KL容量が非負であることを導く。 -/
theorem finite_kl_capacity_nonnegative
    {L A Ω : Type*} [MeasurableSpace Ω]
    (admissible : L → Set A) (law : A → FiniteKLDivergenceLaw Ω)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a,
      BddAbove (finiteKLDivergenceScore ∘ law '' admissible a))
    (a : L) :
    0 ≤ layerCapacity admissible (finiteKLDivergenceScore ∘ law) a := by
  apply layerCapacity_nonnegative_of_score_nonnegative
    admissible (finiteKLDivergenceScore ∘ law) hnonempty hbounded
  intro a' x hx
  exact ENNReal.toReal_nonneg

/-- Measure-theoretic conditional mutual information is a finite-KL score,
so its capacity is nonnegative under the same nonemptiness and finite-capacity
conditions stated in Theorem 19. This completes the `[0,∞)` range condition
for the general measurable CMI specialization of (22.6).
日本語要約：一般測度CMI容量が原文の値域 [0,∞) に入ることを示す。 -/
theorem conditional_mutual_information_capacity_nonnegative
    {L A X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G]
    [MeasurableSpace Y]
    (admissible : L → Set A)
    (law : A → FiniteConditionalMutualInformationLaw X G Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw) ''
        admissible a))
    (a : L) :
    0 ≤ layerCapacity admissible
      (finiteKLDivergenceScore ∘ (fun x => (law x).toFiniteKLLaw)) a := by
  exact finite_kl_capacity_nonnegative admissible
    (fun x => (law x).toFiniteKLLaw) hnonempty hbounded a

/-- Specialize layer capacity to the finite-goal conditional-mutual-information
API from Theorem 21. Problems share finite `X`, `G`, and `Y` alphabets here.
This is narrower than Theorem 19's varying problem spaces, so the fully
general score-based result above remains the general interface.
日本語要約：有限ゴール・有限問題空間で条件付き相互情報量を用いる層容量を定義する。 -/
noncomputable def finiteGoalLayerCapacity
    {L A X G Y : Type*} [Fintype X] [Fintype G]
    (admissible : L → Set A) (mass : A → X → G → ℝ)
    (policy : A → X → G → Y) (a : L) : ℝ :=
  layerCapacity admissible
    (fun q => Tomabechi.Theorem21.finiteConditionalMutualInformation
      (mass q) (policy q)) a

/-- The joint law of the finite context, goal, and deterministic output.
日本語要約：有限モデルの問題・ゴール・決定論的出力の同時質量を定義する。-/
noncomputable def finiteGoalJointLaw
    {X G Y : Type*}
    (mass : X → G → ℝ) (policy : X → G → Y) : X → G → Y → ℝ := by
  classical
  exact fun x g y => if policy x g = y then mass x g else 0

/-- Conditional mutual information written only in terms of a finite joint law
of `(X,G,Y)`. This makes the score depend on the observable law rather than on
policy values at zero-mass `(x,g)` pairs. -/
-- 日本語要約：有限同時法則から条件付き相互情報量を計算する。
noncomputable def finiteConditionalMutualInformationOfJointLaw
    {X G Y : Type*} [Fintype X] [Fintype G] [Fintype Y]
    (law : X → G → Y → ℝ) : ℝ := by
  classical
  exact
    (∑ x : X, ∑ g : G,
      Tomabechi.Theorem21.finiteConditionalEntropyTerm
        (∑ y : Y, law x g y)
        (∑ g' : G, ∑ y : Y, law x g' y)) -
    (∑ x : X, ∑ g : G, ∑ y : Y,
      Tomabechi.Theorem21.finiteConditionalEntropyTerm
        (law x g y) (∑ g' : G, law x g' y))

/-- The existing finite `(mass, policy)` definition of conditional mutual
information factors through the induced `(X,G,Y)` joint law. Consequently,
preserving that law is sufficient to preserve the score even when the
deterministic policy changes on zero-mass inputs.
日本語要約：有限条件付き相互情報量が誘導同時法則だけで定まり、零質量入力での政策値を保存せずとも法則保存からスコア保存を導ける。-/
theorem finiteConditionalMutualInformation_factors_through_jointLaw
    {X G Y : Type*} [Fintype X] [Fintype G] [Fintype Y]
    (mass : X → G → ℝ) (policy : X → G → Y) :
    Tomabechi.Theorem21.finiteConditionalMutualInformation mass policy =
      finiteConditionalMutualInformationOfJointLaw
        (finiteGoalJointLaw mass policy) := by
  classical
  unfold Tomabechi.Theorem21.finiteConditionalMutualInformation
    Tomabechi.Theorem21.finiteConditionalEntropyGivenInput
    Tomabechi.Theorem21.finiteConditionalEntropyGivenInputAndOutput
    finiteConditionalMutualInformationOfJointLaw
  simp only [finiteGoalJointLaw]
  have houtput (x : X) (g : G) :
      (∑ y : Y,
        Tomabechi.Theorem21.finiteConditionalEntropyTerm
          (if policy x g = y then mass x g else 0)
          (∑ g' : G, if policy x g' = y then mass x g' else 0)) =
        Tomabechi.Theorem21.finiteConditionalEntropyTerm (mass x g)
          (∑ g' : G,
            if policy x g' = policy x g then mass x g' else 0) := by
    rw [Finset.sum_eq_single_of_mem (policy x g) (Finset.mem_univ _)
      (by
        intro y hy hne
        simp [Ne.symm hne,
          Tomabechi.Theorem21.finiteConditionalEntropyTerm])]
    rw [if_pos rfl]
  have hmass (x : X) (g : G) :
      (∑ y : Y, if policy x g = y then mass x g else 0) = mass x g := by
    rw [Finset.sum_eq_single_of_mem (policy x g) (Finset.mem_univ _)
      (by
        intro y hy hne
        simp [Ne.symm hne])]
    rw [if_pos rfl]
  have htotal (x : X) :
      (∑ g' : G, ∑ y : Y,
        if policy x g' = y then mass x g' else 0) =
        ∑ g' : G, mass x g' := by
    apply Finset.sum_congr rfl
    intro g' hg'
    rw [Finset.sum_eq_single_of_mem (policy x g') (Finset.mem_univ _)
      (by
        intro y hy hne
        simp [Ne.symm hne])]
    rw [if_pos rfl]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro g hg
    rw [hmass, htotal]
  · apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro g hg
    exact (houtput x g).symm

/-- A finite-goal capacity version of (22.6) whose embedding premise preserves
only the induced joint law. It therefore allows a deterministic policy to
change on inputs of zero mass, matching the distribution-level condition in
Theorem 19.
日本語要約：誘導された問題・ゴール・出力の同時法則だけを保存する層間単射から容量単調性を導く。-/
theorem finite_goal_capacity_nondecreasing_of_joint_distribution_preserving_embedding
    {L A X G Y : Type*} [Preorder L] [Fintype X] [Fintype G] [Fintype Y]
    (admissible : L → Set A) (mass : A → X → G → ℝ)
    (policy : A → X → G → Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun q => Tomabechi.Theorem21.finiteConditionalMutualInformation
        (mass q) (policy q)) '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A → A)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hpreserves : ∀ {a b : L} (hab : a ≤ b) (q : A),
      q ∈ admissible a → embedding hab q ∈ admissible b ∧
        finiteGoalJointLaw (mass (embedding hab q)) (policy (embedding hab q)) =
          finiteGoalJointLaw (mass q) (policy q))
    (a b : L) (hab : a ≤ b) :
    finiteGoalLayerCapacity admissible mass policy a ≤
      finiteGoalLayerCapacity admissible mass policy b := by
  classical
  let jointLaw : A → X → G → Y → ℝ := fun q =>
    finiteGoalJointLaw (mass q) (policy q)
  let scoreOfLaw : (X → G → Y → ℝ) → ℝ :=
    finiteConditionalMutualInformationOfJointLaw
  let score : A → ℝ := fun q =>
    Tomabechi.Theorem21.finiteConditionalMutualInformation (mass q) (policy q)
  have hscore : ∀ q, score q = scoreOfLaw (jointLaw q) := by
    intro q
    exact finiteConditionalMutualInformation_factors_through_jointLaw
      (mass q) (policy q)
  have hmapsTo : ∀ {a' b' : L} (hab' : a' ≤ b') {q : A},
      q ∈ admissible a' → embedding hab' q ∈ admissible b' := by
    intro a' b' hab' q hq
    exact (hpreserves hab' q hq).1
  change layerCapacity admissible score a ≤ layerCapacity admissible score b
  exact capacity_nondecreasing_of_injective_law_preserving_embedding
    admissible jointLaw scoreOfLaw score hscore hnonempty hbounded
    embedding hinjective hmapsTo
    (by
      intro a' b' hab' q hq
      exact (hpreserves hab' q hq).2)
    a b hab

/-- For a finite goal alphabet, normalized nonnegative joint masses bound the
capacity score by `card G`; hence the set of admissible scores is bounded
above without a separate finiteness premise.
日本語要約：有限ゴール上の確率モデルから容量の上限を評価する。 -/
theorem finite_goal_capacity_bounded_of_probability_mass
    {L A X G Y : Type*} [Fintype X] [Fintype G]
    (admissible : L → Set A) (mass : A → X → G → ℝ)
    (policy : A → X → G → Y)
    (hnormalized : ∀ a q, q ∈ admissible a →
      (∑ x : X, ∑ g : G, mass q x g) = 1)
    (hmass_nonneg : ∀ a q, q ∈ admissible a → ∀ x g,
      0 ≤ mass q x g)
    (a : L) : BddAbove
      ((fun q => Tomabechi.Theorem21.finiteConditionalMutualInformation
        (mass q) (policy q)) '' admissible a) := by
  refine ⟨(Fintype.card G : ℝ), ?_⟩
  rintro score ⟨q, hq, rfl⟩
  have hbound := Tomabechi.Theorem21.finiteConditionalMutualInformation_le_card_mul_total
    (mass q) (policy q) (fun x g => hmass_nonneg a q hq x g)
  rw [hnormalized a q hq] at hbound
  simpa using hbound

/-- Distribution-preserving embeddings make the finite-goal capacity
nondecreasing when source and target problems use the same finite alphabets.
The premise preserves the joint model in a strict coordinatewise form
(conditional masses and deterministic action map); the conclusion then follows
by rewriting the Theorem 21 information score and applying the supremum
monotonicity argument. Injectivity is retained from the source assumption,
although the score monotonicity argument itself only needs range inclusion.
日本語要約：同一有限アルファベットで分布を保存する段階間埋め込みから容量単調性を導く。 -/
theorem finite_goal_capacity_nondecreasing_of_distribution_preserving_embedding
    {L A X G Y : Type*} [Preorder L] [Fintype X] [Fintype G]
    (admissible : L → Set A) (mass : A → X → G → ℝ)
    (policy : A → X → G → Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun q => Tomabechi.Theorem21.finiteConditionalMutualInformation
        (mass q) (policy q)) '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A → A)
    (_hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hpreserves : ∀ {a b : L} (hab : a ≤ b) (x : A), x ∈ admissible a →
      embedding hab x ∈ admissible b ∧ mass (embedding hab x) = mass x ∧
        policy (embedding hab x) = policy x)
    (a b : L) (hab : a ≤ b) :
    finiteGoalLayerCapacity admissible mass policy a ≤
      finiteGoalLayerCapacity admissible mass policy b := by
  let ModelLaw := (X → G → ℝ) × (X → G → Y)
  let jointModel : A → ModelLaw := fun q => (mass q, policy q)
  let modelScore : ModelLaw → ℝ := fun law =>
    Tomabechi.Theorem21.finiteConditionalMutualInformation law.1 law.2
  let score : A → ℝ := fun q =>
    Tomabechi.Theorem21.finiteConditionalMutualInformation (mass q) (policy q)
  have hscore : ∀ q, score q = modelScore (jointModel q) := by
    intro q
    rfl
  have hmapsTo : ∀ {a' b' : L} (hab' : a' ≤ b') {q : A},
      q ∈ admissible a' → embedding hab' q ∈ admissible b' := by
    intro a' b' hab' q hq
    exact (hpreserves hab' q hq).1
  have hlawPreserving : ∀ {a' b' : L} (hab' : a' ≤ b') {q : A},
      q ∈ admissible a' → jointModel (embedding hab' q) = jointModel q := by
    intro a' b' hab' q hq
    obtain ⟨_, hmass, hpolicy⟩ := hpreserves hab' q hq
    exact Prod.ext hmass hpolicy
  change layerCapacity admissible score a ≤ layerCapacity admissible score b
  exact capacity_nondecreasing_of_injective_law_preserving_embedding
    admissible jointModel modelScore score hscore hnonempty hbounded
    embedding _hinjective hmapsTo hlawPreserving a b hab

/-- Distribution-preserving embeddings make normalized finite-goal capacity
nondecreasing without assuming score boundedness separately. Normalization
and nonnegative masses give the uniform upper bound `card G`, and the finite
conditional-mutual-information lemma supplies the score preservation.
日本語要約：確率正規化の仮定を用いて有限ゴール容量の単調性を得る。 -/
theorem finite_goal_capacity_nondecreasing_of_probability_embedding
    {L A X G Y : Type*} [Preorder L] [Fintype X] [Fintype G]
    (admissible : L → Set A) (mass : A → X → G → ℝ)
    (policy : A → X → G → Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hnormalized : ∀ a q, q ∈ admissible a →
      (∑ x : X, ∑ g : G, mass q x g) = 1)
    (hmass_nonneg : ∀ a q, q ∈ admissible a → ∀ x g,
      0 ≤ mass q x g)
    (embedding : ∀ {a b : L}, a ≤ b → A → A)
    (hinjective : ∀ {a b : L} (hab : a ≤ b), Function.Injective (embedding hab))
    (hpreserves : ∀ {a b : L} (hab : a ≤ b) (x : A), x ∈ admissible a →
      embedding hab x ∈ admissible b ∧ mass (embedding hab x) = mass x ∧
        policy (embedding hab x) = policy x)
    (a b : L) (hab : a ≤ b) :
    finiteGoalLayerCapacity admissible mass policy a ≤
      finiteGoalLayerCapacity admissible mass policy b := by
  apply finite_goal_capacity_nondecreasing_of_distribution_preserving_embedding
    admissible mass policy hnonempty
    (fun a' => finite_goal_capacity_bounded_of_probability_mass admissible mass
      policy hnormalized hmass_nonneg a')
    embedding hinjective hpreserves a b hab

/-- The finite-goal conditional-mutual-information capacity is monotone along
the information-accumulating LUB stages. This directly combines (22.1) with
the probability-model instance of (22.6), including the normalization bound
that makes every stage capacity well-defined.
日本語要約：情報蓄積LUB列に沿う有限ゴール容量の単調非減少性を示す。 -/
theorem finite_goal_capacity_monotone_along_lub_stages
    {L A X G Y : Type*} [SemilatticeSup L] [Fintype X] [Fintype G]
    (admissible : L → Set A) (mass : A → X → G → ℝ)
    (policy : A → X → G → Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hnormalized : ∀ a q, q ∈ admissible a →
      (∑ x : X, ∑ g : G, mass q x g) = 1)
    (hmass_nonneg : ∀ a q, q ∈ admissible a → ∀ x g,
      0 ≤ mass q x g)
    (embedding : ∀ {a b : L}, a ≤ b → A → A)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hpreserves : ∀ {a b : L} (hab : a ≤ b) (x : A),
      x ∈ admissible a →
        embedding hab x ∈ admissible b ∧ mass (embedding hab x) = mass x ∧
          policy (embedding hab x) = policy x)
    (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone (fun n => finiteGoalLayerCapacity admissible mass policy (u n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hupdate n]
  exact finite_goal_capacity_nondecreasing_of_probability_embedding
    admissible mass policy hnonempty hnormalized hmass_nonneg
    embedding hinjective hpreserves (u n) (u n ⊔ v (n + 1)) le_sup_left

/-- The stagewise version of finite (22.6) with preservation stated only for
the induced `(X,G,Y)` joint law. Normalized nonnegative masses provide the
uniform score bound needed to define every layer capacity.
日本語要約：同時法則保存だけを仮定し、LUB更新列に沿う有限ゴール容量の単調性を示す。-/
theorem finite_goal_capacity_monotone_along_lub_stages_of_joint_distribution_preserving_embedding
    {L A X G Y : Type*} [SemilatticeSup L] [Fintype X] [Fintype G] [Fintype Y]
    (admissible : L → Set A) (mass : A → X → G → ℝ)
    (policy : A → X → G → Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hnormalized : ∀ a q, q ∈ admissible a →
      (∑ x : X, ∑ g : G, mass q x g) = 1)
    (hmass_nonneg : ∀ a q, q ∈ admissible a → ∀ x g,
      0 ≤ mass q x g)
    (embedding : ∀ {a b : L}, a ≤ b → A → A)
    (hinjective : ∀ {a b : L} (hab : a ≤ b),
      Function.Injective (embedding hab))
    (hpreserves : ∀ {a b : L} (hab : a ≤ b) (q : A),
      q ∈ admissible a → embedding hab q ∈ admissible b ∧
        finiteGoalJointLaw (mass (embedding hab q)) (policy (embedding hab q)) =
          finiteGoalJointLaw (mass q) (policy q))
    (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone (fun n => finiteGoalLayerCapacity admissible mass policy (u n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hupdate n]
  exact finite_goal_capacity_nondecreasing_of_joint_distribution_preserving_embedding
    admissible mass policy hnonempty
    (fun a => finite_goal_capacity_bounded_of_probability_mass admissible mass
      policy hnormalized hmass_nonneg a)
    embedding hinjective hpreserves (u n) (u n ⊔ v (n + 1)) le_sup_left

/-- The finite-goal layer capacity is nonnegative once every admissible
problem-policy pair has nonnegative conditional mutual information. For a
concrete Theorem 19 instance, this is the separate information-theoretic
obligation; the layer-supremum argument itself is purely order theoretic.
日本語要約：各許容問題・方策対でスコア非負なら層容量も非負である。 -/
theorem finite_goal_capacity_nonnegative
    {L A X G Y : Type*} [Fintype X] [Fintype G]
    (admissible : L → Set A) (mass : A → X → G → ℝ)
    (policy : A → X → G → Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun q => Tomabechi.Theorem21.finiteConditionalMutualInformation
        (mass q) (policy q)) '' admissible a))
    (hinformation_nonnegative : ∀ a q, q ∈ admissible a →
      0 ≤ Tomabechi.Theorem21.finiteConditionalMutualInformation
        (mass q) (policy q))
    (a : L) : 0 ≤ finiteGoalLayerCapacity admissible mass policy a := by
  exact layerCapacity_nonnegative_of_score_nonnegative admissible
    (fun q => Tomabechi.Theorem21.finiteConditionalMutualInformation
      (mass q) (policy q)) hnonempty hbounded hinformation_nonnegative a

/-- In the finite-goal specialization, nonnegative joint masses suffice for
nonnegative conditional mutual information and hence nonnegative layer
capacity. This discharges the score nonnegativity premise from the concrete
probability model; boundedness of the score image remains explicit.
日本語要約：非負の正規化質量から有限ゴール容量の非負性を導く。 -/
theorem finite_goal_capacity_nonnegative_of_mass
    {L A X G Y : Type*} [Fintype X] [Fintype G]
    (admissible : L → Set A) (mass : A → X → G → ℝ)
    (policy : A → X → G → Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove
      ((fun q => Tomabechi.Theorem21.finiteConditionalMutualInformation
        (mass q) (policy q)) '' admissible a))
    (hmass_nonneg : ∀ a q, q ∈ admissible a → ∀ x g,
      0 ≤ mass q x g)
    (a : L) : 0 ≤ finiteGoalLayerCapacity admissible mass policy a := by
  apply finite_goal_capacity_nonnegative admissible mass policy hnonempty hbounded
  · intro a' q hq
    exact Tomabechi.Theorem21.finiteConditionalMutualInformation_nonneg
      (mass q) (policy q) (fun x g => hmass_nonneg a' q hq x g)

/-- Under probability normalization, finite-goal layer capacity is both
nonnegative and at most the number of goals. Thus the score supremum is a
finite real quantity in this common finite-alphabet specialization.
日本語要約：確率正規化の下で有限ゴール容量が非負かつゴール数以下であることを示す。 -/
theorem finite_goal_capacity_probability_range
    {L A X G Y : Type*} [Fintype X] [Fintype G]
    (admissible : L → Set A) (mass : A → X → G → ℝ)
    (policy : A → X → G → Y)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hnormalized : ∀ a q, q ∈ admissible a →
      (∑ x : X, ∑ g : G, mass q x g) = 1)
    (hmass_nonneg : ∀ a q, q ∈ admissible a → ∀ x g,
      0 ≤ mass q x g)
    (a : L) :
    0 ≤ finiteGoalLayerCapacity admissible mass policy a ∧
      finiteGoalLayerCapacity admissible mass policy a ≤ Fintype.card G := by
  let score := fun q => Tomabechi.Theorem21.finiteConditionalMutualInformation
    (mass q) (policy q)
  have hbounded := finite_goal_capacity_bounded_of_probability_mass
    admissible mass policy hnormalized hmass_nonneg a
  have hnonemptyScore : (score '' admissible a).Nonempty :=
    (hnonempty a).image score
  have hLUB : IsLUB (score '' admissible a)
      (sSup (score '' admissible a)) :=
    isLUB_csSup hnonemptyScore (by simpa [score] using hbounded)
  have hscore_le : ∀ z ∈ score '' admissible a,
      z ≤ (Fintype.card G : ℝ) := by
    rintro z ⟨q, hq, rfl⟩
    have h := Tomabechi.Theorem21.finiteConditionalMutualInformation_le_card_mul_total
      (mass q) (policy q) (fun x g => hmass_nonneg a q hq x g)
    rw [hnormalized a q hq] at h
    simpa using h
  constructor
  · exact finite_goal_capacity_nonnegative_of_mass admissible mass policy
      hnonempty (fun a' => finite_goal_capacity_bounded_of_probability_mass
        admissible mass policy hnormalized hmass_nonneg a') hmass_nonneg a
  · change sSup (score '' admissible a) ≤ (Fintype.card G : ℝ)
    exact hLUB.2 hscore_le

/-- The dwell-time bound (22.5) is sufficient for the exponential distance
estimate to fall below ε. This is a scalar consequence of the quantitative
rate, independent of the switched-system existence assumptions.
日本語要約：指数距離評価に対し、対数待ち時間 (22.5) が指定誤差への到達に十分と示す。 -/
theorem dwell_time_suffices_for_error
    (C epsilon gamma c T : ℝ)
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hgamma : 0 < gamma) (hc : 0 < c)
    (hT : max 0 (1 / (gamma * c) * Real.log (C / epsilon)) ≤ T) :
    C * Real.exp (-gamma * c * T) ≤ epsilon := by
  by_cases hepsilonC : epsilon < C
  · have hCpos : 0 < C := lt_trans hepsilon hepsilonC
    have hratio : 1 < C / epsilon := (one_lt_div hepsilon).2 hepsilonC
    have hlog : 0 < Real.log (C / epsilon) := Real.log_pos hratio
    have hrate : 0 < gamma * c := mul_pos hgamma hc
    have hquotient : 0 < 1 / (gamma * c) * Real.log (C / epsilon) :=
      mul_pos (one_div_pos.mpr hrate) hlog
    have hmax : max 0 (1 / (gamma * c) * Real.log (C / epsilon)) =
        1 / (gamma * c) * Real.log (C / epsilon) := max_eq_right hquotient.le
    have hlogbound : Real.log (C / epsilon) / (gamma * c) ≤ T := by
      have h := le_trans (le_of_eq hmax.symm) hT
      simpa [one_div, div_eq_mul_inv, mul_comm] using h
    have hscaled : Real.log (C / epsilon) ≤ (gamma * c) * T := by
      calc
        Real.log (C / epsilon) ≤ T * (gamma * c) :=
          (div_le_iff₀ hrate).mp hlogbound
        _ = (gamma * c) * T := by ring
    have harg : -gamma * c * T ≤ -Real.log (C / epsilon) := by
      nlinarith
    have hexp : Real.exp (-gamma * c * T) ≤
        Real.exp (-Real.log (C / epsilon)) := Real.exp_le_exp.mpr harg
    calc
      C * Real.exp (-gamma * c * T) ≤
          C * Real.exp (-Real.log (C / epsilon)) :=
        mul_le_mul_of_nonneg_left hexp hCpos.le
      _ = epsilon := by
        rw [Real.exp_neg, Real.exp_log (div_pos hCpos hepsilon)]
        field_simp
  · have hCT : C ≤ epsilon := le_of_not_gt hepsilonC
    have hTnonneg : 0 ≤ T := le_trans (le_max_left 0
      (1 / (gamma * c) * Real.log (C / epsilon))) hT
    have hexp : Real.exp (-gamma * c * T) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hrate : 0 ≤ gamma * c := (mul_pos hgamma hc).le
      nlinarith
    calc
      C * Real.exp (-gamma * c * T) ≤ C := by
        calc
          C * Real.exp (-gamma * c * T) ≤ C * 1 :=
            mul_le_mul_of_nonneg_left hexp hC
          _ = C := mul_one C
      _ ≤ epsilon := hCT

/-- Combine the waiting-time condition (22.5) with an exponential trajectory
estimate: after waiting at least the logarithmic dwell time, the state is
within `epsilon` of the stage minimizer. The trajectory estimate can be
instantiated by Theorem 21's quantitative state-distance conclusion.
日本語要約：待ち時間 (22.5) を満たせば指数減衰軌道が許容誤差内に入ることを導く。 -/
theorem exponential_distance_reaches_error_after_dwell
    {E : Type*} [PseudoMetricSpace E]
    (trajectory : ℝ → E) (xstar : E) (t₀ T C epsilon gamma c : ℝ)
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hgamma : 0 < gamma) (hc : 0 < c)
    (hT : max 0 (1 / (gamma * c) * Real.log (C / epsilon)) ≤ T)
    (hdecay : dist (trajectory (t₀ + T)) xstar ≤
      C * Real.exp (-gamma * c * T)) :
    dist (trajectory (t₀ + T)) xstar ≤ epsilon :=
  le_trans hdecay (dwell_time_suffices_for_error C epsilon gamma c T
    hC hepsilon hgamma hc hT)

/-- During a dwell interval, an actual switched trajectory inherits the
uninterrupted stage's energy estimate while both trajectories solve the same
stage dynamics with the same initial value. Equality on the interval is an
explicit premise here: deriving it requires the source's uniqueness theorem
for the switched closed-loop ODE.
日本語要約：dwell上の実軌道・凍結軌道の一致を使い、指数減衰評価を実軌道に移す。 -/
theorem switched_stage_gap_decay_of_freeze_agreement
    {E : Type*} (actual free : ℝ → E) (potential : E → ℝ)
    (xstar : E) (t₀ T c gamma : ℝ)
    (hT : 0 ≤ T)
    (hmatch : ∀ τ ∈ Set.Icc 0 T, actual (t₀ + τ) = free (t₀ + τ))
    (hfreeDecay : ∀ τ ∈ Set.Icc 0 T,
      potential (free (t₀ + τ)) - potential xstar ≤
        Real.exp (-2 * gamma * c * τ) *
          (potential (free t₀) - potential xstar)) :
    ∀ τ ∈ Set.Icc 0 T,
      potential (actual (t₀ + τ)) - potential xstar ≤
        Real.exp (-2 * gamma * c * τ) *
          (potential (actual t₀) - potential xstar) := by
  intro τ hτ
  have hstart : actual t₀ = free t₀ := by
    simpa using hmatch 0 ⟨le_rfl, hT⟩
  rw [hmatch τ hτ, hstart]
  exact hfreeDecay τ hτ

/-- Derive agreement of the actual and frozen-stage trajectories from the
same-stage ODE and the closed-ball uniqueness theorem in Theorem 21. This is
the finite-dimensional local uniqueness step used for the switch interval;
the endpoint is excluded by `Ico` and is obtained separately by continuity.
日本語要約：同じ閉ループODEと初期値に対する一意性で切替前まで二軌道を一致させる。 -/
theorem switched_orbits_agree_before_endpoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E → E →L[ℝ] E) (gradient : E → E) (center : E)
    (r t₀ T : ℝ)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (gradient y))) x)
    (actual free : ℝ → E)
    (hactualBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      actual t ∈ Metric.closedBall center r)
    (hfreeBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      free t ∈ Metric.closedBall center r)
    (hactualFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt actual (-(A (actual t) (gradient (actual t)))) t)
    (hfreeFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt free (-(A (free t) (gradient (free t)))) t)
    (hinit : actual t₀ = free t₀) :
    Set.EqOn actual free (Set.Ico t₀ (t₀ + T) : Set ℝ) := by
  exact Tomabechi.Theorem21.theorem21_state_dependent_closed_loop_unique_on_ball
    A gradient center r t₀ (t₀ + T) hfieldC1 actual free
    hactualBall hfreeBall hactualFlow hfreeFlow hinit

/-- Continuity extends equality of two trajectories from `[a,b)` to the
switching instant `b`.
日本語要約：半開区間での一致は右端連続性により切替時刻まで延長できる。 -/
theorem eq_at_right_endpoint_of_eqOn_Ico
    {E : Type*} [TopologicalSpace E] [T2Space E]
    (f g : ℝ → E) (a b : ℝ) (hab : a < b)
    (heq : Set.EqOn f g (Set.Ico a b))
    (hf : ContinuousAt f b) (hg : ContinuousAt g b) : f b = g b := by
  have hleft : Set.Ioi a ∈ 𝓝 b := Ioi_mem_nhds hab
  have hnear : Set.Iio b ∩ Set.Ioi a ∈ 𝓝[Set.Iio b] b :=
    inter_mem_nhdsWithin _ hleft
  have heventually : f =ᶠ[𝓝[Set.Iio b] b] g := by
    filter_upwards [hnear] with t ht
    exact heq ⟨le_of_lt ht.2, ht.1⟩
  have hf' : Tendsto f (𝓝[Set.Iio b] b) (𝓝 (f b)) :=
    hf.mono_left nhdsWithin_le_nhds
  have hg' : Tendsto g (𝓝[Set.Iio b] b) (𝓝 (g b)) :=
    hg.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique_of_eventuallyEq hf' hg' heventually

/-- The ODE uniqueness result plus continuity at the switching instant gives
agreement on the full closed dwell interval.
日本語要約：一意性による区間内部の一致と終端連続性を合わせ閉dwell全体で同定する。 -/
theorem switched_orbits_agree_on_closed_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E → E →L[ℝ] E) (gradient : E → E) (center : E)
    (r t₀ T : ℝ) (hT : 0 < T)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (gradient y))) x)
    (actual free : ℝ → E)
    (hactualBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      actual t ∈ Metric.closedBall center r)
    (hfreeBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      free t ∈ Metric.closedBall center r)
    (hactualFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt actual (-(A (actual t) (gradient (actual t)))) t)
    (hfreeFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt free (-(A (free t) (gradient (free t)))) t)
    (hinit : actual t₀ = free t₀)
    (hactualCont : ContinuousAt actual (t₀ + T))
    (hfreeCont : ContinuousAt free (t₀ + T)) :
    Set.EqOn actual free (Set.Icc t₀ (t₀ + T)) := by
  have heqIco := switched_orbits_agree_before_endpoint A gradient center r t₀ T
    hfieldC1 actual free hactualBall hfreeBall hactualFlow hfreeFlow hinit
  intro t ht
  by_cases htb : t < t₀ + T
  · exact heqIco ⟨ht.1, htb⟩
  · have hteq : t = t₀ + T := le_antisymm ht.2 (le_of_not_gt htb)
    subst t
    exact eq_at_right_endpoint_of_eqOn_Ico actual free t₀ (t₀ + T)
      (by linarith) heqIco hactualCont hfreeCont

/-- Switched-orbit uniqueness with the one-sided derivative that is natural
at a switching time. The paths need only be continuous on the dwell interval,
and solve the ODE with a right derivative on `[t₀,t₁)`; no two-sided
derivative is imposed at the initial switch.
日本語要約：切替開始点では右微分だけを仮定し、連続性とdwell内のODEから閉区間全体の軌道一致を示す。-/
theorem switched_orbits_agree_on_closed_interval_of_right_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E) (center : E) (r t₀ t₁ : ℝ) (L : ℝ≥0)
    (hL : LipschitzOnWith L field (Metric.closedBall center r))
    (actual frozen : ℝ → E)
    (hactualBall : ∀ t ∈ Set.Ico t₀ t₁,
      actual t ∈ Metric.closedBall center r)
    (hfrozenBall : ∀ t ∈ Set.Ico t₀ t₁,
      frozen t ∈ Metric.closedBall center r)
    (hactualContinuous : ContinuousOn actual (Set.Icc t₀ t₁))
    (hfrozenContinuous : ContinuousOn frozen (Set.Icc t₀ t₁))
    (hactualFlow : ∀ t ∈ Set.Ico t₀ t₁,
      HasDerivWithinAt actual (field (actual t)) (Set.Ici t) t)
    (hfrozenFlow : ∀ t ∈ Set.Ico t₀ t₁,
      HasDerivWithinAt frozen (field (frozen t)) (Set.Ici t) t)
    (hinitial : actual t₀ = frozen t₀) :
    Set.EqOn actual frozen (Set.Icc t₀ t₁) := by
  exact ODE_solution_unique_of_mem_Icc_right
    (fun _ _ => hL) hactualContinuous hactualFlow hactualBall
    hfrozenContinuous hfrozenFlow hfrozenBall hinitial

/-- Dimension-free version of switched-orbit agreement when a Lipschitz
constant for the closed-loop field is supplied directly. The finite-dimensional
corollary above derives this bound from C¹ regularity on a compact closed ball;
in a general normed space, local C¹ regularity alone does not provide a uniform
Lipschitz constant on a noncompact ball.
日本語要約：一般ノルム空間で場のLipschitz定数を仮定した次元非依存の一意性版。 -/
theorem switched_orbits_agree_on_closed_interval_of_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E) (center : E) (r t₀ T : ℝ) (L : ℝ≥0)
    (hT : 0 < T)
    (hL : LipschitzOnWith L field (Metric.closedBall center r))
    (actual free : ℝ → E)
    (hactualBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      actual t ∈ Metric.closedBall center r)
    (hfreeBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      free t ∈ Metric.closedBall center r)
    (hactualFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt actual (field (actual t)) t)
    (hfreeFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt free (field (free t)) t)
    (hinit : actual t₀ = free t₀)
    (hactualCont : ContinuousAt actual (t₀ + T))
    (hfreeCont : ContinuousAt free (t₀ + T)) :
    Set.EqOn actual free (Set.Icc t₀ (t₀ + T)) := by
  have heqIco := Tomabechi.Theorem21.ode_trajectories_eqOn_Ico_of_lipschitz_on_closedBall
    field center r t₀ (t₀ + T) L hL actual free hactualBall hfreeBall
    hactualFlow hfreeFlow hinit
  intro t ht
  by_cases htb : t < t₀ + T
  · exact heqIco ⟨ht.1, htb⟩
  · have hteq : t = t₀ + T := le_antisymm ht.2 (le_of_not_gt htb)
    subst t
    exact eq_at_right_endpoint_of_eqOn_Ico actual free t₀ (t₀ + T)
      (by linarith) heqIco hactualCont hfreeCont

/-- Dimension-free transfer of a frozen-stage energy estimate to the actual
switched solution, assuming a direct Lipschitz bound for the vector field.
日本語要約：直接仮定したLipschitz性から軌道一致を証明し凍結軌道の指数評価を移す。 -/
theorem switched_stage_gap_decay_from_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E) (center : E) (r t₀ T gamma c : ℝ) (L : ℝ≥0)
    (hT : 0 < T)
    (hL : LipschitzOnWith L field (Metric.closedBall center r))
    (actual free : ℝ → E) (potential : E → ℝ) (xstar : E)
    (hactualBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      actual t ∈ Metric.closedBall center r)
    (hfreeBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      free t ∈ Metric.closedBall center r)
    (hactualFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt actual (field (actual t)) t)
    (hfreeFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt free (field (free t)) t)
    (hinit : actual t₀ = free t₀)
    (hactualCont : ContinuousAt actual (t₀ + T))
    (hfreeCont : ContinuousAt free (t₀ + T))
    (hfreeDecay : ∀ t ∈ Set.Icc t₀ (t₀ + T),
      potential (free t) - potential xstar ≤
        Real.exp (-2 * gamma * c * (t - t₀)) *
          (potential (free t₀) - potential xstar)) :
    ∀ t ∈ Set.Icc t₀ (t₀ + T),
      potential (actual t) - potential xstar ≤
        Real.exp (-2 * gamma * c * (t - t₀)) *
          (potential (actual t₀) - potential xstar) := by
  have hagree := switched_orbits_agree_on_closed_interval_of_lipschitz
    field center r t₀ T L hT hL actual free hactualBall hfreeBall
    hactualFlow hfreeFlow hinit hactualCont hfreeCont
  have hstart : actual t₀ = free t₀ := hagree ⟨le_rfl, by linarith⟩
  intro t ht
  rw [hagree ht, hstart]
  exact hfreeDecay t ht

/-- The frozen-stage exponential estimate transfers to the actual switched
trajectory throughout the dwell interval before its endpoint. Unlike the
abstract agreement lemma above, this derives trajectory agreement from the
shared ODE, C¹ field, closed-ball containment, and same initial value.
日本語要約：有限次元のC¹場に対するODE一意性を使ってdwell上の指数評価を移す。 -/
theorem switched_stage_gap_decay_from_ode_uniqueness
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E → E →L[ℝ] E) (gradient : E → E) (center : E)
    (r t₀ T c gamma : ℝ) (hT : 0 < T)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (gradient y))) x)
    (actual free : ℝ → E) (potential : E → ℝ) (xstar : E)
    (hactualBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      actual t ∈ Metric.closedBall center r)
    (hfreeBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      free t ∈ Metric.closedBall center r)
    (hactualFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt actual (-(A (actual t) (gradient (actual t)))) t)
    (hfreeFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt free (-(A (free t) (gradient (free t)))) t)
    (hinit : actual t₀ = free t₀)
    (hactualCont : ContinuousAt actual (t₀ + T))
    (hfreeCont : ContinuousAt free (t₀ + T))
    (hfreeDecay : ∀ t ∈ Set.Icc t₀ (t₀ + T),
      potential (free t) - potential xstar ≤
        Real.exp (-2 * gamma * c * (t - t₀)) *
          (potential (free t₀) - potential xstar)) :
    ∀ t ∈ Set.Icc t₀ (t₀ + T),
      potential (actual t) - potential xstar ≤
        Real.exp (-2 * gamma * c * (t - t₀)) *
          (potential (actual t₀) - potential xstar) := by
  have hagree := switched_orbits_agree_on_closed_interval A gradient center r t₀ T
    hT hfieldC1 actual free hactualBall hfreeBall hactualFlow hfreeFlow hinit
    hactualCont hfreeCont
  have hstart : actual t₀ = free t₀ := hagree ⟨le_rfl, by linarith⟩
  intro t ht
  rw [hagree ht, hstart]
  exact hfreeDecay t ht

/-- End-to-end interface for (22.4): a stage estimate on the frozen orbit
(for example, the second conjunct of `per_stage_exponential_decay`) and
finite-dimensional ODE uniqueness imply the same quantitative estimate for
the actual switched orbit throughout the closed dwell interval.
日本語要約：凍結段階の指数評価と実軌道とのdwell一致から実軌道の評価を導く。 -/
theorem switched_stage_gap_decay_from_stage_estimate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E → E →L[ℝ] E) (gradient : E → E) (center : E)
    (r t₀ T c gamma : ℝ) (hT : 0 < T)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (gradient y))) x)
    (actual free : ℝ → E) (potential : E → ℝ) (xstar : E)
    (hactualBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      actual t ∈ Metric.closedBall center r)
    (hfreeBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      free t ∈ Metric.closedBall center r)
    (hactualFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt actual (-(A (actual t) (gradient (actual t)))) t)
    (hfreeFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt free (-(A (free t) (gradient (free t)))) t)
    (hinit : actual t₀ = free t₀)
    (hactualCont : ContinuousAt actual (t₀ + T))
    (hfreeCont : ContinuousAt free (t₀ + T))
    (hstageEstimate : ∀ t, t₀ ≤ t →
      potential (free t) - potential xstar ≤
        Real.exp (-2 * gamma * c * (t - t₀)) *
          (potential (free t₀) - potential xstar)) :
    ∀ t ∈ Set.Icc t₀ (t₀ + T),
      potential (actual t) - potential xstar ≤
        Real.exp (-2 * gamma * c * (t - t₀)) *
          (potential (actual t₀) - potential xstar) := by
  apply switched_stage_gap_decay_from_ode_uniqueness A gradient center r t₀ T
    c gamma hT hfieldC1 actual free potential xstar hactualBall hfreeBall
    hactualFlow hfreeFlow hinit hactualCont hfreeCont
  intro t ht
  exact hstageEstimate t ht.1

/-- Apply (22.5) to the actual switched state at the end of the dwell
interval. The frozen-stage distance estimate is transferred by finite-
dimensional ODE uniqueness, with continuity supplying agreement at the right
endpoint.
日本語要約：凍結軌道との一致と待ち時間条件から、実切替軌道の切替時誤差を評価する。 -/
theorem switched_state_reaches_error_after_dwell
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E → E →L[ℝ] E) (gradient : E → E) (center : E)
    (r t₀ T C epsilon gamma c : ℝ) (hT : 0 < T)
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hgamma : 0 < gamma) (hc : 0 < c)
    (hwait : max 0 (1 / (gamma * c) * Real.log (C / epsilon)) ≤ T)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (gradient y))) x)
    (actual free : ℝ → E) (xstar : E)
    (hactualBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      actual t ∈ Metric.closedBall center r)
    (hfreeBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      free t ∈ Metric.closedBall center r)
    (hactualFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt actual (-(A (actual t) (gradient (actual t)))) t)
    (hfreeFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivAt free (-(A (free t) (gradient (free t)))) t)
    (hinit : actual t₀ = free t₀)
    (hactualCont : ContinuousAt actual (t₀ + T))
    (hfreeCont : ContinuousAt free (t₀ + T))
    (hfreeDistance : ∀ t ∈ Set.Icc t₀ (t₀ + T),
      dist (free t) xstar ≤ C * Real.exp (-gamma * c * (t - t₀))) :
    dist (actual (t₀ + T)) xstar ≤ epsilon := by
  have hagree := switched_orbits_agree_on_closed_interval A gradient center r
    t₀ T hT hfieldC1 actual free hactualBall hfreeBall hactualFlow hfreeFlow
    hinit hactualCont hfreeCont
  have hendpoint : t₀ + T ∈ Set.Icc t₀ (t₀ + T) := ⟨by linarith, le_rfl⟩
  rw [hagree hendpoint]
  have hrate := hfreeDistance (t₀ + T) hendpoint
  have htime : (t₀ + T) - t₀ = T := by ring
  rw [htime] at hrate
  exact le_trans hrate (dwell_time_suffices_for_error C epsilon gamma c T
    hC hepsilon hgamma hc hwait)

/-- The potential gap at the next stage excludes the preceding minimizer from
the next stage's sublevel set. The strict gap estimate is exposed as a premise:
the paper derives it from strong convexity along the segment between minimizers.
This interface avoids silently assuming the Hessian-to-strong-convexity step.
日本語要約：強凸性による段階間ポテンシャル差が次段閾値を超えると旧最小点を排除する。 -/
theorem previous_minimizer_outside_next_sublevel
    {X : Type*} (potential : ℕ → X → ℝ) (xstar : ℕ → X)
    (theta c delta : ℝ) (n : ℕ)
    (hthreshold : theta < c / 2 * delta ^ 2)
    (hgap : c / 2 * delta ^ 2 ≤
      potential (n + 1) (xstar n) - potential (n + 1) (xstar (n + 1))) :
    xstar n ∉ {x : X | potential (n + 1) x -
      potential (n + 1) (xstar (n + 1)) ≤ theta} := by
  change ¬ (potential (n + 1) (xstar n) -
    potential (n + 1) (xstar (n + 1)) ≤ theta)
  linarith

/-- If the old minimizer belongs to the old reachable TCZ and the next-stage
strong-convexity gap excludes it from the new TCZ, the two TCZ sets differ.
日本語要約：旧最小点の旧TCZ所属と次段TCZからの排除により隣接TCZの不一致を示す。 -/
theorem stage_tcz_changes
    {X : Type*} (tcz : ℕ → Set X) (xstar : ℕ → X) (n : ℕ)
    (hold : xstar n ∈ tcz n) (hnew : xstar n ∉ tcz (n + 1)) :
    tcz (n + 1) ≠ tcz n := by
  intro heq
  have : xstar n ∈ tcz (n + 1) := by simpa [heq] using hold
  exact hnew this

end Tomabechi.Theorem22
