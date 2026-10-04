import Theorem22

/-!
# 定理19：ゴール条件付き制御容量

定理22にある共通型のスコア容量APIを、抽象度ごとに異なる問題型を持つ
依存型族へ拡張する。層間の単射・許容性・評価保存から容量単調性を導き、
束の端点、有限ゴール条件付き相互情報量への適用、端点正規化を整理する。

このファイルの抽象核は「容量を定理19のCMIと同一視する」ものではない。
CMIスコアおよびその問題ごとの分布・有限性条件は入力データである。
-/

open Tomabechi.Theorem22

namespace Tomabechi.Theorem19

/-- 各抽象度で問題型自体が異なる許容問題・方策対のスコア上限。 -/
noncomputable def dependentLayerCapacity
    {L : Type*} [Preorder L] (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (score : ∀ a, A a → ℝ) (a : L) : ℝ :=
  sSup (score a '' admissible a)

/-- 問題型の異なる層でも、評価値を保つ単射によって容量は減少しない。
原文19の単射条件を保ち、問題族・方策族をまとめた対を `A a` とする。 -/
theorem dependentCapacity_nondecreasing_of_scorePreservingEmbedding
    {L : Type*} [Preorder L] (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (score : ∀ a, A a → ℝ)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove (score a '' admissible a))
    (embedding : ∀ {a b}, a ≤ b → A a → A b)
    (_hinjective : ∀ {a b} (hab : a ≤ b), Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hscore : ∀ {a b} (hab : a ≤ b) {x}, x ∈ admissible a →
      score b (embedding hab x) = score a x)
    (a b : L) (hab : a ≤ b) :
    dependentLayerCapacity A admissible score a ≤
      dependentLayerCapacity A admissible score b := by
  let Ia := score a '' admissible a
  let Ib := score b '' admissible b
  have hne : Ia.Nonempty := (hnonempty a).image (score a)
  have hlub : IsLUB Ia (sSup Ia) := isLUB_csSup hne (by simpa [Ia] using hbounded a)
  have hbound : ∀ x ∈ Ia, x ≤ sSup Ib := by
    rintro y ⟨x, hx, rfl⟩
    have hy : score b (embedding hab x) ∈ Ib :=
      ⟨embedding hab x, hmapsTo hab hx, rfl⟩
    calc
      score a x = score b (embedding hab x) := (hscore hab hx).symm
      _ ≤ sSup Ib := le_csSup (hbounded b) hy
  change sSup Ia ≤ sSup Ib
  exact hlub.2 hbound

/-- 原文の `0` と `⊤` が容量の最小値・最大値を与えることを、
単調性から端点比較として述べる。 -/
theorem bottom_top_capacity_bounds
    {L : Type*} [CompleteLattice L] (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (score : ∀ a, A a → ℝ)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove (score a '' admissible a))
    (embedding : ∀ {a b}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b} (hab : a ≤ b), Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hscore : ∀ {a b} (hab : a ≤ b) {x}, x ∈ admissible a →
      score b (embedding hab x) = score a x) (a : L) :
    dependentLayerCapacity A admissible score ⊥ ≤
        dependentLayerCapacity A admissible score a ∧
      dependentLayerCapacity A admissible score a ≤
        dependentLayerCapacity A admissible score ⊤ := by
  constructor
  · exact dependentCapacity_nondecreasing_of_scorePreservingEmbedding
      A admissible score hnonempty hbounded embedding hinjective hmapsTo hscore
      ⊥ a bot_le
  · exact dependentCapacity_nondecreasing_of_scorePreservingEmbedding
      A admissible score hnonempty hbounded embedding hinjective hmapsTo hscore
      a ⊤ le_top

/-- 物理層の全問題で条件付きゴールエントロピーが零なら、
各問題の `I(G;Y|X) ≤ H(G|X)` という情報不等式から容量も零となる。
この抽象版では、有限ゴールCMIの不等式と零エントロピーを明示入力にする。 -/
theorem zeroCapacity_of_zeroGoalEntropy
    {A : Type*} (admissible : Set A) (score entropy : A → ℝ)
    (hnonempty : admissible.Nonempty) (hbounded : BddAbove (score '' admissible))
    (hscore_nonneg : ∀ x ∈ admissible, 0 ≤ score x)
    (hscore_le_entropy : ∀ x ∈ admissible, score x ≤ entropy x)
    (hentropy_zero : ∀ x ∈ admissible, entropy x = 0) :
    sSup (score '' admissible) = 0 := by
  apply le_antisymm
  · apply csSup_le (hnonempty.image score)
    rintro y ⟨x, hx, rfl⟩
    have h := hscore_le_entropy x hx
    rw [hentropy_zero x hx] at h
    exact h
  · obtain ⟨x, hx⟩ := hnonempty
    have hmem : score x ∈ score '' admissible := ⟨x, hx, rfl⟩
    exact (hscore_nonneg x hx).trans (le_csSup hbounded hmem)

/-- 正の端点差のもとでの両端固定アフィン正規化。 -/
noncomputable def endpointNormalization (lo hi x : ℝ) : ℝ :=
  (x - lo) / (hi - lo)

theorem endpointNormalization_values (lo hi : ℝ) (h : lo < hi) :
    endpointNormalization lo hi lo = 0 ∧
    endpointNormalization lo hi hi = 1 := by
  constructor
  · simp [endpointNormalization]
  · simp [endpointNormalization, sub_ne_zero.mpr (ne_of_gt h)]

/-- 両端の容量差が正なら、原文19のアフィン正規化は容量値について厳密増加。 -/
theorem endpointNormalization_strictMono (lo hi : ℝ) (h : lo < hi) :
    StrictMono (endpointNormalization lo hi) := by
  intro x y hxy
  exact (div_lt_div_iff_of_pos_right (sub_pos.mpr h)).mpr (sub_lt_sub_right hxy lo)

/-- 端点を0と1へ写すアフィン関数は一意。
正容量を含む原文の正規化における「一意」の内容を明示する。 -/
theorem endpointAffine_unique (lo hi : ℝ) (h : lo < hi)
    (f : ℝ → ℝ) (hf : ∃ m c, ∀ x, f x = m * x + c)
    (hlo : f lo = 0) (hhi : f hi = 1) :
    ∀ x, f x = endpointNormalization lo hi x := by
  obtain ⟨m, c, hlin⟩ := hf
  have hm : m = 1 / (hi - lo) := by
    have hhi' : m * hi + c = 1 := by rw [← hlin hi, hhi]
    have hlo' : m * lo + c = 0 := by rw [← hlin lo, hlo]
    have hmul : m * (hi - lo) = 1 := by nlinarith
    exact (eq_div_iff (sub_ne_zero.mpr (ne_of_gt h))).2 (by nlinarith [hmul])
  intro x
  rw [hlin x, hm]
  have hc : c = -lo / (hi - lo) := by
    have hlo' : m * lo + c = 0 := by rw [← hlin lo, hlo]
    rw [hm] at hlo'
    field_simp at hlo'
    field_simp
    linarith
  rw [hc]
  unfold endpointNormalization
  ring

/-- 問題dとその型に依存する方策πの許容対。各問題の方策集合は空でもよい。 -/
def admissibleProblemPolicyPairs
    {D : Type*} (Policy : D → Type*) (problems : Set D)
    (policies : ∀ d, Set (Policy d)) : Set (Σ d, Policy d) :=
  {q | q.1 ∈ problems ∧ q.2 ∈ policies q.1}

/-- 原文19の問題/方策二重上限と許容対上限の同定。
非負スコア・全許容対の非空性・有限容量だけを使う。各問題の方策非空性は要求せず、
空の内側集合の実数sSup=0を全体容量の非負性で扱う。 -/
theorem problemPolicy_doubleSup_eq_pairSup
    {D : Type*} (Policy : D → Type*) (problems : Set D)
    (policies : ∀ d, Set (Policy d)) (score : ∀ d, Policy d → ℝ)
    (hnonempty : (admissibleProblemPolicyPairs Policy problems policies).Nonempty)
    (hbounded : BddAbove ((fun q : Σ d, Policy d => score q.1 q.2) ''
      admissibleProblemPolicyPairs Policy problems policies))
    (hscoreNonneg : ∀ d, d ∈ problems → ∀ p, p ∈ policies d → 0 ≤ score d p) :
    sSup ((fun d => sSup (score d '' policies d)) '' problems) =
      sSup ((fun q : Σ d, Policy d => score q.1 q.2) ''
        admissibleProblemPolicyPairs Policy problems policies) := by
  let pairs := admissibleProblemPolicyPairs Policy problems policies
  let scores := (fun q : Σ d, Policy d => score q.1 q.2) '' pairs
  let capacity := sSup scores
  obtain ⟨q₀, hq₀⟩ := hnonempty
  have hpairScoresNonempty : scores.Nonempty := ⟨_, q₀, hq₀, rfl⟩
  have hcapacityNonneg : 0 ≤ capacity :=
    (hscoreNonneg q₀.1 hq₀.1 q₀.2 hq₀.2).trans
      (le_csSup hbounded ⟨q₀, hq₀, rfl⟩)
  have hfiberBounded : ∀ d, d ∈ problems → BddAbove (score d '' policies d) := by
    intro d hd
    apply hbounded.mono
    rintro r ⟨p, hp, rfl⟩
    exact ⟨⟨d, p⟩, ⟨hd, hp⟩, rfl⟩
  have hfiberLe : ∀ d, d ∈ problems → sSup (score d '' policies d) ≤ capacity := by
    intro d hd
    rcases Set.eq_empty_or_nonempty (policies d) with hempty | hne
    · rw [hempty, Set.image_empty, Real.sSup_empty]
      exact hcapacityNonneg
    · apply csSup_le (hne.image (score d))
      rintro r ⟨p, hp, rfl⟩
      exact le_csSup hbounded ⟨⟨d, p⟩, ⟨hd, hp⟩, rfl⟩
  have houterNonempty : ((fun d => sSup (score d '' policies d)) '' problems).Nonempty :=
    ⟨_, q₀.1, hq₀.1, rfl⟩
  have houterBounded : BddAbove ((fun d => sSup (score d '' policies d)) '' problems) := by
    refine ⟨capacity, ?_⟩
    rintro r ⟨d, hd, rfl⟩
    exact hfiberLe d hd
  apply le_antisymm
  · apply csSup_le houterNonempty
    rintro r ⟨d, hd, rfl⟩
    exact hfiberLe d hd
  · apply csSup_le hpairScoresNonempty
    rintro r ⟨q, hq, rfl⟩
    exact (le_csSup (hfiberBounded q.1 hq.1) ⟨q.2, hq.2, rfl⟩).trans
      (le_csSup houterBounded ⟨q.1, hq.1, rfl⟩)

end Tomabechi.Theorem19

#print axioms Tomabechi.Theorem19.problemPolicy_doubleSup_eq_pairSup
#print axioms Tomabechi.Theorem19.endpointNormalization_strictMono
