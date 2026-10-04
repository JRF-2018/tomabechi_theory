import Theorem16_25_Core

/-!
# 定理25の Python 例 (`examples/theorem25_no_self.py`) の Lean 根拠

(A) 履歴 h∈{0,1,2} ごとの縮小写像 `F_h(S)=(1-L)c_h+L S`（L=3/5）: 各 `F_h` は縮小で唯一固定点 `c_h`、
    `c_0≠c_1` なので全履歴共通の固定点は存在しない（定理25 (25.1) の量化）。
    一般定理 `theorem25_no_common_fixedPoint_of_historyFamily` を使う。
(B) 候補自性Σ: 外生 Γ∈{0,1}²（一様）、候補 s∈ℤ、出力 `Y=Γ₁-Γ₂+β s`。構造因果モデル
    `Theorem25StructuralCausalModel` の do(Σ=s) 法則で、β=0 なら 25-D（法則不変）→ Atman なし
    （`theorem25_secondConclusion_of_functionalCompleteness`）、β=1 なら 25-D が破れて Atman が成立。
    ※ Python の連続ノイズ版を、有限値・決定論的な形に置き換えた（対応表参照）。
(C) 父・母・子の逆役割関係（25.C1）と水平グラフの連結性: 有限グラフで `decide`。
-/

namespace Tomabechi.Examples.Theorem25

open Tomabechi.Theorem16_25

/-! ## (A) 履歴相対の固定点 -/

/-- Python の `c = {0:[0.1,0.9], 1:[0.8,0.2], 2:[0.5,0.5]}`。 -/
noncomputable def c : Fin 3 → ℝ × ℝ := ![(1 / 10, 9 / 10), (4 / 5, 1 / 5), (1 / 2, 1 / 2)]

/-- Python の `F(h,S)=(1-L)c_h+L S`、L=0.6。 -/
noncomputable def F (h : Fin 3) (S : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - 3 / 5) * (c h).1 + 3 / 5 * S.1, (1 - 3 / 5) * (c h).2 + 3 / 5 * S.2)

theorem F_contracting (h : Fin 3) : ContractingWith (3 / 5 : NNReal) (F h) := by
  refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, ?_⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [F, Prod.dist_eq, Real.dist_eq, NNReal.coe_div, NNReal.coe_ofNat]
  have h1 : |(1 - 3 / 5) * (c h).1 + 3 / 5 * x.1 - ((1 - 3 / 5) * (c h).1 + 3 / 5 * y.1)| =
      3 / 5 * |x.1 - y.1| := by
    rw [show (1 - 3 / 5) * (c h).1 + 3 / 5 * x.1 - ((1 - 3 / 5) * (c h).1 + 3 / 5 * y.1) =
      3 / 5 * (x.1 - y.1) by ring, abs_mul]; norm_num
  have h2 : |(1 - 3 / 5) * (c h).2 + 3 / 5 * x.2 - ((1 - 3 / 5) * (c h).2 + 3 / 5 * y.2)| =
      3 / 5 * |x.2 - y.2| := by
    rw [show (1 - 3 / 5) * (c h).2 + 3 / 5 * x.2 - ((1 - 3 / 5) * (c h).2 + 3 / 5 * y.2) =
      3 / 5 * (x.2 - y.2) by ring, abs_mul]; norm_num
  rw [h1, h2, ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 5)]

theorem F_fixed_iff (h : Fin 3) (S : ℝ × ℝ) : F h S = S ↔ S = c h := by
  constructor
  · intro hS
    have h1 := congrArg Prod.fst hS
    have h2 := congrArg Prod.snd hS
    simp only [F] at h1 h2
    exact Prod.ext (by linarith) (by linarith)
  · rintro rfl
    refine Prod.ext ?_ ?_ <;> simp only [F] <;> ring

/-- 履歴別の唯一固定点族（担体は全空間）。 -/
noncomputable def historyFixedPoints : HistoryFixedPoints (Fin 3) (ℝ × ℝ) where
  carrier := fun _ _ => True
  feedback := fun h y => ⟨F h y.1, trivial⟩
  fixedPoint := fun h => ⟨c h, trivial⟩
  isFixed := fun h => Subtype.ext ((F_fixed_iff h (c h)).2 rfl)
  unique := fun h y hy => Subtype.ext ((F_fixed_iff h y.1).1 (congrArg Subtype.val hy))

/-- (25.1): 履歴 0 と 1 の固定点は異なり、全履歴に共通する固定点は存在しない。 -/
theorem no_common_fixedPoint :
    c 0 ≠ c 1 ∧
      ¬ ∃ s : ℝ × ℝ, ∃ hmem : ∀ h, historyFixedPoints.carrier h s,
        ∀ h, historyFixedPoints.feedback h ⟨s, hmem h⟩ = ⟨s, hmem h⟩ := by
  have hsep : c 0 ≠ c 1 := by
    intro h
    have := congrArg Prod.fst h
    norm_num [c] at this
  exact ⟨hsep, theorem25_no_common_fixedPoint_of_historyFamily
    (h₁ := 0) (h₂ := 1) historyFixedPoints (by simpa [historyFixedPoints] using hsep)⟩

/-! ## (B) 候補自性Σと条件25-D（有限値SCM） -/

/-- 外生 Γ∈{0,1}² の一様確率測度。 -/
noncomputable def uniformGamma : MeasureTheory.ProbabilityMeasure (Bool × Bool) :=
  ⟨(PMF.uniformOfFintype (Bool × Bool)).toMeasure, inferInstance⟩

/-- 真偽値の指示関数（整数）。 -/
def ind (b : Bool) : ℤ := if b then 1 else 0

/-- Python の SCM `Y = Γ₁ - Γ₂ + β Σ`（ノイズなし・有限値版）。基準の候補は Σ=0。 -/
noncomputable def scm (β : ℤ) :
    Theorem25StructuralCausalModel Unit Unit Unit (Bool × Bool)
      (fun _ : Unit => Bool × Bool) (fun _ : Unit => ℤ) (fun _ : Unit => ℤ) :=
  { defaultCandidate := fun _ => 0
    exogenousLaw := fun _ _ => uniformGamma
    stateEquation := fun _ _ _ u _ => u
    outputEquation := fun _ _ _ u s => ind u.1 - ind u.2 + β * s
    baselineJointAEMeasurable := fun _ _ _ => (measurable_of_finite _).aemeasurable
    intervenedJointAEMeasurable := fun _ _ _ _ => (measurable_of_finite _).aemeasurable
    independentFixedIndividualization := fun _ _ _ => True }

/-- β=0: do(Σ=s) は (Γ,Y) の同時法則を変えない（25-D の操作的形式）。 -/
theorem scm_zero_functionallyComplete :
    ((scm 0).toProbabilityCausalModel.toCausalModel).FunctionallyComplete := by
  intro d a h s
  simp [Theorem25ProbabilityCausalModel.toCausalModel,
    Theorem25StructuralCausalModel.toProbabilityCausalModel, scm]

/-- β=0: 25-D のもとで Atman は成立しない（定理25 (25.2) の因果コア）。 -/
theorem scm_zero_no_atman : ∀ d a, ¬ ((scm 0).toProbabilityCausalModel.toCausalModel).hasAtman d a :=
  theorem25_secondConclusion_of_functionalCompleteness _ scm_zero_functionallyComplete

/-- β=1: do(Σ=2) で `{Y=2}` の確率が 0 から正に変わる（25-D が破れる）。 -/
theorem scm_one_law_changes :
    ((scm 1).toProbabilityCausalModel.toCausalModel).intervenedLaw () () () 2 ≠
      ((scm 1).toProbabilityCausalModel.toCausalModel).baselineLaw () () () := by
  intro h
  have hA : MeasurableSet {x : (Bool × Bool) × ℤ | x.2 = 2} :=
    measurable_snd (measurableSet_singleton 2)
  have h' := congrArg
    (fun μ : MeasureTheory.ProbabilityMeasure ((Bool × Bool) × ℤ) =>
      MeasureTheory.ProbabilityMeasure.toMeasure μ {x | x.2 = 2}) h
  simp only [Theorem25ProbabilityCausalModel.toCausalModel] at h'
  rw [Theorem25StructuralCausalModel.intervenedJointLaw_apply _ _ _ _ _ _ hA,
    Theorem25StructuralCausalModel.baselineJointLaw_apply _ _ _ _ _ hA] at h'
  have hbase : ((fun u : Bool × Bool => (u, ind u.1 - ind u.2 + 1 * (0 : ℤ))) ⁻¹'
      {x : (Bool × Bool) × ℤ | x.2 = 2}) = ∅ := by
    ext u; rcases u with ⟨a, b⟩; cases a <;> cases b <;> simp [ind]
  have hint : ({(false, false)} : Set (Bool × Bool)) ⊆
      ((fun u : Bool × Bool => (u, ind u.1 - ind u.2 + 1 * (2 : ℤ))) ⁻¹'
        {x : (Bool × Bool) × ℤ | x.2 = 2}) := by
    intro u hu; simp at hu; subst hu; simp [ind]
  have hpos : 0 < MeasureTheory.ProbabilityMeasure.toMeasure uniformGamma {(false, false)} := by
    change 0 < (PMF.uniformOfFintype (Bool × Bool)).toMeasure {(false, false)}
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp
  simp only [scm] at h'
  rw [hbase] at h'
  have := lt_of_lt_of_le hpos (MeasureTheory.measure_mono hint)
  rw [MeasureTheory.measure_empty] at h'
  exact (ne_of_gt this) h'

/-- β=1: Atman（独立・固定的な候補自性＋非冗長な因果効果）が成立する。25-D なしでは無我は出ない。 -/
theorem scm_one_has_atman :
    ((scm 1).toProbabilityCausalModel.toCausalModel).hasAtman () () :=
  ⟨2, trivial, (), scm_one_law_changes⟩

/-! ## (C) 父・母・子の逆役割関係と水平グラフの連結性（有限グラフ） -/

/-- 頂点: 0=祖父, 1=父, 2=母, 3=子, 4=叔母, 5=祖母（Python の `people` と同じ）。 -/
abbrev Person := Fin 6

/-- Python の `father_of = {(祖父,父),(父,子)}`。 -/
def FatherOf (f c : Person) : Prop := (f, c) = (0, 1) ∨ (f, c) = (1, 3)

/-- Python の `mother_of = {(母,子),(祖母,叔母)}`。 -/
def MotherOf (m c : Person) : Prop := (m, c) = (2, 3) ∨ (m, c) = (5, 4)

/-- 逆役割ラベル: `HasFather c f ⇔ FatherOf f c`（25.C1、同一関係の逆向き記述）。 -/
def HasFather (c f : Person) : Prop := FatherOf f c

theorem fatherOf_iff_hasFather (f c : Person) : FatherOf f c ↔ HasFather c f := Iff.rfl

/-- 水平関係グラフの隣接（父母子辺に、叔母と父の関係辺を1本加えたもの。無向化）。 -/
def adj (a b : Person) : Prop :=
  (a, b) = (0, 1) ∨ (a, b) = (1, 3) ∨ (a, b) = (2, 3) ∨ (a, b) = (5, 4) ∨ (a, b) = (1, 4) ∨
  (b, a) = (0, 1) ∨ (b, a) = (1, 3) ∨ (b, a) = (2, 3) ∨ (b, a) = (5, 4) ∨ (b, a) = (1, 4)

/-- (25.C2): 水平関係グラフは連結（祖父から全員へ有限経路がある）。 -/
theorem relation_graph_connected : ∀ v : Person, Relation.ReflTransGen adj 0 v := by
  have e01 : adj 0 1 := by simp [adj]
  have e13 : adj 1 3 := by simp [adj]
  have e14 : adj 1 4 := by simp [adj]
  have e45 : adj 4 5 := by simp [adj]
  have e32 : adj 3 2 := by simp [adj]
  have h1 : Relation.ReflTransGen adj 0 1 := .single e01
  intro v
  fin_cases v
  · exact .refl
  · exact h1
  · exact h1.tail e13 |>.tail e32
  · exact h1.tail e13
  · exact h1.tail e14
  · exact h1.tail e14 |>.tail e45

/-- (25.C4): 出生をもつ子（3）には父と母がいる。 -/
theorem child_has_father_and_mother : ∃ f m : Person, FatherOf f 3 ∧ MotherOf m 3 :=
  ⟨1, 2, Or.inr rfl, Or.inl rfl⟩

end Tomabechi.Examples.Theorem25
