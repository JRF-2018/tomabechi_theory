import Theorem19_22

/-!
# 定理19の問題別アルファベットと問題/方策二重上限

原文の各問題・方策対には、独自の文脈型・有限離散ゴール型・出力型を許す。
個別lawのKL型CMIとエントロピー評価を再利用して容量を構成する。
問題族全体で共通の有限ゴール集合や一様ゴール数を要求しない。
層間の評価保存と有限容量は原文の独立条件として保持する。
-/

open MeasureTheory ProbabilityTheory Tomabechi.Theorem22

namespace Tomabechi.Theorem19_Heterogeneous

universe u v w

/-- 実数への変換前のKL容量が有限なら、各許容lawも有限KLを持つ。
問題ごとにX/G/Y型が異なってよい。原文の有限容量から有限law証明を取り出す入口で、
∞.toReal=0を有限性の代用にせず、拡張非負実数の上限を先に評価する。 -/
noncomputable def finiteMeasureCMILawOfFiniteCapacity
    {Q : Type*} (X G Y : Q → Type*)
    [∀ q, MeasurableSpace (X q)] [∀ q, MeasurableSpace (G q)]
    [∀ q, MeasurableSpace (Y q)]
    (law : ∀ q, ConditionalMutualInformationLaw (X q) (G q) (Y q))
    (admissible : Set Q)
    (hcapacity : sSup ((fun q => InformationTheory.klDiv (law q).joint
      (law q).referenceMeasure) '' admissible) ≠ ⊤)
    (q : Q) (hq : q ∈ admissible) :
    FiniteConditionalMutualInformationLaw (X q) (G q) (Y q) :=
  ⟨law q, ne_top_of_le_ne_top hcapacity (le_sSup ⟨q, hq, rfl⟩)⟩

/-- 有限容量から取り出した有限lawは、元の分布・条件付き周辺核を保持する。 -/
theorem finiteMeasureCMILawOfFiniteCapacity_distribution
    {Q : Type*} (X G Y : Q → Type*)
    [∀ q, MeasurableSpace (X q)] [∀ q, MeasurableSpace (G q)]
    [∀ q, MeasurableSpace (Y q)]
    (law : ∀ q, ConditionalMutualInformationLaw (X q) (G q) (Y q))
    (admissible : Set Q)
    (hcapacity : sSup ((fun q => InformationTheory.klDiv (law q).joint
      (law q).referenceMeasure) '' admissible) ≠ ⊤)
    (q : Q) (hq : q ∈ admissible) :
    (finiteMeasureCMILawOfFiniteCapacity X G Y law admissible hcapacity q hq).distribution =
      law q := rfl

/-- 一つの許容問題・方策対の有限ゴールCMIデータ。
型と可測構造、有限ゴール性、条件付き周辺法則と有限KL証明を同じパッケージに置く。
確率的出力を許し、Input/Outputの有限性・標準Borel性は要求しない。
条件付き核はlawに明示保持し、核の無条件存在を主張する構造ではない。 -/
structure FiniteGoalCMIProblem where
  Input : Type u
  Goal : Type v
  Output : Type w
  inputMeasurable : MeasurableSpace Input
  goalMeasurable : MeasurableSpace Goal
  outputMeasurable : MeasurableSpace Output
  goalFintype : Fintype Goal
  goalSingletons : @MeasurableSingletonClass Goal goalMeasurable
  law : @FiniteConditionalMutualInformationLaw Input Goal Output
    inputMeasurable goalMeasurable outputMeasurable

/-- 問題自身のアルファベット上で計算した有限KL型CMI。 -/
noncomputable def FiniteGoalCMIProblem.score (p : FiniteGoalCMIProblem) : ℝ := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  exact finiteKLDivergenceScore p.law.toFiniteKLLaw

/-- 問題自身の条件付きゴール核から計算したH(G|X)。 -/
noncomputable def FiniteGoalCMIProblem.goalEntropy (p : FiniteGoalCMIProblem) : ℝ := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  letI := p.goalFintype
  exact Tomabechi.Theorem19_22.inputGoalEntropy p.law.distribution

theorem FiniteGoalCMIProblem.score_nonneg (p : FiniteGoalCMIProblem) : 0 ≤ p.score := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  change 0 ≤ (InformationTheory.klDiv p.law.distribution.joint
    p.law.distribution.referenceMeasure).toReal
  exact ENNReal.toReal_nonneg

/-- 問題ごとの有限ゴール性だけでCMI≤H(G|X)。全問題共通のゴール型を使わない。 -/
theorem FiniteGoalCMIProblem.score_le_goalEntropy (p : FiniteGoalCMIProblem) :
    p.score ≤ p.goalEntropy := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  letI := p.goalFintype
  letI := p.goalSingletons
  exact Tomabechi.Theorem19_22.finite_measure_cmi_le_inputGoalEntropy p.law

theorem FiniteGoalCMIProblem.score_eq_zero_of_goalEntropy_zero
    (p : FiniteGoalCMIProblem) (hzero : p.goalEntropy = 0) : p.score = 0 :=
  le_antisymm (by simpa only [hzero] using p.score_le_goalEntropy) p.score_nonneg

/-- 問題固有の同時法則が条件付き独立参照法則に一致するという独立性。 -/
def FiniteGoalCMIProblem.ConditionallyIndependent (p : FiniteGoalCMIProblem) : Prop := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  exact p.law.distribution.joint = p.law.distribution.referenceMeasure

/-- 問題ごとに異なる可測アルファベットでも、条件付き独立ならCMIは零。 -/
theorem FiniteGoalCMIProblem.score_eq_zero_of_independence
    (p : FiniteGoalCMIProblem) (hindependent : p.ConditionallyIndependent) : p.score = 0 := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  exact Tomabechi.Theorem19_22.finite_measure_cmi_score_eq_zero_of_joint_eq_reference
    p.law hindependent

/-- 問題別アルファベットをもつ層容量は、Σ型で束ねた定理22容量と一致。
同じ問題型の要素に同じCMIを割り当てる表現同定である。 -/
theorem heterogeneous_measure_cmi_capacity_eq_pooledLayerCapacity
    {L : Type*} [Preorder L] (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (problem : ∀ a, A a → FiniteGoalCMIProblem)
    (a : L) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun b x => (problem b x).score) a =
      layerCapacity (Tomabechi.Theorem19_22.pooledAdmissible A admissible)
        (fun q => (problem q.1 q.2).score) a := by
  classical
  unfold Tomabechi.Theorem19.dependentLayerCapacity layerCapacity
    Tomabechi.Theorem19_22.pooledAdmissible
  congr 1
  ext r
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨a, x⟩, ⟨x, rfl, hx⟩, rfl⟩
  · rintro ⟨⟨b, x⟩, ⟨y, hq, hy⟩, hr⟩
    cases hq
    exact ⟨y, hy, hr⟩

/-- 原文19の評価保存単射から問題別アルファベットのCMI容量単調性。
評価保存は原文に明示される条件であり、異なる型のlawを点ごとの等号で比較しない。
分布保存の具体化は共通型のlaw橋や可測同型によるKL保存を別に使う。 -/
theorem heterogeneous_measure_cmi_capacity_nondecreasing
    {L : Type*} [Preorder L] (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (problem : ∀ a, A a → FiniteGoalCMIProblem)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove ((fun x => (problem a x).score) '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b), Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hevaluation : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      (problem b (embedding hab x)).score = (problem a x).score)
    (a b : L) (hab : a ≤ b) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => (problem c x).score) a ≤
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => (problem c x).score) b := by
  exact Tomabechi.Theorem19.dependentCapacity_nondecreasing_of_scorePreservingEmbedding
    A admissible (fun c x => (problem c x).score)
    hnonempty hbounded embedding hinjective hmapsTo hevaluation a b hab

/-- 同じ層間対応を定理22のLUB更新に沿って反復した容量単調性。 -/
theorem heterogeneous_measure_cmi_capacity_monotone_along_lub_stages
    {L : Type*} [SemilatticeSup L] (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (problem : ∀ a, A a → FiniteGoalCMIProblem)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove ((fun x => (problem a x).score) '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b), Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hevaluation : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      (problem b (embedding hab x)).score = (problem a x).score)
    (u v : ℕ → L) (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone (fun n => Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => (problem c x).score) (u n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hupdate n]
  exact heterogeneous_measure_cmi_capacity_nondecreasing A admissible problem
    hnonempty hbounded embedding hinjective hmapsTo hevaluation _ _ le_sup_left

/-- 異なるゴール型の問題を含む指定層でも、全問題の零エントロピーから容量零。
零エントロピーからスコア集合の有界性も導くので、ここでは容量有限性を追加入力しない。 -/
theorem heterogeneous_measure_cmi_capacity_eq_zero_of_goalEntropy_zero
    {L : Type*} [Preorder L] (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (problem : ∀ a, A a → FiniteGoalCMIProblem)
    (a : L) (hnonempty : (admissible a).Nonempty)
    (hzero : ∀ x, x ∈ admissible a → (problem a x).goalEntropy = 0) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => (problem c x).score) a = 0 := by
  apply Tomabechi.Theorem19.zeroCapacity_of_zeroGoalEntropy
    (admissible a) (fun x => (problem a x).score)
    (fun x => (problem a x).goalEntropy) hnonempty
  · refine ⟨0, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    simpa only [hzero x hx] using (problem a x).score_le_goalEntropy
  · exact fun x _ => (problem a x).score_nonneg
  · exact fun x _ => (problem a x).score_le_goalEntropy
  · exact hzero

/-- 問題/方策ごとに異なるCMIアルファベットでも、原文19の二重上限と対上限は一致。
各問題の方策集合の非空性を要求せず、CMI非負性をパッケージから供給する。 -/
theorem heterogeneous_measure_cmi_doubleSup_eq_pairSup
    {D : Type*} (Policy : D → Type*) (problems : Set D)
    (policies : ∀ d, Set (Policy d)) (problem : ∀ d, Policy d → FiniteGoalCMIProblem)
    (hnonempty : (Tomabechi.Theorem19.admissibleProblemPolicyPairs
      Policy problems policies).Nonempty)
    (hbounded : BddAbove ((fun q : Σ d, Policy d => (problem q.1 q.2).score) ''
      Tomabechi.Theorem19.admissibleProblemPolicyPairs Policy problems policies)) :
    sSup ((fun d => sSup ((fun p => (problem d p).score) '' policies d)) '' problems) =
      sSup ((fun q : Σ d, Policy d => (problem q.1 q.2).score) ''
        Tomabechi.Theorem19.admissibleProblemPolicyPairs Policy problems policies) := by
  exact Tomabechi.Theorem19.problemPolicy_doubleSup_eq_pairSup
    Policy problems policies (fun d p => (problem d p).score) hnonempty hbounded
    (fun d _ p _ => (problem d p).score_nonneg)

/-- 原文19の容量に関する結論を問題別アルファベットの一つの入口でまとめる。
非負性・層単調性・端点比較・物理層零容量・正規化の単調性/端点/一意性を返す。
同じ許容問題族と層間評価保存写像を全結論に使い、有限容量と正の端点差は原文条件に保持。
単射方策の情報達成はTheorem19_22の個別law定理で別に扱う。 -/
theorem heterogeneous_measure_cmi_original_capacity_conclusions
    {L : Type*} [CompleteLattice L] (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (problem : ∀ a, A a → FiniteGoalCMIProblem)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hbounded : ∀ a, BddAbove ((fun x => (problem a x).score) '' admissible a))
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b), Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hevaluation : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      (problem b (embedding hab x)).score = (problem a x).score)
    (hphysicalZero : ∀ x, x ∈ admissible ⊥ → (problem ⊥ x).goalEntropy = 0)
    (hgap : Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => (problem c x).score) ⊥ <
        Tomabechi.Theorem19.dependentLayerCapacity A admissible
          (fun c x => (problem c x).score) ⊤) :
    let capacity := Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => (problem c x).score)
    let normalized := fun a => Tomabechi.Theorem19.endpointNormalization
      (capacity ⊥) (capacity ⊤) (capacity a)
    Monotone capacity ∧
      (∀ a, 0 ≤ capacity a ∧ capacity ⊥ ≤ capacity a ∧ capacity a ≤ capacity ⊤) ∧
      capacity ⊥ = 0 ∧ Monotone normalized ∧ normalized ⊥ = 0 ∧ normalized ⊤ = 1 ∧
      (∀ g : ℝ → ℝ, (∃ m c, ∀ x, g x = m * x + c) →
        g (capacity ⊥) = 0 → g (capacity ⊤) = 1 →
        ∀ x, g x = Tomabechi.Theorem19.endpointNormalization (capacity ⊥) (capacity ⊤) x) := by
  dsimp only
  let capacity := Tomabechi.Theorem19.dependentLayerCapacity A admissible
    (fun c x => (problem c x).score)
  have hmono : Monotone capacity := by
    intro a b hab
    exact heterogeneous_measure_cmi_capacity_nondecreasing A admissible problem
      hnonempty hbounded embedding hinjective hmapsTo hevaluation a b hab
  have hbounds : ∀ a, 0 ≤ capacity a ∧ capacity ⊥ ≤ capacity a ∧ capacity a ≤ capacity ⊤ := by
    intro a
    obtain ⟨x, hx⟩ := hnonempty a
    exact ⟨(problem a x).score_nonneg.trans (le_csSup (hbounded a) ⟨x, hx, rfl⟩),
      hmono bot_le, hmono le_top⟩
  have hzero := heterogeneous_measure_cmi_capacity_eq_zero_of_goalEntropy_zero
    A admissible problem ⊥ (hnonempty ⊥) hphysicalZero
  have hnormMono := (Tomabechi.Theorem19.endpointNormalization_strictMono
    (capacity ⊥) (capacity ⊤) hgap).monotone.comp hmono
  have hvalues := Tomabechi.Theorem19.endpointNormalization_values
    (capacity ⊥) (capacity ⊤) hgap
  refine ⟨hmono, hbounds, hzero, hnormMono, hvalues.1, hvalues.2, ?_⟩
  intro g hAffine hbottom htop
  exact Tomabechi.Theorem19.endpointAffine_unique (capacity ⊥) (capacity ⊤)
    hgap g hAffine hbottom htop

/-- 出力条件付き核を持たない直接CMI問題。X/Yは任意可測空間。
有限性は各問題に固定せず、許容族の有限容量から導く。 -/
structure DirectGoalCMIProblem where
  Input : Type u
  Goal : Type v
  Output : Type w
  inputMeasurable : MeasurableSpace Input
  goalMeasurable : MeasurableSpace Goal
  outputMeasurable : MeasurableSpace Output
  goalFintype : Fintype Goal
  goalSingletons : @MeasurableSingletonClass Goal goalMeasurable
  joint : @Measure (Input × (Goal × Output))
    (inputMeasurable.prod (goalMeasurable.prod outputMeasurable))
  jointProbability : @IsProbabilityMeasure (Input × (Goal × Output))
    (inputMeasurable.prod (goalMeasurable.prod outputMeasurable)) joint

/-- 直接問題の入力周辺。明示的な可測空間フィールドから定義する。 -/
noncomputable def DirectGoalCMIProblem.inputMarginal (p : DirectGoalCMIProblem) :
    @Measure p.Input p.inputMeasurable :=
  @Measure.map (p.Input × (p.Goal × p.Output)) p.Input
    (p.inputMeasurable.prod (p.goalMeasurable.prod p.outputMeasurable))
    p.inputMeasurable Prod.fst p.joint

/-- 直接問題のCMI。有限性を判定するため拡張実数のまま保持する。 -/
noncomputable def DirectGoalCMIProblem.information (p : DirectGoalCMIProblem) : ENNReal := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  letI := p.goalFintype
  letI := p.goalSingletons
  letI := p.jointProbability
  exact InformationTheory.klDiv (Tomabechi.Theorem19_22.directActionGoalJoint p.joint)
    (Tomabechi.Theorem19_22.directCMIReference p.joint)

noncomputable def DirectGoalCMIProblem.score (p : DirectGoalCMIProblem) : ℝ :=
  p.information.toReal

/-- 直接問題の原文H(G|X)。同時法則から有限ゴール事前核を構成する。 -/
noncomputable def DirectGoalCMIProblem.goalEntropy (p : DirectGoalCMIProblem) : ℝ := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  letI := p.goalFintype
  letI := p.goalSingletons
  letI := p.jointProbability
  exact ∫ x, Tomabechi.Theorem19_22.finiteKernelGoalEntropyAt
    (Tomabechi.Theorem19_22.directPriorGoalKernel p.joint) x ∂p.joint.map Prod.fst

/-- 有限直接CMIは、同時法則から構成した条件付きゴールエントロピー以下。 -/
theorem DirectGoalCMIProblem.score_le_goalEntropy
    (p : DirectGoalCMIProblem) (hfinite : p.information ≠ ⊤) :
    p.score ≤ p.goalEntropy := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  letI := p.goalFintype
  letI := p.goalSingletons
  letI := p.jointProbability
  exact Tomabechi.Theorem19_22.directCMI_le_inputGoalEntropy_of_finite p.joint hfinite

/-- 許容族の拡張容量有限なら各許容問題のKLも有限。 -/
theorem directCMI_information_ne_top_of_finite_capacity
    {Q : Type*} (problem : Q → DirectGoalCMIProblem) (admissible : Set Q)
    (hfinite : sSup ((fun q => (problem q).information) '' admissible) ≠ ⊤)
    (q : Q) (hq : q ∈ admissible) : (problem q).information ≠ ⊤ :=
  ne_top_of_le_ne_top hfinite (le_sSup ⟨q, hq, rfl⟩)

/-- 直接問題の条件付き独立：同時法則と直接独立参照法則が一致する。 -/
def DirectGoalCMIProblem.ConditionallyIndependent (p : DirectGoalCMIProblem) : Prop := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  letI := p.goalFintype
  letI := p.goalSingletons
  letI := p.jointProbability
  exact Tomabechi.Theorem19_22.directActionGoalJoint p.joint =
    Tomabechi.Theorem19_22.directCMIReference p.joint

/-- 条件付き独立なら拡張CMIそのものが零。有限性入力は不要。 -/
theorem DirectGoalCMIProblem.information_eq_zero_of_independence
    (p : DirectGoalCMIProblem) (h : p.ConditionallyIndependent) : p.information = 0 := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  letI := p.goalFintype
  letI := p.goalSingletons
  letI := p.jointProbability
  change InformationTheory.klDiv (Tomabechi.Theorem19_22.directActionGoalJoint p.joint)
    (Tomabechi.Theorem19_22.directCMIReference p.joint) = 0
  letI := Tomabechi.Theorem19_22.directCMIReference_isProbabilityMeasure p.joint
  rw [h]
  exact InformationTheory.klDiv_self _

/-- 直接問題の独立時実数評価は零。 -/
theorem DirectGoalCMIProblem.score_eq_zero_of_independence
    (p : DirectGoalCMIProblem) (h : p.ConditionallyIndependent) : p.score = 0 := by
  unfold DirectGoalCMIProblem.score
  rw [p.information_eq_zero_of_independence h, ENNReal.toReal_zero]

/-- 許容問題族の拡張CMI上限有限から、実数容量に必要な有界性を導く。 -/
theorem directCMI_scores_bddAbove
    {Q : Type*} (problem : Q → DirectGoalCMIProblem) (admissible : Set Q)
    (hfinite : sSup ((fun q => (problem q).information) '' admissible) ≠ ⊤) :
    BddAbove ((fun q => (problem q).score) '' admissible) := by
  refine ⟨(sSup ((fun q => (problem q).information) '' admissible)).toReal, ?_⟩
  rintro r ⟨q, hq, rfl⟩
  exact ENNReal.toReal_mono hfinite (le_sSup ⟨q, hq, rfl⟩)

/-- 直接同時法則からの問題別容量単調性。有限容量を拡張CMIで受け取り、
実数上限の有界性を内部で導く。評価保存単射は原文の独立条件。 -/
theorem directCMI_capacity_nondecreasing
    {L : Type*} [Preorder L] (A : L → Type*) (admissible : ∀ a, Set (A a))
    (problem : ∀ a, A a → DirectGoalCMIProblem)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hfinite : ∀ a, sSup ((fun q => (problem a q).information) '' admissible a) ≠ ⊤)
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b), Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {q}, q ∈ admissible a →
      embedding hab q ∈ admissible b)
    (hevaluation : ∀ {a b : L} (hab : a ≤ b) {q}, q ∈ admissible a →
      (problem b (embedding hab q)).information = (problem a q).information)
    (a b : L) (hab : a ≤ b) :
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c q => (problem c q).score) a ≤
    Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c q => (problem c q).score) b := by
  apply Tomabechi.Theorem19.dependentCapacity_nondecreasing_of_scorePreservingEmbedding
    A admissible (fun c q => (problem c q).score) hnonempty
    (fun c => directCMI_scores_bddAbove (problem c) (admissible c) (hfinite c))
    embedding hinjective hmapsTo _ a b hab
  intro a b hab q hq
  exact congrArg ENNReal.toReal (hevaluation hab hq)

/-- 直接問題型の零容量。H(G|X)=0は指定許容族だけに要求する。 -/
theorem directCMI_capacity_eq_zero_of_goalEntropy_zero
    {Q : Type*} (problem : Q → DirectGoalCMIProblem) (admissible : Set Q)
    (hnonempty : admissible.Nonempty)
    (hfinite : sSup ((fun q => (problem q).information) '' admissible) ≠ ⊤)
    (hentropy : ∀ q ∈ admissible, (problem q).goalEntropy = 0) :
    sSup ((fun q => (problem q).score) '' admissible) = 0 := by
  apply Tomabechi.Theorem19.zeroCapacity_of_zeroGoalEntropy admissible
    (fun q => (problem q).score) (fun q => (problem q).goalEntropy)
    hnonempty (directCMI_scores_bddAbove problem admissible hfinite)
    (fun _ _ => ENNReal.toReal_nonneg) _ hentropy
  intro q hq
  exact (problem q).score_le_goalEntropy
    (directCMI_information_ne_top_of_finite_capacity problem admissible hfinite q hq)

/-- 任意可測出力の直接問題族から原文19の容量結論をまとめる。
有限拡張容量・評価保存単射・物理層零エントロピー・正端点差を明示入力に保つ。 -/
theorem directCMI_original_capacity_conclusions
    {L : Type*} [CompleteLattice L] (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (problem : ∀ a, A a → DirectGoalCMIProblem)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hfinite : ∀ a, sSup ((fun x => (problem a x).information) '' admissible a) ≠ ⊤)
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b), Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hevaluation : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      (problem b (embedding hab x)).information = (problem a x).information)
    (hphysicalZero : ∀ x, x ∈ admissible ⊥ → (problem ⊥ x).goalEntropy = 0)
    (hgap : Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => (problem c x).score) ⊥ <
        Tomabechi.Theorem19.dependentLayerCapacity A admissible
          (fun c x => (problem c x).score) ⊤) :
    let capacity := Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => (problem c x).score)
    let normalized := fun a => Tomabechi.Theorem19.endpointNormalization
      (capacity ⊥) (capacity ⊤) (capacity a)
    Monotone capacity ∧
      (∀ a, 0 ≤ capacity a ∧ capacity ⊥ ≤ capacity a ∧ capacity a ≤ capacity ⊤) ∧
      capacity ⊥ = 0 ∧ Monotone normalized ∧ normalized ⊥ = 0 ∧ normalized ⊤ = 1 ∧
      (∀ g : ℝ → ℝ, (∃ m c, ∀ x, g x = m * x + c) →
        g (capacity ⊥) = 0 → g (capacity ⊤) = 1 →
        ∀ x, g x = Tomabechi.Theorem19.endpointNormalization (capacity ⊥) (capacity ⊤) x) := by
  dsimp only
  have hbounded := fun a => directCMI_scores_bddAbove (problem a) (admissible a) (hfinite a)
  let capacity := Tomabechi.Theorem19.dependentLayerCapacity A admissible
    (fun c x => (problem c x).score)
  have hmono : Monotone capacity := by
    intro a b hab
    exact directCMI_capacity_nondecreasing A admissible problem
      hnonempty hfinite embedding hinjective hmapsTo hevaluation a b hab
  have hbounds : ∀ a, 0 ≤ capacity a ∧ capacity ⊥ ≤ capacity a ∧ capacity a ≤ capacity ⊤ := by
    intro a
    obtain ⟨x, hx⟩ := hnonempty a
    exact ⟨(ENNReal.toReal_nonneg (a := (problem a x).information)).trans (le_csSup (hbounded a) ⟨x, hx, rfl⟩),
      hmono bot_le, hmono le_top⟩
  have hzero := directCMI_capacity_eq_zero_of_goalEntropy_zero
    (problem ⊥) (admissible ⊥) (hnonempty ⊥) (hfinite ⊥) hphysicalZero
  have hnormMono := (Tomabechi.Theorem19.endpointNormalization_strictMono
    (capacity ⊥) (capacity ⊤) hgap).monotone.comp hmono
  have hvalues := Tomabechi.Theorem19.endpointNormalization_values
    (capacity ⊥) (capacity ⊤) hgap
  refine ⟨hmono, hbounds, hzero, hnormMono, hvalues.1, hvalues.2, ?_⟩
  intro g hAffine hbottom htop
  exact Tomabechi.Theorem19.endpointAffine_unique (capacity ⊥) (capacity ⊤)
    hgap g hAffine hbottom htop

/-- 直接CMIの問題/方策二重上限は許容対上限と一致する。
各問題の方策非空性は追加せず、許容対全体の非空性と有限拡張容量を用いる。 -/
theorem directCMI_doubleSup_eq_pairSup
    {D : Type*} (Policy : D → Type*) (problems : Set D)
    (policies : ∀ d, Set (Policy d)) (problem : ∀ d, Policy d → DirectGoalCMIProblem)
    (hnonempty : (Tomabechi.Theorem19.admissibleProblemPolicyPairs
      Policy problems policies).Nonempty)
    (hfinite : sSup ((fun q : Σ d, Policy d => (problem q.1 q.2).information) ''
      Tomabechi.Theorem19.admissibleProblemPolicyPairs Policy problems policies) ≠ ⊤) :
    sSup ((fun d => sSup ((fun p => (problem d p).score) '' policies d)) '' problems) =
      sSup ((fun q : Σ d, Policy d => (problem q.1 q.2).score) ''
        Tomabechi.Theorem19.admissibleProblemPolicyPairs Policy problems policies) := by
  exact Tomabechi.Theorem19.problemPolicy_doubleSup_eq_pairSup
    Policy problems policies (fun d p => (problem d p).score) hnonempty
    (directCMI_scores_bddAbove (fun q : Σ d, Policy d => problem q.1 q.2)
      (Tomabechi.Theorem19.admissibleProblemPolicyPairs Policy problems policies) hfinite)
    (fun _ _ _ _ => ENNReal.toReal_nonneg)

/-- 直接CMI容量を定理22のLUB更新へ接続する。問題別可測型と拡張容量有限性を保持。 -/
theorem directCMI_capacity_monotone_along_lub_stages
    {L : Type*} [SemilatticeSup L] (A : L → Type*)
    (admissible : ∀ a, Set (A a)) (problem : ∀ a, A a → DirectGoalCMIProblem)
    (hnonempty : ∀ a, (admissible a).Nonempty)
    (hfinite : ∀ a, sSup ((fun x => (problem a x).information) '' admissible a) ≠ ⊤)
    (embedding : ∀ {a b : L}, a ≤ b → A a → A b)
    (hinjective : ∀ {a b : L} (hab : a ≤ b), Function.Injective (embedding hab))
    (hmapsTo : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      embedding hab x ∈ admissible b)
    (hevaluation : ∀ {a b : L} (hab : a ≤ b) {x}, x ∈ admissible a →
      (problem b (embedding hab x)).information = (problem a x).information)
    (u v : ℕ → L) (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1)) :
    Monotone (fun n => Tomabechi.Theorem19.dependentLayerCapacity A admissible
      (fun c x => (problem c x).score) (u n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hupdate n]
  exact directCMI_capacity_nondecreasing A admissible problem
    hnonempty hfinite embedding hinjective hmapsTo hevaluation _ _ le_sup_left

/-- 直接問題型の可測復元による情報達成。
任意可測出力を保ち、復号器の可測性とjoint-a.e.復元を実際の入力にする。 -/
theorem DirectGoalCMIProblem.score_eq_goalEntropy_of_recovery
    (p : DirectGoalCMIProblem) (hfinite : p.information ≠ ⊤) :
    letI := p.inputMeasurable
    letI := p.goalMeasurable
    letI := p.outputMeasurable
    ∀ (recover : p.Input × p.Output → p.Goal), Measurable recover →
      (∀ᵐ z ∂p.joint, recover (z.1, z.2.2) = z.2.1) → p.score = p.goalEntropy := by
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  letI := p.goalFintype
  letI := p.goalSingletons
  letI := p.jointProbability
  intro recover hmeas hrecovers
  exact Tomabechi.Theorem19_22.directCMI_eq_inputGoalEntropy_of_recovery
    p.joint hfinite recover hmeas hrecovers

/-- 異種の直接問題族で、有限容量から各許容lawの有限KLを取り出し、
各問題の可測な決定論的単射方策による情報達成を同じ `score` / `goalEntropy` に接続する。
出力型ごとの `MeasurableEq` は可測復号器構成に使う十分条件であり、任意可測出力への
一般化ではない。 -/
theorem directCMI_heterogeneous_injective_policy_attains_goalEntropy
    {Q : Type*} (problem : Q → DirectGoalCMIProblem) (admissible : Set Q)
    (hfinite : sSup ((fun q => (problem q).information) '' admissible) ≠ ⊤)
    (action : ∀ q, (problem q).Input × (problem q).Goal → (problem q).Output)
    (hmeas : ∀ q, @Measurable ((problem q).Input × (problem q).Goal)
      (problem q).Output ((problem q).inputMeasurable.prod (problem q).goalMeasurable)
      (problem q).outputMeasurable (action q))
    (hgenerated : ∀ q, (problem q).joint =
      (@Measure.map ((problem q).Input × (problem q).Goal) ((problem q).Input ×
          ((problem q).Goal × (problem q).Output))
        ((problem q).inputMeasurable.prod (problem q).goalMeasurable)
        ((problem q).inputMeasurable.prod
          ((problem q).goalMeasurable.prod (problem q).outputMeasurable))
        (fun z : (problem q).Input × (problem q).Goal => (z.1, z.2, action q z))
        (@Measure.map ((problem q).Input × ((problem q).Goal × (problem q).Output))
          ((problem q).Input × (problem q).Goal)
          ((problem q).inputMeasurable.prod
            ((problem q).goalMeasurable.prod (problem q).outputMeasurable))
          ((problem q).inputMeasurable.prod (problem q).goalMeasurable)
          (fun z : (problem q).Input × ((problem q).Goal × (problem q).Output) =>
            (z.1, z.2.1)) (problem q).joint)))
    (hinjective : ∀ q, ∀ᵐ x ∂(problem q).inputMarginal,
      Function.Injective (fun g => action q (x, g)))
    (hstandardBorel : ∀ q, @StandardBorelSpace (problem q).Output
      (problem q).outputMeasurable) :
    ∀ q ∈ admissible, (problem q).score = (problem q).goalEntropy := by
  intro q hq
  let p := problem q
  letI := p.inputMeasurable
  letI := p.goalMeasurable
  letI := p.outputMeasurable
  letI := p.goalFintype
  letI := p.goalSingletons
  letI := p.jointProbability
  letI := hstandardBorel q
  letI : MeasurableEq p.Output := inferInstance
  have hkl : p.information ≠ ⊤ :=
    directCMI_information_ne_top_of_finite_capacity problem admissible hfinite q hq
  change (InformationTheory.klDiv
    (Tomabechi.Theorem19_22.directActionGoalJoint p.joint)
    (Tomabechi.Theorem19_22.directCMIReference p.joint)).toReal = p.goalEntropy
  change (InformationTheory.klDiv
    (Tomabechi.Theorem19_22.directActionGoalJoint p.joint)
    (Tomabechi.Theorem19_22.directCMIReference p.joint)).toReal = _
  exact Tomabechi.Theorem19_22.directCMI_eq_inputGoalEntropy_of_injective_deterministic_joint
    p.joint hkl (action q) (hmeas q) (hgenerated q) (hinjective q)

end Tomabechi.Theorem19_Heterogeneous

namespace Tomabechi.Theorem19_Heterogeneous

/-- P16の二値証人を、定理19で使う直接KL問題型に包む。出力の自明σ代数を
保持し、標準Borel条件は加えない。 -/
noncomputable def indiscreteBitDirectProblem : DirectGoalCMIProblem := by
  let law := Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw
  exact {
    Input := Unit
    Goal := Bool
    Output := Tomabechi.Theorem19_22.DecoderRegularityWitness.IndiscreteBit
    inputMeasurable := inferInstance
    goalMeasurable := inferInstance
    outputMeasurable := inferInstance
    goalFintype := inferInstance
    goalSingletons := inferInstance
    joint := law.joint
    jointProbability := law.joint_isProbabilityMeasure }

/-- 二値証人の直接CMIは既存CMI lawのKLそのもので、有限かつ零である。 -/
theorem indiscreteBitDirectProblem_information_eq_zero :
    indiscreteBitDirectProblem.information = 0 := by
  let law := Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw
  letI := law.joint_isProbabilityMeasure
  change InformationTheory.klDiv
    (Tomabechi.Theorem19_22.directActionGoalJoint law.joint)
    (Tomabechi.Theorem19_22.directCMIReference law.joint) = 0
  rw [Tomabechi.Theorem19_22.directCMI_kl_eq_existing law,
    Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw_cmi_eq_zero]

/-- 直接問題型が計算する条件付きゴールエントロピーは、同じ二値lawの
`H(G|X)=log 2` と一致する。 -/
theorem indiscreteBitDirectProblem_goalEntropy_eq_log_two :
    indiscreteBitDirectProblem.goalEntropy = Real.log 2 := by
  let law := Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw
  letI := law.joint_isProbabilityMeasure
  change (∫ x, Tomabechi.Theorem19_22.finiteKernelGoalEntropyAt
      (Tomabechi.Theorem19_22.directPriorGoalKernel law.joint) x
      ∂law.joint.map Prod.fst) = Real.log 2
  have hprior := Tomabechi.Theorem19_22.directPriorGoalKernel_eq_existing law
  rw [← Tomabechi.Theorem19_22.cmiJoint_inputMarginal law] at hprior
  have hentropy :
      (fun x => Tomabechi.Theorem19_22.finiteKernelGoalEntropyAt
        (Tomabechi.Theorem19_22.directPriorGoalKernel law.joint) x) =ᵐ[
          law.joint.map Prod.fst]
      (fun x => Tomabechi.Theorem19_22.finiteKernelGoalEntropyAt
        law.goalGivenInput x) := hprior.mono fun x hx => by
    simp [Tomabechi.Theorem19_22.finiteKernelGoalEntropyAt,
      Tomabechi.Theorem19_22.finiteKernelGoalMass,
      Tomabechi.Theorem21.conditionalGoalEntropyAt, hx]
  rw [MeasureTheory.integral_congr_ae hentropy]
  rw [Tomabechi.Theorem19_22.cmiJoint_inputMarginal law]
  exact Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw_inputEntropy_eq_log_two

/-- 直接KL型の同一 `DirectGoalCMIProblem` 上で情報達成等式が破れる。
任意可測Yへの一般化に対するC2証人であり、原文適合性は別途C1/C3で判定する。 -/
theorem indiscreteBitDirectProblem_score_lt_goalEntropy :
    indiscreteBitDirectProblem.score < indiscreteBitDirectProblem.goalEntropy := by
  rw [DirectGoalCMIProblem.score, indiscreteBitDirectProblem_information_eq_zero,
    ENNReal.toReal_zero, indiscreteBitDirectProblem_goalEntropy_eq_log_two]
  exact Real.log_pos (by norm_num)

end Tomabechi.Theorem19_Heterogeneous

#print axioms Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_score_lt_goalEntropy

#print axioms Tomabechi.Theorem19_Heterogeneous.FiniteGoalCMIProblem.score_le_goalEntropy
#print axioms Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_capacity_eq_pooledLayerCapacity
#print axioms Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_capacity_nondecreasing
#print axioms Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_capacity_monotone_along_lub_stages
#print axioms Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_capacity_eq_zero_of_goalEntropy_zero
#print axioms Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_doubleSup_eq_pairSup
#print axioms Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_original_capacity_conclusions
#print axioms Tomabechi.Theorem19_Heterogeneous.FiniteGoalCMIProblem.score_eq_zero_of_independence
#print axioms Tomabechi.Theorem19_Heterogeneous.directCMI_heterogeneous_injective_policy_attains_goalEntropy
#print axioms Tomabechi.Theorem19_Heterogeneous.finiteMeasureCMILawOfFiniteCapacity

#print axioms Tomabechi.Theorem19_Heterogeneous.directCMI_scores_bddAbove
#print axioms Tomabechi.Theorem19_Heterogeneous.directCMI_capacity_nondecreasing

#print axioms Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.score_le_goalEntropy
#print axioms Tomabechi.Theorem19_Heterogeneous.directCMI_capacity_eq_zero_of_goalEntropy_zero

#print axioms Tomabechi.Theorem19_Heterogeneous.directCMI_original_capacity_conclusions

#print axioms Tomabechi.Theorem19_Heterogeneous.directCMI_doubleSup_eq_pairSup

#print axioms Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.information_eq_zero_of_independence
#print axioms Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.score_eq_zero_of_independence

#print axioms Tomabechi.Theorem19_Heterogeneous.directCMI_capacity_monotone_along_lub_stages

#print axioms Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.score_eq_goalEntropy_of_recovery
