import Theorem16_25
import Theorem19_Heterogeneous

/-!
# P16: 定理19の情報達成節に対する反例モデル候補

任意可測出力という読みの下で、二値ゴールを自明σ代数の出力へ写す。
定理16の固定点証人と、全抽象度で同じ問題・方策を持つ定理19容量系を
束ねた候補である。定理19の内部ゴール表象は、固定点状態・そのコンパクト表象・
ゴール事前確率が一致する形で明示する。出力規約の適合性は原文記載が曖昧なため
別途監査対象とする。
-/

open MeasureTheory ProbabilityTheory Topology Tomabechi.Theorem16_25

namespace Tomabechi.Theorem19_Counterexample

/-- 全層で同じ単点TCZを使う逆系。層は自然数で、上向き有向・最大元なし。 -/
abbrev SubjectLayer := ℕ

noncomputable def subjectFixedPointExists : Prop :=
  ∃ x : {x : ∀ i : SubjectLayer, Unit //
      x ∈ affineInverseLimitSet (fun _ : SubjectLayer => Unit)
        (fun _ : SubjectLayer => (Set.univ : Set Unit))
        (fun {_ _} _ _ => ())},
    inducedAffineInverseLimitMap
      (fun _ : SubjectLayer => Unit)
      (fun _ : SubjectLayer => (Set.univ : Set Unit))
      (fun {_ _} _ _ => ())
      (by intro β α h x hx; trivial)
      (fun _ x => x)
      (by intro β α h x; rfl) x = x

/-- 定理16原文層条件を満たす単点逆系に、Fan–Glicksbergの固定点定理を適用する。
自己写像は各層の恒等写像で、得られる主体はその逆極限固定点である。 -/
theorem subjectFixedPointExists_of_originalConditions : subjectFixedPointExists := by
  classical
  let E : SubjectLayer → Type := fun _ => Unit
  let K : ∀ i, Set (E i) := fun _ => Set.univ
  let project : ∀ {β α : SubjectLayer}, β ≤ α → E α → E β := fun _ _ => ()
  have hcompact : ∀ i, IsCompact (K i) := by intro i; exact isCompact_univ
  have hnonempty : ∀ i, (K i).Nonempty := by intro i; exact ⟨(), trivial⟩
  have hconvex : ∀ i, Convex ℝ (K i) := by intro i; exact convex_univ
  have haffine : ∀ ⦃β α⦄ (hβα : β ≤ α) (x y : E α) (a b : ℝ),
      x ∈ K α → y ∈ K α → 0 ≤ a → 0 ≤ b → a + b = 1 →
      project hβα (a • x + b • y) = a • project hβα x + b • project hβα y := by
    intro β α h x y a b hx hy ha hb hab
    exact Subsingleton.elim _ _
  have hrefl : ∀ i (x : {x : E i // x ∈ K i}),
      project (le_rfl : i ≤ i) x.1 = x.1 := by intro i x; exact Subsingleton.elim _ _
  have hcomp : ∀ {γ β α} (hγβ : γ ≤ β) (hβα : β ≤ α)
      (x : {x : E α // x ∈ K α}),
      project hγβ (project hβα x.1) = project (hγβ.trans hβα) x.1 := by
    intro γ β α hγβ hβα x
    exact Subsingleton.elim _ _
  have hmaps : ∀ ⦃β α⦄ (hβα : β ≤ α), Set.MapsTo (project hβα) (K α) (K β) := by
    intro β α h x hx
    trivial
  have hcontinuous : ∀ (j : ProjectionConstraintIndex SubjectLayer),
      ContinuousOn (project j.2) (K j.1.2) := by
    intro j
    exact continuousOn_const
  have hnoMax : ∀ i : SubjectLayer, ∃ j, i < j := by
    intro i
    exact ⟨i + 1, Nat.lt_succ_self i⟩
  let f : ∀ i, {x : E i // x ∈ K i} → {x : E i // x ∈ K i} := fun _ x => x
  have hcomm : ∀ ⦃β α⦄ (hβα : β ≤ α) (x : {x : E α // x ∈ K α}),
      affineLayerProjection E K project hmaps hβα (f α x) =
        f β (affineLayerProjection E K project hmaps hβα x) := by
    intro β α h x
    apply Subtype.ext
    exact Subsingleton.elim _ _
  have hf : ∀ i, Continuous (f i) := by intro i; exact continuous_id
  obtain ⟨x, hx⟩ := theorem16_fixedPoint_exists_of_originalLayerConditions
    E K hcompact hnonempty hconvex project haffine hrefl hcomp hmaps hcontinuous
    hnoMax f hcomm hf
  refine ⟨x, ?_⟩
  simpa [subjectFixedPointExists, E, K, project, f] using hx

/-! ### 二値ゴール分布を持つ定理16の自己表象候補

元のUnit逆系はゴール情報を保持できないため、ここでは各層状態を `[0,1]` に広げる。
固定点座標 `1/2` はBoolゴールの一様事前分布を表し、ゴール型で添字づけた
表象ベクトルを定義する。 -/

abbrev GoalRepLayer := ℕ

def goalRepTCZ (_ : GoalRepLayer) : Set ℝ := Set.Icc 0 1

def goalRepProjection {_β _α : GoalRepLayer} (_ : _β ≤ _α) (x : ℝ) : ℝ := x

noncomputable def goalRepFeedback (_ : GoalRepLayer)
    (_ : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}) :
    {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} := ⟨1 / 2, by norm_num⟩

noncomputable def goalRepPoint : ∀ _ : GoalRepLayer, ℝ := fun _ => 1 / 2

/-- 区間TCZ・恒等射影・定数feedbackが定理16の層条件を満たすため、
既存の原文条件付き固定点定理を適用できる。 -/
theorem goalRepLayerSystem_has_fixedPoint_of_theorem16_conditions :
    ∃ x : {x : ∀ i : GoalRepLayer, ℝ //
        x ∈ affineInverseLimitSet (fun _ : GoalRepLayer => ℝ)
          goalRepTCZ goalRepProjection},
      inducedAffineInverseLimitMap (fun _ : GoalRepLayer => ℝ)
        goalRepTCZ goalRepProjection
        (by intro β α hβα x hx; simpa [goalRepProjection, goalRepTCZ] using hx)
        goalRepFeedback
        (by intro β α hβα x; apply Subtype.ext; rfl) x = x := by
  let E : GoalRepLayer → Type := fun _ => ℝ
  let K : ∀ i, Set (E i) := goalRepTCZ
  let project : ∀ {β α : GoalRepLayer}, β ≤ α → E α → E β :=
    fun _ x => x
  have hcompact : ∀ i, IsCompact (K i) := by
    intro i
    exact isCompact_Icc
  have hnonempty : ∀ i, (K i).Nonempty := by
    intro i
    exact ⟨1 / 2, by norm_num [K, goalRepTCZ]⟩
  have hconvex : ∀ i, Convex ℝ (K i) := by
    intro i
    exact convex_Icc 0 1
  have haffine : ∀ ⦃β α⦄ (hβα : β ≤ α) (x y : E α) (a b : ℝ),
      x ∈ K α → y ∈ K α → 0 ≤ a → 0 ≤ b → a + b = 1 →
      project hβα (a • x + b • y) = a • project hβα x + b • project hβα y := by
    intro β α hβα x y a b hx hy ha hb hab
    rfl
  have hrefl : ∀ i (x : {x : E i // x ∈ K i}),
      project (le_rfl : i ≤ i) x.1 = x.1 := by
    intro i x
    rfl
  have hcomp : ∀ {γ β α} (hγβ : γ ≤ β) (hβα : β ≤ α)
      (x : {x : E α // x ∈ K α}),
      project hγβ (project hβα x.1) = project (hγβ.trans hβα) x.1 := by
    intro γ β α hγβ hβα x
    rfl
  have hmaps : ∀ ⦃β α⦄ (hβα : β ≤ α), Set.MapsTo (project hβα) (K α) (K β) := by
    intro β α hβα x hx
    exact hx
  have hcontinuous : ∀ (j : ProjectionConstraintIndex GoalRepLayer),
      ContinuousOn (project j.2) (K j.1.2) := by
    intro j
    exact continuousOn_id
  have hnoMax : ∀ i : GoalRepLayer, ∃ j, i < j := by
    intro i
    exact ⟨i + 1, Nat.lt_succ_self i⟩
  let f : ∀ i, {x : E i // x ∈ K i} → {x : E i // x ∈ K i} :=
    fun _ _ => ⟨1 / 2, by norm_num [K, goalRepTCZ]⟩
  have hcomm : ∀ ⦃β α⦄ (hβα : β ≤ α) (x : {x : E α // x ∈ K α}),
      affineLayerProjection E K project hmaps hβα (f α x) =
        f β (affineLayerProjection E K project hmaps hβα x) := by
    intro β α hβα x
    apply Subtype.ext
    rfl
  have hf : ∀ i, Continuous (f i) := by
    intro i
    exact continuous_const
  exact theorem16_fixedPoint_exists_of_originalLayerConditions
    E K hcompact hnonempty hconvex project haffine hrefl hcomp hmaps hcontinuous
    hnoMax f hcomm hf

theorem goalRepPoint_mem_inverseLimit :
    goalRepPoint ∈ affineInverseLimitSet (fun _ : GoalRepLayer => ℝ)
      goalRepTCZ goalRepProjection := by
  constructor
  · intro i
    exact ⟨by norm_num [goalRepPoint], by norm_num [goalRepPoint]⟩
  · intro β α hβα
    rfl

noncomputable def goalRepSubject :
    {x : ∀ i : GoalRepLayer, ℝ //
      x ∈ affineInverseLimitSet (fun _ : GoalRepLayer => ℝ)
        goalRepTCZ goalRepProjection} :=
  ⟨goalRepPoint, goalRepPoint_mem_inverseLimit⟩

theorem goalRepSubject_fixed :
    inducedAffineInverseLimitMap (fun _ : GoalRepLayer => ℝ)
      goalRepTCZ goalRepProjection
      (by intro β α hβα x hx; simpa [goalRepProjection, goalRepTCZ] using hx)
      goalRepFeedback
      (by
        intro β α hβα x
        apply Subtype.ext
        rfl)
      goalRepSubject = goalRepSubject := by
  apply Subtype.ext
  funext i
  rfl

abbrev GoalRepSubjectState :=
  {x : ∀ i : GoalRepLayer, ℝ //
    x ∈ affineInverseLimitSet (fun _ : GoalRepLayer => ℝ)
      goalRepTCZ goalRepProjection}

abbrev GoalProbabilityRepresentation := {p : ℝ // p ∈ Set.Icc (0 : ℝ) 1}

noncomputable def goalRepLayerSelfMap : ∀ i : GoalRepLayer,
    {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} →
      {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} := goalRepFeedback

theorem goalRepLayerSelfMap_commutes :
    ∀ ⦃β α : GoalRepLayer⦄ (hβα : β ≤ α)
      (x : {x : ℝ // x ∈ goalRepTCZ α}),
      affineLayerProjection (fun _ : GoalRepLayer => ℝ) goalRepTCZ
        goalRepProjection
        (by intro β α hβα x hx; simpa [goalRepProjection, goalRepTCZ] using hx)
        hβα (goalRepLayerSelfMap α x) =
      goalRepLayerSelfMap β
        (affineLayerProjection (fun _ : GoalRepLayer => ℝ) goalRepTCZ
          goalRepProjection
          (by intro β α hβα x hx; simpa [goalRepProjection, goalRepTCZ] using hx)
          hβα x) := by
  intro β α hβα x
  apply Subtype.ext
  rfl

noncomputable def goalRepSubjectSelfMap : GoalRepSubjectState → GoalRepSubjectState :=
  inducedAffineInverseLimitMap (fun _ : GoalRepLayer => ℝ)
    goalRepTCZ goalRepProjection
    (by intro β α hβα x hx; simpa [goalRepProjection, goalRepTCZ] using hx)
    goalRepLayerSelfMap goalRepLayerSelfMap_commutes

theorem goalRepSubjectSelfMap_continuous : Continuous goalRepSubjectSelfMap := by
  apply inducedAffineInverseLimitMap_continuous
  intro i
  exact continuous_const

noncomputable def goalRepSubjectRepresent (s : GoalRepSubjectState) :
    GoalProbabilityRepresentation := ⟨s.1 0, s.2.1 0⟩

theorem goalRepSubjectRepresent_continuous :
    Continuous goalRepSubjectRepresent := by
  apply Continuous.subtype_mk
  exact (continuous_apply 0).comp continuous_subtype_val

noncomputable def goalRepSubjectRepresentation :
    SelfRepresentation GoalRepSubjectState GoalProbabilityRepresentation where
  relation := {p | p.1 = goalRepSubjectRepresent p.2}
  relation_closed := by
    exact isClosed_eq continuous_fst
      (goalRepSubjectRepresent_continuous.comp continuous_snd)
  represent := goalRepSubjectRepresent
  represent_continuous := goalRepSubjectRepresent_continuous
  represents := by
    intro s
    rfl

noncomputable def goalRepRepresentationFeedback :
    GoalProbabilityRepresentation → GoalProbabilityRepresentation :=
  fun _ => ⟨1 / 2, by norm_num⟩

theorem goalRepRepresentationFeedback_continuous :
    Continuous goalRepRepresentationFeedback := continuous_const

theorem goalRepSubjectRepresentation_equivariant (s : GoalRepSubjectState) :
    goalRepSubjectRepresentation.represent (goalRepSubjectSelfMap s) =
      goalRepRepresentationFeedback (goalRepSubjectRepresentation.represent s) := by
  apply Subtype.ext
  simp [goalRepSubjectSelfMap, inducedAffineInverseLimitMap,
    goalRepLayerSelfMap, goalRepFeedback, goalRepSubjectRepresentation,
    goalRepSubjectRepresent, goalRepRepresentationFeedback]

theorem goalRepSubjectSelfMap_fixedPoint_is_subject :
    goalRepSubjectSelfMap goalRepSubject = goalRepSubject := by
  apply Subtype.ext
  funext i
  simp [goalRepSubjectSelfMap, inducedAffineInverseLimitMap,
    goalRepLayerSelfMap, goalRepFeedback, goalRepSubject, goalRepPoint]

def internalGoalProbabilityFromRepresentation
    (r : GoalProbabilityRepresentation) (g : Bool) : ℝ :=
  if g then r.1 else 1 - r.1

theorem goalRepSubjectRepresentation_encodes_goalLaw :
    ∀ g : Bool,
      internalGoalProbabilityFromRepresentation
          (goalRepSubjectRepresentation.represent goalRepSubject) g =
        (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure {g}).toReal := by
  intro g
  cases g <;> simp [internalGoalProbabilityFromRepresentation,
    goalRepSubjectRepresentation, goalRepSubjectRepresent, goalRepSubject,
    goalRepPoint, Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure_singleton]
    <;> norm_num

def subjectGoalSelfRepresentationPremises : Prop :=
  Nonempty (SelfRepresentation GoalRepSubjectState GoalProbabilityRepresentation) ∧
    Continuous goalRepSubjectSelfMap ∧
    goalRepSubjectSelfMap goalRepSubject = goalRepSubject ∧
    Continuous goalRepRepresentationFeedback ∧
    (∀ s, goalRepSubjectRepresentation.represent (goalRepSubjectSelfMap s) =
      goalRepRepresentationFeedback (goalRepSubjectRepresentation.represent s)) ∧
    ∀ g : Bool,
      internalGoalProbabilityFromRepresentation
        (goalRepSubjectRepresentation.represent goalRepSubject) g =
          (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure {g}).toReal

theorem subjectGoalSelfRepresentationPremises_holds :
    subjectGoalSelfRepresentationPremises := by
  exact ⟨⟨goalRepSubjectRepresentation⟩, goalRepSubjectSelfMap_continuous,
    goalRepSubjectSelfMap_fixedPoint_is_subject,
    goalRepRepresentationFeedback_continuous,
    goalRepSubjectRepresentation_equivariant,
    goalRepSubjectRepresentation_encodes_goalLaw⟩

/-- 定理19のゴールcarrierで添字づけた、主体の内部ゴール確率表象。 -/
def subjectGoalProbabilityRep (x : ∀ _ : GoalRepLayer, ℝ) : Bool → ℝ :=
  fun g => if g then x 0 else 1 - x 0

/-- 固定点主体の自己表象は、二値ゴール事前分布の各原子確率を保持する。
これは固定点単点のUnit表象では表せなかったデータを同じsubject carrierへ接続する。 -/
theorem goalRepSubject_represents_binaryGoalLaw :
    ∀ g : Bool,
      subjectGoalProbabilityRep goalRepSubject.1 g =
        (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure {g}).toReal := by
  intro g
  cases g <;> simp [subjectGoalProbabilityRep, goalRepSubject, goalRepPoint,
    Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure_singleton] <;> norm_num

theorem goalRepSubject_matches_law_goalKernel :
    ∀ g : Bool,
      subjectGoalProbabilityRep goalRepSubject.1 g =
        (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw
          |>.goalGivenInput () {g}).toReal := by
  intro g
  change subjectGoalProbabilityRep goalRepSubject.1 g =
    (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure {g}).toReal
  exact goalRepSubject_represents_binaryGoalLaw g

/-- 二値ゴールの双方は、全層TCZの主体状態空間で異なる表象点を持つ。 -/
def goalStateCode (g : Bool) : ℝ := if g then 1 else 0

theorem goalStateCode_mem_subjectTCZ (g : Bool) :
    goalStateCode g ∈ goalRepTCZ 0 := by
  cases g <;> norm_num [goalStateCode, goalRepTCZ]

theorem goalStateCode_injective : Function.Injective goalStateCode := by
  intro g h hgh
  cases g <;> cases h <;> simp_all [goalStateCode]

theorem goalRepSubject_internalGoalRepresentation :
    Function.Injective goalStateCode ∧
      (∀ g, goalStateCode g ∈ goalRepTCZ 0) ∧
      (∀ g, subjectGoalProbabilityRep goalRepSubject.1 g =
        (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure {g}).toReal) :=
  ⟨goalStateCode_injective, goalStateCode_mem_subjectTCZ,
    goalRepSubject_represents_binaryGoalLaw⟩

/-- 定理19に渡す主体: 定理16の区間層系から固定点が存在し、選んだ同じ固定点の
ゴール確率表象が二値CMI lawの事前分布と一致する。 -/
def subjectGoalModelPremises : Prop :=
  (Nonempty (∃ x : {x : ∀ i : GoalRepLayer, ℝ //
      x ∈ affineInverseLimitSet (fun _ : GoalRepLayer => ℝ)
        goalRepTCZ goalRepProjection},
      inducedAffineInverseLimitMap (fun _ : GoalRepLayer => ℝ)
        goalRepTCZ goalRepProjection
        (by intro β α hβα x hx; simpa [goalRepProjection, goalRepTCZ] using hx)
        goalRepFeedback
        (by intro β α hβα x; apply Subtype.ext; rfl) x = x)) ∧
  inducedAffineInverseLimitMap (fun _ : GoalRepLayer => ℝ)
    goalRepTCZ goalRepProjection
    (by intro β α hβα x hx; simpa [goalRepProjection, goalRepTCZ] using hx)
    goalRepFeedback
    (by intro β α hβα x; apply Subtype.ext; rfl)
    goalRepSubject = goalRepSubject ∧
  (∀ g : Bool, subjectGoalProbabilityRep goalRepSubject.1 g =
    (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure {g}).toReal) ∧
  (∀ g : Bool, subjectGoalProbabilityRep goalRepSubject.1 g =
    (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw
      |>.goalGivenInput () {g}).toReal) ∧
  (Function.Injective goalStateCode ∧
    (∀ g, goalStateCode g ∈ goalRepTCZ 0) ∧
    (∀ g : Bool, subjectGoalProbabilityRep goalRepSubject.1 g =
      (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure {g}).toReal)) ∧
  subjectGoalSelfRepresentationPremises

/-! ### 定理19の全層容量データ

Bool束の各層に同じ一つの許容問題・方策対を置く。恒等埋め込みはjointとCMI評価を
保存し、各層の容量は零なので有限である。物理層の「全問題でH=0」という条件は
このモデルでは成立しないが、原文の条件文「その場合は容量0」は容量が実際に0なので満たす。
-/

abbrev AbstractLayer := Bool

/-- 許容対 `(d,π)` を依存Σ型で保持する。候補では問題記述子と、その問題の許容方策が
それぞれ単点だが、CMI lawはこの対が指す同じ固定対象に割り当てる。 -/
abbrev GoalProblem := Unit
abbrev GoalPolicy (_ : GoalProblem) := Unit
abbrev GoalProblemPolicyPair := Σ d : GoalProblem, GoalPolicy d

noncomputable def layerProblem (_ : AbstractLayer) (_ : GoalProblemPolicyPair) :=
  Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem

def layerPolicy (_ : AbstractLayer) (_ : GoalProblemPolicyPair)
    (z : Unit × Bool) : Tomabechi.Theorem19_22.DecoderRegularityWitness.IndiscreteBit :=
  Tomabechi.Theorem19_22.DecoderRegularityWitness.encode z.2

theorem layerPolicy_measurable (_a : AbstractLayer) (_q : GoalProblemPolicyPair) :
    Measurable (layerPolicy _a _q) :=
  Tomabechi.Theorem19_22.DecoderRegularityWitness.encode_measurable.comp measurable_snd

theorem layerProblem_joint_eq_binaryContextLaw (_a : AbstractLayer)
    (_q : GoalProblemPolicyPair) :
    (layerProblem _a _q).joint =
      Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw.joint := by
  rfl

theorem layerProblem_joint_generated_by_layerPolicy (a : AbstractLayer)
    (q : GoalProblemPolicyPair) :
    (layerProblem a q).joint =
      (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw.input ⊗ₘ
        Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw.goalGivenInput).map
        (fun z => (z.1, z.2, layerPolicy a q z)) := by
  rw [layerProblem_joint_eq_binaryContextLaw]
  exact Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw_generated_by_encode

def layerAdmissible (_ : AbstractLayer) : Set GoalProblemPolicyPair := Set.univ

noncomputable def layerScore (a : AbstractLayer) (q : GoalProblemPolicyPair) : ℝ :=
  (layerProblem a q).score

theorem layerScore_eq_zero (a : AbstractLayer) (q : GoalProblemPolicyPair) :
    layerScore a q = 0 := by
  simp [layerScore, layerProblem,
    Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.score,
    Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_information_eq_zero]

theorem layerProblemPool_nonempty (a : AbstractLayer) :
    (layerAdmissible a).Nonempty := ⟨⟨(), ()⟩, Set.mem_univ _⟩

theorem layerScores_bounded (a : AbstractLayer) :
    BddAbove (layerScore a '' layerAdmissible a) := by
  refine ⟨0, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  rw [layerScore_eq_zero]

theorem layerCapacity_eq_zero (a : AbstractLayer) :
    Tomabechi.Theorem19.dependentLayerCapacity
      (fun _ : AbstractLayer => GoalProblemPolicyPair) layerAdmissible layerScore a = 0 := by
  unfold Tomabechi.Theorem19.dependentLayerCapacity
  apply le_antisymm
  · apply csSup_le (layerProblemPool_nonempty a |>.image (layerScore a))
    rintro y ⟨u, hu, rfl⟩
    rw [layerScore_eq_zero]
  · have hy : layerScore a ⟨(), ()⟩ ∈ layerScore a '' layerAdmissible a :=
      ⟨⟨(), ()⟩, Set.mem_univ _, rfl⟩
    have hle := le_csSup (layerScores_bounded a) hy
    simpa [layerScore_eq_zero] using hle

/-- 全抽象度における容量データと反例候補を、同一構成で束ねる。
主体は定理16の区間層固定点で二値ゴールlawを表象する。各層は明示的な依存Σ型の
`(d,π)` singletonを持ち、問題・方策から同じlawを生成し、層間恒等写像が評価を保存する。 -/
theorem P16_candidate_layer_data_and_failure :
    subjectGoalModelPremises ∧
    (∀ a : AbstractLayer, (layerAdmissible a).Nonempty) ∧
    (∀ a : AbstractLayer, BddAbove (layerScore a '' layerAdmissible a)) ∧
    (∀ a : AbstractLayer,
      Tomabechi.Theorem19.dependentLayerCapacity
        (fun _ : AbstractLayer => GoalProblemPolicyPair) layerAdmissible layerScore a = 0) ∧
    (∀ a b : AbstractLayer, a ≤ b →
      ∃ embedding : GoalProblemPolicyPair → GoalProblemPolicyPair,
        Function.Injective embedding ∧
        (∀ x, x ∈ layerAdmissible a → embedding x ∈ layerAdmissible b) ∧
        (∀ x, layerScore b (embedding x) = layerScore a x) ∧
        (∀ x, (layerProblem b (embedding x)).joint = (layerProblem a x).joint)) ∧
    (∀ _hsupposePhysicalGoalsDeterministic :
      (∀ q : GoalProblemPolicyPair, (layerProblem ⊥ q).goalEntropy = 0),
      Tomabechi.Theorem19.dependentLayerCapacity
        (fun _ : AbstractLayer => GoalProblemPolicyPair) layerAdmissible layerScore ⊥ = 0) ∧
    (Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem.score <
      Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem.goalEntropy) := by
  refine ⟨⟨⟨goalRepLayerSystem_has_fixedPoint_of_theorem16_conditions⟩,
      goalRepSubject_fixed, goalRepSubject_represents_binaryGoalLaw,
      goalRepSubject_matches_law_goalKernel, goalRepSubject_internalGoalRepresentation,
      subjectGoalSelfRepresentationPremises_holds⟩,
      ?_, ?_, ?_, ?_, ?_,
    Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_score_lt_goalEntropy⟩
  · intro a
    exact layerProblemPool_nonempty a
  · intro a
    exact layerScores_bounded a
  · intro a
    exact layerCapacity_eq_zero a
  · intro a b hab
    refine ⟨id, Function.injective_id, ?_, ?_⟩
    · intro x hx
      exact Set.mem_univ _
    · constructor
      · intro x
        rfl
      · intro x
        rfl
  · intro hdeterministic
    exact layerCapacity_eq_zero ⊥

/-- C4候補package。定理16区間層系の固定点・同じ固定点の二値ゴール確率表象・
全層容量データ・失敗する直接問題と、可測単射方策・生成jointを束ねる。 -/
def P16_candidate_package_spec : Prop :=
    (subjectGoalModelPremises ∧
      (∀ a : AbstractLayer, (layerAdmissible a).Nonempty) ∧
      (∀ a : AbstractLayer, BddAbove (layerScore a '' layerAdmissible a)) ∧
      (∀ a : AbstractLayer,
        Tomabechi.Theorem19.dependentLayerCapacity
          (fun _ : AbstractLayer => GoalProblemPolicyPair) layerAdmissible layerScore a = 0) ∧
      (∀ a b : AbstractLayer, a ≤ b →
        ∃ embedding : GoalProblemPolicyPair → GoalProblemPolicyPair,
          Function.Injective embedding ∧
          (∀ x, x ∈ layerAdmissible a → embedding x ∈ layerAdmissible b) ∧
          (∀ x, layerScore b (embedding x) = layerScore a x) ∧
          (∀ x, (layerProblem b (embedding x)).joint = (layerProblem a x).joint)) ∧
      (∀ _hdeterministic :
        (∀ q : GoalProblemPolicyPair, (layerProblem ⊥ q).goalEntropy = 0),
        Tomabechi.Theorem19.dependentLayerCapacity
          (fun _ : AbstractLayer => GoalProblemPolicyPair) layerAdmissible layerScore ⊥ = 0) ∧
      Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem.score ≠
        Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem.goalEntropy) ∧
    Measurable (fun z : Unit × Bool =>
      Tomabechi.Theorem19_22.DecoderRegularityWitness.encode z.2) ∧
    Function.Injective Tomabechi.Theorem19_22.DecoderRegularityWitness.encode ∧
    Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw.joint =
      (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw.input ⊗ₘ
        Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw.goalGivenInput).map
        (fun z => (z.1, z.2, Tomabechi.Theorem19_22.DecoderRegularityWitness.encode z.2)) ∧
    (∀ a q, Measurable (layerPolicy a q)) ∧
    (∀ a q, (layerProblem a q).joint =
      Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw.joint) ∧
    (∀ a q, (layerProblem a q).joint =
      (Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw.input ⊗ₘ
        Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw.goalGivenInput).map
        (fun z => (z.1, z.2, layerPolicy a q z))) ∧
    Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem.information = 0 ∧
    Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem.goalEntropy = Real.log 2 ∧
    Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem.information ≠ ⊤ ∧
    (∀ a q, 0 < (layerProblem a q).goalEntropy)
theorem P16_candidate_package_with_goalProbabilityRepresentation :
  P16_candidate_package_spec := by
  have hmodel := P16_candidate_layer_data_and_failure
  have hstrict := Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_score_lt_goalEntropy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hmodel.1, hmodel.2.1, hmodel.2.2.1, hmodel.2.2.2.1,
      hmodel.2.2.2.2.1, hmodel.2.2.2.2.2.1, ne_of_lt hstrict⟩
  · exact Tomabechi.Theorem19_22.DecoderRegularityWitness.encode_measurable.comp
      measurable_snd
  · exact Tomabechi.Theorem19_22.DecoderRegularityWitness.encode_injective
  · exact Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw_generated_by_encode
  · exact fun a q => layerPolicy_measurable a q
  · exact fun a q => layerProblem_joint_eq_binaryContextLaw a q
  · exact fun a q => layerProblem_joint_generated_by_layerPolicy a q
  · exact Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_information_eq_zero
  · exact Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_goalEntropy_eq_log_two
  · rw [Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_information_eq_zero]
    norm_num
  · intro a q
    change 0 < Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem.goalEntropy
    rw [Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_goalEntropy_eq_log_two]
    exact Real.log_pos (by norm_num)

/-- P16の具体的なモデルデータ。主体、直接law、決定論的方策、および各抽象層の
問題・方策族を一つの対象に保持する。 -/
structure P16ConcreteModel where
  subject : GoalRepSubjectState
  directProblem : Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem
  policy : Unit × Bool →
    Tomabechi.Theorem19_22.DecoderRegularityWitness.IndiscreteBit
  problemFamily : AbstractLayer → GoalProblemPolicyPair →
    Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem
  policyFamily : AbstractLayer → GoalProblemPolicyPair → Unit × Bool →
    Tomabechi.Theorem19_22.DecoderRegularityWitness.IndiscreteBit
  packageEvidence : P16_candidate_package_spec

noncomputable def p16ConcreteModel : P16ConcreteModel where
  subject := goalRepSubject
  directProblem := Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem
  policy := fun z => Tomabechi.Theorem19_22.DecoderRegularityWitness.encode z.2
  problemFamily := layerProblem
  policyFamily := layerPolicy
  packageEvidence := P16_candidate_package_with_goalProbabilityRepresentation

def P16ConcreteModel.OriginalPremises (M : P16ConcreteModel) : Prop :=
  M.subject = goalRepSubject ∧
    M.directProblem = Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem ∧
    M.policy = (fun z => Tomabechi.Theorem19_22.DecoderRegularityWitness.encode z.2) ∧
    M.problemFamily = layerProblem ∧ M.policyFamily = layerPolicy ∧
      P16_candidate_package_spec

/-- C4の存在形: 一つの主体/law/方策/層族を持つ同一モデルで原文の明示抽象前提を
満たし、決定論的単射方策による情報達成等式を否定する。 -/
theorem P16_exists_concrete_counterexample_under_measurable_output_reading :
    ∃ M : P16ConcreteModel,
      M.OriginalPremises ∧
        M.directProblem.score ≠ M.directProblem.goalEntropy := by
  refine ⟨p16ConcreteModel, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl,
      P16_candidate_package_with_goalProbabilityRepresentation⟩
  · change Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem.score ≠
      Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem.goalEntropy
    exact ne_of_lt
      Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_score_lt_goalEntropy

end Tomabechi.Theorem19_Counterexample

#print axioms Tomabechi.Theorem19_Counterexample.subjectFixedPointExists_of_originalConditions
#print axioms Tomabechi.Theorem19_Counterexample.goalRepLayerSystem_has_fixedPoint_of_theorem16_conditions
#print axioms Tomabechi.Theorem19_Counterexample.goalRepSubject_represents_binaryGoalLaw
#print axioms Tomabechi.Theorem19_Counterexample.subjectGoalSelfRepresentationPremises_holds
#print axioms Tomabechi.Theorem19_Counterexample.goalRepSubjectRepresentation_encodes_goalLaw
#print axioms Tomabechi.Theorem19_Counterexample.P16_candidate_layer_data_and_failure
#print axioms Tomabechi.Theorem19_Counterexample.P16_candidate_package_with_goalProbabilityRepresentation
#print axioms Tomabechi.Theorem19_Counterexample.P16_exists_concrete_counterexample_under_measurable_output_reading
