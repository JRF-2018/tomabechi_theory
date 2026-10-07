import Tomabechi.Consistency.ConsistencyR1_CommonLattice
import Tomabechi.Consistency.ConsistencyC1_ConsensusControl
import Tomabechi.Consistency.ConsistencyC3_StagePresentation
import Mathlib.MeasureTheory.Measure.Basic

/-!
# R1: 定理20の有限情報束を共通束へ移す

定理20の二主体有限情報束を、共通概念束の0/1指示関数部分へ写す。
有限集合の演算と順序は共通束側でも保存される。
-/

namespace Tomabechi.Consistency.R1

open MeasureTheory
open Tomabechi.Consistency.ConsistencyC1Consensus

/-- 定理19の情報lawを全共通束へ延長する。底では物理層lawを保ち、
底以外の全概念点では同じ正情報lawを使う。 -/
noncomputable def commonConceptInformationLaw
    (a : CommonConcept) : Measure (Unit × Bool × Bool) :=
  if a = ⊥ then Tomabechi.Consistency.C3.physicalLayerLaw.joint
  else Tomabechi.Consistency.C3.upperJoint

/-- 情報lawからTheorem 19のjoint/reference問題を同時に構成する。 -/
noncomputable def commonConceptInformationPair (a : CommonConcept) :
    Tomabechi.Consistency.C3.C3CMIPair :=
  if a = ⊥ then Tomabechi.Consistency.C3.physicalCMIPair
  else Tomabechi.Consistency.C3.upperCMIPair

theorem commonConceptInformationLaw_bottom :
    commonConceptInformationLaw (⊥ : CommonConcept) =
      Tomabechi.Consistency.C3.physicalLayerLaw.joint := by
  simp [commonConceptInformationLaw]

theorem commonConceptInformationLaw_of_ne_bottom
    {a : CommonConcept} (ha : a ≠ ⊥) :
    commonConceptInformationLaw a = Tomabechi.Consistency.C3.upperJoint := by
  simp [commonConceptInformationLaw, ha]

theorem commonConceptInformationLaw_isProbability
    (a : CommonConcept) : IsProbabilityMeasure (commonConceptInformationLaw a) := by
  by_cases ha : a = ⊥
  · subst a
    simpa [commonConceptInformationLaw] using
      Tomabechi.Consistency.C3.physicalLayerLaw.joint_isProbabilityMeasure
  · rw [commonConceptInformationLaw_of_ne_bottom ha]
    exact Tomabechi.Consistency.C3.upperJoint_isProbability

theorem commonConceptInformationPair_joint_eq
    (a : CommonConcept) :
    Tomabechi.Theorem19_22.directActionGoalJoint
      (commonConceptInformationLaw a) =
      (commonConceptInformationPair a).joint := by
  by_cases ha : a = ⊥ <;> simp [commonConceptInformationLaw,
    commonConceptInformationPair, ha, Tomabechi.Consistency.C3.physicalCMIPair,
    Tomabechi.Consistency.C3.upperCMIPair]

theorem commonConceptInformationPair_reference_eq
    (a : CommonConcept)
    [IsProbabilityMeasure (commonConceptInformationLaw a)] :
    Tomabechi.Theorem19_22.directCMIReference
      (commonConceptInformationLaw a) =
      (commonConceptInformationPair a).reference := by
  by_cases ha : a = ⊥
  · subst a
    letI : IsProbabilityMeasure Tomabechi.Consistency.C3.physicalLayerLaw.joint :=
      Tomabechi.Consistency.C3.physicalLayerLaw.joint_isProbabilityMeasure
    simp only [commonConceptInformationLaw, commonConceptInformationPair,
      ↓reduceIte]
    change Tomabechi.Theorem19_22.directCMIReference
        Tomabechi.Consistency.C3.physicalLayerLaw.joint =
      Tomabechi.Theorem19_22.directCMIReference
        Tomabechi.Consistency.C3.physicalLayerLaw.joint
    rfl
  · letI : IsProbabilityMeasure Tomabechi.Consistency.C3.upperJoint :=
      Tomabechi.Consistency.C3.upperJoint_isProbability
    simp [commonConceptInformationLaw, commonConceptInformationPair, ha,
      Tomabechi.Consistency.C3.upperCMIPair]

theorem commonConceptInformationPair_score_bottom :
    Tomabechi.Consistency.C3.cmiPairScore
      (commonConceptInformationPair (⊥ : CommonConcept)) = 0 := by
  simpa [commonConceptInformationPair] using
    Tomabechi.Consistency.C3.physicalCMIPair_score_zero

theorem commonConceptInformationPair_score_of_ne_bottom
    {a : CommonConcept} (ha : a ≠ ⊥) :
    Tomabechi.Consistency.C3.cmiPairScore (commonConceptInformationPair a) =
      Real.log 2 := by
  simp [commonConceptInformationPair, ha,
    Tomabechi.Consistency.C3.upperCMIPair_score_log_two]

theorem commonConceptInformationPair_score_positive_of_ne_bottom
    {a : CommonConcept} (ha : a ≠ ⊥) :
    0 < Tomabechi.Consistency.C3.cmiPairScore (commonConceptInformationPair a) := by
  rw [commonConceptInformationPair_score_of_ne_bottom ha]
  exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

theorem layerAddress_zero_eq_bottom :
    layerAddressEmbedding (0 : WithTop ℕ) = ⊥ := by
  change diagonalLayer 0 = ⊥
  ext i
  simp [diagonalLayer, layerRatio]

theorem layerAddress_succ_ne_bottom (n : ℕ) :
    layerAddressEmbedding ((n + 1 : ℕ) : WithTop ℕ) ≠ ⊥ := by
  intro h
  have hpos : 0 < layerRatio (n + 1) := by
    unfold layerRatio
    positivity
  change layerAddress ((n + 1 : ℕ) : WithTop ℕ) = ⊥ at h
  rw [layerAddress_nat] at h
  have hcoord := congrFun h 0
  have hval := congrArg (fun z : unitInterval => (z : ℝ)) hcoord
  simp only [diagonalLayer] at hval
  exact (not_lt_of_ge (le_of_eq hval)) hpos

theorem commonConceptInformationLaw_recovers_physical_address :
    commonConceptInformationLaw
      (layerAddressEmbedding (0 : WithTop ℕ)) =
      Tomabechi.Consistency.C3.physicalLayerLaw.joint := by
  rw [layerAddress_zero_eq_bottom]
  exact commonConceptInformationLaw_bottom

theorem commonConceptInformationLaw_recovers_upper_address (n : ℕ) :
    commonConceptInformationLaw
      (layerAddressEmbedding ((n + 1 : ℕ) : WithTop ℕ)) =
      Tomabechi.Consistency.C3.upperJoint :=
  commonConceptInformationLaw_of_ne_bottom (layerAddress_succ_ne_bottom n)

/-- 定理20の有限情報束を共通束の部分集合として表したもの。 -/
def c1InformationImage : Set CommonConcept :=
  finiteSymbolsEmbedding '' c1SymbolInfoLattice

/-- 定理20の象徴集合を共通束へ写した集合。 -/
def c1SymbolImage : Set CommonConcept :=
  finiteSymbolsEmbedding '' c1SymbolW

/-- 定理20の住所候補も同じ写像を通して共通束の元にする。 -/
def c1SymbolAddressImage : CommonConcept :=
  finiteSymbolsEmbedding c1SymbolAddress

theorem c1SymbolImage_subset_c1InformationImage :
    c1SymbolImage ⊆ c1InformationImage := by
  intro a ha
  rcases ha with ⟨s, hs, rfl⟩
  exact ⟨s, c1SymbolW_subset_info hs, rfl⟩

theorem c1InformationImage_bottom : (⊥ : CommonConcept) ∈ c1InformationImage := by
  refine ⟨∅, c1SymbolInfo_bot, ?_⟩
  simp [finiteSymbolsEmbedding_empty]

theorem c1InformationImage_join_closed {a b : CommonConcept}
    (ha : a ∈ c1InformationImage) (hb : b ∈ c1InformationImage) :
    a ⊔ b ∈ c1InformationImage := by
  rcases ha with ⟨x, hx, rfl⟩
  rcases hb with ⟨y, hy, rfl⟩
  refine ⟨x ∪ y, c1SymbolInfo_join_closed hx hy, ?_⟩
  rw [finiteSymbolsEmbedding_union]

theorem c1InformationImage_meet_closed {a b : CommonConcept}
    (ha : a ∈ c1InformationImage) (hb : b ∈ c1InformationImage) :
    a ⊓ b ∈ c1InformationImage := by
  rcases ha with ⟨x, hx, rfl⟩
  rcases hb with ⟨y, hy, rfl⟩
  refine ⟨x ∩ y, c1SymbolInfo_meet_closed hx hy, ?_⟩
  rw [finiteSymbolsEmbedding_inter]

theorem c1InformationImage_proper : c1InformationImage ≠ Set.univ := by
  intro hEq
  have hmem : coordinateEmbedding 1 (1 : unitInterval) ∈ c1InformationImage := by
    rw [hEq]
    exact Set.mem_univ _
  rcases hmem with ⟨s, hs, hse⟩
  have hcoord0 : finiteSymbolsEmbedding s 0 = 0 := by
    have := congrFun hse 0
    simpa [c1SymbolAddressImage, coordinateEmbedding] using this
  have hcoord1 : finiteSymbolsEmbedding s 1 = 1 := by
    have := congrFun hse 1
    simpa [coordinateEmbedding] using this
  rcases hs with hs | hs
  · subst s
    simp [finiteSymbolsEmbedding] at hcoord1
  · subst s
    simp [finiteSymbolsEmbedding] at hcoord0

theorem c1SymbolImage_eq_singleton :
    c1SymbolImage = {c1SymbolAddressImage} := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [c1SymbolImage, c1SymbolAddressImage, c1SymbolW, c1SymbolAddress] using hs
  · intro hx
    have hx' : x = c1SymbolAddressImage := by simpa using hx
    subst x
    exact ⟨c1SymbolAddress, by simp [c1SymbolW, c1SymbolAddress], rfl⟩

theorem c1SymbolAddressImage_isLUB :
    IsLUB c1SymbolImage c1SymbolAddressImage := by
  rw [c1SymbolImage_eq_singleton]
  constructor
  · intro x hx
    have : x = c1SymbolAddressImage := by simpa using hx
    simpa [this]
  · intro y hy
    exact hy (by simp)

end Tomabechi.Consistency.R1
