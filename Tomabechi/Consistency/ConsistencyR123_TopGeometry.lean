import Tomabechi.Consistency.ConsistencyR1_C6FullIndex

/-!
# 共通束頂点の内積空間構造

頂点の型同定から解析構造を移し、既存の距離との一致を証明する。
インスタンスはこのファイル内で局所的に使い、共有署名の距離を変更しない。
-/
noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.R1 Tomabechi.Consistency.C6
open Tomabechi.Examples.Theorem27Op
private abbrev chartNorm (S : Type) (h : S = E2) : NormedAddCommGroup S := by
  subst S
  infer_instance
private abbrev chartInner (S : Type) (h : S = E2) :
    @InnerProductSpace ℝ S _ (chartNorm S h).toSeminormedAddCommGroup := by
  subst S
  exact inferInstance
/-- 頂点の型同定から得るノルム付き加法群。 -/
abbrev sharedTopNorm : NormedAddCommGroup (fullCommonLayerState (⊤ : CommonConcept)) :=
  chartNorm _ fullCommonTopState_eq_c6Top
local instance : NormedAddCommGroup (fullCommonLayerState (⊤ : CommonConcept)) := sharedTopNorm

/-- 同じノルムに対応する実内積。 -/
abbrev sharedTopInner : InnerProductSpace ℝ (fullCommonLayerState (⊤ : CommonConcept)) :=
  chartInner _ fullCommonTopState_eq_c6Top
private theorem chartDist (S : Type) (h : S = E2) (x y : S) :
    @dist S (chartNorm S h).toDist x y = dist (cast h x) (cast h y) := by
  subst S
  rfl
local instance : InnerProductSpace ℝ (fullCommonLayerState (⊤ : CommonConcept)) := sharedTopInner

/-- 既存の頂点距離を変えずに一般解析入口を使える。 -/
theorem sharedTopMetric_eq_normMetric : fullCommonTopPseudoMetricSpace =
    (@NormedAddCommGroup.toMetricSpace (fullCommonLayerState (⊤ : CommonConcept)) sharedTopNorm).toPseudoMetricSpace := by
  apply PseudoMetricSpace.ext
  change Dist.mk _ = Dist.mk _
  congr 1
  funext x y
  exact (chartDist _ fullCommonTopState_eq_c6Top x y).symm
private def chartLinear (S : Type) (h : S = E2) :
    letI := chartNorm S h
    letI := chartInner S h
    S ≃ₗᵢ[ℝ] E2 := by
  subst S
  exact LinearIsometryEquiv.refl ℝ E2
private theorem chartComplete (S : Type) (h : S = E2) :
    letI := chartNorm S h
    CompleteSpace S := by
  subst S
  infer_instance
private theorem chartLinear_apply (S : Type) (h : S = E2) (x : S) :
    chartLinear S h x = cast h x := by
  subst S
  rfl

/-- 移されたノルムと同じ既存距離で頂点は完備。 -/
theorem sharedTopComplete : CompleteSpace (fullCommonLayerState (⊤ : CommonConcept)) := by
  rw [sharedTopMetric_eq_normMetric]
  exact chartComplete _ fullCommonTopState_eq_c6Top


/-- 頂点型同定は実線形等長同型でもある。 -/
def sharedTopLinearIsometryEquiv :
    fullCommonLayerState (⊤ : CommonConcept) ≃ₗᵢ[ℝ] E2 :=
  chartLinear _ fullCommonTopState_eq_c6Top

/-- 解析用の線形同型は既存の頂点保存写像と同じ写像である。 -/
theorem sharedTopLinearIsometryEquiv_apply (x : fullCommonLayerState (⊤ : CommonConcept)) :
    sharedTopLinearIsometryEquiv x = fullCommonTopStateEquiv x :=
  chartLinear_apply _ fullCommonTopState_eq_c6Top x

private abbrev replacePseudo {S : Type} (g : NormedAddCommGroup S) (m : PseudoMetricSpace S)
    (hm : m = g.toPseudoMetricSpace) : NormedAddCommGroup S := {
  g with
  toPseudoMetricSpace := m
  eq_of_dist_eq_zero := by rw [hm]; exact g.eq_of_dist_eq_zero
  dist_eq := by rw [hm]; exact g.dist_eq }

private theorem replacePseudo_eq {S : Type} (g : NormedAddCommGroup S) (m : PseudoMetricSpace S)
    (hm : m = g.toPseudoMetricSpace) : replacePseudo g m hm = g := by
  cases hm
  rfl

private abbrev replaceInner {S : Type} (g : NormedAddCommGroup S) (m : PseudoMetricSpace S)
    (hm : m = g.toPseudoMetricSpace) (inn : @InnerProductSpace ℝ S _ g.toSeminormedAddCommGroup) :
    @InnerProductSpace ℝ S _ (replacePseudo g m hm).toSeminormedAddCommGroup :=
  (congrArg (fun n : NormedAddCommGroup S =>
    @InnerProductSpace ℝ S _ n.toSeminormedAddCommGroup) (replacePseudo_eq g m hm)).mpr inn

private def replaceIso {S : Type} (g : NormedAddCommGroup S) (m : PseudoMetricSpace S)
    (hm : m = g.toPseudoMetricSpace) (inn : @InnerProductSpace ℝ S _ g.toSeminormedAddCommGroup)
    (iso : letI := g; letI := inn; S ≃ₗᵢ[ℝ] E2) :
    letI := replacePseudo g m hm
    letI := replaceInner g m hm inn
    S ≃ₗᵢ[ℝ] E2 := by
  cases hm
  exact iso

/-- 既存の距離構造を定義的に含む解析用ノルム。 -/
abbrev sharedTopCompatibleNorm :=
  replacePseudo sharedTopNorm fullCommonTopPseudoMetricSpace sharedTopMetric_eq_normMetric

/-- 既存距離を含むノルムに対応する、同じ実内積。 -/
abbrev sharedTopCompatibleInner :=
  replaceInner sharedTopNorm fullCommonTopPseudoMetricSpace sharedTopMetric_eq_normMetric sharedTopInner

/-- 既存の距離構造と解析構造の親インスタンスは定義的に一致する。 -/
theorem sharedTopCompatibleMetric : sharedTopCompatibleNorm.toPseudoMetricSpace =
    fullCommonTopPseudoMetricSpace := rfl

/-- 既存距離を保つ内積空間構造での頂点等長同型。 -/
def sharedTopCompatibleIso :
    letI := sharedTopCompatibleNorm
    letI := sharedTopCompatibleInner
    fullCommonLayerState (⊤ : CommonConcept) ≃ₗᵢ[ℝ] E2 :=
  replaceIso sharedTopNorm fullCommonTopPseudoMetricSpace sharedTopMetric_eq_normMetric
    sharedTopInner sharedTopLinearIsometryEquiv

private theorem replaceIso_apply {S : Type} (g : NormedAddCommGroup S) (m : PseudoMetricSpace S)
    (hm : m = g.toPseudoMetricSpace) (inn : @InnerProductSpace ℝ S _ g.toSeminormedAddCommGroup)
    (iso : letI := g; letI := inn; S ≃ₗᵢ[ℝ] E2) (x : S) :
    replaceIso g m hm inn iso x = iso x := by
  cases hm
  rfl

/-- 距離構造を合わせた解析同型も元の頂点写像と同じである。 -/
theorem sharedTopCompatibleIso_apply (x : fullCommonLayerState (⊤ : CommonConcept)) :
    sharedTopCompatibleIso x = fullCommonTopStateEquiv x :=
  (replaceIso_apply sharedTopNorm fullCommonTopPseudoMetricSpace sharedTopMetric_eq_normMetric
    sharedTopInner sharedTopLinearIsometryEquiv x).trans (sharedTopLinearIsometryEquiv_apply x)

#print axioms sharedTopCompatibleIso

#print axioms sharedTopMetric_eq_normMetric
#print axioms sharedTopComplete
#print axioms sharedTopLinearIsometryEquiv
end Tomabechi.Consistency.R123
