import Tomabechi.Consistency.ConsistencyR123_Shared16Indexing

/-!
# 定理16の担体を層別 TCZ と同定

原文 §7 は `K_{i,α}(h) := TCZ_{i,α}(h) ⊂ E_{i,α}` と書く。従来、定理16の系の担体は
旧署名の `(selfRepresentation h).TCZ i`（全層で同じ区間 `[0,1]`）を読むだけで、
N.data の層 α の制御データから作った TCZ との等式がなかった。また、存在節・
表象節・縮小節の前件は具体定理の側にだけあり、述語の外にあった。

**案A（観測で結ぶ）を採る。** 既存の区間担体は保ち、層 α = `index16 i` と履歴 h について
`SharedModelSignature.layerTCZ N h i` を次の同時刻到達 ∩ 評価閾値集合として定義する。

* 履歴の中心 `c = historyCenter h` での共有核の一歩 `step c t E z`
  （t ∈ [0,1]、初期の認知座標が [0,1]）の認知座標に到達する点であって、
* N.data の **層 α の実走行費**（`N.data.runningCost (index16 i) … 0`）が閾値
  `1 + 16·(1/2) = 9` 以下（すなわち評価 `V_h ≤ 1/2`）であるもの。

層 α の状態型（`fullCommonLayerState (index16 i)`）と旧有限層の `AgentState` は
`fullCommonLayerIndex_layerAddress` の型同値で結ぶ（`layerStateCast`）。
証明するのは、`AdditionalConditions N.legacy` と `SharedDataPreservation N` のもとで
`(N.legacy.selfRepresentation h).TCZ i = N.layerTCZ h i = [0,1]` であること、および
定理16の存在節・表象節・縮小節（`Theorem16EntryClause`）を同じ述語の field に入れることである。

**範囲：** 層 α の制御問題は「共有核の一歩と層 α の費用」を通して使う。層ごとに
独立の制御問題から TCZ を再構成して担体が層で変わる案B は採らない（担体は全層で
`[0,1]` のまま）。定理16の原文の仮定のうち担体が局所凸 Hausdorff であることは
`[0,1] ⊂ ℝ` で成り立つ。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1
open Tomabechi.Theorem16_25 Tomabechi.Consistency.C2
open Tomabechi.Consistency.C4 Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus

/-- 層 `index16 i` の状態型と旧有限層 `AgentState` の同一視（型の等式からの cast）。 -/
def layerStateCast (i : ℕ) (x : AgentState) : fullCommonLayerState (index16 i) :=
  cast (congrArg C6LayeredState (fullCommonLayerIndex_layerAddress (WithTop.some i))).symm x

/-- 層 α = `index16 i` の方策型と旧有限層の方策型の同一視。 -/
def layerPolicyCast (i : ℕ) (u : C1GainSignal) : fullCommonLayerPolicy (index16 i) :=
  cast (congrArg C6LayeredPolicy (fullCommonLayerIndex_layerAddress (WithTop.some i))).symm u

/-- 評価閾値 `V_h ≤ 1/2` に対応する実走行費の閾値 `1 + 16 · (1/2)`。 -/
def layerCostThreshold : ℝ := 9

/-- 履歴 h・層 `index16 i` の TCZ（案A）。同時刻到達 ∩ 層 α の実走行費の閾値集合。 -/
def SharedModelSignature.layerTCZ (N : SharedModelSignature) (h : Bool) (i : ℕ) : Set ℝ :=
  {y | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ (z : CompleteState) (E : ℝ),
    cognitiveCoordinate z ∈ Set.Icc (0 : ℝ) 1 ∧
    y = cognitiveCoordinate (N.legacy.step (N.legacy.historyCenter h) t E z) ∧
    N.data.runningCost (index16 i) (layerPolicyCast i (N.legacy.informationPolicy false))
      (layerStateCast i
        (N.legacy.finiteProjection 0 (N.legacy.historyCenter h)
          (N.legacy.step (N.legacy.historyCenter h) t E z))) 0 ≤ layerCostThreshold}

/-- 有限層の費用は、型の cast を通しても旧有限層の費用に等しい。 -/
theorem SharedDataPreservation.layerCost_eq {N : SharedModelSignature}
    (h : SharedDataPreservation N) (i : ℕ) (u : C1GainSignal) (x : AgentState) (t : ℝ) :
    N.data.runningCost (index16 i) (layerPolicyCast i u) (layerStateCast i x) t =
      N.legacy.data.runningCost (some i) u x t := by
  rw [h.runningCost]
  have key : ∀ (idx : CommonLayer) (e : idx = (WithTop.some i))
      (π : C6LayeredPolicy idx) (y : C6LayeredState idx),
      N.legacy.data.runningCost idx π y t =
        N.legacy.data.runningCost (some i) (cast (congrArg C6LayeredPolicy e) π)
          (cast (congrArg C6LayeredState e) y) t := by
    intro idx e; subst e; intros; rfl
  refine (key _ (fullCommonLayerIndex_layerAddress (WithTop.some i)) _ _).trans ?_
  simp only [layerPolicyCast, layerStateCast]
  congr 1 <;> exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- 層 α の実走行費は、同じ履歴中心の二次評価 `1 + 16 V_h` に等しい。 -/
theorem SharedModelSignature.layerCost_eq_potential {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy)
    (hi : ℕ) (u : C1GainSignal) (h : Bool) (z : CompleteState) (t : ℝ) :
    N.data.runningCost (index16 hi) (layerPolicyCast hi u)
      (layerStateCast hi (N.legacy.finiteProjection 0 (N.legacy.historyCenter h) z)) t =
      1 + 16 * theorem16_intervalGradientPotential h (cognitiveCoordinate z) := by
  rw [hp.layerCost_eq, hA.toCommonDataCouplings.core_finite_cost, hA.c4_evaluation]

theorem SharedModelSignature.layerTCZ_eq_carrier {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) (h : Bool) (i : ℕ) :
    N.layerTCZ h i = Set.Icc (0 : ℝ) 1 := by
  have hc := hA.history_centers
  have hflow := hA.history_flows
  have hcore := hA.toCommonDataCouplings.core_cognitive
  ext y
  constructor
  · rintro ⟨t, ht, z, E, hz, rfl, _⟩
    rw [hcore, hc]
    have := theorem16_intervalGradientFlow_stays h (cognitiveCoordinate z) t hz ht
    simpa [theorem16_intervalGradientFlow, hc] using this
  · intro hy
    refine ⟨0, by norm_num, (y, 0), 0, hy, ?_, ?_⟩
    · rw [hcore]; simp [cognitiveCoordinate]
    · rw [SharedModelSignature.layerCost_eq_potential hp hA, hcore, hc]
      have hz : cognitiveCoordinate ((y, (0 : ℝ)) : CompleteState) = y := rfl
      rw [hz]
      simp only [Real.exp_zero, neg_zero, mul_one]
      rw [add_sub_cancel, theorem16_intervalGradientPotential, layerCostThreshold]
      have hcen : theorem16_intervalGradientCenter h ∈ Set.Icc (0 : ℝ) 1 := by
        cases h <;> norm_num [theorem16_intervalGradientCenter]
      have habs := abs_le.mp (show |y - theorem16_intervalGradientCenter h| ≤ 1 by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2, hcen.1, hcen.2])
      nlinarith [habs.1, habs.2]


/-- 定理16の存在節・表象節・縮小節（C4 一般入口の第一連言）。
履歴ごとの逆極限に一意な固定点があり、表象写像の下でも固定され、関係に属し、
率 `exp(-1)` で幾何収束する。 -/
def Theorem16EntryClause : Prop :=
  ∀ h, letI := theorem16_intervalGradientFlowC4Metric h; ∃! x : C4InverseLimit h,
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      theorem16_intervalGradientFlowLayerSystem.carrier
      theorem16_intervalGradientFlowLayerSystem.project
      theorem16_intervalGradientFlowLayerSystem.projectMaps
      theorem16_intervalGradientFlowLayerSystem.feedback
      theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h x = x ∧
    theorem16_intervalGradientFlowC4RepresentedMap h
      ((theorem16_intervalGradientFlowC4SelfRepresentation h).represent x) =
        (theorem16_intervalGradientFlowC4SelfRepresentation h).represent x ∧
    ((theorem16_intervalGradientFlowC4SelfRepresentation h).represent x, x) ∈
      (theorem16_intervalGradientFlowC4SelfRepresentation h).relation ∧
    ∀ (x₀ : C4InverseLimit h) (n : ℕ),
      dist
        ((historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
          theorem16_intervalGradientFlowLayerSystem.carrier
          theorem16_intervalGradientFlowLayerSystem.project
          theorem16_intervalGradientFlowLayerSystem.projectMaps
          theorem16_intervalGradientFlowLayerSystem.feedback
          theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h)^[n] x₀) x ≤
        (Real.exp (-1)) ^ n * dist x₀ x

theorem theorem16EntryClause_holds : Theorem16EntryClause :=
  theorem16_intervalGradientFlowC4_generalEntryConnection.1

/-- 定理16の担体と層別 TCZ の同定と、存在・表象・縮小節を
同じ N の述語に入れた受入型。層 α = `index16 i`。 -/
structure Shared16LayerTCZInputs (N : SharedModelSignature) : Prop where
  /-- 旧署名の自己表象の TCZ は、層 α の制御データから作った TCZ に等しい。 -/
  tcz_eq : ∀ (h : Bool) (i : ℕ), (N.legacy.selfRepresentation h).TCZ i = N.layerTCZ h i
  /-- 定理16の層系の担体 K_{i,α}(h) は同じ層別 TCZ に等しい。 -/
  carrier_eq : ∀ (h : Bool) (i : ℕ),
    theorem16_intervalGradientFlowLayerSystem.carrier h i = N.layerTCZ h i
  /-- 層 α の実走行費は同じ履歴中心の二次評価 `1 + 16 V_h` に等しい（TCZ の評価が層の費用）。 -/
  layer_cost : ∀ (h : Bool) (i : ℕ) (u : C1GainSignal) (z : CompleteState) (t : ℝ),
    N.data.runningCost (index16 i) (layerPolicyCast i u)
      (layerStateCast i (N.legacy.finiteProjection 0 (N.legacy.historyCenter h) z)) t =
      1 + 16 * theorem16_intervalGradientPotential h (cognitiveCoordinate z)
  /-- 存在節・表象節・縮小節の前件と結論。 -/
  entry_clause : Theorem16EntryClause

theorem SharedModelSignature.shared16LayerTCZInputs {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) :
    Shared16LayerTCZInputs N where
  tcz_eq := fun h i => by
    rw [hA.toCommonDataCouplings.self_tcz, theorem16_intervalGradientFlowC4TCZ_eq_carrier,
      SharedModelSignature.layerTCZ_eq_carrier hp hA]
  carrier_eq := fun h i => by
    rw [SharedModelSignature.layerTCZ_eq_carrier hp hA]; rfl
  layer_cost := fun h i u z t => SharedModelSignature.layerCost_eq_potential hp hA i u h z t
  entry_clause := theorem16EntryClause_holds

theorem sharedModel_shared16LayerTCZInputs : Shared16LayerTCZInputs sharedModel :=
  SharedModelSignature.shared16LayerTCZInputs sharedModel_preservation
    sharedModel_explicitAdditionalConditions.legacy

/-- 容量入力・定理16の添字入力に、定理16の担体の層別 TCZ 同定を加えた存在宣言。 -/
theorem final_consistency_with_16layerTCZ :
    ∃ N : SharedModelSignature,
      FullOriginalPremises N ∧ ExplicitAdditionalConditions N ∧ SharedNondegenerate N ∧
        SharedCapacityInputs N ∧ Shared16Indexing N ∧ Shared16LayerTCZInputs N :=
  ⟨sharedModel, sharedModel_fullOriginalPremises, sharedModel_explicitAdditionalConditions,
    sharedModel_nondegenerate, sharedModel_capacityInputs, sharedModel_shared16Indexing,
    sharedModel_shared16LayerTCZInputs⟩

#print axioms SharedModelSignature.layerTCZ_eq_carrier
#print axioms SharedModelSignature.shared16LayerTCZInputs
#print axioms final_consistency_with_16layerTCZ
end Tomabechi.Consistency.R123
