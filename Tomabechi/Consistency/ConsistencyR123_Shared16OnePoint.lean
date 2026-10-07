import Tomabechi.Consistency.ConsistencyR123_GenealogyMortality

/-!
# 定理16の層別 TCZ を一点の初期状態から

以前の `layerTCZ` と C4 の TCZ は、**初期集合 `[0,1]` 全体**から時刻 `τ∈[0,1]` で到達する点の
集合として作られていた。§2.1 の TCZ(x₀)=⋃_{τ≥0}[ℛ(τ;x₀)∩Ω_θ(τ)]（閉到達スライスは `K_π(x₀)∩Ω_θ`、
`K_π` は閉包）とは読みが違う。ここでは **一点の初期状態 `x₀ = 1/2`** から作り直す。

* 一点からの勾配流の到達集合 `{c_h + (x₀−c_h)e^{−t} | t ≥ 0}` の閉包は線分
  `seg16 h`（`h=false`：`[0,1/2]`、`h=true`：`[1/2,1]`）。閾値 `V_h ≤ 1/2` は線分全体を含む。
* 新しい層系 `layerSystem16OnePoint`：担体は全層で `seg16 h`、射影は恒等、フィードバックは時刻1の
  勾配流（線分を線分へ写し、率 `e⁻¹` の縮小）、固定点は `c_h`（二履歴で 0 と 1）。
* `SharedModelSignature.layerTCZ1 N h i`：N の履歴中心の共有核の一歩を **`cog z = x₀` の一点**から
  `t ≥ 0` で動かして到達する点の閉包と、層 α の実走行費の閾値集合の共通部分。

**範囲：** 共通周囲空間 `E_i = ℝ` は変えない。担体は全層で同じ線分（案A の範囲）。旧 `layerTCZ`
（初期集合 `[0,1]`）と旧 `Shared16LayerTCZInputs` は残し、本ファイルの `Shared16OnePointInputs` を
別の受入型として加える。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1 Tomabechi.Consistency.C2
open Tomabechi.Consistency.C4 Tomabechi.Theorem16_25

/-- 一点の初期状態。 -/
def onePointStart : ℝ := 1 / 2

def seg16Lo (h : Bool) : ℝ := if h then 1 / 2 else 0
def seg16Hi (h : Bool) : ℝ := if h then 1 else 1 / 2

/-- 一点 `x₀` から履歴 h の勾配流で到達する点の閉包（線分）。 -/
def seg16 (h : Bool) : Set ℝ := Set.Icc (seg16Lo h) (seg16Hi h)

theorem seg16_subset_unit (h : Bool) : seg16 h ⊆ Set.Icc (0 : ℝ) 1 := by
  intro y hy
  cases h <;> simp only [seg16, seg16Lo, seg16Hi, Set.mem_Icc, Bool.false_eq_true, if_false,
    if_true] at hy ⊢ <;> constructor <;> linarith [hy.1, hy.2]

theorem onePointStart_mem (h : Bool) : onePointStart ∈ seg16 h := by
  cases h <;> simp [seg16, seg16Lo, seg16Hi, onePointStart] <;> norm_num

theorem center_mem_seg16 (h : Bool) : theorem16_intervalGradientCenter h ∈ seg16 h := by
  cases h <;> simp [seg16, seg16Lo, seg16Hi, theorem16_intervalGradientCenter] <;> norm_num

/-- 線分は勾配流のもとで前向き不変（t ≥ 0）。 -/
theorem flow_mem_seg16 (h : Bool) {y t : ℝ} (hy : y ∈ seg16 h) (ht : 0 ≤ t) :
    theorem16_intervalGradientFlow h y t ∈ seg16 h := by
  have hq0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hq1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  cases h
  · simp only [seg16, seg16Lo, seg16Hi, Set.mem_Icc, Bool.false_eq_true, if_false] at hy ⊢
    simp only [theorem16_intervalGradientFlow, theorem16_intervalGradientCenter,
      Bool.false_eq_true, if_false, sub_zero, zero_add]
    constructor
    · exact mul_nonneg hy.1 hq0.le
    · nlinarith [hy.1, hy.2]
  · simp only [seg16, seg16Lo, seg16Hi, Set.mem_Icc, if_true] at hy ⊢
    simp only [theorem16_intervalGradientFlow, theorem16_intervalGradientCenter, if_true]
    constructor
    · nlinarith [hy.1, hy.2]
    · nlinarith [hy.1, hy.2]

/-- 時刻1の勾配流写像（線分上）。 -/
def feedback16OnePoint (h : Bool) (_i : ℕ) (x : {x : ℝ // x ∈ seg16 h}) : {x : ℝ // x ∈ seg16 h} :=
  ⟨theorem16_intervalGradientFlow h x.1 1, flow_mem_seg16 h x.2 (by norm_num)⟩

theorem seg16_stronglyConvex (h : Bool) :
    Tomabechi.Theorem21.StronglyConvexOn (seg16 h) (theorem16_intervalGradientPotential h)
      (theorem16_intervalGradient h) 1 := by
  intro x hx y hy
  rw [Real.norm_eq_abs]
  rw [RCLike.inner_apply]
  simp [theorem16_intervalGradientPotential, theorem16_intervalGradient]
  nlinarith [sq_nonneg (y - x)]

theorem feedback16OnePoint_contracting (h : Bool) (i : ℕ) :
    ContractingWith ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩ (feedback16OnePoint h i) := by
  let trajectory : {x : ℝ // x ∈ seg16 h} → ℝ → ℝ :=
    fun x t => theorem16_intervalGradientFlow h x.1 t
  have hcontract := stronglyConvexGradientFlow_timeMap_contracting
    (seg16 h) (theorem16_intervalGradientPotential h)
    (theorem16_intervalGradient h) 1 1 (by norm_num)
    (seg16_stronglyConvex h) (by norm_num)
    trajectory
    (by intro x t; exact theorem16_intervalGradientFlow_hasDerivAt h x.1 t)
    (by intro x t ht; exact flow_mem_seg16 h x.2 ht.1)
    (by intro x; exact theorem16_intervalGradientFlow_start h x.1)
  have hmaps : feedback16OnePoint h i = fun x =>
      (⟨trajectory x 1, flow_mem_seg16 h x.2 (by norm_num)⟩ : {x : ℝ // x ∈ seg16 h}) := by
    funext x; apply Subtype.ext; rfl
  rw [hmaps]
  simpa [trajectory, mul_comm] using hcontract

/-- 一点初期状態から作った層系：担体は全層で線分 `seg16 h`、射影は恒等。 -/
noncomputable def layerSystem16OnePoint : Theorem16HistoryLayerSystem Bool Nat (fun _ : Nat => ℝ) := by
  refine {
    carrier := fun h _ => seg16 h
    compact := ?_
    nonempty := ?_
    convex := ?_
    project := fun _ x => x
    projectAffineOnCarrier := ?_
    projectRefl := ?_
    projectComp := ?_
    projectMaps := ?_
    projectContinuousOn := ?_
    noMax := ?_
    feedback := fun h i => feedback16OnePoint h i
    feedbackCommutes := ?_
    feedbackContinuous := ?_ }
  · intro h i; exact isCompact_Icc
  · intro h i; exact ⟨onePointStart, onePointStart_mem h⟩
  · intro h i; exact convex_Icc _ _
  · intro h β α hβα x y a b hx hy ha hb hab; rfl
  · intro h i x; rfl
  · intro h γ β α hγβ hβα x; rfl
  · intro h β α hβα x hx; simpa using hx
  · intro h j; exact continuousOn_id
  · intro i; exact ⟨i + 1, Nat.lt_succ_self i⟩
  · intro h β α hβα x; apply Subtype.ext; rfl
  · intro h i
    apply Continuous.subtype_mk
    exact continuous_const.add
      ((continuous_subtype_val.sub continuous_const).mul_const (Real.exp (-1)))


/-! ## 逆極限・距離・縮小 -/

abbrev IL1 (h : Bool) :=
  {x : ∀ i : Nat, ℝ // x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
    layerSystem16OnePoint.carrier layerSystem16OnePoint.project h}

/-- 恒等射影の逆極限は第0座標で線分と同型。 -/
def invLimEquiv1 (h : Bool) : IL1 h ≃ {x : ℝ // x ∈ seg16 h} where
  toFun x := ⟨x.1 0, x.2.1 0⟩
  invFun x := ⟨fun _ => x.1, by
    constructor
    · intro i; exact x.2
    · intro β α hβα; rfl⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hcompat := x.2.2 (show 0 ≤ i by omega)
    simpa [layerSystem16OnePoint] using hcompat.symm
  right_inv x := by
    apply Subtype.ext
    rfl

/-- 第0座標で引き戻した距離。 -/
@[instance_reducible]
noncomputable def metric1 (h : Bool) : MetricSpace (IL1 h) :=
  MetricSpace.induced (invLimEquiv1 h) (invLimEquiv1 h).injective inferInstance

theorem complete1 (h : Bool) : @CompleteSpace (IL1 h) (metric1 h).toPseudoMetricSpace.toUniformSpace := by
  letI : MetricSpace (IL1 h) := metric1 h
  letI : CompleteSpace {x : ℝ // x ∈ seg16 h} := isClosed_Icc.completeSpace_coe
  have hiso : Isometry (invLimEquiv1 h) := fun _ _ => rfl
  exact (⟨invLimEquiv1 h, fun _ _ => rfl⟩ : IL1 h ≃ᵢ {x : ℝ // x ∈ seg16 h}).completeSpace

theorem contracting1 (h : Bool) :
    letI : MetricSpace (IL1 h) := metric1 h
    ContractingWith ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩
      (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
        layerSystem16OnePoint.carrier layerSystem16OnePoint.project
        layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
        layerSystem16OnePoint.feedbackCommutes h) := by
  letI : MetricSpace (IL1 h) := metric1 h
  have hrate : (⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩ : NNReal) < 1 := by
    change Real.exp (-1) < 1
    rw [Real.exp_lt_one_iff]; norm_num
  refine ⟨hrate, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hx0 : (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes h x).1 0 =
      (feedback16OnePoint h 0 ⟨x.1 0, x.2.1 0⟩).1 := by
    simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap, id]
    rfl
  have hy0 : (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes h y).1 0 =
      (feedback16OnePoint h 0 ⟨y.1 0, y.2.1 0⟩).1 := by
    simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap, id]
    rfl
  change dist ((historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes h x).1 0)
      ((historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes h y).1 0) ≤ Real.exp (-1) * dist (x.1 0) (y.1 0)
  rw [hx0, hy0]
  exact (feedback16OnePoint_contracting h 0).2.dist_le_mul ⟨x.1 0, x.2.1 0⟩ ⟨y.1 0, y.2.1 0⟩


/-! ## 自己表象・存在節・表象節・縮小節 -/

instance (h : Bool) : CompactSpace {x : ℝ // x ∈ seg16 h} :=
  isCompact_iff_compactSpace.mp (by unfold seg16; exact isCompact_Icc)

/-- 第0座標で読む自己表象（線分上）。 -/
def selfRep1 (h : Bool) : SelfRepresentation (IL1 h) {x : ℝ // x ∈ seg16 h} where
  relation := {p | p.1.1 = p.2.1 0}
  relation_closed := isClosed_eq (continuous_subtype_val.comp continuous_fst)
    ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd))
  represent := fun x => ⟨x.1 0, x.2.1 0⟩
  represent_continuous := Continuous.subtype_mk
    ((continuous_apply 0).comp continuous_subtype_val) (fun x => x.2.1 0)
  represents := fun x => rfl

theorem feedback16OnePoint_continuous (h : Bool) (i : ℕ) : Continuous (feedback16OnePoint h i) := by
  apply Continuous.subtype_mk
  exact continuous_const.add
    ((continuous_subtype_val.sub continuous_const).mul_const (Real.exp (-1)))

/-- 定理16の存在節・表象節・縮小節（一点初期状態の線分層系）。 -/
def Theorem16EntryClause1 : Prop :=
  ∀ h, letI := metric1 h; ∃! x : IL1 h,
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes h x = x ∧
    feedback16OnePoint h 0 ((selfRep1 h).represent x) = (selfRep1 h).represent x ∧
    ((selfRep1 h).represent x, x) ∈ (selfRep1 h).relation ∧
    ∀ (x₀ : IL1 h) (n : ℕ),
      dist ((historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
        layerSystem16OnePoint.carrier layerSystem16OnePoint.project
        layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
        layerSystem16OnePoint.feedbackCommutes h)^[n] x₀) x ≤
        (Real.exp (-1)) ^ n * dist x₀ x

theorem theorem16EntryClause1_holds : Theorem16EntryClause1 := by
  intro h
  exact layerSystem16OnePoint.fullRepresentedFixedPointConclusion metric1 complete1
    (fun _ => ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩) contracting1
    (fun h => {x : ℝ // x ∈ seg16 h}) selfRep1 (fun h => feedback16OnePoint h 0)
    (fun h => feedback16OnePoint_continuous h 0) (fun h x => by apply Subtype.ext; rfl) h


/-! ## 一点初期状態からの層別 TCZ（閉到達スライス） -/

/-- 一点 `x₀` から履歴 h の中心 c での共有核を `t ≥ 0` 動かして到達する認知座標の集合 `ℛ_π(x₀)`。 -/
def SharedModelSignature.reach1 (N : SharedModelSignature) (h : Bool) : Set ℝ :=
  {y | ∃ t : ℝ, 0 ≤ t ∧ ∃ (z : CompleteState) (E : ℝ), cognitiveCoordinate z = onePointStart ∧
    y = cognitiveCoordinate (N.legacy.step (N.legacy.historyCenter h) t E z)}

/-- 履歴 h・層 `index16 i` の一点初期状態からの閉到達 TCZ `K_π(x₀) ∩ Ω_θ`：
到達集合の閉包と、層 α の実走行費の閾値集合（点 y は標準の持ち上げ `(y,0)` で評価）の共通部分。 -/
def SharedModelSignature.layerTCZ1 (N : SharedModelSignature) (h : Bool) (i : ℕ) : Set ℝ :=
  closure (N.reach1 h) ∩
    {y | N.data.runningCost (index16 i) (layerPolicyCast i (N.legacy.informationPolicy false))
      (layerStateCast i (N.legacy.finiteProjection 0 (N.legacy.historyCenter h) ((y, 0) : CompleteState)))
        0 ≤ layerCostThreshold}

theorem SharedModelSignature.reach1_eq {N : SharedModelSignature}
    (hA : AdditionalConditions N.legacy) (h : Bool) :
    N.reach1 h = {y | ∃ t : ℝ, 0 ≤ t ∧ y = theorem16_intervalGradientFlow h onePointStart t} := by
  have hc := hA.history_centers
  have hcore := hA.toCommonDataCouplings.core_cognitive
  ext y
  constructor
  · rintro ⟨t, ht, z, E, hz, rfl⟩
    refine ⟨t, ht, ?_⟩
    rw [hcore, hc, hz]
    rfl
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, (onePointStart, 0), 0, rfl, ?_⟩
    rw [hcore, hc]
    rfl

theorem reach_subset_seg16 (h : Bool) :
    {y | ∃ t : ℝ, 0 ≤ t ∧ y = theorem16_intervalGradientFlow h onePointStart t} ⊆ seg16 h := by
  rintro y ⟨t, ht, rfl⟩
  exact flow_mem_seg16 h (onePointStart_mem h) ht

theorem seg16_subset_closure_reach (h : Bool) :
    seg16 h ⊆ closure {y | ∃ t : ℝ, 0 ≤ t ∧ y = theorem16_intervalGradientFlow h onePointStart t} := by
  intro y hy
  set c := theorem16_intervalGradientCenter h with hc
  have hx0 : onePointStart - c ≠ 0 := by
    cases h <;> simp [hc, theorem16_intervalGradientCenter, onePointStart] <;> norm_num
  by_cases hyc : y = c
  · subst hyc
    refine mem_closure_of_tendsto (b := Filter.atTop) (f := fun t : ℝ =>
      theorem16_intervalGradientFlow h onePointStart t) ?_ ?_
    · have h1 : Filter.Tendsto (fun t : ℝ => Real.exp (-t)) Filter.atTop (nhds 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero
      have := (h1.const_mul (onePointStart - c)).const_add c
      simpa [theorem16_intervalGradientFlow] using this
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact ⟨t, ht, rfl⟩
  · -- y ≠ c：e^{-t} = (y-c)/(x₀-c) ∈ (0,1]
    apply subset_closure
    have hr : 0 < (y - c) / (onePointStart - c) ∧ (y - c) / (onePointStart - c) ≤ 1 := by
      cases h
      · simp only [seg16, seg16Lo, seg16Hi, Set.mem_Icc, Bool.false_eq_true, if_false] at hy
        simp only [hc, theorem16_intervalGradientCenter, Bool.false_eq_true, if_false,
          onePointStart] at hyc hx0 ⊢
        have hy0 : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hyc)
        constructor
        · positivity
        · rw [div_le_one (by norm_num)]; linarith [hy.2]
      · simp only [seg16, seg16Lo, seg16Hi, Set.mem_Icc, if_true] at hy
        simp only [hc, theorem16_intervalGradientCenter, if_true, onePointStart] at hyc hx0 ⊢
        have hy1 : y < 1 := lt_of_le_of_ne hy.2 hyc
        have : (y - 1) / (1 / 2 - 1) = (1 - y) / (1 / 2) := by
          rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, div_neg, ← neg_div]; ring_nf
        rw [this]
        constructor
        · apply div_pos (by linarith) (by norm_num)
        · rw [div_le_one (by norm_num)]; linarith [hy.1]
    refine ⟨-Real.log ((y - c) / (onePointStart - c)), ?_, ?_⟩
    · have := Real.log_nonpos hr.1.le hr.2
      linarith
    · simp only [theorem16_intervalGradientFlow, ← hc, neg_neg]
      rw [Real.exp_log hr.1]
      field_simp
      ring

/-- 一点からの到達集合の閉包は線分 `seg16 h`。 -/
theorem closure_reach_eq_seg16 (h : Bool) :
    closure {y | ∃ t : ℝ, 0 ≤ t ∧ y = theorem16_intervalGradientFlow h onePointStart t} =
      seg16 h := by
  apply Set.Subset.antisymm
  · exact closure_minimal (reach_subset_seg16 h) isClosed_Icc
  · exact seg16_subset_closure_reach h


/-! ## 層別 TCZ ＝ 線分担体 -/

theorem SharedModelSignature.layerTCZ1_eq_seg16 {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) (h : Bool) (i : ℕ) :
    N.layerTCZ1 h i = seg16 h := by
  have hcl : closure (N.reach1 h) = seg16 h := by
    rw [SharedModelSignature.reach1_eq hA, closure_reach_eq_seg16]
  ext y
  constructor
  · rintro ⟨hy, _⟩
    rwa [hcl] at hy
  · intro hy
    refine ⟨by rwa [hcl], ?_⟩
    show N.data.runningCost (index16 i) (layerPolicyCast i (N.legacy.informationPolicy false))
      (layerStateCast i (N.legacy.finiteProjection 0 (N.legacy.historyCenter h)
        ((y, 0) : CompleteState))) 0 ≤ layerCostThreshold
    rw [SharedModelSignature.layerCost_eq_potential hp hA]
    have hu := seg16_subset_unit h hy
    have hcen : theorem16_intervalGradientCenter h ∈ Set.Icc (0 : ℝ) 1 := by
      cases h <;> norm_num [theorem16_intervalGradientCenter]
    have habs := abs_le.mp (show |y - theorem16_intervalGradientCenter h| ≤ 1 by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hcen.1, hcen.2])
    rw [layerCostThreshold, theorem16_intervalGradientPotential]
    change 1 + 16 * ((y - theorem16_intervalGradientCenter h) ^ 2 / 2) ≤ 9
    nlinarith [habs.1, habs.2]

/-- 線分上の不動点は履歴の中心。 -/
theorem feedback16OnePoint_fixedValue (h : Bool) (i : ℕ) (x : {x : ℝ // x ∈ seg16 h})
    (hfix : feedback16OnePoint h i x = x) : x.1 = theorem16_intervalGradientCenter h := by
  have hcoord := congrArg Subtype.val hfix
  change theorem16_intervalGradientFlow h x.1 1 = x.1 at hcoord
  have hq : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  have hprod : (x.1 - theorem16_intervalGradientCenter h) * (Real.exp (-1) - 1) = 0 := by
    dsimp [theorem16_intervalGradientFlow] at hcoord
    nlinarith
  rcases mul_eq_zero.mp hprod with hc | hr
  · linarith
  · exact absurd (by linarith : Real.exp (-1) = 1) (ne_of_lt hq)

/-- 逆極限上の不動点は、全座標が履歴の中心。 -/
theorem fixedPoint1_coordinate (h : Bool) (x : IL1 h)
    (hfix : historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes h x = x) (i : ℕ) :
    x.1 i = theorem16_intervalGradientCenter h := by
  have hc := congrFun (congrArg Subtype.val hfix) i
  simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap, id] at hc
  exact feedback16OnePoint_fixedValue h i ⟨x.1 i, x.2.1 i⟩ (Subtype.ext hc)

/-- 一点初期状態の線分層系による定理16の受入型。担体は一点 `x₀=1/2` からの閉到達スライス。 -/
structure Shared16OnePointInputs (N : SharedModelSignature) : Prop where
  /-- 初期状態は一点 `x₀ ∈ (0,1)`。 -/
  start_interior : 0 < onePointStart ∧ onePointStart < 1
  /-- 到達集合の閉包は線分（履歴ごとに異なる）。 -/
  closure_reach : ∀ h, closure (N.reach1 h) = seg16 h
  carriers_differ : seg16 false ≠ seg16 true
  /-- 層別 TCZ（一点の閉到達スライス）＝線分担体。 -/
  tcz_eq : ∀ (h : Bool) (i : ℕ), N.layerTCZ1 h i = seg16 h
  carrier_eq : ∀ (h : Bool) (i : ℕ), layerSystem16OnePoint.carrier h i = N.layerTCZ1 h i
  layer_nonempty : ∀ (h : Bool) (i : ℕ), (N.layerTCZ1 h i).Nonempty
  layer_compact : ∀ (h : Bool) (i : ℕ), IsCompact (N.layerTCZ1 h i)
  layer_convex : ∀ (h : Bool) (i : ℕ), Convex ℝ (N.layerTCZ1 h i)
  project_maps : type_of% layerSystem16OnePoint.projectMaps
  project_affine : type_of% layerSystem16OnePoint.projectAffineOnCarrier
  project_refl : type_of% layerSystem16OnePoint.projectRefl
  project_comp : type_of% layerSystem16OnePoint.projectComp
  project_continuous : type_of% layerSystem16OnePoint.projectContinuousOn
  no_maximum : type_of% layerSystem16OnePoint.noMax
  feedback_commutes : type_of% layerSystem16OnePoint.feedbackCommutes
  feedback_continuous : type_of% layerSystem16OnePoint.feedbackContinuous
  rep_closed : ∀ h, IsClosed (selfRep1 h).relation
  rep_continuous : ∀ h, Continuous (selfRep1 h).represent
  rep_map_continuous : ∀ h, Continuous (feedback16OnePoint h 0)
  complete : ∀ h, @CompleteSpace (IL1 h) (metric1 h).toPseudoMetricSpace.toUniformSpace
  contracting : type_of% contracting1
  entry_clause : Theorem16EntryClause1
  /-- 不動点は全座標が履歴の中心で、二履歴で異なる（0 と 1）。 -/
  fixed_point_center : ∀ (h : Bool) (x : IL1 h),
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes h x = x →
    ∀ i, x.1 i = theorem16_intervalGradientCenter h
  fixed_points_separate : ∀ (xf : IL1 false) (xt : IL1 true),
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes false xf = xf →
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes true xt = xt →
    xf.1 ≠ xt.1

theorem SharedModelSignature.shared16OnePointInputs {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) :
    Shared16OnePointInputs N where
  start_interior := by unfold onePointStart; constructor <;> norm_num
  closure_reach := fun h => by
    rw [SharedModelSignature.reach1_eq hA, closure_reach_eq_seg16]
  carriers_differ := fun hc => by
    have := congrArg (fun S : Set ℝ => (0 : ℝ) ∈ S) hc
    simp [seg16, seg16Lo, seg16Hi] at this
    norm_num at this
  tcz_eq := fun h i => SharedModelSignature.layerTCZ1_eq_seg16 hp hA h i
  carrier_eq := fun h i => (SharedModelSignature.layerTCZ1_eq_seg16 hp hA h i).symm
  layer_nonempty := fun h i => by
    rw [SharedModelSignature.layerTCZ1_eq_seg16 hp hA]; exact ⟨_, onePointStart_mem h⟩
  layer_compact := fun h i => by
    rw [SharedModelSignature.layerTCZ1_eq_seg16 hp hA]; exact isCompact_Icc
  layer_convex := fun h i => by
    rw [SharedModelSignature.layerTCZ1_eq_seg16 hp hA]; exact convex_Icc _ _
  project_maps := layerSystem16OnePoint.projectMaps
  project_affine := layerSystem16OnePoint.projectAffineOnCarrier
  project_refl := layerSystem16OnePoint.projectRefl
  project_comp := layerSystem16OnePoint.projectComp
  project_continuous := layerSystem16OnePoint.projectContinuousOn
  no_maximum := layerSystem16OnePoint.noMax
  feedback_commutes := layerSystem16OnePoint.feedbackCommutes
  feedback_continuous := layerSystem16OnePoint.feedbackContinuous
  rep_closed := fun h => (selfRep1 h).relation_closed
  rep_continuous := fun h => (selfRep1 h).represent_continuous
  rep_map_continuous := fun h => feedback16OnePoint_continuous h 0
  complete := complete1
  contracting := contracting1
  entry_clause := theorem16EntryClause1_holds
  fixed_point_center := fun h x hfix i => fixedPoint1_coordinate h x hfix i
  fixed_points_separate := fun xf xt hf ht heq => by
    have h0 := fixedPoint1_coordinate false xf hf 0
    have h1 := fixedPoint1_coordinate true xt ht 0
    rw [heq] at h0
    simp [theorem16_intervalGradientCenter] at h0 h1
    linarith

theorem sharedModel_shared16OnePointInputs : Shared16OnePointInputs sharedModel :=
  SharedModelSignature.shared16OnePointInputs sharedModel_preservation
    sharedModel_explicitAdditionalConditions.legacy

/-- 新しい層系の不動点の座標は、25 の SCM が読む旧固定点（`[0,1]` の系）の座標と一致する。
固定点が変わらないので、Γ（`fixedPoint_gamma`）・自己表象の側は影響を受けない。 -/
theorem fixedPoint1_eq_old (h : Bool) (x : IL1 h)
    (hfix : historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16OnePoint.carrier layerSystem16OnePoint.project
      layerSystem16OnePoint.projectMaps layerSystem16OnePoint.feedback
      layerSystem16OnePoint.feedbackCommutes h x = x) (i : ℕ) :
    x.1 i = (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 i := by
  rw [fixedPoint1_coordinate h x hfix i, theorem16_intervalGradientFlowFixedPoint_coordinate]

/-- v3：v2 の全受入型と 25-C4/C5 の拡張に、一点初期状態の層別 TCZを加えた存在宣言。 -/
theorem final_consistency_v3 :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N ∧
        GenealogyMortalityExtension N ∧ Shared16OnePointInputs N :=
  ⟨sharedModel,
    ⟨sharedModel_fullOriginalPremises, sharedModel_capacityInputs,
      sharedModel_shared16LayerTCZInputs, sharedModel_normUnification⟩,
    ⟨sharedModel_explicitAdditionalConditions,
      sharedModel_pointDomainInputs.explicitHConditions,
      sharedModel_shared16Indexing, sharedModel_baseDomain⟩,
    ⟨sharedModel_nondegenerate, sharedModel_nativeNondegenerate⟩,
    sharedModel_baseBackground21, sharedModel.sharedTopCompleteReading,
    sharedModel_normUnificationConclusions, sharedModel_theorem4Ranges,
    sharedModel_shared16Premises, sharedModel_subjectIdentity, sharedModel_noClockCoordinate,
    sharedModel_borelStructure, sharedModel_genealogyMortality, sharedModel_shared16OnePointInputs⟩

#print axioms SharedModelSignature.shared16OnePointInputs
#print axioms fixedPoint1_eq_old
#print axioms final_consistency_v3

end Tomabechi.Consistency.R123
