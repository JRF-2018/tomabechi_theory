import Tomabechi.Consistency.ConsistencyR123_FinalV6

/-!
# 正典 TCZ を定理16の担体にする

§2.1 の正典 TCZ は `TCZ(x₀) := ⋃_{τ≥0}[ℛ(τ;x₀) ∩ Ω_θ(τ)]`（閉包を取らない）で、閉到達スライス
`K_π(x₀)∩Ω_θ(t)` とは別の定義である。ミニマル13版 §7 の担体は正典の名前 `TCZ` なので、一点版の `layerTCZ1`
（到達集合の**閉包**を取った線分）は担体の読みとして足りない。有限時刻の指数軌道は中心に届かず、
閉包にだけ中心が加わるためである（`SharedModelSignature.core_step_misses_center`）。

ここでは **全許容制御による到達**を採る。

* **16 の層の制御系：** 速度制御 `ẋ = u`（`f(x,u,t)=u` は状態について Lipschitz）、許容制御は
  可測で `|u|≤1` の信号 `VelControl`。軌道は `x(t)=x₀+∫₀ᵗ u`（1-Lipschitz）。到達集合は
  `ℛ(τ;x₀) = [x₀−τ, x₀+τ]`（`velReach_eq`）。これは旧 C4 の区間制御系（`theorem16_intervalControlled*`）の、
  可測制御・任意の初期点への拡張である。
* **一点の初期状態** `x₀ = 1/2`。**評価** `Ω_θ` は N.data の層 α の実走行費の閾値集合
  （`V_h ≤ 1/2`）で、`[c_h−1, c_h+1]`。
* `canonicalLayerTCZ N h i := {y | ∃ τ ≥ 0, y ∈ ℛ(τ;x₀) ∧ cost(y,τ) ≤ 9}`（閉包なし）。
  `= ball16 h := [c_h−1, c_h+1]`（履歴ごとに異なる閉区間）で、非空・コンパクト・凸。
* **選択フィードバックは許容制御：** 勾配フィードバック `u = c_h − x` は担体の上で `|u| ≤ 1`
  （`ball16` はちょうどその範囲）なので、閉ループ軌道は許容制御系の軌道（`selected_flow_admissible`）。
  また N の共有核の認知座標の動き（`core_cognitive`）はこの選択方策の時刻 A の流れに一致する
  （`core_step_is_selected_flow`）。
* 担体 `ball16 h` を全層で共有する層系 `layerSystem16Canonical`（射影は恒等、フィードバックは時刻1の勾配流で
  率 `e⁻¹` の縮小）。定理16の存在節・表象節・縮小節を `fullRepresentedFixedPointConclusion` から得る。
* 25 の三表現（Self・Ego・TCZ）の TCZ 成分、19 の実験の自己過程成分を、同じ正典 TCZ に揃える。

**範囲（限定）：** 速度制御系は 16 の層の TCZ 生成系としての**モデルの選択**で、N.data の有限層の
有界ゲイン力学（中心に有限時間では届かない）から導いたものではない。N.data とは、(i) 評価 Ω が
N.data の層 α の実走行費、(ii) 選択方策が N の共有核の認知座標の動きと一致、の二点で接続する。
有界ゲイン力学だけでは正典 TCZ が閉でないことは `SharedModelSignature.core_step_misses_center` が示す。Ego の型は
`Set.Icc 0 1 → Set.Icc 0 1` なので、担体 `ball16` が `[0,1]` を超える部分では Ego を担体上のフィードバックの
拡張とは述べられない（`[0,1]` との共通部分でのみ述べる）。旧 `[0,1]` 版・一点閉包版・正典版が同じだとは
主張しない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1 Tomabechi.Consistency.C2
open Tomabechi.Consistency.C4 Tomabechi.Theorem16_25

/-! ## 16 の層の制御系（速度制御）と到達集合 -/

/-- 許容制御：可測で `|u| ≤ 1`。 -/
abbrev VelControl := {u : ℝ → ℝ // Measurable u ∧ ∀ t, |u t| ≤ 1}

/-- 軌道 `x(t) = x₀ + ∫₀ᵗ u`。 -/
def velTraj (x₀ : ℝ) (u : VelControl) (t : ℝ) : ℝ := x₀ + ∫ s in (0 : ℝ)..t, u.1 s

theorem velControl_intervalIntegrable (u : VelControl) (a b : ℝ) :
    IntervalIntegrable u.1 volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    u.2.1.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => ?_))
  simpa using u.2.2 t

/-- 軌道は 1-Lipschitz。 -/
theorem velTraj_lipschitz (x₀ : ℝ) (u : VelControl) : LipschitzWith 1 (velTraj x₀ u) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [velTraj, NNReal.coe_one, one_mul, Real.dist_eq]
  have h : (x₀ + ∫ r in (0 : ℝ)..s, u.1 r) - (x₀ + ∫ r in (0 : ℝ)..t, u.1 r) =
      ∫ r in t..s, u.1 r := by
    rw [← intervalIntegral.integral_interval_sub_left (velControl_intervalIntegrable u 0 s)
      (velControl_intervalIntegrable u 0 t)]
    ring
  rw [h]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := s) (C := 1)
    (f := u.1) (fun r _ => by simpa using u.2.2 r)
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- 時刻 τ に到達する状態の集合 `ℛ(τ;x₀)`（全許容制御）。 -/
def velReach (x₀ τ : ℝ) : Set ℝ := {y | ∃ u : VelControl, y = velTraj x₀ u τ}

theorem velReach_eq {x₀ τ : ℝ} (hτ : 0 ≤ τ) : velReach x₀ τ = Set.Icc (x₀ - τ) (x₀ + τ) := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ) (C := 1)
      (f := u.1) (fun r _ => by simpa using u.2.2 r)
    have h1 : |∫ r in (0 : ℝ)..τ, u.1 r| ≤ τ := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hτ] using this
    have := abs_le.mp h1
    constructor <;> simp only [velTraj] <;> linarith [this.1, this.2]
  · intro hy
    by_cases h0 : τ = 0
    · subst h0
      have : y = x₀ := by simpa using hy
      exact ⟨⟨fun _ => 0, measurable_const, by simp⟩, by simp [velTraj, this]⟩
    · have hpos : 0 < τ := lt_of_le_of_ne hτ (Ne.symm h0)
      refine ⟨⟨fun _ => (y - x₀) / τ, measurable_const, fun _ => ?_⟩, ?_⟩
      · rw [abs_div, abs_of_pos hpos, div_le_one hpos]
        exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      · simp only [velTraj, intervalIntegral.integral_const, smul_eq_mul]
        field_simp
        ring

/-- 一点の初期状態からの到達の和集合は全体（任意の `y` は τ=|y−x₀| で到達）。 -/
theorem velReach_mem_of {x₀ y : ℝ} : y ∈ velReach x₀ |y - x₀| := by
  rw [velReach_eq (abs_nonneg _)]
  constructor
  · linarith [neg_abs_le (y - x₀)]
  · linarith [le_abs_self (y - x₀)]

/-! ## 閉区間担体 `ball16 h = [c_h − 1, c_h + 1]` -/

/-- 履歴 h の担体：`V_h ≤ 1/2` の閾値集合 `[c_h−1, c_h+1]`。 -/
def ball16 (h : Bool) : Set ℝ :=
  Set.Icc (theorem16_intervalGradientCenter h - 1) (theorem16_intervalGradientCenter h + 1)

theorem center_mem_ball16 (h : Bool) : theorem16_intervalGradientCenter h ∈ ball16 h := by
  constructor <;> linarith

theorem flow_mem_ball16 (h : Bool) {y t : ℝ} (hy : y ∈ ball16 h) (ht : 0 ≤ t) :
    theorem16_intervalGradientFlow h y t ∈ ball16 h := by
  have hq0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hq1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  set c := theorem16_intervalGradientCenter h
  have hyc : |y - c| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hf : theorem16_intervalGradientFlow h y t - c = (y - c) * Real.exp (-t) := by
    simp [theorem16_intervalGradientFlow, c]
  have habs : |theorem16_intervalGradientFlow h y t - c| ≤ 1 := by
    rw [hf, abs_mul, abs_of_pos hq0]
    nlinarith [abs_nonneg (y - c)]
  have := abs_le.mp habs
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- 時刻1の勾配流写像（線分上）。 -/
def feedback16Canonical (h : Bool) (_i : ℕ) (x : {x : ℝ // x ∈ ball16 h}) : {x : ℝ // x ∈ ball16 h} :=
  ⟨theorem16_intervalGradientFlow h x.1 1, flow_mem_ball16 h x.2 (by norm_num)⟩

theorem ball16_stronglyConvex (h : Bool) :
    Tomabechi.Theorem21.StronglyConvexOn (ball16 h) (theorem16_intervalGradientPotential h)
      (theorem16_intervalGradient h) 1 := by
  intro x hx y hy
  rw [Real.norm_eq_abs]
  rw [RCLike.inner_apply]
  simp [theorem16_intervalGradientPotential, theorem16_intervalGradient]
  nlinarith [sq_nonneg (y - x)]

theorem feedback16Canonical_contracting (h : Bool) (i : ℕ) :
    ContractingWith ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩ (feedback16Canonical h i) := by
  let trajectory : {x : ℝ // x ∈ ball16 h} → ℝ → ℝ :=
    fun x t => theorem16_intervalGradientFlow h x.1 t
  have hcontract := stronglyConvexGradientFlow_timeMap_contracting
    (ball16 h) (theorem16_intervalGradientPotential h)
    (theorem16_intervalGradient h) 1 1 (by norm_num)
    (ball16_stronglyConvex h) (by norm_num)
    trajectory
    (by intro x t; exact theorem16_intervalGradientFlow_hasDerivAt h x.1 t)
    (by intro x t ht; exact flow_mem_ball16 h x.2 ht.1)
    (by intro x; exact theorem16_intervalGradientFlow_start h x.1)
  have hmaps : feedback16Canonical h i = fun x =>
      (⟨trajectory x 1, flow_mem_ball16 h x.2 (by norm_num)⟩ : {x : ℝ // x ∈ ball16 h}) := by
    funext x; apply Subtype.ext; rfl
  rw [hmaps]
  simpa [trajectory, mul_comm] using hcontract

/-- 一点初期状態から作った層系：担体は全層で線分 `ball16 h`、射影は恒等。 -/
noncomputable def layerSystem16Canonical : Theorem16HistoryLayerSystem Bool Nat (fun _ : Nat => ℝ) := by
  refine {
    carrier := fun h _ => ball16 h
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
    feedback := fun h i => feedback16Canonical h i
    feedbackCommutes := ?_
    feedbackContinuous := ?_ }
  · intro h i; exact isCompact_Icc
  · intro h i; exact ⟨_, center_mem_ball16 h⟩
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

abbrev ILc (h : Bool) :=
  {x : ∀ i : Nat, ℝ // x ∈ historyAffineInverseLimitSet (fun _ : Nat => ℝ)
    layerSystem16Canonical.carrier layerSystem16Canonical.project h}

/-- 恒等射影の逆極限は第0座標で線分と同型。 -/
def invLimEquivC (h : Bool) : ILc h ≃ {x : ℝ // x ∈ ball16 h} where
  toFun x := ⟨x.1 0, x.2.1 0⟩
  invFun x := ⟨fun _ => x.1, by
    constructor
    · intro i; exact x.2
    · intro β α hβα; rfl⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hcompat := x.2.2 (show 0 ≤ i by omega)
    simpa [layerSystem16Canonical] using hcompat.symm
  right_inv x := by
    apply Subtype.ext
    rfl

/-- 第0座標で引き戻した距離。 -/
@[instance_reducible]
noncomputable def metricC (h : Bool) : MetricSpace (ILc h) :=
  MetricSpace.induced (invLimEquivC h) (invLimEquivC h).injective inferInstance

theorem completeC (h : Bool) : @CompleteSpace (ILc h) (metricC h).toPseudoMetricSpace.toUniformSpace := by
  letI : MetricSpace (ILc h) := metricC h
  letI : CompleteSpace {x : ℝ // x ∈ ball16 h} := isClosed_Icc.completeSpace_coe
  have hiso : Isometry (invLimEquivC h) := fun _ _ => rfl
  exact (⟨invLimEquivC h, fun _ _ => rfl⟩ : ILc h ≃ᵢ {x : ℝ // x ∈ ball16 h}).completeSpace

theorem contractingC (h : Bool) :
    letI : MetricSpace (ILc h) := metricC h
    ContractingWith ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩
      (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
        layerSystem16Canonical.carrier layerSystem16Canonical.project
        layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
        layerSystem16Canonical.feedbackCommutes h) := by
  letI : MetricSpace (ILc h) := metricC h
  have hrate : (⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩ : NNReal) < 1 := by
    change Real.exp (-1) < 1
    rw [Real.exp_lt_one_iff]; norm_num
  refine ⟨hrate, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hx0 : (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes h x).1 0 =
      (feedback16Canonical h 0 ⟨x.1 0, x.2.1 0⟩).1 := by
    simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap, id]
    rfl
  have hy0 : (historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes h y).1 0 =
      (feedback16Canonical h 0 ⟨y.1 0, y.2.1 0⟩).1 := by
    simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap, id]
    rfl
  change dist ((historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes h x).1 0)
      ((historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes h y).1 0) ≤ Real.exp (-1) * dist (x.1 0) (y.1 0)
  rw [hx0, hy0]
  exact (feedback16Canonical_contracting h 0).2.dist_le_mul ⟨x.1 0, x.2.1 0⟩ ⟨y.1 0, y.2.1 0⟩


/-! ## 自己表象・存在節・表象節・縮小節 -/

instance (h : Bool) : CompactSpace {x : ℝ // x ∈ ball16 h} :=
  isCompact_iff_compactSpace.mp (by unfold ball16; exact isCompact_Icc)

/-- 第0座標で読む自己表象（線分上）。 -/
def selfRepC (h : Bool) : SelfRepresentation (ILc h) {x : ℝ // x ∈ ball16 h} where
  relation := {p | p.1.1 = p.2.1 0}
  relation_closed := isClosed_eq (continuous_subtype_val.comp continuous_fst)
    ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd))
  represent := fun x => ⟨x.1 0, x.2.1 0⟩
  represent_continuous := Continuous.subtype_mk
    ((continuous_apply 0).comp continuous_subtype_val) (fun x => x.2.1 0)
  represents := fun x => rfl

theorem feedback16Canonical_continuous (h : Bool) (i : ℕ) : Continuous (feedback16Canonical h i) := by
  apply Continuous.subtype_mk
  exact continuous_const.add
    ((continuous_subtype_val.sub continuous_const).mul_const (Real.exp (-1)))

/-- 定理16の存在節・表象節・縮小節（一点初期状態の線分層系）。 -/
def Theorem16EntryClauseC : Prop :=
  ∀ h, letI := metricC h; ∃! x : ILc h,
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes h x = x ∧
    feedback16Canonical h 0 ((selfRepC h).represent x) = (selfRepC h).represent x ∧
    ((selfRepC h).represent x, x) ∈ (selfRepC h).relation ∧
    ∀ (x₀ : ILc h) (n : ℕ),
      dist ((historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
        layerSystem16Canonical.carrier layerSystem16Canonical.project
        layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
        layerSystem16Canonical.feedbackCommutes h)^[n] x₀) x ≤
        (Real.exp (-1)) ^ n * dist x₀ x

theorem theorem16EntryClauseC_holds : Theorem16EntryClauseC := by
  intro h
  exact layerSystem16Canonical.fullRepresentedFixedPointConclusion metricC completeC
    (fun _ => ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩) contractingC
    (fun h => {x : ℝ // x ∈ ball16 h}) selfRepC (fun h => feedback16Canonical h 0)
    (fun h => feedback16Canonical_continuous h 0) (fun h x => by apply Subtype.ext; rfl) h



theorem feedback16Canonical_fixedValue (h : Bool) (i : ℕ) (x : {x : ℝ // x ∈ ball16 h})
    (hfix : feedback16Canonical h i x = x) : x.1 = theorem16_intervalGradientCenter h := by
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
theorem fixedPointC_coordinate (h : Bool) (x : ILc h)
    (hfix : historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes h x = x) (i : ℕ) :
    x.1 i = theorem16_intervalGradientCenter h := by
  have hc := congrFun (congrArg Subtype.val hfix) i
  simp only [historyInducedAffineInverseLimitMap, inducedAffineInverseLimitMap, id] at hc
  exact feedback16Canonical_fixedValue h i ⟨x.1 i, x.2.1 i⟩ (Subtype.ext hc)


theorem fixedPointC_eq_old (h : Bool) (x : ILc h)
    (hfix : historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes h x = x) (i : ℕ) :
    x.1 i = (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 i := by
  rw [fixedPointC_coordinate h x hfix i, theorem16_intervalGradientFlowFixedPoint_coordinate]



/-! ## 正典 TCZ（閉包を取らない）＝ 担体 -/

/-- 層 α の実評価の閾値集合 `Ω_θ(τ)`（点 y は標準の持ち上げ `(y,0)` で評価、時刻は τ）。 -/
def SharedModelSignature.layerOmega (N : SharedModelSignature) (h : Bool) (i : ℕ) (τ : ℝ) :
    Set ℝ :=
  {y | N.data.runningCost (index16 i) (layerPolicyCast i (N.legacy.informationPolicy false))
    (layerStateCast i (N.legacy.finiteProjection 0 (N.legacy.historyCenter h) ((y, 0) : CompleteState)))
      τ ≤ layerCostThreshold}

/-- 正典 TCZ：`⋃_{τ≥0}[ℛ(τ;x₀) ∩ Ω_θ(τ)]`。一点の初期状態 `x₀ = 1/2`、全許容制御の到達、閉包なし。 -/
def SharedModelSignature.canonicalLayerTCZ (N : SharedModelSignature) (h : Bool) (i : ℕ) : Set ℝ :=
  {y | ∃ τ : ℝ, 0 ≤ τ ∧ y ∈ velReach onePointStart τ ∧ y ∈ N.layerOmega h i τ}

theorem SharedModelSignature.layerOmega_eq {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) (h : Bool) (i : ℕ)
    (τ : ℝ) : N.layerOmega h i τ = ball16 h := by
  ext y
  show N.data.runningCost (index16 i) (layerPolicyCast i (N.legacy.informationPolicy false))
    (layerStateCast i (N.legacy.finiteProjection 0 (N.legacy.historyCenter h)
      ((y, 0) : CompleteState))) τ ≤ layerCostThreshold ↔ y ∈ ball16 h
  rw [SharedModelSignature.layerCost_eq_potential hp hA, layerCostThreshold,
    theorem16_intervalGradientPotential]
  change 1 + 16 * ((y - theorem16_intervalGradientCenter h) ^ 2 / 2) ≤ 9 ↔ _
  constructor
  · intro hle
    have habs : |y - theorem16_intervalGradientCenter h| ≤ 1 := by
      apply abs_le_one_iff_mul_self_le_one.mpr
      nlinarith
    have := abs_le.mp habs
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro hy
    have habs := abs_le.mp (show |y - theorem16_intervalGradientCenter h| ≤ 1 from
      abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    nlinarith [habs.1, habs.2]

/-- 正典 TCZ ＝ 閉区間 `ball16 h`（履歴ごとに異なる、非空・コンパクト・凸）。 -/
theorem SharedModelSignature.canonicalLayerTCZ_eq {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) (h : Bool) (i : ℕ) :
    N.canonicalLayerTCZ h i = ball16 h := by
  ext y
  constructor
  · rintro ⟨τ, _, _, hΩ⟩
    rwa [SharedModelSignature.layerOmega_eq hp hA] at hΩ
  · intro hy
    refine ⟨|y - onePointStart|, abs_nonneg _, velReach_mem_of, ?_⟩
    rwa [SharedModelSignature.layerOmega_eq hp hA]

/-- 有限時刻の一点勾配軌道は中心に届かない（閉包を取った担体との違い）。 -/
theorem onePoint_flow_ne_center (h : Bool) (t : ℝ) :
    theorem16_intervalGradientFlow h onePointStart t ≠ theorem16_intervalGradientCenter h := by
  have hx : onePointStart - theorem16_intervalGradientCenter h ≠ 0 := by
    cases h <;> norm_num [onePointStart, theorem16_intervalGradientCenter]
  have he : Real.exp (-t) ≠ 0 := ne_of_gt (Real.exp_pos _)
  intro hh
  have hz : (onePointStart - theorem16_intervalGradientCenter h) * Real.exp (-t) = 0 := by
    dsimp [theorem16_intervalGradientFlow] at hh
    linarith
  exact (mul_ne_zero hx he) hz

/-- 選択フィードバック `u = c_h − x` が生成する閉ループ軌道は、許容制御系の軌道：
担体上で `|u| ≤ 1`、`flow(s) = y + ∫₀ˢ u`。 -/
theorem selected_flow_admissible (h : Bool) {y : ℝ} (hy : y ∈ ball16 h) :
    ∃ u : VelControl, ∀ t : ℝ, 0 ≤ t →
      theorem16_intervalGradientFlow h y t = velTraj y u t := by
  set c := theorem16_intervalGradientCenter h
  have hyc : |y - c| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  refine ⟨⟨fun s => c - theorem16_intervalGradientFlow h y (max s 0), ?_, ?_⟩, ?_⟩
  · have hc : Continuous (fun s : ℝ => theorem16_intervalGradientFlow h y (max s 0)) := by
      unfold theorem16_intervalGradientFlow; fun_prop
    exact (continuous_const.sub hc).measurable
  · intro s
    have hq0 : 0 < Real.exp (-(max s 0)) := Real.exp_pos _
    have hq1 : Real.exp (-(max s 0)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith [le_max_right s 0]
    have : c - theorem16_intervalGradientFlow h y (max s 0) = -((y - c) * Real.exp (-(max s 0))) := by
      simp [theorem16_intervalGradientFlow, c]
    show |c - theorem16_intervalGradientFlow h y (max s 0)| ≤ 1
    rw [this, abs_neg, abs_mul, abs_of_pos hq0]
    nlinarith [abs_nonneg (y - c)]
  · intro t ht
    simp only [velTraj]
    have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (theorem16_intervalGradientFlow h y) (c - theorem16_intervalGradientFlow h y (max s 0)) s := by
      intro s hs
      have hs0 : 0 ≤ s := by
        rcases Set.mem_uIcc.mp hs with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
      have := theorem16_intervalGradientFlow_hasDerivAt h y s
      rw [max_eq_left hs0]
      convert this using 1
      simp [theorem16_intervalGradient, c]
    have hint : IntervalIntegrable (fun s : ℝ => c - theorem16_intervalGradientFlow h y (max s 0))
        volume 0 t := by
      apply Continuous.intervalIntegrable
      have hc : Continuous (fun s : ℝ => theorem16_intervalGradientFlow h y (max s 0)) := by
        unfold theorem16_intervalGradientFlow; fun_prop
      exact continuous_const.sub hc
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp [theorem16_intervalGradientFlow_start]

/-- N の共有核の認知座標の動きは、選択方策の時刻 A の流れに一致する。 -/
theorem SharedModelSignature.core_step_is_selected_flow {N : SharedModelSignature}
    (hA : AdditionalConditions N.legacy) (h : Bool) (z : CompleteState) (A E : ℝ) :
    cognitiveCoordinate (N.legacy.step (N.legacy.historyCenter h) A E z) =
      theorem16_intervalGradientFlow h (cognitiveCoordinate z) A := by
  rw [hA.toCommonDataCouplings.core_cognitive, hA.history_centers]
  rfl

/-- 有界ゲイン力学（N の共有核）では、どれだけ制御しても有限の積分利得 A では中心に届かない。
正典 TCZ が閉でないのはこの力学の性質で、正典 TCZ を担体にするには中心へ有限時間で届く別の許容入力
（速度制御）が要る（本ファイルの `VelControl`）。 -/
theorem SharedModelSignature.core_step_misses_center {N : SharedModelSignature}
    (hA : AdditionalConditions N.legacy) (h : Bool) (z : CompleteState) (A E : ℝ)
    (hz : cognitiveCoordinate z ≠ theorem16_intervalGradientCenter h) :
    cognitiveCoordinate (N.legacy.step (N.legacy.historyCenter h) A E z) ≠
      theorem16_intervalGradientCenter h := by
  rw [SharedModelSignature.core_step_is_selected_flow hA]
  intro hh
  have he : Real.exp (-A) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hz' : (cognitiveCoordinate z - theorem16_intervalGradientCenter h) * Real.exp (-A) = 0 := by
    dsimp [theorem16_intervalGradientFlow] at hh
    linarith
  exact (mul_ne_zero (sub_ne_zero.mpr hz) he) hz'



/-! ## 定理25の自己過程・定理19の実験を正典 TCZ に揃える -/

/-- TCZ 成分を正典 TCZ に取り替えた三表現。Self・Ego は旧表象のもの。 -/
def SharedModelSignature.selfRepCanonical (N : SharedModelSignature) (h : Bool) :
    C6TypedSelfRepresentation where
  Self := (N.legacy.selfRepresentation h).Self
  Ego := (N.legacy.selfRepresentation h).Ego
  TCZ := fun i => N.canonicalLayerTCZ h i

def SharedModelSignature.typedObservationCanonical (N : SharedModelSignature)
    (z : CommonConceptGamma × Bool) :
    (CommonConceptGamma × C6TypedSelfRepresentation) × Bool :=
  ((z.1, N.selfRepCanonical z.2), z.2)

theorem SharedModelSignature.typedObservationCanonical_measurable (N : SharedModelSignature) :
    Measurable N.typedObservationCanonical :=
  (measurable_fst.prodMk
    ((measurable_of_finite N.selfRepCanonical).comp measurable_snd)).prodMk measurable_snd

/-- 同じN.scmから生成する、正典 TCZ の型付き自己過程。 -/
def SharedModelSignature.selfProcessCanonical (N : SharedModelSignature) (d : Bool)
    (a : CommonConcept) :
    Theorem25SelfProcessSCM Bool (Bool × Bool)
      (CommonConceptGamma × C6TypedSelfRepresentation) Bool Bool where
  exogenousLaw := N.scm.model.scm.exogenousLaw
  inputHistory := N.scm.model.scm.globalHistory
  candidateVariable := N.scm.model.scm.candidateVariable d a
  inputHistoryAEMeasurable := N.scm.model.scm.globalHistoryAEMeasurable
  candidateAEMeasurable := N.scm.model.scm.candidateVariableAEMeasurable d a
  baselineEquation := fun H u => N.typedObservationCanonical
    (N.scm.model.scm.stateEquation d a H u,
      N.scm.model.scm.outputEquation d a H u (N.scm.model.scm.candidateVariable d a u))
  intervenedEquation := fun H s u => N.typedObservationCanonical
    (N.scm.model.scm.stateEquation d a H u, N.scm.model.scm.outputEquation d a H u s)
  baselineAEMeasurable := fun H => N.typedObservationCanonical_measurable.comp_aemeasurable
    (N.scm.model.scm.baselineJointAEMeasurable d a H)
  intervenedAEMeasurable := fun H s => N.typedObservationCanonical_measurable.comp_aemeasurable
    (N.scm.model.scm.intervenedJointAEMeasurable d a H s)

theorem SharedKernelInputs.selfProcessCanonical25A2 {N : SharedModelSignature}
    (h : SharedKernelInputs N) (d : Bool) (a : CommonConcept) :
    (N.selfProcessCanonical d a).toLawModel.Condition25A2 () := by
  apply (N.selfProcessCanonical d a).condition25A2
  · exact ((N.scm.model.scm.candidateIndependentOfGlobalContext d a).comp
      measurable_id measurable_fst).symm
  · intro H s
    apply ProbabilityMeasure.toMeasure_injective
    change (N.scm.model.scm.exogenousLaw.toMeasure).map _ =
      (N.scm.model.scm.exogenousLaw.toMeasure).map _
    apply Measure.map_congr
    filter_upwards [h.scm_output_noninterference d a H s] with u hu
    change N.typedObservationCanonical (_, _) = N.typedObservationCanonical (_, _)
    rw [hu]

local instance (a : CommonConcept) : MeasurableSpace (fullCommonLayerState a) :=
  sharedLayerStateMeasurable (fullCommonLayerIndex a)

/-- 19 の実験の観測：自己過程成分は正典 TCZ の自己過程。 -/
def SharedModelSignature.fullExperimentObservationCanonical (N : SharedModelSignature)
    (decode : SharedInformationDecoder) (d H : Bool) (a : CommonConcept)
    (x : fullCommonLayerState a) (T t : ℝ) (w : C6ExperimentInput) : FullExperimentObservation a :=
  let π := decode a w.2.2.2
  let y := N.data.trajectory a π x T t
  (w, ((N.selfProcessCanonical d a).baselineEquation H w.1, (y, N.data.runningCost a π y t)))

def SharedModelSignature.fullExperimentLawCanonical (N : SharedModelSignature)
    (decode : SharedInformationDecoder) (d H : Bool) (a : CommonConcept)
    (x : fullCommonLayerState a) (T t : ℝ) : Measure (FullExperimentObservation a) :=
  (N.fullExperimentInputLaw a).map (N.fullExperimentObservationCanonical decode d H a x T t)

theorem SharedDataPreservation.fullExperimentCanonical_selfProcess {N : SharedModelSignature}
    (h : SharedDataPreservation N) (decode d H a x T t) :
    (N.fullExperimentLawCanonical decode d H a x T t).map (fun z => z.2.1) =
      (N.selfProcessCanonical d a).exogenousLaw.toMeasure.map
        ((N.selfProcessCanonical d a).baselineEquation H) := by
  letI := h.fullInformation_probability a
  rw [SharedModelSignature.fullExperimentLawCanonical,
    Measure.map_map (show Measurable (fun z : FullExperimentObservation a => z.2.1) from
      measurable_fst.comp measurable_snd) (measurable_of_finite _)]
  change (N.fullExperimentInputLaw a).map (((N.selfProcessCanonical d a).baselineEquation H) ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_of_finite _) measurable_fst,
    SharedModelSignature.fullExperimentInputLaw, Measure.map_fst_prod]
  simp
  rfl

/-- 定理16の正典担体の受入型。担体は一点 `x₀=1/2` からの正典 TCZ（閉包なし、全許容制御）。 -/
structure Shared16CanonicalInputs (N : SharedModelSignature) : Prop where
  start_interior : 0 < onePointStart ∧ onePointStart < 1
  /-- 正典 TCZ ＝ 閉区間 `[c_h−1, c_h+1]`（履歴ごとに異なる）。 -/
  tcz_eq : ∀ (h : Bool) (i : ℕ), N.canonicalLayerTCZ h i = ball16 h
  carrier_eq : ∀ (h : Bool) (i : ℕ), layerSystem16Canonical.carrier h i = N.canonicalLayerTCZ h i
  carriers_differ : ball16 false ≠ ball16 true
  tcz_two_points : ∀ (h : Bool) (i : ℕ), ∃ x y : ℝ, x ≠ y ∧ x ∈ N.canonicalLayerTCZ h i ∧
    y ∈ N.canonicalLayerTCZ h i
  layer_nonempty : ∀ (h : Bool) (i : ℕ), (N.canonicalLayerTCZ h i).Nonempty
  layer_compact : ∀ (h : Bool) (i : ℕ), IsCompact (N.canonicalLayerTCZ h i)
  layer_convex : ∀ (h : Bool) (i : ℕ), Convex ℝ (N.canonicalLayerTCZ h i)
  /-- 閉包を取らなくても中心は有限時刻で許容制御により到達する。 -/
  center_reached : ∀ h : Bool, ∃ τ : ℝ, 0 ≤ τ ∧
    theorem16_intervalGradientCenter h ∈ velReach onePointStart τ
  /-- 一点の指数軌道（選択方策）は有限時刻で中心に届かない。 -/
  selected_trajectory_misses_center : ∀ (h : Bool) (t : ℝ),
    theorem16_intervalGradientFlow h onePointStart t ≠ theorem16_intervalGradientCenter h
  /-- 選択フィードバックは許容制御系の許容方策。 -/
  selected_admissible : ∀ (h : Bool) (y : ℝ), y ∈ ball16 h →
    ∃ u : VelControl, ∀ t : ℝ, 0 ≤ t → theorem16_intervalGradientFlow h y t = velTraj y u t
  /-- N の共有核の認知座標の動きは、選択方策の時刻 A の流れ。 -/
  core_is_selected_flow : ∀ (h : Bool) (z : CompleteState) (A E : ℝ),
    cognitiveCoordinate (N.legacy.step (N.legacy.historyCenter h) A E z) =
      theorem16_intervalGradientFlow h (cognitiveCoordinate z) A
  project_maps : type_of% layerSystem16Canonical.projectMaps
  project_affine : type_of% layerSystem16Canonical.projectAffineOnCarrier
  project_refl : type_of% layerSystem16Canonical.projectRefl
  project_comp : type_of% layerSystem16Canonical.projectComp
  project_continuous : type_of% layerSystem16Canonical.projectContinuousOn
  no_maximum : type_of% layerSystem16Canonical.noMax
  feedback_commutes : type_of% layerSystem16Canonical.feedbackCommutes
  feedback_continuous : type_of% layerSystem16Canonical.feedbackContinuous
  rep_closed : ∀ h, IsClosed (selfRepC h).relation
  rep_continuous : ∀ h, Continuous (selfRepC h).represent
  rep_map_continuous : ∀ h, Continuous (feedback16Canonical h 0)
  complete : ∀ h, @CompleteSpace (ILc h) (metricC h).toPseudoMetricSpace.toUniformSpace
  contracting : type_of% contractingC
  entry_clause : Theorem16EntryClauseC
  fixed_point_center : ∀ (h : Bool) (x : ILc h),
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes h x = x →
    ∀ i, x.1 i = theorem16_intervalGradientCenter h
  fixed_points_separate : ∀ (xf : ILc false) (xt : ILc true),
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes false xf = xf →
    historyInducedAffineInverseLimitMap (fun _ : Nat => ℝ)
      layerSystem16Canonical.carrier layerSystem16Canonical.project
      layerSystem16Canonical.projectMaps layerSystem16Canonical.feedback
      layerSystem16Canonical.feedbackCommutes true xt = xt →
    xf.1 ≠ xt.1

theorem ball16_false_ne_true : ball16 false ≠ ball16 true := by
  intro hc
  have := congrArg (fun S : Set ℝ => (-1 : ℝ) ∈ S) hc
  simp [ball16, theorem16_intervalGradientCenter] at this
  norm_num at this

theorem SharedModelSignature.shared16CanonicalInputs {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) :
    Shared16CanonicalInputs N where
  start_interior := by unfold onePointStart; constructor <;> norm_num
  tcz_eq := fun h i => SharedModelSignature.canonicalLayerTCZ_eq hp hA h i
  carrier_eq := fun h i => (SharedModelSignature.canonicalLayerTCZ_eq hp hA h i).symm
  carriers_differ := ball16_false_ne_true
  tcz_two_points := fun h i => by
    rw [SharedModelSignature.canonicalLayerTCZ_eq hp hA]
    refine ⟨theorem16_intervalGradientCenter h - 1, theorem16_intervalGradientCenter h + 1,
      by linarith, ⟨le_rfl, by linarith⟩, ⟨by linarith, le_rfl⟩⟩
  layer_nonempty := fun h i => by
    rw [SharedModelSignature.canonicalLayerTCZ_eq hp hA]; exact ⟨_, center_mem_ball16 h⟩
  layer_compact := fun h i => by
    rw [SharedModelSignature.canonicalLayerTCZ_eq hp hA]; exact isCompact_Icc
  layer_convex := fun h i => by
    rw [SharedModelSignature.canonicalLayerTCZ_eq hp hA]; exact convex_Icc _ _
  center_reached := fun h => by
    refine ⟨|theorem16_intervalGradientCenter h - onePointStart|, abs_nonneg _, ?_⟩
    exact velReach_mem_of
  selected_trajectory_misses_center := onePoint_flow_ne_center
  selected_admissible := fun h y hy => selected_flow_admissible h hy
  core_is_selected_flow := fun h z A E => SharedModelSignature.core_step_is_selected_flow hA h z A E
  project_maps := layerSystem16Canonical.projectMaps
  project_affine := layerSystem16Canonical.projectAffineOnCarrier
  project_refl := layerSystem16Canonical.projectRefl
  project_comp := layerSystem16Canonical.projectComp
  project_continuous := layerSystem16Canonical.projectContinuousOn
  no_maximum := layerSystem16Canonical.noMax
  feedback_commutes := layerSystem16Canonical.feedbackCommutes
  feedback_continuous := layerSystem16Canonical.feedbackContinuous
  rep_closed := fun h => (selfRepC h).relation_closed
  rep_continuous := fun h => (selfRepC h).represent_continuous
  rep_map_continuous := fun h => feedback16Canonical_continuous h 0
  complete := completeC
  contracting := contractingC
  entry_clause := theorem16EntryClauseC_holds
  fixed_point_center := fun h x hfix i => fixedPointC_coordinate h x hfix i
  fixed_points_separate := fun xf xt hf ht heq => by
    have h0 := fixedPointC_coordinate false xf hf 0
    have h1 := fixedPointC_coordinate true xt ht 0
    rw [heq] at h0
    simp [theorem16_intervalGradientCenter] at h0 h1
    linarith

theorem sharedModel_shared16CanonicalInputs : Shared16CanonicalInputs sharedModel :=
  SharedModelSignature.shared16CanonicalInputs sharedModel_preservation
    sharedModel_explicitAdditionalConditions.legacy

/-- 定理25の自己過程の TCZ 成分が、正典の定理16担体と同じ対象であることの受入型。 -/
structure Shared25CanonicalSelf (N : SharedModelSignature) : Prop where
  a2 : ∀ d a, (N.selfProcessCanonical d a).toLawModel.Condition25A2 ()
  tcz_is_carrier : ∀ h i, (N.selfRepCanonical h).TCZ i = layerSystem16Canonical.carrier h i
  tcz_ball : ∀ h i, (N.selfRepCanonical h).TCZ i = ball16 h
  tcz_history_sensitive : (N.selfRepCanonical false).TCZ 0 ≠ (N.selfRepCanonical true).TCZ 0
  /-- Ego は `[0,1]` との共通部分で、担体上のフィードバック（時刻1の勾配流）に一致する
  （Ego の型が `Set.Icc 0 1` のため、担体が `[0,1]` を超える部分は述べない）。 -/
  ego_agrees_on_unit : ∀ h i (x : Set.Icc (0 : ℝ) 1) (hx : x.1 ∈ ball16 h),
    (((N.selfRepCanonical h).Ego i x : Set.Icc (0 : ℝ) 1) : ℝ) =
      (feedback16Canonical h i ⟨x.1, hx⟩ : ℝ)

theorem SharedModelSignature.shared25CanonicalSelf {N : SharedModelSignature}
    (hk : SharedKernelInputs N) (h1 : Shared16CanonicalInputs N) : Shared25CanonicalSelf N := by
  refine ⟨hk.selfProcessCanonical25A2, ?_, ?_, ?_, ?_⟩
  · intro h i; exact (h1.carrier_eq h i).symm
  · intro h i; exact h1.tcz_eq h i
  · change N.canonicalLayerTCZ false 0 ≠ N.canonicalLayerTCZ true 0
    rw [h1.tcz_eq, h1.tcz_eq]; exact h1.carriers_differ
  · intro h i x hx
    change (((N.legacy.selfRepresentation h).Ego i x : Set.Icc (0 : ℝ) 1) : ℝ) = _
    rw [hk.additional.toCommonDataCouplings.self_ego]
    rfl

theorem sharedModel_shared25CanonicalSelf : Shared25CanonicalSelf sharedModel :=
  SharedModelSignature.shared25CanonicalSelf sharedModel_kernelInputs
    sharedModel_shared16CanonicalInputs

/-- 19 の主体・履歴と 16/25 の同一性（正典 TCZ の自己過程で）。 -/
structure SharedSubjectIdentityCanonical (N : SharedModelSignature) : Prop where
  experiment_self_process : ∀ (d H : Bool) (a : CommonConcept) (x : fullCommonLayerState a)
    (T t : ℝ),
    (N.fullExperimentLawCanonical fullInformationDecoder d H a x T t).map (fun z => z.2.1) =
      (N.selfProcessCanonical d a).exogenousLaw.toMeasure.map
        ((N.selfProcessCanonical d a).baselineEquation H)
  representation_is_canonical : ∀ (d : Bool) (a : CommonConcept) (H s : Bool) (u : Bool × Bool),
    ((N.selfProcessCanonical d a).intervenedEquation H s u).1.2 =
      N.selfRepCanonical (N.scm.model.scm.outputEquation d a H u s)
  output_is_history : ∀ (d : Bool) (a : CommonConcept) (H s : Bool) (u : Bool × Bool),
    N.scm.model.scm.outputEquation d a H u s = H
  gamma_from_16_fixed_point : ∀ (d : Bool) (a : CommonConcept) (h : Bool) (u : Bool × Bool),
    N.scm.model.scm.stateEquation d a h u =
      commonConceptStateCode d a (theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1

theorem sharedModel_subjectIdentityCanonical : SharedSubjectIdentityCanonical sharedModel where
  experiment_self_process := fun d H a x T t =>
    sharedModel_preservation.fullExperimentCanonical_selfProcess fullInformationDecoder d H a x T t
  representation_is_canonical := fun d a H s u => rfl
  output_is_history := sharedModel_subjectIdentity.output_is_history
  gamma_from_16_fixed_point := sharedModel_subjectIdentity.gamma_from_16_fixed_point

theorem SharedSubjectIdentityCanonical.representation_eq_history {N : SharedModelSignature}
    (h : SharedSubjectIdentityCanonical N) (d : Bool) (a : CommonConcept) (H s : Bool)
    (u : Bool × Bool) :
    ((N.selfProcessCanonical d a).intervenedEquation H s u).1.2 = N.selfRepCanonical H := by
  rw [h.representation_is_canonical, h.output_is_history]

/-- v7：v6 の全受入型に、正典 TCZ の定理16担体・定理25の自己過程・定理19の実験の同一性を加えた存在宣言。
旧 `[0,1]` 版・一点閉包版の受入型は別の読みとして残る（正典版は置換ではなく追加）。 -/
theorem final_consistency_v7 :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N ∧
        GenealogyMortalityExtension N ∧ Shared16OnePointInputs N ∧ SharedTheorem21V0 N ∧
        Shared25OnePointSelf N ∧ SharedTheorem21V0Common N ∧ MortalityOnN N ∧
        MortalityPresence25B ∧ Shared16CanonicalInputs N ∧ Shared25CanonicalSelf N ∧
        SharedSubjectIdentityCanonical N :=
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
    sharedModel_borelStructure, sharedModel_genealogyMortality, sharedModel_shared16OnePointInputs,
    sharedModel_theorem21V0, sharedModel_shared25OnePointSelf,
    SharedModelSignature.sharedTheorem21V0Common sharedModel_theorem21V0
      sharedModel_stageSwitchInputs,
    sharedModel_mortalityOnN, mortalityPresence25B,
    sharedModel_shared16CanonicalInputs, sharedModel_shared25CanonicalSelf,
    sharedModel_subjectIdentityCanonical⟩

#print axioms SharedModelSignature.canonicalLayerTCZ_eq
#print axioms SharedModelSignature.shared16CanonicalInputs
#print axioms sharedModel_shared25CanonicalSelf
#print axioms sharedModel_subjectIdentityCanonical
#print axioms final_consistency_v7

end Tomabechi.Consistency.R123
