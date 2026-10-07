import Tomabechi.Consistency.ConsistencyR123_FixedCapacity

/-!
# 定理1・2・4 を共通領域 X 全体で共有評価 `commonV0X` について

以前の段階では、定理20・24 が全域で `commonV0X = 1 + 2(x₀−x₁)²` を使うこと、全段 `U_n ⊂ X` は示したが、
定理1・2・4 を箱の外の初期点を含む `X` 全体で述べ直すことが残っていた。理由は定理2の個人閾値残差
`[(x_i)²−θ]₊`（`θ=1/10` 固定、`DA`）で、箱の外では `Φ₂ ≠ commonV0X − 1` だった。

**閾値 θ は原文の定理2の自由なパラメータ**なので、`θ` を大きく取り直した並列の残差系 `DX`（`θX=10`）を
置く。`X3 := {x | ∀ i, |x i| ≤ 3}`（段の閉球 `closedBall 0 3` を含む）の上では個人残差の項は消え、
`DX.potential x = 2(x₀−x₁)² = commonV0X x − 1`。したがって

* **定理2：** `DX`・`X3` の全初期点・全非負開始時刻で、定理2の定量結論（共有TCZまでの距離・個人残差・
  辺不整合の指数減衰と極限）。
* **定理1：** 閾値 1 の残差 `residual1 (commonV0X y) 1 = 2(y₀−y₁)²`。**ℝ² の全初期点**で成り立つ。
* **定理4：** 臨場感 `P = exp(−(commonV0X − 1))`、`Q = 1`、`κ=1`、`θ_P=0`。**ℝ² の全初期点**で成り立つ。

3 つとも同じ `commonV0X`・同じ一点 K（実 flow の閉到達集合）・同じ共有 flow で、20 の拡張・24 の有限層
費用と同じ評価である。N の `pointAdapter` の flow・到達集合を通して述べる。

**範囲：** 定理2は `X3` の上（`θX` を `X3` の大きさに合わせて取るため）。定理1・4 は全域。定理3
（`Φ₃` は抽象残差で零平均箱点に限る）は共通状態領域の対象外。旧 `N.base.V0`・`DA`（θ=1/10、箱）に基づく
入口は旧版として残る（置換は最終の統合で行う）。
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Theorem2 Tomabechi.Theorem1 Tomabechi.Theorem4
open Tomabechi.Consistency.R2 Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Examples.Theorem2

/-- 領域 `X3`：各座標の絶対値 ≤ 3（段の閉球を含む）。 -/
def domainX3 : Set AgentState := {x | ∀ i, |x i| ≤ 3}

/-- `X3` に合わせて大きく取った個人閾値（原文の定理2のパラメータ）。 -/
def θX : ℝ := 10

/-- 定理2の並列の共有残差系：`DA` と同じ構造で閾値だけ `θX`。 -/
abbrev DX : StatePairResidualSystem (Fin 2) (Fin 2) where
  State := fun _ => ℝ
  Representation := ℝ
  endpoint := endpointF
  reverseEdge := Fin.rev
  reverseEdge_involutive := Fin.rev_rev
  reverse_endpoint_left := by intro e; fin_cases e <;> rfl
  reverse_endpoint_right := by intro e; fin_cases e <;> rfl
  repr := fun _ x => x
  basePotential := fun _ x _ => x ^ 2
  threshold := fun _ => θX
  individual := fun _ x _ => max (x ^ 2 - θX) 0
  individualWeight := fun _ => 1
  edgeWeight := fun _ => γ / 2
  edgeWeight_reverse := fun _ => rfl
  mismatch := fun _ x y _ => (x - y) ^ 2
  reverseLeft := fun _ x => x
  reverseRight := fun _ y => y
  reverseLeft_repr := fun _ _ => rfl
  reverseRight_repr := fun _ _ => rfl
  mismatch_symmetric := by intro e x y t; show (x - y) ^ 2 = (y - x) ^ 2; ring
  mismatch_nonneg := fun _ _ _ _ => sq_nonneg _
  mismatch_zero_iff := by
    intro e x y t
    show (x - y) ^ 2 = 0 ↔ x = y
    rw [sq_eq_zero_iff, sub_eq_zero]
  individualWeight_pos := fun _ => one_pos
  edgeWeight_pos := fun _ => by unfold γ; norm_num
  individual_nonneg := fun _ _ _ => by simp
  individual_eq_positivePart := fun _ _ _ => rfl

theorem DX_potential_eq (x : AgentState) (t : ℝ) :
    DX.potential x t = max (x 0 ^ 2 - θX) 0 + max (x 1 ^ 2 - θX) 0 + γ * (x 0 - x 1) ^ 2 := by
  have : DX.potential x t = _ := rfl
  rw [this]
  simp [Fin.sum_univ_two, endpointF, StatePairResidualSystem.potential, γ]
  ring

/-- `X3` の上で `DX.potential = commonV0X − 1`。 -/
theorem DX_potential_eq_on_X3 {x : AgentState} (hx : x ∈ domainX3) (t : ℝ) :
    DX.potential x t = commonV0X x - 1 := by
  rw [DX_potential_eq]
  have h0 : x 0 ^ 2 - θX ≤ 0 := by
    have := abs_le.mp (hx 0); unfold θX; nlinarith [this.1, this.2]
  have h1 : x 1 ^ 2 - θX ≤ 0 := by
    have := abs_le.mp (hx 1); unfold θX; nlinarith [this.1, this.2]
  rw [max_eq_right h0, max_eq_right h1]
  simp only [commonV0X, γ]
  ring

/-- 全域の共有残差 `F y = commonV0X y − 1 = 2(y₀−y₁)²`。 -/
def Fg (y : AgentState) : ℝ := commonV0X y - 1

theorem Fg_eq (y : AgentState) : Fg y = 2 * (y 0 - y 1) ^ 2 := by
  simp only [Fg, commonV0X]; ring

theorem Fg_nonneg (y : AgentState) : 0 ≤ Fg y := by
  rw [Fg_eq]; positivity

/-- 共有 flow 上で `F` は率 6 で減衰（全初期点）。 -/
theorem Fg_flow (x : AgentState) (t₀ t : ℝ) :
    Fg (consensusOptimalFlow.flow t₀ x t) = Fg x * Real.exp (-6 * (t - t₀)) := by
  rw [Fg_eq, Fg_eq, consensusOptimalFlow_gap, mul_pow, ← Real.exp_nat_mul]
  have : ((2 : ℕ) : ℝ) * (-3 * (t - t₀)) = -6 * (t - t₀) := by push_cast; ring
  rw [this]; ring

/-- 合意点は一点 K に属する。 -/
theorem agreementPoint_mem_K (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    agreementPoint x ∈ pointReachableClosure x t₀ := by
  rw [pointReachableClosure_eq_orbitSegment x t₀ ht₀]
  refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
  simp [segmentPoint, agreementPoint]

theorem Fg_agreement (x : AgentState) : Fg (agreementPoint x) = 0 := by
  rw [Fg_eq]; simp [agreementPoint]

/-- 共有 flow は `X3` を保つ（開始時刻以降）。 -/
theorem flow_mem_X3 {x : AgentState} (hx : x ∈ domainX3) (t₀ t : ℝ) (ht : t₀ ≤ t) :
    consensusOptimalFlow.flow t₀ x t ∈ domainX3 := by
  have hq0 : 0 < Real.exp (-3 * (t - t₀)) := Real.exp_pos _
  have hq1 : Real.exp (-3 * (t - t₀)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  set q := Real.exp (-3 * (t - t₀))
  have h0 := abs_le.mp (hx 0)
  have h1 := abs_le.mp (hx 1)
  intro i
  fin_cases i
  · change |meanState x + halfDifference x * q| ≤ 3
    simp only [meanState, halfDifference]
    rw [abs_le]; constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]
  · change |meanState x - halfDifference x * q| ≤ 3
    simp only [meanState, halfDifference]
    rw [abs_le]; constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

/-- 合意点・一点 K（線分）は `X3` に入る。 -/
theorem agreementPoint_mem_X3 {x : AgentState} (hx : x ∈ domainX3) : agreementPoint x ∈ domainX3 := by
  have h0 := abs_le.mp (hx 0)
  have h1 := abs_le.mp (hx 1)
  have hm : |meanState x| ≤ 3 := by
    rw [abs_le]; simp only [meanState]; constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  intro i
  fin_cases i <;> exact hm

/-! ## 共通の補助：合意点への距離と指数 -/

/-- 共有 flow の合意点への距離の二乗は、その点の共有残差以下（全初期点）。 -/
theorem dist_flow_agreement_sq_le (x : AgentState) (t₀ t : ℝ) :
    dist (consensusOptimalFlow.flow t₀ x t) (agreementPoint x) ^ 2 ≤
      Fg (consensusOptimalFlow.flow t₀ x t) := by
  have hdist := consensusOptimalFlow_dist_agreementPoint_le x t₀ t
  have hh := sq_le_sq₀ (dist_nonneg : 0 ≤ dist
    (consensusOptimalFlow.flow t₀ x t) (agreementPoint x)) (by positivity :
      0 ≤ |halfDifference x| * Real.exp (-3 * (t - t₀)))
  have h := hh.mpr hdist
  have hsq : dist (consensusOptimalFlow.flow t₀ x t) (agreementPoint x) ^ 2 ≤
      (halfDifference x) ^ 2 * Real.exp (-6 * (t - t₀)) := by
    simpa only [mul_pow, sq_abs, ← Real.exp_nat_mul, Nat.cast_ofNat,
      show (2 : ℝ) * (-3 * (t - t₀)) = -6 * (t - t₀) by ring] using h
  rw [Fg_flow, Fg_eq]
  have : 2 * (x 0 - x 1) ^ 2 = 8 * (halfDifference x) ^ 2 := by
    simp only [halfDifference]; ring
  rw [this]
  nlinarith [sq_nonneg (halfDifference x), Real.exp_pos (-6 * (t - t₀))]

/-- 率6の指数 `F e^{-6(t−t₀)}` の微分。 -/
theorem hasDerivAt_Fexp (F t₀ t : ℝ) :
    HasDerivAt (fun s => F * Real.exp (-6 * (s - t₀))) (-6 * (F * Real.exp (-6 * (t - t₀)))) t := by
  have hlin : HasDerivAt (fun u : ℝ => -6 * (u - t₀)) (-6) t := by
    simpa using ((hasDerivAt_id t).sub_const t₀).const_mul (-6)
  have hexp := (Real.hasDerivAt_exp (-6 * (t - t₀))).comp t hlin
  convert hexp.const_mul F using 1
  · rfl
  · ring

theorem Fexp_ac (F t₀ T : ℝ) :
    AbsolutelyContinuousOnInterval (fun s => F * Real.exp (-6 * (s - t₀))) t₀ T := by
  have hcd : ContDiff ℝ 1 (fun s : ℝ => F * Real.exp (-6 * (s - t₀))) := by fun_prop
  exact hcd.contDiffOn.absolutelyContinuousOnInterval

/-! ## 定理1：全初期点・`commonV0X` -/

/-- 一点 K 内の閾値 1 の TCZ（`commonV0X` について）。 -/
def point1TargetX (x : AgentState) (t₀ : ℝ) : Set AgentState :=
  {y | y ∈ pointReachableClosure x t₀ ∧ commonV0X y ≤ 1}

theorem residual1_commonV0X (y : AgentState) :
    residual1 (commonV0X y) 1 = Fg y := by
  unfold residual1 Fg
  exact max_eq_left (by have := Fg_nonneg y; unfold Fg at this; linarith)

theorem agreement_mem_target1 (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    agreementPoint x ∈ point1TargetX x t₀ := by
  refine ⟨agreementPoint_mem_K x t₀ ht₀, ?_⟩
  have := Fg_agreement x
  unfold Fg at this; linarith

/-- 定理1（`commonV0X`、ℝ² の全初期点・全非負開始時刻）。 -/
theorem theorem1_commonDomainX (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈ pointReachableClosure x t₀) ∧
    (∀ t, t₀ ≤ t → Metric.infDist (consensusOptimalFlow.flow t₀ x t) (point1TargetX x t₀) ≤
      Real.sqrt (Fg x) * Real.exp (-3 * (t - t₀))) ∧
    Tendsto (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t) (point1TargetX x t₀))
      atTop (𝓝 0) := by
  have hcore := theorem1_reachable_tcz_distance_tendsto_zero
    (consensusOptimalFlow.flow t₀ x)
    (policyFlowReachableAt consensusOptimalFlow {x} t₀)
    (fun y _ => commonV0X y) 1 3 1 t₀
    (fun t ht => mem_policyFlowReachableAt_of_flow consensusOptimalFlow {x}
      t₀ t x (Set.mem_singleton x) ht)
    (fun T hT s hs => ⟨agreementPoint x, agreement_mem_target1 x t₀ ht₀⟩)
    (fun T hT => by
      have hfun : (fun s => residual1 ((fun y (_ : ℝ) => commonV0X y)
          (consensusOptimalFlow.flow t₀ x s) s) 1) =
          fun s => Fg x * Real.exp (-6 * (s - t₀)) := by
        funext s; simp only [residual1_commonV0X, Fg_flow]
      rw [hfun]
      exact Fexp_ac _ _ _)
    (fun T hT => by
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun t _ => ?_)
      have hfun : (fun r => residual1 ((fun y (_ : ℝ) => commonV0X y)
          (consensusOptimalFlow.flow t₀ x r) r) 1) =
          fun r => Fg x * Real.exp (-6 * (r - t₀)) := by
        funext r; simp only [residual1_commonV0X, Fg_flow]
      rw [hfun, (hasDerivAt_Fexp (Fg x) t₀ t).deriv]
      simp only [residual1_commonV0X, Fg_flow]
      nlinarith)
    (fun T hT s hs => by
      have hmem : agreementPoint x ∈ {y | y ∈ closedLoopReachableSet
          (policyFlowReachableAt consensusOptimalFlow {x} t₀) ∧ (fun y _ => commonV0X y) y s ≤ 1} :=
        agreement_mem_target1 x t₀ ht₀
      have hle := Metric.infDist_le_dist_of_mem (x := consensusOptimalFlow.flow t₀ x s) hmem
      simp only [one_mul, residual1_commonV0X]
      have hsq := dist_flow_agreement_sq_le x t₀ s
      exact (pow_le_pow_left₀ Metric.infDist_nonneg hle 2).trans hsq)
    ht₀ (by norm_num) (by norm_num)
  obtain ⟨h1, h2, h3⟩ := hcore
  refine ⟨h1, fun t ht => ?_, h3⟩
  have := h2 t ht
  rw [one_mul, consensusOptimalFlow.initial, residual1_commonV0X] at this
  exact this

/-! ## 定理4：全初期点・`commonV0X`、臨場感 `P = exp(−F)`、`Q = 1` -/

/-- 実効評価 `Ṽ = V₀ − κ P Q`（κ=1）。 -/
def effX (y : AgentState) : ℝ :=
  effectivePotential (commonV0X y) (Real.exp (-(Fg y))) 1 1

theorem effX_eq (y : AgentState) : effX y = 1 + Fg y - Real.exp (-(Fg y)) := by
  unfold effX effectivePotential Fg; ring

theorem effX_bounds (y : AgentState) : Fg y ≤ effX y ∧ effX y ≤ 2 * Fg y := by
  rw [effX_eq]
  have hF := Fg_nonneg y
  have hexp_le : Real.exp (-(Fg y)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hone_sub : 1 - Fg y ≤ Real.exp (-(Fg y)) := by
    have h := Real.add_one_le_exp (-(Fg y)); linarith
  constructor <;> linarith

theorem effX_nonneg (y : AgentState) : 0 ≤ effX y :=
  (Fg_nonneg y).trans (effX_bounds y).1

/-- 閾値 0 の臨場感加重 TCZ（一点 K 内）。 -/
def point4TargetX (x : AgentState) (t₀ : ℝ) : Set AgentState :=
  weightedTCZ (pointReachableClosure x t₀) (fun y _ => commonV0X y)
    (fun y _ => Real.exp (-(Fg y))) (fun _ _ => (1 : ℝ)) 1 0 0

theorem agreement_mem_target4 (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    agreementPoint x ∈ point4TargetX x t₀ := by
  refine ⟨agreementPoint_mem_K x t₀ ht₀, ?_⟩
  change effX (agreementPoint x) ≤ 0
  rw [effX_eq, Fg_agreement]; simp

theorem residual4_X (y : AgentState) :
    residual4 (commonV0X y) (Real.exp (-(Fg y))) 1 1 0 = effX y := by
  unfold residual4 Tomabechi.Theorem1.residual1
  change max (effX y - 0) 0 = effX y
  rw [sub_zero]; exact max_eq_left (effX_nonneg y)

/-- 共有 flow に沿った実効残差の明示式。 -/
theorem effX_flow (x : AgentState) (t₀ t : ℝ) :
    effX (consensusOptimalFlow.flow t₀ x t) = sharedT4Explicit (Fg x) t₀ t := by
  rw [effX_eq, Fg_flow]; rfl

/-- 定理4（`commonV0X`、ℝ² の全初期点・全非負開始時刻）。 -/
theorem theorem4_commonDomainX (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈ pointReachableClosure x t₀) ∧
    (∀ t, t₀ ≤ t → Metric.infDist (consensusOptimalFlow.flow t₀ x t) (point4TargetX x t₀) ≤
      Real.sqrt (effX x) * Real.exp (-(3 / 2 : ℝ) * (t - t₀))) ∧
    Tendsto (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t) (point4TargetX x t₀))
      atTop (𝓝 0) := by
  have hres : ∀ r, residual4 ((fun y (_ : ℝ) => commonV0X y) (consensusOptimalFlow.flow t₀ x r) r)
      ((fun y (_ : ℝ) => Real.exp (-(Fg y))) (consensusOptimalFlow.flow t₀ x r) r)
      ((fun (_ : AgentState) (_ : ℝ) => (1 : ℝ)) (consensusOptimalFlow.flow t₀ x r) r) 1 0 =
      sharedT4Explicit (Fg x) t₀ r := fun r => by
    show residual4 (commonV0X _) (Real.exp (-(Fg _))) 1 1 0 = _
    rw [residual4_X, effX_flow]
  have hcore := weighted_reachable_tcz_distance_tendsto_zero
    (consensusOptimalFlow.flow t₀ x)
    (policyFlowReachableAt consensusOptimalFlow {x} t₀)
    (fun y _ => commonV0X y) (fun y _ => Real.exp (-(Fg y))) (fun _ _ => (1 : ℝ))
    1 0 (3 / 2) 1 t₀
    (fun t ht => mem_policyFlowReachableAt_of_flow consensusOptimalFlow {x}
      t₀ t x (Set.mem_singleton x) ht)
    (fun T hT s hs => ⟨agreementPoint x, agreement_mem_target4 x t₀ ht₀⟩)
    (fun T hT => by
      have hfun : (fun s => residual4 ((fun y (_ : ℝ) => commonV0X y) (consensusOptimalFlow.flow t₀ x s) s)
          ((fun y (_ : ℝ) => Real.exp (-(Fg y))) (consensusOptimalFlow.flow t₀ x s) s)
          ((fun (_ : AgentState) (_ : ℝ) => (1 : ℝ)) (consensusOptimalFlow.flow t₀ x s) s) 1 0) =
          sharedT4Explicit (Fg x) t₀ := funext hres
      rw [hfun]
      have hcd : ContDiff ℝ 1 (sharedT4Explicit (Fg x) t₀) := by
        unfold sharedT4Explicit; fun_prop
      exact hcd.contDiffOn.absolutelyContinuousOnInterval)
    (fun T hT => by
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun t _ => ?_)
      have hfun : (fun r => residual4 ((fun y (_ : ℝ) => commonV0X y) (consensusOptimalFlow.flow t₀ x r) r)
          ((fun y (_ : ℝ) => Real.exp (-(Fg y))) (consensusOptimalFlow.flow t₀ x r) r)
          ((fun (_ : AgentState) (_ : ℝ) => (1 : ℝ)) (consensusOptimalFlow.flow t₀ x r) r) 1 0) =
          sharedT4Explicit (Fg x) t₀ := funext hres
      rw [hfun, (sharedT4Explicit_hasDerivAt (Fg x) t₀ t).deriv, hres t]
      have hG : 0 ≤ Fg x * Real.exp (-6 * (t - t₀)) := mul_nonneg (Fg_nonneg x) (Real.exp_pos _).le
      have hb := effX_bounds (consensusOptimalFlow.flow t₀ x t)
      rw [← effX_flow, Fg_flow] at *
      have hexp := Real.exp_pos (-(Fg x * Real.exp (-6 * (t - t₀))))
      nlinarith [hb.2, hexp, hG])
    (fun T hT s hs => by
      have hmem : agreementPoint x ∈ weightedTCZ (closedLoopReachableSet
          (policyFlowReachableAt consensusOptimalFlow {x} t₀)) (fun y _ => commonV0X y)
          (fun y _ => Real.exp (-(Fg y))) (fun _ _ => (1 : ℝ)) 1 0 s :=
        agreement_mem_target4 x t₀ ht₀
      have hle := Metric.infDist_le_dist_of_mem (x := consensusOptimalFlow.flow t₀ x s) hmem
      rw [one_mul]
      show _ ≤ residual4 (commonV0X _) (Real.exp (-(Fg _))) 1 1 0
      rw [residual4_X]
      exact (pow_le_pow_left₀ Metric.infDist_nonneg hle 2).trans
        ((dist_flow_agreement_sq_le x t₀ s).trans (effX_bounds _).1))
    ht₀ (by norm_num) (by norm_num)
  obtain ⟨h1, h2, h3⟩ := hcore
  refine ⟨h1, fun t ht => ?_, h3⟩
  have := h2 t ht
  rw [one_mul, consensusOptimalFlow.initial] at this
  have e : residual4 ((fun y (_ : ℝ) => commonV0X y) x t₀)
      ((fun y (_ : ℝ) => Real.exp (-(Fg y))) x t₀)
      ((fun (_ : AgentState) (_ : ℝ) => (1 : ℝ)) x t₀) 1 0 = effX x := residual4_X x
  rw [e] at this
  exact this

/-! ## 定理2：`X3` の全初期点、`DX`（θX=10） -/

theorem DX_connected : ∀ i j : Fin 2, Relation.ReflTransGen
    (fun a b => ∃ e, ((DX.endpoint e).1 = a ∧ (DX.endpoint e).2 = b) ∨
      ((DX.endpoint e).1 = b ∧ (DX.endpoint e).2 = a)) i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.single ⟨0, Or.inr ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.refl

/-- 定理2（`DX`、`X3` の全初期点・全非負開始時刻）。 -/
theorem theorem2_commonDomainX {x : AgentState} (hx : x ∈ domainX3) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    StatePairResidualSystem.ReachableStatePairConclusion DX
      (policyFlowReachableAt consensusOptimalFlow {x} t₀) (consensusOptimalFlow.flow t₀ x)
      DX_connected 3 1 t₀ := by
  have hpot : ∀ s, t₀ ≤ s →
      DX.potential (consensusOptimalFlow.flow t₀ x s) s = Fg x * Real.exp (-6 * (s - t₀)) := by
    intro s hs
    rw [DX_potential_eq_on_X3 (flow_mem_X3 hx t₀ s hs) s]
    exact Fg_flow x t₀ s
  apply DX.theorem2_reachable_state_pair_quantitative_conclusion _ _ DX_connected 3 1 t₀
    (by norm_num) (by norm_num) ht₀
  · intro s hs
    exact mem_policyFlowReachableAt_of_flow consensusOptimalFlow {x} t₀ s x
      (Set.mem_singleton x) hs
  · intro s hs
    refine ⟨agreementPoint x, agreementPoint_mem_K x t₀ ht₀, ?_⟩
    rw [DX_potential_eq_on_X3 (agreementPoint_mem_X3 hx) s]
    exact Fg_agreement x
  · intro T hT
    refine (Fexp_ac (Fg x) t₀ T).congr ?_
    intro s hs
    rw [Set.uIcc_of_le hT] at hs
    exact (hpot s hs.1).symm
  · intro T hT
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (measure_singleton t₀ : volume ({t₀} : Set ℝ) = 0)] with t hne ht
    have hlt : t₀ < t := lt_of_le_of_ne ht.1 (by simpa [eq_comm] using hne)
    have hnear : (fun s => DX.potential (consensusOptimalFlow.flow t₀ x s) s) =ᶠ[𝓝 t]
        fun s => Fg x * Real.exp (-6 * (s - t₀)) := by
      filter_upwards [Ioi_mem_nhds hlt] with u hu
      exact hpot u hu.le
    rw [((hasDerivAt_Fexp (Fg x) t₀ t).congr_of_eventuallyEq hnear).deriv, hpot t ht.1]
    nlinarith
  · intro s hs
    have hmem : agreementPoint x ∈ DX.sharedTCZ (closedLoopReachableSet
        (policyFlowReachableAt consensusOptimalFlow {x} t₀)) s := by
      refine ⟨agreementPoint_mem_K x t₀ ht₀, ?_⟩
      rw [DX_potential_eq_on_X3 (agreementPoint_mem_X3 hx) s]
      exact Fg_agreement x
    have hle := Metric.infDist_le_dist_of_mem (x := consensusOptimalFlow.flow t₀ x s) hmem
    rw [one_mul, hpot s hs, ← Fg_flow]
    exact (pow_le_pow_left₀ Metric.infDist_nonneg hle 2).trans (dist_flow_agreement_sq_le x t₀ s)

/-! ## N の実 flow・到達集合を通した述べ方と、同じ V₀ の統一 -/

/-- N の `pointAdapter` の flow・到達集合は、任意の初期点・開始時刻で共有 flow・一点 K と一致する。 -/
theorem SharedDataPreservation.pointAdapter_is_consensus {N : SharedModelSignature}
    (h : SharedDataPreservation N) (x : AgentState) (t₀ : ℝ) :
    (N.pointAdapter x t₀).flow = consensusOptimalFlow ∧
      (N.pointAdapter x t₀).reachable = pointReachableClosure x t₀ := by
  have hF : (N.pointAdapter x t₀).flow = consensusOptimalFlow :=
    (h.point_flow x t₀).trans N.legacy.c1.selectedFlow_eq_rate3
  refine ⟨hF, ?_⟩
  rw [h.point_reachable, hF]
  rfl

/-- 定理1・2・4 を、同じ `commonV0X`・同じ共有 flow・同じ一点 K で、共通領域の上で述べた受入型。
定理1・4 は ℝ² 全体、定理2は `X3`（`θX=10`）。 -/
structure SharedDomainTheorems (N : SharedModelSignature) : Prop where
  /-- N の flow・到達集合は共有 flow・一点 K（全初期点）。 -/
  adapter : ∀ (x : AgentState) (t₀ : ℝ), (N.pointAdapter x t₀).flow = consensusOptimalFlow ∧
    (N.pointAdapter x t₀).reachable = pointReachableClosure x t₀
  /-- 評価：`DX.potential = commonV0X − 1`（`X3` の上）、`residual1 (commonV0X) 1 = commonV0X − 1`、
  `effX = 1 + F − exp(−F)`（`F = commonV0X − 1`）。 -/
  evaluation_X3 : ∀ x ∈ domainX3, ∀ t, DX.potential x t = commonV0X x - 1
  residual1_eq : ∀ y, residual1 (commonV0X y) 1 = commonV0X y - 1
  theorem1 : ∀ (x : AgentState) (t₀ : ℝ), 0 ≤ t₀ →
    (∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈ pointReachableClosure x t₀) ∧
    (∀ t, t₀ ≤ t → Metric.infDist (consensusOptimalFlow.flow t₀ x t) (point1TargetX x t₀) ≤
      Real.sqrt (Fg x) * Real.exp (-3 * (t - t₀))) ∧
    Tendsto (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t) (point1TargetX x t₀))
      atTop (𝓝 0)
  theorem2 : ∀ x ∈ domainX3, ∀ t₀ : ℝ, 0 ≤ t₀ →
    StatePairResidualSystem.ReachableStatePairConclusion DX
      (policyFlowReachableAt consensusOptimalFlow {x} t₀) (consensusOptimalFlow.flow t₀ x)
      DX_connected 3 1 t₀
  theorem4 : ∀ (x : AgentState) (t₀ : ℝ), 0 ≤ t₀ →
    (∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈ pointReachableClosure x t₀) ∧
    (∀ t, t₀ ≤ t → Metric.infDist (consensusOptimalFlow.flow t₀ x t) (point4TargetX x t₀) ≤
      Real.sqrt (effX x) * Real.exp (-(3 / 2 : ℝ) * (t - t₀))) ∧
    Tendsto (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t) (point4TargetX x t₀))
      atTop (𝓝 0)
  /-- 20 の拡張と 24 の有限層費用が、同じ `commonV0X` を全域で使う。 -/
  theorem20_same : N.theorem20BaseExtension = commonV0XE
  theorem24_same : ∀ (k : ℕ) (π : C1GainSignal) (x : AgentState) (t : ℝ),
    N.legacy.data.runningCost (some k) π x t = commonV0X x
  /-- 段の閉球は同じ領域 `X` に入る。 -/
  stage_balls : ∀ n, Metric.closedBall (N.stages n).center (N.stages n).radius ⊆ stageHull
  /-- 段の閉球は座標の上で `X3` に入る（定理2の領域と同じ）。 -/
  stage_balls_X3 : ∀ n, ∀ z ∈ Metric.closedBall (N.stages n).center (N.stages n).radius,
    c1EuclideanCoordinates z ∈ domainX3

theorem stageHull_subset_X3 {z : C1EuclideanAgentState} (hz : z ∈ stageHull) :
    c1EuclideanCoordinates z ∈ domainX3 := by
  intro i
  have hn : ‖z‖ ≤ 3 := by simpa [stageHull, Metric.mem_closedBall, dist_zero_right] using hz
  have hi := PiLp.norm_apply_le z i
  change |z i| ≤ 3
  simpa [Real.norm_eq_abs] using hi.trans hn

theorem sharedModel_domainTheorems : SharedDomainTheorems sharedModel where
  adapter := fun x t₀ => sharedModel_preservation.pointAdapter_is_consensus x t₀
  evaluation_X3 := fun x hx t => DX_potential_eq_on_X3 hx t
  residual1_eq := fun y => residual1_commonV0X y
  theorem1 := theorem1_commonDomainX
  theorem2 := fun x hx t₀ ht₀ => theorem2_commonDomainX hx t₀ ht₀
  theorem4 := theorem4_commonDomainX
  theorem20_same := sharedModel_commonDomainX.theorem20_global
  theorem24_same := sharedModel_finiteCost_eq_commonV0X
  stage_balls := fun n => stage_ball_subset_hull n
  stage_balls_X3 := fun n z hz => stageHull_subset_X3 (stage_ball_subset_hull n hz)

/-- v10：v9 に、定理1・2・4 を共通領域・共有評価で述べた受入型を加えた存在宣言。 -/
theorem final_consistency_v10 :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N ∧
        GenealogyMortalityExtension N ∧ Shared16OnePointInputs N ∧ SharedTheorem21V0 N ∧
        Shared25OnePointSelf N ∧ SharedTheorem21V0Common N ∧ MortalityOnN N ∧
        MortalityPresence25B ∧ Shared16CanonicalInputs N ∧ Shared25CanonicalSelf N ∧
        SharedSubjectIdentityCanonical N ∧ SharedCommonDomainX N ∧ SharedFixedCapacityInputs N ∧
        SharedDomainTheorems N :=
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
    sharedModel_subjectIdentityCanonical, sharedModel_commonDomainX,
    sharedModel_fixedCapacityInputs, sharedModel_domainTheorems⟩

#print axioms theorem1_commonDomainX
#print axioms theorem2_commonDomainX
#print axioms theorem4_commonDomainX
#print axioms sharedModel_domainTheorems
#print axioms final_consistency_v10

end Tomabechi.Consistency.R123
