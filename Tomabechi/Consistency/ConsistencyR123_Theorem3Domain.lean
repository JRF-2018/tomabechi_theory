import Tomabechi.Consistency.ConsistencyR123_FinalGate

/-!
# 定理3の `Φ₂` を `DX` に揃える（共通領域上の定理3）

これまで定理3の入口（`SharedTheorem3PointInputs`、`c1Theorem3StatePhi3`）は、定理2の共有残差として
`DA`（個人閾値 `θ = 1/10`、箱 `|x_i| ≤ 1/4`）を使っていた。以前に定理2を `DX`（`θX = 10`）へ移したので、
同じ `Φ₂` の記号が定理2と定理3で別の読みになっていた（箱の上でだけ一致）。ここで定理3の
`Φ₃ = Φ₂ + Σ η_i 𝒜_i` の `Φ₂` を **定理2と同じ `DX.potential`** に取り替える。

* 領域：`domainX1 := {x | ∀ i, |x i| ≤ 1}`（`⊂ X3`）。定理3の抽象化 `c1Theorem3System` は各座標の大きさを
  `min(|x|,1)` に切り取る（`unitInterval` へ入れるため）ので、`|x_i| ≤ 1` で切り取りが効かず
  `𝒜_i = x_i²` となる。旧版の箱 `|x_i| ≤ 1/4` より広い。
* 零平均の初期点で（平均が保存されるので、非零平均では `Ω₃ ∩ K₃ = ∅` で原文の仮定「Ω₃ が非空」が成り立たない）、
  全非負開始時刻で、定理3の状態付き一般入口を `DX.potential` について適用する。
* 共有 flow が零平均では原点への縮小 `flow_i = x_i·e^{−3(t−t₀)}` であることから、`Φ₃ = G(x)e^{−6(t−t₀)}`、
  `G(x) = 2(x₀−x₁)² + ½(x₀²+x₁²)`。

**範囲：** `|x_i| ≤ 1` の零平均点。`|x_i| > 1` では抽象化が飽和して `Φ₃` の散逸条件が成り立たない
（`c1Theorem3System` の切り取りの選択による）。箱の上では旧 `DA` 版と一致する（`phi3_eq_on_box`）。
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Theorem1 Tomabechi.Theorem3 Tomabechi.Theorem2
open Tomabechi.Consistency.R2
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1Theorem3Bridge
open Tomabechi.Examples.Theorem2

local instance (i : Fin 2) : PseudoMetricSpace (c1Theorem3System.State i) := by
  change PseudoMetricSpace ℝ
  infer_instance

/-- 領域 `X1`：各座標の絶対値 ≤ 1（定理3の抽象化の切り取りが効かない範囲）。 -/
def domainX1 : Set AgentState := {x | ∀ i, |x i| ≤ 1}

theorem domainX1_subset_X3 {x : AgentState} (hx : x ∈ domainX1) : x ∈ domainX3 :=
  fun i => (hx i).trans (by norm_num)

/-- 定理3の抽象残差は `|z_i| ≤ 1` で `z_i²`（旧版は箱 `|z_i| ≤ 1/4` で証明していた）。 -/
theorem c1Theorem3System_abstraction_residual_X1 (i : Fin 2) (z : AgentState)
    (hz : z ∈ domainX1) : c1Theorem3System.abstractResidual i (z i) = z i ^ 2 := by
  have hiOne : |z i| ≤ 1 := hz i
  have habs : clippedMagnitude (z i) = ⟨|z i|, ⟨abs_nonneg _, hiOne⟩⟩ := by
    apply Subtype.ext
    simp [clippedMagnitude, min_eq_left hiOne]
  change euclideanCoordinateNorm
      (c1Theorem3System.ι (c1Theorem3System.abstraction i (z i)) -
        c1Theorem3System.ι c1Theorem3System.lub) ^ 2 = z i ^ 2
  rw [c1Theorem3System_lub]
  fin_cases i
  · have hlocal : clippedMagnitude (z 0) = ⟨|z 0|, ⟨abs_nonneg _, hz 0⟩⟩ := by simpa using habs
    simp [c1Theorem3System, hlocal, euclideanCoordinateNorm, Fin.sum_univ_two, sq_abs]
    rw [Real.sq_sqrt (sq_nonneg (z 0))]
  · have hlocal : clippedMagnitude (z 1) = ⟨|z 1|, ⟨abs_nonneg _, hz 1⟩⟩ := by simpa using habs
    simp [c1Theorem3System, hlocal, euclideanCoordinateNorm, Fin.sum_univ_two, sq_abs]
    rw [Real.sq_sqrt (sq_nonneg (z 1))]

/-- `DX` に揃えた状態上の `Φ₃`。 -/
def phi3X (z : AgentState) (t : ℝ) : ℝ :=
  c1Theorem3System.statePotential DX.potential c1Theorem3Weight z t

/-- `X1` の上の明示式 `Φ₃ = 2(z₀−z₁)² + ½(z₀²+z₁²)`。 -/
theorem phi3X_eq {z : AgentState} (hz : z ∈ domainX1) (t : ℝ) :
    phi3X z t = 2 * (z 0 - z 1) ^ 2 + (1 / 2 : ℝ) * (z 0 ^ 2 + z 1 ^ 2) := by
  unfold phi3X AbstractSharedSystem.statePotential
  rw [Fin.sum_univ_two, DX_potential_eq_on_X3 (domainX1_subset_X3 hz) t,
    c1Theorem3System_abstraction_residual_X1 0 z hz, c1Theorem3System_abstraction_residual_X1 1 z hz]
  norm_num [c1Theorem3Weight, commonV0X]
  ring

/-- 箱の上で、旧 `DA` 版の `Φ₃` と一致する。 -/
theorem phi3X_eq_old_on_box {z : AgentState} (hz : z ∈ box) (t : ℝ) :
    phi3X z t = c1Theorem3StatePhi3 z t := by
  rw [c1Theorem3StatePhi3_eq_on_box z hz t,
    phi3X_eq (fun i => (hz i).trans (by norm_num)) t]

/-- 零平均の共有 flow は原点への縮小。 -/
theorem flow_zero_mean {x : AgentState} (hmean : x 0 + x 1 = 0) (t₀ s : ℝ) (i : Fin 2) :
    consensusOptimalFlow.flow t₀ x s i = x i * Real.exp (-3 * (s - t₀)) := by
  have hm : meanState x = 0 := by simp only [meanState]; linarith
  have hh : halfDifference x = x 0 := by simp only [halfDifference]; linarith
  fin_cases i
  · change meanState x + halfDifference x * Real.exp (-3 * (s - t₀)) = _
    rw [hm, hh]; simp
  · show meanState x - halfDifference x * Real.exp (-3 * (s - t₀)) = x 1 * Real.exp (-3 * (s - t₀))
    have : x 1 = -x 0 := by linarith
    rw [hm, hh, this]; ring

theorem flow_mem_X1 {x : AgentState} (hx : x ∈ domainX1) (hmean : x 0 + x 1 = 0)
    (t₀ t : ℝ) (ht : t₀ ≤ t) : consensusOptimalFlow.flow t₀ x t ∈ domainX1 := by
  have hq0 : 0 < Real.exp (-3 * (t - t₀)) := Real.exp_pos _
  have hq1 : Real.exp (-3 * (t - t₀)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
  intro i
  rw [flow_zero_mean hmean, abs_mul, abs_of_pos hq0]
  nlinarith [hx i, abs_nonneg (x i)]

/-- 零平均・`X1` の点では、共有 flow に沿って `Φ₃ = G(x)e^{−6(t−t₀)}`。 -/
theorem phi3X_flow {x : AgentState} (hx : x ∈ domainX1) (hmean : x 0 + x 1 = 0)
    (t₀ s : ℝ) (hs : t₀ ≤ s) (t : ℝ) :
    phi3X (consensusOptimalFlow.flow t₀ x s) t =
      (2 * (x 0 - x 1) ^ 2 + (1 / 2 : ℝ) * (x 0 ^ 2 + x 1 ^ 2)) * Real.exp (-6 * (s - t₀)) := by
  rw [phi3X_eq (flow_mem_X1 hx hmean t₀ s hs), flow_zero_mean hmean, flow_zero_mean hmean]
  have : Real.exp (-3 * (s - t₀)) ^ 2 = Real.exp (-6 * (s - t₀)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [← this]; ring

theorem phi3X_nonneg {z : AgentState} (hz : z ∈ domainX1) (t : ℝ) : 0 ≤ phi3X z t := by
  rw [phi3X_eq hz]; positivity

local instance : NormedAddCommGroup (∀ i, c1Theorem3System.State i) := by
  change NormedAddCommGroup AgentState
  infer_instance

local instance : NormedSpace ℝ (∀ i, c1Theorem3System.State i) := by
  change NormedSpace ℝ AgentState
  infer_instance

/-- 共有 flow の `X1` 上の零平均点での定理3の結論（`DX` の `Φ₃`）。 -/
structure Theorem3ConclusionX (x : AgentState) (t₀ : ℝ) : Prop where
  reachable : ∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈ pointReachableClosure x t₀
  state_bound : ∀ t, t₀ ≤ t →
    Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (c1Theorem3System.stateTCZ (pointReachableClosure x t₀) DX.potential c1Theorem3Weight t) ≤
    Real.sqrt (phi3X x t₀) * Real.exp (-3 * (t - t₀))
  agent_bound : ∀ i t, t₀ ≤ t →
    euclideanCoordinateNorm (c1Theorem3System.ι (c1Theorem3System.abstraction i
      (consensusOptimalFlow.flow t₀ x t i)) - c1Theorem3System.ι c1Theorem3System.lub) ≤
    Real.sqrt (phi3X x t₀ / c1Theorem3Weight i) * Real.exp (-3 * (t - t₀))
  state_limit : Tendsto (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t)
    (c1Theorem3System.stateTCZ (pointReachableClosure x t₀) DX.potential c1Theorem3Weight t))
    atTop (𝓝 0)
  agent_limit : ∀ i, Tendsto (fun t => euclideanCoordinateNorm
    (c1Theorem3System.ι (c1Theorem3System.abstraction i
      (consensusOptimalFlow.flow t₀ x t i)) - c1Theorem3System.ι c1Theorem3System.lub))
    atTop (𝓝 0)

theorem agreement_mem_theorem3Target {x : AgentState} (hx : x ∈ domainX1) (hmean : x 0 + x 1 = 0)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (t : ℝ) :
    agreementPoint x ∈ c1Theorem3System.stateTCZ (pointReachableClosure x t₀) DX.potential
      c1Theorem3Weight t := by
  have hm : meanState x = 0 := by simp only [meanState]; linarith
  have hag : agreementPoint x ∈ domainX1 := by
    intro i; fin_cases i <;> (simp only [agreementPoint]; show |meanState x| ≤ 1; rw [hm]; simp)
  refine ⟨agreementPoint_mem_K x t₀ ht₀, ?_⟩
  show phi3X (agreementPoint x) t = 0
  rw [phi3X_eq hag]
  simp [agreementPoint, hm]

/-- 定理3（`DX` の `Φ₃`、`X1` の零平均の全初期点・全非負開始時刻）。 -/
theorem theorem3_commonDomainX {x : AgentState} (hx : x ∈ domainX1) (hmean : x 0 + x 1 = 0)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) : Theorem3ConclusionX x t₀ := by
  set G : ℝ := 2 * (x 0 - x 1) ^ 2 + (1 / 2 : ℝ) * (x 0 ^ 2 + x 1 ^ 2) with hG
  have hGnn : 0 ≤ G := by rw [hG]; positivity
  have hpot : ∀ s, t₀ ≤ s → c1Theorem3System.statePotential DX.potential c1Theorem3Weight
      (fun j => consensusOptimalFlow.flow t₀ x s j) s = G * Real.exp (-6 * (s - t₀)) := by
    intro s hs
    exact phi3X_flow hx hmean t₀ s hs s
  have hcore := fun i : Fin 2 => c1Theorem3System.theorem3_reachable_state_tcz_quantitative_conclusion
    (show ℝ → Set AgentState from policyFlowReachableAt consensusOptimalFlow {x} t₀)
    (fun j t => consensusOptimalFlow.flow t₀ x t j)
    DX.potential c1Theorem3Weight i 3 1 t₀
    (by norm_num [c1Theorem3Weight]) (by norm_num) (by norm_num) ht₀
    (fun t ht => mem_policyFlowReachableAt_of_flow consensusOptimalFlow {x}
      t₀ t x (Set.mem_singleton _) ht)
    (fun s hs => by
      rw [DX_potential_eq_on_X3 (domainX1_subset_X3 (flow_mem_X1 hx hmean t₀ s hs))]
      have := Fg_nonneg (consensusOptimalFlow.flow t₀ x s); unfold Fg at this; linarith)
    (fun t ht j => mul_nonneg (by norm_num [c1Theorem3Weight])
      (AbstractSharedSystem.abstractResidual_nonneg c1Theorem3System j _))
    (fun s hs => ⟨agreementPoint x, agreement_mem_theorem3Target hx hmean t₀ ht₀ s⟩)
    (fun T hT => by
      refine (Fexp_ac G t₀ T).congr ?_
      intro s hs
      rw [Set.uIcc_of_le hT] at hs
      exact (hpot s hs.1).symm)
    (fun T hT => by
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (measure_singleton t₀ : volume ({t₀} : Set ℝ) = 0)] with t hne ht
      have hlt : t₀ < t := lt_of_le_of_ne ht.1 (by simpa [eq_comm] using hne)
      have hnear : (fun r => c1Theorem3System.statePotential DX.potential c1Theorem3Weight
          (fun j => consensusOptimalFlow.flow t₀ x r j) r) =ᶠ[𝓝 t]
          fun r => G * Real.exp (-6 * (r - t₀)) := by
        filter_upwards [Ioi_mem_nhds hlt] with u hu
        exact hpot u hu.le
      rw [((hasDerivAt_Fexp G t₀ t).congr_of_eventuallyEq hnear).deriv, hpot t ht.1]
      nlinarith)
    (fun s hs => by
      have hmem := agreement_mem_theorem3Target hx hmean t₀ ht₀ s
      have hle := Metric.infDist_le_dist_of_mem
        (x := (fun j => consensusOptimalFlow.flow t₀ x s j)) hmem
      rw [one_mul]
      have hsq := dist_flow_agreement_sq_le x t₀ s
      have hpe : Fg (consensusOptimalFlow.flow t₀ x s) ≤
          c1Theorem3System.statePotential DX.potential c1Theorem3Weight
            (fun j => consensusOptimalFlow.flow t₀ x s j) s := by
        have hflow := flow_mem_X1 hx hmean t₀ s hs
        show Fg _ ≤ phi3X (consensusOptimalFlow.flow t₀ x s) s
        rw [phi3X_eq hflow, Fg_eq]
        nlinarith [sq_nonneg (consensusOptimalFlow.flow t₀ x s 0),
          sq_nonneg (consensusOptimalFlow.flow t₀ x s 1)]
      exact (pow_le_pow_left₀ Metric.infDist_nonneg hle 2).trans (hsq.trans hpe))
  have hat₀ : phi3X x t₀ = G := by rw [phi3X_eq hx]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; exact (hcore 0).1 t ht
  · intro t ht
    have h0 := ((hcore 0).2.1 t ht).1
    have hx0 : (fun j => consensusOptimalFlow.flow t₀ x t₀ j) = x := by
      funext j; rw [consensusOptimalFlow.initial]
    rw [one_mul, hx0] at h0
    exact h0
  · intro i t ht
    have h0 := ((hcore i).2.1 t ht).2
    have hx0 : (fun j => consensusOptimalFlow.flow t₀ x t₀ j) = x := by
      funext j; rw [consensusOptimalFlow.initial]
    rw [hx0] at h0
    exact h0
  · exact (hcore 0).2.2.1
  · intro i; exact (hcore i).2.2.2

/-- 定理3を、定理2と同じ `DX` の `Φ₂` で、共通領域の上（`X1` の零平均点）で述べた受入型。 -/
structure SharedDomainTheorem3 (N : SharedModelSignature) : Prop where
  /-- `Φ₃` の `Φ₂` は定理2と同じ `DX.potential`。`X1` の上で明示式、箱の上で旧 `DA` 版と一致。 -/
  phi3_explicit : ∀ z ∈ domainX1, ∀ t, phi3X z t =
    2 * (z 0 - z 1) ^ 2 + (1 / 2 : ℝ) * (z 0 ^ 2 + z 1 ^ 2)
  phi3_old_on_box : ∀ z ∈ box, ∀ t, phi3X z t = c1Theorem3StatePhi3 z t
  shared_residual_same_as_theorem2 : ∀ z ∈ domainX1, ∀ t, DX.potential z t = commonV0X z - 1
  /-- N の flow・到達集合は共有 flow・一点 K。 -/
  adapter : ∀ (x : AgentState) (t₀ : ℝ), (N.pointAdapter x t₀).flow = consensusOptimalFlow ∧
    (N.pointAdapter x t₀).reachable = pointReachableClosure x t₀
  /-- 定理3の結論（`X1` の零平均の全初期点・全非負開始時刻）。 -/
  theorem3 : ∀ x ∈ domainX1, x 0 + x 1 = 0 → ∀ t₀ : ℝ, 0 ≤ t₀ → Theorem3ConclusionX x t₀
  /-- 前提を満たす非自明な初期点がある（箱の外を含む）。 -/
  nontrivial_initial : ∃ x ∈ domainX1, x 0 + x 1 = 0 ∧ x ≠ 0 ∧ x ∉ box

theorem sharedModel_domainTheorem3 : SharedDomainTheorem3 sharedModel where
  phi3_explicit := fun z hz t => phi3X_eq hz t
  phi3_old_on_box := fun z hz t => phi3X_eq_old_on_box hz t
  shared_residual_same_as_theorem2 := fun z hz t => DX_potential_eq_on_X3 (domainX1_subset_X3 hz) t
  adapter := fun x t₀ => sharedModel_preservation.pointAdapter_is_consensus x t₀
  theorem3 := fun x hx hmean t₀ ht₀ => theorem3_commonDomainX hx hmean t₀ ht₀
  nontrivial_initial := by
    refine ⟨![1, -1], ?_, by simp, ?_, ?_⟩
    · intro i; fin_cases i <;> simp
    · intro h
      have := congrFun h 0
      simp at this
    · intro h
      have := h 0
      simp at this
      norm_num at this

/-- v12：v11 の統合に、`Φ₂ = DX` に揃えた定理3を加える。 -/
theorem final_consistency_v12 :
    ∃ N : SharedModelSignature, SharedFinalConsistency N ∧ SharedDomainTheorem3 N :=
  ⟨sharedModel, sharedModel_finalConsistency, sharedModel_domainTheorem3⟩

#print axioms theorem3_commonDomainX
#print axioms sharedModel_domainTheorem3
#print axioms final_consistency_v12

end Tomabechi.Consistency.R123
