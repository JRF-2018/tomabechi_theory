import Tomabechi.Consistency.ConsistencyR123_FullSelf

/-!
# 現行評価 `commonV0X` に対する原文前件

これまでの `SharedR3Inputs.theorem4_argmin` / `theorem20_argmin` と旧 `error1/2/3/4` は、旧 `N.base.V0`
（`1 + DA.potential`、箱 `|x_i| ≤ 1/4`）に結ばれていた。以前に結論側は `commonV0X = 1 + 2(x₀−x₁)²`
（ℝ² 全域）へ移したが、**原文の前件**（反復地平の費用最適性、補題0の「K の全点・全時刻」の誤差境界、
「任意の内部点・任意の非負開始時刻からの再始動」の絶対連続性・散逸）は現行評価について型に入っていなかった。

ここでは旧 `N.base.V0` を変更せず（`SharedCommonDomainX` の `base_ne_outside_box`：`x=![1,1]` で旧 14/5 ≠ 新 1 なので、
同一視は不可能）、現行評価について次を証明して `FullOriginalPremisesCurrent N` にまとめる。

* **有限地平 argmin**（定理1・4・20）：選択ゲイン（定数 3）が、`N` の実軌道・全競合可測ゲインに対して
  `∫ ofReal(V)` を最小化する。`V = commonV0X`／`effX`／`commonV0X − slope`。箱の仮定なし、ℝ² 全域。
* **補題0（K の全点・再始動）**（定理1・2・3・4）：K の**全点** `y` で `dist(y, TCZ)² ≤ C·Φ(y)`（`C=1`）、
  K は前向き不変、`Φ ≥ 0`、目標は非空。さらに K の**任意の点 y・任意の非負開始時刻 s** から出発した
  共有 flow に沿って `Φ` は絶対連続で、a.e. に `D⁺Φ ≤ −rate·Φ`（定理1・2・3 は rate 6、定理4 は rate 3）。
  再始動の目標は元の K 上の同じ目標集合（K を固定したまま）。

**範囲：** 定理1・4・20 は ℝ² 全域、定理2 は `X3`、定理3 は `X1` の零平均点（目標集合が非空になる
初期点は、このモデルでは零平均点に限る：`theorem3_target_nonempty_iff_zero_mean`）。
定理24 の割引無限地平の最適性とは区別した、有限地平の費用比較。誤差の距離は状態の sup 距離（`AgentState = Fin 2 → ℝ`）。
旧 `N.base` は補助 field のまま残り、ここでは現行評価の前件だけを述べる。
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Theorem1 Tomabechi.Theorem3 Tomabechi.Theorem2
open Tomabechi.Consistency.R2 Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1Theorem3Bridge
open Tomabechi.Examples.Theorem2

/-! ## 補助：半差の比較と線分 -/

theorem Fg_eq_two_D (y : AgentState) : Fg y = 2 * commonBaseD y := by
  rw [Fg_eq]; simp [commonBaseD]

/-- 最大ゲインの閉ループの半差の二乗は、任意の可測ゲインのそれ以下。 -/
theorem commonBaseD_maxGain_le (x : AgentState) (t₀ s : ℝ) (u : C1GainSignal) (hs : t₀ ≤ s) :
    commonBaseD (controlledConsensusState x t₀ c1MaxGainSignal s) ≤
      commonBaseD (controlledConsensusState x t₀ u s) := by
  have hsq := c1MaxGain_orbit_sq_le (halfDifference x) t₀ s u hs
  have hmax : c1ControlledOrbit (halfDifference x) t₀ c1MaxGainSignal s =
      halfDifference x * Real.exp (-(3 * (s - t₀))) := by
    simp [c1ControlledOrbit, c1MaxGain_accumulation]
  rw [commonBaseD_eq_halfDifference_sq, commonBaseD_eq_halfDifference_sq,
    controlledConsensusState_halfDifference, controlledConsensusState_halfDifference]
  have := mul_le_mul_of_nonneg_left (by rw [hmax]; exact hsq :
    (c1ControlledOrbit (halfDifference x) t₀ c1MaxGainSignal s) ^ 2 ≤
      (c1ControlledOrbit (halfDifference x) t₀ u s) ^ 2) (by norm_num : (0 : ℝ) ≤ 4)
  exact this

/-- 定理20の現行実効評価：`commonV0X − κ·slope`（κ=1、slope=−D）。 -/
def eff20X (y : AgentState) : ℝ := commonV0X y - commonBaseSlope y

theorem eff20X_eq (y : AgentState) : eff20X y = 1 + 3 * commonBaseD y := by
  simp only [eff20X, commonBaseSlope, commonV0X, commonBaseD]; ring

/-- 同じ N の実軌道（正有限層・可測ゲイン）で `V` を積分した有限地平費用。 -/
def SharedModelSignature.currentCost (N : SharedModelSignature) (V : AgentState → ℝ)
    (x : AgentState) (t₀ T : ℝ) (u : C1GainSignal) : ENNReal :=
  ∫⁻ s, ENNReal.ofReal (V (N.legacy.data.trajectory (some 1) u x t₀ s))
    ∂volume.restrict (Set.Icc t₀ (t₀ + T))

theorem SharedKernelInputs.currentCost_eq {N : SharedModelSignature} (h : SharedKernelInputs N)
    (V : AgentState → ℝ) (x : AgentState) (t₀ T : ℝ) (u : C1GainSignal) :
    N.currentCost V x t₀ T u =
      ∫⁻ s, ENNReal.ofReal (V (controlledConsensusState x t₀ u s))
        ∂volume.restrict (Set.Icc t₀ (t₀ + T)) := by
  unfold SharedModelSignature.currentCost
  apply lintegral_congr
  intro s
  rw [h.original.finite_control_solution]

/-- 残差が `D` の単調関数なら、最大ゲインが有限地平費用を最小化する（箱の仮定なし）。 -/
theorem SharedKernelInputs.currentArgmin_of_monotone {N : SharedModelSignature}
    (h : SharedKernelInputs N) (V : AgentState → ℝ)
    (hV : ∀ a b : AgentState, commonBaseD a ≤ commonBaseD b → V a ≤ V b)
    (x : AgentState) (t₀ T : ℝ) (u : C1GainSignal) :
    N.currentCost V x t₀ T N.legacy.c1.selectedGain ≤ N.currentCost V x t₀ T u := by
  rw [h.currentCost_eq, h.currentCost_eq, N.legacy.c1.selectedGain_eq_maximum]
  apply lintegral_mono_ae
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards with s hs
  exact ENNReal.ofReal_le_ofReal (hV _ _ (commonBaseD_maxGain_le x t₀ s u hs.1))

theorem commonV0X_mono_D {a b : AgentState} (h : commonBaseD a ≤ commonBaseD b) :
    commonV0X a ≤ commonV0X b := by
  have : Fg a ≤ Fg b := by rw [Fg_eq_two_D, Fg_eq_two_D]; linarith
  unfold Fg at this; linarith

theorem effX_mono_D {a b : AgentState} (h : commonBaseD a ≤ commonBaseD b) : effX a ≤ effX b := by
  have : Fg a ≤ Fg b := by rw [Fg_eq_two_D, Fg_eq_two_D]; linarith
  rw [effX_eq, effX_eq]; exact commonBaseTheorem4Effective_monotone this

theorem eff20X_mono_D {a b : AgentState} (h : commonBaseD a ≤ commonBaseD b) :
    eff20X a ≤ eff20X b := by
  rw [eff20X_eq, eff20X_eq]; linarith

/-- 線分上の点：平均は保存、座標は `mean ± h·r`。 -/
theorem agreementPoint_segmentPoint (x : AgentState) (r : ℝ) :
    agreementPoint (segmentPoint x r) = agreementPoint x := by
  simp [agreementPoint, meanState, segmentPoint]

theorem Fg_segmentPoint (x : AgentState) (r : ℝ) :
    Fg (segmentPoint x r) = 8 * (halfDifference x * r) ^ 2 := by
  rw [Fg_eq]; simp [segmentPoint, halfDifference]; ring

theorem dist_segmentPoint_agreement_sq_le (x : AgentState) (r : ℝ) :
    dist (segmentPoint x r) (agreementPoint x) ^ 2 ≤ Fg (segmentPoint x r) := by
  have hle : dist (segmentPoint x r) (agreementPoint x) ≤ |halfDifference x * r| := by
    refine (dist_pi_le_iff (abs_nonneg _)).2 ?_
    intro i
    fin_cases i
    · simp [segmentPoint, agreementPoint, Real.dist_eq]
    · simp [segmentPoint, agreementPoint, Real.dist_eq]
  have := pow_le_pow_left₀ dist_nonneg hle 2
  rw [sq_abs] at this
  rw [Fg_segmentPoint]
  nlinarith [sq_nonneg (halfDifference x * r)]

/-- K の点は線分上の点。 -/
theorem mem_K_segment {x : AgentState} {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {y : AgentState}
    (hy : y ∈ pointReachableClosure x t₀) : ∃ r ∈ Set.Icc (0 : ℝ) 1, y = segmentPoint x r := by
  rw [pointReachableClosure_eq_orbitSegment x t₀ ht₀] at hy
  rcases hy with ⟨r, hr, rfl⟩
  exact ⟨r, hr, rfl⟩

/-- 座標の大きさの一様な上界は線分上でも保たれる。 -/
theorem segmentPoint_bound {x : AgentState} {B : ℝ} (hx : ∀ i, |x i| ≤ B) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (i : Fin 2) : |segmentPoint x r i| ≤ B := by
  have h0 := abs_le.mp (hx 0)
  have h1 := abs_le.mp (hx 1)
  obtain ⟨hr0, hr1⟩ := hr
  fin_cases i
  · show |meanState x + halfDifference x * r| ≤ B
    simp only [meanState, halfDifference]
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hr0 (sub_nonneg.2 h0.2),
      mul_nonneg hr0 (sub_nonneg.2 h0.1), mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 h1.2),
      mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 h1.1)]
  · show |meanState x - halfDifference x * r| ≤ B
    simp only [meanState, halfDifference]
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hr0 (sub_nonneg.2 h1.2),
      mul_nonneg hr0 (sub_nonneg.2 h1.1), mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 h0.2),
      mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 h0.1)]

/-! ## 再始動の絶対連続性・散逸（率 6 の指数と、定理4の明示式） -/

theorem Fexp_restart (Ψ : ℝ → ℝ) (G s : ℝ) (heq : ∀ r, s ≤ r → Ψ r = G * Real.exp (-6 * (r - s)))
    (T : ℝ) (hT : s ≤ T) :
    AbsolutelyContinuousOnInterval Ψ s T ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc s T), deriv Ψ t ≤ -6 * Ψ t := by
  constructor
  · refine (Fexp_ac G s T).congr ?_
    intro r hr
    rw [Set.uIcc_of_le hT] at hr
    exact (heq r hr.1).symm
  · rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (measure_singleton s : volume ({s} : Set ℝ) = 0)] with t hne ht
    have hlt : s < t := lt_of_le_of_ne ht.1 (by simpa [eq_comm] using hne)
    have hnear : Ψ =ᶠ[𝓝 t] fun r => G * Real.exp (-6 * (r - s)) := by
      filter_upwards [Ioi_mem_nhds hlt] with u hu
      exact heq u hu.le
    rw [((hasDerivAt_Fexp G s t).congr_of_eventuallyEq hnear).deriv]
    exact le_of_eq (by rw [heq t ht.1])

theorem T4_restart (F s : ℝ) (hF : 0 ≤ F) (T : ℝ) :
    AbsolutelyContinuousOnInterval (sharedT4Explicit F s) s T ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc s T), deriv (sharedT4Explicit F s) t ≤
        -3 * sharedT4Explicit F s t := by
  constructor
  · have hcd : ContDiff ℝ 1 (sharedT4Explicit F s) := by
      unfold sharedT4Explicit; fun_prop
    exact hcd.contDiffOn.absolutelyContinuousOnInterval
  · rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun t _ => ?_)
    rw [(sharedT4Explicit_hasDerivAt F s t).deriv]
    have ha : 0 ≤ F * Real.exp (-6 * (t - s)) := mul_nonneg hF (Real.exp_pos _).le
    have hE := Real.exp_pos (-(F * Real.exp (-6 * (t - s))))
    have hb := Real.add_one_le_exp (-(F * Real.exp (-6 * (t - s))))
    unfold sharedT4Explicit
    nlinarith [mul_nonneg ha hE.le]

/-! ## 補題0（K の全点・任意の再始動）を型にする -/

local instance (i : Fin 2) : PseudoMetricSpace (c1Theorem3System.State i) := by
  change PseudoMetricSpace ℝ
  infer_instance

local instance : NormedAddCommGroup (∀ i, c1Theorem3System.State i) := by
  change NormedAddCommGroup AgentState
  infer_instance

local instance : NormedSpace ℝ (∀ i, c1Theorem3System.State i) := by
  change NormedSpace ℝ AgentState
  infer_instance

/-- 原文補題0の前件：定義域 `D` の初期点 `x`、全非負開始時刻 `t₀` について、
K（`pointReachableClosure`）が前向き不変・`Φ ≥ 0`・目標が非空、K の**全点**で `dist(y,TCZ)² ≤ 1·Φ(y)`、
K の**任意の点 `y`・任意の非負開始時刻 `s`** から出発した共有 flow に沿って `Φ` が絶対連続で
a.e. に `D⁺Φ ≤ −rate·Φ`。目標集合は元の K 上の同じ `Tgt x t₀`。 -/
structure RestartLemma0 (D : AgentState → Prop) (Φ : AgentState → ℝ → ℝ)
    (Tgt : AgentState → ℝ → ℝ → Set AgentState) (rate : ℝ) : Prop where
  forward_invariant : ∀ x, D x → ∀ t₀, 0 ≤ t₀ → ∀ y ∈ pointReachableClosure x t₀,
    ∀ s t, s ≤ t → consensusOptimalFlow.flow s y t ∈ pointReachableClosure x t₀
  nonneg : ∀ x, D x → ∀ t₀, 0 ≤ t₀ → ∀ y ∈ pointReachableClosure x t₀, ∀ t, 0 ≤ Φ y t
  target_nonempty : ∀ x, D x → ∀ t₀, 0 ≤ t₀ → ∀ t, (Tgt x t₀ t).Nonempty
  error_all_K : ∀ x, D x → ∀ t₀, 0 ≤ t₀ → ∀ y ∈ pointReachableClosure x t₀, ∀ t,
    Metric.infDist y (Tgt x t₀ t) ^ 2 ≤ 1 * Φ y t
  restart_ac : ∀ x, D x → ∀ t₀, 0 ≤ t₀ → ∀ y ∈ pointReachableClosure x t₀,
    ∀ s, 0 ≤ s → ∀ T, s ≤ T →
    AbsolutelyContinuousOnInterval (fun r => Φ (consensusOptimalFlow.flow s y r) r) s T
  restart_dissipation : ∀ x, D x → ∀ t₀, 0 ≤ t₀ → ∀ y ∈ pointReachableClosure x t₀,
    ∀ s, 0 ≤ s → ∀ T, s ≤ T →
    ∀ᵐ t ∂volume.restrict (Set.Icc s T),
      deriv (fun r => Φ (consensusOptimalFlow.flow s y r) r) t ≤
        -rate * Φ (consensusOptimalFlow.flow s y t) t

/-- 定理1の残差 `[V₀−1]₊`（`V₀ = commonV0X`）。 -/
def phi1X (y : AgentState) (_ : ℝ) : ℝ := residual1 (commonV0X y) 1

theorem phi1X_eq (y : AgentState) (t : ℝ) : phi1X y t = Fg y := residual1_commonV0X y

/-- 定理4の実効残差（`P=exp(−F)`、`Q=1`、`κ=1`、閾値 0）。 -/
def phi4X (y : AgentState) (_ : ℝ) : ℝ :=
  Tomabechi.Theorem4.residual4 (commonV0X y) (Real.exp (-(Fg y))) 1 1 0

theorem phi4X_eq (y : AgentState) (t : ℝ) : phi4X y t = effX y := residual4_X y

def target1X (x : AgentState) (t₀ _t : ℝ) : Set AgentState := point1TargetX x t₀
def target4X (x : AgentState) (t₀ _t : ℝ) : Set AgentState := point4TargetX x t₀
def target2X (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  DX.sharedTCZ (pointReachableClosure x t₀) t
def target3X (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  c1Theorem3System.stateTCZ (pointReachableClosure x t₀) DX.potential c1Theorem3Weight t

/-- 定理3の定義域：`X1` の零平均点。 -/
def domain3 (x : AgentState) : Prop := x ∈ domainX1 ∧ x 0 + x 1 = 0

theorem restartLemma0_theorem1 : RestartLemma0 (fun _ => True) phi1X target1X 6 where
  forward_invariant := fun x _ t₀ ht₀ y hy s t hst =>
    pointReachableClosure_forward_invariant x t₀ ht₀ hy hst
  nonneg := fun x _ t₀ ht₀ y _ t => by rw [phi1X_eq]; exact Fg_nonneg y
  target_nonempty := fun x _ t₀ ht₀ t => ⟨agreementPoint x, agreement_mem_target1 x t₀ ht₀⟩
  error_all_K := fun x _ t₀ ht₀ y hy t => by
    obtain ⟨r, hr, rfl⟩ := mem_K_segment ht₀ hy
    have hle := Metric.infDist_le_dist_of_mem (x := segmentPoint x r)
      (agreement_mem_target1 x t₀ ht₀)
    rw [phi1X_eq, one_mul]
    exact (pow_le_pow_left₀ Metric.infDist_nonneg hle 2).trans
      (dist_segmentPoint_agreement_sq_le x r)
  restart_ac := fun x _ t₀ ht₀ y hy s hs T hT =>
    (Fexp_restart (fun r => phi1X (consensusOptimalFlow.flow s y r) r) (Fg y) s
      (fun r _ => by rw [phi1X_eq, Fg_flow]) T hT).1
  restart_dissipation := fun x _ t₀ ht₀ y hy s hs T hT =>
    (Fexp_restart (fun r => phi1X (consensusOptimalFlow.flow s y r) r) (Fg y) s
      (fun r _ => by rw [phi1X_eq, Fg_flow]) T hT).2

theorem restartLemma0_theorem4 : RestartLemma0 (fun _ => True) phi4X target4X 3 where
  forward_invariant := fun x _ t₀ ht₀ y hy s t hst =>
    pointReachableClosure_forward_invariant x t₀ ht₀ hy hst
  nonneg := fun x _ t₀ ht₀ y _ t => by rw [phi4X_eq]; exact effX_nonneg y
  target_nonempty := fun x _ t₀ ht₀ t => ⟨agreementPoint x, agreement_mem_target4 x t₀ ht₀⟩
  error_all_K := fun x _ t₀ ht₀ y hy t => by
    obtain ⟨r, hr, rfl⟩ := mem_K_segment ht₀ hy
    have hle := Metric.infDist_le_dist_of_mem (x := segmentPoint x r)
      (agreement_mem_target4 x t₀ ht₀)
    rw [phi4X_eq, one_mul]
    exact (pow_le_pow_left₀ Metric.infDist_nonneg hle 2).trans
      ((dist_segmentPoint_agreement_sq_le x r).trans (effX_bounds _).1)
  restart_ac := fun x _ t₀ ht₀ y hy s hs T hT => by
    have hΨ : (fun r => phi4X (consensusOptimalFlow.flow s y r) r) =
        sharedT4Explicit (Fg y) s := funext fun r => by rw [phi4X_eq, effX_flow]
    rw [hΨ]; exact (T4_restart (Fg y) s (Fg_nonneg y) T).1
  restart_dissipation := fun x _ t₀ ht₀ y hy s hs T hT => by
    have hΨ : (fun r => phi4X (consensusOptimalFlow.flow s y r) r) =
        sharedT4Explicit (Fg y) s := funext fun r => by rw [phi4X_eq, effX_flow]
    filter_upwards [(T4_restart (Fg y) s (Fg_nonneg y) T).2] with t ht
    have e : phi4X (consensusOptimalFlow.flow s y t) t = sharedT4Explicit (Fg y) s t :=
      congrFun hΨ t
    rw [e, hΨ]; exact ht

theorem K_subset_X3 {x : AgentState} (hx : x ∈ domainX3) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {y : AgentState} (hy : y ∈ pointReachableClosure x t₀) : y ∈ domainX3 := by
  obtain ⟨r, hr, rfl⟩ := mem_K_segment ht₀ hy
  exact fun i => segmentPoint_bound hx hr i

theorem K_subset_X1 {x : AgentState} (hx : x ∈ domainX1) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {y : AgentState} (hy : y ∈ pointReachableClosure x t₀) : y ∈ domainX1 := by
  obtain ⟨r, hr, rfl⟩ := mem_K_segment ht₀ hy
  exact fun i => segmentPoint_bound hx hr i

theorem K_zero_mean {x : AgentState} (hmean : x 0 + x 1 = 0) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {y : AgentState} (hy : y ∈ pointReachableClosure x t₀) : y 0 + y 1 = 0 := by
  obtain ⟨r, hr, rfl⟩ := mem_K_segment ht₀ hy
  simp only [segmentPoint, meanState, halfDifference]
  simp
  linarith

theorem restartLemma0_theorem2 : RestartLemma0 (fun x => x ∈ domainX3) DX.potential target2X 6 where
  forward_invariant := fun x _ t₀ ht₀ y hy s t hst =>
    pointReachableClosure_forward_invariant x t₀ ht₀ hy hst
  nonneg := fun x hx t₀ ht₀ y hy t => by
    rw [DX_potential_eq_on_X3 (K_subset_X3 hx ht₀ hy)]
    have := Fg_nonneg y; unfold Fg at this; linarith
  target_nonempty := fun x hx t₀ ht₀ t => by
    refine ⟨agreementPoint x, agreementPoint_mem_K x t₀ ht₀, ?_⟩
    rw [DX_potential_eq_on_X3 (agreementPoint_mem_X3 hx) t]
    exact Fg_agreement x
  error_all_K := fun x hx t₀ ht₀ y hy t => by
    have hmem : agreementPoint x ∈ target2X x t₀ t := by
      refine ⟨agreementPoint_mem_K x t₀ ht₀, ?_⟩
      rw [DX_potential_eq_on_X3 (agreementPoint_mem_X3 hx) t]
      exact Fg_agreement x
    obtain ⟨r, hr, rfl⟩ := mem_K_segment ht₀ hy
    have hle := Metric.infDist_le_dist_of_mem (x := segmentPoint x r) hmem
    rw [one_mul, DX_potential_eq_on_X3 (K_subset_X3 hx ht₀ hy) t]
    exact (pow_le_pow_left₀ Metric.infDist_nonneg hle 2).trans
      (dist_segmentPoint_agreement_sq_le x r)
  restart_ac := fun x hx t₀ ht₀ y hy s hs T hT =>
    (Fexp_restart (fun r => DX.potential (consensusOptimalFlow.flow s y r) r) (Fg y) s
      (fun r hr => by
        rw [DX_potential_eq_on_X3 (flow_mem_X3 (K_subset_X3 hx ht₀ hy) s r hr)]
        exact Fg_flow y s r) T hT).1
  restart_dissipation := fun x hx t₀ ht₀ y hy s hs T hT =>
    (Fexp_restart (fun r => DX.potential (consensusOptimalFlow.flow s y r) r) (Fg y) s
      (fun r hr => by
        rw [DX_potential_eq_on_X3 (flow_mem_X3 (K_subset_X3 hx ht₀ hy) s r hr)]
        exact Fg_flow y s r) T hT).2

theorem restartLemma0_theorem3 : RestartLemma0 domain3 phi3X target3X 6 where
  forward_invariant := fun x _ t₀ ht₀ y hy s t hst =>
    pointReachableClosure_forward_invariant x t₀ ht₀ hy hst
  nonneg := fun x hx t₀ ht₀ y hy t => phi3X_nonneg (K_subset_X1 hx.1 ht₀ hy) t
  target_nonempty := fun x hx t₀ ht₀ t =>
    ⟨agreementPoint x, agreement_mem_theorem3Target hx.1 hx.2 t₀ ht₀ t⟩
  error_all_K := fun x hx t₀ ht₀ y hy t => by
    have hmem := agreement_mem_theorem3Target hx.1 hx.2 t₀ ht₀ t
    have hyX1 := K_subset_X1 hx.1 ht₀ hy
    obtain ⟨r, hr, rfl⟩ := mem_K_segment ht₀ hy
    have hle := Metric.infDist_le_dist_of_mem (x := segmentPoint x r) hmem
    have hsq := dist_segmentPoint_agreement_sq_le x r
    have hpe : Fg (segmentPoint x r) ≤ phi3X (segmentPoint x r) t := by
      rw [phi3X_eq hyX1, Fg_eq]
      nlinarith [sq_nonneg (segmentPoint x r 0), sq_nonneg (segmentPoint x r 1)]
    rw [one_mul]
    exact (pow_le_pow_left₀ Metric.infDist_nonneg hle 2).trans (hsq.trans hpe)
  restart_ac := fun x hx t₀ ht₀ y hy s hs T hT =>
    (Fexp_restart (fun r => phi3X (consensusOptimalFlow.flow s y r) r)
      (2 * (y 0 - y 1) ^ 2 + (1 / 2 : ℝ) * (y 0 ^ 2 + y 1 ^ 2)) s
      (fun r hr => phi3X_flow (K_subset_X1 hx.1 ht₀ hy) (K_zero_mean hx.2 ht₀ hy) s r hr r)
      T hT).1
  restart_dissipation := fun x hx t₀ ht₀ y hy s hs T hT =>
    (Fexp_restart (fun r => phi3X (consensusOptimalFlow.flow s y r) r)
      (2 * (y 0 - y 1) ^ 2 + (1 / 2 : ℝ) * (y 0 ^ 2 + y 1 ^ 2)) s
      (fun r hr => phi3X_flow (K_subset_X1 hx.1 ht₀ hy) (K_zero_mean hx.2 ht₀ hy) s r hr r)
      T hT).2

/-- 定理3の目標集合が非空になる `X1` の初期点は、ちょうど零平均点（このモデルでの帰結で、
原文の仮定ではない）。 -/
theorem theorem3_target_nonempty_iff_zero_mean {x : AgentState} (hx : x ∈ domainX1) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) (t : ℝ) : (target3X x t₀ t).Nonempty ↔ x 0 + x 1 = 0 := by
  constructor
  · rintro ⟨y, hyK, hy0⟩
    have hyX1 := K_subset_X1 hx ht₀ hyK
    have hy0' : phi3X y t = 0 := hy0
    rw [phi3X_eq hyX1] at hy0'
    have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0 - y 1), sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0 - y 1), sq_nonneg (y 0), sq_nonneg (y 1)]
    obtain ⟨r, hr, rfl⟩ := mem_K_segment ht₀ hyK
    have hm : meanState (segmentPoint x r) = meanState x := by
      simp [meanState, segmentPoint]
    simp only [meanState] at hm
    linarith
  · intro hmean
    exact ⟨agreementPoint x, agreement_mem_theorem3Target hx hmean t₀ ht₀ t⟩

/-! ## 現行評価の原文前件の受入型 -/

/-- 現行評価 `commonV0X` について、原文の前件（有限地平 argmin、補題0の K 全点・再始動）を
同じ `N` で述べた受入型。旧 `N.base` は補助 field のままで、ここでは使わない。 -/
structure FullOriginalPremisesCurrent (N : SharedModelSignature) : Prop where
  /-- N の flow・到達集合は共有 flow・一点 K（全初期点）。 -/
  adapter : ∀ (x : AgentState) (t₀ : ℝ), (N.pointAdapter x t₀).flow = consensusOptimalFlow ∧
    (N.pointAdapter x t₀).reachable = pointReachableClosure x t₀
  selected_gain : N.legacy.c1.selectedGain = c1MaxGainSignal
  v0_nonneg : ∀ y, 0 ≤ commonV0X y
  v0_is_layer_cost : ∀ (k : ℕ) (π : C1GainSignal) (y : AgentState) (t : ℝ),
    N.legacy.data.runningCost (some k) π y t = commonV0X y
  argmin1 : ∀ x t₀ T (u : C1GainSignal),
    N.currentCost commonV0X x t₀ T N.legacy.c1.selectedGain ≤ N.currentCost commonV0X x t₀ T u
  argmin4 : ∀ x t₀ T (u : C1GainSignal),
    N.currentCost effX x t₀ T N.legacy.c1.selectedGain ≤ N.currentCost effX x t₀ T u
  argmin20 : ∀ x t₀ T (u : C1GainSignal),
    N.currentCost eff20X x t₀ T N.legacy.c1.selectedGain ≤ N.currentCost eff20X x t₀ T u
  lemma0_theorem1 : RestartLemma0 (fun _ => True) phi1X target1X 6
  lemma0_theorem2 : RestartLemma0 (fun x => x ∈ domainX3) DX.potential target2X 6
  lemma0_theorem3 : RestartLemma0 domain3 phi3X target3X 6
  lemma0_theorem4 : RestartLemma0 (fun _ => True) phi4X target4X 3
  theorem3_target_nonempty : ∀ x ∈ domainX1, ∀ t₀, 0 ≤ t₀ → ∀ t,
    ((target3X x t₀ t).Nonempty ↔ x 0 + x 1 = 0)

theorem sharedModel_fullOriginalPremisesCurrent : FullOriginalPremisesCurrent sharedModel where
  adapter := fun x t₀ => sharedModel_preservation.pointAdapter_is_consensus x t₀
  selected_gain := sharedModel.legacy.c1.selectedGain_eq_maximum
  v0_nonneg := fun y => (commonV0X_ge_one y).trans' (by norm_num)
  v0_is_layer_cost := sharedModel_finiteCost_eq_commonV0X
  argmin1 := fun x t₀ T u => sharedModel_kernelInputs.currentArgmin_of_monotone commonV0X
    (fun _ _ h => commonV0X_mono_D h) x t₀ T u
  argmin4 := fun x t₀ T u => sharedModel_kernelInputs.currentArgmin_of_monotone effX
    (fun _ _ h => effX_mono_D h) x t₀ T u
  argmin20 := fun x t₀ T u => sharedModel_kernelInputs.currentArgmin_of_monotone eff20X
    (fun _ _ h => eff20X_mono_D h) x t₀ T u
  lemma0_theorem1 := restartLemma0_theorem1
  lemma0_theorem2 := restartLemma0_theorem2
  lemma0_theorem3 := restartLemma0_theorem3
  lemma0_theorem4 := restartLemma0_theorem4
  theorem3_target_nonempty := fun x hx t₀ ht₀ t => theorem3_target_nonempty_iff_zero_mean hx ht₀ t

/-- 現行評価の原文前件を、最終整合（v11 の `SharedFinalConsistency`・層制御系・担体全体の自己過程）と同じ `N` で。 -/
theorem final_consistency_with_current_premises :
    ∃ N sig, SharedFinalConsistency N ∧ LayerControlSound N sig ∧ Shared25FullSelf N ∧
      FullOriginalPremisesCurrent N :=
  ⟨sharedModel, velocityLayerControlSignature, sharedModel_finalConsistency,
    sharedModel_layerControlSound, sharedModel_shared25FullSelf,
    sharedModel_fullOriginalPremisesCurrent⟩

#print axioms restartLemma0_theorem1
#print axioms restartLemma0_theorem2
#print axioms restartLemma0_theorem3
#print axioms restartLemma0_theorem4
#print axioms theorem3_target_nonempty_iff_zero_mean
#print axioms sharedModel_fullOriginalPremisesCurrent
#print axioms final_consistency_with_current_premises

end Tomabechi.Consistency.R123
