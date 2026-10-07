import Tomabechi.Consistency.ConsistencyR123_Theorem3Domain

/-!
# 正典 TCZ を生成する制御系を署名に入れる

指摘：16 の `VelControl`（速度制御）と 24 の `C1GainSignal`（ゲイン制御）を同じ添字で暗黙に
使い分けていた。ここでは **層別の独立生成系を認める形式化**（案1）として、16 の層の TCZ 生成系を
専用の署名 `CognitiveControlSystem` に入れ、各 `(主体 d, 履歴 h, 層 i)` の表（`SharedModelSignature.layerControlTable`）で

| 項目 | 内容 |
|---|---|
| 状態型 | `ℝ`（認知座標） |
| 許容入力 | 可測で `\|u\| ≤ 1` の信号（`VelControl`） |
| `f(x,u,t)` | `u`（状態について 0-Lipschitz） |
| 解 | `x₀ + ∫_{t₀}^{t} u`（**全開始時刻** `t₀`、Carathéodory 解：AC・a.e. 微分） |
| 一意解 | AC かつ a.e. で `ẋ = u` かつ初期値 `x₀` なら解に一致 |
| 到達集合 | `ℛ(τ; x₀, t₀) = {解(τ)}` ＝ `[x₀−(τ−t₀), x₀+(τ−t₀)]`（全許容信号に量化） |
| 評価 | N.data の層 `index16 i` の実走行費の閾値集合 `Ω_θ`（`layerOmega`） |
| 正典 TCZ | `⋃_{τ≥t₀}[ℛ(τ;x₀,t₀) ∩ Ω_θ(τ)]`（閉包なし）＝ `ball16 h` |

を指定する。24 の制御系（`C1GainSignal`、`controlledConsensusState`）は**別の入力型・別の生成系**であり、
この表では 16 の層の系として使わない。共有するのは評価 Ω（N.data の層の実走行費）と、選択方策の
指定軌道（`core_step_is_selected_flow`）だけである。

**報告範囲：** これは「層別生成系を認める定式化での同時充足」であって、native の層制御から
正典 TCZ を構成したものではない。`nativeReach = velReach` を要求しない（同じ証人で中心の所属が異なる：
`core_step_misses_center` と `center_reached`）。強い共有モデルの認定には、速度とゲインを同じ制御族に
埋め込む別証人（案2）が必要で、本ファイルでは行わない。
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1 Tomabechi.Consistency.C2
open Tomabechi.Theorem16_25

/-! ## 全開始時刻の速度制御解 -/

/-- 開始時刻 `t₀`、初期値 `x` の解 `x + ∫_{t₀}^{t} u`。 -/
def velTrajAt (x t₀ : ℝ) (u : VelControl) (t : ℝ) : ℝ := x + ∫ s in t₀..t, u.1 s

theorem velTrajAt_start (x t₀ : ℝ) (u : VelControl) : velTrajAt x t₀ u t₀ = x := by
  simp [velTrajAt]

theorem velTrajAt_lipschitz (x t₀ : ℝ) (u : VelControl) : LipschitzWith 1 (velTrajAt x t₀ u) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [velTrajAt, NNReal.coe_one, one_mul, Real.dist_eq]
  have h : (x + ∫ r in t₀..s, u.1 r) - (x + ∫ r in t₀..t, u.1 r) = ∫ r in t..s, u.1 r := by
    rw [← intervalIntegral.integral_interval_sub_left (velControl_intervalIntegrable u t₀ s)
      (velControl_intervalIntegrable u t₀ t)]
    ring
  rw [h]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := s) (C := 1)
    (f := u.1) (fun r _ => by simpa using u.2.2 r)
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- 全区間で絶対連続。 -/
theorem velTrajAt_ac (x t₀ : ℝ) (u : VelControl) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (velTrajAt x t₀ u) a b :=
  (velTrajAt_lipschitz x t₀ u).lipschitzOnWith.absolutelyContinuousOnInterval

theorem velControl_locallyIntegrable (u : VelControl) : LocallyIntegrable u.1 volume := by
  intro p
  refine ⟨Set.Icc (p - 1) (p + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    (velControl_intervalIntegrable u (p - 1) (p + 1))

/-- Carathéodory 解：ほとんど至る所 `ẋ = u(t)`（Lebesgue の微分定理）。 -/
theorem velTrajAt_ae_hasDerivAt (x t₀ : ℝ) (u : VelControl) :
    ∀ᵐ t, HasDerivAt (velTrajAt x t₀ u) (u.1 t) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral (velControl_locallyIntegrable u)] with t ht
  exact (ht t₀).const_add x

/-- 一意性：AC で、ほとんど至る所 `ẏ = u`、初期値 `x` なら解に一致する。 -/
theorem velTrajAt_unique (x t₀ : ℝ) (u : VelControl) {y : ℝ → ℝ}
    (hy_ac : ∀ T, t₀ ≤ T → AbsolutelyContinuousOnInterval y t₀ T)
    (hy_deriv : ∀ T, t₀ ≤ T → ∀ᵐ t, t ∈ Set.Icc t₀ T → HasDerivAt y (u.1 t) t)
    (hy0 : y t₀ = x) : ∀ t, t₀ ≤ t → y t = velTrajAt x t₀ u t := by
  intro T hT
  have hg_ac : AbsolutelyContinuousOnInterval (fun s => y s - velTrajAt x t₀ u s) t₀ T :=
    (hy_ac T hT).sub (velTrajAt_ac x t₀ u t₀ T)
  have hg_deriv : ∀ᵐ s, s ∈ Set.uIcc t₀ T →
      HasDerivAt (fun s => y s - velTrajAt x t₀ u s) 0 s := by
    filter_upwards [hy_deriv T hT, velTrajAt_ae_hasDerivAt x t₀ u] with s h1 h2 hs
    rw [Set.uIcc_of_le hT] at hs
    have := (h1 hs).fun_sub h2
    simpa using this
  obtain ⟨C, hC⟩ := hg_ac.const_of_ae_hasDerivAt_zero hg_deriv
  have h0 := hC t₀ (Set.mem_uIcc.mpr (Or.inl ⟨le_rfl, hT⟩))
  have hT' := hC T (Set.mem_uIcc.mpr (Or.inl ⟨hT, le_rfl⟩))
  simp only [velTrajAt_start, hy0, sub_self] at h0
  have := hT'
  rw [← h0] at this
  linarith

/-- 全許容信号に量化した、時刻 `τ` の到達集合 `ℛ(τ; x, t₀)`。 -/
def velReachAt (x t₀ τ : ℝ) : Set ℝ := {y | ∃ u : VelControl, y = velTrajAt x t₀ u τ}

theorem velReachAt_eq {x t₀ τ : ℝ} (hτ : t₀ ≤ τ) :
    velReachAt x t₀ τ = Set.Icc (x - (τ - t₀)) (x + (τ - t₀)) := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₀) (b := τ) (C := 1)
      (f := u.1) (fun r _ => by simpa using u.2.2 r)
    have h1 : |∫ r in t₀..τ, u.1 r| ≤ τ - t₀ := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hτ)] using this
    have := abs_le.mp h1
    constructor <;> simp only [velTrajAt] <;> linarith [this.1, this.2]
  · intro hy
    by_cases h0 : τ = t₀
    · subst h0
      have : y = x := by simpa using hy
      exact ⟨⟨fun _ => 0, measurable_const, by simp⟩, by simp [velTrajAt, this]⟩
    · have hpos : 0 < τ - t₀ := sub_pos.mpr (lt_of_le_of_ne hτ (Ne.symm h0))
      refine ⟨⟨fun _ => (y - x) / (τ - t₀), measurable_const, fun _ => ?_⟩, ?_⟩
      · rw [abs_div, abs_of_pos hpos, div_le_one hpos]
        exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      · simp only [velTrajAt, intervalIntegral.integral_const, smul_eq_mul]
        field_simp
        ring

/-! ## 署名：認知座標の制御系 -/

/-- 認知座標 `ℝ` の制御系（状態 ℝ、入力 ℝ）：許容入力・`f(x,u,t)`・全開始時刻の解・ODE・一意性。 -/
structure CognitiveControlSystem where
  /-- 許容入力信号。 -/
  admissible : (ℝ → ℝ) → Prop
  /-- 方程式 `ẋ = f(x,u,t)`。 -/
  f : ℝ → ℝ → ℝ → ℝ
  /-- 開始時刻 `t₀`、初期値 `x` の解。 -/
  solution : ℝ → ℝ → (ℝ → ℝ) → ℝ → ℝ
  /-- `f` は状態についてリプシッツ。 -/
  state_lipschitz : ∃ L : NNReal, ∀ u t, LipschitzWith L (fun x => f x u t)
  solution_initial : ∀ x t₀ u, solution x t₀ u t₀ = x
  solution_ac : ∀ x t₀ u, admissible u → ∀ a b, AbsolutelyContinuousOnInterval (solution x t₀ u) a b
  solution_ode : ∀ x t₀ u, admissible u →
    ∀ᵐ t, HasDerivAt (solution x t₀ u) (f (solution x t₀ u t) (u t) t) t
  /-- 一意性：AC・a.e. で ODE・初期値を満たす関数は解に一致する（開始時刻以降）。 -/
  solution_unique : ∀ x t₀ u, admissible u → ∀ y : ℝ → ℝ,
    (∀ T, t₀ ≤ T → AbsolutelyContinuousOnInterval y t₀ T) →
    (∀ T, t₀ ≤ T → ∀ᵐ t, t ∈ Set.Icc t₀ T → HasDerivAt y (f (y t) (u t) t) t) →
    y t₀ = x → ∀ t, t₀ ≤ t → y t = solution x t₀ u t

/-- 全許容入力に量化した到達集合 `ℛ(τ; x, t₀)`。 -/
def CognitiveControlSystem.reach (S : CognitiveControlSystem) (x t₀ τ : ℝ) : Set ℝ :=
  {y | ∃ u, S.admissible u ∧ y = S.solution x t₀ u τ}

/-- 16 の層の TCZ 生成系：速度制御 `ẋ = u`、許容入力は可測で `|u| ≤ 1`、解は `x + ∫_{t₀}^{t} u`。 -/
def velocityControlSystem : CognitiveControlSystem where
  admissible := fun u => Measurable u ∧ ∀ t, |u t| ≤ 1
  f := fun _ u _ => u
  solution := fun x t₀ u t => x + ∫ s in t₀..t, u s
  state_lipschitz := ⟨0, fun u t => LipschitzWith.const u⟩
  solution_initial := fun x t₀ u => by simp
  solution_ac := fun x t₀ u hu a b => velTrajAt_ac x t₀ ⟨u, hu⟩ a b
  solution_ode := fun x t₀ u hu => velTrajAt_ae_hasDerivAt x t₀ ⟨u, hu⟩
  solution_unique := fun x t₀ u hu y hac hderiv hy0 =>
    velTrajAt_unique x t₀ ⟨u, hu⟩ hac hderiv hy0

theorem velocityControlSystem_reach_eq {x t₀ τ : ℝ} (hτ : t₀ ≤ τ) :
    velocityControlSystem.reach x t₀ τ = Set.Icc (x - (τ - t₀)) (x + (τ - t₀)) := by
  rw [← velReachAt_eq hτ]
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩
  · rintro ⟨u, rfl⟩; exact ⟨u.1, u.2, rfl⟩

/-! ## 署名の表：各 `(主体 d, 履歴 h, 層 i)` の制御系と正典 TCZ -/

/-- 各 `(d,h,i)` の制御系を指定する署名 field。 -/
structure LayerControlSignature where
  system : Bool → Bool → ℕ → CognitiveControlSystem

/-- 16 の層の系はすべての `(d,h,i)` で速度制御系。24 のゲイン制御系は使わない。 -/
def velocityLayerControlSignature : LayerControlSignature := ⟨fun _ _ _ => velocityControlSystem⟩

/-- 評価（N.data の層の実走行費）と、制御系から作る正典 TCZ `⋃_{τ≥t₀}[ℛ(τ;x,t₀) ∩ Ω_θ(τ)]`。 -/
def SharedModelSignature.canonicalTCZAt (N : SharedModelSignature) (S : CognitiveControlSystem)
    (h : Bool) (i : ℕ) (x t₀ : ℝ) : Set ℝ :=
  {y | ∃ τ : ℝ, t₀ ≤ τ ∧ y ∈ S.reach x t₀ τ ∧ y ∈ N.layerOmega h i τ}

/-- 正典 TCZ ＝ `ball16 h`（全初期点・全開始時刻、閉包なし）。 -/
theorem SharedModelSignature.canonicalTCZAt_velocity_eq {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) (h : Bool) (i : ℕ)
    (x t₀ : ℝ) : N.canonicalTCZAt velocityControlSystem h i x t₀ = ball16 h := by
  ext y
  constructor
  · rintro ⟨τ, _, _, hΩ⟩
    rwa [SharedModelSignature.layerOmega_eq hp hA] at hΩ
  · intro hy
    refine ⟨t₀ + |y - x|, by linarith [abs_nonneg (y - x)], ?_, ?_⟩
    · rw [velocityControlSystem_reach_eq (by linarith [abs_nonneg (y - x)])]
      constructor
      · simp only [add_sub_cancel_left]; linarith [neg_abs_le (y - x)]
      · simp only [add_sub_cancel_left]; linarith [le_abs_self (y - x)]
    · rwa [SharedModelSignature.layerOmega_eq hp hA]

/-- 一点 `x₀=1/2`・開始時刻 `0` の正典 TCZ は `canonicalLayerTCZ`と一致する。 -/
theorem SharedModelSignature.canonicalTCZAt_eq_canonicalLayerTCZ {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) (h : Bool) (i : ℕ) :
    N.canonicalTCZAt velocityControlSystem h i onePointStart 0 = N.canonicalLayerTCZ h i := by
  rw [SharedModelSignature.canonicalTCZAt_velocity_eq hp hA,
    SharedModelSignature.canonicalLayerTCZ_eq hp hA]

/-- 選択フィードバックの閉ループ軌道は、全開始時刻で許容入力による解。 -/
theorem selected_flow_admissible_at (h : Bool) {y : ℝ} (hy : y ∈ ball16 h) (t₀ : ℝ) :
    ∃ u : ℝ → ℝ, velocityControlSystem.admissible u ∧ ∀ t : ℝ, t₀ ≤ t →
      theorem16_intervalGradientFlow h y (t - t₀) = velocityControlSystem.solution y t₀ u t := by
  obtain ⟨U, hU⟩ := selected_flow_admissible h hy
  refine ⟨fun s => U.1 (s - t₀), ⟨U.2.1.comp (measurable_id.sub_const t₀),
    fun s => U.2.2 _⟩, fun t ht => ?_⟩
  have h1 := hU (t - t₀) (by linarith)
  show _ = y + ∫ s in t₀..t, U.1 (s - t₀)
  rw [intervalIntegral.integral_comp_sub_right (fun s => U.1 s) t₀, sub_self]
  rw [h1]
  rfl

/-- 署名の表の健全性：各 `(d,h,i)` で、制御系・評価・正典 TCZ・選択方策・24 の系との違いを同じ署名で。 -/
structure LayerControlSound (N : SharedModelSignature) (sig : LayerControlSignature) : Prop where
  /-- 表の内容：16 の層の系は速度制御系（24 のゲイン系ではない）。 -/
  system_is_velocity : ∀ d h i, sig.system d h i = velocityControlSystem
  /-- 正典 TCZ ＝ `ball16 h`（全初期点・全非負開始時刻）。 -/
  tcz_eq : ∀ d h i (x t₀ : ℝ), 0 ≤ t₀ →
    N.canonicalTCZAt (sig.system d h i) h i x t₀ = ball16 h
  tcz_matches_canonical : ∀ d h i,
    N.canonicalTCZAt (sig.system d h i) h i onePointStart 0 = N.canonicalLayerTCZ h i
  /-- 評価は N.data の層の実走行費の閾値集合。 -/
  evaluation_from_data : ∀ h i τ, N.layerOmega h i τ = ball16 h
  /-- 中心は有限時刻で許容入力により到達する。 -/
  center_reached : ∀ d h i (x t₀ : ℝ), ∃ τ : ℝ, t₀ ≤ τ ∧
    theorem16_intervalGradientCenter h ∈ (sig.system d h i).reach x t₀ τ
  /-- 24 の有界ゲイン力学（共有核）は中心に届かない：生成系が別である理由。 -/
  gain_core_misses_center : ∀ (h : Bool) (z : CompleteState) (A E : ℝ),
    cognitiveCoordinate z ≠ theorem16_intervalGradientCenter h →
    cognitiveCoordinate (N.legacy.step (N.legacy.historyCenter h) A E z) ≠
      theorem16_intervalGradientCenter h
  /-- 選択フィードバックの閉ループ軌道は許容入力による解（全開始時刻）で、共有核の認知座標の動きと一致。 -/
  selected_admissible : ∀ d h i (y : ℝ), y ∈ ball16 h → ∀ t₀ : ℝ, ∃ u,
    (sig.system d h i).admissible u ∧ ∀ t : ℝ, t₀ ≤ t →
      theorem16_intervalGradientFlow h y (t - t₀) = (sig.system d h i).solution y t₀ u t
  selected_is_core : ∀ (h : Bool) (z : CompleteState) (A E : ℝ),
    cognitiveCoordinate (N.legacy.step (N.legacy.historyCenter h) A E z) =
      theorem16_intervalGradientFlow h (cognitiveCoordinate z) A

theorem SharedModelSignature.layerControlSound {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) :
    LayerControlSound N velocityLayerControlSignature where
  system_is_velocity := fun _ _ _ => rfl
  tcz_eq := fun d h i x t₀ _ => SharedModelSignature.canonicalTCZAt_velocity_eq hp hA h i x t₀
  tcz_matches_canonical := fun d h i =>
    SharedModelSignature.canonicalTCZAt_eq_canonicalLayerTCZ hp hA h i
  evaluation_from_data := fun h i τ => SharedModelSignature.layerOmega_eq hp hA h i τ
  center_reached := fun d h i x t₀ => by
    refine ⟨t₀ + |theorem16_intervalGradientCenter h - x|,
      by linarith [abs_nonneg (theorem16_intervalGradientCenter h - x)], ?_⟩
    show _ ∈ velocityControlSystem.reach x t₀ _
    rw [velocityControlSystem_reach_eq (by linarith [abs_nonneg (theorem16_intervalGradientCenter h - x)])]
    constructor
    · simp only [add_sub_cancel_left]; linarith [neg_abs_le (theorem16_intervalGradientCenter h - x)]
    · simp only [add_sub_cancel_left]; linarith [le_abs_self (theorem16_intervalGradientCenter h - x)]
  gain_core_misses_center := fun h z A E hz =>
    SharedModelSignature.core_step_misses_center hA h z A E hz
  selected_admissible := fun d h i y hy t₀ => selected_flow_admissible_at h hy t₀
  selected_is_core := fun h z A E => SharedModelSignature.core_step_is_selected_flow hA h z A E

theorem sharedModel_layerControlSound : LayerControlSound sharedModel velocityLayerControlSignature :=
  SharedModelSignature.layerControlSound sharedModel_preservation
    sharedModel_explicitAdditionalConditions.legacy

/-- 層別生成系を認める定式化での同時充足：最終統合（v11）に、署名の表を加えた存在宣言。 -/
theorem final_consistency_with_layer_control :
    ∃ N : SharedModelSignature, ∃ sig : LayerControlSignature,
      SharedFinalConsistency N ∧ LayerControlSound N sig :=
  ⟨sharedModel, velocityLayerControlSignature, sharedModel_finalConsistency,
    sharedModel_layerControlSound⟩

#print axioms velTrajAt_unique
#print axioms velTrajAt_ae_hasDerivAt
#print axioms velocityControlSystem
#print axioms SharedModelSignature.canonicalTCZAt_velocity_eq
#print axioms sharedModel_layerControlSound
#print axioms final_consistency_with_layer_control

end Tomabechi.Consistency.R123
