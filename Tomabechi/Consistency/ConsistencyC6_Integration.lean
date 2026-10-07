import Tomabechi.Consistency.ConsistencyC2_EntropyBalance
import Tomabechi.Consistency.ConsistencyC3_StagePresentation
import Tomabechi.Consistency.ConsistencyC4_Theorem16_25
import Tomabechi.Consistency.ConsistencyC5_Theorem24_27
import Tomabechi.Consistency.ConsistencyC1_CommonModel

/-!
# C6: 共通層束とC1–C5の部分保存接続

共通候補束 `WithTop ℕ` 上でC2/C3の正層添字・平均場中心、C4/C5の
二値履歴・上下層を対応させる。また、C1の選択flowをC2完全状態経由で
C5の上位最適軌道へ写し、C1–C2–C5間の軌道保存を証明する。C2任意完全状態から
C5へのflow・走行費・最適値の保存も示す。

これらはS0/S1/S2/S3/S4/S6の部分接続に加え、C4の履歴SCM出力とC5のBool層ラベルを
同一視する接続を含む。C1を含む全対象へのadapter、共通履歴法則・評価体系、
および全非退化条件の同時証人はまだ含まない。
-/

namespace Tomabechi.Consistency.C6

open Tomabechi.Consistency.C2
open Tomabechi.Consistency.C3
open Tomabechi.Consistency.C4
open Tomabechi.Consistency.C5

open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1CommonModel
open Filter
open scoped Topology

/-- 全トラックで使う候補の共通束。 -/
abbrev CommonLayer := WithTop ℕ

/-- 16や逆極限に使う無限段添字を有限層へ順序埋め込みする。 -/
def commonStageAddress (n : ℕ) : CommonLayer := n

theorem commonStageAddress_ne_top (n : ℕ) :
    commonStageAddress n ≠ (⊤ : CommonLayer) := by
  simp [commonStageAddress]

theorem commonStageAddress_injective : Function.Injective commonStageAddress := by
  intro m n h
  exact WithTop.coe_injective h

theorem commonStageAddress_monotone : Monotone commonStageAddress := by
  intro m n h
  exact WithTop.coe_le_coe.mpr h

/-- C3 Nat段の共通層写像は有限joinを保つ。 -/
theorem commonStageAddress_sup (m n : ℕ) :
    commonStageAddress (m ⊔ n) = commonStageAddress m ⊔ commonStageAddress n := by
  change ((max m n : ℕ) : CommonLayer) = max (m : CommonLayer) n
  exact WithTop.coe_max m n

/-- C3 Nat段の共通層写像は有限meetを保つ。 -/
theorem commonStageAddress_inf (m n : ℕ) :
    commonStageAddress (m ⊓ n) = commonStageAddress m ⊓ commonStageAddress n := by
  change ((min m n : ℕ) : CommonLayer) = min (m : CommonLayer) n
  exact WithTop.coe_min m n

/-- Nat段階から共通束への順序埋込み。有限段どうしの大小関係を正確に保つ。 -/
def commonStageOrderEmbedding : ℕ ↪o CommonLayer where
  toFun := commonStageAddress
  inj' := commonStageAddress_injective
  map_rel_iff' := by
    intro m n
    exact WithTop.coe_le_coe

theorem commonStageAddress_directed :
    ∀ m n : ℕ, ∃ k : ℕ,
      commonStageAddress m ≤ commonStageAddress k ∧
      commonStageAddress n ≤ commonStageAddress k := by
  intro m n
  refine ⟨max m n, ?_, ?_⟩
  · exact WithTop.coe_le_coe.mpr (Nat.le_max_left m n)
  · exact WithTop.coe_le_coe.mpr (Nat.le_max_right m n)

theorem commonStageAddress_no_maximal :
  ∀ n : ℕ, ∃ m : ℕ, commonStageAddress n < commonStageAddress m := by
  intro n
  exact ⟨n + 1, WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)⟩

theorem commonLayer_bottom : (⊥ : CommonLayer) = (0 : CommonLayer) := rfl

theorem commonLayer_top_is_infinite :
    (⊤ : CommonLayer) ≠ commonStageAddress n := by
  simp [commonStageAddress]

/-- C5の二層を共通束の底と最上位へ送る。 -/
def operationalLayerAddress (a : Layer) : CommonLayer :=
  if a then ⊤ else 0

theorem operationalLayerAddress_bottom :
    operationalLayerAddress (⊥ : Layer) = (⊥ : CommonLayer) := by
  simp [operationalLayerAddress]

theorem operationalLayerAddress_top :
    operationalLayerAddress (⊤ : Layer) = (⊤ : CommonLayer) := by
  simp [operationalLayerAddress]

theorem operationalLayerAddress_monotone :
    Monotone operationalLayerAddress := by
  intro a b hab
  cases a with
  | false => cases b <;> simp [operationalLayerAddress]
  | true =>
      cases b with
      | false => exact False.elim ((show ¬ (true : Bool) ≤ false by decide) hab)
      | true => rfl

theorem operationalLayerAddress_injective :
    Function.Injective operationalLayerAddress := by
  intro a b hab
  cases a <;> cases b <;> simp_all [operationalLayerAddress]

/-- C4/C5の二層順序を、共通束上の底と最上位へ順序埋込みする。 -/
def operationalLayerOrderEmbedding : Layer ↪o CommonLayer where
  toFun := operationalLayerAddress
  inj' := operationalLayerAddress_injective
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;> simp [operationalLayerAddress]

theorem operationalLayerAddress_sup (a b : Layer) :
    operationalLayerAddress (a ⊔ b) =
      operationalLayerAddress a ⊔ operationalLayerAddress b := by
  cases a <;> cases b <;> rfl

theorem operationalLayerAddress_inf (a b : Layer) :
    operationalLayerAddress (a ⊓ b) =
      operationalLayerAddress a ⊓ operationalLayerAddress b := by
  cases a <;> cases b <;> rfl

/-- C4の二履歴が持つ固定点中心は、C5と共通のBool層を
C3の表象へ送った値と一致する。履歴を別の層ラベルへ取り違えない。 -/
theorem history_center_matches_common_layer_representation (h : Bool) :
    Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h =
      representation (operationalLayerAddress h) := by
  cases h <;> simp [Tomabechi.Theorem16_25.theorem16_intervalGradientCenter,
    operationalLayerAddress, representation]

/-- C4の各逆極限固定点は、全有限層でその履歴に対応する共通束表象を持つ。 -/
theorem c4_fixedPoint_coordinate_matches_commonLayer (h : Bool) (i : ℕ) :
    (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 i =
      representation (operationalLayerAddress h) := by
  rw [Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoint_coordinate]
  exact history_center_matches_common_layer_representation h

/-- 履歴別逆極限の全座標は、共通束の履歴表象を反復したプロファイルになる。 -/
noncomputable def commonHistoryProfile (h : Bool) : ℕ → ℝ :=
  fun _ => representation (operationalLayerAddress h)

theorem c4_fixedPoint_eq_commonHistoryProfile (h : Bool) :
    (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 =
      commonHistoryProfile h := by
  funext i
  exact c4_fixedPoint_coordinate_matches_commonLayer h i

/-- C4一般接続定理が一意性から生成する固定点は、既存の履歴別固定点と同じである。
したがって一般接続で使う点にも共通層プロファイルの座標表示が成り立つ。 -/
theorem c4_generatedFixedPoint_eq_commonHistoryProfile (h : Bool) :
    (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points.fixedPoint h).1 =
      commonHistoryProfile h := by
  have heq :=
    Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points.unique h
      (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoints.fixedPoint h)
      (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoints.isFixed h)
  funext i
  have hcoord := congrFun (congrArg Subtype.val heq) i
  rw [← hcoord]
  exact c4_fixedPoint_coordinate_matches_commonLayer h i

theorem c4_commonHistoryProfiles_separate :
    commonHistoryProfile false ≠ commonHistoryProfile true := by
  intro h
  have h0 := congrFun h 0
  norm_num [commonHistoryProfile, operationalLayerAddress, representation] at h0

theorem c4_fixedPoints_separate_through_commonLayer :
    (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoints.fixedPoint false).1 ≠
      (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoints.fixedPoint true).1 := by
  rw [c4_fixedPoint_eq_commonHistoryProfile, c4_fixedPoint_eq_commonHistoryProfile]
  exact c4_commonHistoryProfiles_separate

/-- C4/C5共通層写像とC5上層目標はN5の非退化条件を満たす。
下位層が最上位より真に低く、上位の実alive集合には目標内外の状態がある。 -/
theorem c6_N5_C5LayerTarget_nonempty (T : ℝ) (hT : 0 ≤ T) :
    operationalLayerAddress false < (⊤ : CommonLayer) ∧
      ∃ x y : Tomabechi.Examples.Theorem27Op.E2,
        x ∈ Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive ∧
        y ∈ Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive ∧
        x ∈ Tomabechi.Theorem24_26.theorem26ZeroValueTarget
          Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive
          (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) T ∧
        y ∉ Tomabechi.Theorem24_26.theorem26ZeroValueTarget
          Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive
          (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) T := by
  constructor
  · norm_num [operationalLayerAddress]
  · rcases Tomabechi.Examples.Theorem27.vectorSourceDynamics.target_nonempty T hT with
      ⟨x, hx⟩
    refine ⟨x, Tomabechi.Examples.Theorem27.vec 1 0, ?_, ?_, hx, ?_⟩
    · exact Set.mem_univ x
    · exact Set.mem_univ _
    · change Tomabechi.Examples.Theorem27.vec 1 0 ∉
        Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
          (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue
            (⊤ : Tomabechi.Theorem24_26_Model.SourceAbstraction)) T
      rw [Tomabechi.Examples.Theorem27.vectorSourceTargetTop_eq_ring]
      exact Tomabechi.Consistency.C5.active_state_outside_target T

/-- C5上層で選んだ初期状態e0は、N5の極座標で書いた半径1・角度0と同じ点。 -/
theorem c5_e0_eq_vec_one_zero :
    Tomabechi.Examples.Theorem27Op.e0 = Tomabechi.Examples.Theorem27.vec 1 0 := by
  ext i
  fin_cases i <;>
    simp [Tomabechi.Examples.Theorem27Op.e0, Tomabechi.Examples.Theorem27.vec]

/-- N1のC5接続証人。目標外の上層初期値から正時間区間[0,1]を動き、
軌道は全区間で同じモデルのalive集合にあり、両端の状態は異なる。 -/
theorem c6_N1_C5Alive_nonconstantTrajectory :
    ∃ x : Tomabechi.Examples.Theorem27Op.E2,
      x ∉ Tomabechi.Examples.Theorem27Op.ringE 0 ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy x 0 s ∈
          Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive) ∧
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy x 0 0 ≠
        Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy x 0 1 := by
  let x := Tomabechi.Examples.Theorem27.vec 1 0
  refine ⟨x, ?_, ?_, ?_⟩
  · exact Tomabechi.Consistency.C5.active_state_outside_target 0
  · intro s hs
    exact Tomabechi.Examples.Theorem27.vectorSourceDynamics.trajectory_alive
      x 0 s (by norm_num) (Set.mem_univ _) hs.1
  · intro heq
    have h0 :
        (Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy x 0 0) 1 = 0 := by
      rw [Tomabechi.Examples.Theorem27.vectorSourceDataTrajectory_eq_flowE
        x 0 0 (by norm_num) (by norm_num)]
      norm_num [x, Tomabechi.Examples.Theorem27.vec,
        Tomabechi.Examples.Theorem27Op.flowE_1,
        Tomabechi.Examples.Theorem27Op.omg]
    have h1 :
        (Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy x 0 1) 1 ≠ 0 := by
      rw [Tomabechi.Examples.Theorem27.vectorSourceDataTrajectory_eq_flowE
        x 0 1 (by norm_num) (by norm_num)]
      norm_num [x, Tomabechi.Examples.Theorem27.vec,
        Tomabechi.Examples.Theorem27Op.flowE_1,
        Tomabechi.Examples.Theorem27Op.omg]
    have := congrArg (fun y : Tomabechi.Examples.Theorem27Op.E2 => y 1) heq
    exact h1 (this ▸ h0)

/-- N2を共通Nat層とC4の実区間carrierで接続する。
共通添字は非空・有向・最大元なしで、同じC4層に異なる二状態を持つ。 -/
theorem c6_N2_C4CommonLayer_nondegenerate :
    (∃ n : ℕ, commonStageAddress n ≠ (⊤ : CommonLayer)) ∧
      (∀ m n : ℕ, ∃ k : ℕ,
        commonStageAddress m ≤ commonStageAddress k ∧
        commonStageAddress n ≤ commonStageAddress k) ∧
      (∀ n : ℕ, ∃ m : ℕ, commonStageAddress n < commonStageAddress m) ∧
      (∃ h : Bool, ∃ n : ℕ, ∃ x y : ℝ,
        commonStageAddress n ≠ (⊤ : CommonLayer) ∧
        x ≠ y ∧
        x ∈ Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.carrier h n ∧
        y ∈ Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.carrier h n) := by
  refine ⟨⟨0, commonStageAddress_ne_top 0⟩,
    commonStageAddress_directed, commonStageAddress_no_maximal, ?_⟩
  refine ⟨false, 0, 0, 1, commonStageAddress_ne_top 0, by norm_num, ?_, ?_⟩
  · change (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1
    norm_num
  · change (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1
    norm_num

/-- C4の共有履歴SCMが出力するBoolは、共通束表象プロファイルの第0座標を
最上位値1かどうかで読む結果そのものである。 -/
theorem c4_sharedSCM_output_is_commonLayerCode
    (d a h s : Bool) (u : Bool × Bool) :
    (Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM).outputEquation
        d a h u s =
      decide (commonHistoryProfile h 0 = 1) := by
  rw [Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM_output_is_inverseLimitFixedPoint]
  rw [c4_fixedPoint_eq_commonHistoryProfile]

/-- 25共有SCMが出力する値は、16一般接続が生成する固定点の第0座標を
二値化したものでもある。一般接続用fixedPointとSCMの観測を直接同定する。 -/
theorem c4_sharedSCM_output_eq_generatedFixedPointCode
    (d a h s : Bool) (u : Bool × Bool) :
    (Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM).outputEquation
        d a h u s =
      decide ((Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points.fixedPoint h).1 0 = 1) := by
  rw [Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM_output_is_inverseLimitFixedPoint]
  have hold := c4_fixedPoint_coordinate_matches_commonLayer h 0
  have hnew := c4_generatedFixedPoint_eq_commonHistoryProfile h
  have hnew0 := congrFun hnew 0
  have hcoord :
      (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 0 =
        (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points.fixedPoint h).1 0 :=
    hold.trans hnew0.symm
  rw [hcoord]

/-- C4一般接続の固定点を25-C3のΓ状態符号へ入れると、同じ履歴SCMの関係状態を復元する。 -/
theorem c4_generatedFixedPoint_encodes_sharedGamma (d a h : Bool) :
    Tomabechi.Theorem16_25.theorem25_intervalGradientFlowStateCode d a
        (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points.fixedPoint h).1 =
      Tomabechi.Theorem16_25.theorem25_historyDependentPresenceRelations.relationalState d h a := by
  have hgen := c4_generatedFixedPoint_eq_commonHistoryProfile h
  have hexp := c4_fixedPoint_eq_commonHistoryProfile h
  have hsame :
      (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points.fixedPoint h).1 =
        (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoints.fixedPoint h).1 :=
    hgen.trans hexp.symm
  rw [hsame]
  exact Tomabechi.Theorem16_25.theorem25_intervalGradientFlowStateCode_matches d a h

/-- C4の共有SCM出力は、C5のBool層/情報源ラベルと同じ履歴値そのものである。
この等式は全主体・行為・外生入力・状態について成り立つ。 -/
theorem c4_sharedSCM_output_eq_history
    (d a h s : Bool) (u : Bool × Bool) :
    (Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM).outputEquation
        d a h u s = h := by
  rw [c4_sharedSCM_output_is_commonLayerCode]
  cases h <;> norm_num [commonHistoryProfile, operationalLayerAddress, representation]

/-- C4履歴からSCMで読んだ値をC5層として共通束へ送ると、
同じ履歴の層アドレスに一致する。履歴と層を別ラベルへずらさない。 -/
theorem c4_history_output_has_c5_layer_address
    (d a h s : Bool) (u : Bool × Bool) :
    operationalLayerAddress
        ((Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM).outputEquation
          d a h u s) = operationalLayerAddress h := by
  rw [c4_sharedSCM_output_eq_history]

/-- C4履歴を同じBoolのC5層として読むときに選ぶ、実際のC5状態と方策。
下層はUnit/PUnit、上層はE2と既存の最大可測ゲイン方策を使う。 -/
structure C6C4C5ControlAdapter (h : Bool) where
  layer : Tomabechi.Consistency.C5.Layer
  layer_is_history : layer = h
  commonAddress : CommonLayer
  address_is_history : commonAddress = operationalLayerAddress h
  state : Tomabechi.Consistency.C5.State layer
  policy : Tomabechi.Consistency.C5.Policy layer
  policy_admissible :
    Tomabechi.Examples.Theorem27.vectorSourceData.admissible layer policy state 0
  policy_is_data_optimum : ∀ T : ℝ,
    policy = Tomabechi.Examples.Theorem27.vectorSourceData.optimalPolicy layer state T
  starts_at_initial_state :
    Tomabechi.Examples.Theorem27.vectorSourceData.trajectory layer policy state 0 0 = state

/-- 各履歴についてC5の当該層から実制御データを選び、許容性を証明する。 -/
noncomputable def c6C4C5ControlAdapter (h : Bool) : C6C4C5ControlAdapter h := by
  cases h with
  | false =>
      exact {
        layer := false
        layer_is_history := rfl
        commonAddress := operationalLayerAddress false
        address_is_history := rfl
        state := ()
        policy := PUnit.unit
        policy_admissible := trivial
        policy_is_data_optimum := by intro T; rfl
        starts_at_initial_state := rfl }
  | true =>
      exact {
        layer := true
        layer_is_history := rfl
        commonAddress := operationalLayerAddress true
        address_is_history := rfl
        state := Tomabechi.Examples.Theorem27Op.e0
        policy := Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        policy_admissible := by
          change Tomabechi.Examples.Theorem27.measurableGainVectorPolicyAdmissible _
          exact ⟨Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain,
            fun _ => rfl⟩
        policy_is_data_optimum := by
          intro T
          rfl
        starts_at_initial_state := by
          change Tomabechi.Examples.Theorem27.measurableGainVectorOrbit _ _ 0 0 _ = _
          simp [Tomabechi.Examples.Theorem27.measurableGainVectorOrbit,
            Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_initial,
            Tomabechi.Examples.Theorem27Op.e0] }

theorem c6C4C5ControlAdapter_nonempty (h : Bool) :
    Nonempty (C6C4C5ControlAdapter h) :=
  ⟨c6C4C5ControlAdapter h⟩

/-- 各C4履歴で選ぶC5制御の値関数。履歴タグに応じた実C5状態の最適値を記録する。 -/
noncomputable def c6C4C5OptimalValueAt (T : ℝ) : Bool → ℝ
  | false => Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue false () T
  | true => Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
      Tomabechi.Examples.Theorem27Op.e0 T

theorem c6C4C5OptimalValueAt_eq_adapter (h : Bool) (T : ℝ) :
    c6C4C5OptimalValueAt T h =
      Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue
        (c6C4C5ControlAdapter h).layer (c6C4C5ControlAdapter h).state T := by
  cases h <;> rfl

/-- C5費用データの最適方策が達成する有限開始時刻の割引積分費用は、
履歴adapterが選んだ方策についてそのoptimalValueに等しい。 -/
theorem c6C4C5ControlAdapter_optimalCost_attained
    (h : Bool) (T : ℝ) (hT : 0 ≤ T) :
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue
        (c6C4C5ControlAdapter h).layer (c6C4C5ControlAdapter h).state T =
      ∫ s, Tomabechi.Theorem24_26.theorem26DiscountWeight
          Tomabechi.Examples.Theorem27.vectorSourceData.rho T s *
        Tomabechi.Examples.Theorem27.vectorSourceData.runningCost
          (c6C4C5ControlAdapter h).layer (c6C4C5ControlAdapter h).policy
          (Tomabechi.Examples.Theorem27.vectorSourceData.trajectory
            (c6C4C5ControlAdapter h).layer (c6C4C5ControlAdapter h).policy
            (c6C4C5ControlAdapter h).state T s) s
        ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := by
  rw [(c6C4C5ControlAdapter h).policy_is_data_optimum T]
  exact Tomabechi.Examples.Theorem27.vectorSourceData.optimal_value_attained
    (c6C4C5ControlAdapter h).layer (c6C4C5ControlAdapter h).state T hT

/-- 履歴ごとに型の異なるC5状態を、タグ付き直和へ損失なくまとめる。 -/
abbrev C6C5ControlledState :=
  Bool × (Unit ⊕ Tomabechi.Examples.Theorem27Op.E2)

/-- C4履歴hに選んだC5最適制御を、実時刻tの状態へ写す。 -/
noncomputable def c6C4C5ControlledTrajectoryAt (t : ℝ) (h : Bool) :
    C6C5ControlledState := by
  cases h with
  | false => exact (false, Sum.inl ())
  | true =>
      exact (true, Sum.inr (Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        (c6C4C5ControlAdapter true).policy (c6C4C5ControlAdapter true).state 0 t))

theorem c6C4C5ControlledTrajectoryAt_initial (h : Bool) :
    c6C4C5ControlledTrajectoryAt 0 h =
      (h, if h then Sum.inr Tomabechi.Examples.Theorem27Op.e0 else Sum.inl ()) := by
  cases h with
  | false => rfl
  | true =>
      change (true, Sum.inr (Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        Tomabechi.Examples.Theorem27Op.e0 0 0)) = _
      congr 1
      have htraj := Tomabechi.Examples.Theorem27.vectorSourceData.trajectory_initial
        true Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        Tomabechi.Examples.Theorem27Op.e0 0 (by norm_num)
        (by
          change Tomabechi.Examples.Theorem27.measurableGainVectorPolicyAdmissible _
          exact ⟨Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain,
            fun _ => rfl⟩)
      simpa using congrArg
        (Sum.inr : Tomabechi.Examples.Theorem27Op.E2 →
          Unit ⊕ Tomabechi.Examples.Theorem27Op.E2) htraj

/-- C4の履歴が上層を選んだとき、adapterが選ぶ初期状態に定理27の
PZS/残差降下率分類を実際に適用できる。 -/
noncomputable def c6C4C5ControlAdapter_upper_theorem27_classification
    (T : ℝ) (hT : 0 ≤ T) :=
  Tomabechi.Consistency.C5.all_initial_pzs_classification
    (c6C4C5ControlAdapter true).state T hT

/-- 同じadapter初期値で定理27の全時刻入力差下界も適用する。 -/
noncomputable def c6C4C5ControlAdapter_upper_theorem27_action_gap
    (T : ℝ) (hT : 0 ≤ T) :=
  Tomabechi.Consistency.C5.all_initial_action_gap
    (c6C4C5ControlAdapter true).state T hT

/-- 上層を選んだ履歴では、C5の任意の二次元初期状態を保ったまま
同じ最適feedbackへ渡す一般adapter。 -/
structure C6C4C5UpperControlAdapter
    (x : Tomabechi.Examples.Theorem27Op.E2) where
  commonAddress : CommonLayer
  address_is_top : commonAddress = (⊤ : CommonLayer)
  state : Tomabechi.Consistency.C5.State true
  state_is_input : state = x
  policy : Tomabechi.Consistency.C5.Policy true
  policy_admissible :
    Tomabechi.Examples.Theorem27.vectorSourceData.admissible true policy state 0
  policy_is_data_optimum : ∀ T : ℝ,
    policy = Tomabechi.Examples.Theorem27.vectorSourceData.optimalPolicy true state T
  starts_at_initial_state :
    Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true policy state 0 0 = state

noncomputable def c6C4C5UpperControlAdapter
    (x : Tomabechi.Examples.Theorem27Op.E2) : C6C4C5UpperControlAdapter x where
  commonAddress := ⊤
  address_is_top := rfl
  state := x
  state_is_input := rfl
  policy := Tomabechi.Examples.Theorem27.vectorMaximalPolicy
  policy_admissible := by
    change Tomabechi.Examples.Theorem27.measurableGainVectorPolicyAdmissible _
    exact ⟨Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain,
      fun _ => rfl⟩
  policy_is_data_optimum := by intro T; rfl
  starts_at_initial_state :=
    Tomabechi.Examples.Theorem27.vectorSourceData.trajectory_initial
      true Tomabechi.Examples.Theorem27.vectorMaximalPolicy x 0 (by norm_num)
      (by
        change Tomabechi.Examples.Theorem27.measurableGainVectorPolicyAdmissible _
        exact ⟨Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain,
          fun _ => rfl⟩)

/-- 任意上層状態に適合させたC5 adapter上で定理27分類を使う。 -/
noncomputable def c6C4C5UpperControlAdapter_theorem27_classification
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T) :=
  Tomabechi.Consistency.C5.all_initial_pzs_classification
    (c6C4C5UpperControlAdapter x).state T hT

/-- 任意上層状態に適合させたC5 adapter上で定理27入力差下界を使う。 -/
noncomputable def c6C4C5UpperControlAdapter_theorem27_action_gap
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T) :=
  Tomabechi.Consistency.C5.all_initial_action_gap
    (c6C4C5UpperControlAdapter x).state T hT

/-- C4の共有SCMへ一点入力を与えたとき、出力履歴の法則を押し出しmeasureとして作る。
入力は固定するが、履歴hは任意であり、出力は共有SCMの実際の方程式を通る。 -/
noncomputable def c4_historyOutputLaw (h : Bool) : MeasureTheory.Measure Bool :=
  (MeasureTheory.Measure.dirac ()).map
    (fun _ : Unit =>
      (Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM).outputEquation
        false false h (false, false) false)

/-- C4の出力法則は、C5層に置く同じ履歴のDirac法則と一致する。 -/
theorem c4_historyOutputLaw_eq_c5LayerLaw (h : Bool) :
    c4_historyOutputLaw h = MeasureTheory.Measure.dirac h := by
  rw [c4_historyOutputLaw, MeasureTheory.Measure.map_dirac' (by fun_prop)]
  rw [c4_sharedSCM_output_eq_history]

/-- C4の共有SCMに与える全入力の型。積measure上の任意の外生・主体・行為・
履歴・状態の同時法則を受け取り、出力と履歴座標のpushforwardを比較する。 -/
abbrev C4C5SCMInput := (((Bool × Bool) × Bool) × (Bool × Bool)) × Bool

private noncomputable def c4OutputFromInput (i : C4C5SCMInput) : Bool :=
  (Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM).outputEquation
    i.1.1.1.1 i.1.1.1.2 i.1.1.2 i.1.2 i.2

private def c4HistoryFromInput (i : C4C5SCMInput) : Bool := i.1.1.2

/-- 任意のC4入力法則のもとで、共有SCM出力lawは履歴座標のlawそのもの。
入力法則を一点Diracへ狭めず、押し出し法則の等式として証明する。 -/
theorem c4_outputLaw_eq_historyPushforward (μ : MeasureTheory.Measure C4C5SCMInput) :
    μ.map c4OutputFromInput = μ.map c4HistoryFromInput := by
  apply MeasureTheory.Measure.map_congr
  filter_upwards with i
  exact c4_sharedSCM_output_eq_history
    i.1.1.1.1 i.1.1.1.2 i.1.1.2 i.2 i.1.2

/-- C4の実Riは恒等写像なので、共有SCM出力lawにRiを作用させても、
履歴座標からC5層へ渡したlawと一致する。任意の入力measureで成り立つ。 -/
theorem c4_outputLaw_Ri_eq_historyPushforward
    (μ : MeasureTheory.Measure C4C5SCMInput) :
    (μ.map c4OutputFromInput).map
      Tomabechi.Theorem16_25.theorem25_historyDependentPresenceRelations.roleInverse =
      μ.map c4HistoryFromInput := by
  rw [c4_outputLaw_eq_historyPushforward]
  change (μ.map c4HistoryFromInput).map id = μ.map c4HistoryFromInput
  simp

/-- 任意のC4外生入力法則からC5層へ渡す履歴law adapter。
C5層法則をC4履歴座標の周辺lawとして定め、SCM出力lawとの一致を保持する。 -/
structure C6C4C5GeneralHistoryLawAdapter
    (μ : MeasureTheory.Measure C4C5SCMInput) where
  c4OutputLaw : MeasureTheory.Measure Bool
  c5LayerLaw : MeasureTheory.Measure Bool
  c4_law : c4OutputLaw = μ.map c4OutputFromInput
  c5_law : c5LayerLaw = μ.map c4HistoryFromInput
  preserves_law : c4OutputLaw = c5LayerLaw
  ri_preserves_c5_law :
    c4OutputLaw.map
      Tomabechi.Theorem16_25.theorem25_historyDependentPresenceRelations.roleInverse =
      c5LayerLaw

noncomputable def c6C4C5GeneralHistoryLawAdapter
    (μ : MeasureTheory.Measure C4C5SCMInput) :
    C6C4C5GeneralHistoryLawAdapter μ where
  c4OutputLaw := μ.map c4OutputFromInput
  c5LayerLaw := μ.map c4HistoryFromInput
  c4_law := rfl
  c5_law := rfl
  preserves_law := c4_outputLaw_eq_historyPushforward μ
  ri_preserves_c5_law := c4_outputLaw_Ri_eq_historyPushforward μ

/-- 確率入力lawからの履歴周辺lawも確率measureのままである。 -/
theorem c4_historyPushforward_isProbability
    (μ : MeasureTheory.Measure C4C5SCMInput)
    [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map c4HistoryFromInput) := by
  rw [MeasureTheory.Measure.isProbabilityMeasure_map_iff]
  · infer_instance
  · exact (by fun_prop)

/-- C4出力law・C5層law双方の確率性と同一性をまとめたS5部分adapter。 -/
structure C6C4C5ProbabilityHistoryLawAdapter
    (μ : MeasureTheory.Measure C4C5SCMInput)
    [MeasureTheory.IsProbabilityMeasure μ] where
  lawAdapter : C6C4C5GeneralHistoryLawAdapter μ
  c4_output_isProbability : MeasureTheory.IsProbabilityMeasure lawAdapter.c4OutputLaw
  c5_layer_isProbability : MeasureTheory.IsProbabilityMeasure lawAdapter.c5LayerLaw

noncomputable def c6C4C5ProbabilityHistoryLawAdapter
    (μ : MeasureTheory.Measure C4C5SCMInput)
    [MeasureTheory.IsProbabilityMeasure μ] :
    C6C4C5ProbabilityHistoryLawAdapter μ where
  lawAdapter := c6C4C5GeneralHistoryLawAdapter μ
  c4_output_isProbability := by
    rw [(c6C4C5GeneralHistoryLawAdapter μ).preserves_law]
    exact c4_historyPushforward_isProbability μ
  c5_layer_isProbability := c4_historyPushforward_isProbability μ

/-- C4の任意の確率入力lawを、Ri付きのC5層lawと各層の実制御データへ
一括して接続する部分統合adapter。各履歴ラベルには対応するC5層を割り当てる。 -/
structure C6C4C5LayerControlLawAdapter
    (μ : MeasureTheory.Measure C4C5SCMInput)
    [MeasureTheory.IsProbabilityMeasure μ] where
  historyLaw : C6C4C5ProbabilityHistoryLawAdapter μ
  controls : ∀ h : Bool, C6C4C5ControlAdapter h

noncomputable def c6C4C5LayerControlLawAdapter
    (μ : MeasureTheory.Measure C4C5SCMInput)
    [MeasureTheory.IsProbabilityMeasure μ] :
    C6C4C5LayerControlLawAdapter μ where
  historyLaw := c6C4C5ProbabilityHistoryLawAdapter μ
  controls := c6C4C5ControlAdapter

theorem c6C4C5LayerControlLawAdapter_nonempty
    (μ : MeasureTheory.Measure C4C5SCMInput)
    [MeasureTheory.IsProbabilityMeasure μ] :
    Nonempty (C6C4C5LayerControlLawAdapter μ) :=
  ⟨c6C4C5LayerControlLawAdapter μ⟩

/-- C4の実際の無作為化C3-SCMから、C6比較用タプルへ外生入力・履歴・候補を運ぶ。 -/
noncomputable def c4RandomizedInputToC6Intervened
    (d a s : Bool) (u : Bool × Bool) : C4C5SCMInput :=
  ((((d, a),
      (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u),
    u),
    s)

private noncomputable def c4RandomizedInputToC6 (u : Bool × Bool) : C4C5SCMInput :=
  c4RandomizedInputToC6Intervened false false
    ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.candidateVariable
      false false u) u

/-- C6 comparison inputを経由した固定点共有SCMの出力は、同じ外生入力に対する
無作為化C3モデルの実出力と一致する。両方とも大域履歴値を返す。 -/
theorem c4RandomizedActualOutput_eq_c6Output (u : Bool × Bool) :
    (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.outputEquation
        false false
        ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
        u
        ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.candidateVariable
          false false u) =
      c4OutputFromInput (c4RandomizedInputToC6 u) := by
  rw [Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomized_output_eq_history]
  rw [c4RandomizedInputToC6, c4RandomizedInputToC6Intervened, c4OutputFromInput,
    c4_sharedSCM_output_eq_history]

theorem c4RandomizedIntervenedOutput_eq_c6Output_allContexts
    (d a s : Bool) (u : Bool × Bool) :
    (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.outputEquation
        d a
        ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
        u s =
      c4OutputFromInput (c4RandomizedInputToC6Intervened d a s u) := by
  rw [Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomized_output_eq_history]
  rw [c4RandomizedInputToC6Intervened, c4OutputFromInput, c4_sharedSCM_output_eq_history]

theorem c4RandomizedIntervenedOutput_eq_c6Output (s : Bool) (u : Bool × Bool) :
    (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.outputEquation
        false false
        ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
        u s =
      c4OutputFromInput (c4RandomizedInputToC6Intervened false false s u) := by
  exact c4RandomizedIntervenedOutput_eq_c6Output_allContexts false false s u

/-- 同じC4外生確率measureをC6のlaw比較入力へ押し出したmeasure。 -/
noncomputable def c4RandomizedInputLaw : MeasureTheory.Measure C4C5SCMInput :=
  ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
    c4RandomizedInputToC6

theorem c4RandomizedInputLaw_isProbability :
    MeasureTheory.IsProbabilityMeasure c4RandomizedInputLaw := by
  rw [c4RandomizedInputLaw, MeasureTheory.Measure.isProbabilityMeasure_map_iff]
  · infer_instance
  · exact (measurable_of_finite _).aemeasurable

/-- 履歴出力のlawは、C6入力経由のlawとC4無作為化モデルの実出力lawで一致する。 -/
theorem c4RandomizedOutputLaw_eq_actualModelOutputLaw :
    c4RandomizedInputLaw.map c4OutputFromInput =
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
        (fun u =>
          (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.outputEquation
            false false
            ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
            u
            ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.candidateVariable
              false false u)) := by
  rw [c4RandomizedInputLaw, MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext u
  exact (c4RandomizedActualOutput_eq_c6Output u).symm

/-- 同じ外生measure上で、C4実SCMとC6共有SCMの(state, output)介入joint lawが一致する。
stateは元の25-C3 Γ状態を保ち、candidate介入値sを任意に取る。 -/
noncomputable def c4C6StateOutputFromInput (i : C4C5SCMInput) :
    Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool :=
  ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.stateEquation
      i.1.1.1.1 i.1.1.1.2 i.1.1.2 i.1.2,
    c4OutputFromInput i)

theorem c4RandomizedIntervenedJointLaw_eq_actualModelJointLaw (d a s : Bool) :
    (((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
      (c4RandomizedInputToC6Intervened d a s)).map c4C6StateOutputFromInput =
    ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
      (fun u =>
        ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.stateEquation
            d a
            ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
            u,
          (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.outputEquation
            d a
            ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
            u s)) := by
  rw [MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext u
  apply Prod.ext
  · rfl
  · exact (c4RandomizedIntervenedOutput_eq_c6Output_allContexts d a s u).symm

instance c4RandomizedInputLaw_probabilityInstance :
    MeasureTheory.IsProbabilityMeasure c4RandomizedInputLaw :=
  c4RandomizedInputLaw_isProbability

/-- C4の実外生lawから得たC5層lawは、元の同じSCMのglobalHistory lawである。
同じ値にはC5各層の実制御adapterも用意し、候補二値の正質量を同じ外生law上で保つ。 -/
theorem c6C4RandomizedLayerLaw_eq_sourceHistoryLaw_and_controls :
    (c6C4C5LayerControlLawAdapter c4RandomizedInputLaw).historyLaw.lawAdapter.c5LayerLaw =
        ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
          (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory ∧
      (∀ h : Bool, Nonempty (C6C4C5ControlAdapter h)) ∧
      (∀ s : Bool,
        Tomabechi.Theorem16_25.Theorem25GlobalHistorySCM.candidateHasPositiveMass
          ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.toIndexed)
          false false s) ∧
      (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedSelfProcessSCM).toLawModel.Condition25A2 () := by
  letI : MeasureTheory.IsProbabilityMeasure c4RandomizedInputLaw :=
    c4RandomizedInputLaw_isProbability
  refine ⟨?_, c6C4C5ControlAdapter_nonempty,
    Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomized_candidate_has_positive_mass,
    ?_⟩
  change c4RandomizedInputLaw.map c4HistoryFromInput = _
  rw [c4RandomizedInputLaw, MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  exact Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedSelfProcessSCM_satisfies25A2

/-- C4/C5共有入力lawをC5最適制御の実trajectoryへ押し出すと、C4モデルの同じ
globalHistoryから直接作るtrajectory lawに一致する。 -/
theorem c6C4RandomizedControlledTrajectoryLaw_eq_sourceHistoryTrajectoryLaw (t : ℝ) :
    (c6C4C5LayerControlLawAdapter c4RandomizedInputLaw).historyLaw.lawAdapter.c5LayerLaw.map
        (c6C4C5ControlledTrajectoryAt t) =
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
        (fun u => c6C4C5ControlledTrajectoryAt t
          ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)) := by
  have hLaw := c6C4RandomizedLayerLaw_eq_sourceHistoryLaw_and_controls.1
  rw [hLaw, MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- C5の履歴別最適値（実際の割引積分費用）は、C4外生lawから得る
globalHistory lawを介して計算した費用lawと一致する。 -/
theorem c6C4RandomizedOptimalCostLaw_eq_sourceHistoryCostLaw
    (T : ℝ) (hT : 0 ≤ T) :
    (c6C4C5LayerControlLawAdapter c4RandomizedInputLaw).historyLaw.lawAdapter.c5LayerLaw.map
        (c6C4C5OptimalValueAt T) =
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
        (fun u => c6C4C5OptimalValueAt T
          ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)) := by
  have hLaw := c6C4RandomizedLayerLaw_eq_sourceHistoryLaw_and_controls.1
  rw [hLaw, MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- 履歴ごとに選んだC5方策が実際に支払う有限地平割引費用。 -/
noncomputable def c6C4C5RealizedCostAt (T : ℝ) (h : Bool) : ℝ :=
  ∫ s, Tomabechi.Theorem24_26.theorem26DiscountWeight
      Tomabechi.Examples.Theorem27.vectorSourceData.rho T s *
    Tomabechi.Examples.Theorem27.vectorSourceData.runningCost
      (c6C4C5ControlAdapter h).layer (c6C4C5ControlAdapter h).policy
      (Tomabechi.Examples.Theorem27.vectorSourceData.trajectory
        (c6C4C5ControlAdapter h).layer (c6C4C5ControlAdapter h).policy
        (c6C4C5ControlAdapter h).state T s) s
    ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T

/-- 非負地平では各履歴の実割引費用が、その選択状態でのC5最適値に達する。 -/
theorem c6C4C5RealizedCostAt_eq_optimalValue
    (T : ℝ) (hT : 0 ≤ T) (h : Bool) :
    c6C4C5RealizedCostAt T h = c6C4C5OptimalValueAt T h := by
  rw [c6C4C5OptimalValueAt_eq_adapter]
  simpa [c6C4C5RealizedCostAt] using
    (c6C4C5ControlAdapter_optimalCost_attained h T hT).symm

/-- 履歴タグ・実制御状態・実割引費用を同じ履歴から作る結合観測量。 -/
noncomputable def c6C4C5JointControlOutcome (T t : ℝ) (h : Bool) :
    Bool × C6C5ControlledState × ℝ :=
  (h, c6C4C5ControlledTrajectoryAt t h, c6C4C5RealizedCostAt T h)

/-- C4外生lawから履歴・C5制御状態・C5実割引費用を同時に押し出したlawは、
同じSCMのglobalHistory lawから作るlawと一致する。周辺law別の主張より強く、
trajectoryと実費用が同じ履歴変数で結合していることを保存する。 -/
theorem c6C4RandomizedJointControlOutcomeLaw_eq_sourceHistoryLaw
    (T t : ℝ) :
    (c6C4C5LayerControlLawAdapter c4RandomizedInputLaw).historyLaw.lawAdapter.c5LayerLaw.map
        (c6C4C5JointControlOutcome T t) =
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
        (fun u => c6C4C5JointControlOutcome T t
          ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)) := by
  have hLaw := c6C4RandomizedLayerLaw_eq_sourceHistoryLaw_and_controls.1
  rw [hLaw, MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- 25-C3の介入観測 `(Γ,Y⁺)` とC5の履歴別制御状態・最適値を
同じ履歴/外生入力から作る結合観測。 -/
noncomputable def c4C6IntervenedJointControlOutcome
    (T t : ℝ) (i : C4C5SCMInput) :
    (Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool) ×
      (Bool × C6C5ControlledState × ℝ) :=
  (c4C6StateOutputFromInput i,
    c6C4C5JointControlOutcome T t i.1.1.2)

/-- C4の介入joint `(Γ,Y⁺)` とC5のtrajectory・最適値を結合しても、
ひとつの外生入力から定めたlawと、C4の実際の介入モデル上で同じ履歴から作るlawは一致する。
これは介入観測と制御評価の間の同時依存を保存するS5接続である。 -/
theorem c4RandomizedIntervenedJointControlOutcomeLaw_eq_actualModelLaw
    (d a s : Bool) (T t : ℝ) :
    (((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
      (c4RandomizedInputToC6Intervened d a s)).map
        (c4C6IntervenedJointControlOutcome T t) =
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
        (fun u =>
          (((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.stateEquation
              d a
              ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
              u,
            (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.outputEquation
              d a
              ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
              u s),
          c6C4C5JointControlOutcome T t
            ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u))) := by
  rw [MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext u
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact (c4RandomizedIntervenedOutput_eq_c6Output_allContexts d a s u).symm
  · rfl

/-- C4→C5の履歴law保存を、同じBool型上の確率measure等式として束ねる。 -/
structure C6C4C5HistoryLawAdapter (h : Bool) where
  outputLaw : MeasureTheory.Measure Bool
  c4_outputLaw : outputLaw = c4_historyOutputLaw h
  c5_layerLaw : outputLaw = MeasureTheory.Measure.dirac h

noncomputable def c6C4C5HistoryLawAdapter (h : Bool) :
    C6C4C5HistoryLawAdapter h where
  outputLaw := c4_historyOutputLaw h
  c4_outputLaw := rfl
  c5_layerLaw := c4_historyOutputLaw_eq_c5LayerLaw h

theorem c6C4C5HistoryLawAdapter_nonempty (h : Bool) :
    Nonempty (C6C4C5HistoryLawAdapter h) :=
  ⟨c6C4C5HistoryLawAdapter h⟩

/-- C2の完全状態から27の半径・位相座標を作るための観測経過時間。
経過時間は独立時計ではなく、物理観測yと認知座標qから復元する。 -/
def entropyObservedElapsed (z : CompleteState) : ℝ :=
  physicalCoordinate z + (cognitiveCoordinate z) ^ 2

/-- C2の完全状態を27の二次元認知状態へ写す観測写像。 -/
noncomputable def entropyStateTo27
    (z : CompleteState) : Tomabechi.Examples.Theorem27Op.E2 :=
  Real.exp (-entropyObservedElapsed z) • Tomabechi.Examples.Theorem27Op.e0 +
    ((3 / 2 : ℝ) * entropyObservedElapsed z) •
      Tomabechi.Examples.Theorem27Op.e1

/-- C5への二次元観測は、少なくともその第一座標から総エントロピー観測を復元する。 -/
theorem entropyStateTo27_injective_observedElapsed {z w : CompleteState}
    (h : entropyStateTo27 z = entropyStateTo27 w) :
    entropyObservedElapsed z = entropyObservedElapsed w := by
  have h0 := congrArg (fun v : Tomabechi.Examples.Theorem27Op.E2 => v 0) h
  have he : Real.exp (-entropyObservedElapsed z) =
      Real.exp (-entropyObservedElapsed w) := by
    simpa [entropyStateTo27, Tomabechi.Examples.Theorem27Op.e0,
      Tomabechi.Examples.Theorem27Op.e1] using h0
  have hlog := Real.exp_injective he
  linarith

/-- C2の状態則を全初期状態へ延長する明示流。認知座標は元の
`q'=1-q` に従い、物理座標は全エントロピー経過率を1に保つよう従う。 -/
noncomputable def completeEntropyFlow (z : CompleteState) (t : ℝ) : CompleteState :=
  let q := cognitiveCoordinate z
  let elapsed := entropyObservedElapsed z + t
  let q' := 1 - (1 - q) * Real.exp (-t)
  (q', elapsed - q' ^ 2)

/-- C2の完全状態上の制御なし速度場。 -/
def entropyVectorField (z : CompleteState) : CompleteState :=
  (1 - cognitiveCoordinate z,
    1 - 2 * cognitiveCoordinate z * (1 - cognitiveCoordinate z))

theorem completeEntropyFlow_initial (z : CompleteState) :
    completeEntropyFlow z 0 = z := by
  rcases z with ⟨q, y⟩
  simp [completeEntropyFlow, entropyObservedElapsed,
    cognitiveCoordinate, physicalCoordinate]

theorem entropyObservedElapsed_completeEntropyFlow (z : CompleteState) (t : ℝ) :
    entropyObservedElapsed (completeEntropyFlow z t) =
      entropyObservedElapsed z + t := by
  rcases z with ⟨q, y⟩
  simp only [completeEntropyFlow, entropyObservedElapsed,
    cognitiveCoordinate, physicalCoordinate]
  ring

theorem cognitiveCoordinate_completeEntropyFlow (z : CompleteState) (t : ℝ) :
    cognitiveCoordinate (completeEntropyFlow z t) =
      1 - (1 - cognitiveCoordinate z) * Real.exp (-t) := by
  simp [completeEntropyFlow, cognitiveCoordinate]

theorem completeEntropyFlow_cognitive_derivative
    (z : CompleteState) (t : ℝ) :
    HasDerivAt (fun s => cognitiveCoordinate (completeEntropyFlow z s))
      ((1 - cognitiveCoordinate z) * Real.exp (-t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s))
      (-Real.exp (-t)) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  have hmul := hexp.const_mul (1 - cognitiveCoordinate z)
  have hq := HasDerivAt.const_sub (1 : ℝ) hmul
  convert hq using 1 <;> simp [completeEntropyFlow, cognitiveCoordinate]

theorem completeEntropyFlow_cognitive_derivative_eq_field
    (z : CompleteState) (t : ℝ) :
    HasDerivAt (fun s => cognitiveCoordinate (completeEntropyFlow z s))
      (entropyVectorField (completeEntropyFlow z t)).1 t := by
  simpa [entropyVectorField, cognitiveCoordinate_completeEntropyFlow] using
    completeEntropyFlow_cognitive_derivative z t

theorem completeEntropyFlow_physical_derivative_eq_field
    (z : CompleteState) (t : ℝ) :
    HasDerivAt (fun s => physicalCoordinate (completeEntropyFlow z s))
      (entropyVectorField (completeEntropyFlow z t)).2 t := by
  let q := fun s : ℝ => cognitiveCoordinate (completeEntropyFlow z s)
  have hq : HasDerivAt q (1 - q t) t := by
    convert completeEntropyFlow_cognitive_derivative z t using 1
    change 1 - cognitiveCoordinate (completeEntropyFlow z t) = _
    rw [cognitiveCoordinate_completeEntropyFlow]
    ring
  have hq2 : HasDerivAt (fun s => q s ^ 2) (2 * q t * (1 - q t)) t := by
    convert hq.pow 2 using 1 <;> simp [q]
  have hid : HasDerivAt (fun s : ℝ => entropyObservedElapsed z + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (entropyObservedElapsed z)
  have hy := hid.sub hq2
  have hfun : (fun s => physicalCoordinate (completeEntropyFlow z s)) =
      fun s => entropyObservedElapsed z + s - q s ^ 2 := by
    funext s
    simp [q, completeEntropyFlow, entropyObservedElapsed,
      cognitiveCoordinate, physicalCoordinate]
  rw [hfun]
  convert hy using 1
  · simp [entropyVectorField, q]

theorem completeEntropyFlow_hasDerivAt
    (z : CompleteState) (t : ℝ) :
    HasDerivAt (fun s => completeEntropyFlow z s)
      (entropyVectorField (completeEntropyFlow z t)) t := by
  convert (completeEntropyFlow_cognitive_derivative_eq_field z t).prodMk
    (completeEntropyFlow_physical_derivative_eq_field z t) using 1
  funext s
  exact (Prod.eta _).symm

/-- 明示流は任意の二時刻で再始動できる。 -/
theorem completeEntropyFlow_semigroup (z : CompleteState) (s t : ℝ) :
    completeEntropyFlow (completeEntropyFlow z s) t =
      completeEntropyFlow z (s + t) := by
  have hq : cognitiveCoordinate (completeEntropyFlow (completeEntropyFlow z s) t) =
      cognitiveCoordinate (completeEntropyFlow z (s + t)) := by
    rw [cognitiveCoordinate_completeEntropyFlow,
      cognitiveCoordinate_completeEntropyFlow,
      cognitiveCoordinate_completeEntropyFlow]
    rw [show 1 - (1 - (1 - cognitiveCoordinate z) * Real.exp (-s)) =
        (1 - cognitiveCoordinate z) * Real.exp (-s) by ring]
    congr 1
    calc
      (1 - cognitiveCoordinate z) * Real.exp (-s) * Real.exp (-t) =
          (1 - cognitiveCoordinate z) * (Real.exp (-s) * Real.exp (-t)) := by ring_nf
      _ = (1 - cognitiveCoordinate z) * Real.exp (-(s + t)) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
  apply Prod.ext
  · exact hq
  · have hlhs : physicalCoordinate (completeEntropyFlow (completeEntropyFlow z s) t) =
        entropyObservedElapsed (completeEntropyFlow z s) + t -
          cognitiveCoordinate (completeEntropyFlow (completeEntropyFlow z s) t) ^ 2 := by
      simp [completeEntropyFlow, entropyObservedElapsed, cognitiveCoordinate,
        physicalCoordinate]
    have hrhs : physicalCoordinate (completeEntropyFlow z (s + t)) =
        entropyObservedElapsed z + (s + t) -
          cognitiveCoordinate (completeEntropyFlow z (s + t)) ^ 2 := by
      simp [completeEntropyFlow, entropyObservedElapsed, cognitiveCoordinate,
        physicalCoordinate]
    change physicalCoordinate (completeEntropyFlow (completeEntropyFlow z s) t) =
      physicalCoordinate (completeEntropyFlow z (s + t))
    rw [hlhs, hrhs, entropyObservedElapsed_completeEntropyFlow, hq]
    ring

theorem generalizedEntropy_eq_observedElapsed (z : CompleteState) :
    generalizedEntropy z = 1 + entropyObservedElapsed z := by
  rw [generalizedEntropy, weightedLayerEntropy_tsum]
  simp [entropyObservedElapsed, physicalEntropy, physicalCoordinate,
    cognitiveCoordinate]
  ring

theorem generalizedEntropy_completeEntropyFlow (z : CompleteState) (t : ℝ) :
    generalizedEntropy (completeEntropyFlow z t) = generalizedEntropy z + t := by
  rw [generalizedEntropy_eq_observedElapsed,
    entropyObservedElapsed_completeEntropyFlow,
    generalizedEntropy_eq_observedElapsed]
  ring

/-- 任意の異なる二時刻で完全状態が異なる。単調な一般化エントロピーにより
完全状態そのものの非再帰が従う。 -/
theorem completeEntropyFlow_nonrecurrent (z : CompleteState) {s t : ℝ}
    (hst : s ≠ t) : completeEntropyFlow z s ≠ completeEntropyFlow z t := by
  intro heq
  have hent := congrArg generalizedEntropy heq
  rw [generalizedEntropy_completeEntropyFlow,
    generalizedEntropy_completeEntropyFlow] at hent
  exact hst (by linarith)

theorem baseEntropyTrajectory_eq_completeEntropyFlow (t : ℝ) :
    trajectory t = completeEntropyFlow (0, 0) t := by
  simp [trajectory, completeEntropyFlow, cognitiveCoordinate,
    entropyObservedElapsed, physicalCoordinate]

theorem entropyStateTo27_completeEntropyFlow (z : CompleteState) (t : ℝ) :
    entropyStateTo27 (completeEntropyFlow z t) =
      Real.exp (-(entropyObservedElapsed z + t)) •
          Tomabechi.Examples.Theorem27Op.e0 +
        ((3 / 2 : ℝ) * (entropyObservedElapsed z + t)) •
          Tomabechi.Examples.Theorem27Op.e1 := by
  rw [entropyStateTo27, entropyObservedElapsed_completeEntropyFlow]

/-- 全てのC2初期完全状態に対する拡張流は、持ち上げた初期状態からの
27最大ゲインベクトル軌道を正確に再現する。 -/
theorem completeEntropyFlow_lift_matches_maximal27
    (z : CompleteState) (t : ℝ) :
    entropyStateTo27 (completeEntropyFlow z t) =
      Tomabechi.Examples.Theorem27.measurableGainVectorOrbit
        (Real.exp (-entropyObservedElapsed z))
        ((3 / 2 : ℝ) * entropyObservedElapsed z) 0 t
        Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain := by
  rw [entropyStateTo27_completeEntropyFlow]
  unfold Tomabechi.Examples.Theorem27.measurableGainVectorOrbit
  rw [Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain_orbit]
  ext i
  fin_cases i
  · simp [Tomabechi.Examples.Theorem27Op.e0,
      Tomabechi.Examples.Theorem27Op.e1_apply0,
      Tomabechi.Examples.Theorem26_27ControlClasses.orbit,
      Tomabechi.Examples.Theorem26_27ControlClasses.rate]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp [Tomabechi.Examples.Theorem27Op.e0_apply1,
      Tomabechi.Examples.Theorem27Op.e1,
      Tomabechi.Examples.Theorem26_27ControlClasses.orbit,
      Tomabechi.Examples.Theorem26_27ControlClasses.rate]
    ring

/-- これは明示的な軌道式だけの一致ではなく、C5の定理24–27入力データが
返す全初期状態からの最適軌道との一致である。 -/
theorem completeEntropyFlow_lift_matches_theorem27_data
    (z : CompleteState) (t : ℝ) (ht : 0 ≤ t) :
    entropyStateTo27 (completeEntropyFlow z t) =
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        (entropyStateTo27 z) 0 t := by
  rw [Tomabechi.Examples.Theorem27.vectorSourceDataTrajectory_eq_flowE
    (entropyStateTo27 z) 0 t (by norm_num) ht]
  have hx : entropyStateTo27 z =
      Real.exp (-entropyObservedElapsed z) •
          Tomabechi.Examples.Theorem27Op.e0 +
        ((3 / 2 : ℝ) * entropyObservedElapsed z) •
          Tomabechi.Examples.Theorem27Op.e1 := by
    rfl
  rw [hx, ← Tomabechi.Examples.Theorem27.maximal_measurable_vector_orbit_eq_operational
    (Real.exp (-entropyObservedElapsed z))
    ((3 / 2 : ℝ) * entropyObservedElapsed z) 0 t (by norm_num) ht]
  exact completeEntropyFlow_lift_matches_maximal27 z t

theorem completeEntropyFlow_lift_preserves_running_cost
    (z : CompleteState) (t : ℝ) :
    Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true
      Tomabechi.Examples.Theorem27.vectorMaximalPolicy
      (entropyStateTo27 (completeEntropyFlow z t)) t =
      3 * Real.exp (-2 * (entropyObservedElapsed z + t)) := by
  change 3 * (entropyStateTo27 (completeEntropyFlow z t) 0) ^ 2 = _
  rw [entropyStateTo27_completeEntropyFlow]
  simp [Tomabechi.Examples.Theorem27Op.e0,
    Tomabechi.Examples.Theorem27Op.e1_apply0]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem completeEntropyFlow_lift_preserves_optimal_value
    (z : CompleteState) (t : ℝ) :
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
      (entropyStateTo27 (completeEntropyFlow z t)) t =
      Real.exp (-2 * (entropyObservedElapsed z + t)) := by
  change (entropyStateTo27 (completeEntropyFlow z t) 0) ^ 2 = _
  rw [entropyStateTo27_completeEntropyFlow]
  simp [Tomabechi.Examples.Theorem27Op.e0,
    Tomabechi.Examples.Theorem27Op.e1_apply0]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem entropyObservedElapsed_on_trajectory (t : ℝ) :
    entropyObservedElapsed (trajectory t) = t := by
  simp [entropyObservedElapsed, physicalCoordinate, cognitiveCoordinate,
    trajectory]

/-- C1二主体の平均・不一致からC2の完全状態を作る座標写像。
C2の認知座標は `1-d` とし、C1の二主体状態を逆に復元できる。 -/
noncomputable def c1ToCompleteState (x : AgentState) : CompleteState :=
  let q := 1 - halfDifference x
  (q, 5 + meanState x - q ^ 2)

/-- C2完全状態からC1の二主体状態を復元する射影。 -/
def completeStateToC1 (m : ℝ) (z : CompleteState) : AgentState :=
  ![m + (1 - cognitiveCoordinate z), m - (1 - cognitiveCoordinate z)]

/-- 重み付き正層和を含めたC2一般化エントロピーは、完全状態flowに沿って
実際のentropyObservedElapsedに1を加えた値となる。 -/
theorem generalizedEntropy_completeEntropyFlow_eq_elapsed (z : CompleteState) (t : ℝ) :
    Tomabechi.Consistency.C2.generalizedEntropy (completeEntropyFlow z t) =
      entropyObservedElapsed z + t + 1 := by
  rw [Tomabechi.Consistency.C2.generalizedEntropy,
    Tomabechi.Consistency.C2.weightedLayerEntropy_tsum]
  simp [Tomabechi.Consistency.C2.physicalEntropy,
    Tomabechi.Consistency.C2.physicalCoordinate,
    Tomabechi.Consistency.C2.cognitiveCoordinate,
    completeEntropyFlow, entropyObservedElapsed]

/-- C1箱flowをC2完全状態へ接続したとき、一般化エントロピーは
元の初期値からちょうど rate-3 の生産量だけ増える。 -/
theorem c1CompleteFlow_generalizedEntropy_exactProduction
    (x : AgentState) (t₀ t : ℝ) :
    Tomabechi.Consistency.C2.generalizedEntropy
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) =
      Tomabechi.Consistency.C2.generalizedEntropy (c1ToCompleteState x) +
        3 * (t - t₀) := by
  have hbase : Tomabechi.Consistency.C2.generalizedEntropy (c1ToCompleteState x) =
      entropyObservedElapsed (c1ToCompleteState x) + 1 := by
    have h := generalizedEntropy_completeEntropyFlow_eq_elapsed
      (c1ToCompleteState x) 0
    simpa [completeEntropyFlow_initial] using h
  rw [generalizedEntropy_completeEntropyFlow_eq_elapsed, hbase]
  ring

/-- C5上層の最適値は、同じC2完全状態上の一般化エントロピーから
`exp(-2(S-1))` として厳密に復元できる。費用評価を別状態の式に置き換えない。 -/
theorem completeEntropyFlow_C5OptimalValue_eq_generalizedEntropy
    (z : CompleteState) (t : ℝ) :
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (entropyStateTo27 (completeEntropyFlow z t)) t =
      Real.exp (-2 *
        (Tomabechi.Consistency.C2.generalizedEntropy (completeEntropyFlow z t) - 1)) := by
  rw [completeEntropyFlow_lift_preserves_optimal_value,
    generalizedEntropy_completeEntropyFlow_eq_elapsed]
  congr 1
  ring

theorem completeStateToC1_c1ToCompleteState (x : AgentState) :
    completeStateToC1 (meanState x) (c1ToCompleteState x) = x := by
  ext i
  fin_cases i <;>
    simp [completeStateToC1, c1ToCompleteState, cognitiveCoordinate,
      meanState, halfDifference] <;> ring

/-- C1の初期箱をC2完全状態へ写したとき、認知座標は一様に
`[3/4,5/4]` に入る。符号付き半差を保ったままの評価である。 -/
theorem c1ToCompleteState_cognitive_mem (x : AgentState) (hx : x ∈ box) :
    cognitiveCoordinate (c1ToCompleteState x) ∈ Set.Icc (3 / 4 : ℝ) (5 / 4) := by
  have h0 : |x 0| ≤ (1 / 4 : ℝ) := hx 0
  have h1 : |x 1| ≤ (1 / 4 : ℝ) := hx 1
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  change 3 / 4 ≤ 1 - halfDifference x ∧ 1 - halfDifference x ≤ 5 / 4
  rw [halfDifference]
  constructor <;> nlinarith

/-- C1の箱全体から作る物理観測は正であり、実際には `51/16` 以上。
これは初期時刻だけの評価で、将来の物理観測の符号は主張しない。 -/
theorem c1ToCompleteState_physical_lower (x : AgentState) (hx : x ∈ box) :
    (51 / 16 : ℝ) ≤ physicalCoordinate (c1ToCompleteState x) := by
  have hq := c1ToCompleteState_cognitive_mem x hx
  have hm0 : |x 0| ≤ (1 / 4 : ℝ) := hx 0
  have hm1 : |x 1| ≤ (1 / 4 : ℝ) := hx 1
  have hm0' := abs_le.mp hm0
  have hm1' := abs_le.mp hm1
  have hqlo := hq.1
  have hqhi := hq.2
  change (51 / 16 : ℝ) ≤ 5 + meanState x - (1 - halfDifference x) ^ 2
  have hsq : (1 - halfDifference x) ^ 2 ≤ (25 / 16 : ℝ) := by
    rw [halfDifference]
    nlinarith
  rw [meanState]
  nlinarith

/-- C1の箱から始めた完全状態流では、未来の認知座標も同じ区間にとどまる。
時刻差は非負とし、半差の符号は絶対値評価で両側とも扱う。 -/
theorem c1CompleteFlow_cognitive_mem (x : AgentState) (hx : x ∈ box)
    (t₀ t : ℝ) (htt : t₀ ≤ t) :
    cognitiveCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) ∈
        Set.Icc (3 / 4 : ℝ) (5 / 4) := by
  have hd : |halfDifference x| ≤ (1 / 4 : ℝ) := by
    have h0 : |x 0| ≤ (1 / 4 : ℝ) := hx 0
    have h1 : |x 1| ≤ (1 / 4 : ℝ) := hx 1
    have h0' := abs_le.mp h0
    have h1' := abs_le.mp h1
    rw [halfDifference]
    rw [abs_le]
    constructor <;> nlinarith
  have htime : 0 ≤ 3 * (t - t₀) := by positivity
  have hexp0 : 0 < Real.exp (-(3 * (t - t₀))) := Real.exp_pos _
  have hexp1 : Real.exp (-(3 * (t - t₀))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hprod : |halfDifference x * Real.exp (-(3 * (t - t₀)))| ≤ (1 / 4 : ℝ) := by
    rw [abs_mul]
    calc
      |halfDifference x| * |Real.exp (-(3 * (t - t₀)))| ≤ (1 / 4) * 1 := by
        apply mul_le_mul hd ?_ (abs_nonneg _) (by norm_num)
        rw [abs_of_pos hexp0]
        exact hexp1
      _ = (1 / 4 : ℝ) := by ring
  have hq : cognitiveCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) =
        1 - halfDifference x * Real.exp (-(3 * (t - t₀))) := by
    rw [cognitiveCoordinate_completeEntropyFlow]
    simp [c1ToCompleteState, cognitiveCoordinate]
  rw [hq]
  have := abs_le.mp hprod
  change 3 / 4 ≤ 1 - halfDifference x * Real.exp (-(3 * (t - t₀))) ∧
    1 - halfDifference x * Real.exp (-(3 * (t - t₀))) ≤ 5 / 4
  constructor <;> nlinarith

/-- 初期箱から移送した完全状態の物理観測は、開始後も `51/16` 以上。
エントロピー生成の時間増加があり、認知座標は有界なので正値が保たれる。 -/
theorem c1CompleteFlow_physical_lower
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (htt : t₀ ≤ t) :
    (51 / 16 : ℝ) ≤ physicalCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) := by
  have hq := c1CompleteFlow_cognitive_mem x hx t₀ t htt
  have hq2 : (cognitiveCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))) ^ 2 ≤ (25 / 16 : ℝ) := by
    nlinarith [hq.1, hq.2]
  have hm0 : |x 0| ≤ (1 / 4 : ℝ) := hx 0
  have hm1 : |x 1| ≤ (1 / 4 : ℝ) := hx 1
  have hm0' := abs_le.mp hm0
  have hm1' := abs_le.mp hm1
  have hmean : -(1 / 4 : ℝ) ≤ meanState x := by
    rw [meanState]
    nlinarith
  have htime : 0 ≤ 3 * (t - t₀) := by positivity
  have hphysical : physicalCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) =
      5 + meanState x + 3 * (t - t₀) -
        (cognitiveCoordinate
          (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))) ^ 2 := by
    simp [completeEntropyFlow, entropyObservedElapsed, c1ToCompleteState,
      cognitiveCoordinate, physicalCoordinate]
  rw [hphysical]
  nlinarith

/-- C1の物理時間tにおける各層エントロピー `1+q²` の導関数。
完全状態流の基準時間を `3(t-t₀)` とするため、生成率は3倍される。 -/
theorem c1CompleteFlow_layerEntropy_hasDerivAt (x : AgentState) (t₀ t : ℝ) :
    HasDerivAt
      (fun s : ℝ => 1 +
        (cognitiveCoordinate
          (completeEntropyFlow (c1ToCompleteState x) (3 * (s - t₀)))) ^ 2)
      (6 * cognitiveCoordinate
          (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) *
        (1 - cognitiveCoordinate
          (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))))) t := by
  have hq := completeEntropyFlow_cognitive_derivative
    (c1ToCompleteState x) (3 * (t - t₀))
  have htime : HasDerivAt (fun s : ℝ => 3 * (s - t₀)) 3 t := by
    convert ((hasDerivAt_id t).sub_const t₀).const_mul 3 using 1 <;> norm_num
  have hcomp := hq.comp t htime
  have hqscaled : HasDerivAt
      (fun s : ℝ => cognitiveCoordinate
        (completeEntropyFlow (c1ToCompleteState x) (3 * (s - t₀))))
      (3 * (1 - cognitiveCoordinate
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))))) t := by
    convert hcomp using 1 <;> (try rfl) <;>
      rw [cognitiveCoordinate_completeEntropyFlow] <;> ring
  have hsq := hqscaled.pow 2
  have hsum := hsq.const_add 1
  convert hsum using 1 <;> ring

/-- C1箱からの全未来流で、共通の各層エントロピーの物理時間導関数は
絶対値 `15/8` 以下、従ってC2の一様有界性定数2以下である。 -/
theorem c1CompleteFlow_layerEntropy_derivative_bound
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (htt : t₀ ≤ t) :
    |6 * cognitiveCoordinate
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) *
      (1 - cognitiveCoordinate
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))))| ≤ (15 / 8 : ℝ) := by
  have hq := c1CompleteFlow_cognitive_mem x hx t₀ t htt
  have hqAbs : |cognitiveCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))| ≤ (5 / 4 : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [hq.1, hq.2]
  have honeqAbs : |1 - cognitiveCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))| ≤ (1 / 4 : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [hq.1, hq.2]
  calc
    |6 * cognitiveCoordinate
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) *
      (1 - cognitiveCoordinate
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))))|
      = 6 * |cognitiveCoordinate
          (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))| *
        |1 - cognitiveCoordinate
          (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))| := by rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    _ ≤ 6 * (5 / 4) * (1 / 4) := by gcongr
    _ = (15 / 8 : ℝ) := by norm_num

/-- C1から移した各正層エントロピーの共通生成率。 -/
noncomputable def c1CompleteFlow_layerRate
    (x : AgentState) (t₀ t : ℝ) : ℝ :=
  6 * cognitiveCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) *
    (1 - cognitiveCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))))

/-- 各有限層集合について、実際の微分和が共通生成率と重みの有限和の積になる。
有限和の項を一つの共通観測から計算し、別々の層の値を混同しない。 -/
theorem c1CompleteFlow_finiteLayerDerivative_eq
    (s : Finset PositiveLayer) (x : AgentState) (t₀ t : ℝ) :
    (∑ n ∈ s, layerWeight n *
      deriv (fun u => layerEntropy n
        (completeEntropyFlow (c1ToCompleteState x) (3 * (u - t₀)))) t) =
      (∑ n ∈ s, layerWeight n) * c1CompleteFlow_layerRate x t₀ t := by
  have hderiv (n : PositiveLayer) :
      deriv (fun u => layerEntropy n
        (completeEntropyFlow (c1ToCompleteState x) (3 * (u - t₀)))) t =
        c1CompleteFlow_layerRate x t₀ t := by
    have h := (c1CompleteFlow_layerEntropy_hasDerivAt x t₀ t).deriv
    simpa [layerEntropy, c1CompleteFlow_layerRate] using h
  simp_rw [hderiv]
  rw [Finset.sum_mul]

/-- C1箱上、未来区間内の実際の有限層微分和はC2で使う上界2を満たす。
層重みの有限和が1以下であることと生成率`15/8`以下を合わせる。 -/
theorem c1CompleteFlow_finiteLayerDerivative_bound
    (s : Finset PositiveLayer) (x : AgentState) (hx : x ∈ box)
    (t₀ t : ℝ) (htt : t₀ ≤ t) :
    |∑ n ∈ s, layerWeight n *
      deriv (fun u => layerEntropy n
        (completeEntropyFlow (c1ToCompleteState x) (3 * (u - t₀)))) t| ≤ (2 : ℝ) := by
  rw [c1CompleteFlow_finiteLayerDerivative_eq]
  have hw0 : 0 ≤ ∑ n ∈ s, layerWeight n := by
    apply Finset.sum_nonneg
    intro n hn
    exact le_of_lt (layerWeight_pos n)
  have hw1 := layerWeight_sum_le_one s
  have hr := c1CompleteFlow_layerEntropy_derivative_bound x hx t₀ t htt
  rw [c1CompleteFlow_layerRate, abs_mul]
  calc
    |∑ n ∈ s, layerWeight n| * |c1CompleteFlow_layerRate x t₀ t|
      = (∑ n ∈ s, layerWeight n) *
        |c1CompleteFlow_layerRate x t₀ t| := by rw [abs_of_nonneg hw0]
    _ ≤ 1 * (15 / 8) := by
      exact mul_le_mul hw1 hr (abs_nonneg _) (by norm_num)
    _ ≤ 2 := by norm_num

/-- C1から移した全有限層微分和を、時刻の関数として用意する。 -/
noncomputable def c1CompleteFlow_finiteLayerDerivative
    (s : Finset PositiveLayer) (x : AgentState) (t₀ : ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ s, layerWeight n *
    deriv (fun u => layerEntropy n
      (completeEntropyFlow (c1ToCompleteState x) (3 * (u - t₀)))) t

theorem c1CompleteFlow_layerRate_continuous
    (x : AgentState) (t₀ : ℝ) : Continuous (c1CompleteFlow_layerRate x t₀) := by
  have hq : Continuous (fun t => cognitiveCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))) := by
    have hform : (fun t => cognitiveCoordinate
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))) =
        fun t => 1 - halfDifference x * Real.exp (-(3 * (t - t₀))) := by
      funext t
      rw [cognitiveCoordinate_completeEntropyFlow]
      simp [c1ToCompleteState, cognitiveCoordinate]
    rw [hform]
    fun_prop
  unfold c1CompleteFlow_layerRate
  exact (continuous_const.mul hq).mul (continuous_const.sub hq)

theorem c1CompleteFlow_finiteLayerDerivative_continuous
    (s : Finset PositiveLayer) (x : AgentState) (t₀ : ℝ) :
    Continuous (c1CompleteFlow_finiteLayerDerivative s x t₀) := by
  have heq : c1CompleteFlow_finiteLayerDerivative s x t₀ =
      fun t => (∑ n ∈ s, layerWeight n) * c1CompleteFlow_layerRate x t₀ t := by
    funext t
    exact c1CompleteFlow_finiteLayerDerivative_eq s x t₀ t
  rw [heq]
  exact continuous_const.mul (c1CompleteFlow_layerRate_continuous x t₀)

/-- 各有限層微分和の族は未来の任意の有界区間上で一様可積分。
区間の両端を開始時刻以後に置くことで、全時刻の点wise上界2を使う。 -/
theorem c1CompleteFlow_A6_allFinite_UI
    (x : AgentState) (hx : x ∈ box) (t₀ a b : ℝ)
    (hta : t₀ ≤ a) (hab : a < b) :
    MeasureTheory.UniformIntegrable
      (fun s : Finset PositiveLayer => c1CompleteFlow_finiteLayerDerivative s x t₀)
      1 (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.uIoc a b)
  have hμfinite : MeasureTheory.IsFiniteMeasure μ := by
    apply (MeasureTheory.isFiniteMeasure_restrict).2
    simp [μ, Real.volume_uIoc]
  letI : MeasureTheory.IsFiniteMeasure μ := hμfinite
  have hmeas : ∀ s : Finset PositiveLayer,
      MeasureTheory.AEStronglyMeasurable
        (c1CompleteFlow_finiteLayerDerivative s x t₀) μ := by
    intro s
    exact (c1CompleteFlow_finiteLayerDerivative_continuous s x t₀).aestronglyMeasurable
  have hbound : ∀ s : Finset PositiveLayer,
      ∀ᵐ t ∂μ, ‖c1CompleteFlow_finiteLayerDerivative s x t₀ t‖ ≤ 2 := by
    intro s
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
    have htIoc : t ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le hab.le] using ht
    have htt : t₀ ≤ t := le_trans hta htIoc.1.le
    have hbnd := c1CompleteFlow_finiteLayerDerivative_bound s x hx t₀ t htt
    rw [Real.norm_eq_abs]
    exact hbnd
  exact uniformIntegrable_of_bound_two μ
      (fun s : Finset PositiveLayer => c1CompleteFlow_finiteLayerDerivative s x t₀)
      hmeas hbound

/-- C1 rate-3時間で移送した完全状態の物理観測の導関数。 -/
theorem c1CompleteFlow_physical_hasDerivAt (x : AgentState) (t₀ t : ℝ) :
    HasDerivAt
      (fun s : ℝ => physicalCoordinate
        (completeEntropyFlow (c1ToCompleteState x) (3 * (s - t₀))))
      (3 - c1CompleteFlow_layerRate x t₀ t) t := by
  have hbase := completeEntropyFlow_physical_derivative_eq_field
    (c1ToCompleteState x) (3 * (t - t₀))
  have htime : HasDerivAt (fun s : ℝ => 3 * (s - t₀)) 3 t := by
    convert ((hasDerivAt_id t).sub_const t₀).const_mul 3 using 1 <;> norm_num
  have hcomp := hbase.comp t htime
  convert hcomp using 1 <;> (try rfl) <;>
    simp [entropyVectorField, c1CompleteFlow_layerRate] <;> ring

theorem c1CompleteFlow_physical_deriv_eq (x : AgentState) (t₀ t : ℝ) :
    deriv (fun s : ℝ => physicalCoordinate
      (completeEntropyFlow (c1ToCompleteState x) (3 * (s - t₀)))) t =
      3 - c1CompleteFlow_layerRate x t₀ t :=
  (c1CompleteFlow_physical_hasDerivAt x t₀ t).deriv

/-- 移送後の各意味層エントロピーは、任意の有限時刻区間で絶対連続。 -/
theorem c1CompleteFlow_layerEntropy_ac
    (n : PositiveLayer) (x : AgentState) (t₀ a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => layerEntropy n
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))) a b := by
  apply absolutelyContinuous_of_hasDerivAt
    (f := fun t => layerEntropy n
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))))
    (f' := c1CompleteFlow_layerRate x t₀)
  · intro t
    have h := c1CompleteFlow_layerEntropy_hasDerivAt x t₀ t
    simpa [layerEntropy, c1CompleteFlow_layerRate] using h
  · exact c1CompleteFlow_layerRate_continuous x t₀

/-- 移送後の物理エントロピーも、任意の有限時刻区間で絶対連続。 -/
theorem c1CompleteFlow_physicalEntropy_ac
    (x : AgentState) (t₀ a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => physicalEntropy
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))) a b := by
  apply absolutelyContinuous_of_hasDerivAt
    (f := fun t => physicalEntropy
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))))
    (f' := fun t => 3 - c1CompleteFlow_layerRate x t₀ t)
  · intro t
    have h := c1CompleteFlow_physical_hasDerivAt x t₀ t
    simpa [physicalEntropy, physicalCoordinate] using h
  · exact continuous_const.sub (c1CompleteFlow_layerRate_continuous x t₀)

/-- 同じ物理観測・同じ全正層列に対するA7の微分収支。
物理生成率は3で、層重み総和はC2の実値1を使う。 -/
theorem c1CompleteFlow_A7_pointwise (x : AgentState) (t₀ t : ℝ) :
    deriv (fun s : ℝ => physicalEntropy
      (completeEntropyFlow (c1ToCompleteState x) (3 * (s - t₀)))) t =
      -(∑' n : PositiveLayer, layerWeight n *
        deriv (fun s => layerEntropy n
          (completeEntropyFlow (c1ToCompleteState x) (3 * (s - t₀)))) t) + 3 := by
  have hlayer (n : PositiveLayer) :
      deriv (fun s => layerEntropy n
        (completeEntropyFlow (c1ToCompleteState x) (3 * (s - t₀)))) t =
        c1CompleteFlow_layerRate x t₀ t := by
    have h := (c1CompleteFlow_layerEntropy_hasDerivAt x t₀ t).deriv
    simpa [layerEntropy, c1CompleteFlow_layerRate] using h
  have hsum : (∑' n : PositiveLayer, layerWeight n *
      deriv (fun s => layerEntropy n
          (completeEntropyFlow (c1ToCompleteState x) (3 * (s - t₀)))) t) =
      c1CompleteFlow_layerRate x t₀ t := by
    have hrewrite : (fun n : PositiveLayer => layerWeight n *
        deriv (fun s => layerEntropy n
          (completeEntropyFlow (c1ToCompleteState x) (3 * (s - t₀)))) t) =
        fun n => c1CompleteFlow_layerRate x t₀ t * layerWeight n := by
      funext n
      rw [hlayer n]
      ring
    rw [hrewrite, tsum_mul_left, layerWeight_tsum]
    ring
  change deriv (fun s : ℝ => physicalCoordinate
    (completeEntropyFlow (c1ToCompleteState x) (3 * (s - t₀)))) t = _
  rw [c1CompleteFlow_physical_deriv_eq, hsum]
  ring

/-- 任意の時刻における重み付き層エントロピー級数は収束する。 -/
theorem c1CompleteFlow_A6_endpoint_summable
    (x : AgentState) (t₀ t : ℝ) :
    Summable (fun n : PositiveLayer => layerWeight n * layerEntropy n
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))) :=
  weightedLayerEntropy_summable
    (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))

/-- A6′の列挙部分和極限は、層重み和と共通生成率の可算和可能性から得る。 -/
theorem c1CompleteFlow_A6_prefix_tendsto
    (x : AgentState) (t₀ t : ℝ) :
    Filter.Tendsto
      (fun k => ∑ i : Fin k,
        layerWeight
            (Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer i.val) *
          deriv (fun u => layerEntropy
            (Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer i.val)
            (completeEntropyFlow (c1ToCompleteState x) (3 * (u - t₀)))) t)
      atTop
      (𝓝 (∑' n : PositiveLayer, layerWeight n *
        deriv (fun u => layerEntropy n
          (completeEntropyFlow (c1ToCompleteState x) (3 * (u - t₀)))) t)) := by
  let e := Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer
  have hsum : Summable (fun n : PositiveLayer => layerWeight n *
      deriv (fun u => layerEntropy n
        (completeEntropyFlow (c1ToCompleteState x) (3 * (u - t₀)))) t) := by
    have h := layerWeight_summable.mul_right (c1CompleteFlow_layerRate x t₀ t)
    have hrewrite : (fun n : PositiveLayer => layerWeight n *
        deriv (fun u => layerEntropy n
          (completeEntropyFlow (c1ToCompleteState x) (3 * (u - t₀)))) t) =
      fun n => layerWeight n * c1CompleteFlow_layerRate x t₀ t := by
      funext n
      have hd : deriv (fun u => layerEntropy n
          (completeEntropyFlow (c1ToCompleteState x) (3 * (u - t₀)))) t =
          c1CompleteFlow_layerRate x t₀ t := by
        have h := (c1CompleteFlow_layerEntropy_hasDerivAt x t₀ t).deriv
        simpa [layerEntropy, c1CompleteFlow_layerRate] using h
      exact congrArg (fun r => layerWeight n * r) hd
    rw [hrewrite]
    exact h
  have h := Tomabechi.Theorem15.enumerated_tsum_partial_tendsto_of_summable
    e (fun n : PositiveLayer => layerWeight n *
      deriv (fun u => layerEntropy n
        (completeEntropyFlow (c1ToCompleteState x) (3 * (u - t₀)))) t) hsum
  simpa [e] using h

/-- C1の任意の箱初期値から作った完全状態流に、15(I)→23-A入口を実際に適用する。
生存域は開始時刻以後であり、各仮定はこの同じ状態・層・重み・生成率から供給する。 -/
theorem c1CompleteFlow_theorem15_23_nonrecurrence
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Ici t₀ → t₂ ∈ Set.Ici t₀ → t₁ < t₂ →
      completeEntropyFlow (c1ToCompleteState x) (3 * (t₂ - t₀)) ≠
        completeEntropyFlow (c1ToCompleteState x) (3 * (t₁ - t₀)) := by
  apply Tomabechi.Theorem15_23.theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence
    (Layer := PositiveLayer) (State := CompleteState)
    (physicalEntropy := physicalEntropy) (layerEntropy := layerEntropy)
    (layerWeight := layerWeight) layerWeight_pos
    (fun _ z => by simp [layerEntropy]; positivity)
    (fun t => completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))
    (fun _ => 3) (Set.Ici t₀)
  · intro a b ha hb hab
    have hint : (∫ t in a..b, (3 : ℝ)) = 3 * (b - a) := by
      simp [intervalIntegral.integral_const]
      ring
    rw [hint]
    nlinarith
  · intro a b ha hb hab n
    exact c1CompleteFlow_layerEntropy_ac n x t₀ a b
  · intro a b ha hb hab
    exact c1CompleteFlow_physicalEntropy_ac x t₀ a b
  · intro a b ha hb hab
    exact ⟨c1CompleteFlow_A6_endpoint_summable x t₀ a,
      c1CompleteFlow_A6_endpoint_summable x t₀ b⟩
  · intro a b ha hb hab
    exact c1CompleteFlow_A6_allFinite_UI x hx t₀ a b
      (Set.mem_Ici.mp ha) hab
  · intro a b ha hb hab
    exact Filter.Eventually.of_forall (c1CompleteFlow_A6_prefix_tendsto x t₀)
  · intro a b ha hb hab
    exact Filter.Eventually.of_forall (c1CompleteFlow_A7_pointwise x t₀)
  · intro a b ha hb hab
    exact Filter.Eventually.of_forall (fun _ => by norm_num)

/-- C1のrate-3選択flowをC2完全状態へ移送し、C1射影で元のflowを回収する。
平均は保存し、不一致座標は `exp(-3t)` で減衰する。 -/
theorem c1Flow_preserved_by_completeEntropyFlow
    (x : AgentState) (t₀ t : ℝ) :
    completeStateToC1 (meanState x)
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) =
      consensusOptimalFlow.flow t₀ x t := by
  ext i
  fin_cases i <;>
    simp [completeStateToC1, c1ToCompleteState, completeEntropyFlow,
      entropyObservedElapsed, cognitiveCoordinate, physicalCoordinate,
      consensusOptimalFlow, meanState, halfDifference] <;> ring

/-- 同じC1初期値から、C2完全状態流をC5のvectorSourceDataへ写すと、
その全データが返す定理27の最大ゲイン軌道に一致する。開始時刻と
定理27側の経過時刻を明示的に区別したadapterである。 -/
theorem c1CompleteFlow_matches_theorem27_data
    (x : AgentState) (t₀ t : ℝ) (htt : t₀ ≤ t) :
    entropyStateTo27
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) =
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        (entropyStateTo27 (c1ToCompleteState x)) 0 (3 * (t - t₀)) := by
  apply completeEntropyFlow_lift_matches_theorem27_data
  positivity

/-- 先のadapterで使うC1完全状態の初期値も、C1二主体状態へ正確に戻る。 -/
theorem c1Initial_projection_exact (x : AgentState) :
    completeStateToC1 (meanState x) (c1ToCompleteState x) = x :=
  completeStateToC1_c1ToCompleteState x

/-- 保存されるrate-3 flowは、局所C1Witnessが実際に選んだ最適flowでもある。 -/
theorem c1CompleteFlow_matches_witness
    (x : AgentState) (t₀ t : ℝ) :
    completeStateToC1 (meanState x)
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) =
      c1Witness.selectedFlow.flow t₀ x t := by
  rw [c1Witness.selectedFlow_eq_rate3]
  exact c1Flow_preserved_by_completeEntropyFlow x t₀ t

/-- C2の具体的なエントロピー軌道を27の二次元軌道へ写すと、
最大ゲイン制御の半径・位相軌道に一致する。これは全初期状態の同定ではなく、
共有された一つの非定常な観測軌道上での力学保存を示す。 -/
theorem entropyTrajectory_lift_matches_maximal27 (t : ℝ) :
    entropyStateTo27 (trajectory t) =
      Tomabechi.Examples.Theorem27.measurableGainVectorOrbit
        1 0 0 t
      Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain := by
  have hleft : entropyStateTo27 (trajectory t) =
      Real.exp (-t) • Tomabechi.Examples.Theorem27Op.e0 +
        ((3 / 2 : ℝ) * t) • Tomabechi.Examples.Theorem27Op.e1 := by
    rw [entropyStateTo27, entropyObservedElapsed_on_trajectory]
  rw [hleft]
  unfold Tomabechi.Examples.Theorem27.measurableGainVectorOrbit
  rw [Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain_orbit]
  ext i
  fin_cases i <;>
    (simp [Tomabechi.Examples.Theorem27Op.e0,
      Tomabechi.Examples.Theorem27Op.e1,
      Tomabechi.Examples.Theorem26_27ControlClasses.orbit,
      Tomabechi.Examples.Theorem26_27ControlClasses.rate] <;> ring)

/-- 上の軌道一致は明示式だけでなく、C5で実際に定理24–27へ渡す
`vectorSourceData` の最適方策軌道について成立する。 -/
theorem entropyTrajectory_matches_theorem27_data (t : ℝ) (ht : 0 ≤ t) :
    entropyStateTo27 (trajectory t) =
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        Tomabechi.Examples.Theorem27Op.e0 0 t := by
  rw [Tomabechi.Examples.Theorem27.vectorSourceDataTrajectory_eq_flowE
    Tomabechi.Examples.Theorem27Op.e0 0 t (by norm_num) ht]
  rw [entropyTrajectory_lift_matches_maximal27,
    Tomabechi.Examples.Theorem27.maximal_measurable_vector_orbit_eq_operational
      1 0 0 t (by norm_num) ht]
  simp [Tomabechi.Examples.Theorem27Op.e0]

/-- 同じ射影状態で、C5の上位走行費はC2認知座標から得る残差表示
`3(1-q)^2` と一致する。 -/
theorem entropy_lifted_running_cost (t : ℝ) (ht : 0 ≤ t) :
    Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true
      Tomabechi.Examples.Theorem27.vectorMaximalPolicy
      (entropyStateTo27 (trajectory t)) t =
      3 * (1 - cognitiveCoordinate (trajectory t)) ^ 2 := by
  change 3 * (entropyStateTo27 (trajectory t) 0) ^ 2 = _
  rw [entropyTrajectory_matches_theorem27_data t ht]
  rw [Tomabechi.Examples.Theorem27.vectorSourceDataTrajectory_eq_flowE
    Tomabechi.Examples.Theorem27Op.e0 0 t (by norm_num) ht]
  simp [Tomabechi.Examples.Theorem27Op.flowE,
    Tomabechi.Theorem24_26_Model.flow,
    Tomabechi.Examples.Theorem27Op.e0,
    Tomabechi.Examples.Theorem27Op.e1_apply0,
    cognitiveCoordinate, trajectory]

/-- C2の正層を、物理層0を避けて共通束の正の有限層へ送る。 -/
def entropyLayerAddress (n : PositiveLayer) : CommonLayer :=
  (originalPositiveIndex n : ℕ)

theorem entropyLayerAddress_ne_top (n : PositiveLayer) :
    entropyLayerAddress n ≠ (⊤ : CommonLayer) := by
  simp [entropyLayerAddress]

theorem entropyLayerAddress_pos (n : PositiveLayer) :
    0 < (entropyLayerAddress n).untopD 0 := by
  simp [entropyLayerAddress, originalPositiveIndex]

theorem entropyLayerAddress_injective :
    Function.Injective entropyLayerAddress := by
  intro m n h
  have h' : originalPositiveIndex m = originalPositiveIndex n := by
    exact WithTop.coe_injective h
  exact originalPositiveIndex_injective h'

theorem entropyLayerAddress_monotone :
    Monotone entropyLayerAddress := by
  intro m n h
  exact WithTop.coe_le_coe.mpr (Nat.succ_le_succ h)

/-- C1/C2正層の共通束写像は、正整数へのシフト後も有限joinを保つ。 -/
theorem entropyLayerAddress_sup (m n : PositiveLayer) :
    entropyLayerAddress (m ⊔ n) = entropyLayerAddress m ⊔ entropyLayerAddress n := by
  apply congrArg (fun k : ℕ => (k : CommonLayer))
  change max m n + 1 = max (m + 1) (n + 1)
  rcases le_total m n with h | h
  · simp [max_eq_right h, max_eq_right (Nat.succ_le_succ h)]
  · simp [max_eq_left h, max_eq_left (Nat.succ_le_succ h)]

/-- C1/C2正層の共通束写像は、正整数へのシフト後も有限meetを保つ。 -/
theorem entropyLayerAddress_inf (m n : PositiveLayer) :
    entropyLayerAddress (m ⊓ n) = entropyLayerAddress m ⊓ entropyLayerAddress n := by
  apply congrArg (fun k : ℕ => (k : CommonLayer))
  change min m n + 1 = min (m + 1) (n + 1)
  rcases le_total m n with h | h
  · simp [min_eq_left h, min_eq_left (Nat.succ_le_succ h)]
  · simp [min_eq_right h, min_eq_right (Nat.succ_le_succ h)]

/-- C2/C1の正層列挙は、共通束への順序埋込みである。 -/
def entropyLayerOrderEmbedding : PositiveLayer ↪o CommonLayer where
  toFun := entropyLayerAddress
  inj' := entropyLayerAddress_injective
  map_rel_iff' := by
    intro m n
    constructor
    · intro h
      exact Nat.add_le_add_iff_right.mp (WithTop.coe_le_coe.mp h)
    · intro h
      exact WithTop.coe_le_coe.mpr (Nat.add_le_add_right h 1)

theorem entropyLayerAddress_not_physical_bottom (n : PositiveLayer) :
    entropyLayerAddress n ≠ (0 : CommonLayer) := by
  simp [entropyLayerAddress, originalPositiveIndex]

/-- C2の第n正層と、C3で対応する第n+1共通段階は同じ束要素である。
この等式が、両トラックで使う中心表象の添字を結びつける。 -/
theorem entropyLayerAddress_eq_commonStageAddress_succ (n : PositiveLayer) :
    entropyLayerAddress n = commonStageAddress (n + 1) := rfl

theorem every_positive_finite_layer_has_entropy_index {k : ℕ} (hk : 0 < k) :
    ∃ n : PositiveLayer, entropyLayerAddress n = (k : CommonLayer) := by
  refine ⟨k - 1, ?_⟩
  change ((originalPositiveIndex (k - 1) : ℕ) : CommonLayer) = (k : CommonLayer)
  have hk1 : 1 ≤ k := by omega
  exact congrArg (fun m : ℕ => (m : CommonLayer))
    (Nat.sub_add_cancel hk1)

/-- C2の幾何重みを共通束へ拡張する。最上位元は15の実数層添字ではないので
重み0とし、有限層kの重みを `2^{-k}` とする。 -/
noncomputable def commonEntropyWeight : CommonLayer → ℝ
  | ⊤ => 0
  | (k : ℕ) => (1 / 2 : ℝ) ^ k

theorem commonEntropyWeight_positive_finite (k : ℕ) :
    0 < commonEntropyWeight (k : CommonLayer) := by
  simp [commonEntropyWeight]

theorem commonEntropyWeight_top : commonEntropyWeight (⊤ : CommonLayer) = 0 := rfl

theorem commonEntropyWeight_matches_C2 (n : PositiveLayer) :
    commonEntropyWeight (entropyLayerAddress n) = layerWeight n := by
  rfl

theorem commonEntropyWeight_positiveLayer_tsum :
    (∑' n : PositiveLayer, commonEntropyWeight (entropyLayerAddress n)) = 1 := by
  simp_rw [commonEntropyWeight_matches_C2]
  exact layerWeight_tsum

/-- 原文15層carrierの各実数添字に、range表現のNat添字を選ぶ。 -/
noncomputable def originalLayerCarrierIndex
    (r : {x : ℝ // x ∈ originalLayerIndexSet}) : ℕ :=
  Classical.choose r.property

theorem originalLayerCarrierIndex_spec
    (r : {x : ℝ // x ∈ originalLayerIndexSet}) :
    (originalLayerCarrierIndex r : ℝ) = r.1 :=
  Classical.choose_spec r.property

/-- 原文15の可算実数添字carrierを共通束へ順序埋込みする。
ℝの添字はcarrier上でNat castとして一意に表せる。 -/
noncomputable def originalLayerCarrierOrderEmbedding :
    {x : ℝ // x ∈ originalLayerIndexSet} ↪o CommonLayer where
  toFun := fun r => commonStageAddress (originalLayerCarrierIndex r)
  inj' := by
    intro r s hrs
    apply Subtype.ext
    have hidx : originalLayerCarrierIndex r = originalLayerCarrierIndex s :=
      WithTop.coe_injective hrs
    calc
      r.1 = (originalLayerCarrierIndex r : ℝ) :=
        (originalLayerCarrierIndex_spec r).symm
      _ = (originalLayerCarrierIndex s : ℝ) := by exact_mod_cast hidx
      _ = s.1 := originalLayerCarrierIndex_spec s
  map_rel_iff' := by
    intro r s
    change commonStageAddress (originalLayerCarrierIndex r) ≤
        commonStageAddress (originalLayerCarrierIndex s) ↔ r.1 ≤ s.1
    constructor
    · intro hidx
      have hnat : originalLayerCarrierIndex r ≤ originalLayerCarrierIndex s :=
        WithTop.coe_le_coe.mp hidx
      have hcast : (originalLayerCarrierIndex r : ℝ) ≤
          (originalLayerCarrierIndex s : ℝ) := by exact_mod_cast hnat
      rw [originalLayerCarrierIndex_spec r, originalLayerCarrierIndex_spec s] at hcast
      exact hcast
    · intro hrs
      have hcast : (originalLayerCarrierIndex r : ℝ) ≤
          (originalLayerCarrierIndex s : ℝ) := by
        rw [originalLayerCarrierIndex_spec r, originalLayerCarrierIndex_spec s]
        exact hrs
      have hnat : originalLayerCarrierIndex r ≤ originalLayerCarrierIndex s :=
        by exact_mod_cast hcast
      exact WithTop.coe_le_coe.mpr hnat

theorem originalLayerCarrierOrderEmbedding_eq_commonStageAddress_of_cast
    (r : {x : ℝ // x ∈ originalLayerIndexSet}) (k : ℕ)
    (hr : r.1 = (k : ℝ)) :
    originalLayerCarrierOrderEmbedding r = commonStageAddress k := by
  apply congrArg commonStageAddress
  have hspec := originalLayerCarrierIndex_spec r
  rw [hr] at hspec
  exact_mod_cast hspec

theorem originalLayerCarrierOrderEmbedding_physical_zero :
    originalLayerCarrierOrderEmbedding ⟨0, ⟨0, by simp⟩⟩ = commonStageAddress 0 :=
  originalLayerCarrierOrderEmbedding_eq_commonStageAddress_of_cast _ _ (by simp)

theorem originalLayerCarrierOrderEmbedding_positive_layer (n : PositiveLayer) :
    originalLayerCarrierOrderEmbedding
        ⟨originalPositiveRealIndex n,
          ⟨originalPositiveIndex n, by
            simp [originalPositiveRealIndex, originalPositiveIndex]⟩⟩ =
      commonStageAddress (originalPositiveIndex n) :=
  originalLayerCarrierOrderEmbedding_eq_commonStageAddress_of_cast _ _ rfl

/-- 定理15の自然数実数像carrierから共通束への写像は、carrier内のjoinを保つ。 -/
theorem originalLayerCarrierOrderEmbedding_sup
    (r s : {x : ℝ // x ∈ originalLayerIndexSet}) :
    originalLayerCarrierOrderEmbedding (r ⊔ s) =
      originalLayerCarrierOrderEmbedding r ⊔ originalLayerCarrierOrderEmbedding s := by
  rcases le_total r s with hrs | hsr
  · rw [sup_eq_right.mpr hrs,
      sup_eq_right.mpr (originalLayerCarrierOrderEmbedding.map_rel_iff.mpr hrs)]
  · rw [sup_eq_left.mpr hsr,
      sup_eq_left.mpr (originalLayerCarrierOrderEmbedding.map_rel_iff.mpr hsr)]

/-- 定理15の自然数実数像carrierから共通束への写像は、carrier内のmeetを保つ。 -/
theorem originalLayerCarrierOrderEmbedding_inf
    (r s : {x : ℝ // x ∈ originalLayerIndexSet}) :
    originalLayerCarrierOrderEmbedding (r ⊓ s) =
      originalLayerCarrierOrderEmbedding r ⊓ originalLayerCarrierOrderEmbedding s := by
  rcases le_total r s with hrs | hsr
  · rw [inf_eq_left.mpr hrs,
      inf_eq_left.mpr (originalLayerCarrierOrderEmbedding.map_rel_iff.mpr hrs)]
  · rw [inf_eq_right.mpr hsr,
      inf_eq_right.mpr (originalLayerCarrierOrderEmbedding.map_rel_iff.mpr hsr)]

/-- C2で宣言された原文型の可算層添字集合を、共通束の有限層へ対応させる。
物理層0は独立に残し、正層nはn+1へ送る。最上位⊤は実数添字へ写さない。 -/
structure C6Theorem15LayerAdapter where
  carrier : Set ℝ
  carrier_eq_original : carrier = originalLayerIndexSet
  carrier_countable : carrier.Countable
  carrier_nonnegative : carrier ⊆ Set.Ici 0
  physical_zero_mem : (0 : ℝ) ∈ carrier
  physical_zero_common_address : commonStageAddress 0 = (0 : CommonLayer)
  positive_layer_mem : ∀ n : PositiveLayer,
    originalPositiveRealIndex n ∈ carrier
  positive_layer_common_address : ∀ n : PositiveLayer,
    entropyLayerAddress n = commonStageAddress (originalPositiveIndex n)
  every_positive_index_is_positive_layer : ∀ r : ℝ, r ∈ carrier → 0 < r →
    ∃ n : PositiveLayer, r = originalPositiveRealIndex n
  every_finite_common_layer_has_original_index : ∀ k : ℕ,
    (k : ℝ) ∈ carrier ∧ commonStageAddress k = (k : CommonLayer)
  original_carrier_order_embedding :
    {r : ℝ // r ∈ originalLayerIndexSet} ↪o CommonLayer
  original_carrier_join_preserved : ∀ r s : {x : ℝ // x ∈ originalLayerIndexSet},
    originalLayerCarrierOrderEmbedding (r ⊔ s) =
      originalLayerCarrierOrderEmbedding r ⊔ originalLayerCarrierOrderEmbedding s
  original_carrier_meet_preserved : ∀ r s : {x : ℝ // x ∈ originalLayerIndexSet},
    originalLayerCarrierOrderEmbedding (r ⊓ s) =
      originalLayerCarrierOrderEmbedding r ⊓ originalLayerCarrierOrderEmbedding s

/-- 物理0と全正層を含む可算添字carrierを具体的に構成する。 -/
noncomputable def c6Theorem15LayerAdapter : C6Theorem15LayerAdapter where
  carrier := originalLayerIndexSet
  carrier_eq_original := rfl
  carrier_countable := originalLayerIndexSet_countable
  carrier_nonnegative := originalLayerIndexSet_nonnegative
  physical_zero_mem := ⟨0, by norm_num⟩
  physical_zero_common_address := rfl
  positive_layer_mem := by
    intro n
    refine ⟨originalPositiveIndex n, ?_⟩
    simp [originalPositiveRealIndex, originalPositiveIndex]
  positive_layer_common_address := by
    intro n
    rfl
  every_positive_index_is_positive_layer := by
    intro r hr hpos
    rw [originalLayerIndexSet] at hr
    rcases hr with ⟨a, ha⟩
    have ha_pos : 0 < a := by
      have : (0 : ℝ) < (a : ℝ) := by simpa [ha] using hpos
      exact_mod_cast this
    refine ⟨a - 1, ?_⟩
    dsimp [originalPositiveRealIndex, originalPositiveIndex]
    rw [← ha]
    congr 1
    omega
  every_finite_common_layer_has_original_index := by
    intro k
    constructor
    · exact ⟨k, rfl⟩
    · rfl
  original_carrier_order_embedding := originalLayerCarrierOrderEmbedding
  original_carrier_join_preserved := originalLayerCarrierOrderEmbedding_sup
  original_carrier_meet_preserved := originalLayerCarrierOrderEmbedding_inf

/-- C3の段階束とC6の候補束は定義上同じ型である。 -/
theorem stageAtom_eq_commonLayer : Atom = CommonLayer := rfl

/-- C3の第n段が使う中心の層番号は、C2の正層番号と一致する。 -/
theorem averagePresentation_center_uses_entropy_layer (n : PositiveLayer) :
    (averagePresentation n).centerRepresentation
        (averagePresentation n).supportLub =
      representation (entropyLayerAddress n) := by
  simpa [entropyLayerAddress, originalPositiveIndex] using
    (averagePresentation_center n)

/-- C3のDirac平均場の実際の支持上限は、共通束の該当有限段そのもの。 -/
theorem averagePresentation_supportLub_is_commonStage (n : ℕ) :
    (averagePresentation n).supportLub = commonStageAddress (n + 1) := rfl

/-- C3の中心列は共通束の単調表象 `(k/(k+1))` に沿う。
正層k=n+1なので、これは `(n+1)/(n+2)` である。 -/
theorem averagePresentation_center_common_formula (n : PositiveLayer) :
    (averagePresentation n).centerRepresentation
        (averagePresentation n).supportLub =
      ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) := by
  rw [averagePresentation_center]
  simp [representation]

/-- 元のH-stage列が使う二次谷の中心も同じ共通束表象を使う。 -/
theorem hStageSequence_center_is_commonStage_representation (n : ℕ) :
    (hStageSequence n).center =
      representation (commonStageAddress (n + 1)) := by
  rw [hStageSequence_center]
  rfl

/-- C3平均場中心とC2正層から得る中心は、同じ共通段階表象である。 -/
theorem averagePresentation_center_eq_hStageSequence_center
    (n : PositiveLayer) :
    (averagePresentation n).centerRepresentation
        (averagePresentation n).supportLub =
      (hStageSequence n).center := by
  rw [averagePresentation_center_uses_entropy_layer,
    entropyLayerAddress_eq_commonStageAddress_succ,
    hStageSequence_center_is_commonStage_representation]

/-- C2の正層は、共通束の有限正層・原文の正実数添字・幾何重みを
一つの証人で結ぶ。最上位元は実数層添字へ写さない。 -/
structure C6C2PositiveLayerAdapter (n : PositiveLayer) where
  commonAddress : CommonLayer
  commonAddress_eq : commonAddress = entropyLayerAddress n
  commonAddress_finite : commonAddress ≠ (⊤ : CommonLayer)
  commonAddress_positive : 0 < commonAddress.untopD 0
  originalRealIndex : ℝ
  originalRealIndex_eq : originalRealIndex = originalPositiveRealIndex n
  originalRealIndex_positive : 0 < originalRealIndex
  realIndex_agrees_with_address :
    ((commonAddress.untopD 0 : ℕ) : ℝ) = originalRealIndex
  commonWeight_agrees : commonEntropyWeight commonAddress = layerWeight n

noncomputable def c6C2PositiveLayerAdapter
    (n : PositiveLayer) : C6C2PositiveLayerAdapter n where
  commonAddress := entropyLayerAddress n
  commonAddress_eq := rfl
  commonAddress_finite := entropyLayerAddress_ne_top n
  commonAddress_positive := entropyLayerAddress_pos n
  originalRealIndex := originalPositiveRealIndex n
  originalRealIndex_eq := rfl
  originalRealIndex_positive := originalPositiveRealIndex_pos n
  realIndex_agrees_with_address := by
    change ((originalPositiveIndex n : ℕ) : ℝ) = originalPositiveRealIndex n
    rfl
  commonWeight_agrees := commonEntropyWeight_matches_C2 n

/-- 同じ段adapterから、C2正層の非物理添字・原文実数添字・重みを取り出せる。 -/
theorem c6C2PositiveLayerAdapter_nonempty (n : PositiveLayer) :
    Nonempty (C6C2PositiveLayerAdapter n) :=
  ⟨c6C2PositiveLayerAdapter n⟩

/-- C2の中間正層、16のNat添字、C4/C5の底・最上位Bool層を
同一のWithTop ℕ束へ配置するS0の層接続証人。 -/
structure C6CommonLayerAdapter (n : ℕ) where
  c2_positive_layer : C6C2PositiveLayerAdapter n
  theorem15_layer_carrier : C6Theorem15LayerAdapter
  c2_address_is_stage_succ :
    c2_positive_layer.commonAddress = commonStageAddress (n + 1)
  c1_positive_addresses_injective : Function.Injective entropyLayerAddress
  c1_positive_addresses_monotone : Monotone entropyLayerAddress
  c1_positive_order_embedding : PositiveLayer ↪o CommonLayer
  c3_stage_order_embedding : ℕ ↪o CommonLayer
  c1_join_preserved : ∀ a b : PositiveLayer,
    entropyLayerAddress (a ⊔ b) = entropyLayerAddress a ⊔ entropyLayerAddress b
  c1_meet_preserved : ∀ a b : PositiveLayer,
    entropyLayerAddress (a ⊓ b) = entropyLayerAddress a ⊓ entropyLayerAddress b
  c3_join_preserved : ∀ a b : ℕ,
    commonStageAddress (a ⊔ b) = commonStageAddress a ⊔ commonStageAddress b
  c3_meet_preserved : ∀ a b : ℕ,
    commonStageAddress (a ⊓ b) = commonStageAddress a ⊓ commonStageAddress b
  c4c5_order_embedding : Layer ↪o CommonLayer
  c4c5_join_preserved : ∀ a b : Layer,
    operationalLayerAddress (a ⊔ b) =
      operationalLayerAddress a ⊔ operationalLayerAddress b
  c4c5_meet_preserved : ∀ a b : Layer,
    operationalLayerAddress (a ⊓ b) =
      operationalLayerAddress a ⊓ operationalLayerAddress b
  c1_common_weight_agrees : ∀ p : PositiveLayer,
    commonEntropyWeight (entropyLayerAddress p) = layerWeight p
  c1_positive_weights_sum_to_one :
    (∑' p : PositiveLayer, commonEntropyWeight (entropyLayerAddress p)) = 1
  nat_index_nonempty : ∃ k : ℕ, True
  nat_index_directed : ∀ i j : ℕ, ∃ k : ℕ,
    commonStageAddress i ≤ commonStageAddress k ∧
    commonStageAddress j ≤ commonStageAddress k
  nat_index_no_maximum : ∀ i : ℕ, ∃ j : ℕ,
    commonStageAddress i < commonStageAddress j
  c4c5_bottom_agrees : operationalLayerAddress false = (⊥ : CommonLayer)
  c4c5_top_agrees : operationalLayerAddress true = (⊤ : CommonLayer)
  c4c5_map_monotone : Monotone operationalLayerAddress
  c4c5_map_injective : Function.Injective operationalLayerAddress
  c2_layer_separated_from_bottom :
    c2_positive_layer.commonAddress ≠ operationalLayerAddress false
  c2_layer_separated_from_top :
    c2_positive_layer.commonAddress ≠ operationalLayerAddress true

noncomputable def c6CommonLayerAdapter (n : ℕ) : C6CommonLayerAdapter n where
  c2_positive_layer := c6C2PositiveLayerAdapter n
  theorem15_layer_carrier := c6Theorem15LayerAdapter
  c2_address_is_stage_succ := by
    exact entropyLayerAddress_eq_commonStageAddress_succ n
  c1_positive_addresses_injective := entropyLayerAddress_injective
  c1_positive_addresses_monotone := entropyLayerAddress_monotone
  c1_positive_order_embedding := entropyLayerOrderEmbedding
  c3_stage_order_embedding := commonStageOrderEmbedding
  c1_join_preserved := entropyLayerAddress_sup
  c1_meet_preserved := entropyLayerAddress_inf
  c3_join_preserved := commonStageAddress_sup
  c3_meet_preserved := commonStageAddress_inf
  c4c5_order_embedding := operationalLayerOrderEmbedding
  c4c5_join_preserved := operationalLayerAddress_sup
  c4c5_meet_preserved := operationalLayerAddress_inf
  c1_common_weight_agrees := commonEntropyWeight_matches_C2
  c1_positive_weights_sum_to_one := commonEntropyWeight_positiveLayer_tsum
  nat_index_nonempty := ⟨0, trivial⟩
  nat_index_directed := commonStageAddress_directed
  nat_index_no_maximum := commonStageAddress_no_maximal
  c4c5_bottom_agrees := operationalLayerAddress_bottom
  c4c5_top_agrees := operationalLayerAddress_top
  c4c5_map_monotone := operationalLayerAddress_monotone
  c4c5_map_injective := operationalLayerAddress_injective
  c2_layer_separated_from_bottom := by
    intro h
    have hzero : (c6C2PositiveLayerAdapter n).commonAddress = 0 := by
      simpa [operationalLayerAddress] using h
    have haddress : entropyLayerAddress n = 0 := by
      simpa [c6C2PositiveLayerAdapter] using hzero
    exact (entropyLayerAddress_not_physical_bottom n) haddress
  c2_layer_separated_from_top := by
    intro h
    have htop : (c6C2PositiveLayerAdapter n).commonAddress = ⊤ := by
      simpa [operationalLayerAddress] using h
    exact (c6C2PositiveLayerAdapter n).commonAddress_finite htop

/-- S7のC3段階を共通束へ接続する証明パッケージ。
平均場の原子・支持・枝・LUBを同じ正層アドレスへ送り、
同じH-stageを使う21段階情報証明を保持する。 -/
structure C6C3StageAdapter (n : ℕ) where
  c2PositiveLayer : C6C2PositiveLayerAdapter n
  commonAddress : CommonLayer
  sourceLayer_address :
    (Tomabechi.Consistency.C3.averagePresentation n).sourceLayer =
      {entropyLayerAddress n}
  measureSupport_address :
    (Tomabechi.Consistency.C3.averagePresentation n).measureSupport =
      {entropyLayerAddress n}
  supportLub_address :
    (Tomabechi.Consistency.C3.averagePresentation n).supportLub =
      entropyLayerAddress n
  branch_address :
    (Tomabechi.Consistency.C3.branchContext n).branch =
      {entropyLayerAddress n}
  symbolSupport_address :
    (Tomabechi.Consistency.C3.branchContext n).symbolSupport =
      {entropyLayerAddress n}
  center_address :
    (Tomabechi.Consistency.C3.averagePresentation n).centerRepresentation
      (Tomabechi.Consistency.C3.averagePresentation n).supportLub =
      representation (entropyLayerAddress n)
  stage_is_meanFieldHStage :
    (Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec =
      Tomabechi.Consistency.C3.valleySequence n

/-- 各C3平均場段階について、S7の順序・谷・情報接続を同時に提示する。 -/
noncomputable def c6C3StageAdapter (n : ℕ) : C6C3StageAdapter n where
  c2PositiveLayer := c6C2PositiveLayerAdapter n
  commonAddress := entropyLayerAddress n
  sourceLayer_address := by
    rw [Tomabechi.Consistency.C3.averagePresentation_sourceLayer]
    rfl
  measureSupport_address := by
    rw [Tomabechi.Consistency.C3.averagePresentation_measureSupport]
    rfl
  supportLub_address := by
    rw [Tomabechi.Consistency.C3.averagePresentation_supportLub]
    rfl
  branch_address := by
    simp [Tomabechi.Consistency.C3.branchContext, entropyLayerAddress,
      originalPositiveIndex]
  symbolSupport_address := by
    simp [Tomabechi.Consistency.C3.branchContext, entropyLayerAddress,
      originalPositiveIndex]
  center_address := averagePresentation_center_uses_entropy_layer n
  stage_is_meanFieldHStage := Tomabechi.Consistency.C3.hStageSequence_toStageValleySpec n

theorem c6C3StageAdapter_nonempty (n : ℕ) : Nonempty (C6C3StageAdapter n) :=
  ⟨c6C3StageAdapter n⟩

/-- 包装されたC6段階と同じ平均場・入力法則を使う21情報結論も各段で成立する。 -/
noncomputable def c6C3StageAdapter_has_stage_information (n : ℕ) :=
  Tomabechi.Consistency.C3.stageInformation n

/-- C3の21情報段階と19容量問題は、同じDirac入力・質量・決定作用から
全く同じ `X×(G×Y)` jointを生成する。ここでは値の一致ではなく測度の一致を示す。 -/
theorem c6C3_generatedJoint_eq_upperJoint (n : ℕ) :
    Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint
      (MeasureTheory.Measure.dirac ())
      Tomabechi.Consistency.C3.inputMass
      Tomabechi.Consistency.C3.inputMass_measurable
      (by
        filter_upwards with x
        exact fun g => Tomabechi.Consistency.C3.inputMass_nonneg x g)
      (by
        filter_upwards with x
        exact Tomabechi.Consistency.C3.inputMass_sum x)
      Tomabechi.Consistency.C3.inputAction
      Tomabechi.Consistency.C3.inputAction_measurable =
      Tomabechi.Consistency.C3.upperJoint := by
  unfold Tomabechi.Consistency.C3.upperJoint
  rfl

/-- 19の保存jointは、21情報段階が直接KL-CMIに渡すjointそのもの。 -/
theorem c6C3_capacityJoint_eq_stageJoint (n : ℕ) :
    Tomabechi.Consistency.C3.upperCMIPair.joint =
      Tomabechi.Theorem19_22.directActionGoalJoint
        (Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint
          (MeasureTheory.Measure.dirac ())
          Tomabechi.Consistency.C3.inputMass
          Tomabechi.Consistency.C3.inputMass_measurable
          (by
            filter_upwards with x
            exact fun g => Tomabechi.Consistency.C3.inputMass_nonneg x g)
          (by
            filter_upwards with x
            exact Tomabechi.Consistency.C3.inputMass_sum x)
          Tomabechi.Consistency.C3.inputAction
          Tomabechi.Consistency.C3.inputAction_measurable) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint
        (MeasureTheory.Measure.dirac ())
        Tomabechi.Consistency.C3.inputMass
        Tomabechi.Consistency.C3.inputMass_measurable
        (by
          filter_upwards with x
          exact fun g => Tomabechi.Consistency.C3.inputMass_nonneg x g)
        (by
          filter_upwards with x
          exact Tomabechi.Consistency.C3.inputMass_sum x)
        Tomabechi.Consistency.C3.inputAction
        Tomabechi.Consistency.C3.inputAction_measurable) := by
    rw [c6C3_generatedJoint_eq_upperJoint n]
    exact Tomabechi.Consistency.C3.upperJoint_isProbability
  rw [c6C3_generatedJoint_eq_upperJoint n]
  rfl

/-- 21情報入力で生成するjointから作る19 reference法則。 -/
noncomputable def c6C3_stageReference (n : ℕ) :
    MeasureTheory.Measure ((Unit × Bool) × Bool) := by
  let J := Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint
    (MeasureTheory.Measure.dirac ())
    Tomabechi.Consistency.C3.inputMass
    Tomabechi.Consistency.C3.inputMass_measurable
    (by
      filter_upwards with x
      exact fun g => Tomabechi.Consistency.C3.inputMass_nonneg x g)
    (by
      filter_upwards with x
      exact Tomabechi.Consistency.C3.inputMass_sum x)
    Tomabechi.Consistency.C3.inputAction
    Tomabechi.Consistency.C3.inputAction_measurable
  letI : MeasureTheory.IsProbabilityMeasure J := by
    rw [show J = Tomabechi.Consistency.C3.upperJoint from
      c6C3_generatedJoint_eq_upperJoint n]
    exact Tomabechi.Consistency.C3.upperJoint_isProbability
  exact Tomabechi.Theorem19_22.directCMIReference J

/-- 19のreference法則も21情報段階に渡される同じjointから生成される。 -/
theorem c6C3_capacityReference_eq_stageReference (n : ℕ) :
    Tomabechi.Consistency.C3.upperCMIPair.reference = c6C3_stageReference n := by
  rw [c6C3_stageReference]
  let J := Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint
    (MeasureTheory.Measure.dirac ())
    Tomabechi.Consistency.C3.inputMass
    Tomabechi.Consistency.C3.inputMass_measurable
    (by
      filter_upwards with x
      exact fun g => Tomabechi.Consistency.C3.inputMass_nonneg x g)
    (by
      filter_upwards with x
      exact Tomabechi.Consistency.C3.inputMass_sum x)
    Tomabechi.Consistency.C3.inputAction
    Tomabechi.Consistency.C3.inputAction_measurable
  letI : MeasureTheory.IsProbabilityMeasure J := by
    rw [show J = Tomabechi.Consistency.C3.upperJoint from
      c6C3_generatedJoint_eq_upperJoint n]
    exact Tomabechi.Consistency.C3.upperJoint_isProbability
  letI : MeasureTheory.IsProbabilityMeasure Tomabechi.Consistency.C3.upperJoint :=
    Tomabechi.Consistency.C3.upperJoint_isProbability
  change Tomabechi.Theorem19_22.directCMIReference
      Tomabechi.Consistency.C3.upperJoint =
    Tomabechi.Theorem19_22.directCMIReference J
  have hJ : J = Tomabechi.Consistency.C3.upperJoint :=
    c6C3_generatedJoint_eq_upperJoint n
  cases hJ
  rfl

/-- 21段階の直接KL情報スコアは19容量問題の同一joint/referenceのスコアである。 -/
noncomputable def c6C3_stageInformationScore (n : ℕ) : ℝ :=
  Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_directCMIScore
    (MeasureTheory.Measure.dirac ())
    Tomabechi.Consistency.C3.inputMass
    Tomabechi.Consistency.C3.inputMass_measurable
    (by
      filter_upwards with x
      exact fun g => Tomabechi.Consistency.C3.inputMass_nonneg x g)
    (by
      filter_upwards with x
      exact Tomabechi.Consistency.C3.inputMass_sum x)
    Tomabechi.Consistency.C3.inputAction
    Tomabechi.Consistency.C3.inputAction_measurable
    (by infer_instance)

theorem c6C3_stageInformationScore_eq_capacityScore (n : ℕ) :
    c6C3_stageInformationScore n =
      Tomabechi.Consistency.C3.cmiPairScore
        Tomabechi.Consistency.C3.upperCMIPair := by
  unfold c6C3_stageInformationScore
  let J := Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint
    (MeasureTheory.Measure.dirac ())
    Tomabechi.Consistency.C3.inputMass
    Tomabechi.Consistency.C3.inputMass_measurable
    (by
      filter_upwards with x
      exact fun g => Tomabechi.Consistency.C3.inputMass_nonneg x g)
    (by
      filter_upwards with x
      exact Tomabechi.Consistency.C3.inputMass_sum x)
    Tomabechi.Consistency.C3.inputAction
    Tomabechi.Consistency.C3.inputAction_measurable
  letI : MeasureTheory.IsProbabilityMeasure J := by
    rw [show J = Tomabechi.Consistency.C3.upperJoint from
      c6C3_generatedJoint_eq_upperJoint n]
    exact Tomabechi.Consistency.C3.upperJoint_isProbability
  letI : MeasureTheory.IsProbabilityMeasure Tomabechi.Consistency.C3.upperJoint :=
    Tomabechi.Consistency.C3.upperJoint_isProbability
  change (InformationTheory.klDiv
      (Tomabechi.Theorem19_22.directActionGoalJoint J)
      (Tomabechi.Theorem19_22.directCMIReference J)).toReal =
    (InformationTheory.klDiv
      (Tomabechi.Theorem19_22.directActionGoalJoint
        Tomabechi.Consistency.C3.upperJoint)
      (Tomabechi.Theorem19_22.directCMIReference
        Tomabechi.Consistency.C3.upperJoint)).toReal
  have hJ : J = Tomabechi.Consistency.C3.upperJoint :=
    c6C3_generatedJoint_eq_upperJoint n
  cases hJ
  rfl

/-- C3の段階情報と19容量計算を一つの保存adapterにまとめる。
同じ段階証明に対し、joint・reference法則・直接CMIスコアの一致を保持する。 -/
structure C6C3InformationAdapter (n : ℕ) where
  stageAdapter : C6C3StageAdapter n
  generatedJoint_is_capacityJoint :
    Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint
      (MeasureTheory.Measure.dirac ())
      Tomabechi.Consistency.C3.inputMass
      Tomabechi.Consistency.C3.inputMass_measurable
      (by
        filter_upwards with x
        exact fun g => Tomabechi.Consistency.C3.inputMass_nonneg x g)
      (by
        filter_upwards with x
        exact Tomabechi.Consistency.C3.inputMass_sum x)
      Tomabechi.Consistency.C3.inputAction
      Tomabechi.Consistency.C3.inputAction_measurable =
      Tomabechi.Consistency.C3.upperJoint
  reference_is_capacityReference :
    c6C3_stageReference n = Tomabechi.Consistency.C3.upperCMIPair.reference
  score_is_capacityScore :
    c6C3_stageInformationScore n =
      Tomabechi.Consistency.C3.cmiPairScore
        Tomabechi.Consistency.C3.upperCMIPair

/-- 実際のC3平均場段階と情報lawを用いる保存adapterの具体的証人。 -/
noncomputable def c6C3InformationAdapter (n : ℕ) : C6C3InformationAdapter n where
  stageAdapter := c6C3StageAdapter n
  generatedJoint_is_capacityJoint := c6C3_generatedJoint_eq_upperJoint n
  reference_is_capacityReference := (c6C3_capacityReference_eq_stageReference n).symm
  score_is_capacityScore := c6C3_stageInformationScore_eq_capacityScore n

theorem c6C3InformationAdapter_nonempty (n : ℕ) :
    Nonempty (C6C3InformationAdapter n) :=
  ⟨c6C3InformationAdapter n⟩

/-- N3のC3接続証人。同じ上位情報lawでは二値goalの条件付きentropyが正で、
各層に許容問題があり、stage 0の共通層addressでは異なる二方策がともに許容される。
そのstageには、法則保存済みのC3情報adapterも付く。 -/
theorem c6_N3_C3PositiveInformation_problemPair :
    (∃ g₁ g₂ : Bool, g₁ ≠ g₂) ∧
      0 < Tomabechi.Theorem21.conditionalGoalEntropy
        (MeasureTheory.Measure.dirac ()) Tomabechi.Consistency.C3.inputMass ∧
      (∀ a : Tomabechi.Consistency.C3.Atom, ∃ q : Bool,
        q ∈ Tomabechi.Consistency.C3.c3ProblemAdmissible a) ∧
      (∃ n : ℕ,
        entropyLayerAddress n = (1 : CommonLayer) ∧
        ∃ q₁ q₂ : Bool,
          q₁ ≠ q₂ ∧
          q₁ ∈ Tomabechi.Consistency.C3.c3ProblemAdmissible (entropyLayerAddress n) ∧
          q₂ ∈ Tomabechi.Consistency.C3.c3ProblemAdmissible (entropyLayerAddress n) ∧
          Nonempty (C6C3InformationAdapter n)) := by
  refine ⟨⟨false, true, Bool.false_ne_true⟩,
    Tomabechi.Consistency.C3.inputEntropy_pos, ?_, ?_⟩
  · intro a
    exact ⟨false, Tomabechi.Consistency.C3.c3Problem_false_admissible a⟩
  · refine ⟨0, ?_, ?_⟩
    · simp [entropyLayerAddress, originalPositiveIndex]
    · refine ⟨false, true, Bool.false_ne_true, ?_, ?_,
        c6C3InformationAdapter_nonempty 0⟩
      · exact Tomabechi.Consistency.C3.c3Problem_false_admissible _
      · have haddr : entropyLayerAddress 0 = (1 : Tomabechi.Consistency.C3.Atom) := by
          simp [entropyLayerAddress, originalPositiveIndex]
        rw [haddr]
        simp [Tomabechi.Consistency.C3.c3ProblemAdmissible]

/-- 各段の初期点は、その段の中心に厳密には届いていない。 -/
theorem c6C3_stageInitial_strict_below_center (n : ℕ) :
    (Tomabechi.Consistency.C3.hStageSequence n).initial <
      Tomabechi.Consistency.C3.representation (n + 1 : ℕ) := by
  induction n with
  | zero =>
      norm_num [Tomabechi.Consistency.C3.hStageSequence,
        Tomabechi.Consistency.C3.packageQuadraticStage,
        Tomabechi.Consistency.C3.valleySequence,
        Tomabechi.Consistency.C3.firstValley,
        Tomabechi.Consistency.C3.stageTime,
        Tomabechi.Theorem23.endpointCompatibleStageSequence,
        Tomabechi.Examples.Theorem23B.quadraticStage,
        Tomabechi.Consistency.C3.representation]
  | succ n ih =>
      rw [Tomabechi.Consistency.C3.hStageSequence_initial_recurrence n]
      have hprod :
          ((Tomabechi.Consistency.C3.hStageSequence n).initial -
            Tomabechi.Consistency.C3.representation (n + 1 : ℕ)) *
              Real.exp (-Tomabechi.Consistency.C3.stageDuration n) < 0 :=
        mul_neg_of_neg_of_pos (sub_neg.mpr ih)
          (Real.exp_pos (-Tomabechi.Consistency.C3.stageDuration n))
      have hmono : Tomabechi.Consistency.C3.representation (n + 1 : ℕ) ≤
          Tomabechi.Consistency.C3.representation (n + 2 : ℕ) := by
        apply Tomabechi.Consistency.C3.representation_monotone
        exact Nat.cast_le.mpr (by omega)
      linarith

/-- 各段の凍結軌道は同段中心へ厳密に進むため、次段初期値は
前段初期値から実際に変化する。 -/
theorem c6C3_stageEndpoint_strictly_moves (n : ℕ) :
    (Tomabechi.Consistency.C3.hStageSequence n).initial <
      (Tomabechi.Consistency.C3.hStageSequence (n + 1)).initial := by
  have holdcenter : (Tomabechi.Consistency.C3.hStageSequence n).initial <
      Tomabechi.Consistency.C3.representation (n + 1 : ℕ) :=
    c6C3_stageInitial_strict_below_center n
  have hdecay_lt : Real.exp (-Tomabechi.Consistency.C3.stageDuration n) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith [Tomabechi.Consistency.C3.stageDuration_pos n]
  rw [Tomabechi.Consistency.C3.hStageSequence_initial_recurrence n]
  have hrewrite :
      Tomabechi.Consistency.C3.representation (n + 1 : ℕ) +
          ((Tomabechi.Consistency.C3.hStageSequence n).initial -
            Tomabechi.Consistency.C3.representation (n + 1 : ℕ)) *
              Real.exp (-Tomabechi.Consistency.C3.stageDuration n) =
        (Tomabechi.Consistency.C3.hStageSequence n).initial +
          (Tomabechi.Consistency.C3.representation (n + 1 : ℕ) -
            (Tomabechi.Consistency.C3.hStageSequence n).initial) *
              (1 - Real.exp (-Tomabechi.Consistency.C3.stageDuration n)) := by ring
  rw [hrewrite]
  exact lt_add_of_pos_right _
    (mul_pos (sub_pos.mpr holdcenter) (sub_pos.mpr hdecay_lt))

/-- N4のC3証人をC6共通層へ接続する。各実stageアドレスは非終端で、
次段は真に新しく、各dwellは正、累積時刻は非有界、実端点は厳密に更新する。
各stageには同じ平均場列・情報law保存adapterが付随する。 -/
theorem c6_N4_C3_sameSequence_nonZeno :
    (∀ n : ℕ,
      entropyLayerAddress n = Tomabechi.Consistency.C3.layerU n ∧
      entropyLayerAddress n < (⊤ : CommonLayer) ∧
      ¬ Tomabechi.Consistency.C3.layerV (n + 1) ≤
        Tomabechi.Consistency.C3.layerU n ∧
      0 < Tomabechi.Consistency.C3.stageDuration n ∧
      Nonempty (C6C3InformationAdapter n)) ∧
      (∀ B : ℝ, ∃ n : ℕ, B < Tomabechi.Consistency.C3.stageTime n) ∧
      (∀ n : ℕ,
        (Tomabechi.Consistency.C3.hStageSequence n).initial <
          (Tomabechi.Consistency.C3.hStageSequence (n + 1)).initial) := by
  refine ⟨?_, ?_, c6C3_stageEndpoint_strictly_moves⟩
  · intro n
    refine ⟨?_, ?_, ?_, Tomabechi.Consistency.C3.stageDuration_pos n,
      c6C3InformationAdapter_nonempty n⟩
    · simp [entropyLayerAddress, originalPositiveIndex,
        Tomabechi.Consistency.C3.layerU]
    · rw [show entropyLayerAddress n = Tomabechi.Consistency.C3.layerU n by
        simp [entropyLayerAddress, originalPositiveIndex, Tomabechi.Consistency.C3.layerU]]
      exact Tomabechi.Consistency.C3.layerU_below_top n
    · exact Tomabechi.Consistency.C3.layerV_new n
  · intro B
    simpa [Tomabechi.Consistency.C3.stageTime] using
      Tomabechi.Consistency.C3.stageTime_unbounded B

/-- N6のC4共同証人を射影する。ひとつのC4一般接続定理が、異なる二履歴の
逆極限固定点と、同じ25共有SCM上で両値に正質量を持つ二値候補を同時に供給する。 -/
theorem c6_N6_C4_sharedSCM_twoHistories_candidateNonconstant :
    (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points.fixedPoint false).1 ≠
      (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points.fixedPoint true).1 ∧
    (∀ s : Bool,
      Tomabechi.Theorem16_25.Theorem25GlobalHistorySCM.candidateHasPositiveMass
        (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.toIndexed)
        false false s) := by
  have h := Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4_generalEntryConnection
  exact ⟨h.2.2.2.1, h.2.2.1⟩

/-- C2の正実数添字は、共通束側で物理層を除いた添字に対応する。 -/
theorem entropy_real_index_matches_address (n : PositiveLayer) :
    originalPositiveRealIndex n =
      ((n + 1 : ℕ) : ℝ) := by
  simp [originalPositiveRealIndex, originalPositiveIndex]

/-- C3の上位情報標本と、C4共有SCMの実外生入力を独立積で載せる共通確率空間。
それぞれの元lawを周辺lawとしてそのまま保ち、混合して同一視しない。 -/
noncomputable def c6C3C4CommonInputLaw :
    MeasureTheory.Measure
      (C4C5SCMInput × (Unit × (Bool × Bool))) :=
  c4RandomizedInputLaw.prod Tomabechi.Consistency.C3.upperJoint

theorem c6C3C4CommonInputLaw_isProbability :
    MeasureTheory.IsProbabilityMeasure c6C3C4CommonInputLaw := by
  letI : MeasureTheory.IsProbabilityMeasure c4RandomizedInputLaw :=
    c4RandomizedInputLaw_isProbability
  letI : MeasureTheory.IsProbabilityMeasure Tomabechi.Consistency.C3.upperJoint :=
    Tomabechi.Consistency.C3.upperJoint_isProbability
  exact MeasureTheory.Measure.prod.instIsProbabilityMeasure _ _

/-- 共通lawの第1周辺は元C4外生入力lawであり、質量も確率性も保存する。 -/
theorem c6C3C4CommonInputLaw_c4_marginal :
    MeasureTheory.Measure.map Prod.fst c6C3C4CommonInputLaw =
      c4RandomizedInputLaw := by
  letI : MeasureTheory.IsProbabilityMeasure Tomabechi.Consistency.C3.upperJoint :=
    Tomabechi.Consistency.C3.upperJoint_isProbability
  rw [c6C3C4CommonInputLaw, MeasureTheory.Measure.map_fst_prod]
  simp

/-- 同じ共通lawの第2周辺は元C3上位情報joint。 -/
theorem c6C3C4CommonInputLaw_c3_marginal :
    MeasureTheory.Measure.map Prod.snd c6C3C4CommonInputLaw =
      Tomabechi.Consistency.C3.upperJoint := by
  letI : MeasureTheory.IsProbabilityMeasure c4RandomizedInputLaw :=
    c4RandomizedInputLaw_isProbability
  rw [c6C3C4CommonInputLaw, MeasureTheory.Measure.map_snd_prod]
  simp

/-- C3情報とC4→C5履歴を一つの確率空間・一つの段添字上で使う部分adapter。
C4側では既存SCM履歴と全履歴制御law、C3側では元上位jointと段階情報adapterを保つ。 -/
structure C6C3C4CommonLawAdapter (n : ℕ) where
  law : MeasureTheory.Measure
      (C4C5SCMInput × (Unit × (Bool × Bool)))
  law_is_common_product : law = c6C3C4CommonInputLaw
  probability : MeasureTheory.IsProbabilityMeasure law
  c4_input_marginal :
    MeasureTheory.Measure.map Prod.fst law = c4RandomizedInputLaw
  c3_information_marginal :
    MeasureTheory.Measure.map Prod.snd law = Tomabechi.Consistency.C3.upperJoint
  common_layer_adapter : C6CommonLayerAdapter n
  /-- 非退化性のN1–N3/N5証人を、C3/C4共通lawと同じ接続adapterに保持する。 -/
  n1_c5_nonconstant_alive_trajectory :
    ∃ x : Tomabechi.Examples.Theorem27Op.E2,
      x ∉ Tomabechi.Examples.Theorem27Op.ringE 0 ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy x 0 s ∈
          Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive) ∧
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy x 0 0 ≠
        Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy x 0 1
  n2_common_layer_non_degenerate :
    (∃ k : ℕ, commonStageAddress k ≠ (⊤ : CommonLayer)) ∧
      (∀ i j : ℕ, ∃ k : ℕ,
        commonStageAddress i ≤ commonStageAddress k ∧
        commonStageAddress j ≤ commonStageAddress k) ∧
      (∀ i : ℕ, ∃ j : ℕ, commonStageAddress i < commonStageAddress j) ∧
      (∃ h : Bool, ∃ i : ℕ, ∃ x y : ℝ,
        commonStageAddress i ≠ (⊤ : CommonLayer) ∧ x ≠ y ∧
        x ∈ Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.carrier h i ∧
        y ∈ Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.carrier h i)
  n3_c3_positive_information_and_admissible_pair :
    (∃ g₁ g₂ : Bool, g₁ ≠ g₂) ∧
      0 < Tomabechi.Theorem21.conditionalGoalEntropy
        (MeasureTheory.Measure.dirac ()) Tomabechi.Consistency.C3.inputMass ∧
      (∀ a : Tomabechi.Consistency.C3.Atom, ∃ q : Bool,
        q ∈ Tomabechi.Consistency.C3.c3ProblemAdmissible a) ∧
      (∃ k : ℕ, entropyLayerAddress k = (1 : CommonLayer) ∧
        ∃ q₁ q₂ : Bool, q₁ ≠ q₂ ∧
          q₁ ∈ Tomabechi.Consistency.C3.c3ProblemAdmissible
            (entropyLayerAddress k) ∧
          q₂ ∈ Tomabechi.Consistency.C3.c3ProblemAdmissible
            (entropyLayerAddress k) ∧ Nonempty (C6C3InformationAdapter k))
  n5_c5_top_target_and_off_target :
    operationalLayerAddress false < (⊤ : CommonLayer) ∧
      ∃ x y : Tomabechi.Examples.Theorem27Op.E2,
        x ∈ Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive ∧
        y ∈ Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive ∧
        x ∈ Tomabechi.Theorem24_26.theorem26ZeroValueTarget
          Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive
          (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) 0 ∧
        y ∉ Tomabechi.Theorem24_26.theorem26ZeroValueTarget
          Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive
          (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) 0
  /-- N7の人口・履歴部分。空でない二主体と、全主体/履歴の実関係辺を保つ。 -/
  n7_two_distinct_subjects : ∃ d e : Bool, d ≠ e
  n7_every_subject_has_other_related_subject : ∀ h d : Bool,
    ∃ e a b r : Bool,
      e ≠ d ∧
        Tomabechi.Theorem16_25.theorem25_historyDependentPresenceRelations.relationEdge
          h d a r e b
  n7_subject_relation_graph_connected : ∀ h d e : Bool,
    Relation.ReflTransGen
      (fun x y : Bool =>
        x ≠ y ∧ ∃ a b r : Bool,
          Tomabechi.Theorem16_25.theorem25_historyDependentPresenceRelations.relationEdge
              h x a r y b) d e
  c4_history_marginal :
    MeasureTheory.Measure.map (fun w => c4HistoryFromInput w.1) law =
      c4RandomizedInputLaw.map c4HistoryFromInput
  c3_stage_information : C6C3InformationAdapter n
  c4_controls : ∀ h : Bool, Nonempty (C6C4C5ControlAdapter h)
  c3_positive_information :
    0 < Tomabechi.Theorem21.conditionalGoalEntropy
      (MeasureTheory.Measure.dirac ()) Tomabechi.Consistency.C3.inputMass
  c3_all_stages_nonempty : ∀ k : ℕ, Nonempty (C6C3InformationAdapter k)
  c3_nonZeno_stage_sequence :
    (∀ k : ℕ,
      entropyLayerAddress k = Tomabechi.Consistency.C3.layerU k ∧
      entropyLayerAddress k < (⊤ : CommonLayer) ∧
      ¬ Tomabechi.Consistency.C3.layerV (k + 1) ≤
        Tomabechi.Consistency.C3.layerU k ∧
      0 < Tomabechi.Consistency.C3.stageDuration k ∧
      Nonempty (C6C3InformationAdapter k)) ∧
      (∀ B : ℝ, ∃ k : ℕ, B < Tomabechi.Consistency.C3.stageTime k) ∧
      (∀ k : ℕ,
        (Tomabechi.Consistency.C3.hStageSequence k).initial <
        (Tomabechi.Consistency.C3.hStageSequence (k + 1)).initial)
  c4_nonconstant_candidate_same_scm :
    (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points.fixedPoint false).1 ≠
      (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points.fixedPoint true).1 ∧
    (∀ s : Bool,
      Tomabechi.Theorem16_25.Theorem25GlobalHistorySCM.candidateHasPositiveMass
        (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.toIndexed)
        false false s)
  c4_history_matches_same_scm :
    c4RandomizedInputLaw.map c4HistoryFromInput =
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
        (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory

/-- 二つの元lawとその既存履歴/情報証人を同じ product law に載せた具体adapter。 -/
noncomputable def c6C3C4CommonLawAdapter (n : ℕ) : C6C3C4CommonLawAdapter n where
  law := c6C3C4CommonInputLaw
  law_is_common_product := rfl
  probability := c6C3C4CommonInputLaw_isProbability
  c4_input_marginal := c6C3C4CommonInputLaw_c4_marginal
  c3_information_marginal := c6C3C4CommonInputLaw_c3_marginal
  common_layer_adapter := c6CommonLayerAdapter n
  n1_c5_nonconstant_alive_trajectory := c6_N1_C5Alive_nonconstantTrajectory
  n2_common_layer_non_degenerate := c6_N2_C4CommonLayer_nondegenerate
  n3_c3_positive_information_and_admissible_pair :=
    c6_N3_C3PositiveInformation_problemPair
  n5_c5_top_target_and_off_target :=
    c6_N5_C5LayerTarget_nonempty 0 (by norm_num)
  n7_two_distinct_subjects := ⟨false, true, Bool.false_ne_true⟩
  n7_every_subject_has_other_related_subject :=
    Tomabechi.Theorem16_25.theorem25_historyDependentPresenceRelations.everyExistenceIsRelated
  n7_subject_relation_graph_connected :=
    Tomabechi.Theorem16_25.theorem25_historyDependentPresenceRelations.relationGraphConnected
  c4_history_marginal := by
    calc
      _ = c4RandomizedInputLaw.map c4HistoryFromInput := by
        rw [show (fun w : C4C5SCMInput × (Unit × (Bool × Bool)) =>
            c4HistoryFromInput w.1) = c4HistoryFromInput ∘ Prod.fst by rfl,
          ← MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop),
          c6C3C4CommonInputLaw_c4_marginal]
      _ = _ := rfl
  c3_stage_information := c6C3InformationAdapter n
  c4_controls := fun h => ⟨c6C4C5ControlAdapter h⟩
  c3_positive_information := Tomabechi.Consistency.C3.inputEntropy_pos
  c3_all_stages_nonempty := c6C3InformationAdapter_nonempty
  c3_nonZeno_stage_sequence := c6_N4_C3_sameSequence_nonZeno
  c4_nonconstant_candidate_same_scm :=
    c6_N6_C4_sharedSCM_twoHistories_candidateNonconstant
  c4_history_matches_same_scm :=
    c6C4RandomizedLayerLaw_eq_sourceHistoryLaw_and_controls.1

theorem c6C3C4CommonLawAdapter_nonempty (n : ℕ) :
    Nonempty (C6C3C4CommonLawAdapter n) := ⟨c6C3C4CommonLawAdapter n⟩

/-- C4の同一共有SCMから、任意の主体・行為における25-A(2)自己過程を読む。
外生法則と履歴変数を変更せず、状態・出力の構造式もその主体・行為のものを使う。 -/
noncomputable def c6SubjectSelfProcessSCM (d a : Bool) :
    Tomabechi.Theorem16_25.Theorem25SelfProcessSCM Bool (Bool × Bool)
      Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma Bool Bool where
  exogenousLaw :=
    Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw
  inputHistory :=
    Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistory
  candidateVariable :=
    Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d a
  inputHistoryAEMeasurable :=
    Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistoryAEMeasurable
  candidateAEMeasurable :=
    Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariableAEMeasurable d a
  baselineEquation := fun h u =>
    (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
      Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u
        (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d a u))
  intervenedEquation := fun h s u =>
    (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
      Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u s)
  baselineAEMeasurable :=
    Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.baselineJointAEMeasurable d a
  intervenedAEMeasurable := fun h s =>
    Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.intervenedJointAEMeasurable d a h s

/-- 主体ごとの自己過程は、同じ共有SCMの外生法則・大域履歴をそのまま用いる。 -/
theorem c6SubjectSelfProcessSCM_source_identifications (d a : Bool) :
    (c6SubjectSelfProcessSCM d a).exogenousLaw =
        Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.exogenousLaw ∧
      (c6SubjectSelfProcessSCM d a).inputHistory =
        Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.globalHistory :=
  ⟨rfl, rfl⟩

/-- 全主体・全行為の25-A(2)。Unit引数は自己過程law modelの単一索引であり、
履歴はBoolのまま、介入law等式は全履歴・全候補について証明する。 -/
theorem c6SubjectSelfProcessSCM_condition25A2 (d a : Bool) :
    (c6SubjectSelfProcessSCM d a).toLawModel.Condition25A2 () := by
  apply (c6SubjectSelfProcessSCM d a).condition25A2
  · change ProbabilityTheory.IndepFun Prod.snd Prod.fst
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool)))
    exact (ProbabilityTheory.indepFun_prod (X := id) (Y := id)
      measurable_id measurable_id).symm
  · intro h s
    apply Subtype.ext
    change ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
        (fun u : Bool × Bool =>
          (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
            Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u s)) =
      ((ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
        (fun u : Bool × Bool =>
          (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.stateEquation d a h u,
            Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.outputEquation d a h u
              (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model.model.scm.candidateVariable d a u)))
    rw [MeasureTheory.Measure.map_congr]
    exact Filter.Eventually.of_forall fun u => by
      simp [Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model,
        Tomabechi.Theorem16_25.theorem25_intervalRandomizedMeasuredC3Model_fromFixedPoints,
        Tomabechi.Theorem16_25.Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints,
        Tomabechi.Theorem16_25.Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints,
        Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoint_coordinate,
        Tomabechi.Theorem16_25.theorem16_intervalGradientCenter]

end Tomabechi.Consistency.C6
