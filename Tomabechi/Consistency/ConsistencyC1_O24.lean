import Tomabechi.Consistency.ConsistencyC1_HFlow
import Tomabechi.Consistency.ConsistencyC1_Consensus
import Tomabechi.Consistency.ConsistencyC1_ConsensusControl

/-!
# C1: 型を分けたSelf・Ego・TCZ adapter

Mini13 §2.4に合わせ、Selfは可能世界集合を選別する意味論的作用素、Egoは
状態と時刻から制御値を返す方策、TCZは状態空間の部分集合として定義する。
三者を同じスカラー値に潰さず、`linearFlow 3 0` の到達集合・feedback・目標集合を
それぞれ保存するadapterを構成する。
-/

noncomputable section

namespace Tomabechi.Consistency.ConsistencyC1O24

open Filter
open scoped Topology
open Tomabechi.Theorem1
open Tomabechi.Consistency.ConsistencyC1

/-- このモデルの基礎評価。 -/
def c1O24V0 (x _t : ℝ) : ℝ := 1 + x ^ 2

/-- Selfは可能世界集合を、基礎評価が閾値以下の世界へ絞る意味論的作用素。 -/
def c1O24Self (t : ℝ) (possibleWorlds : Set ℝ) : Set ℝ :=
  {x | x ∈ possibleWorlds ∧ c1O24V0 x t ≤ 1}

/-- Egoは閉ループflowが選択する制御方策。型は `(time, state) → control`。 -/
def c1O24Ego (t x : ℝ) : ℝ := (linearFlow 3 0).feedback x t

/-- flowが生成する閉到達集合。 -/
def c1O24Reachable (t₀ : ℝ) : Set ℝ :=
  closedLoopReachableSet (policyFlowReachableAt (linearFlow 3 0) Set.univ t₀)

/-- Selfが閉到達可能世界から選ぶ安定集合を、時刻ごとのTCZとして保持する。 -/
def c1O24TCZ (t₀ t : ℝ) : Set ℝ := c1O24Self t (c1O24Reachable t₀)

/-- Self、Ego、TCZを異なる型の三つ組としてまとめる。保存関係は値のフィールドで証明する。 -/
structure C1SelfEgoTCZ (t₀ : ℝ) where
  Self : ℝ → Set ℝ → Set ℝ
  Ego : ℝ → ℝ → ℝ
  TCZ : ℝ → Set ℝ
  reachable : Set ℝ
  flow : ClosedLoopPolicyFlow ℝ ℝ
  self_is_tcz : ∀ t, Self t reachable = TCZ t
  ego_is_flow_feedback : ∀ t x, Ego t x = flow.feedback x t
  tcz_is_self_slice : ∀ t, TCZ t = Self t reachable

/-- 実数H-flowから作る型付き表現三つ組。 -/
def linearFlowSelfEgoTCZ (t₀ : ℝ) : C1SelfEgoTCZ t₀ where
  Self := c1O24Self
  Ego := c1O24Ego
  TCZ := c1O24TCZ t₀
  reachable := c1O24Reachable t₀
  flow := linearFlow 3 0
  self_is_tcz := by intro t; rfl
  ego_is_flow_feedback := by intro t x; rfl
  tcz_is_self_slice := by intro t; rfl

theorem c1O24Reachable_eq_univ (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    c1O24Reachable t₀ = Set.univ := by
  exact linearFlow_closedReachable_univ 3 0 t₀ ht₀

/-- 全非負開始時刻で、Selfの選別結果であるTCZはちょうど目標点 `{0}`。 -/
theorem c1O24TCZ_eq_singleton (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    (linearFlowSelfEgoTCZ t₀).TCZ t = ({0} : Set ℝ) := by
  change c1O24Self t (c1O24Reachable t₀) = ({0} : Set ℝ)
  rw [c1O24Reachable_eq_univ t₀ ht₀]
  ext x
  simp [c1O24Self, c1O24V0]

/-- 型付き三つ組のEgoが出すfeedbackは、元のflowの許容制御である。 -/
theorem c1O24Ego_admissible (t₀ t x : ℝ) :
    (linearFlowSelfEgoTCZ t₀).flow.admissible ((linearFlowSelfEgoTCZ t₀).Ego t x) := by
  rw [(linearFlowSelfEgoTCZ t₀).ego_is_flow_feedback]
  exact (linearFlow 3 0).feedback_admissible x t

/-- Selfが選ぶTCZとEgoが実装するflowを同じ過程として結び、全未来時刻の指数評価を得る。
これはスカラーH-flowに対するO24の具体adapterである。 -/
theorem typedSelfEgoTCZ_exponential (x t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    ∀ t, t₀ ≤ t →
      Metric.infDist ((linearFlowSelfEgoTCZ t₀).flow.flow t₀ x t)
          ((linearFlowSelfEgoTCZ t₀).TCZ t) ≤
        |x| * Real.exp (-3 * (t - t₀)) := by
  have hthm := linearFlow_theorem1 3 0 t₀ x (by norm_num) ht₀
  intro t ht
  have hbound := hthm.2.1 t ht
  simpa [linearFlowSelfEgoTCZ, c1O24TCZ, c1O24Self, c1O24V0, c1O24Reachable] using hbound

open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Examples.Theorem2

/-- 二主体モデルのSelf作用素。可能世界を定理1/2共通残差の零集合へ絞る。 -/
def c1ConsensusSelf (t : ℝ) (possibleWorlds : Set AgentState) : Set AgentState :=
  {x | x ∈ possibleWorlds ∧ consensusV0 x t ≤ 1}

/-- 二主体モデルのEgo方策。値型は合意flowの制御型 `Unit`。 -/
def c1ConsensusEgo (x : AgentState) (t : ℝ) : Unit := consensusFlow.feedback x t

/-- 二主体flowが初期箱から生成する閉到達可能な可能世界集合。 -/
def c1ConsensusReachable (t₀ : ℝ) : Set AgentState :=
  closedLoopReachableSet (policyFlowReachableAt consensusFlow box t₀)

/-- Selfの像として定義する二主体TCZ。 -/
def c1ConsensusTCZ (t₀ t : ℝ) : Set AgentState :=
  c1ConsensusSelf t (c1ConsensusReachable t₀)

/-- Self・Ego・TCZを異なる型で持ち、同じ二主体flow上の保存関係を記録する。 -/
structure C1ConsensusSelfEgoTCZ (t₀ : ℝ) where
  Self : ℝ → Set AgentState → Set AgentState
  Ego : AgentState → ℝ → Unit
  TCZ : ℝ → Set AgentState
  reachable : Set AgentState
  flow : ClosedLoopPolicyFlow AgentState Unit
  self_is_tcz : ∀ t, Self t reachable = TCZ t
  ego_is_flow_feedback : ∀ x t, Ego x t = flow.feedback x t

/-- 定理1/2を接続した二主体H-flowの型付き表現。 -/
def consensusSelfEgoTCZAdapter (t₀ : ℝ) : C1ConsensusSelfEgoTCZ t₀ where
  Self := c1ConsensusSelf
  Ego := c1ConsensusEgo
  TCZ := c1ConsensusTCZ t₀
  reachable := c1ConsensusReachable t₀
  flow := consensusFlow
  self_is_tcz := by intro t; rfl
  ego_is_flow_feedback := by intro x t; rfl

/-- 型付きSelfが選ぶ二主体TCZは、定理2で使うsharedTCZそのものである。 -/
theorem c1ConsensusSelfTCZ_eq_shared
    (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    (consensusSelfEgoTCZAdapter t₀).TCZ t = DA.sharedTCZ box t := by
  change c1ConsensusSelf t (c1ConsensusReachable t₀) = DA.sharedTCZ box t
  unfold c1ConsensusReachable
  rw [consensusFlow_reachable_closure_eq_box t₀ ht₀]
  ext x
  constructor
  · rintro ⟨hx, hV⟩
    refine ⟨hx, ?_⟩
    change 1 + DA.potential x 0 ≤ 1 at hV
    have htime : DA.potential x 0 = DA.potential x t := by
      rw [sharedPotential_eq_coupling x hx 0, sharedPotential_eq_coupling x hx t]
    rw [htime] at hV
    change DA.potential x t = 0
    apply le_antisymm
    · linarith
    · rw [sharedPotential_eq_coupling x hx t]
      unfold γ
      positivity
  · rintro ⟨hx, hpot⟩
    refine ⟨hx, ?_⟩
    change 1 + DA.potential x 0 ≤ 1
    have htime : DA.potential x 0 = DA.potential x t := by
      rw [sharedPotential_eq_coupling x hx 0, sharedPotential_eq_coupling x hx t]
    rw [htime, hpot]
    norm_num

/-- 二主体の型付きEgoは同じH-flowが宣言する許容feedbackである。 -/
theorem c1ConsensusEgo_admissible (t₀ : ℝ) (x : AgentState) (t : ℝ) :
    (consensusSelfEgoTCZAdapter t₀).flow.admissible
      ((consensusSelfEgoTCZAdapter t₀).Ego x t) := by
  rw [(consensusSelfEgoTCZAdapter t₀).ego_is_flow_feedback]
  exact consensusFlow.feedback_admissible x t

/-- 最適化合意flow用のSelf作用素。可能世界を同じ時刻の評価水準で選ぶ。 -/
def c1OptimalConsensusSelf (t : ℝ) (possibleWorlds : Set AgentState) : Set AgentState :=
  {x | x ∈ possibleWorlds ∧ consensusV0 x t ≤ 1}

/-- 最適化合意flow用のEgo feedback。 -/
def c1OptimalConsensusEgo (x : AgentState) (t : ℝ) : ℝ :=
  consensusOptimalFlow.feedback x t

/-- 最大ゲインflowが初期箱から生成する閉到達集合。 -/
def c1OptimalConsensusReachable (t₀ : ℝ) : Set AgentState :=
  closedLoopReachableSet (policyFlowReachableAt consensusOptimalFlow box t₀)

/-- Selfが閉到達可能世界から選ぶ最適化flowのTCZ。 -/
def c1OptimalConsensusTCZ (t₀ t : ℝ) : Set AgentState :=
  c1OptimalConsensusSelf t (c1OptimalConsensusReachable t₀)

/-- 最適化flowの型付きSelf・Ego・TCZ adapter。各表現の型を分けて保持する。 -/
structure C1OptimalConsensusAdapter (t₀ : ℝ) where
  Self : ℝ → Set AgentState → Set AgentState
  Ego : AgentState → ℝ → ℝ
  TCZ : ℝ → Set AgentState
  initialSet : Set AgentState
  reachable : Set AgentState
  flow : ClosedLoopPolicyFlow AgentState ℝ
  reachable_is_closed_loop_closure :
    reachable = closedLoopReachableSet (policyFlowReachableAt flow initialSet t₀)
  self_is_tcz : ∀ t, Self t reachable = TCZ t
  ego_is_flow_feedback : ∀ x t, Ego x t = flow.feedback x t

/-- 有限地平最大ゲイン最適化と定理2時間変換評価を保持するO24三つ組。 -/
def optimalConsensusSelfEgoTCZAdapter (t₀ : ℝ) : C1OptimalConsensusAdapter t₀ where
  Self := c1OptimalConsensusSelf
  Ego := c1OptimalConsensusEgo
  TCZ := c1OptimalConsensusTCZ t₀
  initialSet := box
  reachable := c1OptimalConsensusReachable t₀
  flow := consensusOptimalFlow
  reachable_is_closed_loop_closure := rfl
  self_is_tcz := by intro t; rfl
  ego_is_flow_feedback := by intro x t; rfl

/-- 最適化flowのSelf選別TCZは、定理2と同じ二主体sharedTCZ。 -/
theorem c1OptimalConsensusTCZ_eq_shared (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    (optimalConsensusSelfEgoTCZAdapter t₀).TCZ t = DA.sharedTCZ box t := by
  change c1OptimalConsensusSelf t (c1OptimalConsensusReachable t₀) = DA.sharedTCZ box t
  unfold c1OptimalConsensusReachable
  rw [consensusOptimalFlow_reachable_closure_eq_box t₀ ht₀]
  ext x
  constructor
  · rintro ⟨hx, hV⟩
    refine ⟨hx, ?_⟩
    change 1 + DA.potential x 0 ≤ 1 at hV
    have htime : DA.potential x 0 = DA.potential x t := by
      rw [sharedPotential_eq_coupling x hx 0, sharedPotential_eq_coupling x hx t]
    rw [htime] at hV
    change DA.potential x t = 0
    apply le_antisymm
    · linarith
    · rw [sharedPotential_eq_coupling x hx t]
      unfold γ
      positivity
  · rintro ⟨hx, hpot⟩
    refine ⟨hx, ?_⟩
    change 1 + DA.potential x 0 ≤ 1
    have htime : DA.potential x 0 = DA.potential x t := by
      rw [sharedPotential_eq_coupling x hx 0, sharedPotential_eq_coupling x hx t]
    rw [htime, hpot]
    norm_num

/-- 二主体O24のEgoは有限地平argmin選択の開始点右極限と一致する。 -/
theorem c1OptimalConsensusEgo_is_argmin_right_limit
    (t₀ : ℝ) (x : AgentState) :
    Tendsto (fun s : ℝ => consensusSelectedHorizonControl (t₀, x) s)
      (𝓝[>] t₀) (𝓝 ((optimalConsensusSelfEgoTCZAdapter t₀).Ego x t₀)) := by
  simpa [consensusSelectedHorizonControl, c1OptimalConsensusEgo,
    optimalConsensusSelfEgoTCZAdapter] using
    consensusSelectedHorizonControl_rightLimit t₀ x

/-- 最適化flowのTCZへの距離評価は、型付きTCZを通して定理2の評価と一致する。 -/
theorem c1OptimalConsensusO24_distance
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) :
    Metric.infDist ((optimalConsensusSelfEgoTCZAdapter t₀).flow.flow t₀ x t)
        ((optimalConsensusSelfEgoTCZAdapter t₀).TCZ t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀)) := by
  rw [c1OptimalConsensusTCZ_eq_shared t₀ t ht₀]
  exact consensusOptimalFlow_theorem2_distance x hx t₀ t ht

end Tomabechi.Consistency.ConsistencyC1O24

end
