import Tomabechi.Consistency.ConsistencyR1_CommonLattice
import Tomabechi.Consistency.ConsistencyC6_CommonLayerData

/-!
# R1: C6有限/頂データを共通束全体へ再添字する

`layerProjection` を使い、旧 `WithTop ℕ` 上の依存状態・方策と定理24データを
`CommonConcept` 全体へ引き戻す。埋込み像では旧データを厳密に回収し、
共通束のどの真部分点にも定理24のデータを与える。これは24の入口移送であり、
26/27の全層条件やR1全体の統合完了を意味しない。
-/

noncomputable section

namespace Tomabechi.Consistency.R1

open Tomabechi.Consistency.C6
open Tomabechi.Theorem24_26

private theorem dependentValue_cast_eq
    {I : Type*} {State : I → Type*}
    (f : ∀ i, State i → ℝ) {i j : I} (h : j = i) (x : State i) :
    f j (cast (congrArg State h.symm) x) = f i x := by
  cases h
  rfl

private theorem dependentPolicy_cast_eq
    {I : Type*} {State Policy : I → Type*}
    (f : ∀ i, State i → Policy i) {i j : I} (h : j = i)
    (x : State i) :
    f j (cast (congrArg State h.symm) x) =
      cast (congrArg Policy h.symm) (f i x) := by
  cases h
  rfl

private theorem dependentTrajectory_cast_eq
    {I : Type*} {Policy State : I → Type*}
    (f : ∀ i, Policy i → State i → ℝ → ℝ → State i)
    {i j : I} (h : j = i) (π : Policy i) (x : State i) (T s : ℝ) :
    f j (cast (congrArg Policy h.symm) π)
        (cast (congrArg State h.symm) x) T s =
      cast (congrArg State h.symm) (f i π x T s) := by
  cases h
  rfl

private theorem dependentCost_cast_eq
    {I : Type*} {Policy State : I → Type*}
    (f : ∀ i, Policy i → State i → ℝ) {i j : I} (h : j = i)
    (π : Policy i) (x : State i) :
    f j (cast (congrArg Policy h.symm) π)
      (cast (congrArg State h.symm) x) = f i π x := by
  cases h
  rfl

private theorem dependentPredicate_cast_iff
    {I : Type*} {Policy State : I → Type*}
    (f : ∀ i, Policy i → State i → Prop) {i j : I} (h : j = i)
    (π : Policy i) (x : State i) :
    f j (cast (congrArg Policy h.symm) π)
      (cast (congrArg State h.symm) x) ↔ f i π x := by
  cases h
  rfl

/-- 新共通束の各点で使う、旧C6層番号に対応した状態型。 -/
abbrev commonConceptLayerState (x : CommonConcept) : Type :=
  C6LayeredState (layerProjection x)

/-- 新共通束の各点で使う、旧C6層番号に対応した方策型。 -/
abbrev commonConceptLayerPolicy (x : CommonConcept) : Type :=
  C6LayeredPolicy (layerProjection x)

/-- C6の定理24データを単調射影で共通束全体へ持ち上げたもの。 -/
def commonConceptTheorem24Data :
    Theorem24NonnegativeTimeData commonConceptLayerState commonConceptLayerPolicy where
  rho := c6LayeredNonnegativeTimeData.rho
  rho_pos := c6LayeredNonnegativeTimeData.rho_pos
  trajectory := fun a => c6LayeredNonnegativeTimeData.trajectory (layerProjection a)
  runningCost := fun a => c6LayeredNonnegativeTimeData.runningCost (layerProjection a)
  admissible := fun a => c6LayeredNonnegativeTimeData.admissible (layerProjection a)
  optimalValue := fun a => c6LayeredNonnegativeTimeData.optimalValue (layerProjection a)
  optimalPolicy := fun a => c6LayeredNonnegativeTimeData.optimalPolicy (layerProjection a)
  trajectory_initial := by
    intro a π x T hT hπ
    exact c6LayeredNonnegativeTimeData.trajectory_initial
      (layerProjection a) π x T hT hπ
  runningCost_nonnegative := by
    intro a π x t
    exact c6LayeredNonnegativeTimeData.runningCost_nonnegative
      (layerProjection a) π x t
  measurable_cost := by
    intro a x T π hT hπ
    exact c6LayeredNonnegativeTimeData.measurable_cost
      (layerProjection a) x T π hT hπ
  optimal_cost_integrable := by
    intro a x T hT
    exact c6LayeredNonnegativeTimeData.optimal_cost_integrable
      (layerProjection a) x T hT
  optimal_policy_admissible := by
    intro a x T hT
    exact c6LayeredNonnegativeTimeData.optimal_policy_admissible
      (layerProjection a) x T hT
  optimal_value_attained := by
    intro a x T hT
    exact c6LayeredNonnegativeTimeData.optimal_value_attained
      (layerProjection a) x T hT
  optimal_value_minimal := by
    intro a x T π hT hπ
    exact c6LayeredNonnegativeTimeData.optimal_value_minimal
      (layerProjection a) x T π hT hπ
  condition24A := by
    intro a ha x T hT π hπ
    apply c6LayeredNonnegativeTimeData.condition24A
      (layerProjection a) (layerProjection_lt_top_of_lt_top ha) x T hT π hπ

theorem commonConceptTheorem24Data_recovers_old_address
    (a : WithTop ℕ) :
    layerProjection (layerAddressEmbedding a) = a :=
  layerProjection_layerAddress a

/-- 新しい共通束の頂点は、旧データの頂添字へ射影される。 -/
theorem commonConcept_layerProjection_top :
    layerProjection (⊤ : CommonConcept) = ⊤ := by
  simpa [layerAddress_top] using
    (layerProjection_layerAddress (⊤ : WithTop ℕ))

/-- 新束の全真部分点で、持ち上げた24データが正価値と非恒等零方策を与える。 -/
theorem commonConceptTheorem24_all_proper_points :
    ∀ a (ha : a < (⊤ : CommonConcept))
      (x : commonConceptLayerState a) (T : ℝ), 0 ≤ T →
      0 < commonConceptTheorem24Data.optimalValue a x T ∧
        ¬ FeedbackPZS (commonConceptTheorem24Data.admissible a)
          (fun _ => futureLebesgueMeasure T)
          (fun π y t s => commonConceptTheorem24Data.runningCost a π
            (commonConceptTheorem24Data.trajectory a π y t s) s) x T :=
  theorem24_lower_conclusions_from_nonnegativeTimeData commonConceptTheorem24Data

theorem commonConceptTheorem24Data_recovers_old_finite_layer
    (a : WithTop ℕ) :
    HEq (commonConceptTheorem24Data.trajectory (layerAddressEmbedding a))
      (c6LayeredNonnegativeTimeData.trajectory a) := by
  unfold commonConceptTheorem24Data
  change HEq
    (c6LayeredNonnegativeTimeData.trajectory
      (layerProjection (layerAddress a)))
    (c6LayeredNonnegativeTimeData.trajectory a)
  rw [layerProjection_layerAddress a]

/-- 旧層を共通束へ埋め込んでも、最適値を保つ。 -/
theorem commonConceptTheorem24Data_recovers_old_optimalValue
    (a : WithTop ℕ) (x : C6LayeredState a) (T : ℝ) :
    commonConceptTheorem24Data.optimalValue (layerAddressEmbedding a)
        (cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm) x) T =
      c6LayeredNonnegativeTimeData.optimalValue a x T := by
  unfold commonConceptTheorem24Data
  change c6LayeredNonnegativeTimeData.optimalValue (layerProjection (layerAddress a))
      (cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm) x) T = _
  exact dependentValue_cast_eq
    (fun i y => c6LayeredNonnegativeTimeData.optimalValue i y T)
    (layerProjection_layerAddress a) x

/-- 旧層の方策・状態を型変換して埋め込んでも、瞬時費用を保つ。 -/
theorem commonConceptTheorem24Data_recovers_old_runningCost
    (a : WithTop ℕ) (π : C6LayeredPolicy a) (x : C6LayeredState a) (t : ℝ) :
    commonConceptTheorem24Data.runningCost (layerAddressEmbedding a)
        (cast (congrArg C6LayeredPolicy (layerProjection_layerAddress a).symm) π)
        (cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm) x) t =
      c6LayeredNonnegativeTimeData.runningCost a π x t := by
  unfold commonConceptTheorem24Data
  change c6LayeredNonnegativeTimeData.runningCost (layerProjection (layerAddress a))
      (cast (congrArg C6LayeredPolicy (layerProjection_layerAddress a).symm) π)
      (cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm) x) t = _
  exact dependentCost_cast_eq
    (fun i π y => c6LayeredNonnegativeTimeData.runningCost i π y t)
    (layerProjection_layerAddress a) π x

/-- 旧層の許容性も、共通束上の対応層で同値に保たれる。 -/
theorem commonConceptTheorem24Data_recovers_old_admissibility
    (a : WithTop ℕ) (π : C6LayeredPolicy a) (x : C6LayeredState a) (T : ℝ) :
    commonConceptTheorem24Data.admissible (layerAddressEmbedding a)
        (cast (congrArg C6LayeredPolicy (layerProjection_layerAddress a).symm) π)
        (cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm) x) T ↔
      c6LayeredNonnegativeTimeData.admissible a π x T := by
  unfold commonConceptTheorem24Data
  change c6LayeredNonnegativeTimeData.admissible (layerProjection (layerAddress a))
      (cast (congrArg C6LayeredPolicy (layerProjection_layerAddress a).symm) π)
      (cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm) x) T ↔ _
  exact dependentPredicate_cast_iff
    (fun i π y => c6LayeredNonnegativeTimeData.admissible i π y T)
    (layerProjection_layerAddress a) π x

/-- 旧層の最適方策も、層同値による型変換を除いてそのまま回収される。 -/
theorem commonConceptTheorem24Data_recovers_old_optimalPolicy
    (a : WithTop ℕ) (x : C6LayeredState a) (T : ℝ) :
    commonConceptTheorem24Data.optimalPolicy (layerAddressEmbedding a)
        (cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm) x) T =
      cast (congrArg C6LayeredPolicy (layerProjection_layerAddress a).symm)
        (c6LayeredNonnegativeTimeData.optimalPolicy a x T) := by
  unfold commonConceptTheorem24Data
  change c6LayeredNonnegativeTimeData.optimalPolicy
      (layerProjection (layerAddress a))
      (cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm) x) T = _
  exact dependentPolicy_cast_eq
    (fun i y => c6LayeredNonnegativeTimeData.optimalPolicy i y T)
    (layerProjection_layerAddress a) x

/-- 旧層の軌道も、状態・方策を型変換すれば共通束側で厳密に回収される。 -/
theorem commonConceptTheorem24Data_recovers_old_trajectory
    (a : WithTop ℕ) (π : C6LayeredPolicy a) (x : C6LayeredState a)
    (T s : ℝ) :
    commonConceptTheorem24Data.trajectory (layerAddressEmbedding a)
        (cast (congrArg C6LayeredPolicy (layerProjection_layerAddress a).symm) π)
        (cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm) x) T s =
      cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm)
        (c6LayeredNonnegativeTimeData.trajectory a π x T s) := by
  unfold commonConceptTheorem24Data
  change c6LayeredNonnegativeTimeData.trajectory
      (layerProjection (layerAddress a))
      (cast (congrArg C6LayeredPolicy (layerProjection_layerAddress a).symm) π)
      (cast (congrArg C6LayeredState (layerProjection_layerAddress a).symm) x) T s = _
  exact dependentTrajectory_cast_eq c6LayeredNonnegativeTimeData.trajectory
    (layerProjection_layerAddress a) π x T s

/-- 持ち上げた24データの頂点軌道は、旧C6頂点軌道そのものである。 -/
theorem commonConceptTheorem24Data_top_trajectory :
    HEq (commonConceptTheorem24Data.trajectory (⊤ : CommonConcept))
      (c6LayeredNonnegativeTimeData.trajectory (⊤ : WithTop ℕ)) := by
  exact commonConceptTheorem24Data_recovers_old_finite_layer ⊤

end Tomabechi.Consistency.R1
