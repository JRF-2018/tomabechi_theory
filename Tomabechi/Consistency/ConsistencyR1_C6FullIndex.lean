import Tomabechi.Consistency.ConsistencyR1_C6Transport
import Tomabechi.Consistency.ConsistencyC6_TopActuator
import Tomabechi.Consistency.ConsistencyC6_ActuatorInputs
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# R1: 共通束の頂点を保存するC6層添字

全共通束点を単純に `layerProjection` で再添字すると、頂点状態型は旧C6頂点型と
定義的には一致しない。このファイルでは共通束頂点だけ旧頂添字を選び、真部分点では
射影層を選ぶ `fullCommonLayerIndex` を用いる。これにより頂点の旧層ラベルは保存できる。
-/

noncomputable section

namespace Tomabechi.Consistency.R1

open Tomabechi.Consistency.C6
open Tomabechi.Theorem24_26
open Tomabechi.Examples.Theorem27

private theorem fullIndex_dependentValue_cast_eq
    {I : Type*} {State : I → Type*}
    (f : ∀ i, State i → ℝ) {i j : I} (h : j = i) (x : State i) :
    f j (cast (congrArg State h.symm) x) = f i x := by
  cases h
  rfl

private theorem fullIndex_dependentPolicy_cast_eq
    {I : Type*} {State Policy : I → Type*}
    (f : ∀ i, State i → Policy i) {i j : I} (h : j = i)
    (x : State i) :
    f j (cast (congrArg State h.symm) x) =
      cast (congrArg Policy h.symm) (f i x) := by
  cases h
  rfl

private theorem fullIndex_dependentTrajectory_cast_eq
    {I : Type*} {Policy State : I → Type*}
    (f : ∀ i, Policy i → State i → ℝ → ℝ → State i)
    {i j : I} (h : j = i) (π : Policy i) (x : State i) (T s : ℝ) :
    f j (cast (congrArg Policy h.symm) π)
        (cast (congrArg State h.symm) x) T s =
      cast (congrArg State h.symm) (f i π x T s) := by
  cases h
  rfl

private theorem fullIndex_dependentCost_cast_eq
    {I : Type*} {Policy State : I → Type*}
    (f : ∀ i, Policy i → State i → ℝ) {i j : I} (h : j = i)
    (π : Policy i) (x : State i) :
    f j (cast (congrArg Policy h.symm) π)
      (cast (congrArg State h.symm) x) = f i π x := by
  cases h
  rfl

private theorem fullIndex_dependentPredicate_cast_iff
    {I : Type*} {Policy State : I → Type*}
    (f : ∀ i, Policy i → State i → Prop) {i j : I} (h : j = i)
    (π : Policy i) (x : State i) :
    f j (cast (congrArg Policy h.symm) π)
      (cast (congrArg State h.symm) x) ↔ f i π x := by
  cases h
  rfl

/-- 共通束頂点では旧頂、その他では射影された層番号を使う。 -/
def fullCommonLayerIndex (a : CommonConcept) : WithTop ℕ :=
  if a = ⊤ then ⊤ else layerProjection a

@[simp] theorem fullCommonLayerIndex_top :
    fullCommonLayerIndex (⊤ : CommonConcept) = ⊤ := by
  simp [fullCommonLayerIndex]

theorem fullCommonLayerIndex_eq_projection_of_lt_top
    {a : CommonConcept} (ha : a < ⊤) :
    fullCommonLayerIndex a = layerProjection a := by
  simp [fullCommonLayerIndex, ne_of_lt ha]

/-- The top-label exception in the full index agrees with the projection,
because the projection already sends the common-lattice top to the old top. -/
theorem fullCommonLayerIndex_eq_layerProjection (a : CommonConcept) :
    fullCommonLayerIndex a = layerProjection a := by
  by_cases ha : a = ⊤
  · subst a
    simp [fullCommonLayerIndex, commonConcept_layerProjection_top]
  · simp [fullCommonLayerIndex, ha]

/-- 旧有限層・旧頂は、補正後の新添字でそれぞれ同じアドレスへ戻る。 -/
theorem fullCommonLayerIndex_layerAddress (a : WithTop ℕ) :
    fullCommonLayerIndex (layerAddressEmbedding a) = a := by
  cases a with
  | top =>
      change fullCommonLayerIndex (⊤ : CommonConcept) = ⊤
      simp [fullCommonLayerIndex]
  | coe n =>
      have hn : diagonalLayer n ≠ (⊤ : CommonConcept) :=
        ne_of_lt (diagonalLayer_lt_top n)
      change fullCommonLayerIndex (diagonalLayer n) = (n : WithTop ℕ)
      simp [fullCommonLayerIndex, layerProjection_diagonal, hn]

abbrev fullCommonLayerState (a : CommonConcept) : Type :=
  C6LayeredState (fullCommonLayerIndex a)

abbrev fullCommonLayerPolicy (a : CommonConcept) : Type :=
  C6LayeredPolicy (fullCommonLayerIndex a)

theorem fullCommonTopState_eq_c6Top :
    fullCommonLayerState (⊤ : CommonConcept) = C6LayeredState (⊤ : WithTop ℕ) :=
  congrArg C6LayeredState fullCommonLayerIndex_top

/-- The same top address equality identifies the policy type, independently
of the state type. -/
theorem fullCommonTopPolicy_eq_c6Top :
    fullCommonLayerPolicy (⊤ : CommonConcept) =
      C6LayeredPolicy (⊤ : WithTop ℕ) :=
  congrArg C6LayeredPolicy fullCommonLayerIndex_top

/-- Explicit equivalence for transporting top states to the old C6 model. -/
def fullCommonTopStateEquiv :
    fullCommonLayerState (⊤ : CommonConcept) ≃
      C6LayeredState (⊤ : WithTop ℕ) :=
  Equiv.cast fullCommonTopState_eq_c6Top

/-- Explicit equivalence for transporting top policies to the old C6 model. -/
def fullCommonTopPolicyEquiv :
    fullCommonLayerPolicy (⊤ : CommonConcept) ≃
      C6LayeredPolicy (⊤ : WithTop ℕ) :=
  Equiv.cast fullCommonTopPolicy_eq_c6Top

@[simp] theorem fullCommonTopPolicyEquiv_symm_apply
    (π : C6LayeredPolicy (⊤ : WithTop ℕ)) :
    fullCommonTopPolicyEquiv.symm π =
      cast (congrArg C6LayeredPolicy
        (fullCommonLayerIndex_layerAddress ⊤).symm) π := by
  rfl

@[simp] theorem fullCommonTopStateEquiv_symm_apply
    (x : C6LayeredState (⊤ : WithTop ℕ)) :
    fullCommonTopStateEquiv.symm x =
      cast (congrArg C6LayeredState
        (fullCommonLayerIndex_layerAddress ⊤).symm) x := by
  rfl

/-- The state cast induces the product-domain equivalence required by a
nonnegative-time Markov feedback. This is only a type equivalence; measurable
transport is a separate obligation. -/
def fullCommonTopTimeStateEquiv :
    (Set.Ici (0 : ℝ) × fullCommonLayerState (⊤ : CommonConcept)) ≃
      (Set.Ici (0 : ℝ) × C6LayeredState (⊤ : WithTop ℕ)) :=
  Equiv.prodCongr (Equiv.refl _) fullCommonTopStateEquiv

/-- Pull the old C6 top metric back along the state equivalence, so distances
are unchanged by the common-concept top cast. -/
instance fullCommonTopPseudoMetricSpace :
    PseudoMetricSpace (fullCommonLayerState (⊤ : CommonConcept)) where
  dist x y := dist (fullCommonTopStateEquiv x) (fullCommonTopStateEquiv y)
  dist_self x := by simp
  dist_comm x y := by simp [dist_comm]
  dist_triangle x y z := by
    simpa using dist_triangle (fullCommonTopStateEquiv x)
      (fullCommonTopStateEquiv y) (fullCommonTopStateEquiv z)

/-- Use the Borel σ-algebra of the pulled-back top metric. -/
instance fullCommonTopMeasurableSpace :
    MeasurableSpace (fullCommonLayerState (⊤ : CommonConcept)) :=
  borel (fullCommonLayerState (⊤ : CommonConcept))

instance fullCommonTopBorelSpace :
    BorelSpace (fullCommonLayerState (⊤ : CommonConcept)) := ⟨rfl⟩

/-- The top-state equivalence is an isometry for the pulled-back metric. -/
theorem fullCommonTopStateEquiv_isometry :
    Isometry fullCommonTopStateEquiv := by
  intro x y
  rw [edist_dist, edist_dist]
  rfl

/-- The state cast is measurable in both directions for the Borel structures
generated by the old and pulled-back metrics. -/
def fullCommonTopStateMeasurableEquiv :
    fullCommonLayerState (⊤ : CommonConcept) ≃ᵐ
      C6LayeredState (⊤ : WithTop ℕ) := by
  refine ⟨fullCommonTopStateEquiv, ?_, ?_⟩
  · exact fullCommonTopStateEquiv_isometry.continuous.measurable
  · have hsymm : Isometry fullCommonTopStateEquiv.symm := by
      intro x y
      rw [edist_dist, edist_dist]
      apply congrArg ENNReal.ofReal
      change dist (fullCommonTopStateEquiv
          (fullCommonTopStateEquiv.symm x))
          (fullCommonTopStateEquiv
            (fullCommonTopStateEquiv.symm y)) = dist x y
      simp
    exact hsymm.continuous.measurable

/-- Measurable product-domain equivalence for the nonnegative-time feedback
action. -/
def fullCommonTopTimeStateMeasurableEquiv :
    (Set.Ici (0 : ℝ) × fullCommonLayerState (⊤ : CommonConcept)) ≃ᵐ
      (Set.Ici (0 : ℝ) × C6LayeredState (⊤ : WithTop ℕ)) :=
  (MeasurableEquiv.refl (Set.Ici (0 : ℝ))).prodCongr
    fullCommonTopStateMeasurableEquiv

private theorem nonnegativeTimeFeedback_ext
    {S C : Type*} [MeasurableSpace S] [MeasurableSpace C]
    {f g : NonnegativeTimeBorelMarkovFeedback S C}
    (h : f.action = g.action) : f = g := by
  cases f
  cases g
  simp_all

/-- Conjugating a Borel Markov feedback by the top-state measurable
equivalence preserves Borel measurability in both directions. -/
def fullCommonTopMarkovFeedbackEquiv :
    NonnegativeTimeBorelMarkovFeedback
        (fullCommonLayerState (⊤ : CommonConcept)) E2 ≃
      NonnegativeTimeBorelMarkovFeedback
        (C6LayeredState (⊤ : WithTop ℕ)) E2 where
  toFun f :=
    { action := f.action ∘ fullCommonTopTimeStateMeasurableEquiv.symm
      measurable_action := f.measurable_action.comp
        fullCommonTopTimeStateMeasurableEquiv.symm.measurable }
  invFun f :=
    { action := f.action ∘ fullCommonTopTimeStateMeasurableEquiv
      measurable_action := f.measurable_action.comp
        fullCommonTopTimeStateMeasurableEquiv.measurable }
  left_inv f := by
    apply nonnegativeTimeFeedback_ext
    funext x
    simp [Function.comp_def]
  right_inv f := by
    apply nonnegativeTimeFeedback_ext
    funext x
    simp [Function.comp_def]

/-- Transport the old top policy-to-feedback equivalence and compose it with
the measurable feedback cast. -/
noncomputable def fullCommonTopPolicyEquivDynamics :
    fullCommonLayerPolicy (⊤ : CommonConcept) ≃
      NonnegativeTimeBorelMarkovFeedback
        (fullCommonLayerState (⊤ : CommonConcept)) E2 :=
  fullCommonTopPolicyEquiv.trans
    (c6LayeredDynamics.policyEquiv.trans fullCommonTopMarkovFeedbackEquiv.symm)

/-- The chosen old optimal feedback, transported to the common-concept top. -/
noncomputable def fullCommonTopFeedback : fullCommonLayerPolicy ⊤ :=
  fullCommonTopPolicyEquiv.symm c6LayeredDynamics.feedback

/-- At every embedded old address, the state family is the original C6 family
up to the explicit address equality, including the old top state. -/
theorem fullCommonLayerState_oldAddress_eq (a : WithTop ℕ) :
    fullCommonLayerState (layerAddressEmbedding a) = C6LayeredState a := by
  change C6LayeredState (fullCommonLayerIndex (layerAddressEmbedding a)) = _
  rw [fullCommonLayerIndex_layerAddress]

/-- The existing top-layer theorem 27 kernel applies to the common-concept
state after its explicit top-index cast. This bridge preserves the old kernel's
scope; it does not assert that the theorem 26 dynamics certificate has been
transported to the full common-concept data record. -/
theorem fullCommon_top_theorem27_kernel
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) :
    c6LayeredTheorem27Conclusion
      (cast (congrArg C6LayeredState fullCommonLayerIndex_top) x) T hT := by
  exact c6LayeredData_theorem27_kernel
    (cast (congrArg C6LayeredState fullCommonLayerIndex_top) x) T hT

/-- The 27-A analytic inputs at the common-concept top are the existing
shared-model inputs evaluated on the same explicit state cast. -/
theorem fullCommon_top_actuatorInputs
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) :
    C6TopActuatorInputs
      (cast (congrArg C6LayeredState fullCommonLayerIndex_top) x) T hT := by
  exact c6TopActuatorInputs
    (cast (congrArg C6LayeredState fullCommonLayerIndex_top) x) T hT

/-- The casted top state also satisfies the exact 27-A input record stored in
the common model's original-premise signature. -/
theorem fullCommon_top_originalTopActuatorInputs
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) :
    TopActuatorInputs commonModel
      (cast (congrArg C6LayeredState fullCommonLayerIndex_top) x) T hT := by
  exact commonModel_topActuatorInputs
    (cast (congrArg C6LayeredState fullCommonLayerIndex_top) x) T hT

/-- C6の定理24データを、頂点例外を持つ共通束層添字へ引き戻す。 -/
def fullCommonTheorem24Data :
    Theorem24NonnegativeTimeData fullCommonLayerState fullCommonLayerPolicy where
  rho := c6LayeredNonnegativeTimeData.rho
  rho_pos := c6LayeredNonnegativeTimeData.rho_pos
  trajectory := fun a => c6LayeredNonnegativeTimeData.trajectory (fullCommonLayerIndex a)
  runningCost := fun a => c6LayeredNonnegativeTimeData.runningCost (fullCommonLayerIndex a)
  admissible := fun a => c6LayeredNonnegativeTimeData.admissible (fullCommonLayerIndex a)
  optimalValue := fun a => c6LayeredNonnegativeTimeData.optimalValue (fullCommonLayerIndex a)
  optimalPolicy := fun a => c6LayeredNonnegativeTimeData.optimalPolicy (fullCommonLayerIndex a)
  trajectory_initial := by
    intro a π x T hT hπ
    exact c6LayeredNonnegativeTimeData.trajectory_initial (fullCommonLayerIndex a) π x T hT hπ
  runningCost_nonnegative := by
    intro a π x t
    exact c6LayeredNonnegativeTimeData.runningCost_nonnegative (fullCommonLayerIndex a) π x t
  measurable_cost := by
    intro a x T π hT hπ
    exact c6LayeredNonnegativeTimeData.measurable_cost (fullCommonLayerIndex a) x T π hT hπ
  optimal_cost_integrable := by
    intro a x T hT
    exact c6LayeredNonnegativeTimeData.optimal_cost_integrable (fullCommonLayerIndex a) x T hT
  optimal_policy_admissible := by
    intro a x T hT
    exact c6LayeredNonnegativeTimeData.optimal_policy_admissible (fullCommonLayerIndex a) x T hT
  optimal_value_attained := by
    intro a x T hT
    exact c6LayeredNonnegativeTimeData.optimal_value_attained (fullCommonLayerIndex a) x T hT
  optimal_value_minimal := by
    intro a x T π hT hπ
    exact c6LayeredNonnegativeTimeData.optimal_value_minimal
      (fullCommonLayerIndex a) x T π hT hπ
  condition24A := by
    intro a ha x T hT π hπ
    have hindex : fullCommonLayerIndex a < ⊤ := by
      rw [fullCommonLayerIndex_eq_projection_of_lt_top ha]
      exact layerProjection_lt_top_of_lt_top ha
    exact c6LayeredNonnegativeTimeData.condition24A
      (fullCommonLayerIndex a) hindex x T hT π hπ

theorem fullCommonTheorem24_all_proper_points :
    ∀ a (ha : a < (⊤ : CommonConcept))
      (x : fullCommonLayerState a) (T : ℝ), 0 ≤ T →
      0 < fullCommonTheorem24Data.optimalValue a x T ∧
        ¬ FeedbackPZS (fullCommonTheorem24Data.admissible a)
          (fun _ => futureLebesgueMeasure T)
          (fun π y t s => fullCommonTheorem24Data.runningCost a π
            (fullCommonTheorem24Data.trajectory a π y t s) s) x T :=
  theorem24_lower_conclusions_from_nonnegativeTimeData fullCommonTheorem24Data

/-- The finite/top split in the existing C6 24-data is recovered exactly on
the common-lattice image, with only the dependent state cast made explicit. -/
theorem fullCommonTheorem24Data_recovers_old_optimalValue
    (a : WithTop ℕ) (x : C6LayeredState a) (T : ℝ) :
    fullCommonTheorem24Data.optimalValue (layerAddressEmbedding a)
        (cast (congrArg C6LayeredState
          (fullCommonLayerIndex_layerAddress a).symm) x) T =
      c6LayeredNonnegativeTimeData.optimalValue a x T := by
  unfold fullCommonTheorem24Data
  change c6LayeredNonnegativeTimeData.optimalValue
      (fullCommonLayerIndex (layerAddressEmbedding a))
      (cast (congrArg C6LayeredState
        (fullCommonLayerIndex_layerAddress a).symm) x) T = _
  exact fullIndex_dependentValue_cast_eq
    (fun i y => c6LayeredNonnegativeTimeData.optimalValue i y T)
    (fullCommonLayerIndex_layerAddress a) x

/-- The transported finite and top layers preserve their instantaneous costs. -/
theorem fullCommonTheorem24Data_recovers_old_runningCost
    (a : WithTop ℕ) (π : C6LayeredPolicy a) (x : C6LayeredState a) (t : ℝ) :
    fullCommonTheorem24Data.runningCost (layerAddressEmbedding a)
        (cast (congrArg C6LayeredPolicy
          (fullCommonLayerIndex_layerAddress a).symm) π)
        (cast (congrArg C6LayeredState
          (fullCommonLayerIndex_layerAddress a).symm) x) t =
      c6LayeredNonnegativeTimeData.runningCost a π x t := by
  unfold fullCommonTheorem24Data
  change c6LayeredNonnegativeTimeData.runningCost
      (fullCommonLayerIndex (layerAddressEmbedding a))
      (cast (congrArg C6LayeredPolicy
        (fullCommonLayerIndex_layerAddress a).symm) π)
      (cast (congrArg C6LayeredState
        (fullCommonLayerIndex_layerAddress a).symm) x) t = _
  exact fullIndex_dependentCost_cast_eq
    (fun i p y => c6LayeredNonnegativeTimeData.runningCost i p y t)
    (fullCommonLayerIndex_layerAddress a) π x

/-- Admissibility is invariant under the index-induced policy/state casts. -/
theorem fullCommonTheorem24Data_recovers_old_admissibility
    (a : WithTop ℕ) (π : C6LayeredPolicy a) (x : C6LayeredState a) (T : ℝ) :
    fullCommonTheorem24Data.admissible (layerAddressEmbedding a)
        (cast (congrArg C6LayeredPolicy
          (fullCommonLayerIndex_layerAddress a).symm) π)
        (cast (congrArg C6LayeredState
          (fullCommonLayerIndex_layerAddress a).symm) x) T ↔
      c6LayeredNonnegativeTimeData.admissible a π x T := by
  unfold fullCommonTheorem24Data
  change c6LayeredNonnegativeTimeData.admissible
      (fullCommonLayerIndex (layerAddressEmbedding a))
      (cast (congrArg C6LayeredPolicy
        (fullCommonLayerIndex_layerAddress a).symm) π)
      (cast (congrArg C6LayeredState
        (fullCommonLayerIndex_layerAddress a).symm) x) T ↔ _
  exact fullIndex_dependentPredicate_cast_iff
    (fun i p y => c6LayeredNonnegativeTimeData.admissible i p y T)
    (fullCommonLayerIndex_layerAddress a) π x

/-- The top-address admissibility predicate is preserved by the explicit
index casts, for every policy and state. -/
theorem fullCommonTheorem24Data_top_admissibility
    (π : C6LayeredPolicy (⊤ : WithTop ℕ))
    (x : C6LayeredState (⊤ : WithTop ℕ)) (T : ℝ) :
    fullCommonTheorem24Data.admissible (⊤ : CommonConcept)
        (cast (congrArg C6LayeredPolicy fullCommonLayerIndex_top.symm) π)
        (cast (congrArg C6LayeredState fullCommonLayerIndex_top.symm) x) T ↔
      c6LayeredNonnegativeTimeData.admissible (⊤ : WithTop ℕ) π x T := by
  convert (fullCommonTheorem24Data_recovers_old_admissibility
    (⊤ : WithTop ℕ) π x T) using 1
  have haddr : layerAddressEmbedding (⊤ : WithTop ℕ) = ⊤ := by
    change layerAddress (⊤ : WithTop ℕ) = ⊤
    exact layerAddress_top
  apply Iff.of_eq
  congr 1

/-- The explicit CommonConcept-index cast agrees with the inverse of the top
policy equivalence. -/
theorem fullCommonTopPolicyEquiv_symm_eq_explicitCast
    (π : C6LayeredPolicy (⊤ : WithTop ℕ)) :
    fullCommonTopPolicyEquiv.symm π =
      cast (congrArg C6LayeredPolicy fullCommonLayerIndex_top.symm) π := by
  rfl

/-- The corresponding state cast agrees with the inverse state equivalence. -/
theorem fullCommonTopStateEquiv_symm_eq_explicitCast
    (x : C6LayeredState (⊤ : WithTop ℕ)) :
    fullCommonTopStateEquiv.symm x =
      cast (congrArg C6LayeredState fullCommonLayerIndex_top.symm) x := by
  rfl

/-- General admissibility equivalence, now stated for the transported
CommonConcept policy and state themselves. -/
theorem fullCommonTop_admissible_iff_old
    (π : fullCommonLayerPolicy (⊤ : CommonConcept))
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) :
    fullCommonTheorem24Data.admissible ⊤ π x T ↔
      c6LayeredNonnegativeTimeData.admissible ⊤
        (fullCommonTopPolicyEquiv π) (fullCommonTopStateEquiv x) T := by
  have hp : π =
      cast (congrArg C6LayeredPolicy fullCommonLayerIndex_top.symm)
        (fullCommonTopPolicyEquiv π) :=
    (fullCommonTopPolicyEquiv.symm_apply_apply π).symm.trans
      (fullCommonTopPolicyEquiv_symm_eq_explicitCast
        (fullCommonTopPolicyEquiv π))
  have hx : x =
      cast (congrArg C6LayeredState fullCommonLayerIndex_top.symm)
        (fullCommonTopStateEquiv x) :=
    (fullCommonTopStateEquiv.symm_apply_apply x).symm.trans
      (fullCommonTopStateEquiv_symm_eq_explicitCast
        (fullCommonTopStateEquiv x))
  have hpold : fullCommonTopPolicyEquiv
      (cast (congrArg C6LayeredPolicy fullCommonLayerIndex_top.symm)
        (fullCommonTopPolicyEquiv π)) = fullCommonTopPolicyEquiv π :=
    (congrArg fullCommonTopPolicyEquiv hp).symm
  have hxold : fullCommonTopStateEquiv
      (cast (congrArg C6LayeredState fullCommonLayerIndex_top.symm)
        (fullCommonTopStateEquiv x)) = fullCommonTopStateEquiv x :=
    (congrArg fullCommonTopStateEquiv hx).symm
  rw [hp, hx]
  rw [hpold, hxold]
  exact fullCommonTheorem24Data_top_admissibility
    (fullCommonTopPolicyEquiv π) (fullCommonTopStateEquiv x) T

/-- Admissibility of the transported top feedback is exactly the old C6
admissibility after the explicit state and policy casts. -/
theorem fullCommonTopFeedback_admissible_iff
    (x : C6LayeredState (⊤ : WithTop ℕ)) (T : ℝ) :
    fullCommonTheorem24Data.admissible (⊤ : CommonConcept)
      fullCommonTopFeedback
      (fullCommonTopStateEquiv.symm x) T ↔
    c6LayeredNonnegativeTimeData.admissible (⊤ : WithTop ℕ)
      c6LayeredDynamics.feedback x T := by
  rw [fullCommonTopFeedback, fullCommonTopPolicyEquiv_symm_apply,
    fullCommonTopStateEquiv_symm_apply]
  exact fullCommonTheorem24Data_recovers_old_admissibility
    ⊤ c6LayeredDynamics.feedback x T

private theorem fullCommonTopData_rho_eq_old :
    fullCommonTheorem24Data.rho = c6LayeredNonnegativeTimeData.rho := rfl

private theorem fullCommonTopData_trajectory_eq_old
    (π : C6LayeredPolicy (⊤ : WithTop ℕ))
    (x : C6LayeredState (⊤ : WithTop ℕ)) (T s : ℝ) :
      fullCommonTheorem24Data.trajectory (⊤ : CommonConcept)
        (fullCommonTopPolicyEquiv.symm π) (fullCommonTopStateEquiv.symm x) T s =
      fullCommonTopStateEquiv.symm
        (c6LayeredNonnegativeTimeData.trajectory (⊤ : WithTop ℕ) π x T s) := by
  unfold fullCommonTheorem24Data
  change c6LayeredNonnegativeTimeData.trajectory
      (fullCommonLayerIndex (layerAddressEmbedding ⊤))
      (fullCommonTopPolicyEquiv.symm π) (fullCommonTopStateEquiv.symm x) T s = _
  exact fullIndex_dependentTrajectory_cast_eq
    c6LayeredNonnegativeTimeData.trajectory
    (fullCommonLayerIndex_layerAddress ⊤) π x T s

private theorem fullCommonTopData_runningCost_eq_old
    (π : C6LayeredPolicy (⊤ : WithTop ℕ))
    (x : C6LayeredState (⊤ : WithTop ℕ)) (t : ℝ) :
    fullCommonTheorem24Data.runningCost (⊤ : CommonConcept)
        (fullCommonTopPolicyEquiv.symm π) (fullCommonTopStateEquiv.symm x) t =
      c6LayeredNonnegativeTimeData.runningCost (⊤ : WithTop ℕ) π x t := by
  rw [fullCommonTopPolicyEquiv_symm_apply,
    fullCommonTopStateEquiv_symm_apply]
  simpa [layerAddressEmbedding, layerAddress] using
    fullCommonTheorem24Data_recovers_old_runningCost ⊤ π x t

/-- The controlled trajectory in the CommonConcept top is the inverse state
cast of the corresponding C6 trajectory, for every policy and initial state. -/
theorem fullCommonTop_trajectory_eq_old
    (π : fullCommonLayerPolicy (⊤ : CommonConcept))
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T s : ℝ) :
    fullCommonTheorem24Data.trajectory ⊤ π x T s =
      fullCommonTopStateEquiv.symm
        (c6LayeredNonnegativeTimeData.trajectory ⊤
          (fullCommonTopPolicyEquiv π) (fullCommonTopStateEquiv x) T s) := by
  simpa only [Equiv.symm_apply_apply] using
    fullCommonTopData_trajectory_eq_old
      (fullCommonTopPolicyEquiv π) (fullCommonTopStateEquiv x) T s

/-- The instantaneous running cost is preserved for every transported
policy and state. -/
theorem fullCommonTop_runningCost_eq_old
    (π : fullCommonLayerPolicy (⊤ : CommonConcept))
    (x : fullCommonLayerState (⊤ : CommonConcept)) (t : ℝ) :
    fullCommonTheorem24Data.runningCost ⊤ π x t =
      c6LayeredNonnegativeTimeData.runningCost ⊤
        (fullCommonTopPolicyEquiv π) (fullCommonTopStateEquiv x) t := by
  simpa only [Equiv.symm_apply_apply] using
    fullCommonTopData_runningCost_eq_old
      (fullCommonTopPolicyEquiv π) (fullCommonTopStateEquiv x) t

private theorem fullCommonTopData_optimalValue_eq_old
    (x : C6LayeredState (⊤ : WithTop ℕ)) (T : ℝ) :
    fullCommonTheorem24Data.optimalValue (⊤ : CommonConcept)
        (fullCommonTopStateEquiv.symm x) T =
      c6LayeredNonnegativeTimeData.optimalValue (⊤ : WithTop ℕ) x T := by
  rw [fullCommonTopStateEquiv_symm_apply]
  simpa [layerAddressEmbedding, layerAddress] using
    fullCommonTheorem24Data_recovers_old_optimalValue ⊤ x T

/-- Pull the old top alive region back to the CommonConcept vertex. -/
def fullCommonTopAlive : Set (fullCommonLayerState (⊤ : CommonConcept)) :=
  fullCommonTopStateEquiv ⁻¹' c6LayeredDynamics.alive

/-- The new zero-value target is exactly the inverse image of the old target.
This is the set-level bridge needed before transporting the Lyapunov distance
certificate. -/
theorem fullCommonTopTarget_mem_iff
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) :
    x ∈ theorem26ZeroValueTarget fullCommonTopAlive
        (fullCommonTheorem24Data.optimalValue ⊤) T ↔
      fullCommonTopStateEquiv x ∈ theorem26ZeroValueTarget
        c6LayeredDynamics.alive
        (c6LayeredNonnegativeTimeData.optimalValue ⊤) T := by
  simp only [theorem26ZeroValueTarget, Set.mem_inter_iff, Set.mem_setOf_eq,
    fullCommonTopAlive, Set.mem_preimage]
  have hvalue := fullCommonTopData_optimalValue_eq_old
    (fullCommonTopStateEquiv x) T
  have hvalue' : fullCommonTheorem24Data.optimalValue ⊤ x T =
      c6LayeredNonnegativeTimeData.optimalValue ⊤
        (fullCommonTopStateEquiv x) T := by
    simpa only [Equiv.symm_apply_apply] using hvalue
  constructor
  · rintro ⟨halive, hzero⟩
    refine ⟨halive, ?_⟩
    rw [hvalue'] at hzero
    exact hzero
  · rintro ⟨halive, hzero⟩
    refine ⟨halive, ?_⟩
    rw [hvalue']
    exact hzero

/-- The top-state equivalence maps the transported target onto the old target. -/
theorem fullCommonTopTarget_image (T : ℝ) :
    fullCommonTopStateEquiv '' theorem26ZeroValueTarget fullCommonTopAlive
        (fullCommonTheorem24Data.optimalValue ⊤) T =
      theorem26ZeroValueTarget c6LayeredDynamics.alive
        (c6LayeredNonnegativeTimeData.optimalValue ⊤) T := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (fullCommonTopTarget_mem_iff x T).mp hx
  · intro hy
    refine ⟨fullCommonTopStateEquiv.symm y, ?_, ?_⟩
    · exact (fullCommonTopTarget_mem_iff _ T).mpr (by simpa using hy)
    · simp

/-- Distances to corresponding top targets agree exactly under the pulled-back
metric; this transfers both quadratic Lyapunov distance bounds unchanged. -/
theorem fullCommonTop_infDist_target_eq_old
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) :
    Metric.infDist x (theorem26ZeroValueTarget fullCommonTopAlive
      (fullCommonTheorem24Data.optimalValue ⊤) T) =
    Metric.infDist (fullCommonTopStateEquiv x)
      (theorem26ZeroValueTarget c6LayeredDynamics.alive
        (c6LayeredNonnegativeTimeData.optimalValue ⊤) T) := by
  rw [← fullCommonTopTarget_image T]
  exact (Metric.infDist_image fullCommonTopStateEquiv_isometry).symm

/-- Membership in the alive region is preserved by the top-state cast. -/
theorem fullCommonTopAlive_mem_iff
    (x : fullCommonLayerState (⊤ : CommonConcept)) :
    x ∈ fullCommonTopAlive ↔ fullCommonTopStateEquiv x ∈ c6LayeredDynamics.alive :=
  Iff.rfl

/-- The transported closed-loop path is the cast of the old C6 path. -/
theorem fullCommonTopTrajectory_eq_old
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T s : ℝ) :
    fullCommonTheorem24Data.trajectory ⊤ fullCommonTopFeedback x T s =
      fullCommonTopStateEquiv.symm
        (c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback
          (fullCommonTopStateEquiv x) T s) := by
  simpa [fullCommonTopFeedback] using fullCommonTopData_trajectory_eq_old
    c6LayeredDynamics.feedback (fullCommonTopStateEquiv x) T s

/-- The CommonConcept vertex trajectory is exactly the C6 top path after
applying the state equivalence. -/
theorem fullCommonTopTrajectory_eq_c6TopPath
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T s : ℝ) :
    fullCommonTheorem24Data.trajectory ⊤ fullCommonTopFeedback x T s =
      fullCommonTopStateEquiv.symm
        (Tomabechi.Consistency.C6.c6TopPath
          (fullCommonTopStateEquiv x) T s) := by
  rw [fullCommonTopTrajectory_eq_old]
  rfl

/-- The CommonConcept Lyapunov candidate obtained by pulling back the old
top-layer candidate. -/
def fullCommonTopLyapunov
    (x : fullCommonLayerState (⊤ : CommonConcept)) (t : ℝ) : ℝ :=
  c6LayeredDynamics.W (fullCommonTopStateEquiv x) t

/-- Pulling back the old dynamics keeps the same Lyapunov value at every
transported state. -/
theorem fullCommonTopLyapunov_eq_old
    (x : fullCommonLayerState (⊤ : CommonConcept)) (t : ℝ) :
    fullCommonTopLyapunov x t =
      c6LayeredDynamics.W (fullCommonTopStateEquiv x) t := rfl

/-- The transported feedback remains optimal and its discounted running cost
integrable on the same alive top states. -/
theorem fullCommonTopFeedback_attains_optimum
    (x : C6LayeredState (⊤ : WithTop ℕ)) (T : ℝ)
    (hT : 0 ≤ T) (hx : x ∈ c6LayeredDynamics.alive) :
    fullCommonTheorem24Data.admissible (⊤ : CommonConcept)
      fullCommonTopFeedback (fullCommonTopStateEquiv.symm x) T ∧
    MeasureTheory.Integrable
      (fun s => theorem26DiscountWeight fullCommonTheorem24Data.rho T s *
        fullCommonTheorem24Data.runningCost (⊤ : CommonConcept)
          fullCommonTopFeedback
          (fullCommonTheorem24Data.trajectory (⊤ : CommonConcept)
            fullCommonTopFeedback (fullCommonTopStateEquiv.symm x) T s) s)
      (futureLebesgueMeasure T) ∧
    fullCommonTheorem24Data.optimalValue (⊤ : CommonConcept)
        (fullCommonTopStateEquiv.symm x) T =
      ∫ s, theorem26DiscountWeight fullCommonTheorem24Data.rho T s *
        fullCommonTheorem24Data.runningCost (⊤ : CommonConcept)
          fullCommonTopFeedback
          (fullCommonTheorem24Data.trajectory (⊤ : CommonConcept)
            fullCommonTopFeedback (fullCommonTopStateEquiv.symm x) T s) s
        ∂(futureLebesgueMeasure T) := by
  have hold := c6LayeredDynamics.feedback_attains_optimum x T hT hx
  refine ⟨(fullCommonTopFeedback_admissible_iff x T).2 hold.1, ?_, ?_⟩
  · have hcost :
        (fun s => theorem26DiscountWeight fullCommonTheorem24Data.rho T s *
          fullCommonTheorem24Data.runningCost (⊤ : CommonConcept)
            fullCommonTopFeedback
            (fullCommonTheorem24Data.trajectory (⊤ : CommonConcept)
              fullCommonTopFeedback (fullCommonTopStateEquiv.symm x) T s) s) =
        (fun s => theorem26DiscountWeight 1 T s *
          vectorSourceData.runningCost true c6LayeredDynamics.feedback
            (vectorSourceData.trajectory true c6LayeredDynamics.feedback x T s) s) := by
      funext s
      rw [fullCommonTopData_rho_eq_old, fullCommonTopFeedback,
        fullCommonTopData_trajectory_eq_old,
        fullCommonTopData_runningCost_eq_old]
      simp [c6LayeredData_top_runningCost_fun,
        c6LayeredData_top_trajectory_fun]
    rw [hcost]
    exact hold.2.1
  · have hcost :
        (fun s => theorem26DiscountWeight fullCommonTheorem24Data.rho T s *
          fullCommonTheorem24Data.runningCost (⊤ : CommonConcept)
            fullCommonTopFeedback
            (fullCommonTheorem24Data.trajectory (⊤ : CommonConcept)
              fullCommonTopFeedback (fullCommonTopStateEquiv.symm x) T s) s) =
        (fun s => theorem26DiscountWeight 1 T s *
          vectorSourceData.runningCost true c6LayeredDynamics.feedback
            (vectorSourceData.trajectory true c6LayeredDynamics.feedback x T s) s) := by
      funext s
      rw [fullCommonTopData_rho_eq_old, fullCommonTopFeedback,
        fullCommonTopData_trajectory_eq_old,
        fullCommonTopData_runningCost_eq_old]
      simp [c6LayeredData_top_runningCost_fun,
        c6LayeredData_top_trajectory_fun]
    rw [fullCommonTopData_optimalValue_eq_old, hcost]
    exact hold.2.2

/-- The complete theorem-26 certificate transported to the CommonConcept
vertex. Every field is pulled back through the same state isometry and the
same transported theorem-24 data. -/
def fullCommonTopDynamics :
    Theorem26NonnegativeTimeDynamics fullCommonTheorem24Data E2 where
  policyEquiv := fullCommonTopPolicyEquivDynamics
  feedback := fullCommonTopFeedback
  alive := fullCommonTopAlive
  feedback_attains_optimum := by
    intro x T hT hx
    have hold := fullCommonTopFeedback_attains_optimum
      (fullCommonTopStateEquiv x) T hT ((fullCommonTopAlive_mem_iff x).mp hx)
    simpa only [Equiv.symm_apply_apply] using hold
  W := fullCommonTopLyapunov
  ω := c6LayeredDynamics.ω
  c₁ := c6LayeredDynamics.c₁
  c₂ := c6LayeredDynamics.c₂
  rate := c6LayeredDynamics.rate
  c₁_pos := c6LayeredDynamics.c₁_pos
  c₂_pos := c6LayeredDynamics.c₂_pos
  rate_pos := c6LayeredDynamics.rate_pos
  trajectory_alive := by
    intro x T s hT hx hTs
    apply (fullCommonTopAlive_mem_iff _).mpr
    have hold := c6LayeredDynamics.trajectory_alive
      (fullCommonTopStateEquiv x) T s hT
      ((fullCommonTopAlive_mem_iff x).mp hx) hTs
    simpa [fullCommonTopTrajectory_eq_old] using hold
  target_nonempty := by
    intro T hT
    rcases c6LayeredDynamics.target_nonempty T hT with ⟨y, hy⟩
    refine ⟨fullCommonTopStateEquiv.symm y, ?_⟩
    exact (fullCommonTopTarget_mem_iff _ T).mpr (by simpa using hy)
  target_closed := by
    intro T hT
    have hset : theorem26ZeroValueTarget fullCommonTopAlive
        (fullCommonTheorem24Data.optimalValue ⊤) T =
      fullCommonTopStateEquiv ⁻¹' theorem26ZeroValueTarget
        c6LayeredDynamics.alive
        (c6LayeredNonnegativeTimeData.optimalValue ⊤) T := by
      ext x
      exact fullCommonTopTarget_mem_iff x T
    rw [hset]
    exact (c6LayeredDynamics.target_closed T hT).preimage
      fullCommonTopStateEquiv_isometry.continuous
  target_invariant := by
    intro x T s hT hx hTs
    apply (fullCommonTopTarget_mem_iff _ s).mpr
    have hxin : fullCommonTopStateEquiv x ∈
        theorem26ZeroValueTarget c6LayeredDynamics.alive
          (c6LayeredNonnegativeTimeData.optimalValue ⊤) T :=
      (fullCommonTopTarget_mem_iff x T).mp hx
    have hold := c6LayeredDynamics.target_invariant
      (fullCommonTopStateEquiv x) T s hT hxin hTs
    simpa [fullCommonTopTrajectory_eq_old] using hold
  W_absolutelyContinuous := by
    intro x T s hT hx hTs
    have hpath :
        (fun u => fullCommonTopLyapunov
          (fullCommonTheorem24Data.trajectory ⊤ fullCommonTopFeedback x T u) u) =
        (fun u => c6LayeredDynamics.W
          (c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback
            (fullCommonTopStateEquiv x) T u) u) := by
      funext u
      rw [fullCommonTopTrajectory_eq_old]
      simp [fullCommonTopLyapunov]
    rw [hpath]
    exact c6LayeredDynamics.W_absolutelyContinuous
      (fullCommonTopStateEquiv x) T s hT
      ((fullCommonTopAlive_mem_iff x).mp hx) hTs
  W_nonnegative := by
    intro x T s hT hx hTs
    have hold := c6LayeredDynamics.W_nonnegative
      (fullCommonTopStateEquiv x) T s hT
      ((fullCommonTopAlive_mem_iff x).mp hx) hTs
    simpa [fullCommonTopTrajectory_eq_old, fullCommonTopLyapunov] using hold
  W_rightSlope := by
    intro x T u hT hx hu
    have hold := c6LayeredDynamics.W_rightSlope
      (fullCommonTopStateEquiv x) T u hT
      ((fullCommonTopAlive_mem_iff x).mp hx) hu
    simpa [fullCommonTopTrajectory_eq_old, fullCommonTopLyapunov] using hold
  W_lower_distance_bound := by
    intro x T s hT hx hTs
    have hold := c6LayeredDynamics.W_lower_distance_bound
      (fullCommonTopStateEquiv x) T s hT
      ((fullCommonTopAlive_mem_iff x).mp hx) hTs
    have hdist := fullCommonTop_infDist_target_eq_old
      (fullCommonTheorem24Data.trajectory ⊤ fullCommonTopFeedback x T s) s
    have htraj := fullCommonTopTrajectory_eq_old x T s
    have hstate : fullCommonTopStateEquiv
        (fullCommonTheorem24Data.trajectory ⊤ fullCommonTopFeedback x T s) =
        c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback
          (fullCommonTopStateEquiv x) T s := by
      rw [htraj]
      simp
    rw [← hstate] at hold
    rw [← hdist] at hold
    simpa [fullCommonTopLyapunov] using hold
  W_upper_distance_bound := by
    intro x T s hT hx hTs
    have hold := c6LayeredDynamics.W_upper_distance_bound
      (fullCommonTopStateEquiv x) T s hT
      ((fullCommonTopAlive_mem_iff x).mp hx) hTs
    have hdist := fullCommonTop_infDist_target_eq_old
      (fullCommonTheorem24Data.trajectory ⊤ fullCommonTopFeedback x T s) s
    have htraj := fullCommonTopTrajectory_eq_old x T s
    have hstate : fullCommonTopStateEquiv
        (fullCommonTheorem24Data.trajectory ⊤ fullCommonTopFeedback x T s) =
        c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback
          (fullCommonTopStateEquiv x) T s := by
      rw [htraj]
      simp
    rw [← hstate] at hold
    rw [← hdist] at hold
    simpa [fullCommonTopLyapunov] using hold
  ω_continuous := c6LayeredDynamics.ω_continuous
  ω_zero := c6LayeredDynamics.ω_zero
  ω_nonnegative := c6LayeredDynamics.ω_nonnegative
  ω_monotone_on_nonnegative := c6LayeredDynamics.ω_monotone_on_nonnegative
  value_distance_bound := by
    intro y t ht hy
    have hold := c6LayeredDynamics.value_distance_bound
      (fullCommonTopStateEquiv y) t ht
      ((fullCommonTopAlive_mem_iff y).mp hy)
    have hdist := fullCommonTop_infDist_target_eq_old y t
    have hv0 := fullCommonTopData_optimalValue_eq_old
      (fullCommonTopStateEquiv y) t
    have hvalue : fullCommonTheorem24Data.optimalValue ⊤ y t =
        c6LayeredNonnegativeTimeData.optimalValue ⊤
          (fullCommonTopStateEquiv y) t := by
      simpa only [Equiv.symm_apply_apply] using hv0
    rw [← hdist, ← hvalue] at hold
    simpa using hold

/-- The transported dynamics uses exactly the old C6 feedback action when
states are related by the top-state equivalence. -/
theorem fullCommonTopFeedback_action_eq_old
    (t : Set.Ici (0 : ℝ))
    (x : fullCommonLayerState (⊤ : CommonConcept)) :
    (fullCommonTopDynamics.policyEquiv fullCommonTopDynamics.feedback).action
        (t, x) =
      (c6LayeredDynamics.policyEquiv c6LayeredDynamics.feedback).action
        (t, fullCommonTopStateEquiv x) := by
  have htime : fullCommonTopTimeStateMeasurableEquiv (t, x) =
      (t, fullCommonTopStateEquiv x) := rfl
  simp [fullCommonTopDynamics, fullCommonTopPolicyEquivDynamics,
    fullCommonTopFeedback, fullCommonTopMarkovFeedbackEquiv,
    Function.comp_def, htime]

/-- The legacy 27-A proof package, explicitly tied to the transported
CommonConcept dynamics through its path, feedback action, and Lyapunov value.
This keeps the original actuator hypotheses while making their D/E referents
visible in the type. -/
structure CommonConceptTop27ActuatorBridge
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) : Prop where
  source_inputs : C6TopActuatorInputs (fullCommonTopStateEquiv x) T hT
  trajectory_transport : ∀ s : ℝ,
    fullCommonTheorem24Data.trajectory ⊤ fullCommonTopDynamics.feedback x T s =
      fullCommonTopStateEquiv.symm
        (Tomabechi.Consistency.C6.c6TopPath
          (fullCommonTopStateEquiv x) T s)
  feedback_transport : ∀ (s : ℝ) (hs : T ≤ s),
    (fullCommonTopDynamics.policyEquiv fullCommonTopDynamics.feedback).action
      ⟨⟨s, hT.trans hs⟩,
        fullCommonTheorem24Data.trajectory ⊤ fullCommonTopDynamics.feedback x T s⟩ =
      (c6LayeredDynamics.policyEquiv c6LayeredDynamics.feedback).action
        ⟨⟨s, hT.trans hs⟩,
          Tomabechi.Consistency.C6.c6TopPath (fullCommonTopStateEquiv x) T s⟩
  lyapunov_transport : ∀ s : ℝ,
    fullCommonTopDynamics.W
        (fullCommonTheorem24Data.trajectory ⊤ fullCommonTopDynamics.feedback x T s) s =
      c6LayeredDynamics.W
        (Tomabechi.Consistency.C6.c6TopPath
          (fullCommonTopStateEquiv x) T s) s

/-- Build the typed 27-A bridge at every CommonConcept vertex initial state. -/
theorem fullCommonTop27ActuatorBridge
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) :
    CommonConceptTop27ActuatorBridge x T hT := by
  refine ⟨c6TopActuatorInputs (fullCommonTopStateEquiv x) T hT, ?_, ?_, ?_⟩
  · exact fullCommonTopTrajectory_eq_c6TopPath x T
  · intro s hs
    rw [fullCommonTopFeedback_action_eq_old]
    have hstate : fullCommonTopStateEquiv
        (fullCommonTheorem24Data.trajectory ⊤ fullCommonTopDynamics.feedback x T s) =
        Tomabechi.Consistency.C6.c6TopPath (fullCommonTopStateEquiv x) T s := by
      simpa [fullCommonTopDynamics] using
        congrArg fullCommonTopStateEquiv
          (fullCommonTopTrajectory_eq_c6TopPath x T s)
    rw [hstate]
  · intro s
    simpa [fullCommonTopDynamics, fullCommonTopLyapunov,
      fullCommonTopTrajectory_eq_c6TopPath]

/-- The selected input prescribed by 27-A is the feedback action of the new
CommonConcept dynamics along its own trajectory. -/
theorem fullCommonTop27_u0_eq_transported_feedback
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T s : ℝ)
    (hT : 0 ≤ T) (hs : T ≤ s) :
    Tomabechi.Examples.Theorem27Op.u0E (fullCommonTopStateEquiv x) T s =
      (fullCommonTopDynamics.policyEquiv fullCommonTopDynamics.feedback).action
        ⟨⟨s, hT.trans hs⟩,
          fullCommonTheorem24Data.trajectory ⊤ fullCommonTopDynamics.feedback x T s⟩ := by
  let B := fullCommonTop27ActuatorBridge x T hT
  calc
    _ = (c6LayeredDynamics.policyEquiv c6LayeredDynamics.feedback).action
        ⟨⟨s, hT.trans hs⟩,
          Tomabechi.Consistency.C6.c6TopPath
            (fullCommonTopStateEquiv x) T s⟩ := B.source_inputs.feedback_input s hs
    _ = _ := (B.feedback_transport s hs).symm

private def c6TopPZSAt
    (x : C6LayeredState (⊤ : WithTop ℕ)) (T t : ℝ) : Prop :=
  FeedbackPZS (c6LayeredNonnegativeTimeData.admissible ⊤) futureLebesgueMeasure
    (fun π y a s => c6LayeredNonnegativeTimeData.runningCost ⊤ π
      (c6LayeredNonnegativeTimeData.trajectory ⊤ π y a s) s)
    (c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback x T t) t

/-- The CommonConcept top PZS predicate is expressed entirely with its
transported theorem-24 data and its selected theorem-26 feedback. -/
def fullCommonTopPZSAt
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T t : ℝ) : Prop :=
  FeedbackPZS (fullCommonTheorem24Data.admissible ⊤) futureLebesgueMeasure
    (fun π y a s => fullCommonTheorem24Data.runningCost ⊤ π
      (fullCommonTheorem24Data.trajectory ⊤ π y a s) s)
    (fullCommonTheorem24Data.trajectory ⊤ fullCommonTopDynamics.feedback x T t) t

/-- The old quantitative theorem-27 kernel and its 27-A inputs, bundled at
the same CommonConcept initial state together with the explicit D/E transport.
This adapter records exactly which legacy conclusion is being reused. -/
structure CommonConceptTop27KernelBridge
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) : Prop where
  kernel : c6LayeredTheorem27Conclusion
    (fullCommonTopStateEquiv x) T hT
  actuator : CommonConceptTop27ActuatorBridge x T hT
  pzs_transport : ∀ t, fullCommonTopPZSAt x T t ↔
    c6TopPZSAt (fullCommonTopStateEquiv x) T t

/-- The top-level 27 conclusion restated using the transported CommonConcept
24/26 data and dynamics. The analytic reference fields remain the original
27 fields, while PZS, trajectory, value target, and Lyapunov terms are read
from the new D/E. -/
def fullCommonTopTheorem27Conclusion
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) : Prop :=
  (∀ t, T ≤ t →
    (¬ fullCommonTopPZSAt x T t ↔
      0 < Tomabechi.Theorem27.residualDescentRateAlong
        (fun s y => fullCommonTopDynamics.W y s)
        (fun s => fullCommonTheorem24Data.trajectory ⊤
          fullCommonTopDynamics.feedback x T s) t)) ∧
  (∀ᵐ t ∂futureLebesgueMeasure T, ∀ htt : T ≤ t,
    (¬ fullCommonTopPZSAt x T t ↔
      0 < -inner ℝ
        (Tomabechi.Examples.Theorem27Op.gradWE (fullCommonTopStateEquiv x) T t)
        (Tomabechi.Examples.Theorem27Op.GE
          ((fullCommonTopDynamics.policyEquiv fullCommonTopDynamics.feedback).action
            ⟨⟨t, hT.trans htt⟩,
              fullCommonTheorem24Data.trajectory ⊤
                fullCommonTopDynamics.feedback x T t⟩ -
            Tomabechi.Examples.Theorem27.vectorSourceReferenceInput
              (fullCommonTopStateEquiv x) T t)))) ∧
  (∀ᵐ t ∂futureLebesgueMeasure T,
    (¬ fullCommonTopPZSAt x T t →
      fullCommonTopDynamics.rate * fullCommonTopDynamics.c₁ *
        Metric.infDist
          (fullCommonTheorem24Data.trajectory ⊤
            fullCommonTopDynamics.feedback x T t)
          (theorem26ZeroValueTarget fullCommonTopDynamics.alive
            (fullCommonTheorem24Data.optimalValue ⊤) t) ^ 2 /
          (2 * |(fullCommonTopStateEquiv x) 0| + 1) ≤
        ‖Tomabechi.Examples.Theorem27Op.u0E
            (fullCommonTopStateEquiv x) T t -
          Tomabechi.Examples.Theorem27.vectorSourceReferenceInput
            (fullCommonTopStateEquiv x) T t‖ ∧
      0 < ‖Tomabechi.Examples.Theorem27Op.u0E
          (fullCommonTopStateEquiv x) T t -
        Tomabechi.Examples.Theorem27.vectorSourceReferenceInput
          (fullCommonTopStateEquiv x) T t‖))

/-- The complete running value generated by any transported policy is
pointwise equal to the corresponding C6 running value. -/
theorem fullCommonTop_runningValue_eq_old
    (π : fullCommonLayerPolicy (⊤ : CommonConcept))
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T s : ℝ) :
    fullCommonTheorem24Data.runningCost ⊤ π
        (fullCommonTheorem24Data.trajectory ⊤ π x T s) s =
      c6LayeredNonnegativeTimeData.runningCost ⊤
        (fullCommonTopPolicyEquiv π)
        (c6LayeredNonnegativeTimeData.trajectory ⊤
          (fullCommonTopPolicyEquiv π) (fullCommonTopStateEquiv x) T s) s := by
  rw [fullCommonTop_runningCost_eq_old]
  rw [fullCommonTop_trajectory_eq_old]
  simp

/-- Permanent-zero feasibility is invariant under the top CommonConcept/C6
equivalences. This transports both the existential policy and its almost
everywhere zero-cost condition. -/
theorem fullCommonTopPZS_transport
    (x : fullCommonLayerState (⊤ : CommonConcept)) (t : ℝ) :
    FeedbackPZS (fullCommonTheorem24Data.admissible ⊤)
      futureLebesgueMeasure
      (fun π y a s => fullCommonTheorem24Data.runningCost ⊤ π
        (fullCommonTheorem24Data.trajectory ⊤ π y a s) s) x t ↔
    FeedbackPZS (c6LayeredNonnegativeTimeData.admissible ⊤)
      futureLebesgueMeasure
      (fun π y a s => c6LayeredNonnegativeTimeData.runningCost ⊤ π
        (c6LayeredNonnegativeTimeData.trajectory ⊤ π y a s) s)
      (fullCommonTopStateEquiv x) t := by
  unfold FeedbackPZS
  constructor
  · rintro ⟨π, hπ, hzero⟩
    refine ⟨fullCommonTopPolicyEquiv π,
      (fullCommonTop_admissible_iff_old π x t).mp hπ, ?_⟩
    have hrun : (fun s => fullCommonTheorem24Data.runningCost ⊤ π
        (fullCommonTheorem24Data.trajectory ⊤ π x t s) s) =
      (fun s => c6LayeredNonnegativeTimeData.runningCost ⊤
        (fullCommonTopPolicyEquiv π)
        (c6LayeredNonnegativeTimeData.trajectory ⊤
          (fullCommonTopPolicyEquiv π) (fullCommonTopStateEquiv x) t s) s) := by
      funext s
      exact fullCommonTop_runningValue_eq_old π x t s
    change (fun s => fullCommonTheorem24Data.runningCost ⊤ π
        (fullCommonTheorem24Data.trajectory ⊤ π x t s) s) =ᵐ[
          futureLebesgueMeasure t] 0 at hzero
    rw [hrun] at hzero
    exact hzero
  · rintro ⟨π, hπ, hzero⟩
    refine ⟨fullCommonTopPolicyEquiv.symm π,
      ?_, ?_⟩
    · apply (fullCommonTop_admissible_iff_old
        (fullCommonTopPolicyEquiv.symm π) x t).mpr
      simpa using hπ
    · have hrun : (fun s => fullCommonTheorem24Data.runningCost ⊤
          (fullCommonTopPolicyEquiv.symm π)
          (fullCommonTheorem24Data.trajectory ⊤
            (fullCommonTopPolicyEquiv.symm π) x t s) s) =
        (fun s => c6LayeredNonnegativeTimeData.runningCost ⊤ π
          (c6LayeredNonnegativeTimeData.trajectory ⊤ π
            (fullCommonTopStateEquiv x) t s) s) := by
        funext s
        rw [fullCommonTop_runningValue_eq_old]
        simp
      change (fun s => fullCommonTheorem24Data.runningCost ⊤
          (fullCommonTopPolicyEquiv.symm π)
          (fullCommonTheorem24Data.trajectory ⊤
            (fullCommonTopPolicyEquiv.symm π) x t s) s) =ᵐ[
            futureLebesgueMeasure t] 0
      rw [hrun]
      exact hzero

/-- The PZS predicate used in the top-level theorem-27 output is the C6 PZS
predicate at the corresponding old top trajectory. -/
theorem fullCommonTopPZSAt_iff_c6
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T t : ℝ) :
    fullCommonTopPZSAt x T t ↔
      c6TopPZSAt (fullCommonTopStateEquiv x) T t := by
  have hpath : fullCommonTopStateEquiv
      (fullCommonTheorem24Data.trajectory ⊤ fullCommonTopFeedback x T t) =
    c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback
      (fullCommonTopStateEquiv x) T t := by
    rw [fullCommonTopTrajectory_eq_old]
    simp
  have hpath' : fullCommonTopStateEquiv
      (fullCommonTheorem24Data.trajectory ⊤ fullCommonTopDynamics.feedback x T t) =
    c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback
      (fullCommonTopStateEquiv x) T t := by
    simpa [fullCommonTopDynamics] using hpath
  have hpzs := fullCommonTopPZS_transport
    (fullCommonTheorem24Data.trajectory ⊤
      fullCommonTopDynamics.feedback x T t) t
  rw [hpath'] at hpzs
  simpa only [fullCommonTopPZSAt, c6TopPZSAt] using hpzs

/-- Transfer all three quantitative theorem-27 conclusions to the transported
CommonConcept dynamics. The proof uses only the explicit PZS, actuator, and
isometric target bridges carried by the same kernel bundle. -/
theorem fullCommonTopTheorem27Conclusion_of_kernelBridge
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T)
    (B : CommonConceptTop27KernelBridge x T hT) :
    fullCommonTopTheorem27Conclusion x T hT := by
  have hlegacyPath : ∀ s : ℝ,
      Tomabechi.Consistency.C6.c6TopPath (fullCommonTopStateEquiv x) T s =
        vectorSourceData.trajectory true c6LayeredDynamics.feedback
          (fullCommonTopStateEquiv x) T s := by
    intro s
    rfl
  have hpath : ∀ s,
      fullCommonTopStateEquiv
        (fullCommonTheorem24Data.trajectory ⊤
          fullCommonTopDynamics.feedback x T s) =
      c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback
        (fullCommonTopStateEquiv x) T s := by
    intro s
    rw [B.actuator.trajectory_transport s]
    rw [hlegacyPath s]
    simp [c6LayeredData_top_trajectory_fun]
  have hcurve : (fun s => fullCommonTopDynamics.W
      (fullCommonTheorem24Data.trajectory ⊤
        fullCommonTopDynamics.feedback x T s) s) =
    (fun s => c6LayeredDynamics.W
      (c6LayeredNonnegativeTimeData.trajectory ⊤ c6LayeredDynamics.feedback
        (fullCommonTopStateEquiv x) T s) s) := by
    funext s
    calc
      _ = c6LayeredDynamics.W
          (Tomabechi.Consistency.C6.c6TopPath
            (fullCommonTopStateEquiv x) T s) s :=
        B.actuator.lyapunov_transport s
      _ = _ := by rw [hlegacyPath s]; simp [c6LayeredData_top_trajectory_fun]
  have hres : ∀ t,
      Tomabechi.Theorem27.residualDescentRateAlong
        (fun s y => fullCommonTopDynamics.W y s)
        (fun s => fullCommonTheorem24Data.trajectory ⊤
          fullCommonTopDynamics.feedback x T s) t =
      Tomabechi.Theorem27.residualDescentRateAlong
        (fun s y => c6LayeredDynamics.W y s)
        (fun s => c6LayeredNonnegativeTimeData.trajectory ⊤
          c6LayeredDynamics.feedback (fullCommonTopStateEquiv x) T s) t := by
    intro t
    simp only [Tomabechi.Theorem27.residualDescentRateAlong]
    rw [hcurve]
  refine ⟨?_, ?_, ?_⟩
  · intro t htt
    rw [B.pzs_transport t]
    have hold := B.kernel.1 t htt
    simpa only [c6TopPZSAt, hres t] using hold
  · filter_upwards [B.kernel.2.1] with t ht
    intro htt
    have hold := ht htt
    rw [B.pzs_transport t, B.actuator.feedback_transport t htt]
    rw [hlegacyPath t]
    exact hold
  · filter_upwards [B.kernel.2.2] with t ht
    intro hnot
    have hOldNot : ¬ c6TopPZSAt (fullCommonTopStateEquiv x) T t :=
      (not_congr (B.pzs_transport t)).mp hnot
    have hold := ht hOldNot
    have hdist := fullCommonTop_infDist_target_eq_old
      (fullCommonTheorem24Data.trajectory ⊤
        fullCommonTopDynamics.feedback x T t) t
    rw [← hpath t] at hold
    rw [← hdist] at hold
    simpa [fullCommonTopDynamics] using hold

/-- Bundle the old theorem-27 kernel and 27-A actuator with the proved
CommonConcept-to-C6 PZS transport along the same initial state and horizon. -/
theorem fullCommonTop27KernelBridge
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) :
    CommonConceptTop27KernelBridge x T hT := by
  exact ⟨c6LayeredData_theorem27_kernel (fullCommonTopStateEquiv x) T hT,
    fullCommonTop27ActuatorBridge x T hT,
    fun t => fullCommonTopPZSAt_iff_c6 x T t⟩

/-- Proposition-valued handle for recording the transported dynamics
certificate in another proof-bearing acceptance proposition. -/
def FullCommonTopDynamicsExists : Prop :=
  Nonempty (Theorem26NonnegativeTimeDynamics fullCommonTheorem24Data E2)

theorem fullCommonTopDynamics_exists : FullCommonTopDynamicsExists :=
  ⟨fullCommonTopDynamics⟩

/-- The old optimizer is retained as the optimizer at its embedded address. -/
theorem fullCommonTheorem24Data_recovers_old_optimalPolicy
    (a : WithTop ℕ) (x : C6LayeredState a) (T : ℝ) :
    fullCommonTheorem24Data.optimalPolicy (layerAddressEmbedding a)
        (cast (congrArg C6LayeredState
          (fullCommonLayerIndex_layerAddress a).symm) x) T =
      cast (congrArg C6LayeredPolicy
        (fullCommonLayerIndex_layerAddress a).symm)
        (c6LayeredNonnegativeTimeData.optimalPolicy a x T) := by
  unfold fullCommonTheorem24Data
  change c6LayeredNonnegativeTimeData.optimalPolicy
      (fullCommonLayerIndex (layerAddressEmbedding a))
      (cast (congrArg C6LayeredState
        (fullCommonLayerIndex_layerAddress a).symm) x) T = _
  exact fullIndex_dependentPolicy_cast_eq
    (fun i y => c6LayeredNonnegativeTimeData.optimalPolicy i y T)
    (fullCommonLayerIndex_layerAddress a) x

/-- The old controlled path is retained at its embedded address. -/
theorem fullCommonTheorem24Data_recovers_old_trajectory
    (a : WithTop ℕ) (π : C6LayeredPolicy a) (x : C6LayeredState a)
    (T s : ℝ) :
    fullCommonTheorem24Data.trajectory (layerAddressEmbedding a)
        (cast (congrArg C6LayeredPolicy
          (fullCommonLayerIndex_layerAddress a).symm) π)
        (cast (congrArg C6LayeredState
          (fullCommonLayerIndex_layerAddress a).symm) x) T s =
      cast (congrArg C6LayeredState
        (fullCommonLayerIndex_layerAddress a).symm)
        (c6LayeredNonnegativeTimeData.trajectory a π x T s) := by
  unfold fullCommonTheorem24Data
  change c6LayeredNonnegativeTimeData.trajectory
      (fullCommonLayerIndex (layerAddressEmbedding a))
      (cast (congrArg C6LayeredPolicy
        (fullCommonLayerIndex_layerAddress a).symm) π)
      (cast (congrArg C6LayeredState
        (fullCommonLayerIndex_layerAddress a).symm) x) T s = _
  exact fullIndex_dependentTrajectory_cast_eq
    c6LayeredNonnegativeTimeData.trajectory
    (fullCommonLayerIndex_layerAddress a) π x T s

/-- At the common-concept top, the full reindexed 24-data has the same
discount rate as the original C6 record. -/
theorem fullCommonTheorem24Data_top_rho :
    fullCommonTheorem24Data.rho = c6LayeredNonnegativeTimeData.rho := by
  rfl

/-- Top-layer cost equality needed to transport the 26 certificate. The
dependent top state type is exposed through the explicit index equality. -/
theorem fullCommonTheorem24Data_top_runningCost
    (π : C6LayeredPolicy (⊤ : WithTop ℕ))
    (x : C6LayeredState (⊤ : WithTop ℕ)) (t : ℝ) :
    fullCommonTheorem24Data.runningCost (⊤ : CommonConcept)
        (cast (congrArg C6LayeredPolicy fullCommonLayerIndex_top.symm) π)
        (cast (congrArg C6LayeredState fullCommonLayerIndex_top.symm) x) t =
      c6LayeredNonnegativeTimeData.runningCost (⊤ : WithTop ℕ) π x t := by
  exact fullCommonTheorem24Data_recovers_old_runningCost ⊤ π x t

/-- The same top-index cast preserves the trajectory used by the 26
certificate. -/
theorem fullCommonTheorem24Data_top_trajectory
    (π : C6LayeredPolicy (⊤ : WithTop ℕ))
    (x : C6LayeredState (⊤ : WithTop ℕ)) (T s : ℝ) :
    fullCommonTheorem24Data.trajectory (⊤ : CommonConcept)
        (cast (congrArg C6LayeredPolicy fullCommonLayerIndex_top.symm) π)
        (cast (congrArg C6LayeredState fullCommonLayerIndex_top.symm) x) T s =
      cast (congrArg C6LayeredState fullCommonLayerIndex_top.symm)
        (c6LayeredNonnegativeTimeData.trajectory (⊤ : WithTop ℕ) π x T s) := by
  exact fullCommonTheorem24Data_recovers_old_trajectory ⊤ π x T s

/-- The top-layer value used in the zero-value target is preserved under the
same address cast. -/
theorem fullCommonTheorem24Data_top_optimalValue
    (x : C6LayeredState (⊤ : WithTop ℕ)) (T : ℝ) :
    fullCommonTheorem24Data.optimalValue (⊤ : CommonConcept)
        (cast (congrArg C6LayeredState fullCommonLayerIndex_top.symm) x) T =
      c6LayeredNonnegativeTimeData.optimalValue (⊤ : WithTop ℕ) x T := by
  exact fullCommonTheorem24Data_recovers_old_optimalValue ⊤ x T

end Tomabechi.Consistency.R1

#print axioms Tomabechi.Consistency.R1.fullCommonTopDynamics
