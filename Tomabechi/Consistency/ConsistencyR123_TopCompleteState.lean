import Tomabechi.Consistency.ConsistencyR123_BaseAsStageBackground

/-!
# 定理26の X_⊤ を完全状態として読む

定理26 の X_⊤ は「脳・身体を含む完全状態」である。モデルでは `X_⊤ = E2`（`topProjection`）で、
完全状態 `CompleteState = ℝ × ℝ`（認知座標 q・物理座標 p）から
`disagreementStateTo27 (q,p) = (1−q)·e₀ + (3/2)(p+q²)·e₁` で射影していた。

この射影は**全単射で両方向に連続**（右逆写像は `vectorStateToCompleteState`、
左逆写像は本ファイルで証明）なので、完全状態は E2 と同相である。したがって
「X_⊤ = 完全状態そのもの」と読んでも 26-A の全条件が成り立つ。ここでは

* `completeTopChart : CompleteState ≃ fullCommonLayerState ⊤` と同相性、
* 完全状態の型 `TopComplete` に引き戻し距離（chart が等長になる距離）を入れ、
* ℬ_alive、零価値目標 𝒩_⊤、W_⊤、軌道を完全状態へ引き戻して、26-A の各条件
  （aliveの不変、目標の非空・閉・不変、W の非負・絶対連続・右傾き・距離の上下界、価値の距離上界）
  が引き戻し側でも成り立つこと

を示す。**範囲：** 距離は E2 の距離の引き戻し（`CompleteState` の積距離ではない）。
26-A の条件を `Theorem26NonnegativeTimeDynamics` の型として完全状態上に組み直したものではなく、
各条件の引き戻しの命題である。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1 Tomabechi.Consistency.C2
open Tomabechi.Theorem24_26

/-- 射影の左逆：`vectorStateToCompleteState ∘ disagreementStateTo27 = id`。 -/
theorem vectorStateToCompleteState_left_inverse (z : CompleteState) :
    vectorStateToCompleteState (disagreementStateTo27 z) = z := by
  apply Prod.ext
  · simp [vectorStateToCompleteState, disagreementStateTo27_radial, cognitiveCoordinate]
  · simp [vectorStateToCompleteState, disagreementStateTo27_radial, disagreementStateTo27_phase,
      entropyObservedElapsed, cognitiveCoordinate, physicalCoordinate]
    ring


/-- 射影を同値として組む：完全状態 ≃ E2。 -/
def completeTopEquiv : CompleteState ≃ Tomabechi.Examples.Theorem27Op.E2 where
  toFun := disagreementStateTo27
  invFun := vectorStateToCompleteState
  left_inv := vectorStateToCompleteState_left_inverse
  right_inv := disagreementStateTo27_right_inverse

theorem disagreementStateTo27_continuous : Continuous disagreementStateTo27 := by
  unfold disagreementStateTo27 entropyObservedElapsed cognitiveCoordinate physicalCoordinate
  fun_prop

theorem vectorStateToCompleteState_continuous : Continuous vectorStateToCompleteState := by
  unfold vectorStateToCompleteState
  fun_prop

/-- 完全状態は E2 と同相（射影は全単射で両方向に連続）。 -/
def completeTopHomeo : CompleteState ≃ₜ Tomabechi.Examples.Theorem27Op.E2 where
  toEquiv := completeTopEquiv
  continuous_toFun := disagreementStateTo27_continuous
  continuous_invFun := vectorStateToCompleteState_continuous

/-- 完全状態から `fullCommonLayerState ⊤`（モデルの X_⊤）への同値。 -/
def completeTopChart : CompleteState ≃ fullCommonLayerState (⊤ : CommonConcept) :=
  completeTopEquiv.trans fullCommonTopStateEquiv.symm

/-- 完全状態の型。X_⊤ の距離（E2 の距離）を chart で引き戻した距離を持つ。 -/
def TopComplete : Type := CompleteState

instance : PseudoMetricSpace TopComplete :=
  PseudoMetricSpace.induced (fun z : CompleteState => completeTopChart z) inferInstance

def topChart : TopComplete ≃ fullCommonLayerState (⊤ : CommonConcept) := completeTopChart

theorem topChart_isometry : Isometry topChart := Isometry.of_dist_eq (fun _ _ => rfl)

theorem infDist_topChart_preimage (z : TopComplete)
    (S : Set (fullCommonLayerState (⊤ : CommonConcept))) :
    Metric.infDist z (topChart ⁻¹' S) = Metric.infDist (topChart z) S := by
  have h := Metric.infDist_image topChart_isometry (x := z) (t := topChart ⁻¹' S)
  rw [Set.image_preimage_eq S topChart.surjective] at h
  exact h.symm


/-! ## 26-A の引き戻し -/

/-- ℬ_alive の引き戻し。 -/
def SharedModelSignature.topAliveC (N : SharedModelSignature) : Set TopComplete :=
  topChart ⁻¹' N.dynamics.alive

/-- 零価値目標 𝒩_⊤(T) の引き戻し。 -/
def SharedModelSignature.topTargetC (N : SharedModelSignature) (T : ℝ) : Set TopComplete :=
  topChart ⁻¹' theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) T

/-- 同じ閉ループ軌道を完全状態へ引き戻したもの。 -/
def SharedModelSignature.topFlowC (N : SharedModelSignature) (z : TopComplete) (T s : ℝ) :
    TopComplete :=
  topChart.symm (N.topPath (topChart z) T s)

def SharedModelSignature.topWC (N : SharedModelSignature) (z : TopComplete) (t : ℝ) : ℝ :=
  N.dynamics.W (topChart z) t

def SharedModelSignature.topValueC (N : SharedModelSignature) (z : TopComplete) (t : ℝ) : ℝ :=
  N.data.optimalValue ⊤ (topChart z) t

theorem topChart_topFlowC (N : SharedModelSignature) (z : TopComplete) (T s : ℝ) :
    topChart (N.topFlowC z T s) = N.topPath (topChart z) T s :=
  topChart.apply_symm_apply _

/-- 26-A の各条件を、完全状態 `TopComplete`（E2 の距離の引き戻し）上へ引き戻した命題。 -/
structure SharedTopCompleteReading (N : SharedModelSignature) : Prop where
  chart_homeo : Function.Bijective topChart ∧ Continuous topChart ∧ Continuous topChart.symm
  alive_invariant : ∀ (z : TopComplete) (T s : ℝ), 0 ≤ T → z ∈ N.topAliveC → T ≤ s →
    N.topFlowC z T s ∈ N.topAliveC
  target_nonempty : ∀ T : ℝ, 0 ≤ T → (N.topTargetC T).Nonempty
  target_closed : ∀ T : ℝ, 0 ≤ T → IsClosed (N.topTargetC T)
  target_invariant : ∀ (z : TopComplete) (T s : ℝ), 0 ≤ T → z ∈ N.topTargetC T → T ≤ s →
    N.topFlowC z T s ∈ N.topTargetC s
  W_nonnegative : ∀ (z : TopComplete) (T s : ℝ), 0 ≤ T → z ∈ N.topAliveC → T ≤ s →
    0 ≤ N.topWC (N.topFlowC z T s) s
  W_absolutelyContinuous : ∀ (z : TopComplete) (T s : ℝ), 0 ≤ T → z ∈ N.topAliveC → T ≤ s →
    AbsolutelyContinuousOnInterval (fun u => N.topWC (N.topFlowC z T u) u) T s
  W_rightSlope : ∀ (z : TopComplete) (T u : ℝ), 0 ≤ T → z ∈ N.topAliveC → T ≤ u →
    Tomabechi.Theorem1.RightSlopeBound (fun s => N.topWC (N.topFlowC z T s) s) u
      (-N.dynamics.rate * N.topWC (N.topFlowC z T u) u)
  W_lower_distance_bound : ∀ (z : TopComplete) (T s : ℝ), 0 ≤ T → z ∈ N.topAliveC → T ≤ s →
    N.dynamics.c₁ * (Metric.infDist (N.topFlowC z T s) (N.topTargetC s)) ^ 2 ≤
      N.topWC (N.topFlowC z T s) s
  W_upper_distance_bound : ∀ (z : TopComplete) (T s : ℝ), 0 ≤ T → z ∈ N.topAliveC → T ≤ s →
    N.topWC (N.topFlowC z T s) s ≤
      N.dynamics.c₂ * (Metric.infDist (N.topFlowC z T s) (N.topTargetC s)) ^ 2
  value_distance_bound : ∀ (y : TopComplete) (t : ℝ), 0 ≤ t → y ∈ N.topAliveC →
    0 ≤ N.topValueC y t ∧
      N.topValueC y t ≤ N.dynamics.ω (Metric.infDist y (N.topTargetC t))

theorem SharedModelSignature.sharedTopCompleteReading (N : SharedModelSignature) :
    SharedTopCompleteReading N := by
  have hwf : ∀ (z : TopComplete) (T s : ℝ),
      N.topWC (N.topFlowC z T s) s = N.dynamics.W (N.topPath (topChart z) T s) s := by
    intro z T s; simp [SharedModelSignature.topWC, topChart_topFlowC]
  refine {
    chart_homeo := ⟨topChart.bijective, topChart_isometry.continuous, ?_⟩
    alive_invariant := ?_
    target_nonempty := ?_
    target_closed := ?_
    target_invariant := ?_
    W_nonnegative := ?_
    W_absolutelyContinuous := ?_
    W_rightSlope := ?_
    W_lower_distance_bound := ?_
    W_upper_distance_bound := ?_
    value_distance_bound := ?_ }
  · have : Isometry topChart.symm := by
      intro x y
      rw [edist_dist, edist_dist]
      apply congrArg ENNReal.ofReal
      change dist (topChart (topChart.symm x)) (topChart (topChart.symm y)) = dist x y
      simp
    exact this.continuous
  · intro z T s hT hz hs
    change topChart (N.topFlowC z T s) ∈ N.dynamics.alive
    rw [topChart_topFlowC]
    exact N.dynamics.trajectory_alive _ T s hT hz hs
  · intro T hT
    obtain ⟨x, hx⟩ := N.dynamics.target_nonempty T hT
    exact ⟨topChart.symm x, by simpa [SharedModelSignature.topTargetC] using hx⟩
  · intro T hT
    exact (N.dynamics.target_closed T hT).preimage topChart_isometry.continuous
  · intro z T s hT hz hs
    change topChart (N.topFlowC z T s) ∈
      theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) s
    rw [topChart_topFlowC]
    exact N.dynamics.target_invariant _ T s hT hz hs
  · intro z T s hT hz hs
    rw [hwf]
    exact N.dynamics.W_nonnegative _ T s hT hz hs
  · intro z T s hT hz hs
    simp only [hwf]
    exact N.dynamics.W_absolutelyContinuous _ T s hT hz hs
  · intro z T u hT hz hu
    simp only [hwf]
    exact N.dynamics.W_rightSlope _ T u hT hz hu
  · intro z T s hT hz hs
    rw [hwf, SharedModelSignature.topTargetC, infDist_topChart_preimage, topChart_topFlowC]
    exact N.dynamics.W_lower_distance_bound _ T s hT hz hs
  · intro z T s hT hz hs
    rw [hwf, SharedModelSignature.topTargetC, infDist_topChart_preimage, topChart_topFlowC]
    exact N.dynamics.W_upper_distance_bound _ T s hT hz hs
  · intro y t ht hy
    rw [SharedModelSignature.topTargetC, infDist_topChart_preimage]
    exact N.dynamics.value_distance_bound _ t ht hy

/-- chart はモデルの射影 `sharedModel.topProjection` そのもの（E2 側で見ると一致する）。 -/
theorem completeTopChart_eq_topProjection (z : CompleteState) :
    fullCommonTopStateEquiv (completeTopChart z) = sharedModel.topProjection z := by
  simp [completeTopChart, completeTopEquiv]
  rfl

theorem final_consistency_v2_with_top_complete_state :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N := by
  obtain ⟨N, h1, h2, h3, h4⟩ := final_consistency_v2_with_base_background21
  exact ⟨N, h1, h2, h3, h4, N.sharedTopCompleteReading⟩

#print axioms completeTopHomeo
#print axioms SharedModelSignature.sharedTopCompleteReading
#print axioms final_consistency_v2_with_top_complete_state
end Tomabechi.Consistency.R123
