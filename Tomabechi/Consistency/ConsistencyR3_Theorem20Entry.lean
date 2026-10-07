import Tomabechi.Consistency.ConsistencyR3_CommonBase

/-!
# 共有基礎評価を使う定理20原文条件入口

Euclidean状態上でD=(x₀-x₁)²、V₀=1+2D、実効評価=1+3Dを使う。
同じrate-3流を生成する移動度は恒等写像の1/4倍である。
箱内ではV₀は定理1/4/24の共通基礎評価そのもの。
箱外は二次式への明示拡張であり、DAの箱外の非線形評価を同一視しない。
初期集合は一点。象徴目標は原文条件入口の全域零集合を使う。
-/

noncomputable section
namespace Tomabechi.Consistency.R3
open MeasureTheory Filter
open scoped Topology Gradient
open Tomabechi.Theorem1
open Tomabechi.Examples.Theorem2
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.R2

def sharedT20D (x : C1EuclideanAgentState) : ℝ := 4 * c1EuclideanSymbolDistance x
def sharedT20V0 (x : C1EuclideanAgentState) : ℝ := 1 + 8 * c1EuclideanSymbolDistance x
def sharedT20GradD (x : C1EuclideanAgentState) : C1EuclideanAgentState :=
  (4 : ℝ) • c1EuclideanSymbolDistanceGradient x
def sharedT20Mobility (_t : ℝ) : C1EuclideanAgentState →L[ℝ] C1EuclideanAgentState :=
  (1 / 4 : ℝ) • ContinuousLinearMap.id ℝ C1EuclideanAgentState
def sharedT20InverseMobility (_t : ℝ) : C1EuclideanAgentState →L[ℝ] C1EuclideanAgentState :=
  (4 : ℝ) • ContinuousLinearMap.id ℝ C1EuclideanAgentState

/-- 定理20が読む基礎評価は、箱内で同じ共有基礎評価と一致する。 -/
theorem sharedT20V0_eq_common (x : C1EuclideanAgentState) (hx : x ∈ c1EuclideanBox) :
    sharedT20V0 x = commonBaseV0 (c1EuclideanCoordinates x) 0 := by
  rw [commonBaseV0_eq_theorem20_candidate_on_box _ hx,
    sharedT20V0, c1EuclideanSymbolDistance_eq_coordinates]
  dsimp [commonBaseD, c1SymbolDistance]
  ring

theorem sharedT20D_eq_common (x : C1EuclideanAgentState) :
    sharedT20D x = commonBaseD (c1EuclideanCoordinates x) := by
  rw [sharedT20D, c1EuclideanSymbolDistance_eq_coordinates]
  dsimp [commonBaseD, c1SymbolDistance]
  ring

private theorem scaledSymbolGradient (k : ℝ) (x : C1EuclideanAgentState) :
    HasGradientAt (fun y => k * c1EuclideanSymbolDistance y)
      (k • c1EuclideanSymbolDistanceGradient x) x := by
  apply (hasGradientAt_iff_hasFDerivAt).2
  convert (c1EuclideanSymbolDistance_hasGradientAt x).hasFDerivAt.const_smul k using 1
  exact map_smul (InnerProductSpace.toDual ℝ C1EuclideanAgentState) k _

theorem sharedT20V0_hasGradientAt (x : C1EuclideanAgentState) :
    HasGradientAt sharedT20V0 ((8 : ℝ) • c1EuclideanSymbolDistanceGradient x) x := by
  apply (hasGradientAt_iff_hasFDerivAt).2
  exact (scaledSymbolGradient 8 x).hasFDerivAt.const_add 1

theorem sharedT20D_hasGradientAt (x : C1EuclideanAgentState) :
    HasGradientAt sharedT20D (sharedT20GradD x) x := scaledSymbolGradient 4 x

/-- 定数baselineを保った実効評価の勾配。 -/
theorem sharedT20Effective_hasGradientAt (x : C1EuclideanAgentState) :
    HasGradientAt (fun y => sharedT20V0 y - 1 * 1 * (1 * (-sharedT20D y)))
      ((12 : ℝ) • c1EuclideanSymbolDistanceGradient x) x := by
  have h : HasGradientAt (fun y => 1 + 12 * c1EuclideanSymbolDistance y)
      ((12 : ℝ) • c1EuclideanSymbolDistanceGradient x) x :=
    (hasGradientAt_iff_hasFDerivAt).2 ((scaledSymbolGradient 12 x).hasFDerivAt.const_add 1)
  convert h using 1
  funext y
  dsimp [sharedT20V0, sharedT20D]
  ring

/-- 新評価の勾配と1/4移動度が、元と同じrate-3場を生成する。 -/
theorem sharedT20_field (x : C1EuclideanAgentState) (t : ℝ) :
    differentiableEuclideanConsensusOptimalFlow.vectorField x
      (differentiableEuclideanConsensusOptimalFlow.feedback x t) t =
        -(sharedT20Mobility t)
          (∇ (fun y => sharedT20V0 y - 1 * 1 * (1 * (-sharedT20D y))) x) := by
  rw [(sharedT20Effective_hasGradientAt x).gradient]
  change euclideanConsensusOptimalFlow.vectorField x
    (euclideanConsensusOptimalFlow.feedback x t) t = _
  rw [c1EuclideanOptimalField_eq_neg_three_gradient]
  norm_num [sharedT20Mobility, smul_smul]
  module

/-- Euclidean化しても、一点初期集合の閉到達集合は同じ線分の像となる。 -/
theorem sharedT20_pointK_eq_image (x : C1EuclideanAgentState) (t₀ : ℝ) :
    closedLoopReachableSet (policyFlowReachableAt euclideanConsensusOptimalFlow {x} t₀) =
      c1EuclideanCoordinates.symm '' pointReachableClosure (c1EuclideanCoordinates x) t₀ := by
  have hset : {y | ∃ τ : ℝ, 0 ≤ τ ∧
      y ∈ policyFlowReachableAt euclideanConsensusOptimalFlow {x} t₀ τ} =
      c1EuclideanCoordinates.symm '' {y | ∃ τ : ℝ, 0 ≤ τ ∧
        y ∈ policyFlowReachableAt consensusOptimalFlow {c1EuclideanCoordinates x} t₀ τ} := by
    ext y
    constructor
    · rintro ⟨τ, hτ, hstart, z, hz, rfl⟩
      have hz' : z = x := Set.mem_singleton_iff.mp hz
      subst z
      refine ⟨consensusOptimalFlow.flow t₀ (c1EuclideanCoordinates x) τ,
        ⟨τ, hτ, hstart, c1EuclideanCoordinates x, Set.mem_singleton _, rfl⟩, ?_⟩
      rfl
    · rintro ⟨z, ⟨τ, hτ, hstart, w, hw, rfl⟩, rfl⟩
      have hw' : w = c1EuclideanCoordinates x := Set.mem_singleton_iff.mp hw
      subst w
      exact ⟨τ, hτ, hstart, x, Set.mem_singleton _, rfl⟩
  change closure _ = c1EuclideanCoordinates.symm '' closure _
  rw [hset]
  exact c1EuclideanCoordinates.symm.toHomeomorph.isClosedEmbedding.closure_image_eq _

theorem sharedT20_pointK_compact (x : C1EuclideanAgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    IsCompact (closedLoopReachableSet
      (policyFlowReachableAt euclideanConsensusOptimalFlow {x} t₀)) := by
  rw [sharedT20_pointK_eq_image, pointReachableClosure_eq_orbitSegment _ t₀ ht₀]
  apply IsCompact.image ?_ c1EuclideanCoordinates.symm.continuous
  exact isCompact_Icc.image (by unfold segmentPoint; fun_prop)

theorem sharedT20_pointK_invariant (x : C1EuclideanAgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    ∀ y ∈ closedLoopReachableSet
      (policyFlowReachableAt euclideanConsensusOptimalFlow {x} t₀),
      ∀ t, t₀ ≤ t → euclideanConsensusOptimalFlow.flow t₀ y t ∈
        closedLoopReachableSet (policyFlowReachableAt euclideanConsensusOptimalFlow {x} t₀) := by
  intro y hy t ht
  rw [sharedT20_pointK_eq_image] at hy ⊢
  rcases hy with ⟨z, hz, rfl⟩
  refine ⟨consensusOptimalFlow.flow t₀ z t,
    pointReachableClosure_forward_invariant _ t₀ ht₀ hz ht, ?_⟩
  simp [euclideanConsensusOptimalFlow, c1EuclideanCoordinates_toLp]

/-- 原文条件の全結論。共有評価・実移動度・一点初期集合を一般入口へ直接渡す。
距離の象徴零集合、下降方向同値、微分の厳密負値、全時間の極限も保持する。 -/
def SharedT20OriginalConclusions (x : C1EuclideanAgentState) (t₀ : ℝ) : Prop :=
    (∀ t, t₀ ≤ t →
      sharedT20D (euclideanConsensusOptimalFlow.flow t₀ x t) ≤
        sharedT20D (euclideanConsensusOptimalFlow.flow t₀ x t₀) * Real.exp (-(t - t₀)) ∧
      Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x t) c1EuclideanSymbolTarget ≤
        2 * Real.sqrt (sharedT20D (euclideanConsensusOptimalFlow.flow t₀ x t₀)) *
          Real.exp (-(1 / 2 : ℝ) * (t - t₀)) ∧
      deriv (fun r => sharedT20D (euclideanConsensusOptimalFlow.flow t₀ x r)) t ≤
        -(1 / 2 : ℝ) * (2 * sharedT20D (euclideanConsensusOptimalFlow.flow t₀ x t)) ∧
      (euclideanConsensusOptimalFlow.flow t₀ x t ∉ c1EuclideanSymbolTarget →
        deriv (fun r => sharedT20D (euclideanConsensusOptimalFlow.flow t₀ x r)) t < 0) ∧
      inner ℝ
        (sharedT20InverseMobility t (euclideanConsensusOptimalFlow.vectorField
          (euclideanConsensusOptimalFlow.flow t₀ x t)
          (euclideanConsensusOptimalFlow.feedback (euclideanConsensusOptimalFlow.flow t₀ x t) t) t))
        (-(sharedT20Mobility t (sharedT20GradD (euclideanConsensusOptimalFlow.flow t₀ x t)))) =
          -deriv (fun r => sharedT20D (euclideanConsensusOptimalFlow.flow t₀ x r)) t) ∧
    Tendsto (fun t => Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x t)
      c1EuclideanSymbolTarget) atTop (𝓝 0)

theorem sharedBase_theorem20_point_entry (x : C1EuclideanAgentState)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    SharedT20OriginalConclusions x t₀ := by
  let F := differentiableEuclideanConsensusOptimalFlow
  let gradD : ℝ → C1EuclideanAgentState := fun r => sharedT20GradD (F.flow t₀ x r)
  let gradV : ℝ → C1EuclideanAgentState := fun r =>
    (8 : ℝ) • c1EuclideanSymbolDistanceGradient (F.flow t₀ x r)
  let g2 : ℝ → ℝ := fun r => 2 * sharedT20D (F.flow t₀ x r)
  have hg2 : ∀ r, inner ℝ (gradD r) (sharedT20Mobility r (gradD r)) = g2 r := by
    intro r
    change inner ℝ ((4 : ℝ) • c1EuclideanSymbolDistanceGradient (F.flow t₀ x r))
      ((1 / 4 : ℝ) • ((4 : ℝ) • c1EuclideanSymbolDistanceGradient (F.flow t₀ x r))) =
        2 * (4 * c1EuclideanSymbolDistance (F.flow t₀ x r))
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      c1EuclideanSymbolGradient_inner_self]
    ring
  simpa only [SharedT20OriginalConclusions, one_mul, mul_one, neg_one_mul,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, differentiableEuclideanConsensusOptimalFlow,
    gradD, gradV, g2, F] using
    (Tomabechi.Theorem20.theorem20_policy_flow_original_condition_conclusion
      F sharedT20Mobility sharedT20InverseMobility sharedT20V0 (fun _ => 1)
      sharedT20D (fun d => -d) 1 1 (1 / 2) (1 / 2) 1 2 (1 / 4) t₀ ht₀ {x} x
      (Set.mem_singleton _) c1EuclideanSymbolTarget g2 (fun _ => -1)
      gradV (fun _ => 0) gradD sharedT20_field
      (sharedT20_pointK_compact x t₀ ht₀) (sharedT20_pointK_invariant x t₀ ht₀)
      (fun r _ => sharedT20V0_hasGradientAt _) (fun r _ => hasGradientAt_const _ 1)
      (fun r _ => sharedT20D_hasGradientAt _)
      (fun y => mul_nonneg (by norm_num) (c1EuclideanSymbolDistance_nonneg y))
      (fun y => by
        rw [sharedT20D, mul_eq_zero]
        norm_num
        exact c1EuclideanSymbolDistance_zero_iff y)
      c1EuclideanSymbolTarget_nonempty c1EuclideanSymbolTarget_closed
      (fun r _ => hasDerivAt_neg _) (by intro r hr y; simp [sharedT20Mobility,
        sharedT20InverseMobility, smul_smul])
      (by intro r hr y z; simp [sharedT20Mobility, real_inner_smul_left,
        real_inner_smul_right, real_inner_comm])
      (by intro r hr y; simp [sharedT20Mobility, real_inner_smul_right,
        real_inner_self_eq_norm_sq])
      (by
        intro r hr hreach hnot
        have hgv : gradV r = (2 : ℝ) • gradD r := by dsimp [gradV, gradD, sharedT20GradD]; module
        have hnonneg : 0 ≤ g2 r := by
          exact mul_nonneg (by norm_num)
            (mul_nonneg (by norm_num) (c1EuclideanSymbolDistance_nonneg _))
        simp only [mul_one, map_zero, inner_zero_right, mul_zero, add_zero, hgv,
          map_smul, real_inner_smul_right, hg2]
        nlinarith)
      (by intros; norm_num)
      (by intro r hr; dsimp [g2]; norm_num)
      (by intro r hr; exact (hg2 r).symm)
      (by
        intro r hr
        have hh := c1EuclideanSymbolDistance_error_bound (F.flow t₀ x r)
        have hle : c1EuclideanSymbolDistance (F.flow t₀ x r) ≤ sharedT20D (F.flow t₀ x r) := by
          dsimp [sharedT20D]
          nlinarith [c1EuclideanSymbolDistance_nonneg (F.flow t₀ x r)]
        exact hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (by norm_num)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- 原文の象徴零集合を、同じ一点初期Kへ制限した目標。 -/
def sharedT20PointTarget (x : C1EuclideanAgentState) (t₀ : ℝ) : Set C1EuclideanAgentState :=
  closedLoopReachableSet (policyFlowReachableAt euclideanConsensusOptimalFlow {x} t₀) ∩
    c1EuclideanSymbolTarget

def sharedT20Agreement (x : C1EuclideanAgentState) : C1EuclideanAgentState :=
  c1EuclideanCoordinates.symm (agreementPoint (c1EuclideanCoordinates x))

/-- K内の象徴目標は、同じ初期状態の合意点singletonに一致する。 -/
theorem sharedT20PointTarget_eq_singleton (x : C1EuclideanAgentState)
    (hx : x ∈ c1EuclideanBox) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    sharedT20PointTarget x t₀ = {sharedT20Agreement x} := by
  have hsymbol (y : C1EuclideanAgentState) : y ∈ c1EuclideanSymbolTarget ↔
      c1EuclideanCoordinates y ∈ c1SymbolTarget c1SymbolAddress := by
    rw [← c1EuclideanSymbolDistance_zero_iff, c1EuclideanSymbolDistance_eq_coordinates,
      c1SymbolDistance_zero_iff]
  have himage : sharedT20PointTarget x t₀ = c1EuclideanCoordinates.symm ''
      pointTheorem20Target (c1EuclideanCoordinates x) t₀ 0 := by
    unfold sharedT20PointTarget
    rw [sharedT20_pointK_eq_image]
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, htarget⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      simpa using (hsymbol (c1EuclideanCoordinates.symm z)).mp htarget
    · rintro ⟨z, ⟨hz, htarget⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      exact (hsymbol _).mpr (by simpa using htarget)
  rw [himage, pointTheorem20Target_eq_pointSharedTCZ _ hx t₀ 0 ht₀,
    pointSharedTCZ_eq_singleton _ hx t₀ 0 ht₀, Set.image_singleton]
  rfl

/-- 全域象徴目標への最近点も合意点である。二次元距離の二乗を直接比較する。 -/
theorem sharedT20Agreement_minimizes_distance (y z : C1EuclideanAgentState)
    (hz : z ∈ c1EuclideanSymbolTarget) : dist y (sharedT20Agreement y) ≤ dist y z := by
  have hz' : z 0 = z 1 := hz
  let m : ℝ := (y 0 + y 1) / 2
  have hleft : dist y (sharedT20Agreement y) =
      Real.sqrt ((y 0 - m) ^ 2 + (y 1 - m) ^ 2) := by
    rw [PiLp.dist_eq_of_L2]
    simp [sharedT20Agreement, agreementPoint, meanState, c1EuclideanCoordinates,
      EuclideanSpace.equiv, m, Real.dist_eq, sq_abs]
  have hright : dist y z = Real.sqrt ((y 0 - z 0) ^ 2 + (y 1 - z 1) ^ 2) := by
    rw [PiLp.dist_eq_of_L2]
    simp [Real.dist_eq, sq_abs]
  rw [hleft, hright, ← hz']
  apply Real.sqrt_le_sqrt
  dsimp [m]
  nlinarith [sq_nonneg ((y 0 + y 1) / 2 - z 0)]

/-- 元の象徴零集合への距離は合意射影への距離に厳密一致する。 -/
theorem sharedT20_globalTarget_infDist (y : C1EuclideanAgentState) :
    Metric.infDist y c1EuclideanSymbolTarget = dist y (sharedT20Agreement y) := by
  apply le_antisymm
  · apply Metric.infDist_le_dist_of_mem
    rfl
  · apply (Metric.le_infDist c1EuclideanSymbolTarget_nonempty).mpr
    intro z hz
    exact sharedT20Agreement_minimizes_distance y z hz

/-- 同じflowは平均を保存するので、各時刻の合意射影は初期点の合意射影と等しい。 -/
theorem sharedT20Agreement_flow (x : C1EuclideanAgentState) (t₀ t : ℝ) :
    sharedT20Agreement (euclideanConsensusOptimalFlow.flow t₀ x t) = sharedT20Agreement x := by
  apply c1EuclideanCoordinates.injective
  simp only [sharedT20Agreement, ContinuousLinearEquiv.apply_symm_apply]
  have heq : c1EuclideanCoordinates (euclideanConsensusOptimalFlow.flow t₀ x t) =
      consensusOptimalFlow.flow t₀ (c1EuclideanCoordinates x) t := by
    simp [euclideanConsensusOptimalFlow]
  rw [heq]
  ext i
  fin_cases i <;> simp [agreementPoint, meanState, consensusOptimalFlow, halfDifference] <;> ring

/-- 軌道上では一点Kで目標を制限しても距離が変わらない。
これにより一般20入口の全距離結論を同じ一点K目標へそのまま移せる。 -/
theorem sharedT20PointTarget_infDist_eq (x : C1EuclideanAgentState)
    (hx : x ∈ c1EuclideanBox) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (t : ℝ) :
    Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x t) (sharedT20PointTarget x t₀) =
      Metric.infDist (euclideanConsensusOptimalFlow.flow t₀ x t) c1EuclideanSymbolTarget := by
  rw [sharedT20PointTarget_eq_singleton x hx t₀ ht₀, Metric.infDist_singleton,
    sharedT20_globalTarget_infDist, sharedT20Agreement_flow]

#print axioms sharedBase_theorem20_point_entry
#print axioms sharedT20PointTarget_infDist_eq
end Tomabechi.Consistency.R3
