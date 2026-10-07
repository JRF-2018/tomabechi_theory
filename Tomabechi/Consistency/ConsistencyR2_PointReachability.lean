import Tomabechi.Consistency.ConsistencyC1_ConsensusControl
import Tomabechi.Consistency.ConsistencyC1_Theorem3Bridge
import Tomabechi.Consistency.ConsistencyC1_O24

/-!
# R2: 一点初期状態からの合意点到達閉包

固定した一点からrate-3合意flowを動かすと、その閉到達集合は少なくとも
対応する合意点を含む。有限時刻の軌道列が合意点へ収束することから示す。
-/

noncomputable section

namespace Tomabechi.Consistency.R2

open Filter
open scoped Topology
open Tomabechi.Theorem1
open Tomabechi.Examples.Theorem2
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1Theorem3Bridge

/-- 初期状態の二主体平均を両座標に持つ合意点。 -/
def agreementPoint (x : AgentState) : AgentState := ![meanState x, meanState x]

/-- 線分上の点を、合意点からの残り割合 `r` で表す。 -/
def segmentPoint (x : AgentState) (r : ℝ) : AgentState :=
  ![meanState x + halfDifference x * r, meanState x - halfDifference x * r]

/-- 初期状態と合意点を結ぶ閉線分。 -/
def orbitSegment (x : AgentState) : Set AgentState :=
  segmentPoint x '' Set.Icc (0 : ℝ) 1

/-- 初期状態を一点に固定した方策閉ループ到達集合の閉包。 -/
def pointReachableClosure (x : AgentState) (t₀ : ℝ) : Set AgentState :=
  closedLoopReachableSet
    (policyFlowReachableAt consensusOptimalFlow ({x} : Set AgentState) t₀)

/-- 一点閉包を使った定理1の閾値集合。 -/
def pointTheorem1Target (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  {y | y ∈ pointReachableClosure x t₀ ∧ consensusV0 y t ≤ 1}

/-- 一点閉包を使った定理4の臨場感加重目標集合。 -/
def pointTheorem4Target (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  Tomabechi.Theorem4.weightedTCZ (pointReachableClosure x t₀)
    consensusPresenceV0 consensusPresenceP consensusPresenceQ 1 1 t

/-- 一点Kと定理2の共有TCZ条件を同時に課した目標。 -/
def pointSharedTCZ (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  {y | y ∈ pointReachableClosure x t₀ ∧ y ∈ DA.sharedTCZ box t}

/-- The original full-`Φ₃` zero target restricted to the point-initialized K. -/
def pointTheorem3Target (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  {y | y ∈ pointReachableClosure x t₀ ∧ c1Theorem3StatePhi3 y t = 0}

theorem agreementPoint_mem_box (x : AgentState) (hx : x ∈ box) :
    agreementPoint x ∈ box := by
  have ha := (abs_le.mp (hx 0))
  have hb := (abs_le.mp (hx 1))
  have hmlo : -(1 / 4 : ℝ) ≤ meanState x := by
    unfold meanState
    nlinarith
  have hmhi : meanState x ≤ 1 / 4 := by
    unfold meanState
    nlinarith
  intro i
  fin_cases i <;> simpa [agreementPoint, box] using abs_le.mpr ⟨hmlo, hmhi⟩

theorem agreementPoint_potential_eq_zero
    (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    DA.potential (agreementPoint x) t = 0 := by
  rw [sharedPotential_eq_coupling (agreementPoint x) (agreementPoint_mem_box x hx) t]
  simp [agreementPoint, Tomabechi.Examples.Theorem2.γ]

theorem agreementPoint_mem_sharedTCZ
    (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    agreementPoint x ∈ DA.sharedTCZ box t := by
  exact ⟨agreementPoint_mem_box x hx, agreementPoint_potential_eq_zero x hx t⟩

theorem optimalFlow_at_later_time_tendsto_agreementPoint
    (x : AgentState) (t₀ : ℝ) :
    Tendsto (fun n : ℕ => consensusOptimalFlow.flow t₀ x (t₀ + n))
      atTop (𝓝 (agreementPoint x)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun n : ℕ => (3 : ℝ) * n) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(3 : ℝ) * n)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    convert h using 1
    funext n
    congr 1
    ring
  have hdecay : Tendsto (fun n : ℕ => halfDifference x * Real.exp (-(3 : ℝ) * n))
      atTop (𝓝 0) := by simpa using tendsto_const_nhds.mul hexp
  have hconst : Tendsto (fun _ : ℕ => meanState x) atTop (𝓝 (meanState x)) :=
    tendsto_const_nhds
  have hplus : Tendsto
      (fun n : ℕ => meanState x + halfDifference x * Real.exp (-(3 : ℝ) * n))
      atTop (𝓝 (meanState x)) := by simpa using hconst.add hdecay
  have hminus : Tendsto
      (fun n : ℕ => meanState x - halfDifference x * Real.exp (-(3 : ℝ) * n))
      atTop (𝓝 (meanState x)) := by
    simpa [sub_eq_add_neg] using hconst.add hdecay.neg
  apply tendsto_pi_nhds.2
  intro i
  fin_cases i
  · simpa [consensusOptimalFlow, agreementPoint] using hplus
  · simpa [consensusOptimalFlow, agreementPoint] using hminus

theorem agreementPoint_mem_pointReachableClosure
    (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    agreementPoint x ∈ pointReachableClosure x t₀ := by
  have hseq : ∀ n : ℕ,
      consensusOptimalFlow.flow t₀ x (t₀ + n) ∈ pointReachableClosure x t₀ := by
    intro n
    change consensusOptimalFlow.flow t₀ x (t₀ + n) ∈
      closedLoopReachableSet
        (policyFlowReachableAt consensusOptimalFlow ({x} : Set AgentState) t₀)
    unfold closedLoopReachableSet
    apply subset_closure
    refine ⟨t₀ + n, ?_, ?_⟩
    · positivity
    · exact mem_policyFlowReachableAt_of_flow consensusOptimalFlow
        ({x} : Set AgentState) t₀ (t₀ + n) x (Set.mem_singleton x) (by linarith)
  exact isClosed_closure.mem_of_tendsto
    (optimalFlow_at_later_time_tendsto_agreementPoint x t₀)
    (Filter.Eventually.of_forall hseq)

/-- 一点到達閉包は、初期状態と合意点の間の閉線分に含まれる。 -/
theorem pointReachableClosure_subset_orbitSegment
    (x : AgentState) (t₀ : ℝ) :
    pointReachableClosure x t₀ ⊆ orbitSegment x := by
  have hclosed : IsClosed (orbitSegment x) := by
    unfold orbitSegment
    apply (isCompact_Icc.image_of_continuousOn ?_).isClosed
    have hc : Continuous (segmentPoint x) := by
      unfold segmentPoint
      fun_prop
    exact hc.continuousOn
  apply closure_minimal ?_ hclosed
  rintro y ⟨τ, hτ, hy⟩
  rcases hy with ⟨hstart, z, hz, hy⟩
  rcases Set.mem_singleton_iff.mp hz with rfl
  subst y
  let r : ℝ := Real.exp (-(3 : ℝ) * (τ - t₀))
  have hnonneg : 0 ≤ τ - t₀ := by linarith
  have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  refine ⟨r, ⟨hr0, hr1⟩, ?_⟩
  ext i
  fin_cases i <;> simp [segmentPoint, meanState, halfDifference, consensusOptimalFlow,
    r]

/-- 有限時刻で線分上の任意の正の割合を実現できる。 -/
theorem orbitSegment_subset_pointReachableClosure
    (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    orbitSegment x ⊆ pointReachableClosure x t₀ := by
  rintro y ⟨r, hr, rfl⟩
  by_cases hr0 : r = 0
  · rw [hr0]
    simpa [segmentPoint, agreementPoint, meanState] using
      agreementPoint_mem_pointReachableClosure x t₀ ht₀
  · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hlog : Real.log r ≤ 0 := Real.log_nonpos (le_of_lt hrpos) hr.2
    let τ : ℝ := t₀ - Real.log r / 3
    have hstart : t₀ ≤ τ := by dsimp [τ]; linarith
    have hexp : Real.exp (-(3 : ℝ) * (τ - t₀)) = r := by
      rw [show -(3 : ℝ) * (τ - t₀) = Real.log r by dsimp [τ]; ring,
        Real.exp_log hrpos]
    have hexp' : Real.exp (-(3 * (τ - t₀))) = r := by
      convert hexp using 1 <;> congr 1 <;> ring
    unfold pointReachableClosure closedLoopReachableSet
    apply subset_closure
    refine ⟨τ, ?_, ?_⟩
    · exact le_trans ht₀ hstart
    · have hstate : consensusOptimalFlow.flow t₀ x τ = segmentPoint x r := by
        ext i
        fin_cases i <;>
          simp [segmentPoint, meanState, halfDifference, consensusOptimalFlow] <;>
          first | exact Or.inl hexp' | exact Or.inl hexp'
      rw [← hstate]
      exact mem_policyFlowReachableAt_of_flow consensusOptimalFlow
        ({x} : Set AgentState) t₀ τ x (Set.mem_singleton x) hstart

theorem pointReachableClosure_eq_orbitSegment
    (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    pointReachableClosure x t₀ = orbitSegment x := by
  exact Set.Subset.antisymm (pointReachableClosure_subset_orbitSegment x t₀)
    (orbitSegment_subset_pointReachableClosure x t₀ ht₀)

/-- 線分上の点から同じrate-3 flowを進めても、線分上にとどまる。 -/
theorem consensusOptimalFlow_segmentPoint
    (x : AgentState) (r s t : ℝ) :
    consensusOptimalFlow.flow s (segmentPoint x r) t =
      segmentPoint x (r * Real.exp (-(3 : ℝ) * (t - s))) := by
  ext i
  fin_cases i <;>
    simp [consensusOptimalFlow, segmentPoint, meanState, halfDifference] <;>
    ring

/-- 一点閉到達集合は開始時刻以後のflowで前向き不変である。 -/
theorem pointReachableClosure_forward_invariant
    (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    {y : AgentState} (hy : y ∈ pointReachableClosure x t₀)
    {s t : ℝ} (hst : s ≤ t) :
    consensusOptimalFlow.flow s y t ∈ pointReachableClosure x t₀ := by
  rw [pointReachableClosure_eq_orbitSegment x t₀ ht₀] at hy ⊢
  rcases hy with ⟨r, hr, rfl⟩
  rw [consensusOptimalFlow_segmentPoint]
  refine ⟨r * Real.exp (-(3 : ℝ) * (t - s)), ?_, rfl⟩
  constructor
  · exact mul_nonneg hr.1 (le_of_lt (Real.exp_pos _))
  · calc
      r * Real.exp (-(3 : ℝ) * (t - s)) ≤ r * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by nlinarith [hst])) hr.1
      _ ≤ 1 := by nlinarith [hr.2]

/-- Rate-3軌道から、その初期点の合意点までの距離は半差分の指数減衰で抑えられる。 -/
theorem consensusOptimalFlow_dist_agreementPoint_le
    (x : AgentState) (t₀ t : ℝ) :
    dist (consensusOptimalFlow.flow t₀ x t) (agreementPoint x) ≤
      |halfDifference x| * Real.exp (-(3 : ℝ) * (t - t₀)) := by
  rw [dist_pi_le_iff (by positivity)]
  intro i
  fin_cases i <;>
    rw [Real.dist_eq] <;>
    simp [consensusOptimalFlow, agreementPoint, meanState, halfDifference,
      abs_mul, abs_of_pos (Real.exp_pos _)]

/-- 箱内軌道の一点目標への距離二乗は、対応する共有ポテンシャル以下で指数減衰する。 -/
theorem consensusOptimalFlow_pointTarget_distance_sq_le
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀)
    (ht : t₀ ≤ t) :
    (Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (pointTheorem1Target x t₀ t)) ^ 2 ≤
      DA.potential x t₀ * Real.exp (-(6 : ℝ) * (t - t₀)) := by
  have hagree : agreementPoint x ∈ pointTheorem1Target x t₀ t := by
    refine ⟨agreementPoint_mem_pointReachableClosure x t₀ ht₀, ?_⟩
    change 1 + DA.potential (agreementPoint x) 0 ≤ 1
    rw [agreementPoint_potential_eq_zero x hx 0]
    norm_num
  have hinf := Metric.infDist_le_dist_of_mem
    (x := consensusOptimalFlow.flow t₀ x t) (y := agreementPoint x) hagree
  have hdist := consensusOptimalFlow_dist_agreementPoint_le x t₀ t
  have hexp : Real.exp (-(6 : ℝ) * (t - t₀)) =
      (Real.exp (-(3 : ℝ) * (t - t₀))) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ (dist (consensusOptimalFlow.flow t₀ x t) (agreementPoint x)) ^ 2 := by
      exact pow_le_pow_left₀ (Metric.infDist_nonneg) hinf 2
    _ ≤ (|halfDifference x| * Real.exp (-(3 : ℝ) * (t - t₀))) ^ 2 :=
      pow_le_pow_left₀ dist_nonneg hdist 2
    _ ≤ DA.potential x t₀ * Real.exp (-(6 : ℝ) * (t - t₀)) := by
      rw [sharedPotential_eq_coupling x hx t₀, hexp]
      rw [show x 0 - x 1 = 2 * halfDifference x by
        dsimp [halfDifference]; ring]
      simp only [γ]
      rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg (|halfDifference x| *
        Real.exp (-(3 : ℝ) * (t - t₀)))]

/-- 定理4の一点閉包付き重み目標にも、同じ直接的な距離評価が成り立つ。 -/
theorem consensusOptimalFlow_pointTheorem4_distance_sq_le
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀)
    (ht : t₀ ≤ t) :
    (Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (pointTheorem4Target x t₀ t)) ^ 2 ≤
      DA.potential x t₀ * Real.exp (-(6 : ℝ) * (t - t₀)) := by
  have hagree : agreementPoint x ∈ pointTheorem4Target x t₀ t := by
    change agreementPoint x ∈ pointReachableClosure x t₀ ∧
      Tomabechi.Theorem4.effectivePotential
        (consensusPresenceV0 (agreementPoint x) t)
        (consensusPresenceP (agreementPoint x) t)
        (consensusPresenceQ (agreementPoint x) t) 1 ≤ 1
    refine ⟨agreementPoint_mem_pointReachableClosure x t₀ ht₀, ?_⟩
    rw [consensusPresence_effective_eq_shared]
    rw [agreementPoint_potential_eq_zero x hx 0]
    norm_num
  have hinf := Metric.infDist_le_dist_of_mem
    (x := consensusOptimalFlow.flow t₀ x t) (y := agreementPoint x) hagree
  have hdist := consensusOptimalFlow_dist_agreementPoint_le x t₀ t
  have hexp : Real.exp (-(6 : ℝ) * (t - t₀)) =
      (Real.exp (-(3 : ℝ) * (t - t₀))) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ (dist (consensusOptimalFlow.flow t₀ x t) (agreementPoint x)) ^ 2 :=
      pow_le_pow_left₀ (Metric.infDist_nonneg) hinf 2
    _ ≤ (|halfDifference x| * Real.exp (-(3 : ℝ) * (t - t₀))) ^ 2 :=
      pow_le_pow_left₀ dist_nonneg hdist 2
    _ ≤ DA.potential x t₀ * Real.exp (-(6 : ℝ) * (t - t₀)) := by
      rw [sharedPotential_eq_coupling x hx t₀, hexp]
      rw [show x 0 - x 1 = 2 * halfDifference x by
        dsimp [halfDifference]; ring]
      simp only [γ]
      rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg (|halfDifference x| *
        Real.exp (-(3 : ℝ) * (t - t₀)))]

/-- 一点Kに対する最適化Selfは、同じrate-3方策と閉ループflowを保持する。 -/
def pointOptimalSelf (t : ℝ) (possibleWorlds : Set AgentState) : Set AgentState :=
  {y | y ∈ possibleWorlds ∧ consensusV0 y t ≤ 1}

def pointOptimalTCZ (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  pointOptimalSelf t (pointReachableClosure x t₀)

structure PointConsensusSelfEgoTCZ (x₀ : AgentState) (t₀ : ℝ) where
  Self : ℝ → Set AgentState → Set AgentState
  Ego : AgentState → ℝ → ℝ
  TCZ : ℝ → Set AgentState
  initialSet : Set AgentState
  reachable : Set AgentState
  flow : ClosedLoopPolicyFlow AgentState ℝ
  initialSet_is_singleton : initialSet = {x₀}
  reachable_is_closed_loop_closure :
    reachable = closedLoopReachableSet (policyFlowReachableAt flow initialSet t₀)
  self_is_tcz : ∀ t, Self t reachable = TCZ t
  ego_is_flow_feedback : ∀ x t, Ego x t = flow.feedback x t

def pointOptimalConsensusAdapter (x : AgentState) (t₀ : ℝ) :
    PointConsensusSelfEgoTCZ x t₀ where
  Self := pointOptimalSelf
  Ego := fun y t => consensusOptimalFlow.feedback y t
  TCZ := pointOptimalTCZ x t₀
  initialSet := {x}
  reachable := pointReachableClosure x t₀
  flow := consensusOptimalFlow
  initialSet_is_singleton := rfl
  reachable_is_closed_loop_closure := rfl
  self_is_tcz := by intro t; rfl
  ego_is_flow_feedback := by intro y t; rfl

/-- Point-initial-set specialization of the project O24 adapter type. It
retains the singleton as the actual initial set and uses its exact closed-loop
reachability closure as `reachable`. -/
def pointOptimalConsensusC1O24Adapter (x : AgentState) (t₀ : ℝ) :
    Tomabechi.Consistency.ConsistencyC1O24.C1OptimalConsensusAdapter t₀ where
  Self := pointOptimalSelf
  Ego := fun y t => consensusOptimalFlow.feedback y t
  TCZ := pointOptimalTCZ x t₀
  initialSet := {x}
  reachable := pointReachableClosure x t₀
  flow := consensusOptimalFlow
  reachable_is_closed_loop_closure := rfl
  self_is_tcz := by intro t; rfl
  ego_is_flow_feedback := by intro y t; rfl

theorem pointOptimalConsensusC1O24Adapter_initialSet
    (x : AgentState) (t₀ : ℝ) :
    (pointOptimalConsensusC1O24Adapter x t₀).initialSet = {x} := by
  simp [pointOptimalConsensusC1O24Adapter]

theorem pointOptimalConsensusC1O24Adapter_reachable
    (x : AgentState) (t₀ : ℝ) :
    (pointOptimalConsensusC1O24Adapter x t₀).reachable =
      closedLoopReachableSet (policyFlowReachableAt
        (pointOptimalConsensusC1O24Adapter x t₀).flow
        (pointOptimalConsensusC1O24Adapter x t₀).initialSet t₀) :=
  (pointOptimalConsensusC1O24Adapter x t₀).reachable_is_closed_loop_closure

theorem pointOptimalConsensusAdapter_uses_singleton_initial_set
    (x : AgentState) (t₀ : ℝ) :
    (pointOptimalConsensusAdapter x t₀).initialSet = {x} := rfl

theorem pointOptimalConsensusAdapter_reachable_is_exact_K
    (x : AgentState) (t₀ : ℝ) :
    (pointOptimalConsensusAdapter x t₀).reachable =
      closedLoopReachableSet
        (policyFlowReachableAt (pointOptimalConsensusAdapter x t₀).flow
          (pointOptimalConsensusAdapter x t₀).initialSet t₀) :=
  (pointOptimalConsensusAdapter x t₀).reachable_is_closed_loop_closure

theorem pointReachableClosure_subset_box
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) :
    pointReachableClosure x t₀ ⊆ box := by
  have hclosed : IsClosed box := by
    have heq : box = Set.pi Set.univ
        (fun _ : Fin 2 => Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
      ext z
      change (∀ i, |z i| ≤ 1 / 4) ↔
        (∀ i ∈ Set.univ, z i ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4))
      simp only [Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
    rw [heq]
    exact isClosed_set_pi (fun _ _ => isClosed_Icc)
  apply closure_minimal ?_ hclosed
  rintro y ⟨τ, hτ, hy⟩
  rcases hy with ⟨hstart, z, hz, hy⟩
  have hz' : z = x := Set.mem_singleton_iff.mp hz
  subst z
  rw [hy]
  exact consensusOptimalFlow_forward_invariant x hx t₀ τ hstart

/-- 点初期値のSelf目標はその初期点に固有の合意点一つになる。 -/
theorem pointOptimalTCZ_eq_singleton
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    pointOptimalTCZ x t₀ t = {agreementPoint x} := by
  ext y
  constructor
  · rintro ⟨hyK, hV⟩
    have hybox := pointReachableClosure_subset_box x hx t₀ hyK
    have hpot : DA.potential y 0 = 0 := by
      change 1 + DA.potential y 0 ≤ 1 at hV
      have hform := sharedPotential_eq_coupling y hybox 0
      rw [hform] at hV
      have hγ : 0 < γ := by norm_num [γ]
      have hsq : (y 0 - y 1) ^ 2 = 0 := by nlinarith
      have hgap : y 0 - y 1 = 0 := (sq_eq_zero_iff).mp hsq
      rw [hform, hgap]
      simp
    rw [pointReachableClosure_eq_orbitSegment x t₀ ht₀] at hyK
    rcases hyK with ⟨r, hr, hy⟩
    have hcoords : y 0 = y 1 := by
      have hform := sharedPotential_eq_coupling y hybox 0
      rw [hform] at hpot
      have hγ : γ ≠ 0 := by norm_num [γ]
      have hsq : (y 0 - y 1) ^ 2 = 0 := (mul_eq_zero.mp hpot).resolve_left hγ
      exact sub_eq_zero.mp ((sq_eq_zero_iff.mp hsq))
    have heq : y = agreementPoint x := by
      have h0 := congrFun hy 0
      have h1 := congrFun hy 1
      have h0' : meanState x + halfDifference x * r = y 0 := by
        simpa [segmentPoint] using h0
      have h1' : meanState x - halfDifference x * r = y 1 := by
        simpa [segmentPoint] using h1
      have hseg : meanState x + halfDifference x * r =
          meanState x - halfDifference x * r := by
        rw [h0', h1']
        exact hcoords
      have hy0 : y 0 = meanState x := by
        rw [← h0']
        nlinarith [hseg]
      have hy1 : y 1 = meanState x := by
        rw [← h1']
        nlinarith [hseg]
      ext i
      fin_cases i
      · simpa [agreementPoint] using hy0
      · simpa [agreementPoint] using hy1
    simpa [heq]
  · intro hy
    have hy' : y = agreementPoint x := by simpa using hy
    subst y
    constructor
    · exact agreementPoint_mem_pointReachableClosure x t₀ ht₀
    · change 1 + DA.potential (agreementPoint x) 0 ≤ 1
      rw [agreementPoint_potential_eq_zero x hx 0]
      norm_num

theorem pointOptimalConsensusTCZ_eq_singleton
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    (pointOptimalConsensusAdapter x t₀).TCZ t = {agreementPoint x} :=
  pointOptimalTCZ_eq_singleton x hx t₀ t ht₀

/-- 点初期値版O24距離評価。Selfの目標を全箱ではなく、その一点の閉到達Kで切り出す。 -/
theorem pointOptimalConsensusO24_distance
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ)
    (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) :
    Metric.infDist
      ((pointOptimalConsensusC1O24Adapter x t₀).flow.flow t₀ x t)
      ((pointOptimalConsensusC1O24Adapter x t₀).TCZ t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀)) := by
  change Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (pointOptimalTCZ x t₀ t) ≤
    Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))
  rw [pointOptimalTCZ_eq_singleton x hx t₀ t ht₀,
    Metric.infDist_singleton]
  have hroot : |halfDifference x| ≤ Real.sqrt (DA.potential x t₀) := by
    rw [← Real.sqrt_sq (abs_nonneg (halfDifference x))]
    apply Real.sqrt_le_sqrt
    rw [sharedPotential_eq_coupling x hx t₀, show x 0 - x 1 =
      2 * halfDifference x by dsimp [halfDifference]; ring]
    simp [γ]
    nlinarith [sq_nonneg (halfDifference x)]
  calc
    dist (consensusOptimalFlow.flow t₀ x t) (agreementPoint x) ≤
        |halfDifference x| * Real.exp (-(3 : ℝ) * (t - t₀)) :=
      consensusOptimalFlow_dist_agreementPoint_le x t₀ t
    _ ≤ Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀)) := by
      exact mul_le_mul_of_nonneg_right hroot (le_of_lt (Real.exp_pos _))

theorem pointSharedTCZ_eq_singleton
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    pointSharedTCZ x t₀ t = {agreementPoint x} := by
  ext y
  constructor
  · rintro ⟨hyK, hyShared⟩
    have hyBox := pointReachableClosure_subset_box x hx t₀ hyK
    have hgap : y 0 = y 1 := by
      have hpot := sharedPotential_eq_coupling y hyBox t
      rcases hyShared with ⟨_, hpotential⟩
      rw [hpot] at hpotential
      have hγ : γ ≠ 0 := by norm_num [γ]
      have hsq : (y 0 - y 1) ^ 2 = 0 :=
        (mul_eq_zero.mp hpotential).resolve_left hγ
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    rw [pointReachableClosure_eq_orbitSegment x t₀ ht₀] at hyK
    rcases hyK with ⟨r, hr, hyEq⟩
    have h0 := congrFun hyEq 0
    have h1 := congrFun hyEq 1
    have h0' : meanState x + halfDifference x * r = y 0 := by
      simpa [segmentPoint] using h0
    have h1' : meanState x - halfDifference x * r = y 1 := by
      simpa [segmentPoint] using h1
    have hseg : meanState x + halfDifference x * r =
        meanState x - halfDifference x * r := by rw [h0', h1']; exact hgap
    have hy0 : y 0 = meanState x := by rw [← h0']; nlinarith [hseg]
    have hy1 : y 1 = meanState x := by rw [← h1']; nlinarith [hseg]
    have heq : y = agreementPoint x := by
      ext i
      fin_cases i
      · simpa [agreementPoint] using hy0
      · simpa [agreementPoint] using hy1
    simpa [heq]
  · intro hy
    have hy' : y = agreementPoint x := by simpa using hy
    subst y
    exact ⟨agreementPoint_mem_pointReachableClosure x t₀ ht₀,
      agreementPoint_mem_sharedTCZ x hx t⟩

/-- 定理2共有TCZを一点Kで制限した目標にも同じrate-3指数評価が成り立つ。 -/
theorem consensusOptimalFlow_pointSharedTCZ_distance
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ)
    (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) :
    Metric.infDist (consensusOptimalFlow.flow t₀ x t) (pointSharedTCZ x t₀ t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀)) := by
  rw [pointSharedTCZ_eq_singleton x hx t₀ t ht₀, Metric.infDist_singleton]
  have hroot : |halfDifference x| ≤ Real.sqrt (DA.potential x t₀) := by
    rw [← Real.sqrt_sq (abs_nonneg (halfDifference x))]
    apply Real.sqrt_le_sqrt
    rw [sharedPotential_eq_coupling x hx t₀, show x 0 - x 1 =
      2 * halfDifference x by dsimp [halfDifference]; ring]
    simp [γ]
    nlinarith [sq_nonneg (halfDifference x)]
  calc
    dist (consensusOptimalFlow.flow t₀ x t) (agreementPoint x) ≤
        |halfDifference x| * Real.exp (-(3 : ℝ) * (t - t₀)) :=
      consensusOptimalFlow_dist_agreementPoint_le x t₀ t
    _ ≤ Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀)) :=
      mul_le_mul_of_nonneg_right hroot (le_of_lt (Real.exp_pos _))

/-- 定理20の住所記号が選ぶ対角目標を、一点K上に制限した版。 -/
def pointTheorem20Target (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  {y | y ∈ pointReachableClosure x t₀ ∧
    y ∈ c1SymbolTarget c1SymbolAddress}

theorem pointTheorem20Target_eq_pointSharedTCZ
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    pointTheorem20Target x t₀ t = pointSharedTCZ x t₀ t := by
  have hsymbol := c1SymbolTarget_box_eq_sharedTCZ t
  ext y
  constructor
  · rintro ⟨hyK, hySymbol⟩
    have hyBox := pointReachableClosure_subset_box x hx t₀ hyK
    have hyShared : y ∈ DA.sharedTCZ box t := by
      rw [← hsymbol]
      exact ⟨hyBox, hySymbol⟩
    exact ⟨hyK, hyShared⟩
  · rintro ⟨hyK, hyShared⟩
    have hyBox := pointReachableClosure_subset_box x hx t₀ hyK
    rw [← hsymbol] at hyShared
    exact ⟨hyK, hyShared.2⟩

theorem consensusOptimalFlow_pointTheorem20_distance
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ)
    (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) :
    Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (pointTheorem20Target x t₀ t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀)) := by
  rw [pointTheorem20Target_eq_pointSharedTCZ x hx t₀ t ht₀]
  exact consensusOptimalFlow_pointSharedTCZ_distance x hx t₀ t ht₀ ht

theorem pointReachableClosure_nonempty
    (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (pointReachableClosure x t₀).Nonempty := by
  exact ⟨agreementPoint x, agreementPoint_mem_pointReachableClosure x t₀ ht₀⟩

/-- 零平均スライスでは、同じ一点到達閉包上に定理3の完全ポテンシャル目標がある。 -/
theorem pointReachableClosure_has_theorem3Target
    (x : AgentState) (hmean : x 0 + x 1 = 0)
    (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    ∃ z ∈ pointReachableClosure x t₀, c1Theorem3StatePhi3 z t = 0 := by
  have hagree : agreementPoint x = c1Theorem3Zero := by
    ext i
    fin_cases i <;> simp [agreementPoint, meanState, c1Theorem3Zero] <;> linarith
  have htarget : c1Theorem3Zero ∈ pointReachableClosure x t₀ := by
    rw [← hagree]
    exact agreementPoint_mem_pointReachableClosure x t₀ ht₀
  have hzbox : c1Theorem3Zero ∈ box := by
    intro i
    fin_cases i <;> norm_num [c1Theorem3Zero, box]
  refine ⟨c1Theorem3Zero, htarget, ?_⟩
  rw [c1Theorem3StatePhi3_eq_on_box c1Theorem3Zero hzbox t]
  simp [c1Theorem3Zero]

/-- On the zero-mean slice the point-K original Theorem 3 target is exactly
the singleton origin. -/
theorem pointTheorem3Target_eq_singleton
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    pointTheorem3Target x t₀ t = {c1Theorem3Zero} := by
  have hagree : agreementPoint x = c1Theorem3Zero := by
    ext i
    fin_cases i <;> simp [agreementPoint, meanState, c1Theorem3Zero] <;> linarith
  ext z
  constructor
  · rintro ⟨hzK, hphi⟩
    have hzbox := pointReachableClosure_subset_box x hx t₀ hzK
    rw [c1Theorem3StatePhi3_eq_on_box z hzbox t] at hphi
    have hz0 : z 0 ^ 2 = 0 := by nlinarith [sq_nonneg (z 0 - z 1)]
    have hz1 : z 1 ^ 2 = 0 := by nlinarith [sq_nonneg (z 0 - z 1)]
    have hz0' : z 0 = 0 := (sq_eq_zero_iff).mp hz0
    have hz1' : z 1 = 0 := (sq_eq_zero_iff).mp hz1
    have hzero : z = c1Theorem3Zero := by
      ext i
      fin_cases i <;> simp [c1Theorem3Zero, hz0', hz1']
    simpa [hzero]
  · intro hz
    have hz' : z = c1Theorem3Zero := by simpa using hz
    subst z
    constructor
    · rw [← hagree]
      exact agreementPoint_mem_pointReachableClosure x t₀ ht₀
    · rw [c1Theorem3StatePhi3_eq_on_box c1Theorem3Zero (by
        intro i
        simp [c1Theorem3Zero, box]) t]
      simp [c1Theorem3Zero]

/-- The original Theorem 3 point-K target has a rate-3 distance estimate on
the zero-mean slice. -/
theorem consensusOptimalFlow_pointTheorem3_distance
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) :
    Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (pointTheorem3Target x t₀ t) ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀)) := by
  rw [pointTheorem3Target_eq_singleton x hx hmean t₀ t ht₀,
    Metric.infDist_singleton]
  have hagree : agreementPoint x = c1Theorem3Zero := by
    ext i
    fin_cases i <;> simp [agreementPoint, meanState, c1Theorem3Zero] <;> linarith
  have hroot : |halfDifference x| ≤ Real.sqrt (DA.potential x t₀) := by
    rw [← Real.sqrt_sq (abs_nonneg (halfDifference x))]
    apply Real.sqrt_le_sqrt
    rw [sharedPotential_eq_coupling x hx t₀, show x 0 - x 1 =
      2 * halfDifference x by dsimp [halfDifference]; ring]
    simp [γ]
    nlinarith [sq_nonneg (halfDifference x)]
  calc
    dist (consensusOptimalFlow.flow t₀ x t) (c1Theorem3Zero) =
        dist (consensusOptimalFlow.flow t₀ x t) (agreementPoint x) := by rw [hagree]
    _ ≤ |halfDifference x| * Real.exp (-(3 : ℝ) * (t - t₀)) :=
      consensusOptimalFlow_dist_agreementPoint_le x t₀ t
    _ ≤ Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀)) :=
      mul_le_mul_of_nonneg_right hroot (le_of_lt (Real.exp_pos _))

/-- On the zero-mean slice, the original full `Φ₃` residual along the
point-initialized rate-3 flow decays exactly at rate 6. -/
theorem consensusOptimalFlow_zeroMean_theorem3_residual_eq
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ t : ℝ) (ht : t₀ ≤ t) :
    c1Theorem3StatePhi3 (consensusOptimalFlow.flow t₀ x t) t =
      c1Theorem3StatePhi3 x t₀ * Real.exp (-6 * (t - t₀)) := by
  have hflowbox := consensusOptimalFlow_forward_invariant x hx t₀ t ht
  have hx1 : x 1 = -x 0 := by linarith
  have hexp : Real.exp (-(6 * (t - t₀))) =
      (Real.exp (-3 * (t - t₀))) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [c1Theorem3StatePhi3_eq_on_box _ hflowbox t,
    c1Theorem3StatePhi3_eq_on_box x hx t₀]
  simp [consensusOptimalFlow, meanState, halfDifference, hx1]
  rw [hexp]
  ring

theorem pointTheorem1Target_nonempty
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    (pointTheorem1Target x t₀ t).Nonempty := by
  refine ⟨agreementPoint x, agreementPoint_mem_pointReachableClosure x t₀ ht₀, ?_⟩
  change 1 + DA.potential (agreementPoint x) 0 ≤ 1
  rw [agreementPoint_potential_eq_zero x hx 0]
  norm_num

theorem pointTheorem4Target_nonempty
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    (pointTheorem4Target x t₀ t).Nonempty := by
  refine ⟨agreementPoint x, agreementPoint_mem_pointReachableClosure x t₀ ht₀, ?_⟩
  rw [consensusPresence_effective_eq_shared]
  rw [agreementPoint_potential_eq_zero x hx 0]
  norm_num

end Tomabechi.Consistency.R2
