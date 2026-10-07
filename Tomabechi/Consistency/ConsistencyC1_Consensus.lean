import Theorem1_4_HFlow
import Tomabechi.Examples.Theorem2_SharedTCZ

/-!
# C1: 二主体合意flowによる定理2の全初期値モデル

二主体の平均を保ちながら不一致だけを指数的に減衰させる連続時間合意系を作る。
初期値を非自明なコンパクト箱に取り、局所評価の閾値条件と正の辺結合を同時に保つ。
-/

noncomputable section

namespace Tomabechi.Consistency.ConsistencyC1Consensus

open MeasureTheory
open Filter
open scoped Topology
open Tomabechi.Theorem1
open Tomabechi.Theorem2
open Tomabechi.Examples.Theorem2

abbrev AgentState := Fin 2 → ℝ

def box : Set AgentState := {x | ∀ i, |x i| ≤ 1 / 4}

def meanState (x : AgentState) : ℝ := (x 0 + x 1) / 2

def halfDifference (x : AgentState) : ℝ := (x 0 - x 1) / 2

def consensusOrbit (m d τ : ℝ) : AgentState :=
  ![m + d * Real.exp (-2 * τ), m - d * Real.exp (-2 * τ)]

def consensusFlow : ClosedLoopPolicyFlow AgentState Unit where
  admissible := fun _ => True
  feedback := fun _ _ => ()
  vectorField := fun x _ _ => ![ -(x 0 - x 1), x 0 - x 1 ]
  flow := fun t₀ x t => consensusOrbit (meanState x) (halfDifference x) (t - t₀)
  feedback_admissible := by intro x t; trivial
  initial := by
    intro t₀ x
    change consensusOrbit (meanState x) (halfDifference x) (t₀ - t₀) = x
    simp only [sub_self]
    ext i
    fin_cases i <;> simp [consensusOrbit, meanState, halfDifference] <;> ring
  restart := by
    intro t₀ x s t h₀s hst
    change consensusOrbit (meanState x) (halfDifference x) (t - t₀) =
      consensusOrbit
        (meanState (consensusOrbit (meanState x) (halfDifference x) (s - t₀)))
        (halfDifference (consensusOrbit (meanState x) (halfDifference x) (s - t₀)))
        (t - s)
    have hmean : meanState (consensusOrbit (meanState x) (halfDifference x) (s - t₀)) = meanState x := by
      simp [meanState, consensusOrbit]
    have hdiff : halfDifference
        (consensusOrbit (meanState x) (halfDifference x) (s - t₀)) =
          halfDifference x * Real.exp (-2 * (s - t₀)) := by
      simp [halfDifference, consensusOrbit]
    rw [hmean, hdiff]
    ext i
    fin_cases i <;> simp [consensusOrbit] <;>
      rw [show -(2 * (t - t₀)) = -2 * (s - t₀) + -2 * (t - s) by ring,
        Real.exp_add] <;> ring

/-- Flowの二主体間の差は、初期差に指数因子を掛けたものとなる。 -/
theorem consensusFlow_gap (x : AgentState) (t₀ t : ℝ) :
    (consensusFlow.flow t₀ x t) 0 - (consensusFlow.flow t₀ x t) 1 =
      (x 0 - x 1) * Real.exp (-2 * (t - t₀)) := by
  simp [consensusFlow, consensusOrbit, meanState, halfDifference]
  ring

/- `consensusFlow` の座標ごとの式は滑らかであり、同じfeedbackのベクトル場を満たす。 -/
def differentiableConsensusFlow : DifferentiableClosedLoopPolicyFlow AgentState Unit where
  toClosedLoopPolicyFlow := consensusFlow
  solves := by
    intro t₀ x t ht
    apply hasDerivAt_pi.2
    intro i
    have hlin : HasDerivAt (fun s : ℝ => -2 * (s - t₀)) (-2) t := by
      simpa using (hasDerivAt_id t).sub_const t₀ |>.const_mul (-2)
    have hexp := (Real.hasDerivAt_exp (-2 * (t - t₀))).comp t hlin
    fin_cases i
    · have hcoord := (hexp.const_mul (halfDifference x)).add_const (meanState x)
      convert hcoord using 1
      · funext s
        simp [consensusFlow, consensusOrbit]
        ring
      · simp [consensusFlow, consensusOrbit]
        ring
    · have hcoord := (hexp.const_mul (-halfDifference x)).add_const (meanState x)
      convert hcoord using 1
      · funext s
        simp [consensusFlow, consensusOrbit]
        ring
      · simp [consensusFlow, consensusOrbit]
        ring


/-- 正の時間差では指数係数が0と1の間にある。 -/
theorem consensus_exp_bounds (t₀ t : ℝ) (ht : t₀ ≤ t) :
    0 ≤ Real.exp (-2 * (t - t₀)) ∧ Real.exp (-2 * (t - t₀)) ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    nlinarith

/-- 重みが0と1の間なら、区間内二点の凸結合も区間内にある。 -/
theorem convexCombination_mem_box (a b α : ℝ)
    (ha : |a| ≤ 1 / 4) (hb : |b| ≤ 1 / 4)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    |α * a + (1 - α) * b| ≤ 1 / 4 := by
  have haLo := (abs_le.mp ha).1
  have haHi := (abs_le.mp ha).2
  have hbLo := (abs_le.mp hb).1
  have hbHi := (abs_le.mp hb).2
  have hβ : 0 ≤ 1 - α := by linarith
  rw [abs_le]
  constructor
  · have h1 := mul_le_mul_of_nonneg_left haLo hα
    have h2 := mul_le_mul_of_nonneg_left hbLo hβ
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left haHi hα
    have h2 := mul_le_mul_of_nonneg_left hbHi hβ
    nlinarith

/-- 合意flowは、平均を係数とする凸結合なので、初期箱を前方不変に保つ。 -/
theorem consensusFlow_forward_invariant
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht : t₀ ≤ t) :
    consensusFlow.flow t₀ x t ∈ box := by
  intro i
  have he := consensus_exp_bounds t₀ t ht
  have hαLo : 0 ≤ (1 + Real.exp (-2 * (t - t₀))) / 2 := by linarith
  have hαHi : (1 + Real.exp (-2 * (t - t₀))) / 2 ≤ 1 := by linarith
  have hβLo : 0 ≤ (1 - Real.exp (-2 * (t - t₀))) / 2 := by linarith
  have hβHi : (1 - Real.exp (-2 * (t - t₀))) / 2 ≤ 1 := by linarith
  have h0 := hx 0
  have h1 := hx 1
  fin_cases i
  · change |meanState x + halfDifference x * Real.exp (-2 * (t - t₀))| ≤ 1 / 4
    have hform : meanState x + halfDifference x * Real.exp (-2 * (t - t₀)) =
        ((1 + Real.exp (-2 * (t - t₀))) / 2) * x 0 +
          (1 - (1 + Real.exp (-2 * (t - t₀))) / 2) * x 1 := by
      simp [meanState, halfDifference]
      ring
    rw [hform]
    exact convexCombination_mem_box (x 0) (x 1)
      ( (1 + Real.exp (-2 * (t - t₀))) / 2) h0 h1 hαLo hαHi
  · change |meanState x - halfDifference x * Real.exp (-2 * (t - t₀))| ≤ 1 / 4
    have hform : meanState x - halfDifference x * Real.exp (-2 * (t - t₀)) =
        ((1 - Real.exp (-2 * (t - t₀))) / 2) * x 0 +
          (1 - (1 - Real.exp (-2 * (t - t₀))) / 2) * x 1 := by
      simp [meanState, halfDifference]
      ring
    rw [hform]
    exact convexCombination_mem_box (x 0) (x 1)
      ((1 - Real.exp (-2 * (t - t₀))) / 2) h0 h1 hβLo hβHi

/-- 初期箱は二つの閉区間の逆像の共通部分なので閉集合である。 -/
theorem box_isClosed : IsClosed box := by
  have hrepr : box = ⋂ i : Fin 2, (fun x : AgentState => x i) ⁻¹' Set.Icc (-(1 / 4 : ℝ)) (1 / 4) := by
    ext x
    simp [box, abs_le]
  rw [hrepr]
  apply isClosed_iInter
  intro i
  exact isClosed_Icc.preimage (continuous_apply i)

/-- flowが生成する閉到達集合は初期箱そのものになる。 -/
theorem consensusFlow_reachable_closure_eq_box (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    closedLoopReachableSet (policyFlowReachableAt consensusFlow box t₀) = box := by
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ box_isClosed
    rintro y ⟨τ, hτ, hy⟩
    rcases hy with ⟨hstart, x, hx, rfl⟩
    exact consensusFlow_forward_invariant x hx t₀ τ hstart
  · intro y hy
    apply subset_closure
    refine ⟨t₀, ht₀, ?_⟩
    exact ⟨le_rfl, y, hy, (consensusFlow.initial t₀ y).symm⟩

/-- 箱の中では各主体の基礎評価残差は0で、共有残差は辺の不一致項だけになる。 -/
theorem sharedPotential_eq_coupling (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    DA.potential x t = γ * (x 0 - x 1) ^ 2 := by
  rw [potential_eq ![0, 0] x t]
  have h0 : max (x 0 ^ 2 - θ) 0 = 0 := by
    apply max_eq_right
    have := hx 0
    unfold θ
    have hsq : (x 0) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      have hsqAbs := (sq_le_sq₀ (abs_nonneg (x 0)) (by norm_num : 0 ≤ (1 / 4 : ℝ))).2 this
      simpa [sq_abs] using hsqAbs
    nlinarith
  have h1 : max (x 1 ^ 2 - θ) 0 = 0 := by
    apply max_eq_right
    have := hx 1
    unfold θ
    have hsq : (x 1) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      have hsqAbs := (sq_le_sq₀ (abs_nonneg (x 1)) (by norm_num : 0 ≤ (1 / 4 : ℝ))).2 this
      simpa [sq_abs] using hsqAbs
    nlinarith
  simp [h0, h1, γ]

/-- 箱内初期値からの合意軌道上で共有残差は指数関数で厳密に減衰する。 -/
theorem consensusPotentialPath_eq
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht : t₀ ≤ t) :
    DA.potential (consensusFlow.flow t₀ x t) t =
      γ * ((x 0 - x 1) * Real.exp (-2 * (t - t₀))) ^ 2 := by
  rw [sharedPotential_eq_coupling _
    (consensusFlow_forward_invariant x hx t₀ t ht) t]
  rw [consensusFlow_gap]

/-- 箱内で共有残差が0の状態が常に存在する（対角線上の原点）。 -/
theorem consensus_sharedTCZ_nonempty (t : ℝ) :
    (DA.sharedTCZ box t).Nonempty := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro i
    simp [box]
  · have hpot := potential_eq ![0, 0] (fun _ : Fin 2 => (0 : ℝ)) t
    simpa [DA, θ, γ] using hpot

/-- 非零の二主体不一致は正の辺結合項を生み、結合残差は空虚でない。 -/
theorem consensus_nonzero_mismatch_has_positive_potential (t : ℝ) :
    0 < DA.potential (![1 / 4, -1 / 4] : AgentState) t := by
  have hx : ( (![1 / 4, -1 / 4] : AgentState)) ∈ box := by
    intro i
    fin_cases i <;> norm_num [box]
  rw [sharedPotential_eq_coupling _ hx t]
  norm_num [γ]

/-- 全箱状態で、共有TCZへの距離二乗は共有残差以下（したがって全時刻の誤差境界）。 -/
theorem consensus_global_error_bound (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    (Metric.infDist x (DA.sharedTCZ box t)) ^ 2 ≤ DA.potential x t := by
  let m := meanState x
  let q : AgentState := fun _ => m
  have hm : |m| ≤ 1 / 4 := by
    dsimp [m, meanState]
    have h0 := hx 0
    have h1 := hx 1
    have hl0 := (abs_le.mp h0).1
    have hu0 := (abs_le.mp h0).2
    have hl1 := (abs_le.mp h1).1
    have hu1 := (abs_le.mp h1).2
    rw [abs_le]
    constructor <;> linarith
  have hqbox : q ∈ box := by
    intro i
    simpa [q] using hm
  have hqpot : DA.potential q t = 0 := by
    rw [sharedPotential_eq_coupling q hqbox t]
    simp [q, m, meanState, γ]
  have hqmem : q ∈ DA.sharedTCZ box t := ⟨hqbox, hqpot⟩
  have hdist : dist x q ≤ |x 0 - x 1| / 2 := by
    rw [dist_pi_le_iff (by positivity)]
    intro i
    fin_cases i
    · change dist (x 0) m ≤ |x 0 - x 1| / 2
      rw [Real.dist_eq]
      dsimp [m, meanState]
      rw [show x 0 - (x 0 + x 1) / 2 = (x 0 - x 1) / 2 by ring]
      rw [abs_div]
      norm_num
    · change dist (x 1) m ≤ |x 0 - x 1| / 2
      rw [Real.dist_eq]
      dsimp [m, meanState]
      rw [show x 1 - (x 0 + x 1) / 2 = -(x 0 - x 1) / 2 by ring]
      rw [abs_div, abs_neg]
      norm_num
  have hinf : Metric.infDist x (DA.sharedTCZ box t) ≤ dist x q :=
    Metric.infDist_le_dist_of_mem hqmem
  have hsq : (Metric.infDist x (DA.sharedTCZ box t)) ^ 2 ≤
      (x 0 - x 1) ^ 2 / 4 := by
    have h1 := (sq_le_sq₀ Metric.infDist_nonneg (dist_nonneg)).2 hinf
    have h2 := (sq_le_sq₀ (dist_nonneg) (by positivity)).2 hdist
    calc
      (Metric.infDist x (DA.sharedTCZ box t)) ^ 2 ≤ (dist x q) ^ 2 := h1
      _ ≤ (|x 0 - x 1| / 2) ^ 2 := h2
      _ = (x 0 - x 1) ^ 2 / 4 := by rw [div_pow, sq_abs]; norm_num
  rw [sharedPotential_eq_coupling x hx t]
  unfold γ
  nlinarith [hsq, sq_nonneg (x 0 - x 1)]

/-- 合意flowの共有残差を表す滑らかな閉形式。 -/
def consensusResidualPath (x : AgentState) (t₀ s : ℝ) : ℝ :=
  γ * ((x 0 - x 1) * Real.exp (-2 * (s - t₀))) ^ 2

/-- 閉形式の共有残差は率2で厳密に指数減衰する。 -/
theorem consensusResidualPath_hasDerivAt (x : AgentState) (t₀ s : ℝ) :
    HasDerivAt (consensusResidualPath x t₀)
      (-2 * 2 * consensusResidualPath x t₀ s) s := by
  have hlin : HasDerivAt (fun v : ℝ => -2 * (v - t₀)) (-2) s := by
    simpa using (hasDerivAt_id s).sub_const t₀ |>.const_mul (-2)
  have hexp := (Real.hasDerivAt_exp (-2 * (s - t₀))).comp s hlin
  have hgap := hexp.const_mul (x 0 - x 1)
  have hsquare := hgap.pow 2
  have hpath := hsquare.const_mul γ
  convert hpath using 1
  · funext v
    simp [consensusResidualPath]
  · simp [consensusResidualPath]
    ring

/-- 滑らかな閉形式は有限区間で絶対連続である。 -/
theorem consensusResidualPath_ac (x : AgentState) (t₀ T : ℝ) :
    AbsolutelyContinuousOnInterval (consensusResidualPath x t₀) t₀ T := by
  have hcont : ContDiff ℝ 1 (consensusResidualPath x t₀) := by
    unfold consensusResidualPath
    fun_prop
  exact hcont.contDiffOn.absolutelyContinuousOnInterval

/-- 合意flow上の実残差関数。定理2の時間依存ポテンシャルそのものを表す。 -/
def consensusPotentialAlong (x : AgentState) (t₀ : ℝ) : ℝ → ℝ :=
  fun s => DA.potential (consensusFlow.flow t₀ x s) s

/-- 箱から始めた前向き区間では、実残差は滑らかな閉形式と一致する。 -/
theorem consensusPotentialAlong_eq (x : AgentState) (hx : x ∈ box)
    (t₀ T : ℝ) (hT : t₀ ≤ T) :
    Set.EqOn (consensusPotentialAlong x t₀) (consensusResidualPath x t₀)
      (Set.uIcc t₀ T) := by
  intro s hs
  rw [Set.uIcc_of_le hT] at hs
  exact consensusPotentialPath_eq x hx t₀ s hs.1

/-- 定理2入口が要求する実残差も、箱内の任意の有限前向き区間で絶対連続。 -/
theorem consensusPotentialAlong_ac (x : AgentState) (hx : x ∈ box)
    (t₀ T : ℝ) (hT : t₀ ≤ T) :
    AbsolutelyContinuousOnInterval (consensusPotentialAlong x t₀) t₀ T := by
  apply (consensusResidualPath_ac x t₀ T).congr
  intro s hs
  exact (consensusPotentialAlong_eq x hx t₀ T hT hs).symm

/-- 実残差の導関数は率4で減る。これは定理2入口の率2条件を満たす。 -/
theorem consensusPotentialAlong_decay_ae (x : AgentState) (hx : x ∈ box)
    (t₀ T : ℝ) (hT : t₀ < T) :
    ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
      deriv (consensusPotentialAlong x t₀) s ≤
        -2 * 2 * consensusPotentialAlong x t₀ s := by
  have hpair : ({t₀, T} : Set ℝ) = {t₀} ∪ {T} := by ext u; simp [or_comm]
  have hnull : volume ({t₀, T} : Set ℝ) = 0 := by
    rw [hpair]
    exact measure_union_null (measure_singleton t₀) (measure_singleton T)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hnull] with s hs hIcc
  have hst₀ : s ≠ t₀ := by
    intro h
    apply hs
    simp [h]
  have hsT : s ≠ T := by
    intro h
    apply hs
    simp [h]
  have hinside : s ∈ Set.Ioo t₀ T := ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hst₀), lt_of_le_of_ne hIcc.2 hsT⟩
  have heq : consensusPotentialAlong x t₀ =ᶠ[nhds s] consensusResidualPath x t₀ := by
    have hnhds := Ioo_mem_nhds hinside.1 hinside.2
    filter_upwards [hnhds] with u hu
    apply consensusPotentialAlong_eq x hx t₀ T hT.le
    rw [Set.uIcc_of_le hT.le]
    exact ⟨hu.1.le, hu.2.le⟩
  have hderiv := (consensusResidualPath_hasDerivAt x t₀ s).congr_of_eventuallyEq heq
  rw [hderiv.deriv]
  have hval := consensusPotentialAlong_eq x hx t₀ T hT.le (by
    rw [Set.uIcc_of_le hT.le]
    exact ⟨hinside.1.le, hinside.2.le⟩)
  rw [hval]

/-- 二主体合意flowへ定理2の状態対入口を適用し、共有TCZへの指数距離評価を得る。 -/
theorem consensusFlow_theorem2 (x : AgentState) (hx : x ∈ box)
    (t₀ T : ℝ) (hT : t₀ < T) :
    (consensusFlow.flow t₀ x T ∈ box ∧
      Metric.infDist (consensusFlow.flow t₀ x T) (DA.sharedTCZ box T) ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-2 * (T - t₀))) ∧
    (∀ i, DA.individual i ((consensusFlow.flow t₀ x T) i) T ≤
      (DA.potential x t₀ / DA.individualWeight i) * Real.exp (-4 * (T - t₀))) ∧
    (∀ e, DA.mismatch e ((consensusFlow.flow t₀ x T) (DA.endpoint e).1)
      ((consensusFlow.flow t₀ x T) (DA.endpoint e).2) T ≤
      (DA.potential x t₀ / DA.edgeWeight e) * Real.exp (-4 * (T - t₀))) := by
  have hconnected : ∀ i j : Fin 2, Relation.ReflTransGen
      (fun a b => ∃ e, ((DA.endpoint e).1 = a ∧ (DA.endpoint e).2 = b) ∨
        ((DA.endpoint e).1 = b ∧ (DA.endpoint e).2 = a)) i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨0, Or.inl ⟨rfl, rfl⟩⟩
    · exact Relation.ReflTransGen.single ⟨0, Or.inr ⟨rfl, rfl⟩⟩
    · exact Relation.ReflTransGen.refl
  have hres := DA.theorem2_state_pair_conditional_conclusion
    box (fun s => consensusFlow.flow t₀ x s) hconnected 2 1 t₀ T
    two_pos one_pos hT.le
    (fun s hs => consensusFlow_forward_invariant x hx t₀ s hs.1)
    (fun s _ => consensus_sharedTCZ_nonempty s)
    (by
      change AbsolutelyContinuousOnInterval (consensusPotentialAlong x t₀) t₀ T
      exact consensusPotentialAlong_ac x hx t₀ T hT.le)
    (by
      change ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
        deriv (consensusPotentialAlong x t₀) s ≤ -2 * 2 * consensusPotentialAlong x t₀ s
      exact consensusPotentialAlong_decay_ae x hx t₀ T hT)
    (fun s hs => by
      simpa using consensus_global_error_bound (consensusFlow.flow t₀ x s)
        (consensusFlow_forward_invariant x hx t₀ s hs.1) s)
  have hinitial : consensusFlow.flow t₀ x t₀ = x := consensusFlow.initial t₀ x
  have hpot : DA.potential (consensusFlow.flow t₀ x t₀) t₀ = DA.potential x t₀ := by
    rw [hinitial]
  rw [hpot] at hres
  have hexp : -(2 * 2 * (T - t₀)) = -(4 * (T - t₀)) := by congr 1 <;> ring
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using hres.1
  · intro i
    simpa [DA, Dsys, hexp] using hres.2.1 i
  · intro e
    simpa [hexp] using hres.2.2.1 e

/-- 定理1用の基礎評価。定理2と同じ共有残差を閾値1の上に載せる。 -/
def consensusV0 (x : AgentState) (_t : ℝ) : ℝ := 1 + DA.potential x 0

/-- 箱上では定理1の正部分残差が定理2の共有残差そのものになる。 -/
theorem consensusV0_residual_eq_potential (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    residual1 (consensusV0 x t) 1 = DA.potential x t := by
  have hpot : DA.potential x t = γ * (x 0 - x 1) ^ 2 :=
    sharedPotential_eq_coupling x hx t
  have hzero : DA.potential x 0 = DA.potential x t := by
    rw [sharedPotential_eq_coupling x hx 0, sharedPotential_eq_coupling x hx t]
  rw [consensusV0, hzero, residual1]
  rw [show 1 + DA.potential x t - 1 = DA.potential x t by ring]
  rw [max_eq_left (show 0 ≤ DA.potential x t by rw [hpot]; unfold γ; positivity)]

/-- 同じ合意flow・到達閉包・共有残差を用いて定理1と定理2の入口を両方満たす。

定理1では `V₀=1+Φ₂`, `θ=1` とし、そのTCZスライスが定理2のsharedTCZに一致する。
これにより、二つの定理を別モデルでなく同じ二主体モデル上で適用する。 -/
theorem consensusFlow_theorems1and2_same_model
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    let K := closedLoopReachableSet (policyFlowReachableAt consensusFlow box t₀)
    (∀ t, t₀ ≤ t → consensusFlow.flow t₀ x t ∈ K) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist (consensusFlow.flow t₀ x t) (DA.sharedTCZ box t) ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-2 * (t - t₀))) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist (consensusFlow.flow t₀ x t)
        {y | y ∈ K ∧ consensusV0 y t ≤ 1} ≤
        Real.sqrt (DA.potential x t₀) * Real.exp (-2 * (t - t₀))) := by
  dsimp
  have hK : closedLoopReachableSet (policyFlowReachableAt consensusFlow box t₀) = box :=
    consensusFlow_reachable_closure_eq_box t₀ ht₀
  have htc : ∀ s, {y : AgentState | y ∈ closedLoopReachableSet
      (policyFlowReachableAt consensusFlow box t₀) ∧ consensusV0 y s ≤ 1} =
      DA.sharedTCZ box s := by
    intro s
    rw [hK]
    ext y
    constructor
    · rintro ⟨hy, hV⟩
      refine ⟨hy, ?_⟩
      change 1 + DA.potential y 0 ≤ 1 at hV
      have htime : DA.potential y 0 = DA.potential y s := by
        rw [sharedPotential_eq_coupling y hy 0, sharedPotential_eq_coupling y hy s]
      rw [htime] at hV
      change DA.potential y s = 0
      apply le_antisymm
      · linarith
      · rw [sharedPotential_eq_coupling y hy s]
        unfold γ
        positivity
    · rintro ⟨hy, hpot⟩
      refine ⟨hy, ?_⟩
      change 1 + DA.potential y 0 ≤ 1
      have htime : DA.potential y 0 = DA.potential y s := by
        rw [sharedPotential_eq_coupling y hy 0, sharedPotential_eq_coupling y hy s]
      rw [htime, hpot]
      norm_num
  have htarget_nonempty : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      {y : AgentState | y ∈ closedLoopReachableSet
        (policyFlowReachableAt consensusFlow box t₀) ∧ consensusV0 y s ≤ 1}.Nonempty := by
    intro T hT s hs
    rw [htc s]
    exact consensus_sharedTCZ_nonempty s
  have hresidual_eq : Set.EqOn
      (fun s => residual1 (consensusV0 (consensusFlow.flow t₀ x s) s) 1)
      (consensusPotentialAlong x t₀) (Set.Ici t₀) := by
    intro s hs
    change residual1 (consensusV0 (consensusFlow.flow t₀ x s) s) 1 =
      DA.potential (consensusFlow.flow t₀ x s) s
    exact consensusV0_residual_eq_potential _
      (consensusFlow_forward_invariant x hx t₀ s hs) s
  have hresidual_ac : ∀ T, t₀ ≤ T →
      AbsolutelyContinuousOnInterval
        (fun s => residual1 (consensusV0 (consensusFlow.flow t₀ x s) s) 1) t₀ T := by
    intro T hT
    apply (consensusPotentialAlong_ac x hx t₀ T hT).congr
    intro s hs
    exact (hresidual_eq (show s ∈ Set.Ici t₀ from by
      rw [Set.uIcc_of_le hT] at hs
      exact hs.1)).symm
  have hdecay_ae : ∀ T, t₀ ≤ T →
      ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
        deriv (fun r => residual1 (consensusV0 (consensusFlow.flow t₀ x r) r) 1) s ≤
          -2 * 2 * residual1 (consensusV0 (consensusFlow.flow t₀ x s) s) 1 := by
    intro T hT
    have hstrict : t₀ < T ∨ t₀ = T := lt_or_eq_of_le hT
    cases hstrict with
    | inr heq =>
      subst T
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1
        (by simp : volume (Set.Icc t₀ t₀) = 0)] with s hs hmem
      exact False.elim (hs hmem)
    | inl hlt =>
      have hpair : ({t₀, T} : Set ℝ) = {t₀} ∪ {T} := by ext u; simp [or_comm]
      have hnull : volume ({t₀, T} : Set ℝ) = 0 := by
        rw [hpair]
        exact measure_union_null (measure_singleton t₀) (measure_singleton T)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hnull] with s hs hIcc
      have hst₀ : s ≠ t₀ := by intro heq; apply hs; simp [heq]
      have hsT : s ≠ T := by intro heq; apply hs; simp [heq]
      have hinside : s ∈ Set.Ioo t₀ T :=
        ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hst₀), lt_of_le_of_ne hIcc.2 hsT⟩
      have hnear : (fun r => residual1 (consensusV0 (consensusFlow.flow t₀ x r) r) 1) =ᶠ[𝓝 s]
          (consensusResidualPath x t₀) := by
        have hnhds := Ioo_mem_nhds hinside.1 hinside.2
        filter_upwards [hnhds] with r hr
        calc
          residual1 (consensusV0 (consensusFlow.flow t₀ x r) r) 1 =
              consensusPotentialAlong x t₀ r :=
            hresidual_eq (show r ∈ Set.Ici t₀ from le_of_lt hr.1)
          _ = consensusResidualPath x t₀ r := by
            apply consensusPotentialAlong_eq x hx t₀ T hT
            rw [Set.uIcc_of_le hT]
            exact ⟨hr.1.le, hr.2.le⟩
      have hderiv := (consensusResidualPath_hasDerivAt x t₀ s).congr_of_eventuallyEq hnear
      have hval := hresidual_eq (show s ∈ Set.Ici t₀ from hIcc.1)
      have hval' := consensusPotentialAlong_eq x hx t₀ T hT (by
        rw [Set.uIcc_of_le hT]
        exact ⟨hinside.1.le, hinside.2.le⟩)
      rw [hderiv.deriv, ← hval', ← hval]
  have herror : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (Metric.infDist (consensusFlow.flow t₀ x s)
        {y : AgentState | y ∈ closedLoopReachableSet
          (policyFlowReachableAt consensusFlow box t₀) ∧ consensusV0 y s ≤ 1}) ^ 2 ≤
        1 * residual1 (consensusV0 (consensusFlow.flow t₀ x s) s) 1 := by
    intro T hT s hs
    rw [htc s]
    have hx_s := consensusFlow_forward_invariant x hx t₀ s hs.1
    rw [consensusV0_residual_eq_potential _ hx_s s]
    simpa [one_mul] using consensus_global_error_bound _ hx_s s
  have hthm1 := theorem1_policy_flow_reachable_tcz_distance_tendsto_zero
    (F := consensusFlow) (initialSet := box) (x₀ := x) (hx₀ := hx)
    (V₀ := consensusV0) (θ := 1) (c := 2) (C := 1) (t₀ := t₀)
    htarget_nonempty hresidual_ac hdecay_ae herror (by
      intro y hy t ht
      have hybox : y ∈ box := hK ▸ hy
      have hflow := consensusFlow_forward_invariant y hybox t₀ t ht
      exact hK.symm ▸ hflow) ht₀ (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [hK]
    exact consensusFlow_forward_invariant x hx t₀ t ht
  · intro t ht
    have hbound := hthm1.2.1 t ht
    have hinit : residual1 (consensusV0 (consensusFlow.flow t₀ x t₀) t₀) 1 =
        DA.potential x t₀ := by
      rw [consensusFlow.initial]
      exact consensusV0_residual_eq_potential x hx t₀
    rw [htc t] at hbound
    simpa [hinit, one_mul] using hbound
  · intro t ht
    have hbound := hthm1.2.1 t ht
    have hinit : residual1 (consensusV0 (consensusFlow.flow t₀ x t₀) t₀) 1 =
        DA.potential x t₀ := by
      rw [consensusFlow.initial]
      exact consensusV0_residual_eq_potential x hx t₀
    simpa [hinit, one_mul] using hbound

end Tomabechi.Consistency.ConsistencyC1Consensus

end
