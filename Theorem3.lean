import Theorem2

/-!
# 定理3：抽象的共有TCZ収束

束のLUBと各主体の状態を同じ型で扱わず、束への写像と順序埋め込みを通じて
抽象残差を定義する。定理2型の共有残差に抽象残差を正の重みで加えた
Lyapunov量の指数散逸を条件として、各主体のLUB表象への定量収束を示す。
LUB表象の実現可能性、零集合の非空性、散逸および距離誤差境界は入力条件であり、
最適方策だけから導くとは主張しない。
-/

namespace Tomabechi.Theorem3

open Filter

/-- 抽象度束の元をユークリッド空間へ埋め込む。 -/
abbrev CoordinateSpace (m : ℕ) := Fin m → ℝ

/-- Euclidean norm on the coordinate function type. `CoordinateSpace` keeps
the pointwise order needed by the order embedding, while this explicit norm
matches `EuclideanSpace ℝ (Fin m)` rather than the default Pi sup norm. -/
noncomputable def euclideanCoordinateNorm {m : ℕ}
    (x : CoordinateSpace m) : ℝ := Real.sqrt (∑ i, (x i) ^ 2)

theorem euclideanCoordinateNorm_nonneg {m : ℕ} (x : CoordinateSpace m) :
    0 ≤ euclideanCoordinateNorm x := Real.sqrt_nonneg _

theorem euclideanCoordinateNorm_eq_zero_iff {m : ℕ} (x : CoordinateSpace m) :
    euclideanCoordinateNorm x = 0 ↔ x = 0 := by
  have hsum_nonneg : 0 ≤ ∑ i : Fin m, (x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  rw [euclideanCoordinateNorm, Real.sqrt_eq_zero hsum_nonneg]
  constructor
  · intro h
    funext i
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (x j))).mp h i (Finset.mem_univ i)
    exact (sq_eq_zero_iff).mp hterm
  · intro h
    subst x
    simp

/-- This explicit coordinate formula is exactly the norm used by the usual
Euclidean space structure on `ℝ^m`. -/
theorem euclideanCoordinateNorm_eq_EuclideanSpace_norm {m : ℕ}
    (x : CoordinateSpace m) :
    euclideanCoordinateNorm x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [euclideanCoordinateNorm, Real.norm_eq_abs, sq_abs]

/-- 有限主体の状態・抽象写像・世界ラベル・表象埋め込みを持つ型付きデータ。
`lub` は全世界ラベルの束上の上限である。 -/
structure AbstractSharedSystem (I : Type*) [Fintype I] [Nonempty I]
    (Lattice : Type*) [CompleteLattice Lattice] (m : ℕ) where
  State : I → Type
  abstraction : ∀ i, State i → Lattice
  worlds : I → Lattice
  ι : Lattice ↪o CoordinateSpace m

namespace AbstractSharedSystem

variable {I Lattice : Type*} [Fintype I] [Nonempty I] [CompleteLattice Lattice]
variable {m : ℕ} (D : AbstractSharedSystem I Lattice m)

/-- 原文の `L* = ⋁ᵢ Wᵢ`。 -/
def lub : Lattice := ⨆ i, D.worlds i

/-- LUB表象への二乗距離。状態型と束要素型は `abstraction` と `ι` を介して接続する。 -/
noncomputable def abstractResidual (i : I) (x : D.State i) : ℝ :=
  euclideanCoordinateNorm (D.ι (D.abstraction i x) - D.ι (D.lub)) ^ 2

theorem abstractResidual_nonneg (i : I) (x : D.State i) :
    0 ≤ D.abstractResidual i x := sq_nonneg _

/-- 抽象残差が零であることは、束表象がLUBそのものに等しいことと同値。 -/
theorem abstractResidual_eq_zero_iff (i : I) (x : D.State i) :
    D.abstractResidual i x = 0 ↔ D.abstraction i x = D.lub := by
  constructor
  · intro h
    change euclideanCoordinateNorm
      (D.ι (D.abstraction i x) - D.ι (D.lub)) ^ 2 = 0 at h
    have hn : euclideanCoordinateNorm
        (D.ι (D.abstraction i x) - D.ι (D.lub)) = 0 := by
      nlinarith
    have hzero := (euclideanCoordinateNorm_eq_zero_iff _).mp hn
    have heq : D.ι (D.abstraction i x) = D.ι (D.lub) := sub_eq_zero.mp hzero
    exact D.ι.injective heq
  · intro h
    change euclideanCoordinateNorm
      (D.ι (D.abstraction i x) - D.ι (D.lub)) ^ 2 = 0
    rw [h]
    simp [euclideanCoordinateNorm]

/-- 共有Lyapunov量にLUB残差を加えた定理3の総残差。 -/
noncomputable def potential (trajectory : ∀ i, ℝ → D.State i)
    (shared : ℝ → ℝ) (η : I → ℝ) (t : ℝ) : ℝ :=
  shared t + ∑ i, η i * D.abstractResidual i (trajectory i t)

/-- 状態上で定義した定理3の総残差 `Φ₃(x,t)=Φ₂(x,t)+ΣᵢηᵢAᵢ(xᵢ)`。
軌道に沿うスカラー関数だけでなく、TCZを定義する状態関数としても保持する。 -/
noncomputable def statePotential
    (sharedAt : (∀ i, D.State i) → ℝ → ℝ) (η : I → ℝ)
    (x : ∀ i, D.State i) (t : ℝ) : ℝ :=
  sharedAt x t + ∑ i, η i * D.abstractResidual i (x i)

/-- 閉到達可能領域内の定理3共有TCZ。零条件は状態上の同じ `Φ₃` を使う。 -/
def stateTCZ (K : Set (∀ i, D.State i))
    (sharedAt : (∀ i, D.State i) → ℝ → ℝ) (η : I → ℝ) (t : ℝ) :
    Set (∀ i, D.State i) :=
  {x | x ∈ K ∧ D.statePotential sharedAt η x t = 0}

/-- 定理3の状態を明示写像で定理2の状態へ移し、正準共有残差 `Φ₂` を評価する。
異なる状態型間の比較はこの写像に集約し、無根拠な型同一視を避ける。 -/
def statePairSharedPotential {E : Type*} [DecidableEq I]
    [Fintype E] [DecidableEq E]
    (D₂ : Tomabechi.Theorem2.StatePairResidualSystem I E)
    (stateMap : ∀ i, D.State i → D₂.State i)
    (x : ∀ i, D.State i) (t : ℝ) : ℝ :=
  D₂.potential (fun i => stateMap i (x i)) t

/-- AC・a.e.下降と共有零集合の距離誤差境界から、同じ総残差 `Φ₃` を使って
共有TCZへの状態距離とLUB表象距離の両方に指数評価を与える定理3の有限時間合成。
指数包絡そのものは仮定せず、定理1の比較核から導く。 -/
theorem theorem3_two_distance_bounds_of_ac_ae_descent
    [∀ i, PseudoMetricSpace (D.State i)]
    (trajectory : ∀ i, ℝ → D.State i)
    (sharedTCZ : ℝ → Set (∀ i, D.State i)) (shared : ℝ → ℝ)
    (η : I → ℝ) (i : I) (c C t₀ t : ℝ)
    (hη : 0 < η i) (hc : 0 < c) (hC : 0 < C) (ht : t₀ ≤ t)
    (hshared_nonneg : ∀ s ∈ Set.Icc t₀ t, 0 ≤ shared s)
    (hterms : ∀ s ∈ Set.Icc t₀ t, ∀ j,
      0 ≤ η j * D.abstractResidual j (trajectory j s))
    (hsharedTCZ_nonempty : ∀ s ∈ Set.Icc t₀ t, (sharedTCZ s).Nonempty)
    (hpotential_ac : AbsolutelyContinuousOnInterval
      (D.potential trajectory shared η) t₀ t)
    (hpotential_decay : ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc t₀ t),
      deriv (D.potential trajectory shared η) s ≤
        -2 * c * D.potential trajectory shared η s)
    (hdistance_error : ∀ s ∈ Set.Icc t₀ t,
      (Metric.infDist (fun j => trajectory j s) (sharedTCZ s)) ^ 2 ≤
        C * D.potential trajectory shared η s) :
    Metric.infDist (fun j => trajectory j t) (sharedTCZ t) ≤
        Real.sqrt (C * D.potential trajectory shared η t₀) *
          Real.exp (-c * (t - t₀)) ∧
    euclideanCoordinateNorm (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)) ≤
        Real.sqrt (D.potential trajectory shared η t₀ / η i) *
          Real.exp (-c * (t - t₀)) := by
  have hpotential_nonneg : ∀ s ∈ Set.Icc t₀ t,
      0 ≤ D.potential trajectory shared η s := by
    intro s hs
    unfold potential
    have hsum : 0 ≤ ∑ j, η j * D.abstractResidual j (trajectory j s) :=
      Finset.sum_nonneg (fun j _ => hterms s hs j)
    linarith [hshared_nonneg s hs]
  have hdecay : D.potential trajectory shared η t ≤
      D.potential trajectory shared η t₀ * Real.exp (-2 * c * (t - t₀)) :=
    Tomabechi.Theorem1.lyapunov_exponential_decay_of_ac_ae_derivative
      (D.potential trajectory shared η) c t₀ t hc ht hpotential_ac hpotential_decay
  have hstate := Tomabechi.Theorem1.individual_tcz_distance_decay_of_ac_ae_derivative
    (fun s => fun j => trajectory j s) sharedTCZ (D.potential trajectory shared η)
    c C t₀ t hc hC ht hsharedTCZ_nonempty hpotential_ac hpotential_nonneg
    hpotential_decay hdistance_error
  have hsum := Finset.single_le_sum (fun j _ => hterms t ⟨ht, le_rfl⟩ j)
    (Finset.mem_univ i)
  have hcomponent : η i * D.abstractResidual i (trajectory i t) ≤
      D.potential trajectory shared η t := by
    unfold potential
    linarith [hshared_nonneg t ⟨ht, le_rfl⟩]
  have hsq := Tomabechi.Theorem2.component_exponential_bound
    (fun s => D.abstractResidual i (trajectory i s))
    (D.potential trajectory shared η) (2 * c) t₀ t (η i)
    (D.potential trajectory shared η t₀) hη
    (by simpa [mul_assoc] using hdecay) hcomponent le_rfl
  have hscale : 0 ≤ D.potential trajectory shared η t₀ / η i := by
    exact div_nonneg (hpotential_nonneg t₀ ⟨le_rfl, ht⟩) (le_of_lt hη)
  have hnorm : 0 ≤ euclideanCoordinateNorm
      (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)) :=
    euclideanCoordinateNorm_nonneg _
  have hexp : 0 ≤ Real.exp (-c * (t - t₀)) := Real.exp_nonneg _
  have hrhs_nonneg : 0 ≤
      Real.sqrt (D.potential trajectory shared η t₀ / η i) *
        Real.exp (-c * (t - t₀)) :=
    mul_nonneg (Real.sqrt_nonneg _) hexp
  have hexp_sq : Real.exp (-c * (t - t₀)) ^ 2 =
      Real.exp (-2 * c * (t - t₀)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hnormsq : euclideanCoordinateNorm
      (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)) ^ 2 =
      D.abstractResidual i (trajectory i t) := rfl
  have hlub := (sq_le_sq₀ hnorm hrhs_nonneg).mp (by
    rw [hnormsq, mul_pow, Real.sq_sqrt hscale, hexp_sq]
    simpa [mul_assoc] using hsq)
  exact ⟨hstate, hlub⟩

/-- 各終端時刻での原文条件を、状態距離とLUB表象距離の大域的な指数収束へ繋ぐ。
指数散逸は入口に置かず、各有限区間のAC・a.e.下降から比較補題で導く。 -/
theorem theorem3_two_distances_tendsto_of_ac_ae_descent
    [∀ i, PseudoMetricSpace (D.State i)]
    (trajectory : ∀ i, ℝ → D.State i)
    (sharedTCZ : ℝ → Set (∀ i, D.State i)) (shared : ℝ → ℝ)
    (η : I → ℝ) (i : I) (c C t₀ : ℝ)
    (hη : 0 < η i) (hc : 0 < c) (hC : 0 < C)
    (hshared_nonneg : ∀ s ≥ t₀, 0 ≤ shared s)
    (hterms : ∀ s ≥ t₀, ∀ j,
      0 ≤ η j * D.abstractResidual j (trajectory j s))
    (hsharedTCZ_nonempty : ∀ s ≥ t₀, (sharedTCZ s).Nonempty)
    (hpotential_ac : ∀ T ≥ t₀, AbsolutelyContinuousOnInterval
      (D.potential trajectory shared η) t₀ T)
    (hpotential_decay : ∀ T ≥ t₀,
      ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc t₀ T),
        deriv (D.potential trajectory shared η) s ≤
          -2 * c * D.potential trajectory shared η s)
    (hdistance_error : ∀ s ≥ t₀,
      (Metric.infDist (fun j => trajectory j s) (sharedTCZ s)) ^ 2 ≤
        C * D.potential trajectory shared η s) :
    Filter.Tendsto
      (fun s => Metric.infDist (fun j => trajectory j s) (sharedTCZ s))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto
      (fun s => euclideanCoordinateNorm
        (D.ι (D.abstraction i (trajectory i s)) - D.ι (D.lub)))
      Filter.atTop (nhds 0) := by
  let phi₀ := D.potential trajectory shared η t₀
  let stateDistance : ℝ → ℝ := fun s =>
    Metric.infDist (fun j => trajectory j s) (sharedTCZ s)
  let lubDistance : ℝ → ℝ := fun s =>
    euclideanCoordinateNorm (D.ι (D.abstraction i (trajectory i s)) - D.ι (D.lub))
  have hstate_nonneg : ∀ᶠ s in Filter.atTop, 0 ≤ stateDistance s :=
    Filter.Eventually.of_forall fun s => Metric.infDist_nonneg
  have hlub_nonneg : ∀ᶠ s in Filter.atTop, 0 ≤ lubDistance s :=
    Filter.Eventually.of_forall fun s => euclideanCoordinateNorm_nonneg _
  have hstate_bound : ∀ᶠ s in Filter.atTop,
      stateDistance s ≤ Real.sqrt (C * phi₀) * Real.exp (-c * (s - t₀)) := by
    filter_upwards [Filter.eventually_ge_atTop t₀] with s hs
    have hpoint := D.theorem3_two_distance_bounds_of_ac_ae_descent trajectory
      sharedTCZ shared η i c C t₀ s hη hc hC hs
      (fun r hr => hshared_nonneg r hr.1)
      (fun r hr j => hterms r hr.1 j)
      (fun r hr => hsharedTCZ_nonempty r hr.1)
      (hpotential_ac s hs) (hpotential_decay s hs)
      (fun r hr => hdistance_error r hr.1)
    simpa [stateDistance, phi₀] using hpoint.1
  have hlub_bound : ∀ᶠ s in Filter.atTop,
      lubDistance s ≤ Real.sqrt (phi₀ / η i) * Real.exp (-c * (s - t₀)) := by
    filter_upwards [Filter.eventually_ge_atTop t₀] with s hs
    have hpoint := D.theorem3_two_distance_bounds_of_ac_ae_descent trajectory
      sharedTCZ shared η i c C t₀ s hη hc hC hs
      (fun r hr => hshared_nonneg r hr.1)
      (fun r hr j => hterms r hr.1 j)
      (fun r hr => hsharedTCZ_nonempty r hr.1)
      (hpotential_ac s hs) (hpotential_decay s hs)
      (fun r hr => hdistance_error r hr.1)
    simpa [lubDistance, phi₀] using hpoint.2
  have hstate_tendsto := Tomabechi.Theorem2.exponential_envelope_tendsto_zero
    stateDistance (Real.sqrt (C * phi₀)) c t₀ hc hstate_nonneg hstate_bound
  have hlub_tendsto := Tomabechi.Theorem2.exponential_envelope_tendsto_zero
    lubDistance (Real.sqrt (phi₀ / η i)) c t₀ hc hlub_nonneg hlub_bound
  exact ⟨hstate_tendsto, hlub_tendsto⟩

/-- 状態上の総残差から閉到達可能TCZを作り、同じ `Φ₃` の散逸から
共有状態距離・LUB表象距離の定量評価と極限を得る定理3の統合入口。
`sharedAt` は原文の共有残差 `Φ₂` を状態と時刻の関数として与える。 -/
theorem theorem3_reachable_state_tcz_quantitative_conclusion
    [∀ i, PseudoMetricSpace (D.State i)]
    (reachableAt : ℝ → Set (∀ i, D.State i))
    (trajectory : ∀ i, ℝ → D.State i)
    (sharedAt : (∀ i, D.State i) → ℝ → ℝ) (η : I → ℝ)
    (i : I) (c C t₀ : ℝ)
    (hη : 0 < η i) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 ≤ t₀)
    (htrajectory_reachable : ∀ s ≥ t₀,
      (fun j => trajectory j s) ∈ reachableAt s)
    (hshared_nonneg : ∀ s ≥ t₀, 0 ≤ sharedAt (fun j => trajectory j s) s)
    (hterms : ∀ s ≥ t₀, ∀ j,
      0 ≤ η j * D.abstractResidual j (trajectory j s))
    (hTCZ_nonempty : ∀ s ≥ t₀,
      (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
        sharedAt η s).Nonempty)
    (hpotential_ac : ∀ T ≥ t₀,
      AbsolutelyContinuousOnInterval
        (fun s => D.statePotential sharedAt η (fun j => trajectory j s) s) t₀ T)
    (hpotential_decay : ∀ T ≥ t₀,
      ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc t₀ T),
        deriv (fun r => D.statePotential sharedAt η (fun j => trajectory j r) r) s ≤
          -2 * c * D.statePotential sharedAt η (fun j => trajectory j s) s)
    (hdistance_error : ∀ s ≥ t₀,
      (Metric.infDist (fun j => trajectory j s)
        (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
          sharedAt η s)) ^ 2 ≤
        C * D.statePotential sharedAt η (fun j => trajectory j s) s) :
    (∀ s ≥ t₀, (fun j => trajectory j s) ∈
      Tomabechi.Theorem1.closedLoopReachableSet reachableAt) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist (fun j => trajectory j t)
        (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
          sharedAt η t) ≤
          Real.sqrt (C * D.statePotential sharedAt η
            (fun j => trajectory j t₀) t₀) * Real.exp (-c * (t - t₀)) ∧
      euclideanCoordinateNorm (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)) ≤
          Real.sqrt (D.statePotential sharedAt η
            (fun j => trajectory j t₀) t₀ / η i) * Real.exp (-c * (t - t₀))) ∧
    (Filter.Tendsto (fun s => Metric.infDist (fun j => trajectory j s)
        (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
          sharedAt η s)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun s => euclideanCoordinateNorm
          (D.ι (D.abstraction i (trajectory i s)) - D.ι (D.lub)))
        Filter.atTop (nhds 0)) := by
  let K := Tomabechi.Theorem1.closedLoopReachableSet reachableAt
  let shared : ℝ → ℝ := fun s => sharedAt (fun j => trajectory j s) s
  let sharedTCZ : ℝ → Set (∀ j, D.State j) := D.stateTCZ K sharedAt η
  have hK : ∀ s ≥ t₀, (fun j => trajectory j s) ∈ K := by
    intro s hs
    exact Tomabechi.Theorem1.mem_closedLoopReachableSet_of_mem_reachableAt
      reachableAt (le_trans ht₀ hs) (htrajectory_reachable s hs)
  have hnonempty : ∀ s ≥ t₀, (sharedTCZ s).Nonempty := hTCZ_nonempty
  have hphiEq : D.potential trajectory shared η =
      (fun s => D.statePotential sharedAt η (fun j => trajectory j s) s) := by
    funext s
    rfl
  have hlimits := D.theorem3_two_distances_tendsto_of_ac_ae_descent
    trajectory sharedTCZ shared η i c C t₀ hη hc hC hshared_nonneg hterms
    hnonempty
    (fun T hT => by rw [hphiEq]; exact hpotential_ac T hT)
    (fun T hT => by
      rw [hphiEq]
      exact hpotential_decay T hT)
    (fun s hs => by simpa [sharedTCZ, stateTCZ, shared,
      AbstractSharedSystem.statePotential, AbstractSharedSystem.potential]
      using hdistance_error s hs)
  refine ⟨hK, ?_, hlimits⟩
  intro t ht
  have hpoint := D.theorem3_two_distance_bounds_of_ac_ae_descent
    trajectory sharedTCZ shared η i c C t₀ t hη hc hC ht
    (fun s hs => hshared_nonneg s hs.1)
    (fun s hs j => hterms s hs.1 j)
    (fun s hs => hnonempty s hs.1)
    (by rw [hphiEq]; exact hpotential_ac t ht)
    (by
      rw [hphiEq]
      exact hpotential_decay t ht)
    (fun s hs => by simpa [sharedTCZ, stateTCZ, shared,
      AbstractSharedSystem.statePotential, AbstractSharedSystem.potential]
      using hdistance_error s hs.1)
  constructor
  · simpa [sharedTCZ, stateTCZ, K, AbstractSharedSystem.statePotential,
      AbstractSharedSystem.potential, shared] using hpoint.1
  · simpa [AbstractSharedSystem.statePotential, AbstractSharedSystem.potential,
      shared] using hpoint.2

/-- P1→P2の状態型付き接続。定理2の正準 `StatePairResidualSystem.potential`
を明示状態写像で定理3状態へ引き戻して `Φ₂` とし、同じ `Φ₃` の零集合を目標に
指数評価・両極限を得る。写像そのものの原文モデル上の構成は別途入力として残る。 -/
theorem theorem3_reachable_state_tcz_from_statePairSystem
    {E : Type*} [DecidableEq I] [Fintype E] [DecidableEq E]
    (D₂ : Tomabechi.Theorem2.StatePairResidualSystem I E)
    (stateMap : ∀ i, D.State i → D₂.State i)
    [∀ i, PseudoMetricSpace (D.State i)]
    (reachableAt : ℝ → Set (∀ i, D.State i))
    (trajectory : ∀ i, ℝ → D.State i) (η : I → ℝ)
    (i : I) (c C t₀ : ℝ)
    (hη : ∀ j, 0 < η j) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 ≤ t₀)
    (htrajectory_reachable : ∀ s ≥ t₀,
      (fun j => trajectory j s) ∈ reachableAt s)
    (hTCZ_nonempty : ∀ s ≥ t₀,
      (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
        (D.statePairSharedPotential D₂ stateMap) η s).Nonempty)
    (hpotential_ac : ∀ T ≥ t₀,
      AbsolutelyContinuousOnInterval
        (fun s => D.statePotential (D.statePairSharedPotential D₂ stateMap) η
          (fun j => trajectory j s) s) t₀ T)
    (hpotential_decay : ∀ T ≥ t₀,
      ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc t₀ T),
        deriv (fun r => D.statePotential (D.statePairSharedPotential D₂ stateMap) η
          (fun j => trajectory j r) r) s ≤
          -2 * c * D.statePotential (D.statePairSharedPotential D₂ stateMap) η
            (fun j => trajectory j s) s)
    (hdistance_error : ∀ s ≥ t₀,
      (Metric.infDist (fun j => trajectory j s)
        (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
          (D.statePairSharedPotential D₂ stateMap) η s)) ^ 2 ≤
        C * D.statePotential (D.statePairSharedPotential D₂ stateMap) η
          (fun j => trajectory j s) s) :
    (∀ s ≥ t₀, (fun j => trajectory j s) ∈
      Tomabechi.Theorem1.closedLoopReachableSet reachableAt) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist (fun j => trajectory j t)
        (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
          (D.statePairSharedPotential D₂ stateMap) η t) ≤
          Real.sqrt (C * D.statePotential (D.statePairSharedPotential D₂ stateMap) η
            (fun j => trajectory j t₀) t₀) * Real.exp (-c * (t - t₀)) ∧
      euclideanCoordinateNorm (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)) ≤
          Real.sqrt (D.statePotential (D.statePairSharedPotential D₂ stateMap) η
            (fun j => trajectory j t₀) t₀ / η i) * Real.exp (-c * (t - t₀))) ∧
    (Filter.Tendsto (fun s => Metric.infDist (fun j => trajectory j s)
        (D.stateTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
          (D.statePairSharedPotential D₂ stateMap) η s)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun s => euclideanCoordinateNorm
          (D.ι (D.abstraction i (trajectory i s)) - D.ι (D.lub)))
        Filter.atTop (nhds 0)) := by
  apply D.theorem3_reachable_state_tcz_quantitative_conclusion
    reachableAt trajectory (D.statePairSharedPotential D₂ stateMap) η i c C t₀
    (hη i) hc hC ht₀ htrajectory_reachable ?_ ?_ hTCZ_nonempty
    hpotential_ac hpotential_decay hdistance_error
  · intro s hs
    unfold statePairSharedPotential
    dsimp [Tomabechi.Theorem2.StatePairResidualSystem.potential]
    apply add_nonneg
    · exact Finset.sum_nonneg fun j _ => D₂.individual_nonneg j
        (stateMap j (trajectory j s)) s
    · exact Finset.sum_nonneg fun e _ => mul_nonneg (le_of_lt (D₂.edgeWeight_pos e))
        (D₂.mismatch_nonneg e _ _ s)
  · intro s hs j
    exact mul_nonneg (le_of_lt (hη j))
      (D.abstractResidual_nonneg j (trajectory j s))

/-- 共有項と抽象残差項が非負なら総残差が各重み付き抽象残差を支配する。 -/
theorem weightedAbstractResidual_le_potential
    (trajectory : ∀ i, ℝ → D.State i) (shared : ℝ → ℝ)
    (η : I → ℝ) (t : ℝ) (i : I)
    (hshared : 0 ≤ shared t)
    (hterms : ∀ j, 0 ≤ η j * D.abstractResidual j (trajectory j t)) :
    η i * D.abstractResidual i (trajectory i t) ≤
      D.potential trajectory shared η t := by
  have hsum := Finset.single_le_sum (fun j _ => hterms j) (Finset.mem_univ i)
  simp only [potential]
  linarith

/-- 共有残差散逸から、LUB埋め込み空間での各主体の二乗距離の
明示的指数上界を得る。正の重み・非負性・指数散逸を仮定として保つ。 -/
theorem abstractResidual_exponential_bound
    (trajectory : ∀ i, ℝ → D.State i) (shared : ℝ → ℝ)
    (η : I → ℝ) (i : I) (c t₀ t initialBound : ℝ)
    (hη : 0 < η i) (_hc : 0 < c) (ht : t₀ ≤ t)
    (hshared_nonneg : ∀ s ≥ t₀, 0 ≤ shared s)
    (hterms : ∀ s ≥ t₀, ∀ j,
      0 ≤ η j * D.abstractResidual j (trajectory j s))
    (hdecay : ∀ s ≥ t₀,
      D.potential trajectory shared η s ≤
        D.potential trajectory shared η t₀ * Real.exp (-(2 * c) * (s - t₀)))
    (hinitial : D.potential trajectory shared η t₀ ≤ initialBound) :
    D.abstractResidual i (trajectory i t) ≤
      (initialBound / η i) * Real.exp (-(2 * c) * (t - t₀)) := by
  have hcomponent := D.weightedAbstractResidual_le_potential
    trajectory shared η t i (hshared_nonneg t ht) (hterms t ht)
  exact Tomabechi.Theorem2.component_exponential_bound
    (fun s => D.abstractResidual i (trajectory i s))
    (D.potential trajectory shared η) (2 * c) t₀ t (η i) initialBound
    hη (by simpa using hdecay t ht) hcomponent hinitial

/-- 原文の主要結論：LUBの順序埋め込み表象への距離が指数率 `c` で減衰する。
これは状態空間上の距離収束を主張せず、原文の型付き抽象表象だけを結論する。 -/
theorem lub_representation_exponential_convergence
    (trajectory : ∀ i, ℝ → D.State i) (shared : ℝ → ℝ)
    (η : I → ℝ) (i : I) (c t₀ t initialBound : ℝ)
    (hη : 0 < η i) (hc : 0 < c) (ht : t₀ ≤ t)
    (hshared_nonneg : ∀ s ≥ t₀, 0 ≤ shared s)
    (hterms : ∀ s ≥ t₀, ∀ j,
      0 ≤ η j * D.abstractResidual j (trajectory j s))
    (hdecay : ∀ s ≥ t₀,
      D.potential trajectory shared η s ≤
        D.potential trajectory shared η t₀ * Real.exp (-(2 * c) * (s - t₀)))
    (hinitial : D.potential trajectory shared η t₀ ≤ initialBound) :
    euclideanCoordinateNorm (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)) ≤
      Real.sqrt (initialBound / η i) * Real.exp (-c * (t - t₀)) := by
  have hsq := D.abstractResidual_exponential_bound trajectory shared η i c t₀ t
    initialBound hη hc ht hshared_nonneg hterms hdecay hinitial
  have hηres := D.abstractResidual_nonneg i (trajectory i t)
  have hscale : 0 ≤ initialBound / η i := by
    have hpot := D.weightedAbstractResidual_le_potential trajectory shared η t₀ i
      (hshared_nonneg t₀ le_rfl) (hterms t₀ le_rfl)
    have hres0 := D.abstractResidual_nonneg i (trajectory i t₀)
    have hpot0 : 0 ≤ D.potential trajectory shared η t₀ := by
      unfold potential
      have hs := hshared_nonneg t₀ le_rfl
      have hsums : 0 ≤ ∑ j, η j * D.abstractResidual j (trajectory j t₀) :=
        Finset.sum_nonneg (fun j _ => hterms t₀ le_rfl j)
      linarith
    have hbound0 : 0 ≤ initialBound := le_trans hpot0 hinitial
    exact div_nonneg hbound0 (le_of_lt hη)
  have hnorm : 0 ≤ euclideanCoordinateNorm
      (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)) :=
    euclideanCoordinateNorm_nonneg _
  have hexp : 0 ≤ Real.exp (-c * (t - t₀)) := Real.exp_nonneg _
  have hsqrt := Real.sq_sqrt hscale
  have hexp_sq : Real.exp (-c * (t - t₀)) ^ 2 =
      Real.exp (-(2 * c) * (t - t₀)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hnormsq : euclideanCoordinateNorm
      (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)) ^ 2 =
      D.abstractResidual i (trajectory i t) := rfl
  have hrhs_nonneg : 0 ≤ Real.sqrt (initialBound / η i) * Real.exp (-c * (t - t₀)) :=
    mul_nonneg (Real.sqrt_nonneg (initialBound / η i)) hexp
  rw [← sq_le_sq₀ hnorm hrhs_nonneg]
  rw [hnormsq]
  rw [mul_pow, Real.sq_sqrt hscale, hexp_sq]
  exact hsq

/-- 指数評価から原文に記された `t → ∞` のLUB表象収束を得る。 -/
theorem lub_representation_tendsto
    (trajectory : ∀ i, ℝ → D.State i) (shared : ℝ → ℝ)
    (η : I → ℝ) (i : I) (c t₀ initialBound : ℝ)
    (hη : 0 < η i) (hc : 0 < c)
    (hshared_nonneg : ∀ s ≥ t₀, 0 ≤ shared s)
    (hterms : ∀ s ≥ t₀, ∀ j,
      0 ≤ η j * D.abstractResidual j (trajectory j s))
    (hdecay : ∀ s ≥ t₀,
      D.potential trajectory shared η s ≤
        D.potential trajectory shared η t₀ * Real.exp (-(2 * c) * (s - t₀)))
    (hinitial : D.potential trajectory shared η t₀ ≤ initialBound) :
    Tendsto (fun t => euclideanCoordinateNorm
      (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)))
      atTop (nhds 0) := by
  have hnonneg : ∀ᶠ t : ℝ in atTop,
      0 ≤ euclideanCoordinateNorm
        (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)) :=
    Filter.Eventually.of_forall (fun t => euclideanCoordinateNorm_nonneg _)
  have hbound : ∀ᶠ t : ℝ in atTop,
      euclideanCoordinateNorm (D.ι (D.abstraction i (trajectory i t)) - D.ι (D.lub)) ≤
        Real.sqrt (initialBound / η i) * Real.exp (-c * (t - t₀)) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨t₀, fun t ht =>
      D.lub_representation_exponential_convergence trajectory shared η i c t₀ t
        initialBound hη hc ht hshared_nonneg hterms hdecay hinitial⟩]
    intro t ht
    exact ht
  exact Tomabechi.Theorem2.exponential_envelope_tendsto_zero _
    (Real.sqrt (initialBound / η i)) c t₀ hc hnonneg hbound

end AbstractSharedSystem
end Tomabechi.Theorem3

#print axioms Tomabechi.Theorem3.AbstractSharedSystem.abstractResidual_exponential_bound
#print axioms Tomabechi.Theorem3.AbstractSharedSystem.lub_representation_exponential_convergence
#print axioms Tomabechi.Theorem3.AbstractSharedSystem.lub_representation_tendsto
#print axioms Tomabechi.Theorem3.AbstractSharedSystem.theorem3_two_distance_bounds_of_ac_ae_descent
#print axioms Tomabechi.Theorem3.AbstractSharedSystem.theorem3_two_distances_tendsto_of_ac_ae_descent
#print axioms Tomabechi.Theorem3.AbstractSharedSystem.theorem3_reachable_state_tcz_quantitative_conclusion
#print axioms Tomabechi.Theorem3.AbstractSharedSystem.theorem3_reachable_state_tcz_from_statePairSystem
