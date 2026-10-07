import Tomabechi.Consistency.ConsistencyC1_ConsensusControl
import Tomabechi.Consistency.ConsistencyR1_CommonLattice
import Theorem3

/-!
# C1: Theorem 3 on the rate-3 consensus flow

The two physical coordinates are also the two agents of an abstract shared
system. On the invariant zero-mean slice, both agents approach the bottom LUB
and the physical consensus diagonal under the same rate-3 flow. The initial
disagreement may be nonzero, so both conclusions are nontrivial.
-/

noncomputable section

namespace Tomabechi.Consistency.ConsistencyC1Theorem3Bridge

open Filter
open MeasureTheory
open scoped Topology
open Tomabechi.Theorem1
open Tomabechi.Theorem3
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Examples.Theorem2

abbrev C1Concept := Tomabechi.Consistency.R1.CommonConcept

def clippedMagnitude (x : ℝ) : unitInterval :=
  ⟨min |x| 1, ⟨le_min (abs_nonneg x) (by norm_num), min_le_right _ _⟩⟩

/-- Each physical agent reports its clipped magnitude in its own lattice coordinate. -/
def c1Theorem3System : AbstractSharedSystem (Fin 2) C1Concept 2 where
  State := fun _ => ℝ
  abstraction := fun i x j => if j = i then clippedMagnitude x else 0
  worlds := fun _ => fun _ => (0 : unitInterval)
  ι := OrderEmbedding.ofMapLEIff (fun f j => (f j : ℝ)) (by
    intro f g
    simp only [Pi.le_def]
    exact forall_congr' fun j => Subtype.coe_le_coe)

local instance (i : Fin 2) : PseudoMetricSpace (c1Theorem3System.State i) := by
  change PseudoMetricSpace ℝ
  infer_instance

theorem c1Theorem3System_lub :
    c1Theorem3System.lub = fun _ => (0 : unitInterval) := by
  funext j
  simp [AbstractSharedSystem.lub, c1Theorem3System]

theorem c1Theorem3System_abstraction_residual
    (i : Fin 2) (z : AgentState) (hz : z ∈ box) :
    c1Theorem3System.abstractResidual i (z i) = z i ^ 2 := by
  have hi := hz i
  have hiOne : |z i| ≤ 1 := hi.trans (by norm_num)
  have habs : clippedMagnitude (z i) = ⟨|z i|, ⟨abs_nonneg _, by
      exact hiOne⟩⟩ := by
    apply Subtype.ext
    simp [clippedMagnitude, min_eq_left hiOne]
  change euclideanCoordinateNorm
      (c1Theorem3System.ι (c1Theorem3System.abstraction i (z i)) -
        c1Theorem3System.ι c1Theorem3System.lub) ^ 2 = z i ^ 2
  rw [c1Theorem3System_lub]
  fin_cases i
  · have hlocal : clippedMagnitude (z 0) =
        ⟨|z 0|, ⟨abs_nonneg _, by linarith [hz 0]⟩⟩ := by
      simpa using habs
    simp [c1Theorem3System, hlocal, euclideanCoordinateNorm,
      Fin.sum_univ_two, sq_abs]
    rw [Real.sq_sqrt (sq_nonneg (z 0))]
  · have hlocal : clippedMagnitude (z 1) =
        ⟨|z 1|, ⟨abs_nonneg _, by linarith [hz 1]⟩⟩ := by
      simpa using habs
    simp [c1Theorem3System, hlocal, euclideanCoordinateNorm,
      Fin.sum_univ_two, sq_abs]
    rw [Real.sq_sqrt (sq_nonneg (z 1))]

def c1Theorem3Trajectory (t₀ : ℝ) (x : AgentState) :
    ∀ i : Fin 2, ℝ → ℝ := fun i s => (consensusOptimalFlow.flow t₀ x s) i

def c1Theorem3SharedTCZ (t : ℝ) : Set AgentState := DA.sharedTCZ box t

def c1Theorem3Weight : Fin 2 → ℝ := fun _ => 1 / 2

def c1Theorem3Potential (x : AgentState) (t₀ : ℝ) (s : ℝ) : ℝ :=
  c1Theorem3System.potential (c1Theorem3Trajectory t₀ x)
    (fun r => DA.potential (consensusOptimalFlow.flow t₀ x r) r)
    c1Theorem3Weight s

def c1Theorem3Zero : AgentState := fun _ => 0

/-- State-wise `Φ₃=Φ₂+ΣηᵢAᵢ`, evaluated on the same physical state and time. -/
def c1Theorem3StatePhi3 (z : AgentState) (t : ℝ) : ℝ :=
  c1Theorem3System.potential (fun i _ => z i)
    (fun _ => DA.potential z t) c1Theorem3Weight t

/-- The original Theorem 3 target: the zero set of the full `Φ₃` inside the
closed reachable region. This is distinct from the zero set of `Φ₂` alone. -/
def c1Theorem3OriginalTCZ (t₀ t : ℝ) : Set AgentState :=
  {z | z ∈ closedLoopReachableSet
      (policyFlowReachableAt consensusOptimalFlow box t₀) ∧
    c1Theorem3StatePhi3 z t = 0}

theorem c1Theorem3StatePhi3_eq_on_box (z : AgentState) (hz : z ∈ box) (t : ℝ) :
    c1Theorem3StatePhi3 z t =
      2 * (z 0 - z 1) ^ 2 + (1 / 2 : ℝ) * (z 0 ^ 2 + z 1 ^ 2) := by
  unfold c1Theorem3StatePhi3 AbstractSharedSystem.potential
  rw [Fin.sum_univ_two]
  rw [sharedPotential_eq_coupling z hz t]
  rw [c1Theorem3System_abstraction_residual 0 z hz,
    c1Theorem3System_abstraction_residual 1 z hz]
  norm_num [γ, c1Theorem3Weight]
  ring

/-- For this box, the full `Φ₃` zero set is exactly the origin; it is smaller
than the diagonal zero set of `Φ₂`. -/
theorem c1Theorem3OriginalTCZ_eq_singleton (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    c1Theorem3OriginalTCZ t₀ t = {c1Theorem3Zero} := by
  ext z
  constructor
  · rintro ⟨hzK, hphi⟩
    have hzbox : z ∈ box := by
      rw [consensusOptimalFlow_reachable_closure_eq_box t₀ ht₀] at hzK
      exact hzK
    rw [c1Theorem3StatePhi3_eq_on_box z hzbox t] at hphi
    have hpot : 0 ≤ 2 * (z 0 - z 1) ^ 2 := by positivity
    have hsquares : 0 ≤ (1 / 2 : ℝ) * (z 0 ^ 2 + z 1 ^ 2) := by positivity
    have h0 : z 0 ^ 2 = 0 := by nlinarith
    have h1 : z 1 ^ 2 = 0 := by nlinarith
    have hz0 : z 0 = 0 := (sq_eq_zero_iff).mp h0
    have hz1 : z 1 = 0 := (sq_eq_zero_iff).mp h1
    change z = c1Theorem3Zero
    funext i
    fin_cases i <;> simp [c1Theorem3Zero, hz0, hz1]
  · intro hz
    have hz0 : z = c1Theorem3Zero := by simpa using hz
    subst z
    constructor
    · rw [consensusOptimalFlow_reachable_closure_eq_box t₀ ht₀]
      intro i
      simp [c1Theorem3Zero, box]
    · rw [c1Theorem3StatePhi3_eq_on_box c1Theorem3Zero (by
        intro i
        simp [c1Theorem3Zero, box]) t]
      simp [c1Theorem3Zero]

theorem c1Theorem3OriginalTCZ_nonempty (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    (c1Theorem3OriginalTCZ t₀ t).Nonempty := by
  rw [c1Theorem3OriginalTCZ_eq_singleton t₀ t ht₀]
  exact Set.singleton_nonempty _


theorem c1Theorem3Trajectory_zeroMean
    (x : AgentState) (hmean : x 0 + x 1 = 0) (t₀ t : ℝ) :
    (c1Theorem3Trajectory t₀ x 0 t) + (c1Theorem3Trajectory t₀ x 1 t) = 0 := by
  change (consensusOptimalFlow.flow t₀ x t) 0 +
    (consensusOptimalFlow.flow t₀ x t) 1 = 0
  simp [consensusOptimalFlow, meanState, halfDifference]
  linarith

def c1Theorem3NontrivialInitial : AgentState := ![(1 / 8 : ℝ), -(1 / 8 : ℝ)]

theorem c1Theorem3NontrivialInitial_mem_box :
    c1Theorem3NontrivialInitial ∈ box := by
  intro i
  fin_cases i <;> norm_num [c1Theorem3NontrivialInitial, box]

theorem c1Theorem3NontrivialInitial_zeroMean :
    c1Theorem3NontrivialInitial 0 + c1Theorem3NontrivialInitial 1 = 0 := by
  norm_num [c1Theorem3NontrivialInitial]

theorem c1Theorem3NontrivialInitial_abstractResidual_positive :
    0 < c1Theorem3System.abstractResidual 0 (c1Theorem3NontrivialInitial 0) := by
  rw [c1Theorem3System_abstraction_residual 0 c1Theorem3NontrivialInitial
    c1Theorem3NontrivialInitial_mem_box]
  norm_num [c1Theorem3NontrivialInitial]

theorem c1Theorem3Potential_eq_of_zeroMean
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ s : ℝ) (hs : t₀ ≤ s) :
    c1Theorem3Potential x t₀ s =
      (9 / 8 : ℝ) * DA.potential (consensusOptimalFlow.flow t₀ x s) s := by
  let y := consensusOptimalFlow.flow t₀ x s
  have hy : y ∈ box := consensusOptimalFlow_forward_invariant x hx t₀ s hs
  have hymean : y 0 + y 1 = 0 := c1Theorem3Trajectory_zeroMean x hmean t₀ s
  have hA0 := c1Theorem3System_abstraction_residual 0 y hy
  have hA1 := c1Theorem3System_abstraction_residual 1 y hy
  have hshared := sharedPotential_eq_coupling y hy s
  unfold c1Theorem3Potential
  change DA.potential y s +
    ∑ i : Fin 2, c1Theorem3Weight i * c1Theorem3System.abstractResidual i (y i) =
      (9 / 8 : ℝ) * DA.potential y s
  rw [Fin.sum_univ_two]
  simp only [c1Theorem3Weight]
  rw [hA0, hA1, hshared]
  have hy1 : y 1 = -y 0 := by linarith
  rw [hy1]
  norm_num [γ]
  ring

theorem c1Theorem3Potential_ac
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ T : ℝ) (hT : t₀ ≤ T) :
    AbsolutelyContinuousOnInterval (c1Theorem3Potential x t₀) t₀ T := by
  apply ((consensusOptimalPotentialAlong_ac x hx t₀ T hT).const_mul (9 / 8 : ℝ)).congr
  intro s hs
  rw [Set.uIcc_of_le hT] at hs
  exact (c1Theorem3Potential_eq_of_zeroMean x hx hmean t₀ s hs.1).symm

theorem c1Theorem3Potential_decay_ae
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ T : ℝ) (hT : t₀ < T) :
    ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc t₀ T),
      deriv (c1Theorem3Potential x t₀) s ≤ -2 * 3 * c1Theorem3Potential x t₀ s := by
  have hpair : ({t₀, T} : Set ℝ) = {t₀} ∪ {T} := by ext u; simp [or_comm]
  have hnull : MeasureTheory.volume ({t₀, T} : Set ℝ) = 0 := by
    rw [hpair]
    exact MeasureTheory.measure_union_null
      (MeasureTheory.measure_singleton t₀) (MeasureTheory.measure_singleton T)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hnull] with s hs hIcc
  have hst₀ : s ≠ t₀ := by intro heq; apply hs; simp [heq]
  have hsT : s ≠ T := by intro heq; apply hs; simp [heq]
  have hinside : s ∈ Set.Ioo t₀ T :=
    ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hst₀), lt_of_le_of_ne hIcc.2 hsT⟩
  have hnear : (c1Theorem3Potential x t₀) =ᶠ[𝓝 s]
      (fun r => (9 / 8 : ℝ) * consensusOptimalResidualPath x t₀ r) := by
    have hnhds := Ioo_mem_nhds hinside.1 hinside.2
    filter_upwards [hnhds] with r hr
    have hphi := c1Theorem3Potential_eq_of_zeroMean x hx hmean t₀ r hr.1.le
    have hbase := consensusOptimalPotentialAlong_eq x hx t₀ T hT.le (by
      rw [Set.uIcc_of_le hT.le]
      exact ⟨hr.1.le, hr.2.le⟩)
    exact hphi.trans (congrArg (fun z : ℝ => (9 / 8 : ℝ) * z) hbase)
  have hpath := (consensusOptimalResidualPath_hasDerivAt x t₀ s).const_mul (9 / 8 : ℝ)
  have hderiv := hpath.congr_of_eventuallyEq hnear
  rw [hderiv.deriv]
  have hval := c1Theorem3Potential_eq_of_zeroMean x hx hmean t₀ s hinside.1.le
  have hbase := consensusOptimalPotentialAlong_eq x hx t₀ T hT.le (by
    rw [Set.uIcc_of_le hT.le]
    exact ⟨hinside.1.le, hinside.2.le⟩)
  rw [← hbase, hval]
  simp [consensusOptimalPotentialAlong]
  nlinarith

theorem c1Theorem3_shared_nonempty (t : ℝ) :
    (c1Theorem3SharedTCZ t).Nonempty := by
  exact consensus_sharedTCZ_nonempty t

theorem c1Theorem3_rate3_quantitative
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ s : ℝ) (ht₀ : 0 ≤ t₀) (hs : t₀ ≤ s) :
    Metric.infDist (consensusOptimalFlow.flow t₀ x s) (DA.sharedTCZ box s) ≤
        Real.sqrt (c1Theorem3Potential x t₀ t₀) * Real.exp (-3 * (s - t₀)) ∧
      euclideanCoordinateNorm
        (c1Theorem3System.ι
          (c1Theorem3System.abstraction 0 ((consensusOptimalFlow.flow t₀ x s) 0)) -
          c1Theorem3System.ι c1Theorem3System.lub) ≤
        Real.sqrt (c1Theorem3Potential x t₀ t₀ / c1Theorem3Weight 0) *
          Real.exp (-3 * (s - t₀)) := by
  have hterms : ∀ r ≥ t₀, ∀ i : Fin 2,
      0 ≤ c1Theorem3Weight i * c1Theorem3System.abstractResidual i
        (c1Theorem3Trajectory t₀ x i r) := by
    intro r hr i
    exact mul_nonneg (by norm_num [c1Theorem3Weight])
      (AbstractSharedSystem.abstractResidual_nonneg c1Theorem3System i _)
  have hshared_nonneg : ∀ r ≥ t₀,
      0 ≤ DA.potential (consensusOptimalFlow.flow t₀ x r) r := by
    intro r hr
    rw [sharedPotential_eq_coupling _
      (consensusOptimalFlow_forward_invariant x hx t₀ r hr) r]
    exact mul_nonneg (by norm_num [γ]) (sq_nonneg _)
  have hTCZ : ∀ r ≥ t₀, (c1Theorem3SharedTCZ r).Nonempty := by
    intro r hr
    exact c1Theorem3_shared_nonempty r
  have hAC : ∀ T ≥ t₀,
      AbsolutelyContinuousOnInterval (c1Theorem3Potential x t₀) t₀ T := by
    intro T hT
    exact c1Theorem3Potential_ac x hx hmean t₀ T hT
  have hdecay : ∀ T ≥ t₀,
      ∀ᵐ r ∂MeasureTheory.volume.restrict (Set.Icc t₀ T),
        deriv (c1Theorem3Potential x t₀) r ≤ -2 * 3 * c1Theorem3Potential x t₀ r := by
    intro T hT
    by_cases hEq : T = t₀
    · subst T
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1
        (by simp : MeasureTheory.volume (Set.Icc t₀ t₀) = 0)] with r hr hmem
      exact False.elim (hr hmem)
    · exact c1Theorem3Potential_decay_ae x hx hmean t₀ T
        (lt_of_le_of_ne hT (Ne.symm hEq))
  have herr : ∀ r ≥ t₀,
      (Metric.infDist (consensusOptimalFlow.flow t₀ x r) (DA.sharedTCZ box r)) ^ 2 ≤
        c1Theorem3Potential x t₀ r := by
    intro r hr
    have hy := consensusOptimalFlow_forward_invariant x hx t₀ r hr
    have hdist := consensus_global_error_bound (consensusOptimalFlow.flow t₀ x r) hy r
    have hphi := c1Theorem3Potential_eq_of_zeroMean x hx hmean t₀ r hr
    nlinarith [hshared_nonneg r hr]
  letI : ∀ i : Fin 2, PseudoMetricSpace (c1Theorem3System.State i) := fun _ => by
    change PseudoMetricSpace ℝ
    infer_instance
  have hresult := c1Theorem3System.theorem3_two_distance_bounds_of_ac_ae_descent
    (c1Theorem3Trajectory t₀ x) (fun r => c1Theorem3SharedTCZ r)
    (fun r => DA.potential (consensusOptimalFlow.flow t₀ x r) r)
    c1Theorem3Weight 0 3 1 t₀ s
    (by norm_num [c1Theorem3Weight]) (by norm_num) (by norm_num) hs
    (fun r hr => hshared_nonneg r hr.1)
    (fun r hr i => hterms r hr.1 i)
    (fun r hr => hTCZ r hr.1)
    (hAC s hs) (hdecay s hs)
    (fun r hr => by
      change (Metric.infDist (consensusOptimalFlow.flow t₀ x r)
        (DA.sharedTCZ box r)) ^ 2 ≤ _
      simpa [c1Theorem3Potential] using herr r hr.1)
  refine ⟨?_, ?_⟩
  · have hstate := hresult.1
    change Metric.infDist (consensusOptimalFlow.flow t₀ x s)
      (DA.sharedTCZ box s) ≤ _ at hstate
    simpa [c1Theorem3Potential] using hstate
  · simpa [c1Theorem3Potential, c1Theorem3Trajectory] using hresult.2



/-- Finite-time quantitative conclusion for the actual full-`Φ₃` zero set. -/
theorem c1Theorem3_original_phi3_bound
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (i : Fin 2) (t₀ s : ℝ) (ht₀ : 0 ≤ t₀) (hs : t₀ ≤ s) :
    Metric.infDist (consensusOptimalFlow.flow t₀ x s)
        (c1Theorem3OriginalTCZ t₀ s) ≤
      Real.sqrt (c1Theorem3Potential x t₀ t₀) * Real.exp (-3 * (s - t₀)) ∧
    euclideanCoordinateNorm
      (c1Theorem3System.ι
        (c1Theorem3System.abstraction i ((consensusOptimalFlow.flow t₀ x s) i)) -
        c1Theorem3System.ι c1Theorem3System.lub) ≤
      Real.sqrt (c1Theorem3Potential x t₀ t₀ / c1Theorem3Weight i) *
        Real.exp (-3 * (s - t₀)) := by
  have hterms : ∀ r ≥ t₀, ∀ j : Fin 2,
      0 ≤ c1Theorem3Weight j * c1Theorem3System.abstractResidual j
        (c1Theorem3Trajectory t₀ x j r) := by
    intro r hr j
    exact mul_nonneg (by norm_num [c1Theorem3Weight])
      (AbstractSharedSystem.abstractResidual_nonneg c1Theorem3System j _)
  have hshared_nonneg : ∀ r ≥ t₀,
      0 ≤ DA.potential (consensusOptimalFlow.flow t₀ x r) r := by
    intro r hr
    rw [sharedPotential_eq_coupling _
      (consensusOptimalFlow_forward_invariant x hx t₀ r hr) r]
    exact mul_nonneg (by norm_num [γ]) (sq_nonneg _)
  have hTCZ : ∀ r ≥ t₀, (c1Theorem3OriginalTCZ t₀ r).Nonempty := by
    intro r hr
    exact c1Theorem3OriginalTCZ_nonempty t₀ r ht₀
  have herr : ∀ r ≥ t₀,
      (Metric.infDist (fun j => c1Theorem3Trajectory t₀ x j r)
        (c1Theorem3OriginalTCZ t₀ r)) ^ 2 ≤ c1Theorem3Potential x t₀ r := by
    intro r hr
    let y := consensusOptimalFlow.flow t₀ x r
    have hybox := consensusOptimalFlow_forward_invariant x hx t₀ r hr
    have hymean : y 0 + y 1 = 0 := c1Theorem3Trajectory_zeroMean x hmean t₀ r
    have hzeroMem : c1Theorem3Zero ∈ c1Theorem3OriginalTCZ t₀ r := by
      rw [c1Theorem3OriginalTCZ_eq_singleton t₀ r ht₀]
      simp [c1Theorem3Zero]
    have hdist : Metric.infDist y (c1Theorem3OriginalTCZ t₀ r) ≤ |y 0| := by
      calc
        Metric.infDist y (c1Theorem3OriginalTCZ t₀ r) ≤ dist y c1Theorem3Zero :=
          Metric.infDist_le_dist_of_mem hzeroMem
        _ ≤ |y 0| := by
          apply (dist_pi_le_iff (abs_nonneg (y 0))).2
          intro j
          fin_cases j
          · simp [c1Theorem3Zero]
          · have hy1 : y 1 = -y 0 := by linarith
            simp [c1Theorem3Zero, hy1]
    have hphi : c1Theorem3Potential x t₀ r = 9 * y 0 ^ 2 := by
      rw [c1Theorem3Potential_eq_of_zeroMean x hx hmean t₀ r hr]
      rw [sharedPotential_eq_coupling y hybox r]
      have hy1 : y 1 = -y 0 := by linarith
      rw [hy1]
      simp [γ]
      ring
    have hn : 0 ≤ Metric.infDist y (c1Theorem3OriginalTCZ t₀ r) :=
      Metric.infDist_nonneg
    have hsq := (sq_le_sq₀ hn (abs_nonneg (y 0))).2 hdist
    rw [hphi]
    change (Metric.infDist y (c1Theorem3OriginalTCZ t₀ r)) ^ 2 ≤ 9 * y 0 ^ 2
    rw [sq_abs] at hsq
    nlinarith [hsq]
  have hdecay : ∀ T ≥ t₀,
      ∀ᵐ r ∂MeasureTheory.volume.restrict (Set.Icc t₀ T),
        deriv (c1Theorem3Potential x t₀) r ≤ -2 * 3 * c1Theorem3Potential x t₀ r := by
    intro T hT
    by_cases hEq : T = t₀
    · subst T
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1
        (by simp : MeasureTheory.volume (Set.Icc t₀ t₀) = 0)] with r hr hmem
      exact False.elim (hr hmem)
    · exact c1Theorem3Potential_decay_ae x hx hmean t₀ T
        (lt_of_le_of_ne hT (Ne.symm hEq))
  letI : ∀ j : Fin 2, PseudoMetricSpace (c1Theorem3System.State j) := fun _ => by
    change PseudoMetricSpace ℝ
    infer_instance
  have hresult := c1Theorem3System.theorem3_two_distance_bounds_of_ac_ae_descent
    (c1Theorem3Trajectory t₀ x) (fun r => c1Theorem3OriginalTCZ t₀ r)
    (fun r => DA.potential (consensusOptimalFlow.flow t₀ x r) r)
    c1Theorem3Weight i 3 1 t₀ s
    (by norm_num [c1Theorem3Weight]) (by norm_num) (by norm_num) hs
    (by intro r hr; exact hshared_nonneg r hr.1)
    (by intro r hr j; exact hterms r hr.1 j)
    (by intro r hr; exact hTCZ r hr.1)
    (c1Theorem3Potential_ac x hx hmean t₀ s hs)
    (hdecay s hs)
    (by intro r hr
        change (Metric.infDist (fun j => c1Theorem3Trajectory t₀ x j r)
          (c1Theorem3OriginalTCZ t₀ r)) ^ 2 ≤ _
        simpa [c1Theorem3Potential, c1Theorem3Trajectory, one_mul] using herr r hr.1)
  rcases hresult with ⟨hstate, habs⟩
  change Metric.infDist (consensusOptimalFlow.flow t₀ x s)
    (c1Theorem3OriginalTCZ t₀ s) ≤ _ at hstate
  refine ⟨?_, ?_⟩
  · simpa [c1Theorem3Potential, c1Theorem3Trajectory, one_mul] using hstate
  · simpa [c1Theorem3Potential, c1Theorem3Trajectory] using habs

/-- The state distance to the full-`Φ₃` zero set and every agent's LUB
representation converge to zero, with their finite-time rates supplied by the
preceding bound. -/
theorem c1Theorem3_original_phi3_tendsto
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    Filter.Tendsto
      (fun s => Metric.infDist (consensusOptimalFlow.flow t₀ x s)
        (c1Theorem3OriginalTCZ t₀ s)) atTop (𝓝 0) ∧
    ∀ i : Fin 2, Filter.Tendsto
      (fun s => euclideanCoordinateNorm
        (c1Theorem3System.ι (c1Theorem3System.abstraction i
          ((consensusOptimalFlow.flow t₀ x s) i)) - c1Theorem3System.ι c1Theorem3System.lub))
      atTop (𝓝 0) := by
  have hstate_nonneg : ∀ᶠ s in atTop,
      0 ≤ Metric.infDist (consensusOptimalFlow.flow t₀ x s)
        (c1Theorem3OriginalTCZ t₀ s) :=
    Filter.Eventually.of_forall fun _ => Metric.infDist_nonneg
  have hstate_bound : ∀ᶠ s in atTop,
      Metric.infDist (consensusOptimalFlow.flow t₀ x s)
        (c1Theorem3OriginalTCZ t₀ s) ≤
          Real.sqrt (c1Theorem3Potential x t₀ t₀) * Real.exp (-3 * (s - t₀)) := by
    filter_upwards [Filter.eventually_ge_atTop t₀] with s hs
    exact (c1Theorem3_original_phi3_bound x hx hmean 0 t₀ s ht₀ hs).1
  have hstate := Tomabechi.Theorem2.exponential_envelope_tendsto_zero
    (fun s => Metric.infDist (consensusOptimalFlow.flow t₀ x s)
      (c1Theorem3OriginalTCZ t₀ s))
    (Real.sqrt (c1Theorem3Potential x t₀ t₀)) 3 t₀ (by norm_num)
    hstate_nonneg hstate_bound
  refine ⟨hstate, ?_⟩
  intro i
  have hi_nonneg : ∀ᶠ s in atTop,
      0 ≤ euclideanCoordinateNorm
        (c1Theorem3System.ι (c1Theorem3System.abstraction i
          ((consensusOptimalFlow.flow t₀ x s) i)) - c1Theorem3System.ι c1Theorem3System.lub) :=
    Filter.Eventually.of_forall fun _ => euclideanCoordinateNorm_nonneg _
  have hi_bound : ∀ᶠ s in atTop,
      euclideanCoordinateNorm
        (c1Theorem3System.ι (c1Theorem3System.abstraction i
          ((consensusOptimalFlow.flow t₀ x s) i)) - c1Theorem3System.ι c1Theorem3System.lub) ≤
          Real.sqrt (c1Theorem3Potential x t₀ t₀ / c1Theorem3Weight i) *
            Real.exp (-3 * (s - t₀)) := by
    filter_upwards [Filter.eventually_ge_atTop t₀] with s hs
    exact (c1Theorem3_original_phi3_bound x hx hmean i t₀ s ht₀ hs).2
  exact Tomabechi.Theorem2.exponential_envelope_tendsto_zero
    (fun s => euclideanCoordinateNorm
      (c1Theorem3System.ι (c1Theorem3System.abstraction i
        ((consensusOptimalFlow.flow t₀ x s) i)) - c1Theorem3System.ι c1Theorem3System.lub))
    (Real.sqrt (c1Theorem3Potential x t₀ t₀ / c1Theorem3Weight i)) 3 t₀
    (by norm_num) hi_nonneg hi_bound



end Tomabechi.Consistency.ConsistencyC1Theorem3Bridge
