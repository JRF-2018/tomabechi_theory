import Theorem15_23

/-!
# C2: 可算無限層のエントロピー収支

各正層を `n+1` で列挙し、物理層 `0` は別枠に置く。層重みは幾何級数、
全層の意味エントロピーは同じ状態観測量とする。完全状態には環境観測量も含め、
その観測量自身をエントロピーに使う。以下の射影は層を粗視化しても状態を保つ
具体例であり、A3/A4を型付きで記録する。
-/

namespace Tomabechi.Consistency.C2

open Filter
open scoped Topology

/-- A uniformly bounded measurable family is uniformly integrable on a finite
measure space. We state the explicit bound used by the finite-subset H-sum. -/
theorem uniformIntegrable_of_bound_two
    {Time Index : Type*} [MeasurableSpace Time]
    (μ : MeasureTheory.Measure Time) [MeasureTheory.IsFiniteMeasure μ]
    (f : Index → Time → ℝ)
    (hmeas : ∀ i, MeasureTheory.AEStronglyMeasurable (f i) μ)
    (hbound : ∀ i, ∀ᵐ t ∂μ, ‖f i t‖ ≤ 2) :
    MeasureTheory.UniformIntegrable f 1 μ := by
  refine ⟨?_, ?_⟩
  · rw [MeasureTheory.unifIntegrable_iff]
    intro ε hε
    refine ⟨ε / 2, ENNReal.div_pos (ne_of_gt hε) (by norm_num), ?_⟩
    intro i s hs
    have hac : (μ.restrict s).AbsolutelyContinuous μ :=
      MeasureTheory.Measure.absolutelyContinuous_restrict
    have hmeasS := (hmeas i).mono_ac hac
    have hboundS := MeasureTheory.ae_restrict_of_ae (s := s) (hbound i)
    have hnorm := MeasureTheory.eLpNorm_le_of_ae_bound hmeasS hboundS
      (p := 1) (C := 2)
    have hnorm' : MeasureTheory.eLpNorm (f i) 1 (μ.restrict s) ≤
        μ s * 2 := by
      simpa [MeasureTheory.Measure.restrict_apply_univ, ENNReal.rpow_one] using hnorm
    calc
      MeasureTheory.eLpNorm (f i) 1 (μ.restrict s) ≤ μ s * 2 := hnorm'
      _ ≤ (ε / 2) * 2 := by gcongr
      _ = ε := by rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  · refine ⟨(μ Set.univ).toNNReal * 2, fun i => ?_⟩
    have hnorm := MeasureTheory.eLpNorm_le_of_ae_bound (hmeas i) (hbound i)
      (p := 1) (C := 2)
    have hμne : μ Set.univ ≠ ⊤ :=
      ne_of_lt MeasureTheory.IsFiniteMeasure.measure_univ_lt_top
    have hnorm' : MeasureTheory.eLpNorm (f i) 1 μ ≤ μ Set.univ * 2 := by
      simpa [ENNReal.rpow_one] using hnorm
    have hcoe : (↑((μ Set.univ).toNNReal * 2) : ENNReal) = μ Set.univ * 2 := by
      rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hμne]
      norm_num
    simpa [hcoe] using hnorm'

/-- A continuously differentiable scalar observable is absolutely continuous
on every finite interval. -/
theorem absolutelyContinuous_of_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f')
    (a b : ℝ) : AbsolutelyContinuousOnInterval f a b := by
  have hint : IntervalIntegrable f' MeasureTheory.volume a b := hc.intervalIntegrable a b
  have hrep : ∀ t, f t = f a + ∫ v in a..t, f' v := by
    intro t
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
      (hc.intervalIntegrable a t)]
    ring
  have h1 := hint.absolutelyContinuousOnInterval_intervalIntegral
    (Set.left_mem_uIcc (a := a) (b := b))
  have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  exact (h2.add h1).congr (fun t _ => by simp [hrep t])

abbrev CompleteState := ℝ × ℝ
abbrev PositiveLayer := ℕ

/-- 第1座標を認知状態、第2座標を環境・物理観測と読む。 -/
def cognitiveCoordinate (z : CompleteState) : ℝ := z.1
def physicalCoordinate (z : CompleteState) : ℝ := z.2

/-- 正層 n は原文の添字 n+1 に対応する。 -/
def originalPositiveIndex (n : PositiveLayer) : ℕ := n + 1

def originalLayerIndexSet : Set ℝ := Set.range (fun a : ℕ => (a : ℝ))

theorem originalLayerIndexSet_countable : originalLayerIndexSet.Countable :=
  Set.countable_range _

theorem originalLayerIndexSet_nonnegative :
    originalLayerIndexSet ⊆ Set.Ici 0 := by
  rintro x ⟨a, rfl⟩
  change 0 ≤ (a : ℝ)
  exact Nat.cast_nonneg a

theorem originalPositiveIndex_pos (n : PositiveLayer) : 0 < originalPositiveIndex n := by
  simp [originalPositiveIndex]

theorem originalPositiveIndex_injective : Function.Injective originalPositiveIndex := by
  intro m n h
  simp [originalPositiveIndex] at h
  omega

noncomputable def originalPositiveRealIndex (n : PositiveLayer) : ℝ :=
  (originalPositiveIndex n : ℝ)

theorem originalPositiveRealIndex_pos (n : PositiveLayer) :
    0 < originalPositiveRealIndex n := by
  dsimp [originalPositiveRealIndex]
  exact_mod_cast originalPositiveIndex_pos n

theorem originalPositiveRealIndex_injective :
    Function.Injective originalPositiveRealIndex := by
  intro m n h
  apply originalPositiveIndex_injective
  exact Nat.cast_injective h

/-- 正の幾何重み `2^(-(n+1))`。 -/
noncomputable def layerWeight (n : PositiveLayer) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

theorem layerWeight_pos (n : PositiveLayer) : 0 < layerWeight n := by
  unfold layerWeight
  positivity

theorem positiveLayer_infinite : Infinite PositiveLayer := inferInstance

theorem layerWeight_summable : Summable layerWeight := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have heq : layerWeight = fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
    funext n
    simp [layerWeight, pow_succ, mul_comm]
  rw [heq]
  exact hg.mul_left _

theorem layerWeight_tsum : (∑' n : PositiveLayer, layerWeight n) = 1 := by
  have hgeom : (∑' n : ℕ, (1 / 2 : ℝ) ^ n) = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have heq : layerWeight = fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
    funext n
    simp [layerWeight, pow_succ, mul_comm]
  rw [heq, tsum_mul_left, hgeom]
  norm_num

theorem layerWeight_sum_le_one (s : Finset PositiveLayer) :
    (∑ n ∈ s, layerWeight n) ≤ 1 := by
  calc
    (∑ n ∈ s, layerWeight n) ≤ ∑' n : PositiveLayer, layerWeight n :=
      layerWeight_summable.sum_le_tsum s (by
        intro n hn
        exact le_of_lt (layerWeight_pos n))
    _ = 1 := layerWeight_tsum

/-- 意味エントロピーは状態の認知座標の `1+q²`。 -/
def layerEntropy (_n : PositiveLayer) (z : CompleteState) : ℝ :=
  1 + (cognitiveCoordinate z) ^ 2

def physicalEntropy (z : CompleteState) : ℝ := physicalCoordinate z

/-- 物理層のエントロピーは独立に0とし、正層列挙へ混ぜない。 -/
def physicalLayerEntropy (_z : CompleteState) : ℝ := 0

/-- 原文の全層添字では `0` を物理層、`a>0` を正層として扱う。 -/
def originalLayerEntropy (a : ℕ) (z : CompleteState) : ℝ :=
  if a = 0 then physicalLayerEntropy z else 1 + (cognitiveCoordinate z) ^ 2

theorem originalLayerEntropy_physical (z : CompleteState) :
    originalLayerEntropy 0 z = physicalLayerEntropy z := by
  simp [originalLayerEntropy]

theorem originalLayerEntropy_positive (n : PositiveLayer) (z : CompleteState) :
    originalLayerEntropy (originalPositiveIndex n) z = layerEntropy n z := by
  simp [originalLayerEntropy, originalPositiveIndex, layerEntropy]

/-- 原文の全層状態は同じ完全状態空間で表し、粗視化射影を恒等写像にする。 -/
def originalProject (α β : ℕ) (_h : β < α) (z : CompleteState) : CompleteState := z

def originalProjection (α β : ℕ) (_h : β ≤ α) (z : CompleteState) : CompleteState := z

theorem originalProjection_measurable (α β : ℕ) (h : β ≤ α) :
    Measurable (originalProjection α β h) := by
  change Measurable (fun z : CompleteState => z)
  exact measurable_id

theorem originalProjection_reflexive (α : ℕ) (z : CompleteState) :
    originalProjection α α le_rfl z = z := rfl

theorem originalProjection_compose (α β γ : ℕ) (h₁ : β ≤ α) (h₂ : γ ≤ β)
    (z : CompleteState) :
    originalProjection β γ h₂ (originalProjection α β h₁ z) =
      originalProjection α γ (by omega) z := rfl

theorem originalProject_measurable (α β : ℕ) (h : β < α) :
    Measurable (originalProject α β h) := by
  change Measurable (fun z : CompleteState => z)
  exact measurable_id

theorem originalProject_reflect (α β : ℕ) (h : β < α) (z : CompleteState) :
    originalProject α β h z = z := rfl

theorem originalProject_bijective (α β : ℕ) (h : β < α) :
    Function.Bijective (originalProject α β h) := by
  change Function.Bijective (fun z : CompleteState => z)
  exact Function.bijective_id

theorem originalProject_compose (α β γ : ℕ) (h₁ : β < α) (h₂ : γ < β)
    (z : CompleteState) :
    originalProject β γ h₂ (originalProject α β h₁ z) =
      originalProject α γ (by omega) z := rfl

/-- A4: positive layers have the same entropy and identity projection, so
coarse-graining preserves entropy and is invertible on equality. -/
theorem originalLayer_coarse_graining (α β : ℕ) (hα : 0 < α)
    (hβ : 0 < β) (h : β < α) (z : CompleteState) :
    originalLayerEntropy β (originalProject α β h z) ≥ originalLayerEntropy α z ∧
      (originalLayerEntropy β (originalProject α β h z) = originalLayerEntropy α z →
        ∃ y, originalProject α β h y = z) := by
  constructor
  · simp [originalLayerEntropy, originalProject, Nat.ne_of_gt hα, Nat.ne_of_gt hβ]
  · intro _
    exact ⟨z, rfl⟩

theorem layerEntropy_nonnegative (z : CompleteState) (n : PositiveLayer) :
    0 ≤ layerEntropy n z := by
  simp [layerEntropy]
  positivity

/-- 各正層の射影。 -/
def project (α β : ℕ) (h : β < α) (z : CompleteState) : CompleteState := z

theorem project_measurable (α β : ℕ) (h : β < α) :
    Measurable (project α β h) := by
  change Measurable (fun z : CompleteState => z)
  exact measurable_id

theorem project_reflect (α β : ℕ) (h : β < α) (z : CompleteState) :
    project α β h z = z := rfl

/-- 射影の合成則。 -/
theorem project_compose (α β γ : ℕ) (h₁ : β < α) (h₂ : γ < β)
    (z : CompleteState) :
    project β γ h₂ (project α β h₁ z) = project α γ (by omega) z := rfl

/-- 粗視化で層エントロピーは保存される。等号の場合の逆向きも明示する。 -/
theorem coarse_graining_entropy (α β : ℕ) (h : β < α) (z : CompleteState) :
    layerEntropy β (project α β h z) ≥ layerEntropy α z ∧
      (layerEntropy β (project α β h z) = layerEntropy α z →
        ∃ y, project α β h y = z) := by
  constructor
  · rfl
  · intro _
    exact ⟨z, rfl⟩

/-- 観測軌道。`q'=1-q`、`y'=q` を環境を含む完全状態上で実現する。 -/
noncomputable def trajectory (t : ℝ) : CompleteState :=
  let q := 1 - Real.exp (-t)
  (q, t - q ^ 2)

abbrev DirectSumState := PositiveLayer → CompleteState

def layerDomain (_a : ℕ) : Set CompleteState := Set.univ

theorem layerDomain_measurable (a : ℕ) : MeasurableSet (layerDomain a) :=
  MeasurableSet.univ

theorem trajectory_continuous : Continuous trajectory := by
  unfold trajectory
  fun_prop

theorem trajectory_measurable : Measurable trajectory :=
  trajectory_continuous.measurable

def diagonalEmbedding (z : CompleteState) : DirectSumState := fun _ => z

theorem diagonalEmbedding_injective : Function.Injective diagonalEmbedding := by
  intro x y h
  exact congrFun h 0

noncomputable def directSumTrajectory (t : ℝ) : DirectSumState :=
  diagonalEmbedding (trajectory t)

theorem directSumTrajectory_measurable : Measurable directSumTrajectory := by
  apply measurable_pi_lambda
  intro n
  exact trajectory_measurable

theorem directSumTrajectory_projection (t : ℝ) (n : PositiveLayer) :
    directSumTrajectory t n = trajectory t := rfl

theorem directSumTrajectory_is_diagonal (t : ℝ) :
    directSumTrajectory t = diagonalEmbedding (trajectory t) := rfl

noncomputable def qCoordinate (t : ℝ) : ℝ := 1 - Real.exp (-t)

def alive : Set ℝ := Set.Ici 0

def production (_t : ℝ) : ℝ := 1

theorem production_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable production MeasureTheory.volume a b := by
  exact continuous_const.intervalIntegrable a b

noncomputable def cognitiveEntropyRate (t : ℝ) : ℝ :=
  2 * qCoordinate t * Real.exp (-t)

noncomputable def physicalEntropyRate (t : ℝ) : ℝ :=
  1 - cognitiveEntropyRate t

theorem continuous_cognitiveEntropyRate : Continuous cognitiveEntropyRate := by
  unfold cognitiveEntropyRate qCoordinate
  fun_prop

theorem continuous_physicalEntropyRate : Continuous physicalEntropyRate := by
  unfold physicalEntropyRate
  exact continuous_const.sub continuous_cognitiveEntropyRate

theorem cognitiveCoordinate_hasDerivAt_pre (t : ℝ) :
    HasDerivAt (fun s => cognitiveCoordinate (trajectory s))
      (Real.exp (-t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  have hq := HasDerivAt.const_sub (1 : ℝ) hexp
  simpa [trajectory, cognitiveCoordinate] using hq

theorem layerEntropy_hasDerivAt_pre (n : PositiveLayer) (t : ℝ) :
    HasDerivAt (fun s => layerEntropy n (trajectory s))
      (2 * cognitiveCoordinate (trajectory t) * Real.exp (-t)) t := by
  have hq := cognitiveCoordinate_hasDerivAt_pre t
  have hsq := hq.pow 2
  have hadd := (hasDerivAt_const t (1 : ℝ)).add hsq
  have hderiv : 0 + (2 : ℝ) * cognitiveCoordinate (trajectory t) ^ (2 - 1) *
      Real.exp (-t) = 2 * cognitiveCoordinate (trajectory t) * Real.exp (-t) := by
    norm_num
  have h' := HasDerivAt.congr_deriv hadd hderiv
  apply HasDerivAt.congr_of_eventuallyEq h'
  filter_upwards [] with s
  simp [layerEntropy]

theorem layerEntropy_deriv_eq_rate_pre (n : PositiveLayer) (t : ℝ) :
    deriv (fun s => layerEntropy n (trajectory s)) t = cognitiveEntropyRate t := by
  rw [(layerEntropy_hasDerivAt_pre n t).deriv]
  simp [cognitiveEntropyRate, qCoordinate, cognitiveCoordinate, trajectory]

theorem layerEntropy_deriv_eq_rate (n : PositiveLayer) (t : ℝ) :
    deriv (fun s => layerEntropy n (trajectory s)) t = cognitiveEntropyRate t := by
  exact layerEntropy_deriv_eq_rate_pre n t

noncomputable def finiteCognitiveRate (s : Finset PositiveLayer) (t : ℝ) : ℝ :=
  ∑ n ∈ s, layerWeight n * deriv (fun u => layerEntropy n (trajectory u)) t

theorem cognitiveEntropyRate_bounds {t : ℝ} (ht : t ∈ alive) :
    0 ≤ cognitiveEntropyRate t ∧ cognitiveEntropyRate t ≤ 2 := by
  have ht' : 0 ≤ t := by simpa [alive] using ht
  have hexp1 : Real.exp (-t) ≤ 1 := (Real.exp_le_one_iff).2 (by linarith)
  have hexp0 : 0 ≤ Real.exp (-t) := Real.exp_nonneg _
  have hq0 : 0 ≤ qCoordinate t := by
    dsimp [qCoordinate]
    linarith [hexp1]
  have hq1 : qCoordinate t ≤ 1 := by
    dsimp [qCoordinate]
    linarith [hexp0]
  constructor
  · unfold cognitiveEntropyRate
    positivity
  · unfold cognitiveEntropyRate
    calc
      2 * qCoordinate t * Real.exp (-t) ≤ 2 * 1 * 1 := by
        gcongr
      _ = 2 := by norm_num

theorem finiteCognitiveRate_continuous (s : Finset PositiveLayer) :
    Continuous (finiteCognitiveRate s) := by
  have heq : finiteCognitiveRate s = fun t =>
      (∑ n ∈ s, layerWeight n) * cognitiveEntropyRate t := by
    funext t
    simp only [finiteCognitiveRate]
    simp_rw [layerEntropy_deriv_eq_rate_pre]
    rw [Finset.sum_mul]
  rw [heq]
  exact continuous_const.mul continuous_cognitiveEntropyRate

theorem finiteCognitiveRate_bounds (s : Finset PositiveLayer) {t : ℝ}
    (ht : t ∈ alive) : 0 ≤ finiteCognitiveRate s t ∧
      finiteCognitiveRate s t ≤ 2 := by
  have hformula : finiteCognitiveRate s t =
      (∑ n ∈ s, layerWeight n) * cognitiveEntropyRate t := by
    simp [finiteCognitiveRate, layerEntropy_deriv_eq_rate_pre, Finset.sum_mul]
  rw [hformula]
  have hw0 : 0 ≤ ∑ n ∈ s, layerWeight n := by
    apply Finset.sum_nonneg
    intro n hn
    exact le_of_lt (layerWeight_pos n)
  have hw1 := layerWeight_sum_le_one s
  have hr := cognitiveEntropyRate_bounds ht
  constructor
  · exact mul_nonneg hw0 hr.1
  · calc
      (∑ n ∈ s, layerWeight n) * cognitiveEntropyRate t ≤ 1 * 2 :=
        mul_le_mul hw1 hr.2 hr.1 (by norm_num)
      _ = 2 := by norm_num

/-- この完全状態上の時間非依存一般化エントロピー。 -/
noncomputable def generalizedEntropy (z : CompleteState) : ℝ :=
  physicalEntropy z +
    ∑' n : PositiveLayer, layerWeight n * layerEntropy n z

theorem weightedLayerEntropy_tsum (z : CompleteState) :
    (∑' n : PositiveLayer, layerWeight n * layerEntropy n z) =
      1 + (cognitiveCoordinate z) ^ 2 := by
  have hrewrite : (fun n : PositiveLayer => layerWeight n * layerEntropy n z) =
      fun n => layerEntropy n z * layerWeight n := by
    funext n
    ring
  rw [hrewrite]
  simp only [layerEntropy]
  rw [tsum_mul_left, layerWeight_tsum]
  ring

theorem weightedLayerEntropy_summable (z : CompleteState) :
    Summable (fun n : PositiveLayer => layerWeight n * layerEntropy n z) := by
  have hweight := layerWeight_summable
  have hrewrite : (fun n : PositiveLayer => layerWeight n * layerEntropy n z) =
      fun n => (1 + (cognitiveCoordinate z) ^ 2) * layerWeight n := by
    funext n
    simp [layerEntropy]
    ring
  rw [hrewrite]
  exact hweight.mul_left _

theorem trajectory_cognitive_nonneg {t : ℝ} (ht : t ∈ alive) :
    0 ≤ cognitiveCoordinate (trajectory t) := by
  simp [alive, trajectory, cognitiveCoordinate] at *
  have he : Real.exp (-t) ≤ 1 := (Real.exp_le_one_iff).2 (by linarith)
  linarith

theorem generalizedEntropy_trajectory (t : ℝ) :
    generalizedEntropy (trajectory t) = t + 1 := by
  rw [generalizedEntropy, weightedLayerEntropy_tsum]
  simp [physicalEntropy, cognitiveCoordinate, physicalCoordinate, trajectory]

theorem generalizedEntropy_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => generalizedEntropy (trajectory s)) 1 t := by
  rw [show (fun s : ℝ => generalizedEntropy (trajectory s)) = fun s => s + 1 by
    funext s
    exact generalizedEntropy_trajectory s]
  simpa [add_comm] using (hasDerivAt_id t).const_add (1 : ℝ)

/-- On the alive interval, `q(t)=1-exp(-t)` has rate `exp(-t)`. -/
theorem cognitiveCoordinate_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => cognitiveCoordinate (trajectory s))
      (Real.exp (-t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  have hq := HasDerivAt.const_sub (1 : ℝ) hexp
  simpa [trajectory, cognitiveCoordinate] using hq

/-- The individual entropy rate is nonzero at every positive time. -/
theorem layerEntropy_hasDerivAt (n : PositiveLayer) (t : ℝ) :
    HasDerivAt (fun s => layerEntropy n (trajectory s))
      (2 * cognitiveCoordinate (trajectory t) * Real.exp (-t)) t := by
  have hq := cognitiveCoordinate_hasDerivAt t
  have hsq := hq.pow 2
  have hadd := (hasDerivAt_const t (1 : ℝ)).add hsq
  have hderiv : 0 + (2 : ℝ) * cognitiveCoordinate (trajectory t) ^ (2 - 1) *
      Real.exp (-t) = 2 * cognitiveCoordinate (trajectory t) * Real.exp (-t) := by
    norm_num
  have h' := HasDerivAt.congr_deriv hadd hderiv
  apply HasDerivAt.congr_of_eventuallyEq h'
  filter_upwards [] with s
  simp [layerEntropy]

theorem layerEntropy_rate_pos {t : ℝ} (ht : 0 < t) (n : PositiveLayer) :
    0 < deriv (fun s => layerEntropy n (trajectory s)) t := by
  rw [(layerEntropy_hasDerivAt n t).deriv]
  have hq : 0 < cognitiveCoordinate (trajectory t) := by
    simp [trajectory, cognitiveCoordinate]
    have he : Real.exp (-t) < 1 := (Real.exp_lt_one_iff).2 (by linarith)
    linarith
  positivity

theorem qCoordinate_hasDerivAt (t : ℝ) :
    HasDerivAt qCoordinate (Real.exp (-t)) t := by
  have heq : qCoordinate = fun s => cognitiveCoordinate (trajectory s) := by
    funext s
    simp [qCoordinate, cognitiveCoordinate, trajectory]
  rw [heq]
  exact cognitiveCoordinate_hasDerivAt t

theorem physicalEntropy_along_eq (t : ℝ) :
    physicalEntropy (trajectory t) = t - (qCoordinate t) ^ 2 := by
  simp [physicalEntropy, physicalCoordinate, trajectory, qCoordinate]

theorem physicalEntropy_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => physicalEntropy (trajectory s))
      (1 - 2 * qCoordinate t * Real.exp (-t)) t := by
  have hq := qCoordinate_hasDerivAt t
  have hsq := hq.pow 2
  have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
  have hbase := hid.sub hsq
  have hderiv : 1 - (2 : ℝ) * qCoordinate t ^ (2 - 1) * Real.exp (-t) =
      1 - 2 * qCoordinate t * Real.exp (-t) := by norm_num
  have h' := HasDerivAt.congr_deriv hbase hderiv
  apply HasDerivAt.congr_of_eventuallyEq h'
  filter_upwards [] with s
  simpa [Function.comp_def] using (physicalEntropy_along_eq s)

theorem layerEntropy_ac (n : PositiveLayer) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => layerEntropy n (trajectory t)) a b := by
  have hf : ∀ t, HasDerivAt (fun s => layerEntropy n (trajectory s))
      (cognitiveEntropyRate t) t := by
    intro t
    convert layerEntropy_hasDerivAt n t using 1 <;>
      simp [cognitiveEntropyRate, qCoordinate, cognitiveCoordinate, trajectory]
  exact absolutelyContinuous_of_hasDerivAt hf continuous_cognitiveEntropyRate a b

theorem physicalEntropy_deriv_eq_rate (t : ℝ) :
    deriv (fun s => physicalEntropy (trajectory s)) t = physicalEntropyRate t := by
  rw [(physicalEntropy_hasDerivAt t).deriv]
  rfl

theorem physicalEntropy_ac (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => physicalEntropy (trajectory t)) a b := by
  have hf : ∀ t, HasDerivAt (fun s => physicalEntropy (trajectory s))
      (physicalEntropyRate t) t := by
    intro t
    convert physicalEntropy_hasDerivAt t using 1 <;>
      simp [physicalEntropyRate, cognitiveEntropyRate, qCoordinate,
        cognitiveCoordinate, trajectory]
  exact absolutelyContinuous_of_hasDerivAt hf continuous_physicalEntropyRate a b

theorem weightedLayerRate_tsum (t : ℝ) :
    (∑' n : PositiveLayer, layerWeight n *
      deriv (fun s => layerEntropy n (trajectory s)) t) = cognitiveEntropyRate t := by
  have hrewrite : (fun n : PositiveLayer => layerWeight n *
      deriv (fun s => layerEntropy n (trajectory s)) t) =
      fun n => cognitiveEntropyRate t * layerWeight n := by
    funext n
    rw [layerEntropy_deriv_eq_rate]
    ring
  rw [hrewrite, tsum_mul_left, layerWeight_tsum]
  ring

theorem theorem15_A7_pointwise (t : ℝ) :
    deriv (fun s => physicalEntropy (trajectory s)) t =
      -(∑' n : PositiveLayer, layerWeight n *
        deriv (fun s => layerEntropy n (trajectory s)) t) + production t := by
  rw [physicalEntropy_deriv_eq_rate, weightedLayerRate_tsum]
  simp [physicalEntropyRate, production]
  ring

theorem theorem15_A6_endpoint_summable (t : ℝ) :
    Summable (fun n : PositiveLayer =>
      layerWeight n * layerEntropy n (trajectory t)) :=
  weightedLayerEntropy_summable (trajectory t)

/-- The layer derivative series converges pointwise to its tsum. This supplies
the enumerated almost-everywhere limit in A6′(ii), in fact at every time. -/
theorem theorem15_A6_prefix_tendsto (t : ℝ) :
    Filter.Tendsto (fun k => ∑ i : Fin k,
      layerWeight ((Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer) i.val) *
        deriv (fun s => layerEntropy
          ((Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer) i.val)
          (trajectory s)) t) atTop
      (𝓝 (∑' n : PositiveLayer, layerWeight n *
        deriv (fun s => layerEntropy n (trajectory s)) t)) := by
  let e := Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer
  have hsum : Summable (fun n : PositiveLayer => layerWeight n *
      deriv (fun s => layerEntropy n (trajectory s)) t) := by
    have h := layerWeight_summable.mul_right (cognitiveEntropyRate t)
    simpa [layerEntropy_deriv_eq_rate] using h
  have h := Tomabechi.Theorem15.enumerated_tsum_partial_tendsto_of_summable
    e (fun n => layerWeight n *
      deriv (fun s => layerEntropy n (trajectory s)) t)
    hsum
  simpa [e, layerEntropy_deriv_eq_rate] using h

/-- Every finite-subset derivative sum is uniformly bounded on each alive
finite interval, hence the whole finite-subset family is UI there. -/
theorem theorem15_A6_allFinite_UI (a b : ℝ)
    (ha : a ∈ alive) (hb : b ∈ alive) (hab : a < b) :
    MeasureTheory.UniformIntegrable finiteCognitiveRate 1
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.uIoc a b)
  have hμfinite : MeasureTheory.IsFiniteMeasure μ := by
    apply (MeasureTheory.isFiniteMeasure_restrict).2
    simp [μ, Real.volume_uIoc]
  letI : MeasureTheory.IsFiniteMeasure μ := hμfinite
  have hmeas : ∀ s : Finset PositiveLayer,
      MeasureTheory.AEStronglyMeasurable (finiteCognitiveRate s) μ := by
    intro s
    exact (finiteCognitiveRate_continuous s).aestronglyMeasurable
  have hbound : ∀ s : Finset PositiveLayer,
      ∀ᵐ t ∂μ, ‖finiteCognitiveRate s t‖ ≤ 2 := by
    intro s
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
    have htIoc : t ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le hab.le] using ht
    have ha0 : 0 ≤ a := by simpa [alive] using ha
    have ht0 : 0 ≤ t := le_trans ha0 htIoc.1.le
    have hbnd := finiteCognitiveRate_bounds s (by simpa [alive] using ht0)
    rw [Real.norm_eq_abs, abs_of_nonneg hbnd.1]
    exact hbnd.2
  simpa [μ] using uniformIntegrable_of_bound_two μ finiteCognitiveRate hmeas hbound

/-- Apply the countably-infinite-layer 15→23-A entrance to the concrete
complete-state trajectory. This is a witness for the specified model. -/
theorem c2_theorem23_nonrecurrence :
    ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      trajectory t₂ ≠ trajectory t₁ := by
  apply Tomabechi.Theorem15_23.theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence
    (Layer := PositiveLayer) (State := CompleteState)
    (physicalEntropy := physicalEntropy) (layerEntropy := layerEntropy)
    (layerWeight := layerWeight) layerWeight_pos
    (fun n z => layerEntropy_nonnegative z n)
    trajectory production alive
  · intro a b ha hb hab
    have hinterval : (∫ t in a..b, production t) = b - a := by
      simp [production, intervalIntegral.integral_const]
    rw [hinterval]
    linarith
  · intro a b ha hb hab n
    exact layerEntropy_ac n a b
  · intro a b ha hb hab
    exact physicalEntropy_ac a b
  · intro a b ha hb hab
    exact ⟨theorem15_A6_endpoint_summable a, theorem15_A6_endpoint_summable b⟩
  · exact theorem15_A6_allFinite_UI
  · intro a b ha hb hab
    exact Filter.Eventually.of_forall theorem15_A6_prefix_tendsto
  · intro a b ha hb hab
    exact Filter.Eventually.of_forall theorem15_A7_pointwise
  · intro a b ha hb hab
    exact Filter.Eventually.of_forall (fun _ => by norm_num [production])

theorem production_integral (a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, production t) = b - a := by
  simp [production, intervalIntegral.integral_const, hab]

theorem production_strict (a b : ℝ) (ha : a ∈ alive) (hb : b ∈ alive)
    (hab : a < b) : 0 < ∫ t in a..b, production t := by
  rw [production_integral a b hab.le]
  linarith

theorem theorem15_23A_strict_production (a b : ℝ)
    (ha : a ∈ alive) (hb : b ∈ alive) (hab : a < b) :
    0 < ∫ t in a..b, production t :=
  production_strict a b ha hb hab

theorem state_nonrepeats (a b : ℝ) (ha : a ∈ alive) (hb : b ∈ alive)
    (hab : a < b) : trajectory a ≠ trajectory b := by
  intro h
  have heq := congrArg generalizedEntropy h
  rw [generalizedEntropy_trajectory, generalizedEntropy_trajectory] at heq
  linarith

end Tomabechi.Consistency.C2
