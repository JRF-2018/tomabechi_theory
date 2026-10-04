import Tomabechi.Information.Capacity
import Tomabechi.Information.FiniteMeasureEntropy
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# 有限ゴール一般測度の条件付き相互情報量核

有限ゴールを保った一般測度CMI法則を構成し、直接KL表現・エントロピー評価を扱う。
文脈・出力を
有限型に限定せず、確率的出力を条件付き核として表す。共同法則保存のみで参照法則保存を
導く場合の可算生成条件と、KL対全体を保存する場合の一般可測空間版を分けて記録する。
-/

namespace Tomabechi.Theorem19_22

open Tomabechi.Theorem22
open MeasureTheory ProbabilityTheory

/-- A measurable representative of each coordinate of an a.e.-measurable
finite goal mass. This is the starting point for constructing the actual
Markov kernel used by the information conclusion; it does not assume that the
original mass is normalized at every input. -/
noncomputable def finiteGoalMassRepresentative
    {X G : Type*} [MeasurableSpace X] [Fintype G]
    (μ : Measure X) (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ) : X → G → ℝ :=
  fun x g => (hmass g).mk (fun x => mass x g) x

/-- The chosen measurable representatives agree with the supplied mass
coordinates almost everywhere. -/
theorem finiteGoalMassRepresentative_ae_eq
    {X G : Type*} [MeasurableSpace X] [Fintype G]
    (μ : Measure X) (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ) (g : G) :
    (fun x => finiteGoalMassRepresentative μ mass hmass x g) =ᵐ[μ]
      (fun x => mass x g) := by
  exact (hmass g).ae_eq_mk.symm

/-- The measurable versions inherit the a.e. probability constraints without
strengthening them to pointwise hypotheses on the original functions. -/
theorem finiteGoalMassRepresentative_probability_ae
    {X G : Type*} [MeasurableSpace X] [Fintype G]
    (μ : Measure X) (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1) :
    ∀ᵐ x ∂μ, (∀ g, 0 ≤ finiteGoalMassRepresentative μ mass hmass x g) ∧
      ∑ g : G, finiteGoalMassRepresentative μ mass hmass x g = 1 := by
  have hcoord : ∀ g, (fun x => finiteGoalMassRepresentative μ mass hmass x g) =ᵐ[μ]
      (fun x => mass x g) := fun g => finiteGoalMassRepresentative_ae_eq μ mass hmass g
  have hcoordAll : ∀ᵐ x ∂μ, ∀ g,
      finiteGoalMassRepresentative μ mass hmass x g = mass x g :=
    ae_all_iff.mpr hcoord
  filter_upwards [hnonneg, hsum, hcoordAll] with x hx htotal hcoords
  refine ⟨?_, ?_⟩
  · intro g
    rw [hcoords g]
    exact hx g
  · calc
      ∑ g : G, finiteGoalMassRepresentative μ mass hmass x g =
          ∑ g : G, mass x g := Finset.sum_congr rfl fun g _ => hcoords g
      _ = 1 := htotal

/-- The finite measure associated with a nonnegative finite probability vector. -/
noncomputable def finiteGoalMeasureOfMass
    {G : Type*} [MeasurableSpace G] [Fintype G]
    (p : G → ℝ) : Measure G :=
  ∑ g : G, ENNReal.ofReal (p g) • Measure.dirac g

/-- A normalized nonnegative finite vector defines a probability measure. -/
theorem finiteGoalMeasureOfMass_isProbability
    {G : Type*} [MeasurableSpace G] [Fintype G]
    (p : G → ℝ) (hnonneg : ∀ g, 0 ≤ p g) (hsum : ∑ g, p g = 1) :
    IsProbabilityMeasure (finiteGoalMeasureOfMass p) := by
  have h : HasSum p 1 := by simpa [hsum] using hasSum_fintype p
  rw [finiteGoalMeasureOfMass, ← Measure.sum_fintype]
  exact h.isProbabilityMeasure_sum_dirac hnonneg

/-- A finite measure built from goal masses has those exact singleton
probabilities. -/
theorem finiteGoalMeasureOfMass_singleton
    {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G] [Fintype G]
    (p : G → ℝ) (g : G) :
    finiteGoalMeasureOfMass p {g} = ENNReal.ofReal (p g) := by
  rw [finiteGoalMeasureOfMass, ← Measure.sum_fintype]
  exact Measure.sum_smul_dirac_singleton

/-- Guard an a.e. probability vector by a fixed point mass off its measurable
validity set. This yields a genuine Markov kernel while keeping the original
mass unchanged almost everywhere. -/
noncomputable def finiteGoalMassKernel
    {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] [Nonempty G]
    (μ : Measure X) (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1) : Kernel X G := by
  classical
  let p := finiteGoalMassRepresentative μ mass hmass
  let good : X → Prop := fun x => (∀ g, 0 ≤ p x g) ∧ ∑ g, p x g = 1
  have hp : ∀ g, Measurable (fun x => p x g) := fun g => (hmass g).measurable_mk
  have hgood : MeasurableSet {x | good x} := by
    dsimp [good]
    have hnonnegSet : ∀ g, MeasurableSet {x | 0 ≤ p x g} := fun g =>
      measurableSet_le measurable_const (hp g)
    have hsumFun : Measurable (fun x => ∑ g : G, p x g) := by
      apply Finset.measurable_sum
      intro g _
      exact hp g
    have hsumSet : MeasurableSet {x | ∑ g : G, p x g = 1} :=
      measurableSet_eq_fun hsumFun measurable_const
    convert (MeasurableSet.iInter hnonnegSet).inter hsumSet using 1
    ext x
    simp [good]
  letI : DecidablePred good := Classical.decPred good
  refine ⟨fun x => if good x then finiteGoalMeasureOfMass (p x)
    else (Measure.dirac (Classical.choice (inferInstance : Nonempty G)) : Measure G), ?_⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hraw : Measurable (fun x => finiteGoalMeasureOfMass (p x) s) := by
    simp only [finiteGoalMeasureOfMass, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.smul_apply]
    apply Finset.measurable_sum
    intro g _
    exact ENNReal.measurable_ofReal.comp (hp g) |>.mul_const _
  have hdirac : Measurable (fun _x : X =>
      (Measure.dirac (Classical.choice (inferInstance : Nonempty G)) : Measure G) s) :=
    measurable_const
  convert Measurable.ite hgood hraw hdirac using 1
  all_goals
    first
    | assumption
    | (ext x; by_cases hx : good x <;> simp [hx])

/-- The guarded kernel is a Markov kernel at every input. -/
theorem finiteGoalMassKernel_markov
    {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] [Nonempty G]
    (μ : Measure X) (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1) :
    IsMarkovKernel (finiteGoalMassKernel μ mass hmass hnonneg hsum) := by
  classical
  constructor
  intro x
  dsimp [finiteGoalMassKernel]
  split_ifs with hx
  · exact finiteGoalMeasureOfMass_isProbability _ hx.1 hx.2
  · infer_instance

/-- The guarded kernel agrees with the supplied conditional goal mass almost
everywhere, coordinate by coordinate. -/
theorem finiteGoalMassKernel_mass_ae_eq
    {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] [Nonempty G]
    (μ : Measure X) (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1) (g : G) :
    (fun x => ((finiteGoalMassKernel μ mass hmass hnonneg hsum) x {g}).toReal) =ᵐ[μ]
        (fun x => mass x g) := by
  have hvalid := finiteGoalMassRepresentative_probability_ae
    μ mass hmass hnonneg hsum
  have hcoords : ∀ᵐ x ∂μ, ∀ g,
      finiteGoalMassRepresentative μ mass hmass x g = mass x g :=
    ae_all_iff.mpr fun g => finiteGoalMassRepresentative_ae_eq μ mass hmass g
  filter_upwards [hvalid, hcoords] with x hx hmassx
  have hpos : 0 ≤ mass x g := by rw [← hmassx g]; exact hx.1 g
  simp [finiteGoalMassKernel, hx,
    finiteGoalMeasureOfMass_singleton, hmassx g, hpos]

/-- The actual joint law generated from the input law, guarded goal kernel,
and deterministic action. Its coordinates are ordered as X × (G × Y), matching
the direct KL-type CMI API. -/
noncomputable def finiteGoalActionGeneratedJoint
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [Nonempty G]
    (μ : Measure X) (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (action : X → G → Y) (haction : ∀ g, Measurable (fun x => action x g)) :
    Measure (X × (G × Y)) := by
  let κ := finiteGoalMassKernel μ mass hmass hnonneg hsum
  letI : IsMarkovKernel κ := finiteGoalMassKernel_markov μ mass hmass hnonneg hsum
  have hAct : Measurable (fun z : X × G => action z.1 z.2) := by
    apply measurable_from_prod_countable_left
    exact haction
  exact (μ ⊗ₘ κ).map (fun z => (z.1, (z.2, action z.1 z.2)))

/-- The generated joint is a probability law whenever the input is one. -/
theorem finiteGoalActionGeneratedJoint_isProbability
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [Nonempty G]
    (μ : Measure X) [IsProbabilityMeasure μ] (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (action : X → G → Y) (haction : ∀ g, Measurable (fun x => action x g)) :
    IsProbabilityMeasure
      (finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction) := by
  let κ := finiteGoalMassKernel μ mass hmass hnonneg hsum
  letI : IsMarkovKernel κ := finiteGoalMassKernel_markov μ mass hmass hnonneg hsum
  unfold finiteGoalActionGeneratedJoint
  infer_instance

/-- The X marginal of the generated joint is the original input law. -/
theorem finiteGoalActionGeneratedJoint_fst
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [Nonempty G]
    (μ : Measure X) [SFinite μ] (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (action : X → G → Y) (haction : ∀ g, Measurable (fun x => action x g)) :
    (finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction).map
      Prod.fst = μ := by
  let κ := finiteGoalMassKernel μ mass hmass hnonneg hsum
  letI : IsMarkovKernel κ := finiteGoalMassKernel_markov μ mass hmass hnonneg hsum
  have hAct : Measurable (fun z : X × G => action z.1 z.2) := by
    apply measurable_from_prod_countable_left
    exact haction
  have hmap : Measurable (fun z : X × G => (z.1, (z.2, action z.1 z.2))) :=
    measurable_fst.prodMk (measurable_snd.prodMk hAct)
  unfold finiteGoalActionGeneratedJoint
  rw [Measure.map_map (by fun_prop) hmap]
  have hcomp : Prod.fst.comp
      (fun z : X × G => (z.1, (z.2, action z.1 z.2))) =
      fun z : X × G => z.1 := rfl
  simp only [hcomp]
  exact Measure.fst_compProd μ κ

/-- The generated joint's (X,G) marginal is exactly the input comp-product
law, before the deterministic action is attached. -/
theorem finiteGoalActionGeneratedJoint_goalMarginal
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [Nonempty G]
    (μ : Measure X) (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (action : X → G → Y) (haction : ∀ g, Measurable (fun x => action x g)) :
    (finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction).map
      (fun z => (z.1, z.2.1)) =
        μ ⊗ₘ finiteGoalMassKernel μ mass hmass hnonneg hsum := by
  let κ := finiteGoalMassKernel μ mass hmass hnonneg hsum
  letI : IsMarkovKernel κ := finiteGoalMassKernel_markov μ mass hmass hnonneg hsum
  have hAct : Measurable (fun z : X × G => action z.1 z.2) := by
    apply measurable_from_prod_countable_left
    exact haction
  have hmap : Measurable (fun z : X × G => (z.1, (z.2, action z.1 z.2))) :=
    measurable_fst.prodMk (measurable_snd.prodMk hAct)
  unfold finiteGoalActionGeneratedJoint
  rw [Measure.map_map (by fun_prop) hmap]
  have hcomp : (fun z : X × (G × Y) => (z.1, z.2.1)).comp
      (fun z : X × G => (z.1, (z.2, action z.1 z.2))) =
        fun z : X × G => z := rfl
  rw [hcomp]
  change Measure.map id (μ ⊗ₘ κ) = μ ⊗ₘ κ
  rw [Measure.map_id]

/-- 有限離散ゴールの確率核を、実数値の条件付き確率ベクトルとして読む。 -/
noncomputable def finiteKernelGoalMass
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    (κ : Kernel Z G) (z : Z) (g : G) : ℝ := (κ z {g}).toReal

/-- 確率核の有限ゴール質量は非負で、総和は1。文脈Zの有限性は使わない。 -/
theorem finiteKernelGoalMass_probability
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ : Kernel Z G) [IsMarkovKernel κ] (z : Z) :
    (∀ g, 0 ≤ finiteKernelGoalMass κ z g) ∧
      ∑ g : G, finiteKernelGoalMass κ z g = 1 := by
  constructor
  · intro g
    exact ENNReal.toReal_nonneg
  · simpa [finiteKernelGoalMass, measureReal_def] using
      (sum_measureReal_singleton (μ := κ z) Finset.univ)

/-- 有限ゴール確率核のエントロピー密度。任意の可測文脈上で定義する。 -/
noncomputable def finiteKernelGoalEntropyAt
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    (κ : Kernel Z G) (z : Z) : ℝ :=
  Tomabechi.Theorem21.conditionalGoalEntropyAt (finiteKernelGoalMass κ z)

/-- 有限離散ゴール核のエントロピー密度は可測。 -/
theorem finiteKernelGoalEntropyAt_measurable
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ : Kernel Z G) :
    Measurable (finiteKernelGoalEntropyAt κ) := by
  unfold finiteKernelGoalEntropyAt Tomabechi.Theorem21.conditionalGoalEntropyAt
  apply Finset.measurable_fun_sum
  intro g _
  exact Tomabechi.Theorem21.measurable_finiteConditionalEntropyTerm_one.comp
    ((Kernel.measurable_coe κ (measurableSet_singleton g)).ennreal_toReal)

/-- 有限離散ゴール核のエントロピー密度は非負かつcard G以下。
上界は可積分性用の粗い評価であり、鋭いlog(card G)評価を主張しない。 -/
theorem finiteKernelGoalEntropyAt_bounds
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ : Kernel Z G) [IsMarkovKernel κ] (z : Z) :
    0 ≤ finiteKernelGoalEntropyAt κ z ∧
      ‖finiteKernelGoalEntropyAt κ z‖ ≤ (Fintype.card G : ℝ) := by
  obtain ⟨hnonneg, hsum⟩ := finiteKernelGoalMass_probability κ z
  constructor
  · unfold finiteKernelGoalEntropyAt Tomabechi.Theorem21.conditionalGoalEntropyAt
    apply Finset.sum_nonneg
    intro g _
    apply Tomabechi.Theorem21.finiteConditionalEntropyTerm_nonneg_of_le
      _ _ (hnonneg g)
    rw [← hsum]
    exact Finset.single_le_sum (fun g _ => hnonneg g) (Finset.mem_univ g)
  · exact Tomabechi.Theorem21.conditionalGoalEntropyAt_norm_le_card
      _ hnonneg hsum

/-- エントロピー密度の可積分性は有限ゴールと有限文脈測度だけから従う。
事後核にも適用でき、事後エントロピーの可積分性を別仮定にしない。 -/
theorem finiteKernelGoalEntropyAt_integrable
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ : Kernel Z G) [IsMarkovKernel κ]
    (μ : Measure Z) [IsFiniteMeasure μ] :
    Integrable (finiteKernelGoalEntropyAt κ) μ := by
  exact (integrable_const (Fintype.card G : ℝ)).mono'
    (finiteKernelGoalEntropyAt_measurable κ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => (finiteKernelGoalEntropyAt_bounds κ z).2)

/-- 条件付きゴールの自己情報量-log p。p=0の点ではReal.log 0=0だが、
核による積分ではその点の質量も0なのでエントロピーの零質量規約と整合する。 -/
noncomputable def finiteKernelGoalSurprisal
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    (κ : Kernel Z G) (z : Z) (g : G) : ℝ :=
  -Real.log (finiteKernelGoalMass κ z g)

/-- 有限ゴール核の自己情報量は積空間Z×G上でも可測。 -/
theorem finiteKernelGoalSurprisal_measurable
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ : Kernel Z G) :
    Measurable (fun z : Z × G => finiteKernelGoalSurprisal κ z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro g
  exact ((Kernel.measurable_coe κ (measurableSet_singleton g)).ennreal_toReal).log.neg

theorem finiteKernelGoalSurprisal_nonneg
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ : Kernel Z G) [IsMarkovKernel κ]
    (z : Z) (g : G) : 0 ≤ finiteKernelGoalSurprisal κ z g := by
  obtain ⟨hnonneg, hsum⟩ := finiteKernelGoalMass_probability κ z
  have hle : finiteKernelGoalMass κ z g ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun g _ => hnonneg g) (Finset.mem_univ g)
  exact neg_nonneg.mpr (Real.log_nonpos (hnonneg g) hle)

/-- 有限ゴール核の自己情報量の期待値は、有限和で定義したエントロピーと一致。 -/
theorem finiteKernelGoalSurprisal_integral
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ : Kernel Z G) [IsMarkovKernel κ] (z : Z) :
    ∫ g, finiteKernelGoalSurprisal κ z g ∂κ z = finiteKernelGoalEntropyAt κ z := by
  rw [integral_fintype Integrable.of_finite]
  unfold finiteKernelGoalEntropyAt Tomabechi.Theorem21.conditionalGoalEntropyAt
  apply Finset.sum_congr rfl
  intro g _
  change finiteKernelGoalMass κ z g * -Real.log (finiteKernelGoalMass κ z g) = _
  by_cases hzero : finiteKernelGoalMass κ z g = 0
  · simp [Tomabechi.Theorem21.finiteConditionalEntropyTerm, hzero]
  · simp [Tomabechi.Theorem21.finiteConditionalEntropyTerm, hzero]

/-- 自己情報量は個別点では無界でも、正しい合成確率法則の下では可積分。
有限ゴールのエントロピー密度評価で証明し、log pの可積分性を追加仮定にしない。 -/
theorem finiteKernelGoalSurprisal_integrable
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ : Kernel Z G) [IsMarkovKernel κ]
    (μ : Measure Z) [IsFiniteMeasure μ] :
    Integrable (fun z : Z × G => finiteKernelGoalSurprisal κ z.1 z.2) (μ ⊗ₘ κ) := by
  apply (Measure.integrable_compProd_iff
    (finiteKernelGoalSurprisal_measurable κ).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun _ => Integrable.of_finite
  · convert finiteKernelGoalEntropyAt_integrable κ μ using 1
    ext z
    calc
      ∫ g, ‖finiteKernelGoalSurprisal κ z g‖ ∂κ z =
          ∫ g, finiteKernelGoalSurprisal κ z g ∂κ z := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun g => Real.norm_of_nonneg
          (finiteKernelGoalSurprisal_nonneg κ z g)
      _ = finiteKernelGoalEntropyAt κ z := finiteKernelGoalSurprisal_integral κ z

/-- 合成法則上で自己情報量を積分すると、文脈ごとのエントロピー密度の積分になる。 -/
theorem finiteKernelGoalSurprisal_integral_compProd
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ : Kernel Z G) [IsMarkovKernel κ]
    (μ : Measure Z) [IsFiniteMeasure μ] :
    ∫ z : Z × G, finiteKernelGoalSurprisal κ z.1 z.2 ∂(μ ⊗ₘ κ) =
      ∫ z, finiteKernelGoalEntropyAt κ z ∂μ := by
  rw [Measure.integral_compProd (finiteKernelGoalSurprisal_integrable κ μ)]
  simp_rw [finiteKernelGoalSurprisal_integral]

/-- 有限離散ゴール上の核のRN微分は、正の参照質量を持つ点では確率質量比。
絶対連続性がある核対に限る。零参照質量の点を除く条件は後のa.e.補題で処理する。 -/
theorem finiteKernel_rnDeriv_eq_ratio
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ η : Kernel Z G)
    [IsMarkovKernel κ] [IsMarkovKernel η] (z : Z)
    (hac : κ z ≪ η z) (g : G) (hη : η z {g} ≠ 0) :
    κ.rnDeriv η z g = κ z {g} / η z {g} := by
  have hmass := Kernel.setLIntegral_rnDeriv hac (measurableSet_singleton g)
  simp only [Measure.restrict_singleton, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul] at hmass
  apply (ENNReal.eq_div_iff hη (measure_ne_top _ _)).mpr
  simpa only [mul_comm] using hmass

/-- 核の対数尤度比は、κ-ほとんど至る所で参照自己情報量と事後自己情報量の差。
零質量点をκに関するa.e.で処理するので、全ゴールの確率正値を仮定しない。 -/
theorem finiteKernel_log_rnDeriv_eq_surprisal_sub
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ η : Kernel Z G)
    [IsMarkovKernel κ] [IsMarkovKernel η] (z : Z) (hac : κ z ≪ η z) :
    ∀ᵐ g ∂κ z, Real.log (κ.rnDeriv η z g).toReal =
      finiteKernelGoalSurprisal η z g - finiteKernelGoalSurprisal κ z g := by
  apply ae_iff_of_countable.mpr
  intro g hκ
  have hη : η z {g} ≠ 0 := fun hzero => hκ (hac hzero)
  have hκreal : (κ z {g}).toReal ≠ 0 :=
    (ENNReal.toReal_pos hκ (measure_ne_top _ _)).ne'
  have hηreal : (η z {g}).toReal ≠ 0 :=
    (ENNReal.toReal_pos hη (measure_ne_top _ _)).ne'
  rw [finiteKernel_rnDeriv_eq_ratio κ η z hac g hη,
    ENNReal.toReal_div, Real.log_div hκreal hηreal]
  unfold finiteKernelGoalSurprisal finiteKernelGoalMass
  ring

/-- 確率核κの自己情報量は非負なので、対数尤度比は参照自己情報量以下。
CMI上界の積分証明で用いる点ごとの評価。 -/
theorem finiteKernel_log_rnDeriv_le_surprisal
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ η : Kernel Z G)
    [IsMarkovKernel κ] [IsMarkovKernel η] (z : Z) (hac : κ z ≪ η z) :
    ∀ᵐ g ∂κ z, Real.log (κ.rnDeriv η z g).toReal ≤
      finiteKernelGoalSurprisal η z g := by
  filter_upwards [finiteKernel_log_rnDeriv_eq_surprisal_sub κ η z hac] with g hg
  rw [hg]
  exact sub_le_self _ (finiteKernelGoalSurprisal_nonneg κ z g)

/-- 同じ文脈周辺を共有する有限ゴール核対では、合成法則の対数尤度比が
核ごとの自己情報量差と一致する。絶対連続性を核のa.e.条件へ分解して使う。 -/
theorem finiteKernelCompProd_llr_eq_surprisal_sub
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ η : Kernel Z G)
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    ∀ᵐ z : Z × G ∂(μ ⊗ₘ κ), llr (μ ⊗ₘ κ) (μ ⊗ₘ η) z =
      finiteKernelGoalSurprisal η z.1 z.2 - finiteKernelGoalSurprisal κ z.1 z.2 := by
  have hkernel := Measure.absolutelyContinuous_compProd_right_iff.mp hac
  have hlog : ∀ᵐ z : Z × G ∂(μ ⊗ₘ κ), Real.log (κ.rnDeriv η z.1 z.2).toReal =
      finiteKernelGoalSurprisal η z.1 z.2 - finiteKernelGoalSurprisal κ z.1 z.2 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun (Kernel.measurable_rnDeriv κ η).ennreal_toReal.log
        ((finiteKernelGoalSurprisal_measurable η).sub
          (finiteKernelGoalSurprisal_measurable κ)))
    exact hkernel.mono fun z hz => finiteKernel_log_rnDeriv_eq_surprisal_sub κ η z hz
  filter_upwards [hac.ae_le (rnDeriv_measure_compProd_right μ κ η), hlog]
    with z hrn hlogz
  simpa only [llr, hrn] using hlogz

/-- 有限ゴール核対のKLは参照自己情報量の期待値から事後エントロピーを引いたもの。
参照自己情報量の可積分性はこの汎用補題では明示するが、CMIでは周辺整合性から供給する。 -/
theorem finiteKernelCompProd_kl_eq_cross_entropy_sub
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (κ η : Kernel Z G)
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η)
    (hcross : Integrable (fun z : Z × G => finiteKernelGoalSurprisal η z.1 z.2)
      (μ ⊗ₘ κ)) :
    (InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal =
      (∫ z : Z × G, finiteKernelGoalSurprisal η z.1 z.2 ∂(μ ⊗ₘ κ)) -
        ∫ z, finiteKernelGoalEntropyAt κ z ∂μ := by
  have hself := finiteKernelGoalSurprisal_integrable κ μ
  have heq := finiteKernelCompProd_llr_eq_surprisal_sub κ η μ hac
  have hint : Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ) :=
    (hcross.sub hself).congr (by
      filter_upwards [heq] with z hz
      exact hz.symm)
  rw [InformationTheory.toReal_klDiv hac hint]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_congr_ae heq, integral_sub hcross hself,
    finiteKernelGoalSurprisal_integral_compProd]

/-- 可測同型による法則の配置変更はKLを保存する。データ処理不等式を両向きに使う。 -/
theorem klDiv_map_measurableEquiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (e : A ≃ᵐ B) (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv (μ.map e) (ν.map e) = InformationTheory.klDiv μ ν := by
  apply le_antisymm (InformationTheory.klDiv_map_le μ ν e.measurable)
  have h := InformationTheory.klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self, Measure.map_id] using h

/-- 同時法則を(X,Y)×Gの順に並べる。有限ゴールの事後核を構成するための配置。 -/
noncomputable def actionGoalJoint
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (law : ConditionalMutualInformationLaw X G Y) : Measure ((X × Y) × G) :=
  law.joint.map (fun z => ((z.1, z.2.2), z.2.1))

theorem actionGoalJoint_isProbabilityMeasure
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (law : ConditionalMutualInformationLaw X G Y) :
    IsProbabilityMeasure (actionGoalJoint law) := by
  letI := law.joint_isProbabilityMeasure
  unfold actionGoalJoint
  infer_instance

/-- 並べ替えた同時法則の第一周辺は、元の(X,Y)周辺と一致する。 -/
theorem actionGoalJoint_fst
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (law : ConditionalMutualInformationLaw X G Y) :
    (actionGoalJoint law).fst = law.input ⊗ₘ law.actionGivenInput := by
  rw [Measure.fst, actionGoalJoint, Measure.map_map (by fun_prop) (by fun_prop)]
  exact law.jointActionMarginal

/-- 配置変更後にも(X,G)周辺は元の条件付きゴール法則に一致する。 -/
theorem actionGoalJoint_goalMarginal
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (law : ConditionalMutualInformationLaw X G Y) :
    (actionGoalJoint law).map (fun z => (z.1.1, z.2)) =
      law.input ⊗ₘ law.goalGivenInput := by
  rw [actionGoalJoint, Measure.map_map (by fun_prop) (by fun_prop)]
  exact law.jointGoalMarginal

/-- X×(G×Y)と(X×Y)×Gの間の可測同型。 -/
def actionGoalReorder
    (X G Y : Type*) [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y] :
    X × (G × Y) ≃ᵐ (X × Y) × G :=
  ((MeasurableEquiv.refl X).prodCongr (MeasurableEquiv.prodComm : G × Y ≃ᵐ Y × G)).trans
    MeasurableEquiv.prodAssoc.symm

/-- CMIを(X,Y)×G順の同時/参照法則で計算しても値は変わらない。 -/
theorem actionGoalJoint_kl_eq
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (law : ConditionalMutualInformationLaw X G Y) :
    InformationTheory.klDiv (actionGoalJoint law)
      (law.referenceMeasure.map (fun z => ((z.1, z.2.2), z.2.1))) =
        InformationTheory.klDiv law.joint law.referenceMeasure := by
  letI := law.joint_isProbabilityMeasure
  letI := law.referenceMeasure_isProbabilityMeasure
  exact klDiv_map_measurableEquiv (actionGoalReorder X G Y) _ _

/-- 行為を観測した文脈(X,Y)上でも、参照ゴール核はXだけに依存する。
この核と行為周辺の合成がCMIの独立参照測度になる。 -/
noncomputable def priorGoalKernelOnAction
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (law : ConditionalMutualInformationLaw X G Y) : Kernel (X × Y) G :=
  law.goalGivenInput.comap Prod.fst measurable_fst

theorem priorGoalKernelOnAction_markov
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (law : ConditionalMutualInformationLaw X G Y) :
    IsMarkovKernel (priorGoalKernelOnAction law) := by
  letI := law.goalKernelMarkov
  unfold priorGoalKernelOnAction
  infer_instance

/-- CMI参照法則を(X,Y)×G順に並べると、行為周辺とXだけに依存する
事前ゴール核の合成になる。これにより事後核との尤度比を同じ文脈上で比較する。 -/
theorem referenceActionGoalJoint_eq
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (law : ConditionalMutualInformationLaw X G Y) :
    law.referenceMeasure.map (fun z => ((z.1, z.2.2), z.2.1)) =
      (law.input ⊗ₘ law.actionGivenInput) ⊗ₘ priorGoalKernelOnAction law := by
  letI := law.inputProbability
  letI := law.goalKernelMarkov
  letI := law.actionKernelMarkov
  letI := priorGoalKernelOnAction_markov law
  have hprod : law.actionGivenInput ×ₖ law.goalGivenInput =
      law.actionGivenInput ⊗ₖ priorGoalKernelOnAction law := by
    ext x s hs
    rw [Kernel.prod_apply, Kernel.compProd_apply hs, Measure.prod_apply hs]
    rfl
  change (law.input ⊗ₘ (law.goalGivenInput ×ₖ law.actionGivenInput)).map
    (fun z => ((z.1, z.2.2), z.2.1)) = _
  calc
    _ = ((law.input ⊗ₘ (law.goalGivenInput ×ₖ law.actionGivenInput)).map
        (Prod.map id Prod.swap)).map
          (MeasurableEquiv.prodAssoc.symm : X × (Y × G) → (X × Y) × G) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (law.input ⊗ₘ ((law.goalGivenInput ×ₖ law.actionGivenInput).map
        Prod.swap)).map MeasurableEquiv.prodAssoc.symm := by
      rw [Measure.compProd_map measurable_swap]
    _ = (law.input ⊗ₘ (law.actionGivenInput ×ₖ law.goalGivenInput)).map
        MeasurableEquiv.prodAssoc.symm := by rw [Kernel.map_prod_swap]
    _ = (law.input ⊗ₘ law.actionGivenInput) ⊗ₘ priorGoalKernelOnAction law := by
      rw [hprod, Measure.compProd_assoc]

/-- 確率同時法則がある以上、ゴール型は非空。事後核の非空性条件はここから供給する。 -/
theorem cmiGoal_nonempty
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (law : ConditionalMutualInformationLaw X G Y) : Nonempty G := by
  letI := law.joint_isProbabilityMeasure
  obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure law.joint
  exact ⟨z.2.1⟩

/-- 有限離散ゴールの事後核G|(X,Y)。X/Yの可算生成性・有限性を要求しない。
同時法則の並べ替えをdisintegrateし、元のlawに事後核フィールドを追加せず構成する。 -/
noncomputable def posteriorGoalKernel
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) : Kernel (X × Y) G := by
  letI := cmiGoal_nonempty law
  letI := actionGoalJoint_isProbabilityMeasure law
  exact (actionGoalJoint law).condKernel

theorem posteriorGoalKernel_markov
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) :
    IsMarkovKernel (posteriorGoalKernel law) := by
  letI := cmiGoal_nonempty law
  letI := actionGoalJoint_isProbabilityMeasure law
  unfold posteriorGoalKernel
  infer_instance

/-- 事後核と行為周辺から元の同時法則を正確に復元する。 -/
theorem posteriorGoalKernel_disintegrates
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) :
    (law.input ⊗ₘ law.actionGivenInput) ⊗ₘ posteriorGoalKernel law =
      actionGoalJoint law := by
  letI := cmiGoal_nonempty law
  letI := actionGoalJoint_isProbabilityMeasure law
  rw [← actionGoalJoint_fst law]
  exact Measure.disintegrate (actionGoalJoint law) (actionGoalJoint law).condKernel

/-- 事後条件付きエントロピーH(G|X,Y)。有限ゴールだけで積分は有限になる。 -/
noncomputable def posteriorGoalEntropy
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) : ℝ :=
  ∫ z, finiteKernelGoalEntropyAt (posteriorGoalKernel law) z
    ∂(law.input ⊗ₘ law.actionGivenInput)

/-- 事後エントロピーは非負。CMI=H(G|X)-H(G|X,Y)の上界証明で用いる。 -/
theorem posteriorGoalEntropy_nonneg
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) :
    0 ≤ posteriorGoalEntropy law := by
  letI := posteriorGoalKernel_markov law
  exact integral_nonneg fun z => (finiteKernelGoalEntropyAt_bounds
    (posteriorGoalKernel law) z).1

/-- 事後エントロピーの積分対象は、有限ゴールと同時法則だけから可積分。
入力・出力空間の有限性や事後核の可積分性を独立に仮定しない。 -/
theorem posteriorGoalEntropy_integrable
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) :
    Integrable (finiteKernelGoalEntropyAt (posteriorGoalKernel law))
      (law.input ⊗ₘ law.actionGivenInput) := by
  letI := law.inputProbability
  letI := law.actionKernelMarkov
  letI := posteriorGoalKernel_markov law
  exact finiteKernelGoalEntropyAt_integrable _ _

/-- 事後エントロピーは有限ゴール数で一様に抑えられる。
これはH(G|X,Y)の有限性の確認であり、CMIの上界そのものは別途証明する。 -/
theorem posteriorGoalEntropy_le_card
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) :
    posteriorGoalEntropy law ≤ (Fintype.card G : ℝ) := by
  letI := law.inputProbability
  letI := law.actionKernelMarkov
  letI := posteriorGoalKernel_markov law
  calc
    posteriorGoalEntropy law ≤ ∫ _z, (Fintype.card G : ℝ)
        ∂(law.input ⊗ₘ law.actionGivenInput) := by
      apply integral_mono (posteriorGoalEntropy_integrable law) (integrable_const _)
      intro z
      exact (le_abs_self _).trans (by
        simpa [Real.norm_eq_abs] using
          (finiteKernelGoalEntropyAt_bounds (posteriorGoalKernel law) z).2)
    _ = (Fintype.card G : ℝ) := by simp

/-- lawから読んだH(G|X)。有限ゴール核のエントロピー密度を入力周辺で積分する。 -/
noncomputable def inputGoalEntropy
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] (law : ConditionalMutualInformationLaw X G Y) : ℝ :=
  ∫ x, finiteKernelGoalEntropyAt law.goalGivenInput x ∂law.input

/-- 事前自己情報量は同時法則の下でも可積分。これは(X,G)周辺整合性から導き、
行為を条件づけた核に対してlog pの可積分性を別に要求しない。 -/
theorem priorGoalSurprisal_integrable_actionGoalJoint
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) :
    Integrable (fun z : (X × Y) × G =>
      finiteKernelGoalSurprisal (priorGoalKernelOnAction law) z.1 z.2)
        (actionGoalJoint law) := by
  letI := law.inputProbability
  letI := law.goalKernelMarkov
  have hint := finiteKernelGoalSurprisal_integrable law.goalGivenInput law.input
  rw [← actionGoalJoint_goalMarginal law] at hint
  exact hint.comp_aemeasurable (by fun_prop)

/-- 同時法則上で事前自己情報量を積分するとH(G|X)になる。
行為分布が確率的であっても、ゴール周辺が保たれていることだけを使う。 -/
theorem priorGoalSurprisal_integral_actionGoalJoint
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) :
    (∫ z : (X × Y) × G,
      finiteKernelGoalSurprisal (priorGoalKernelOnAction law) z.1 z.2
        ∂actionGoalJoint law) = inputGoalEntropy law := by
  letI := law.inputProbability
  letI := law.goalKernelMarkov
  have h := finiteKernelGoalSurprisal_integral_compProd law.goalGivenInput law.input
  rw [← actionGoalJoint_goalMarginal law, integral_map (by fun_prop)
    (finiteKernelGoalSurprisal_measurable law.goalGivenInput).aestronglyMeasurable] at h
  exact h

/-- 一般可測X/Y・有限離散GのCMIについて、KL定義とエントロピー差の等式。
事後核、事後エントロピー、両自己情報量の可積分性をlawから構成する。
上界やエントロピー差そのものを入力に置かない。 -/
theorem finite_measure_cmi_eq_entropy_sub_posterior
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : FiniteConditionalMutualInformationLaw X G Y) :
    (InformationTheory.klDiv law.distribution.joint
      law.distribution.referenceMeasure).toReal =
        inputGoalEntropy law.distribution - posteriorGoalEntropy law.distribution := by
  let D := law.distribution
  letI := D.inputProbability
  letI := D.actionKernelMarkov
  letI := posteriorGoalKernel_markov D
  letI := priorGoalKernelOnAction_markov D
  have hac := (InformationTheory.klDiv_ne_top_iff.mp law.finite).1.map
    (by fun_prop : Measurable (fun z : X × (G × Y) => ((z.1, z.2.2), z.2.1)))
  change actionGoalJoint D ≪
    D.referenceMeasure.map (fun z => ((z.1, z.2.2), z.2.1)) at hac
  rw [← posteriorGoalKernel_disintegrates D, referenceActionGoalJoint_eq D] at hac
  have hcross := priorGoalSurprisal_integrable_actionGoalJoint D
  rw [← posteriorGoalKernel_disintegrates D] at hcross
  have heq := finiteKernelCompProd_kl_eq_cross_entropy_sub
    (posteriorGoalKernel D) (priorGoalKernelOnAction D)
    (D.input ⊗ₘ D.actionGivenInput) hac hcross
  rw [posteriorGoalKernel_disintegrates D, ← referenceActionGoalJoint_eq D,
    actionGoalJoint_kl_eq D, priorGoalSurprisal_integral_actionGoalJoint D] at heq
  exact heq

/-- 原文19で使うI(G;Y|X)≤H(G|X)を一般可測X/Y・有限離散Gで証明。
非負な事後エントロピーを上の等式から落とす。 -/
theorem finite_measure_cmi_le_inputGoalEntropy
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : FiniteConditionalMutualInformationLaw X G Y) :
    finiteKLDivergenceScore law.toFiniteKLLaw ≤ inputGoalEntropy law.distribution := by
  change (InformationTheory.klDiv law.distribution.joint
    law.distribution.referenceMeasure).toReal ≤ _
  rw [finite_measure_cmi_eq_entropy_sub_posterior law]
  exact sub_le_self _ (posteriorGoalEntropy_nonneg law.distribution)

/-- 零条件付きエントロピーならCMIも零。上界は直前の一般測度証明から供給する。 -/
theorem finite_measure_cmi_score_eq_zero_of_inputGoalEntropy_zero
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : FiniteConditionalMutualInformationLaw X G Y)
    (hzero : inputGoalEntropy law.distribution = 0) :
    finiteKLDivergenceScore law.toFiniteKLLaw = 0 := by
  apply le_antisymm
  · simpa only [hzero] using finite_measure_cmi_le_inputGoalEntropy law
  · exact ENNReal.toReal_nonneg

/-- 可測なゴール復元写像があるなら、事後核はその写像のDirac核とa.e.一致する。
復元は同時法則の下でa.e.でよく、全入力や零質量点での一致を要求しない。 -/
theorem posteriorGoalKernel_eq_deterministic_of_recovery
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y)
    (recover : X × Y → G) (hmeas : Measurable recover)
    (hrecovers : ∀ᵐ z ∂law.joint, recover (z.1, z.2.2) = z.2.1) :
    posteriorGoalKernel law =ᵐ[law.input ⊗ₘ law.actionGivenInput]
      Kernel.deterministic recover hmeas := by
  letI := law.inputProbability
  letI := law.actionKernelMarkov
  letI := posteriorGoalKernel_markov law
  have hjoint : actionGoalJoint law =
      (law.input ⊗ₘ law.actionGivenInput).map (fun z => (z, recover z)) := by
    rw [← law.jointActionMarginal, Measure.map_map (by fun_prop) (by fun_prop)]
    apply Measure.map_congr
    filter_upwards [hrecovers] with z hz
    exact Prod.ext rfl hz.symm
  apply Kernel.ae_eq_of_compProd_eq
  rw [posteriorGoalKernel_disintegrates, Measure.compProd_deterministic, hjoint]

/-- 決定論的Diracゴール核のエントロピーは各文脈で零。 -/
theorem finiteKernelGoalEntropyAt_deterministic
    {Z G : Type*} [MeasurableSpace Z] [MeasurableSpace G] [Fintype G]
    [MeasurableSingletonClass G] (recover : Z → G) (hmeas : Measurable recover)
    (z : Z) : finiteKernelGoalEntropyAt (Kernel.deterministic recover hmeas) z = 0 := by
  unfold finiteKernelGoalEntropyAt Tomabechi.Theorem21.conditionalGoalEntropyAt
  apply Finset.sum_eq_zero
  intro g _
  by_cases hg : recover z = g
  · simp [finiteKernelGoalMass, Kernel.deterministic_apply, Measure.dirac_apply',
      hg, Tomabechi.Theorem21.finiteConditionalEntropyTerm]
  · simp [finiteKernelGoalMass, Kernel.deterministic_apply, Measure.dirac_apply',
      hg, Tomabechi.Theorem21.finiteConditionalEntropyTerm]

/-- 可測なゴール復元がa.e.可能ならH(G|X,Y)=0。
事後核の点ごとの指定やエントロピー零そのものは入力しない。 -/
theorem posteriorGoalEntropy_eq_zero_of_recovery
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y)
    (recover : X × Y → G) (hmeas : Measurable recover)
    (hrecovers : ∀ᵐ z ∂law.joint, recover (z.1, z.2.2) = z.2.1) :
    posteriorGoalEntropy law = 0 := by
  unfold posteriorGoalEntropy
  calc
    _ = ∫ z, finiteKernelGoalEntropyAt (Kernel.deterministic recover hmeas) z
        ∂(law.input ⊗ₘ law.actionGivenInput) := by
      apply integral_congr_ae
      filter_upwards [posteriorGoalKernel_eq_deterministic_of_recovery
        law recover hmeas hrecovers] with z hz
      exact congrArg (fun μ : Measure G =>
        Tomabechi.Theorem21.conditionalGoalEntropyAt (fun g => (μ {g}).toReal)) hz
    _ = 0 := by simp only [finiteKernelGoalEntropyAt_deterministic, integral_zero]

/-- 可測ゴール復元がある法則のKL型CMIはH(G|X)を達成する。
有限KL証明はlawに保持し、復元から事後エントロピー零を内部導出する。 -/
theorem finite_measure_cmi_eq_inputGoalEntropy_of_recovery
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : FiniteConditionalMutualInformationLaw X G Y)
    (recover : X × Y → G) (hmeas : Measurable recover)
    (hrecovers : ∀ᵐ z ∂law.distribution.joint, recover (z.1, z.2.2) = z.2.1) :
    finiteKLDivergenceScore law.toFiniteKLLaw = inputGoalEntropy law.distribution := by
  change (InformationTheory.klDiv law.distribution.joint
    law.distribution.referenceMeasure).toReal = _
  rw [finite_measure_cmi_eq_entropy_sub_posterior law,
    posteriorGoalEntropy_eq_zero_of_recovery law.distribution recover hmeas hrecovers,
    sub_zero]

/-- 有限ゴールを自然数添字で列挙する。範囲外では任意の既定ゴールを返す。
復号器の存在・可測性に使う内部構成であり、利用者に列挙を入力させない。 -/
noncomputable def finiteGoalAtIndex
    (G : Type*) [Fintype G] [Nonempty G] (n : ℕ) : G := by
  classical
  exact if hn : n < Fintype.card G then (Fintype.equivFin G).symm ⟨n, hn⟩
    else Classical.choice (inferInstance : Nonempty G)

theorem finiteGoalAtIndex_equivFin
    {G : Type*} [Fintype G] [Nonempty G] (g : G) :
    finiteGoalAtIndex G ((Fintype.equivFin G) g).val = g := by
  simp [finiteGoalAtIndex, ((Fintype.equivFin G) g).isLt]

/-- 出力がどのゴールにも一致しない場合にも、有限ゴール数の添字を番兵として
使うことで、復号器の探索が全(X,Y)上で定義できる。 -/
theorem finiteGoalDecoder_choice_exists
    {X G Y : Type*} [Fintype G] [Nonempty G]
    (action : X × G → Y) (z : X × Y) :
    ∃ n, action (z.1, finiteGoalAtIndex G n) = z.2 ∨ n = Fintype.card G :=
  ⟨Fintype.card G, Or.inr rfl⟩

/-- 有限ゴール方策の復号器。一致する最初のゴールを選び、非像点では既定ゴール。
単射性はこの定義自体には不要であり、左逆性の証明で使う。 -/
noncomputable def finiteGoalDecoder
    {X G Y : Type*} [Fintype G] [Nonempty G]
    (action : X × G → Y) (z : X × Y) : G := by
  classical
  exact finiteGoalAtIndex G (Nat.find (finiteGoalDecoder_choice_exists action z))

/-- 有限ゴール復号器の可測性に必要な方策ごとの一致集合だけを仮定する。
出力空間全体のMeasurableEqを要求しない十分条件。 -/
theorem finiteGoalDecoder_measurable_of_action_graphs
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [Nonempty G]
    (action : X × G → Y)
    (hgraphs : ∀ g, MeasurableSet {z : X × Y | action (z.1, g) = z.2}) :
    Measurable (finiteGoalDecoder action) := by
  classical
  unfold finiteGoalDecoder
  apply Measurable.find (f := fun n (_ : X × Y) => finiteGoalAtIndex G n)
    (p := fun n (z : X × Y) => action (z.1, finiteGoalAtIndex G n) = z.2 ∨ n = Fintype.card G)
    (fun _ => measurable_const)
  intro n
  by_cases hn : n = Fintype.card G
  · simp [hn]
  · simpa only [hn, or_false] using hgraphs (finiteGoalAtIndex G n)

/-- 可測な方策と出力の等値可測性から復号器の可測性を導く。
MeasurableEq Yは標準Borel出力・通常のユークリッド出力で満たされる十分条件。
一般可測Yで単射性だけからこの条件を黙って補わない。 -/
theorem finiteGoalDecoder_measurable
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [Nonempty G] [MeasurableEq Y]
    (action : X × G → Y) (hmeas : Measurable action) :
    Measurable (finiteGoalDecoder action) := by
  apply finiteGoalDecoder_measurable_of_action_graphs
  intro g
  exact measurableSet_eq_fun
    (hmeas.comp (measurable_fst.prodMk measurable_const)) measurable_snd

/-- ゴールに関する単射性が成立する入力xでは、復号器は方策の左逆になる。 -/
theorem finiteGoalDecoder_leftInverse
    {X G Y : Type*} [Fintype G] [Nonempty G]
    (action : X × G → Y) (x : X)
    (hinjective : Function.Injective (fun g => action (x, g))) (g : G) :
    finiteGoalDecoder action (x, action (x, g)) = g := by
  classical
  let hexists := finiteGoalDecoder_choice_exists action (x, action (x, g))
  have hwitness : action (x, finiteGoalAtIndex G ((Fintype.equivFin G) g).val) =
      action (x, g) ∨ ((Fintype.equivFin G) g).val = Fintype.card G := by
    exact Or.inl (by rw [finiteGoalAtIndex_equivFin])
  have hlt : Nat.find hexists < Fintype.card G :=
    lt_of_le_of_lt (Nat.find_min' hexists hwitness) ((Fintype.equivFin G) g).isLt
  apply hinjective
  exact (Nat.find_spec hexists).resolve_right hlt.ne

/-- The same decoder is a left inverse on a sampled goal if every goal with
the same action value must equal that positive-mass goal. This only requires
injectivity on the realized support, not on zero-mass goals among themselves. -/
theorem finiteGoalDecoder_leftInverse_of_supported
    {X G Y : Type*} [Fintype G] [Nonempty G]
    (action : X × G → Y) (x : X) (g : G)
    (hinjective : ∀ g', action (x, g') = action (x, g) → g' = g) :
    finiteGoalDecoder action (x, action (x, g)) = g := by
  classical
  let hexists := finiteGoalDecoder_choice_exists action (x, action (x, g))
  have hwitness : action (x, finiteGoalAtIndex G ((Fintype.equivFin G) g).val) =
      action (x, g) ∨ ((Fintype.equivFin G) g).val = Fintype.card G := by
    exact Or.inl (by rw [finiteGoalAtIndex_equivFin])
  have hlt : Nat.find hexists < Fintype.card G :=
    lt_of_le_of_lt (Nat.find_min' hexists hwitness) ((Fintype.equivFin G) g).isLt
  apply hinjective
  exact (Nat.find_spec hexists).resolve_right hlt.ne

/-- 同時法則の文脈周辺はlawの入力法則と一致する。 -/
theorem cmiJoint_inputMarginal
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (law : ConditionalMutualInformationLaw X G Y) :
    law.joint.map Prod.fst = law.input := by
  letI := law.inputProbability
  letI := law.goalKernelMarkov
  have h := congrArg Measure.fst law.jointGoalMarginal
  rw [Measure.fst_compProd] at h
  change (law.joint.map (fun z => (z.1, z.2.1))).map Prod.fst = law.input at h
  rw [Measure.map_map measurable_fst
    (by fun_prop : Measurable (fun z : X × (G × Y) => (z.1, z.2.1)))] at h
  exact h

/-- 有限ゴール・可測な決定論的方策・入力a.e.の単射性からKL型CMIの情報達成。
復号器と事後エントロピー零を内部構成する。出力の等値可測性は明示した十分条件で、
X/Yの有限性や全入力での単射性、正のゴールエントロピーは要求しない。 -/
theorem finite_measure_cmi_eq_inputGoalEntropy_of_injective_deterministic_action
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [MeasurableEq Y]
    (law : FiniteConditionalMutualInformationLaw X G Y)
    (action : X × G → Y) (hmeas : Measurable action)
    (hdeterministic : ∀ᵐ z ∂law.distribution.joint, z.2.2 = action (z.1, z.2.1))
    (hinjective : ∀ᵐ x ∂law.distribution.input,
      Function.Injective (fun g => action (x, g))) :
    finiteKLDivergenceScore law.toFiniteKLLaw = inputGoalEntropy law.distribution := by
  letI := cmiGoal_nonempty law.distribution
  have hinjectiveJoint : ∀ᵐ z ∂law.distribution.joint,
      Function.Injective (fun g => action (z.1, g)) := by
    apply ae_of_ae_map (p := fun x => Function.Injective (fun g => action (x, g)))
      (by fun_prop : AEMeasurable Prod.fst law.distribution.joint)
    simpa only [cmiJoint_inputMarginal] using hinjective
  apply finite_measure_cmi_eq_inputGoalEntropy_of_recovery law
    (finiteGoalDecoder action) (finiteGoalDecoder_measurable action hmeas)
  filter_upwards [hinjectiveJoint, hdeterministic] with z hi hd
  rw [hd]
  exact finiteGoalDecoder_leftInverse action z.1 hi z.2.1

/-- 決定論的方策が生成する同時法則から情報達成へ渡す入口。
Y=φ(X,G)は元の(X,G)法則の可測写像として表し、同時法則上のa.e.等式を内部導出する。
出力の等値可測性は直前の復号器入口と同じ明示十分条件。 -/
theorem finite_measure_cmi_eq_inputGoalEntropy_of_injective_deterministic_joint
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [MeasurableEq Y]
    (law : FiniteConditionalMutualInformationLaw X G Y)
    (action : X × G → Y) (hmeas : Measurable action)
    (hjoint : law.distribution.joint =
      (law.distribution.input ⊗ₘ law.distribution.goalGivenInput).map
        (fun z => (z.1, z.2, action z)))
    (hinjective : ∀ᵐ x ∂law.distribution.input,
      Function.Injective (fun g => action (x, g))) :
    finiteKLDivergenceScore law.toFiniteKLLaw = inputGoalEntropy law.distribution := by
  apply finite_measure_cmi_eq_inputGoalEntropy_of_injective_deterministic_action
    law action hmeas _ hinjective
  rw [hjoint]
  apply (ae_map_iff (by fun_prop)
    (measurableSet_eq_fun measurable_snd.snd
      (hmeas.comp (measurable_fst.prodMk measurable_snd.fst)))).mpr
  exact Filter.Eventually.of_forall fun _ => rfl


/-- 同時確率測度からCMI lawを構成する十分条件版。
有限離散ゴールと標準Borel出力なら二つの条件付き周辺核が存在し、文脈Xには
標準Borel性・可算生成性を要求しない。一般可測Yについての無条件構成ではない。
ここではKL有限性をまだ証明せず、条件付き法則の構成だけを行う。 -/
noncomputable def cmiLawOfJoint
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [StandardBorelSpace Y]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] :
    ConditionalMutualInformationLaw X G Y := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  letI : Nonempty Y := ⟨z.2.2⟩
  let input := joint.map Prod.fst
  let goalPair := joint.map (fun z => (z.1, z.2.1))
  let actionPair := joint.map (fun z => (z.1, z.2.2))
  letI : IsProbabilityMeasure goalPair := inferInstance
  letI : IsProbabilityMeasure actionPair := inferInstance
  have hgoalFst : goalPair.fst = input := by
    rw [Measure.fst, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hactionFst : actionPair.fst = input := by
    rw [Measure.fst, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  exact {
    input := input
    inputProbability := inferInstance
    goalGivenInput := goalPair.condKernel
    goalKernelMarkov := inferInstance
    actionGivenInput := actionPair.condKernel
    actionKernelMarkov := inferInstance
    joint := joint
    jointGoalMarginal := by
      rw [← hgoalFst]
      exact (Measure.disintegrate goalPair goalPair.condKernel).symm
    jointActionMarginal := by
      rw [← hactionFst]
      exact (Measure.disintegrate actionPair actionPair.condKernel).symm }

/-- 任意可測出力の同時法則を `(X,Y)×G` に並べ替える。
出力条件付き核 `Y|X` の存在を要求しない直接CMI入口。 -/
noncomputable def directActionGoalJoint
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (joint : Measure (X × (G × Y))) : Measure ((X × Y) × G) :=
  joint.map (fun z => ((z.1, z.2.2), z.2.1))

/-- 有限ゴールの事前核だけをdisintegrateする。Yの標準Borel性は不要。 -/
noncomputable def directPriorGoalKernel
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] : Kernel X G := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  exact (joint.map (fun z => (z.1, z.2.1))).condKernel

/-- 直接事前核は確率核。非空性を外部の追加条件にしない。 -/
theorem directPriorGoalKernel_markov
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] :
    IsMarkovKernel (directPriorGoalKernel joint) := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  unfold directPriorGoalKernel
  infer_instance

/-- 入力周辺と直接事前核から元の(X,G)周辺を復元する。
これは直接CMIの事前エントロピーを原文H(G|X)へ同定するための整合条件。 -/
theorem directPriorGoalKernel_disintegrates
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] :
    joint.map Prod.fst ⊗ₘ directPriorGoalKernel joint =
      joint.map (fun z => (z.1, z.2.1)) := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  let goalPair := joint.map (fun z => (z.1, z.2.1))
  have hfst : goalPair.fst = joint.map Prod.fst := by
    rw [Measure.fst, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [← hfst]
  unfold directPriorGoalKernel
  exact Measure.disintegrate goalPair goalPair.condKernel

/-- The direct prior kernel obtained by disintegrating the generated joint is
almost everywhere the very same finite kernel used to generate it. -/
theorem finiteGoalActionGeneratedJoint_priorKernel_ae_eq
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [Nonempty G]
    (μ : Measure X) [IsProbabilityMeasure μ] (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (action : X → G → Y) (haction : ∀ g, Measurable (fun x => action x g))
    [IsProbabilityMeasure
      (finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction)] :
    directPriorGoalKernel
      (finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction) =ᵐ[μ]
        finiteGoalMassKernel μ mass hmass hnonneg hsum := by
  let κ := finiteGoalMassKernel μ mass hmass hnonneg hsum
  let J := finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction
  letI : IsMarkovKernel κ := finiteGoalMassKernel_markov μ mass hmass hnonneg hsum
  letI : IsProbabilityMeasure J := finiteGoalActionGeneratedJoint_isProbability
    μ mass hmass hnonneg hsum action haction
  letI : IsMarkovKernel (directPriorGoalKernel J) := directPriorGoalKernel_markov J
  apply Kernel.ae_eq_of_compProd_eq
  have hfst := finiteGoalActionGeneratedJoint_fst μ mass hmass hnonneg hsum action haction
  have hleft := congrArg (fun ν : Measure X =>
      ν ⊗ₘ directPriorGoalKernel J) hfst
  calc
    μ ⊗ₘ directPriorGoalKernel J = J.map Prod.fst ⊗ₘ directPriorGoalKernel J := hleft.symm
    _ = J.map (fun z => (z.1, z.2.1)) := directPriorGoalKernel_disintegrates J
    _ = μ ⊗ₘ κ := by
      rw [finiteGoalActionGeneratedJoint_goalMarginal μ mass hmass hnonneg hsum action haction]

/-- The direct conditional entropy of the generated joint is the original
conditional entropy computed from the supplied mass function. -/
theorem finiteGoalActionGeneratedJoint_directPriorEntropy_eq
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [Nonempty G]
    (μ : Measure X) [IsProbabilityMeasure μ] (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (action : X → G → Y) (haction : ∀ g, Measurable (fun x => action x g))
    [IsProbabilityMeasure
      (finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction)] :
    ∫ x, finiteKernelGoalEntropyAt
        (directPriorGoalKernel
          (finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction)) x
        ∂(finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction).map Prod.fst =
      Tomabechi.Theorem21.conditionalGoalEntropy μ mass := by
  let J := finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction
  have hprior := finiteGoalActionGeneratedJoint_priorKernel_ae_eq
    μ mass hmass hnonneg hsum action haction
  have hkernelMass : ∀ g, (fun x => finiteKernelGoalMass
      (directPriorGoalKernel J) x g) =ᵐ[μ] (fun x => mass x g) := by
    intro g
    filter_upwards [hprior, finiteGoalMassKernel_mass_ae_eq
      μ mass hmass hnonneg hsum g] with x hq hm
    change (directPriorGoalKernel J x {g}).toReal = mass x g
    rw [hq]
    exact hm
  have hcoords : ∀ᵐ x ∂μ, ∀ g,
      finiteKernelGoalMass (directPriorGoalKernel J) x g = mass x g :=
    ae_all_iff.mpr hkernelMass
  have hentropy : (fun x => finiteKernelGoalEntropyAt
      (directPriorGoalKernel J) x) =ᵐ[μ]
        (fun x => Tomabechi.Theorem21.conditionalGoalEntropyAt (mass x)) := by
    filter_upwards [hcoords] with x hx
    simp only [finiteKernelGoalEntropyAt,
      Tomabechi.Theorem21.conditionalGoalEntropyAt]
    apply Finset.sum_congr rfl
    intro g _
    change Tomabechi.Theorem21.finiteConditionalEntropyTerm
      ((directPriorGoalKernel J x {g}).toReal) 1 =
      Tomabechi.Theorem21.finiteConditionalEntropyTerm (mass x g) 1
    have hx' : (directPriorGoalKernel J x {g}).toReal = mass x g := hx g
    rw [hx']
  rw [finiteGoalActionGeneratedJoint_fst μ mass hmass hnonneg hsum action haction]
  calc
    _ = ∫ x, Tomabechi.Theorem21.conditionalGoalEntropyAt (mass x) ∂μ :=
      MeasureTheory.integral_congr_ae hentropy
    _ = Tomabechi.Theorem21.conditionalGoalEntropy μ mass := rfl

/-- Under the joint law, the prior probability of the realized finite goal is
positive almost everywhere. This is the support fact needed to prove
absolute continuity against the conditional-independence reference law. -/
theorem directPriorGoalKernel_mass_pos_ae
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] :
    ∀ᵐ z ∂joint.map (fun z => (z.1, z.2.1)),
      directPriorGoalKernel joint z.1 {z.2} ≠ 0 := by
  let q := directPriorGoalKernel joint
  letI : IsMarkovKernel q := by
    simpa [q] using directPriorGoalKernel_markov joint
  let input := joint.map Prod.fst
  let mass : X × G → ENNReal := fun z => q z.1 {z.2}
  have hmass : Measurable mass := by
    apply measurable_from_prod_countable_left
    intro g
    change Measurable (fun x : X => q x {g})
    exact Kernel.measurable_coe q (measurableSet_singleton g)
  have hnotzero : MeasurableSet {z : X × G | mass z ≠ 0} := by
    convert (hmass (measurableSet_singleton (0 : ENNReal))).compl using 1
    ext z
    simp [mass]
  have hpos : ∀ᵐ z ∂(input ⊗ₘ q), mass z ≠ 0 := by
    apply (Measure.ae_compProd_iff hnotzero).2
    filter_upwards [] with x
    apply ae_iff_of_countable.mpr
    intro g hg
    exact hg
  have hpos' := hpos
  dsimp [input, q] at hpos'
  rw [directPriorGoalKernel_disintegrates joint] at hpos'
  simpa [q, mass, input] using hpos'

/-- 並べ替えた法則の第一周辺は元の(X,Y)周辺。
行為条件付き核の選択に依存しない。 -/
theorem directActionGoalJoint_fst
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (joint : Measure (X × (G × Y))) :
    (directActionGoalJoint joint).fst = joint.map (fun z => (z.1, z.2.2)) := by
  unfold directActionGoalJoint
  rw [Measure.fst, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- 条件付き独立の参照法則を行為周辺から直接構成する。
定義だけではKL有限性やエントロピー上界を主張しない。 -/
noncomputable def directCMIReference
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] :
    Measure ((X × Y) × G) :=
  (directActionGoalJoint joint).fst ⊗ₘ
    (directPriorGoalKernel joint).comap Prod.fst measurable_fst

/-- 直接参照法則は確率測度。任意可測Yのまま構成できる。 -/
theorem directCMIReference_isProbabilityMeasure
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] :
    IsProbabilityMeasure (directCMIReference joint) := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  unfold directCMIReference directPriorGoalKernel directActionGoalJoint
  infer_instance

/-- 任意可測出力に対する有限ゴール事後核。非空性は同時確率法則から得る。 -/
noncomputable def directPosteriorGoalKernel
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] : Kernel (X × Y) G := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  letI : IsProbabilityMeasure (directActionGoalJoint joint) := by
    unfold directActionGoalJoint
    infer_instance
  exact (directActionGoalJoint joint).condKernel

/-- 有限ゴール事後核による同時法則の復元。行為条件付き核は不要。 -/
theorem directActionGoalJoint_disintegrates
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] :
    (directActionGoalJoint joint).fst ⊗ₘ
      directPosteriorGoalKernel joint = directActionGoalJoint joint := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  letI : IsProbabilityMeasure (directActionGoalJoint joint) := by
    unfold directActionGoalJoint
    infer_instance
  unfold directPosteriorGoalKernel
  exact Measure.disintegrate _ _

/-- 直接配置から(X,G)周辺へ戻すと、元のゴール周辺になる。 -/
theorem directActionGoalJoint_goalMarginal
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (joint : Measure (X × (G × Y))) :
    (directActionGoalJoint joint).map (fun z => (z.1.1, z.2)) =
      joint.map (fun z => (z.1, z.2.1)) := by
  unfold directActionGoalJoint
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- 直接配置の事前自己情報量は可積分。出力核の存在を使わない。 -/
theorem directPriorSurprisal_integrable
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] :
    Integrable (fun z : (X × Y) × G =>
      finiteKernelGoalSurprisal (directPriorGoalKernel joint) z.1.1 z.2)
      (directActionGoalJoint joint) := by
  letI := directPriorGoalKernel_markov joint
  have hint := finiteKernelGoalSurprisal_integrable
    (directPriorGoalKernel joint) (joint.map Prod.fst)
  rw [directPriorGoalKernel_disintegrates,
    ← directActionGoalJoint_goalMarginal joint] at hint
  exact hint.comp_aemeasurable (by fun_prop)

/-- 直接配置で積分した事前自己情報量は原文のH(G|X)。 -/
theorem directPriorSurprisal_integral
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] :
    (∫ z : (X × Y) × G,
      finiteKernelGoalSurprisal (directPriorGoalKernel joint) z.1.1 z.2
      ∂directActionGoalJoint joint) =
    ∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel joint) x ∂joint.map Prod.fst := by
  letI := directPriorGoalKernel_markov joint
  have h := finiteKernelGoalSurprisal_integral_compProd
    (directPriorGoalKernel joint) (joint.map Prod.fst)
  rw [directPriorGoalKernel_disintegrates,
    ← directActionGoalJoint_goalMarginal joint, integral_map (by fun_prop)
    (finiteKernelGoalSurprisal_measurable (directPriorGoalKernel joint)).aestronglyMeasurable] at h
  exact h

/-- 任意可測出力の直接CMIについてエントロピー差を導く。
絶対連続性は明示入力で、有限KL仮定から供給できる。 -/
theorem directCMI_eq_entropy_sub_posterior
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (hac : directActionGoalJoint joint ≪ directCMIReference joint) :
    (InformationTheory.klDiv (directActionGoalJoint joint) (directCMIReference joint)).toReal =
      (∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel joint) x ∂joint.map Prod.fst) -
      ∫ z, finiteKernelGoalEntropyAt (directPosteriorGoalKernel joint) z
        ∂(directActionGoalJoint joint).fst := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  letI : IsProbabilityMeasure (directActionGoalJoint joint) := by
    unfold directActionGoalJoint
    infer_instance
  letI := directPriorGoalKernel_markov joint
  letI : IsMarkovKernel (directPosteriorGoalKernel joint) := by
    unfold directPosteriorGoalKernel
    infer_instance
  have hcross := directPriorSurprisal_integrable joint
  rw [← directActionGoalJoint_disintegrates joint] at hcross
  have hac' : (directActionGoalJoint joint).fst ⊗ₘ directPosteriorGoalKernel joint ≪
      (directActionGoalJoint joint).fst ⊗ₘ
        (directPriorGoalKernel joint).comap Prod.fst measurable_fst := by
    rw [directActionGoalJoint_disintegrates]
    exact hac
  have h := finiteKernelCompProd_kl_eq_cross_entropy_sub
    (directPosteriorGoalKernel joint)
    ((directPriorGoalKernel joint).comap Prod.fst measurable_fst)
    (directActionGoalJoint joint).fst hac' hcross
  rw [directActionGoalJoint_disintegrates] at h
  change (InformationTheory.klDiv (directActionGoalJoint joint) (directCMIReference joint)).toReal =
    (∫ z : (X × Y) × G, finiteKernelGoalSurprisal (directPriorGoalKernel joint)
      z.1.1 z.2 ∂directActionGoalJoint joint) -
    ∫ z, finiteKernelGoalEntropyAt (directPosteriorGoalKernel joint) z
      ∂(directActionGoalJoint joint).fst at h
  rw [directPriorSurprisal_integral] at h
  exact h

/-- Absolute continuity of a direct CMI pair is enough to make its KL finite:
the prior goal surprisal is integrable for every finite goal space, and the
posterior surprisal is integrable by the same bound. This isolates the actual
remaining issue for a generated law: proving absolute continuity from the
model data. -/
theorem directCMI_ne_top_of_ac
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (hac : directActionGoalJoint joint ≪ directCMIReference joint) :
    InformationTheory.klDiv (directActionGoalJoint joint)
      (directCMIReference joint) ≠ ⊤ := by
  letI : IsProbabilityMeasure (directActionGoalJoint joint) := by
    unfold directActionGoalJoint
    infer_instance
  letI := directPriorGoalKernel_markov joint
  letI : IsMarkovKernel (directPosteriorGoalKernel joint) := by
    unfold directPosteriorGoalKernel
    infer_instance
  let μ := (directActionGoalJoint joint).fst
  let κ := directPosteriorGoalKernel joint
  let η : Kernel (X × Y) G :=
    (directPriorGoalKernel joint).comap Prod.fst measurable_fst
  have hμκ : μ ⊗ₘ κ = directActionGoalJoint joint := by
    dsimp [μ, κ]
    exact directActionGoalJoint_disintegrates joint
  have hμη : μ ⊗ₘ η = directCMIReference joint := by
    rfl
  have hac' : μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
    rw [hμκ, hμη]
    exact hac
  have hcross : Integrable (fun z : (X × Y) × G =>
      finiteKernelGoalSurprisal η z.1 z.2) (μ ⊗ₘ κ) := by
    rw [hμκ]
    convert directPriorSurprisal_integrable joint using 1
    ext z
    rfl
  have hself : Integrable (fun z : (X × Y) × G =>
      finiteKernelGoalSurprisal κ z.1 z.2) (μ ⊗ₘ κ) :=
    finiteKernelGoalSurprisal_integrable κ μ
  have heq := finiteKernelCompProd_llr_eq_surprisal_sub κ η μ hac'
  have hllr : Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ) :=
    (hcross.sub hself).congr (by
      filter_upwards [heq] with z hz
      exact hz.symm)
  have hfinite := InformationTheory.klDiv_ne_top hac' hllr
  rw [hμκ, hμη] at hfinite
  exact hfinite

/-- 有限KLという原文容量条件から絶対連続性を得て、直接CMIをH(G|X)で抑える。
X/Yへの標準Borel条件やY|X核は要求しない。 -/
theorem directCMI_le_inputGoalEntropy_of_finite
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (hfinite : InformationTheory.klDiv (directActionGoalJoint joint)
      (directCMIReference joint) ≠ ⊤) :
    (InformationTheory.klDiv (directActionGoalJoint joint) (directCMIReference joint)).toReal ≤
      ∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel joint) x ∂joint.map Prod.fst := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  letI : IsProbabilityMeasure (directActionGoalJoint joint) := by
    unfold directActionGoalJoint
    infer_instance
  letI := directCMIReference_isProbabilityMeasure joint
  letI : IsMarkovKernel (directPosteriorGoalKernel joint) := by
    unfold directPosteriorGoalKernel
    infer_instance
  rw [directCMI_eq_entropy_sub_posterior joint
    (InformationTheory.klDiv_ne_top_iff.mp hfinite).1]
  exact sub_le_self _ (integral_nonneg fun z =>
    (finiteKernelGoalEntropyAt_bounds (directPosteriorGoalKernel joint) z).1)

/-- 既存lawと直接入口の事前核は入力a.e.で一致する。
同時法則の(X,G)周辺整合だけで導き、核の点ごとの同一性は要求しない。 -/
theorem directPriorGoalKernel_eq_existing
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) :
    letI := law.joint_isProbabilityMeasure
    directPriorGoalKernel law.joint =ᵐ[law.input] law.goalGivenInput := by
  letI := law.joint_isProbabilityMeasure
  letI := law.inputProbability
  letI := law.goalKernelMarkov
  letI := directPriorGoalKernel_markov law.joint
  apply Kernel.ae_eq_of_compProd_eq
  rw [← cmiJoint_inputMarginal law, directPriorGoalKernel_disintegrates,
    cmiJoint_inputMarginal law]
  exact law.jointGoalMarginal

/-- 直接参照法則は既存law参照法則の配置変更と一致する。
任意可測Yで成り立ち、出力条件付き核は既存lawの同定にだけ使う。 -/
theorem directCMIReference_eq_existing
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) :
    letI := law.joint_isProbabilityMeasure
    directCMIReference law.joint =
      law.referenceMeasure.map (fun z => ((z.1, z.2.2), z.2.1)) := by
  letI := law.joint_isProbabilityMeasure
  letI := law.inputProbability
  letI := law.actionKernelMarkov
  letI := law.goalKernelMarkov
  letI := directPriorGoalKernel_markov law.joint
  letI := priorGoalKernelOnAction_markov law
  rw [directCMIReference, directActionGoalJoint_fst, law.jointActionMarginal,
    referenceActionGoalJoint_eq]
  apply Measure.compProd_congr
  have h := directPriorGoalKernel_eq_existing law
  have hf := ae_of_ae_map (by fun_prop : AEMeasurable Prod.fst
    (law.input ⊗ₘ law.actionGivenInput))
    (p := fun x => directPriorGoalKernel law.joint x = law.goalGivenInput x)
  rw [← Measure.fst, Measure.fst_compProd] at hf
  exact hf h

/-- 直接CMIと既存lawのKL評価は拡張実数として一致する。
有限性仮定を要求せず、実数化前の値を保存する。 -/
theorem directCMI_kl_eq_existing
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (law : ConditionalMutualInformationLaw X G Y) :
    letI := law.joint_isProbabilityMeasure
    InformationTheory.klDiv (directActionGoalJoint law.joint)
      (directCMIReference law.joint) =
      InformationTheory.klDiv law.joint law.referenceMeasure := by
  letI := law.joint_isProbabilityMeasure
  rw [directCMIReference_eq_existing]
  exact actionGoalJoint_kl_eq law

/-- 直接CMIの可測復号器は事後核をDirac核にする。Y|X核は不要。 -/
theorem directPosteriorGoalKernel_eq_deterministic_of_recovery
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (recover : X × Y → G) (hmeas : Measurable recover)
    (hrecovers : ∀ᵐ z ∂joint, recover (z.1, z.2.2) = z.2.1) :
    directPosteriorGoalKernel joint =ᵐ[(directActionGoalJoint joint).fst]
      Kernel.deterministic recover hmeas := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  letI : IsProbabilityMeasure (directActionGoalJoint joint) := by
    unfold directActionGoalJoint
    infer_instance
  letI : IsMarkovKernel (directPosteriorGoalKernel joint) := by
    unfold directPosteriorGoalKernel
    infer_instance
  have hjoint : directActionGoalJoint joint =
      (directActionGoalJoint joint).fst.map (fun z => (z, recover z)) := by
    rw [directActionGoalJoint_fst, Measure.map_map (by fun_prop) (by fun_prop)]
    apply Measure.map_congr
    filter_upwards [hrecovers] with z hz
    exact Prod.ext rfl hz.symm
  apply Kernel.ae_eq_of_compProd_eq
  rw [directActionGoalJoint_disintegrates, Measure.compProd_deterministic]
  exact hjoint

/-- A measurable recovery map makes the generated direct CMI law absolutely
continuous with respect to its conditional-independence reference law whenever
the realized prior goal mass is positive. -/
theorem directCMI_absolutelyContinuous_of_recovery
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (recover : X × Y → G) (hmeas : Measurable recover)
    (hrecovers : ∀ᵐ z ∂joint, recover (z.1, z.2.2) = z.2.1) :
    directActionGoalJoint joint ≪ directCMIReference joint := by
  letI : IsProbabilityMeasure (directActionGoalJoint joint) := by
    unfold directActionGoalJoint
    infer_instance
  letI := directPriorGoalKernel_markov joint
  letI : IsMarkovKernel (directPosteriorGoalKernel joint) := by
    unfold directPosteriorGoalKernel
    infer_instance
  have hprior : ∀ᵐ z ∂joint, directPriorGoalKernel joint z.1 {z.2.1} ≠ 0 :=
    ae_of_ae_map (by fun_prop : AEMeasurable (fun z : X × (G × Y) =>
      (z.1, z.2.1)) joint) (directPriorGoalKernel_mass_pos_ae joint)
  have hmeasPrior : Measurable
      (fun z : (X × Y) × G => directPriorGoalKernel joint z.1.1 {z.2}) := by
    apply measurable_from_prod_countable_left
    intro g
    change Measurable (fun z : X × Y => directPriorGoalKernel joint z.1 {g})
    exact (Kernel.measurable_coe (directPriorGoalKernel joint)
      (measurableSet_singleton g)).comp measurable_fst
  have hpriorSet : MeasurableSet
      {z : (X × Y) × G | directPriorGoalKernel joint z.1.1 {z.2} ≠ 0} := by
    convert (hmeasPrior (measurableSet_singleton (0 : ENNReal))).compl using 1
    ext z
    simp
  have hpriorJ : ∀ᵐ z ∂directActionGoalJoint joint,
      directPriorGoalKernel joint z.1.1 {z.2} ≠ 0 := by
    change ∀ᵐ z ∂joint.map (fun z : X × (G × Y) => ((z.1, z.2.2), z.2.1)),
      directPriorGoalKernel joint z.1.1 {z.2} ≠ 0
    have := (ae_map_iff (by fun_prop : AEMeasurable
      (fun z : X × (G × Y) => ((z.1, z.2.2), z.2.1)) joint) hpriorSet).2 hprior
    simpa using this
  have hposterior := directPosteriorGoalKernel_eq_deterministic_of_recovery
    joint recover hmeas hrecovers
  let μ := (directActionGoalJoint joint).fst
  have hdisint : μ ⊗ₘ directPosteriorGoalKernel joint = directActionGoalJoint joint := by
    dsimp [μ]
    exact directActionGoalJoint_disintegrates joint
  change directActionGoalJoint joint ≪ μ ⊗ₘ
    (directPriorGoalKernel joint).comap Prod.fst measurable_fst
  have hpriorComp : ∀ᵐ z ∂μ ⊗ₘ directPosteriorGoalKernel joint,
      directPriorGoalKernel joint z.1.1 {z.2} ≠ 0 := by
    rw [hdisint]
    exact hpriorJ
  have hsections := (Measure.ae_compProd_iff hpriorSet).1 hpriorComp
  have hpriorAtRecovery : ∀ᵐ z ∂μ,
      directPriorGoalKernel joint z.1 {recover z} ≠ 0 := by
    filter_upwards [hsections, hposterior] with z hs hp
    have hsection : ∀ᵐ g ∂directPosteriorGoalKernel joint z,
        directPriorGoalKernel joint z.1 {g} ≠ 0 := hs
    rw [hp] at hsection
    exact (ae_iff_of_countable.mp hsection) (recover z) (by simp [Kernel.deterministic_apply])
  rw [← hdisint]
  apply (Measure.absolutelyContinuous_compProd_right_iff).2
  filter_upwards [hpriorAtRecovery, hposterior] with z hmass hp
  rw [hp]
  intro s hzero
  by_cases hmem : recover z ∈ s
  · have hsubset : ({recover z} : Set G) ⊆ s := Set.singleton_subset_iff.mpr hmem
    have hle : directPriorGoalKernel joint z.1 {recover z} ≤
        directPriorGoalKernel joint z.1 s := measure_mono hsubset
    have hzeroKernel : directPriorGoalKernel joint z.1 s = 0 := by
      simpa [Kernel.comap_apply] using hzero
    have hzero' : directPriorGoalKernel joint z.1 {recover z} = 0 := by
      exact le_antisymm (hle.trans (le_of_eq hzeroKernel)) bot_le
    exact (hmass hzero').elim
  · simp [Kernel.deterministic_apply, Kernel.comap_apply, hmem]

/-- 可測復号器がある有限直接CMIはH(G|X)を達成する。
出力等値可測性は要求せず、可測復元という実際に使う条件を明示する。 -/
theorem directCMI_eq_inputGoalEntropy_of_recovery
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (hfinite : InformationTheory.klDiv (directActionGoalJoint joint)
      (directCMIReference joint) ≠ ⊤)
    (recover : X × Y → G) (hmeas : Measurable recover)
    (hrecovers : ∀ᵐ z ∂joint, recover (z.1, z.2.2) = z.2.1) :
    (InformationTheory.klDiv (directActionGoalJoint joint) (directCMIReference joint)).toReal =
      ∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel joint) x ∂joint.map Prod.fst := by
  letI : IsProbabilityMeasure (directActionGoalJoint joint) := by
    unfold directActionGoalJoint
    infer_instance
  letI := directCMIReference_isProbabilityMeasure joint
  have hzero : (∫ z, finiteKernelGoalEntropyAt (directPosteriorGoalKernel joint) z
      ∂(directActionGoalJoint joint).fst) = 0 := by
    calc
      _ = ∫ z, finiteKernelGoalEntropyAt (Kernel.deterministic recover hmeas) z
          ∂(directActionGoalJoint joint).fst := by
        apply integral_congr_ae
        filter_upwards [directPosteriorGoalKernel_eq_deterministic_of_recovery
          joint recover hmeas hrecovers] with z hz
        exact congrArg (fun μ : Measure G =>
          Tomabechi.Theorem21.conditionalGoalEntropyAt (fun g => (μ {g}).toReal)) hz
      _ = 0 := by simp only [finiteKernelGoalEntropyAt_deterministic, integral_zero]
  rw [directCMI_eq_entropy_sub_posterior joint
    (InformationTheory.klDiv_ne_top_iff.mp hfinite).1, hzero, sub_zero]

/-- A measurable a.e. recovery map alone gives finite KL and exact input-goal
entropy for the direct CMI pair; KL finiteness is proved from the joint law. -/
theorem directCMI_eq_inputGoalEntropy_of_recovery_of_support
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (recover : X × Y → G) (hmeas : Measurable recover)
    (hrecovers : ∀ᵐ z ∂joint, recover (z.1, z.2.2) = z.2.1) :
    (InformationTheory.klDiv (directActionGoalJoint joint)
      (directCMIReference joint)).toReal =
      ∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel joint) x
        ∂joint.map Prod.fst := by
  apply directCMI_eq_inputGoalEntropy_of_recovery joint
    (directCMI_ne_top_of_ac joint
      (directCMI_absolutelyContinuous_of_recovery joint recover hmeas hrecovers))
    recover hmeas hrecovers

/-- 直接同時法則の決定論的単射方策は情報を達成する。
入力a.e.単射性を保持し、可測復号器の構成にはMeasurableEq Yを明示する。 -/
theorem directCMI_eq_inputGoalEntropy_of_injective_deterministic_action
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [MeasurableEq Y]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (hfinite : InformationTheory.klDiv (directActionGoalJoint joint)
      (directCMIReference joint) ≠ ⊤)
    (action : X × G → Y) (hmeas : Measurable action)
    (hdeterministic : ∀ᵐ z ∂joint, z.2.2 = action (z.1, z.2.1))
    (hinjective : ∀ᵐ x ∂joint.map Prod.fst,
      Function.Injective (fun g => action (x, g))) :
    (InformationTheory.klDiv (directActionGoalJoint joint) (directCMIReference joint)).toReal =
      ∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel joint) x ∂joint.map Prod.fst := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  have hi : ∀ᵐ z ∂joint, Function.Injective (fun g => action (z.1, g)) :=
    ae_of_ae_map (by fun_prop : AEMeasurable Prod.fst joint) hinjective
  apply directCMI_eq_inputGoalEntropy_of_recovery joint hfinite
    (finiteGoalDecoder action) (finiteGoalDecoder_measurable action hmeas)
  filter_upwards [hi, hdeterministic] with z hz hd
  rw [hd]
  exact finiteGoalDecoder_leftInverse action z.1 hz z.2.1

/-- A measurable deterministic action that is a.e. injective on the finite
goal alphabet attains the direct CMI entropy without an assumed finite-KL
premise. -/
theorem directCMI_eq_inputGoalEntropy_of_injective_deterministic_action_of_support
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [MeasurableEq Y]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (action : X × G → Y) (hmeas : Measurable action)
    (hdeterministic : ∀ᵐ z ∂joint, z.2.2 = action (z.1, z.2.1))
    (hinjective : ∀ᵐ x ∂joint.map Prod.fst,
      Function.Injective (fun g => action (x, g))) :
    (InformationTheory.klDiv (directActionGoalJoint joint)
      (directCMIReference joint)).toReal =
      ∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel joint) x
        ∂joint.map Prod.fst := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  have hi : ∀ᵐ z ∂joint, Function.Injective (fun g => action (z.1, g)) :=
    ae_of_ae_map (by fun_prop : AEMeasurable Prod.fst joint) hinjective
  apply directCMI_eq_inputGoalEntropy_of_recovery_of_support joint
    (finiteGoalDecoder action) (finiteGoalDecoder_measurable action hmeas)
  filter_upwards [hi, hdeterministic] with z hz hd
  rw [hd]
  exact finiteGoalDecoder_leftInverse action z.1 hz z.2.1

/-- A positive conditional goal entropy forces the finite goal type to be
nonempty (with an empty goal type every finite sum, hence the entropy, is zero). -/
theorem finiteGoal_nonempty_of_conditionalGoalEntropy_pos
    {X G : Type*} [MeasurableSpace X] [Fintype G]
    (μ : Measure X) (mass : X → G → ℝ)
    (hpositive : 0 < Tomabechi.Theorem21.conditionalGoalEntropy μ mass) : Nonempty G := by
  by_contra hG
  letI : IsEmpty G := not_nonempty_iff.mp hG
  have hcard : Fintype.card G = 0 := Fintype.card_eq_zero
  have hzero : Tomabechi.Theorem21.conditionalGoalEntropy μ mass = 0 := by
    simp [Tomabechi.Theorem21.conditionalGoalEntropy,
      Tomabechi.Theorem21.conditionalGoalEntropyAt, hcard]
  linarith

noncomputable def finiteGoalActionGeneratedJoint_directCMIScore
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (μ : Measure X) [IsProbabilityMeasure μ] (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (action : X → G → Y) (haction : ∀ g, Measurable (fun x => action x g))
    (hG : Nonempty G) : ℝ := by
  letI : Nonempty G := hG
  let J := finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction
  letI : IsProbabilityMeasure J := finiteGoalActionGeneratedJoint_isProbability
    μ mass hmass hnonneg hsum action haction
  exact (InformationTheory.klDiv (directActionGoalJoint J)
    (directCMIReference J)).toReal

/-- The deterministic action generated from the same a.e. probability mass
attains the direct KL-type CMI under the original support-injectivity
condition. The joint law, its prior kernel, and its conditional entropy are
all constructed from the same μ/mass/action data. -/
theorem finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [MeasurableEq Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (mass : X → G → ℝ)
    (hmass : ∀ g, AEStronglyMeasurable (fun x => mass x g) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hsum : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (action : X → G → Y) (haction : ∀ g, Measurable (fun x => action x g))
    (hinjective : ∀ᵐ x ∂μ, ∀ g, 0 < mass x g →
      ∀ g', action x g' = action x g → g' = g)
    (hinputEntropyPositive : 0 < Tomabechi.Theorem21.conditionalGoalEntropy μ mass) :
    finiteGoalActionGeneratedJoint_directCMIScore
      μ mass hmass hnonneg hsum action haction
      (finiteGoal_nonempty_of_conditionalGoalEntropy_pos μ mass hinputEntropyPositive) =
        Tomabechi.Theorem21.conditionalGoalEntropy μ mass ∧
      0 < finiteGoalActionGeneratedJoint_directCMIScore
        μ mass hmass hnonneg hsum action haction
        (finiteGoal_nonempty_of_conditionalGoalEntropy_pos μ mass hinputEntropyPositive) := by
  letI : Nonempty G := finiteGoal_nonempty_of_conditionalGoalEntropy_pos μ mass hinputEntropyPositive
  let J := finiteGoalActionGeneratedJoint μ mass hmass hnonneg hsum action haction
  let κ := finiteGoalMassKernel μ mass hmass hnonneg hsum
  let actionPair : X × G → Y := fun z => action z.1 z.2
  have hActionPair : Measurable actionPair := by
    apply measurable_from_prod_countable_left
    exact haction
  letI : IsProbabilityMeasure J := finiteGoalActionGeneratedJoint_isProbability
    μ mass hmass hnonneg hsum action haction
  change (InformationTheory.klDiv (directActionGoalJoint J)
    (directCMIReference J)).toReal =
      Tomabechi.Theorem21.conditionalGoalEntropy μ mass ∧
    0 < (InformationTheory.klDiv (directActionGoalJoint J)
      (directCMIReference J)).toReal
  letI : IsMarkovKernel (directPriorGoalKernel J) := directPriorGoalKernel_markov J
  have hpriorEq := finiteGoalActionGeneratedJoint_priorKernel_ae_eq
    μ mass hmass hnonneg hsum action haction
  change directPriorGoalKernel J =ᵐ[μ] κ at hpriorEq
  have hkernelMass : ∀ᵐ x ∂μ, ∀ g,
      finiteKernelGoalMass (directPriorGoalKernel J) x g = mass x g := by
    apply ae_all_iff.mpr
    intro g
    filter_upwards [hpriorEq, finiteGoalMassKernel_mass_ae_eq
      μ mass hmass hnonneg hsum g] with x hq hm
    change ((directPriorGoalKernel J x {g}).toReal = mass x g)
    rw [hq]
    exact hm
  have hkernelMassJ : ∀ᵐ z ∂J, ∀ g,
      finiteKernelGoalMass (directPriorGoalKernel J) z.1 g = mass z.1 g := by
    have hfst := finiteGoalActionGeneratedJoint_fst μ mass hmass hnonneg hsum action haction
    have hbase : ∀ᵐ x ∂J.map Prod.fst, ∀ g,
        finiteKernelGoalMass (directPriorGoalKernel J) x g = mass x g := by
      exact hfst ▸ hkernelMass
    exact ae_of_ae_map (by fun_prop : AEMeasurable Prod.fst J) hbase
  have hpriorPositive : ∀ᵐ z ∂J,
      directPriorGoalKernel J z.1 {z.2.1} ≠ 0 := by
    exact ae_of_ae_map
      (by fun_prop : AEMeasurable (fun z : X × (G × Y) => (z.1, z.2.1)) J)
      (directPriorGoalKernel_mass_pos_ae J)
  have hsamplePositive : ∀ᵐ z ∂J, 0 < mass z.1 z.2.1 := by
    filter_upwards [hkernelMassJ, hpriorPositive] with z hmassz hpos
    have hposReal := ENNReal.toReal_pos hpos (measure_ne_top _ _)
    rw [← hmassz z.2.1]
    exact hposReal
  have hinjectiveJ : ∀ᵐ z ∂J, ∀ g, 0 < mass z.1 g →
      ∀ g', action z.1 g' = action z.1 g → g' = g := by
    have hfst := finiteGoalActionGeneratedJoint_fst μ mass hmass hnonneg hsum action haction
    have hbase : ∀ᵐ x ∂J.map Prod.fst, ∀ g, 0 < mass x g →
        ∀ g', action x g' = action x g → g' = g := by
      exact hfst ▸ hinjective
    exact ae_of_ae_map (by fun_prop : AEMeasurable Prod.fst J) hbase
  have hrecover : ∀ᵐ z ∂J,
      finiteGoalDecoder actionPair (z.1, z.2.2) = z.2.1 := by
    have hdet : ∀ᵐ z ∂J, z.2.2 = action z.1 z.2.1 := by
      dsimp [J, finiteGoalActionGeneratedJoint]
      have hmap : Measurable (fun z : X × G => (z.1, (z.2, action z.1 z.2))) := by
        apply measurable_fst.prodMk
        exact measurable_snd.prodMk hActionPair
      have hActJoint : Measurable (fun z : X × (G × Y) => action z.1 z.2.1) :=
        hActionPair.comp (measurable_fst.prodMk measurable_snd.fst)
      apply (ae_map_iff hmap.aemeasurable
        (measurableSet_eq_fun measurable_snd.snd hActJoint)).2
      filter_upwards [] with z
      rfl
    filter_upwards [hinjectiveJ, hsamplePositive, hdet] with z hinj hz hdetz
    rw [hdetz]
    simpa [actionPair] using finiteGoalDecoder_leftInverse_of_supported
      actionPair z.1 z.2.1 (fun g' heq => hinj z.2.1 hz g' heq)
  have hscore := directCMI_eq_inputGoalEntropy_of_recovery_of_support J
    (finiteGoalDecoder actionPair) (finiteGoalDecoder_measurable actionPair hActionPair)
    hrecover
  rw [finiteGoalActionGeneratedJoint_directPriorEntropy_eq
    μ mass hmass hnonneg hsum action haction] at hscore
  exact ⟨hscore, by rw [hscore]; exact hinputEntropyPositive⟩

/-- 方策ごとの出力一致集合が可測なら、入力a.e.単射性から直接情報達成。
出力全体の等値可測性より弱い明示十分条件。 -/
theorem directCMI_eq_inputGoalEntropy_of_action_graphs
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (hfinite : InformationTheory.klDiv (directActionGoalJoint joint)
      (directCMIReference joint) ≠ ⊤)
    (action : X × G → Y)
    (hgraphs : ∀ g, MeasurableSet {z : X × Y | action (z.1, g) = z.2})
    (hdeterministic : ∀ᵐ z ∂joint, z.2.2 = action (z.1, z.2.1))
    (hinjective : ∀ᵐ x ∂joint.map Prod.fst,
      Function.Injective (fun g => action (x, g))) :
    (InformationTheory.klDiv (directActionGoalJoint joint) (directCMIReference joint)).toReal =
      ∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel joint) x ∂joint.map Prod.fst := by
  let z := Classical.choice (nonempty_of_isProbabilityMeasure joint)
  letI : Nonempty G := ⟨z.2.1⟩
  have hi : ∀ᵐ z ∂joint, Function.Injective (fun g => action (z.1, g)) :=
    ae_of_ae_map (by fun_prop : AEMeasurable Prod.fst joint) hinjective
  apply directCMI_eq_inputGoalEntropy_of_recovery joint hfinite
    (finiteGoalDecoder action) (finiteGoalDecoder_measurable_of_action_graphs action hgraphs)
  filter_upwards [hi, hdeterministic] with z hz hd
  rw [hd]
  exact finiteGoalDecoder_leftInverse action z.1 hz z.2.1

/-- 生成的な決定論的同時法則を直接CMI情報達成へ接続する。
(X,G)周辺の可測写像として生成条件を受け、Y|X核は要求しない。 -/
theorem directCMI_eq_inputGoalEntropy_of_injective_deterministic_joint
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [MeasurableEq Y]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint]
    (hfinite : InformationTheory.klDiv (directActionGoalJoint joint)
      (directCMIReference joint) ≠ ⊤)
    (action : X × G → Y) (hmeas : Measurable action)
    (hjoint : joint = (joint.map (fun z => (z.1, z.2.1))).map
      (fun z => (z.1, z.2, action z)))
    (hinjective : ∀ᵐ x ∂joint.map Prod.fst,
      Function.Injective (fun g => action (x, g))) :
    (InformationTheory.klDiv (directActionGoalJoint joint) (directCMIReference joint)).toReal =
      ∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel joint) x ∂joint.map Prod.fst := by
  apply directCMI_eq_inputGoalEntropy_of_injective_deterministic_action
    joint hfinite action hmeas _ hinjective
  rw [hjoint]
  apply (ae_map_iff (by fun_prop)
    (measurableSet_eq_fun measurable_snd.snd
      (hmeas.comp (measurable_fst.prodMk measurable_snd.fst)))).mpr
  exact Filter.Eventually.of_forall fun _ => rfl

/-- 同時法則から構成したlawは、与えられた同時法則をそのまま保持する。 -/
theorem cmiLawOfJoint_joint
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [StandardBorelSpace Y]
    (joint : Measure (X × (G × Y))) [IsProbabilityMeasure joint] :
    (cmiLawOfJoint joint).joint = joint := by
  rfl

/-- 標準Borel出力の同時法則が等しければ、構成された独立参照法則も等しい。
構成時に選ばれた条件付き核の点ごとの一致を埋め込み条件として要求しない。 -/
theorem cmiLawOfJoint_reference_eq
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    [Fintype G] [MeasurableSingletonClass G] [StandardBorelSpace Y]
    (joint₁ joint₂ : Measure (X × (G × Y)))
    [IsProbabilityMeasure joint₁] [IsProbabilityMeasure joint₂]
    (hjoint : joint₁ = joint₂) :
    (cmiLawOfJoint joint₁).referenceMeasure =
      (cmiLawOfJoint joint₂).referenceMeasure := by
  apply Tomabechi.Theorem22.ConditionalMutualInformationLaw.referenceMeasure_eq_of_joint_eq
  simpa only [cmiLawOfJoint_joint] using hjoint

end Tomabechi.Theorem19_22
