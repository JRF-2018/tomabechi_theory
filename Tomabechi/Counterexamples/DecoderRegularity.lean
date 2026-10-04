import Tomabechi.Information.MeasureCMI
import Theorem19
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# 定理19：出力σ代数の正則性が必要であることの反例（監査用の証人）

出力の可測空間が二値のゴールを区別できない（自明σ代数）とき、集合として単射で可測な
有限ゴールの符号化でも、可測な左逆（復号器）は存在せず、KL型の条件付き相互情報量は
ゴールのエントロピー `log 2` を達成しない。これは「出力が標準Borel等の正則な空間である」
という仮定を省けないことの数学的証人であり、定理19・22の原文そのものの反例ではない。
-/

open Tomabechi.Theorem22
open MeasureTheory ProbabilityTheory

namespace Tomabechi.Theorem19_22
namespace DecoderRegularityWitness

/-- 出力可測構造の監査用。二値の集合に自明σ代数だけを与える。
認知モデルの具体例ではなく、単射性と可測復元可能性の差を示す数学的証人。 -/
structure IndiscreteBit where
  bit : Bool

instance : MeasurableSpace IndiscreteBit := ⊥

def encode (b : Bool) : IndiscreteBit := ⟨b⟩

theorem encode_injective : Function.Injective encode := by
  intro b c h
  exact congrArg IndiscreteBit.bit h

theorem encode_measurable : Measurable encode := by
  intro s hs
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with hempty | huniv
  · simp [hempty]
  · simp [huniv]

/-- 可測かつ単射の有限ゴール符号化でも、出力σ代数がゴールを区別しないと
可測左逆は存在しない。任意可測Y版から出力の分離性を省けないことの証人。 -/
theorem no_measurable_leftInverse
    (recover : IndiscreteBit → Bool) (hmeas : Measurable recover) :
    ¬Function.LeftInverse recover encode := by
  intro hleft
  have hset := hmeas (measurableSet_singleton true)
  rcases MeasurableSpace.measurableSet_bot_iff.mp hset with hempty | huniv
  · have hmem : encode true ∈ recover ⁻¹' {true} := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hleft true]
    rw [hempty] at hmem
    exact hmem
  · have hmem : encode false ∈ recover ⁻¹' {true} := by
      rw [huniv]
      exact Set.mem_univ _
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, hleft false,
      Bool.false_eq_true] using hmem

/-- 可測単射だけから全ゴールの出力一致集合可測性は導けない。
単一文脈・有限二値ゴールの監査用証人であり、元の全体系の反証ではない。 -/
theorem not_all_action_graphs_measurable :
    ¬∀ g : Bool, MeasurableSet {z : Unit × IndiscreteBit | encode g = z.2} := by
  intro hgraphs
  let action : Unit × Bool → IndiscreteBit := fun z => encode z.2
  let recover : IndiscreteBit → Bool := fun y => finiteGoalDecoder action ((), y)
  have hm : Measurable recover :=
    (finiteGoalDecoder_measurable_of_action_graphs action hgraphs).comp
      (measurable_const.prodMk measurable_id)
  apply no_measurable_leftInverse recover hm
  intro g
  exact finiteGoalDecoder_leftInverse action () encode_injective g

/-- 自明σ代数の異なる符号値はDirac法則として区別できない。 -/
theorem dirac_encode_eq (b c : Bool) :
    Measure.dirac (encode b) = Measure.dirac (encode c) := by
  apply Measure.ext
  intro s hs
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with he | hu
  · simp [he]
  · simp [hu]

/-- ゴールは離散に観測できても、固定ゴールに付随する出力符号値は測度で区別できない。 -/
theorem dirac_goal_encode_eq (g b c : Bool) :
    Measure.dirac (g, encode b) = Measure.dirac (g, encode c) := by
  apply Measure.ext
  intro s hs
  have hsection : MeasurableSet ((fun y : IndiscreteBit => (g, y)) ⁻¹' s) :=
    hs.preimage (measurable_const.prodMk measurable_id)
  have hmem : (g, encode b) ∈ s ↔ (g, encode c) ∈ s := by
    rcases MeasurableSpace.measurableSet_bot_iff.mp hsection with he | hu
    · have hb : encode b ∉ (fun y : IndiscreteBit => (g, y)) ⁻¹' s := by rw [he]; simp
      have hc : encode c ∉ (fun y : IndiscreteBit => (g, y)) ⁻¹' s := by rw [he]; simp
      exact iff_of_false hb hc
    · have hb : encode b ∈ (fun y : IndiscreteBit => (g, y)) ⁻¹' s := by rw [hu]; trivial
      have hc : encode c ∈ (fun y : IndiscreteBit => (g, y)) ⁻¹' s := by rw [hu]; trivial
      exact iff_of_true hb hc
  simp only [Measure.dirac_apply' _ hs]
  by_cases hb : (g, encode b) ∈ s
  · simp [Set.indicator_of_mem hb, Set.indicator_of_mem (hmem.mp hb)]
  · have hc : (g, encode c) ∉ s := fun h => hb (hmem.mpr h)
    simp [Set.indicator_of_notMem hb, Set.indicator_of_notMem hc]

/-- 異なる符号値の出力法則間KLは零。集合上の単射性は法則の識別性を保証しない。 -/
theorem klDiv_dirac_encode_eq_zero (b c : Bool) :
    InformationTheory.klDiv (Measure.dirac (encode b)) (Measure.dirac (encode c)) = 0 := by
  rw [dirac_encode_eq b c]
  exact InformationTheory.klDiv_self _

/-- 等重み二値ゴールの決定論的符号化の同時法則。 -/
noncomputable def binaryEncodedJoint : Measure (Bool × IndiscreteBit) :=
  (2 : ENNReal)⁻¹ • Measure.dirac (false, encode false) +
  (2 : ENNReal)⁻¹ • Measure.dirac (true, encode true)

/-- 同じゴール混合に定数出力を付した法則。 -/
noncomputable def binaryConstantJoint : Measure (Bool × IndiscreteBit) :=
  (2 : ENNReal)⁻¹ • Measure.dirac (false, encode false) +
  (2 : ENNReal)⁻¹ • Measure.dirac (true, encode false)

/-- 単射符号化と定数出力は、この可測出力では同時法則として一致する。 -/
theorem binaryEncodedJoint_eq_constant : binaryEncodedJoint = binaryConstantJoint := by
  unfold binaryEncodedJoint binaryConstantJoint
  rw [dirac_goal_encode_eq true true false]

/-- 二つの同時法則間のKLは零。これはまだCMI参照法則との同定ではない。 -/
theorem binaryEncodedJoint_kl_constant_eq_zero :
    InformationTheory.klDiv binaryEncodedJoint binaryConstantJoint = 0 := by
  letI : IsFiniteMeasure binaryConstantJoint := ⟨by
    norm_num [binaryConstantJoint, Measure.add_apply, Measure.smul_apply]⟩
  rw [binaryEncodedJoint_eq_constant]
  exact InformationTheory.klDiv_self _

/-- 等重みの二値ゴール周辺。 -/
noncomputable def binaryGoalMeasure : Measure Bool :=
  (2 : ENNReal)⁻¹ • Measure.dirac false + (2 : ENNReal)⁻¹ • Measure.dirac true

/-- 符号化同時法則は確率法則。 -/
theorem binaryEncodedJoint_isProbabilityMeasure : IsProbabilityMeasure binaryEncodedJoint := by
  constructor
  norm_num [binaryEncodedJoint, Measure.add_apply, Measure.smul_apply]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- 二値ゴール周辺は確率法則。 -/
theorem binaryGoalMeasure_isProbabilityMeasure : IsProbabilityMeasure binaryGoalMeasure := by
  constructor
  norm_num [binaryGoalMeasure, Measure.add_apply, Measure.smul_apply]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- 定数出力側はゴール周辺と出力Diracの独立積法則。 -/
theorem binaryConstantJoint_eq_product :
    binaryConstantJoint = binaryGoalMeasure.prod (Measure.dirac (encode false)) := by
  rw [Measure.prod_dirac]
  unfold binaryGoalMeasure binaryConstantJoint
  rw [Measure.map_add _ _ (by fun_prop),
    Measure.map_smul _ (by fun_prop), Measure.map_smul _ (by fun_prop)]
  simp [Measure.map_dirac' (by fun_prop : Measurable (fun g : Bool => (g, encode false)))]

/-- 二値ゴールの両質量は1/2。 -/
theorem binaryGoalMeasure_singleton (g : Bool) :
    (binaryGoalMeasure {g}).toReal = (1 / 2 : ℝ) := by
  cases g <;> norm_num [binaryGoalMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply', ENNReal.toReal_inv]

/-- 二値ゴールエントロピーはlog 2。 -/
theorem binaryGoalEntropy_eq_log_two :
    Tomabechi.Theorem21.conditionalGoalEntropyAt
      (fun g => (binaryGoalMeasure {g}).toReal) = Real.log 2 := by
  simp [Tomabechi.Theorem21.conditionalGoalEntropyAt, binaryGoalMeasure_singleton,
    Tomabechi.Theorem21.finiteConditionalEntropyTerm, Real.log_div]
  <;> ring

/-- この監査用ゴールのエントロピーは正。 -/
theorem binaryGoalEntropy_pos :
    0 < Tomabechi.Theorem21.conditionalGoalEntropyAt
      (fun g => (binaryGoalMeasure {g}).toReal) := by
  rw [binaryGoalEntropy_eq_log_two]
  exact Real.log_pos (by norm_num)

/-- 符号化法則は実際の両周辺の積に等しい。 -/
theorem binaryEncodedJoint_eq_marginal_product :
    binaryEncodedJoint = binaryEncodedJoint.fst.prod binaryEncodedJoint.snd := by
  letI := binaryGoalMeasure_isProbabilityMeasure
  have h : binaryEncodedJoint = binaryGoalMeasure.prod (Measure.dirac (encode false)) :=
    binaryEncodedJoint_eq_constant.trans binaryConstantJoint_eq_product
  rw [h]
  simp

/-- 単射符号化の相互情報量を実際の周辺積へのKLで評価すると零。
出力可測構造がゴール差を観測できないため、正ゴールエントロピーを達成しない。 -/
theorem binaryEncodedJoint_mutualInformation_eq_zero :
    InformationTheory.klDiv binaryEncodedJoint
      (binaryEncodedJoint.fst.prod binaryEncodedJoint.snd) = 0 := by
  letI := binaryEncodedJoint_isProbabilityMeasure
  rw [← binaryEncodedJoint_eq_marginal_product]
  exact InformationTheory.klDiv_self _

/-- 一般可測出力の集合論的単射符号化は、KL情報量で正ゴールエントロピーを
達成するとは限らない。文脈条件付きCMIへのUnit埋め込みは別に確認する。 -/
theorem binaryEncodedJoint_information_lt_goalEntropy :
    (InformationTheory.klDiv binaryEncodedJoint
      (binaryEncodedJoint.fst.prod binaryEncodedJoint.snd)).toReal <
      Tomabechi.Theorem21.conditionalGoalEntropyAt
        (fun g => (binaryGoalMeasure {g}).toReal) := by
  rw [binaryEncodedJoint_mutualInformation_eq_zero, ENNReal.toReal_zero]
  exact binaryGoalEntropy_pos

/-- Unit文脈と二値ゴール・定数出力核からCMI lawを明示構成する。
後で単射符号化生成法則との同定に用いる独立法則。 -/
noncomputable def binaryContextLaw : ConditionalMutualInformationLaw Unit Bool IndiscreteBit := by
  letI := binaryGoalMeasure_isProbabilityMeasure
  let goal : Kernel Unit Bool := Kernel.const Unit binaryGoalMeasure
  let output : Kernel Unit IndiscreteBit := Kernel.const Unit (Measure.dirac (encode false))
  exact {
    input := Measure.dirac ()
    inputProbability := inferInstance
    goalGivenInput := goal
    goalKernelMarkov := inferInstance
    actionGivenInput := output
    actionKernelMarkov := inferInstance
    joint := Measure.dirac () ⊗ₘ (goal ×ₖ output)
    jointGoalMarginal := by
      change (Measure.dirac () ⊗ₘ (goal ×ₖ output)).map (Prod.map id Prod.fst) = _
      rw [← Measure.compProd_map measurable_fst]
      congr 1
      rw [← Kernel.fst_eq, Kernel.fst_prod]
    jointActionMarginal := by
      change (Measure.dirac () ⊗ₘ (goal ×ₖ output)).map (Prod.map id Prod.snd) = _
      rw [← Measure.compProd_map measurable_snd]
      congr 1
      rw [← Kernel.snd_eq, Kernel.snd_prod] }

/-- Unit文脈のlawはその条件付き独立参照法則に等しい。 -/
theorem binaryContextLaw_joint_eq_reference :
    binaryContextLaw.joint = binaryContextLaw.referenceMeasure := by
  rfl

/-- 明示CMI lawで計算した条件付き相互情報量は零。 -/
theorem binaryContextLaw_cmi_eq_zero :
    InformationTheory.klDiv binaryContextLaw.joint binaryContextLaw.referenceMeasure = 0 := by
  letI := binaryContextLaw.joint_isProbabilityMeasure
  rw [← binaryContextLaw_joint_eq_reference]
  exact InformationTheory.klDiv_self _

/-- Unit文脈の条件付きゴールエントロピーはlog 2。 -/
theorem binaryContextLaw_inputEntropy_eq_log_two :
    inputGoalEntropy binaryContextLaw = Real.log 2 := by
  change (∫ _ : Unit, Tomabechi.Theorem21.conditionalGoalEntropyAt
    (fun g => (binaryGoalMeasure {g}).toReal) ∂Measure.dirac ()) = Real.log 2
  simpa using binaryGoalEntropy_eq_log_two

/-- 二値ゴール測度を単射encodeで出力へ写すと既存の符号化法則になる。 -/
theorem binaryGoalMeasure_map_encode :
    binaryGoalMeasure.map (fun g => (g, encode g)) = binaryEncodedJoint := by
  unfold binaryGoalMeasure binaryEncodedJoint
  rw [Measure.map_add _ _ (by fun_prop),
    Measure.map_smul _ (by fun_prop), Measure.map_smul _ (by fun_prop)]
  simp [Measure.map_dirac' (by fun_prop : Measurable (fun g : Bool => (g, encode g)))]

/-- 文脈lawのjointは符号化法則へUnitを付けたものと一致する。 -/
theorem binaryContextLaw_joint_eq_encoded :
    binaryContextLaw.joint = binaryEncodedJoint.map (fun z => ((), z)) := by
  letI := binaryGoalMeasure_isProbabilityMeasure
  change (Measure.dirac () ⊗ₘ
    (Kernel.const Unit binaryGoalMeasure ×ₖ Kernel.const Unit (Measure.dirac (encode false)))) = _
  rw [Kernel.prod_const, Measure.compProd_const, Measure.dirac_prod,
    ← binaryConstantJoint_eq_product, ← binaryEncodedJoint_eq_constant]

/-- 文脈lawは可測単射方策encodeが(X,G)周辺から生成する法則。
非可測な決定論的等値事象をa.e.仮定にせず、生成測度の等式を直接確認する。 -/
theorem binaryContextLaw_generated_by_encode :
    binaryContextLaw.joint =
      (binaryContextLaw.input ⊗ₘ binaryContextLaw.goalGivenInput).map
        (fun z => (z.1, z.2, encode z.2)) := by
  letI := binaryGoalMeasure_isProbabilityMeasure
  rw [binaryContextLaw_joint_eq_encoded, ← binaryGoalMeasure_map_encode,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change _ = (Measure.dirac () ⊗ₘ Kernel.const Unit binaryGoalMeasure).map _
  rw [Measure.compProd_const, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- 可測単射生成方策でも、一般可測出力ではCMI情報達成が失敗する。
標準Borel出力を含む通常の正則な出力に対する反例ではない。 -/
theorem binaryContextLaw_cmi_lt_inputEntropy :
    (InformationTheory.klDiv binaryContextLaw.joint binaryContextLaw.referenceMeasure).toReal <
      inputGoalEntropy binaryContextLaw := by
  rw [binaryContextLaw_cmi_eq_zero, ENNReal.toReal_zero,
    binaryContextLaw_inputEntropy_eq_log_two]
  exact Real.log_pos (by norm_num)

end DecoderRegularityWitness

end Tomabechi.Theorem19_22
