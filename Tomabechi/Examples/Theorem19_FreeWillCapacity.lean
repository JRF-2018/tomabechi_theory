import Tomabechi.Information.FiniteCMI
import Tomabechi.Information.MeasureCMI

set_option maxHeartbeats 1000000

/-!
# 定理19の Python 例 (`examples/theorem19_free_will_capacity.py`) の Lean 根拠

有限ゴール `G∈Fin 4`（一様）、文脈 `X=Unit`、決定論的方策 `φ:Fin 4→Fin n`（出力アルファベット
サイズ `n`）。`finiteConditionalMutualInformation`（`I(G;Y|X)=H(G|X)-H(G|X,Y)`、プロジェクト既存の
有限CMI）を使い、自由意思容量 `F(n)=max_φ I` を定義する。

* `H(G|X)=log 4`。
* 上界 `I≤H(G|X)`、単射方策で `I=H`（`theorem21_finite_information_capacity`）、したがって
  `F(4)=log 4`。出力が1個なら `I=0`、`F(1)=0`。
* ゴールと独立な非退化二値確率出力の一般測度CMIは0。2出力・3出力の有限容量は
  4値方策の全分割を列挙して、それぞれ `F(2)=log 2`、`F(3)=(3/2)log 2`。
* 単調性（定理19の評価保存単射）: 出力アルファベットの包含 `Fin n ↪ Fin (n+1)` で `F(n)≤F(n+1)`。
* 端点正規化 `f=(F-F(1))/(F(4)-F(1))` は `f(1)=0`, `f(4)=1`。
* 反例（`Theorem19_Counterexample.lean` の反例モデルの精神）: `y(g)=(0.1,0.4,0.6,0.9)` は集合として単射だが、解像度 `b` の区間分割で観測すると
  `b=1`（自明σ代数）で `I=0<log 4`、`b=2` で `I=log 2`、`b=10` で `I=log 4`。

範囲外: 一般の問題族・可測出力の容量値（`Theorem19_Heterogeneous`, `Theorem19_Counterexample`）。
-/

namespace Tomabechi.Examples.Theorem19

open Tomabechi.Theorem21

/-- 文脈 `Unit` 上のゴール事前（一様 `1/4`）。 -/
noncomputable def mass : Unit → Fin 4 → ℝ := fun _ _ => 1 / 4

theorem mass_nonneg (x : Unit) (g : Fin 4) : 0 ≤ mass x g := by unfold mass; norm_num

theorem mass_total : (∑ x : Unit, ∑ g : Fin 4, mass x g) = 1 := by
  simp [mass, Fin.sum_univ_succ]

/-- `H(G|X)=log 4`。 -/
theorem entropy_eq_log_four : finiteConditionalEntropyGivenInput mass = Real.log 4 := by
  unfold finiteConditionalEntropyGivenInput finiteConditionalEntropyTerm
  simp only [Finset.univ_unique, Finset.sum_singleton, mass, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  have h : Real.log (1 / 4 / 1) = -Real.log 4 := by
    rw [div_one, one_div, Real.log_inv]
  have : Real.log (1 / 4 / 1) = -Real.log 4 := h
  norm_num at this ⊢
  linarith

/-- 方策 `φ` の CMI（文脈なし）。 -/
noncomputable def cmi {n : ℕ} (φ : Fin 4 → Fin n) : ℝ :=
  finiteConditionalMutualInformation mass (fun (_ : Unit) g => φ g)

/-- 自由意思容量 `F(n+1)=max_{φ:Fin 4→Fin (n+1)} I(G;φ(G))`（出力アルファベットサイズ `n+1`）。 -/
noncomputable def cap (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun φ : Fin 4 → Fin (n + 1) => cmi φ)

/-- 上界: 任意の方策で `I≤H(G|X)=log 4`。 -/
theorem cmi_le_log_four {n : ℕ} (φ : Fin 4 → Fin n) : cmi φ ≤ Real.log 4 := by
  have h := finiteConditionalMutualInformation_le_entropy mass (fun (_ : Unit) g => φ g) mass_nonneg
  rw [entropy_eq_log_four] at h
  exact h

theorem cap_le_log_four (n : ℕ) : cap n ≤ Real.log 4 :=
  Finset.sup'_le _ _ fun φ _ => cmi_le_log_four φ

/-- 単射方策（Python の「出力が4個以上」）で `I=H(G|X)=log 4`。 -/
theorem cmi_injective {n : ℕ} (φ : Fin 4 → Fin n) (hφ : Function.Injective φ) :
    cmi φ = Real.log 4 := by
  have := theorem21_finite_information_capacity mass (fun (_ : Unit) g => φ g) mass_nonneg
    mass_total (fun x g _ g' h => hφ h) (by rw [entropy_eq_log_four]; exact Real.log_pos (by norm_num))
  rw [← entropy_eq_log_four]
  exact this.1

/-- 出力が1個（`n=1`）なら `I=0`: 零容量。 -/
theorem cap_one : cap 0 = 0 := by
  have hconst : ∀ φ : Fin 4 → Fin 1, cmi φ = 0 := by
    intro φ
    unfold cmi finiteConditionalMutualInformation finiteConditionalEntropyGivenInputAndOutput
      finiteConditionalEntropyGivenInput
    have this : ∀ g g' : Fin 4, (φ g' = φ g) = True := fun g g' => eq_true (Subsingleton.elim _ _)
    simp [this]
  unfold cap
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun φ _ => (hconst φ).le
  · exact (hconst (fun _ => 0)).symm.le.trans (Finset.le_sup' (fun φ : Fin 4 → Fin 1 => cmi φ)
      (Finset.mem_univ _))

/-- 4 個の出力があれば容量は `log 4`（上界と単射方策）。 -/
theorem cap_four : cap 3 = Real.log 4 := by
  refine le_antisymm (cap_le_log_four 3) ?_
  have hid : cmi (id : Fin 4 → Fin 4) = Real.log 4 := cmi_injective id Function.injective_id
  rw [← hid]
  exact Finset.le_sup' (fun φ : Fin 4 → Fin 4 => cmi φ) (Finset.mem_univ _)

/-- CMI は出力のラベル付けに依らない（ファイバーだけで決まる）。`Fin n ↪ Fin (n+1)` で保存される。 -/
theorem cmi_castSucc {n : ℕ} (φ : Fin 4 → Fin n) :
    cmi (fun g => Fin.castSucc (φ g)) = cmi φ := by
  unfold cmi finiteConditionalMutualInformation finiteConditionalEntropyGivenInputAndOutput
  simp [Fin.castSucc_inj]
  convert rfl

/-- 定理19の単調性（評価値保存の単射埋め込み）: `F(n)≤F(n+1)`。 -/
theorem cap_mono (n : ℕ) : cap n ≤ cap (n + 1) := by
  refine Finset.sup'_le _ _ fun φ _ => ?_
  have := Finset.le_sup' (fun ψ : Fin 4 → Fin (n + 2) => cmi ψ)
    (Finset.mem_univ (fun g => Fin.castSucc (φ g)))
  rw [cmi_castSucc] at this
  exact this

/-- Python の層列 `m_α=[1,2,3,4,4]` に対応する容量列は単調で、端点は `0` と `log 4`。 -/
theorem python_layers_monotone_with_endpoints :
    cap 0 ≤ cap 1 ∧ cap 1 ≤ cap 2 ∧ cap 2 ≤ cap 3 ∧ cap 0 = 0 ∧ cap 3 = Real.log 4 :=
  ⟨cap_mono 0, cap_mono 1, cap_mono 2, cap_one, cap_four⟩

/-- 端点正規化 `f=(F-F(1))/(F(4)-F(1))`: `f(1)=0`, `f(4)=1`（`log 4>0`）。 -/
theorem normalization_endpoints :
    (cap 0 - cap 0) / (cap 3 - cap 0) = 0 ∧ (cap 3 - cap 0) / (cap 3 - cap 0) = 1 := by
  have h : cap 3 - cap 0 = Real.log 4 := by rw [cap_four, cap_one]; ring
  constructor
  · simp
  · rw [h]; exact div_self (Real.log_pos (by norm_num)).ne'

/-! ## 反例: 単射だが解像度の粗い観測 -/

/-- 解像度 `b` の区間分割による観測: Python の `idx=min(int(y b), b-1)`、`y=(0.1,0.4,0.6,0.9)`。 -/
def bins1 : Fin 4 → Fin 1 := fun _ => 0
def bins2 : Fin 4 → Fin 2 := ![0, 0, 1, 1]
def bins10 : Fin 4 → Fin 10 := ![1, 4, 6, 9]

/-- `b=1`（自明σ代数）: 集合として単射な `y` でも観測される情報は `I=0<log 4=H(G|X)`。 -/
theorem bins1_info_zero : cmi bins1 = 0 ∧ 0 < Real.log 4 - cmi bins1 := by
  have h0 : cmi bins1 = 0 := by
    unfold cmi finiteConditionalMutualInformation finiteConditionalEntropyGivenInputAndOutput
      finiteConditionalEntropyGivenInput
    have this : ∀ g g' : Fin 4, (bins1 g' = bins1 g) = True := fun g g' => eq_true (Subsingleton.elim _ _)
    simp [this]
  exact ⟨h0, by rw [h0]; simpa using Real.log_pos (by norm_num : (1 : ℝ) < 4)⟩

/-- `b=10`: 区間が十分細かければ（`y` を分離）`I=log 4`。 -/
theorem bins10_info_full : cmi bins10 = Real.log 4 := by
  refine cmi_injective bins10 ?_
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [bins10] at h ⊢

/-- `b=2`: `I=log 2`（2つのブロック `{0,1},{2,3}`）。 -/
theorem bins2_info : cmi bins2 = Real.log 2 := by
  unfold cmi finiteConditionalMutualInformation finiteConditionalEntropyGivenInputAndOutput
  rw [entropy_eq_log_four]
  simp only [finiteConditionalEntropyTerm, mass, Fin.sum_univ_succ, Finset.univ_unique,
    Finset.sum_singleton, Fin.sum_univ_zero]
  simp [bins2]
  norm_num
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h8 : Real.log (1 / 4 / (1 / 2)) = -Real.log 2 := by
    rw [show (1 / 4 / (1 / 2) : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  simp [h8] at *
  linarith

/-! ## ゴールと独立な確率的出力

この例ではゴールを一様な `Fin 4`、出力を非退化な二点分布とし、出力核をゴールに
依存しない定数核にする。同時法則を条件付き独立参照測度そのもので構成するため、
KL自己比較の値0を既存の一般測度CMI APIで得る。
-/

open MeasureTheory ProbabilityTheory

/-- 二点出力の非退化分布 `(1/3, 2/3)`。 -/
noncomputable def randomOutputMass : Fin 2 → ℝ := fun y => if y = 0 then 1 / 3 else 2 / 3

theorem randomOutputMass_nonneg (y : Fin 2) : 0 ≤ randomOutputMass y := by
  fin_cases y <;> norm_num [randomOutputMass]

theorem randomOutputMass_sum : ∑ y : Fin 2, randomOutputMass y = 1 := by
  norm_num [randomOutputMass, Fin.sum_univ_succ]

/-- 一様なゴール分布を有限確率測度にする。 -/
noncomputable def randomGoalMeasure : Measure (Fin 4) :=
  Tomabechi.Theorem19_22.finiteGoalMeasureOfMass (fun _ : Fin 4 => (1 / 4 : ℝ))

theorem randomGoalMeasure_probability : IsProbabilityMeasure randomGoalMeasure := by
  apply Tomabechi.Theorem19_22.finiteGoalMeasureOfMass_isProbability
  · intro g
    norm_num
  · norm_num [Fin.sum_univ_succ]

/-- ゴールと独立な出力分布を有限確率測度にする。 -/
noncomputable def randomOutputMeasure : Measure (Fin 2) :=
  Tomabechi.Theorem19_22.finiteGoalMeasureOfMass randomOutputMass

theorem randomOutputMeasure_probability : IsProbabilityMeasure randomOutputMeasure :=
  Tomabechi.Theorem19_22.finiteGoalMeasureOfMass_isProbability
    randomOutputMass randomOutputMass_nonneg randomOutputMass_sum

theorem randomOutputMeasure_nondegenerate :
    randomOutputMeasure {0} = ENNReal.ofReal (1 / 3) ∧
      randomOutputMeasure {1} = ENNReal.ofReal (2 / 3) := by
  constructor
  · simp [randomOutputMeasure, randomOutputMass, Tomabechi.Theorem19_22.finiteGoalMeasureOfMass_singleton]
  · simp [randomOutputMeasure, randomOutputMass, Tomabechi.Theorem19_22.finiteGoalMeasureOfMass_singleton]

/-- 独立確率出力の条件付き相互情報量データ。
`joint` を条件付き独立参照測度と同じ構成にすることで、KL自己比較となる。 -/
noncomputable def independentRandomOutputLaw :
    Tomabechi.Theorem22.ConditionalMutualInformationLaw Unit (Fin 4) (Fin 2) := by
  let input : Measure Unit := Measure.dirac ()
  letI : IsProbabilityMeasure randomGoalMeasure := randomGoalMeasure_probability
  letI : IsProbabilityMeasure randomOutputMeasure := randomOutputMeasure_probability
  let goalKernel : Kernel Unit (Fin 4) := Kernel.const Unit randomGoalMeasure
  let outputKernel : Kernel Unit (Fin 2) := Kernel.const Unit randomOutputMeasure
  refine {
    input := input
    inputProbability := by dsimp [input]; infer_instance
    goalGivenInput := goalKernel
    goalKernelMarkov := by dsimp [goalKernel]; infer_instance
    actionGivenInput := outputKernel
    actionKernelMarkov := by dsimp [outputKernel]; infer_instance
    joint := input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ Kernel.copy Unit)
    jointGoalMarginal := ?_
    jointActionMarginal := ?_ }
  · letI : IsProbabilityMeasure input := by dsimp [input]; infer_instance
    letI : IsMarkovKernel goalKernel := by dsimp [goalKernel]; infer_instance
    letI : IsMarkovKernel outputKernel := by dsimp [outputKernel]; infer_instance
    calc
      (input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ Kernel.copy Unit)).map
          (fun z : Unit × (Fin 4 × Fin 2) => (z.1, z.2.1)) =
          (input ⊗ₘ (goalKernel ×ₖ outputKernel)).map (Prod.map id Prod.fst) := by
            change (input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ Kernel.copy Unit)).map _ = _
            rw [Kernel.parallelComp_comp_copy]
            rfl
      _ = input ⊗ₘ ((goalKernel ×ₖ outputKernel).map Prod.fst) :=
        (Measure.compProd_map measurable_fst).symm
      _ = input ⊗ₘ goalKernel := by
        rw [← Kernel.fst_eq, Kernel.fst_prod]
  · letI : IsProbabilityMeasure input := by dsimp [input]; infer_instance
    letI : IsMarkovKernel goalKernel := by dsimp [goalKernel]; infer_instance
    letI : IsMarkovKernel outputKernel := by dsimp [outputKernel]; infer_instance
    calc
      (input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ Kernel.copy Unit)).map
          (fun z : Unit × (Fin 4 × Fin 2) => (z.1, z.2.2)) =
          (input ⊗ₘ (goalKernel ×ₖ outputKernel)).map (Prod.map id Prod.snd) := by
            change (input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ Kernel.copy Unit)).map _ = _
            rw [Kernel.parallelComp_comp_copy]
            rfl
      _ = input ⊗ₘ ((goalKernel ×ₖ outputKernel).map Prod.snd) :=
        (Measure.compProd_map measurable_snd).symm
      _ = input ⊗ₘ outputKernel := by
        rw [← Kernel.snd_eq, Kernel.snd_prod]

/-- 非退化な確率的出力でも、ゴールと独立なら測度CMIは厳密に0。 -/
theorem independent_random_output_cmi_zero :
    (InformationTheory.klDiv independentRandomOutputLaw.joint
      independentRandomOutputLaw.referenceMeasure).toReal = 0 := by
  letI : IsProbabilityMeasure independentRandomOutputLaw.input :=
    independentRandomOutputLaw.inputProbability
  letI : IsMarkovKernel independentRandomOutputLaw.goalGivenInput :=
    independentRandomOutputLaw.goalKernelMarkov
  letI : IsMarkovKernel independentRandomOutputLaw.actionGivenInput :=
    independentRandomOutputLaw.actionKernelMarkov
  letI : IsProbabilityMeasure independentRandomOutputLaw.joint :=
    independentRandomOutputLaw.joint_isProbabilityMeasure
  have hsame : independentRandomOutputLaw.joint = independentRandomOutputLaw.referenceMeasure := rfl
  rw [← hsame, InformationTheory.klDiv_self]
  simp

/-- 上の独立例は有限KL条件も満たすので、既存の一般測度CMI-lawへ入る。 -/
noncomputable def independentRandomOutputFiniteLaw :
    Tomabechi.Theorem22.FiniteConditionalMutualInformationLaw Unit (Fin 4) (Fin 2) := by
  refine ⟨independentRandomOutputLaw, ?_⟩
  letI : IsProbabilityMeasure independentRandomOutputLaw.input :=
    independentRandomOutputLaw.inputProbability
  letI : IsMarkovKernel independentRandomOutputLaw.goalGivenInput :=
    independentRandomOutputLaw.goalKernelMarkov
  letI : IsMarkovKernel independentRandomOutputLaw.actionGivenInput :=
    independentRandomOutputLaw.actionKernelMarkov
  letI : IsProbabilityMeasure independentRandomOutputLaw.joint :=
    independentRandomOutputLaw.joint_isProbabilityMeasure
  have hsame : independentRandomOutputLaw.joint = independentRandomOutputLaw.referenceMeasure := rfl
  rw [← hsame, InformationTheory.klDiv_self]
  norm_num

/-- 有限CMI-lawが返すKLスコアも0。 -/
theorem independent_random_output_finite_score_zero :
    Tomabechi.Theorem22.finiteKLDivergenceScore
      independentRandomOutputFiniteLaw.toFiniteKLLaw = 0 := by
  change (InformationTheory.klDiv independentRandomOutputLaw.joint
    independentRandomOutputLaw.referenceMeasure).toReal = 0
  exact independent_random_output_cmi_zero

/-- 任意の有限確率出力測度 `ν` に対する、ゴールと独立な確率カーネルのlaw。
出力値の分布を選ばず、同じ確率測度を全ての `g` に割り当てる。 -/
noncomputable def independentOutputLawFor
    {Y : Type*} [MeasurableSpace Y] [Fintype Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    Tomabechi.Theorem22.ConditionalMutualInformationLaw Unit (Fin 4) Y := by
  let input : Measure Unit := Measure.dirac ()
  letI : IsProbabilityMeasure randomGoalMeasure := randomGoalMeasure_probability
  let goalKernel : Kernel Unit (Fin 4) := Kernel.const Unit randomGoalMeasure
  let outputKernel : Kernel Unit Y := Kernel.const Unit ν
  refine {
    input := input
    inputProbability := by dsimp [input]; infer_instance
    goalGivenInput := goalKernel
    goalKernelMarkov := by dsimp [goalKernel]; infer_instance
    actionGivenInput := outputKernel
    actionKernelMarkov := by dsimp [outputKernel]; infer_instance
    joint := input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ Kernel.copy Unit)
    jointGoalMarginal := ?_
    jointActionMarginal := ?_ }
  · letI : IsProbabilityMeasure input := by dsimp [input]; infer_instance
    letI : IsMarkovKernel goalKernel := by dsimp [goalKernel]; infer_instance
    letI : IsMarkovKernel outputKernel := by dsimp [outputKernel]; infer_instance
    calc
      (input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ Kernel.copy Unit)).map
          (fun z : Unit × (Fin 4 × Y) => (z.1, z.2.1)) =
          (input ⊗ₘ (goalKernel ×ₖ outputKernel)).map (Prod.map id Prod.fst) := by
            change (input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ Kernel.copy Unit)).map _ = _
            rw [Kernel.parallelComp_comp_copy]
            rfl
      _ = input ⊗ₘ ((goalKernel ×ₖ outputKernel).map Prod.fst) :=
        (Measure.compProd_map measurable_fst).symm
      _ = input ⊗ₘ goalKernel := by rw [← Kernel.fst_eq, Kernel.fst_prod]
  · letI : IsProbabilityMeasure input := by dsimp [input]; infer_instance
    letI : IsMarkovKernel goalKernel := by dsimp [goalKernel]; infer_instance
    letI : IsMarkovKernel outputKernel := by dsimp [outputKernel]; infer_instance
    calc
      (input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ Kernel.copy Unit)).map
          (fun z : Unit × (Fin 4 × Y) => (z.1, z.2.2)) =
          (input ⊗ₘ (goalKernel ×ₖ outputKernel)).map (Prod.map id Prod.snd) := by
            change (input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ Kernel.copy Unit)).map _ = _
            rw [Kernel.parallelComp_comp_copy]
            rfl
      _ = input ⊗ₘ ((goalKernel ×ₖ outputKernel).map Prod.snd) :=
        (Measure.compProd_map measurable_snd).symm
      _ = input ⊗ₘ outputKernel := by rw [← Kernel.snd_eq, Kernel.snd_prod]

/-- 任意の有限確率出力分布 `ν` は独立カーネルとなり、CMIのKL値は0。 -/
theorem independent_output_kl_zero_for
    {Y : Type*} [MeasurableSpace Y] [Fintype Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    InformationTheory.klDiv (independentOutputLawFor ν).joint
      (independentOutputLawFor ν).referenceMeasure = 0 := by
  let law := independentOutputLawFor ν
  letI : IsProbabilityMeasure law.input := law.inputProbability
  letI : IsMarkovKernel law.goalGivenInput := law.goalKernelMarkov
  letI : IsMarkovKernel law.actionGivenInput := law.actionKernelMarkov
  letI : IsProbabilityMeasure law.joint := law.joint_isProbabilityMeasure
  have hsame : law.joint = law.referenceMeasure := rfl
  rw [← hsame, InformationTheory.klDiv_self]

/-- 任意の `ν` に対し、出力核・joint・参照測度・有限KL条件を全て備えたlaw。 -/
noncomputable def independentOutputFiniteLawFor
    {Y : Type*} [MeasurableSpace Y] [Fintype Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    Tomabechi.Theorem22.FiniteConditionalMutualInformationLaw Unit (Fin 4) Y := by
  refine ⟨independentOutputLawFor ν, ?_⟩
  rw [independent_output_kl_zero_for]
  norm_num

/-- 任意の有限確率出力分布に対する一般測度CMIスコアは0。 -/
theorem independent_output_finite_score_zero_for
    {Y : Type*} [MeasurableSpace Y] [Fintype Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    Tomabechi.Theorem22.finiteKLDivergenceScore
      (independentOutputFiniteLawFor ν).toFiniteKLLaw = 0 := by
  change (InformationTheory.klDiv (independentOutputLawFor ν).joint
    (independentOutputLawFor ν).referenceMeasure).toReal = 0
  rw [independent_output_kl_zero_for]
  norm_num

/-- `Fin 4` 上の任意の方策を4個の出力値で表す列挙用表現。 -/
def tuplePolicy2 (a b c d : Fin 2) : Fin 4 → Fin 2 := ![a, b, c, d]

/-- 二出力の16個の等号分割を尽くすと、情報量は `log 2` 以下。 -/
theorem cmi_two_le_log_two_tuple (a b c d : Fin 2) :
    cmi (tuplePolicy2 a b c d) ≤ Real.log 2 := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog31 : 4 * Real.log 2 ≤ 3 * Real.log 3 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by norm_num : (16 : ℝ) ≤ 27)
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num,
      show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow, Real.log_pow] at h
    norm_num at h
    linarith
  have hlog12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlog13 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlog14 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [cmi, tuplePolicy2, finiteConditionalMutualInformation,
      finiteConditionalEntropyGivenInputAndOutput, finiteConditionalEntropyGivenInput,
      finiteConditionalEntropyTerm, mass, Fin.sum_univ_succ, Fin.sum_univ_zero,
      hlog12, hlog13, hlog14, hlog4] <;>
    nlinarith [hlog31, Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- 任意の二値方策は4個の値のタプルに書き直せるため、上の分類が全方策を覆う。 -/
theorem cmi_two_le_log_two (φ : Fin 4 → Fin 2) : cmi φ ≤ Real.log 2 := by
  have hφ : φ = tuplePolicy2 (φ 0) (φ 1) (φ 2) (φ 3) := by
    funext i
    fin_cases i <;> simp [tuplePolicy2]
  rw [hφ]
  exact cmi_two_le_log_two_tuple _ _ _ _

/-- 二つずつに分ける方策が上界を達成するので `F(2)=log 2`。 -/
theorem cap_two : cap 1 = Real.log 2 := by
  unfold cap
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun φ _ => cmi_two_le_log_two φ
  · rw [← bins2_info]
    exact Finset.le_sup' (fun φ : Fin 4 → Fin 2 => cmi φ) (Finset.mem_univ bins2)

/-- `Fin 3` 上の方策を四つの出力値で表す列挙用表現。 -/
def tuplePolicy3 (a b c d : Fin 3) : Fin 4 → Fin 3 := ![a, b, c, d]

/-- 三出力の81個の写像を列挙すると、CMIは `(3/2) log 2` 以下。 -/
theorem cmi_three_le_log_three_tuple (a b c d : Fin 3) :
    cmi (tuplePolicy3 a b c d) ≤ (3 / 2) * Real.log 2 := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlog13 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlog14 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [cmi, tuplePolicy3, finiteConditionalMutualInformation,
      finiteConditionalEntropyGivenInputAndOutput, finiteConditionalEntropyGivenInput,
      finiteConditionalEntropyTerm, mass, Fin.sum_univ_succ, hlog12, hlog13, hlog14, hlog4] <;>
    norm_num <;> nlinarith [hlog2, hlog3, hlog23]

/-- 代表元 `(0,1,2,2)` は `(2,1,1)` 分割なので最大値を達成する。 -/
theorem cmi_three_tuple211 :
    cmi (tuplePolicy3 0 1 2 2) = (3 / 2) * Real.log 2 := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlog14 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  norm_num [cmi, tuplePolicy3, finiteConditionalMutualInformation,
    finiteConditionalEntropyGivenInputAndOutput, finiteConditionalEntropyGivenInput,
    finiteConditionalEntropyTerm, mass, Fin.sum_univ_succ, hlog4, hlog12, hlog14,
    Real.log_inv] <;> ring

/-- 任意の三値方策を四つの値で列挙するので上界は全ての方策に成り立つ。 -/
theorem cmi_three_le_log_three (φ : Fin 4 → Fin 3) :
    cmi φ ≤ (3 / 2) * Real.log 2 := by
  have hφ : φ = tuplePolicy3 (φ 0) (φ 1) (φ 2) (φ 3) := by
    funext i
    fin_cases i <;> simp [tuplePolicy3]
  rw [hφ]
  exact cmi_three_le_log_three_tuple _ _ _ _

/-- `(2,1,1)` 方策が上界を達成し、`F(3)=3/2 log 2` となる。 -/
theorem cap_three : cap 2 = (3 / 2) * Real.log 2 := by
  unfold cap
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun φ _ => cmi_three_le_log_three φ
  · rw [← cmi_three_tuple211]
    exact Finset.le_sup' (fun φ : Fin 4 → Fin 3 => cmi φ)
      (Finset.mem_univ (tuplePolicy3 0 1 2 2))

end Tomabechi.Examples.Theorem19
