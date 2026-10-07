import Tomabechi.Consistency.ConsistencyC6_ModelSignature

/-!
# C6：同じ共有署名上の15→23入力

物理観測・全正層観測・重み・完全軌道をモデルのフィールドから取り、
絶対連続性、全有限層族の一様可積分性、接頭和のa.e.収束、A7を供給する。
非再訪の結論だけを独立証人から引用せず、この入力を一般入口へ渡す。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Consistency.C2
open MeasureTheory Filter
open scoped Topology

/-- O07/O08の15→23解析入力。生存時間は非負半直線、生成率は3。
観測は完全状態の関数であり、別の時計座標を追加しない。 -/
structure EntropyBalanceInputs (M : ModelSignature) : Prop where
  weight_positive : ∀ n, 0 < M.weight n
  layer_nonnegative : ∀ n z, 0 ≤ M.layerObservation n z
  production_strict : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < ∫ _t in a..b, (3 : ℝ)
  production_integrable : ∀ a b : ℝ,
    IntervalIntegrable (fun _t : ℝ => (3 : ℝ)) volume a b
  layer_ac : ∀ a b : ℝ, 0 ≤ a → a < b → ∀ n,
    AbsolutelyContinuousOnInterval (fun t => M.layerObservation n (M.completePath t)) a b
  physical_ac : ∀ a b : ℝ, 0 ≤ a → a < b →
    AbsolutelyContinuousOnInterval (fun t => M.physicalObservation (M.completePath t)) a b
  endpoint_summable : ∀ a b : ℝ, 0 ≤ a → a < b →
    Summable (fun n => M.weight n * M.layerObservation n (M.completePath a)) ∧
    Summable (fun n => M.weight n * M.layerObservation n (M.completePath b))
  all_finite_ui : ∀ a b : ℝ, 0 ≤ a → a < b →
    UniformIntegrable (fun (s : Finset PositiveLayer) t => ∑ n ∈ s,
      M.weight n * deriv (fun u => M.layerObservation n (M.completePath u)) t)
      1 (volume.restrict (Set.uIoc a b))
  prefix_tendsto : ∀ a b : ℝ, 0 ≤ a → a < b →
    ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      Tendsto (fun k => ∑ i : Fin k,
        M.weight (Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer i.val) *
          deriv (fun u => M.layerObservation
            (Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer i.val)
            (M.completePath u)) t) atTop
        (𝓝 (∑' n, M.weight n * deriv (fun u => M.layerObservation n (M.completePath u)) t))
  a7_balance : ∀ a b : ℝ, 0 ≤ a → a < b →
    ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      deriv (fun u => M.physicalObservation (M.completePath u)) t =
        -(∑' n, M.weight n * deriv (fun u => M.layerObservation n (M.completePath u)) t) + 3
  production_nonnegative : ∀ a b : ℝ, 0 ≤ a → a < b →
    0 ≤ᵐ[volume.restrict (Set.uIoc a b)] (fun _ : ℝ => (3 : ℝ))

/-- 外部の解析仮定なしに、同じcommonModelの完全pathから全入力を構成する。 -/
theorem commonModel_entropyInputs : EntropyBalanceInputs commonModel := by
  refine {
    weight_positive := layerWeight_pos
    layer_nonnegative := fun n z => layerEntropy_nonnegative z n
    production_strict := c3A7Stitched_production_integral_pos
    production_integrable := fun _ _ => intervalIntegrable_const
    layer_ac := fun a b ha hab n => c3A7StitchedLayerEntropy_ac_between n a b ha hab
    physical_ac := c3A7StitchedPhysicalEntropy_ac_between
    endpoint_summable := c3A7Stitched_A6_endpoint_summable
    all_finite_ui := c3A7Stitched_A6_finite_UI
    prefix_tendsto := ?_
    a7_balance := ?_
    production_nonnegative := c3A7Stitched_production_nonnegative_ae }
  · intro a b ha hab
    filter_upwards [c3A7StitchedCognitive_ae_ode a b ha hab] with t hq
    exact c3A7Stitched_A6_prefix_tendsto_at t _ hq
  · intro a b ha hab
    filter_upwards [c3A7StitchedCognitive_ae_ode a b ha hab] with t hq
    exact c3A7Stitched_A7_at t _ hq

/-- A6′(i)の全alive時刻での有限性。端点条件を任意の[t,t+1]へ適用する。
固定した二端点だけで内部点の有限性を推測する議論ではない。 -/
theorem EntropyBalanceInputs.summable_at {M : ModelSignature}
    (h : EntropyBalanceInputs M) (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun n => M.weight n * M.layerObservation n (M.completePath t)) :=
  (h.endpoint_summable t (t + 1) ht (by linarith)).1

/-- 入力recordを一般15→23入口へ直接渡した、Mの同じ完全軌道の非再訪。 -/
theorem EntropyBalanceInputs.nonrecurrence {M : ModelSignature} (h : EntropyBalanceInputs M) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Ici 0 → t₂ ∈ Set.Ici 0 → t₁ < t₂ →
      M.completePath t₂ ≠ M.completePath t₁ := by
  apply Tomabechi.Theorem15_23.theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence
    M.physicalObservation M.layerObservation M.weight h.weight_positive h.layer_nonnegative
    M.completePath (fun _ => 3) (Set.Ici 0)
  · exact fun a b ha _ hab => h.production_strict a b ha hab
  · exact fun a b ha _ hab => h.layer_ac a b ha hab
  · exact fun a b ha _ hab => h.physical_ac a b ha hab
  · exact fun a b ha _ hab => h.endpoint_summable a b ha hab
  · exact fun a b ha _ hab => h.all_finite_ui a b ha hab
  · exact fun a b ha _ hab => h.prefix_tendsto a b ha hab
  · exact fun a b ha _ hab => h.a7_balance a b ha hab
  · exact fun a b ha _ hab => h.production_nonnegative a b ha hab

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.commonModel_entropyInputs
#print axioms Tomabechi.Consistency.C6.EntropyBalanceInputs.nonrecurrence
#print axioms Tomabechi.Consistency.C6.EntropyBalanceInputs.summable_at
