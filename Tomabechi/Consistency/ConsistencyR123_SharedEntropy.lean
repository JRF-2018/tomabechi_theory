import Tomabechi.Consistency.ConsistencyR123_SharedSignature

/-!
# 共有署名の観測と完全状態pathによる15→23入力

可算正層の重み・観測・完全状態pathを同じ署名Nから読む。
全有限部分和の一様可積分性とA7を含む一般入口へ直接渡す。
層添字は共通束内の正層住所の可算族であり、全束点を可算と仮定しない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory Filter
open scoped Topology
open Tomabechi.Consistency.C6 Tomabechi.Consistency.C2 Tomabechi.Consistency.R1

/-- 正層住所を読む観測と重み。元モデルの観測を別に注入しない。 -/
def SharedModelSignature.positiveObservation (N : SharedModelSignature)
    (p : PositiveLayer) (z : CompleteState) : ℝ :=
  N.observation (commonConceptPositiveEntropyAddress p) z

def SharedModelSignature.positiveWeight (N : SharedModelSignature) (p : PositiveLayer) : ℝ :=
  N.weight (commonConceptPositiveEntropyAddress p)

/-- 共有署名上の定理15/23-Aの全積分収支入力。
A7は他条件から導く仮定に変更せず、独立の収支式として保持する。 -/
structure SharedEntropyInputs (N : SharedModelSignature) : Prop where
  weight_positive : ∀ p, 0 < N.positiveWeight p
  layer_nonnegative : ∀ p z, 0 ≤ N.positiveObservation p z
  production_strict : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < ∫ _t in a..b, (3 : ℝ)
  production_integrable : ∀ a b : ℝ, IntervalIntegrable (fun _t : ℝ => (3 : ℝ)) volume a b
  layer_ac : ∀ a b : ℝ, 0 ≤ a → a < b → ∀ p,
    AbsolutelyContinuousOnInterval (fun t => N.positiveObservation p (N.completePath t)) a b
  physical_ac : ∀ a b : ℝ, 0 ≤ a → a < b →
    AbsolutelyContinuousOnInterval (fun t => N.observation ⊥ (N.completePath t)) a b
  endpoint_summable : ∀ a b : ℝ, 0 ≤ a → a < b →
    Summable (fun p => N.positiveWeight p * N.positiveObservation p (N.completePath a)) ∧
    Summable (fun p => N.positiveWeight p * N.positiveObservation p (N.completePath b))
  all_finite_ui : ∀ a b : ℝ, 0 ≤ a → a < b →
    UniformIntegrable (fun (s : Finset PositiveLayer) t => ∑ p ∈ s,
      N.positiveWeight p * deriv (fun u => N.positiveObservation p (N.completePath u)) t)
      1 (volume.restrict (Set.uIoc a b))
  prefix_tendsto : ∀ a b : ℝ, 0 ≤ a → a < b →
    ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      Tendsto (fun k => ∑ i : Fin k,
        N.positiveWeight (Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer i.val) *
          deriv (fun u => N.positiveObservation
            (Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer i.val)
            (N.completePath u)) t) atTop
        (𝓝 (∑' p, N.positiveWeight p *
          deriv (fun u => N.positiveObservation p (N.completePath u)) t))
  a7_balance : ∀ a b : ℝ, 0 ≤ a → a < b →
    ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      deriv (fun u => N.observation ⊥ (N.completePath u)) t =
        -(∑' p, N.positiveWeight p *
          deriv (fun u => N.positiveObservation p (N.completePath u)) t) + 3
  production_nonnegative : ∀ a b : ℝ, 0 ≤ a → a < b →
    0 ≤ᵐ[volume.restrict (Set.uIoc a b)] (fun _ : ℝ => (3 : ℝ))

/-- 観測・重み・pathの保存式を使い、全積分入力を署名Nへ移す。
Nのデータをcanonical値へ置き換える外部仮定は要求しない。 -/
theorem SharedDataPreservation.entropyInputs {N : SharedModelSignature}
    (hs : SharedDataPreservation N) (he : EntropyBalanceInputs N.legacy) :
    SharedEntropyInputs N := by
  have hw : N.positiveWeight = N.legacy.weight := by
    funext p
    exact hs.weight p
  have ho : N.positiveObservation = N.legacy.layerObservation := by
    funext p z
    exact hs.positive p z
  have hp : N.observation ⊥ = N.legacy.physicalObservation := by
    funext z
    exact hs.physical z
  refine {
    weight_positive := ?_
    layer_nonnegative := ?_
    production_strict := he.production_strict
    production_integrable := he.production_integrable
    layer_ac := ?_
    physical_ac := ?_
    endpoint_summable := ?_
    all_finite_ui := ?_
    prefix_tendsto := ?_
    a7_balance := ?_
    production_nonnegative := he.production_nonnegative }
  · simpa only [hw] using he.weight_positive
  · simpa only [ho] using he.layer_nonnegative
  · simpa only [ho, hs.completePath] using he.layer_ac
  · simpa only [hp, hs.completePath] using he.physical_ac
  · simpa only [hw, ho, hs.completePath] using he.endpoint_summable
  · simpa only [hw, ho, hs.completePath] using he.all_finite_ui
  · simpa only [hw, ho, hs.completePath] using he.prefix_tendsto
  · simpa only [hw, ho, hp, hs.completePath] using he.a7_balance

/-- 同じ署名の完全状態pathに一般15→23入口を直接適用する。 -/
theorem SharedEntropyInputs.nonrecurrence {N : SharedModelSignature}
    (he : SharedEntropyInputs N) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Ici 0 → t₂ ∈ Set.Ici 0 → t₁ < t₂ →
      N.completePath t₂ ≠ N.completePath t₁ := by
  apply Tomabechi.Theorem15_23.theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence
    (N.observation ⊥) N.positiveObservation N.positiveWeight
    he.weight_positive he.layer_nonnegative N.completePath (fun _ => 3) (Set.Ici 0)
  · exact fun a b ha _ hab => he.production_strict a b ha hab
  · exact fun a b ha _ hab => he.layer_ac a b ha hab
  · exact fun a b ha _ hab => he.physical_ac a b ha hab
  · exact fun a b ha _ hab => he.endpoint_summable a b ha hab
  · exact fun a b ha _ hab => he.all_finite_ui a b ha hab
  · exact fun a b ha _ hab => he.prefix_tendsto a b ha hab
  · exact fun a b ha _ hab => he.a7_balance a b ha hab
  · exact fun a b ha _ hab => he.production_nonnegative a b ha hab

/-- 共有署名の具体path上で全入力を同時に満たす。 -/
theorem sharedModel_entropyInputs : SharedEntropyInputs sharedModel :=
  sharedModel_preservation.entropyInputs commonModel_entropyInputs

#print axioms sharedModel_entropyInputs
#print axioms SharedEntropyInputs.nonrecurrence
end Tomabechi.Consistency.R123
