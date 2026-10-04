import Theorem15

/-!
# 定理15(I)から定理23第一部への接続

定理15(I)の一般化エントロピー収支を各生存区間に適用し、定理23の条件23-A
(各区間の総生成量が厳密に正)と合わせて完全状態の非再帰性を得る。
23-Aの厳密正値は定理15の非負性からは導かれないため、独立条件として残す。
-/

namespace Tomabechi.Theorem15_23

open Filter
open scoped Topology

/-- 各生存区間で定理15(I)のA2/A5/A6′/A7条件が成立すれば、積分収支が得られる。
さらに定理23-Aの厳密散逸条件から、完全状態は生存区間内で再帰しない。

A7とA6′は原文の独立仮定のまま入力する。定理15の非負生成から厳密散逸を
導いたとは主張しない。 -/
theorem theorem15_first_part_implies_theorem23_nonrecurrence
    {State Layer : Type*} [Countable Layer] [DecidableEq Layer]
    (enumeration : ℕ ≃ Layer)
    (physicalEntropy : State → ℝ)
    (layerEntropy : Layer → State → ℝ)
    (layerWeight : Layer → ℝ)
    (hweight : ∀ layer, 0 < layerWeight layer)
    (hlayerNonnegative : ∀ layer z, 0 ≤ layerEntropy layer z)
    (state : ℝ → State) (production : ℝ → ℝ) (alive : Set ℝ)
    (hstrict : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      0 < ∫ t in a..b, production t)
    (hA2 : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b → ∀ layer,
      AbsolutelyContinuousOnInterval
        (fun t => layerEntropy layer (state t)) a b)
    (hA5 : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      AbsolutelyContinuousOnInterval
        (fun t => physicalEntropy (state t)) a b)
    (hA6finite : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      Summable (fun layer =>
        layerWeight layer * layerEntropy layer (state a)) ∧
      Summable (fun layer =>
        layerWeight layer * layerEntropy layer (state b)))
    (hA6UI : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      MeasureTheory.UniformIntegrable
        (fun s t => ∑ layer ∈ s,
          layerWeight layer * deriv (fun u => layerEntropy layer (state u)) t)
        1 (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (hA6ae : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
        Tendsto
          (fun n => ∑ i : Fin n,
            layerWeight (enumeration i.val) *
              deriv (fun u => layerEntropy (enumeration i.val) (state u)) t)
          atTop (𝓝 (∑' layer,
            layerWeight layer *
              deriv (fun u => layerEntropy layer (state u)) t)))
    (hA7 : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
        deriv (fun u => physicalEntropy (state u)) t =
          -(∑' layer, layerWeight layer *
            deriv (fun u => layerEntropy layer (state u)) t) + production t)
    (hA7nonnegative : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] production) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      state t₂ ≠ state t₁ := by
  let generalizedEntropy : State → ℝ := fun z =>
    physicalEntropy z + ∑' layer, layerWeight layer * layerEntropy layer z
  apply Tomabechi.Theorem23.complete_state_never_repeats_of_strict_entropy_balance
    generalizedEntropy state production alive hstrict
  intro a b ha hb hab
  have hbalance := Tomabechi.Theorem15.theorem15_trajectory_integral_balance
    enumeration physicalEntropy layerEntropy layerWeight hweight
    hlayerNonnegative state a b (le_of_lt hab)
    (hA2 a b ha hb hab) (hA5 a b ha hb hab)
    (hA6finite a b ha hb hab).1 (hA6finite a b ha hb hab).2
    (hA6UI a b ha hb hab)
    (hA6ae a b ha hb hab) production (hA7 a b ha hb hab)
    (hA7nonnegative a b ha hb hab)
  change generalizedEntropy (state b) - generalizedEntropy (state a) =
    ∫ t in a..b, production t
  exact hbalance.1

/-- 有限個の認知層では列挙 `ℕ ≃ Layer` や可算Vitali極限を使わず、定理15(I)の
有限層収支を各alive区間に適用して定理23第一部へ接続する。厳密正値は23-Aとして
独立に仮定する。 -/
theorem theorem15_finite_layer_implies_theorem23_nonrecurrence
    {State Layer : Type*} [Fintype Layer]
    (physicalEntropy : State → ℝ)
    (layerEntropy : Layer → State → ℝ)
    (layerWeight : Layer → ℝ)
    (hweight : ∀ layer, 0 < layerWeight layer)
    (hlayerNonnegative : ∀ layer z, 0 ≤ layerEntropy layer z)
    (state : ℝ → State) (production : ℝ → ℝ) (alive : Set ℝ)
    (hstrict : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      0 < ∫ t in a..b, production t)
    (hA2 : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b → ∀ layer,
      AbsolutelyContinuousOnInterval
        (fun t => layerEntropy layer (state t)) a b)
    (hA5 : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      AbsolutelyContinuousOnInterval
        (fun t => physicalEntropy (state t)) a b)
    (hA7 : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
        deriv (fun u => physicalEntropy (state u)) t =
          -(∑ layer, layerWeight layer *
            deriv (fun u => layerEntropy layer (state u)) t) + production t)
    (hA7nonnegative : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] production) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      state t₂ ≠ state t₁ := by
  let generalizedEntropy : State → ℝ := fun z =>
    physicalEntropy z + ∑ layer, layerWeight layer * layerEntropy layer z
  apply Tomabechi.Theorem23.complete_state_never_repeats_of_strict_entropy_balance
    generalizedEntropy state production alive hstrict
  intro a b ha hb hab
  have hbalance := Tomabechi.Theorem15.theorem15_finite_layer_integral_balance
    physicalEntropy layerEntropy layerWeight hweight hlayerNonnegative
    state a b (le_of_lt hab)
    (hA2 a b ha hb hab) (hA5 a b ha hb hab) production
    (hA7 a b ha hb hab) (hA7nonnegative a b ha hb hab)
  change generalizedEntropy (state b) - generalizedEntropy (state a) =
    ∫ t in a..b, production t
  exact hbalance.1

/-- A countably infinite layer type admits an internal enumeration by `ℕ`.
This classical choice is an implementation device; the theorem interface
below does not ask users to construct or pass an equivalence. -/
noncomputable def countableLayerEnumeration (Layer : Type*)
    [Countable Layer] [Infinite Layer] : ℕ ≃ Layer :=
  Classical.choice (nonempty_equiv_of_countable (α := ℕ) (β := Layer))

/-- Countably infinitely many layers need no caller-supplied enumeration.
The A6′ prefix-limit premise is stated for the internal enumeration, while
the pointwise entropy summability and finite-subset uniform integrability
remain interval-local. -/
theorem theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence
    {State Layer : Type*} [Countable Layer] [Infinite Layer] [DecidableEq Layer]
    (physicalEntropy : State → ℝ)
    (layerEntropy : Layer → State → ℝ)
    (layerWeight : Layer → ℝ)
    (hweight : ∀ layer, 0 < layerWeight layer)
    (hlayerNonnegative : ∀ layer z, 0 ≤ layerEntropy layer z)
    (state : ℝ → State) (production : ℝ → ℝ) (alive : Set ℝ)
    (hstrict : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      0 < ∫ t in a..b, production t)
    (hA2 : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b → ∀ layer,
      AbsolutelyContinuousOnInterval
        (fun t => layerEntropy layer (state t)) a b)
    (hA5 : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      AbsolutelyContinuousOnInterval
        (fun t => physicalEntropy (state t)) a b)
    (hA6finite : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      Summable (fun layer => layerWeight layer * layerEntropy layer (state a)) ∧
      Summable (fun layer => layerWeight layer * layerEntropy layer (state b)))
    (hA6UI : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      MeasureTheory.UniformIntegrable
        (fun s t => ∑ layer ∈ s,
          layerWeight layer * deriv (fun u => layerEntropy layer (state u)) t)
        1 (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (hA6ae : ∀ (a b : ℝ),
      a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
        Tendsto
          (fun n => ∑ i : Fin n,
            layerWeight (countableLayerEnumeration Layer i.val) *
              deriv (fun u => layerEntropy
                (countableLayerEnumeration Layer i.val) (state u)) t)
          atTop (𝓝 (∑' layer,
            layerWeight layer *
              deriv (fun u => layerEntropy layer (state u)) t))
      )
    (hA7 : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
        deriv (fun u => physicalEntropy (state u)) t =
          -(∑' layer, layerWeight layer *
            deriv (fun u => layerEntropy layer (state u)) t) + production t)
    (hA7nonnegative : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] production) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      state t₂ ≠ state t₁ := by
  classical
  let enumeration : ℕ ≃ Layer := countableLayerEnumeration Layer
  apply theorem15_first_part_implies_theorem23_nonrecurrence enumeration
    physicalEntropy layerEntropy layerWeight hweight hlayerNonnegative
    state production alive hstrict hA2 hA5 hA6finite hA6UI
    (fun a b ha hb hab => hA6ae a b ha hb hab)
  · exact hA7
  · exact hA7nonnegative

end Tomabechi.Theorem15_23
