import Tomabechi.Consistency.ConsistencyR1_CommonLattice
import Tomabechi.Consistency.ConsistencyC3_StagePresentation

/-!
# R1: 元H-stageの中心・原子層と共通束

元の平均場H-stageの中心を作る実数表象は、新しい共通束の対角Nat層の
座標そのものである。また各段の平均場原子が指すNat層は、順序埋込み
`layerAddressEmbedding` で同じ共通束へ送られる。
-/

namespace Tomabechi.Consistency.R1

noncomputable section

open Tomabechi.Consistency.C3

/-- The scalar state of an H-stage is embedded diagonally in the same
two-coordinate space used by the C1 consensus model. -/
abbrev CommonLayerState := Fin 2 → ℝ

def commonDiagonalAgentState (x : ℝ) : CommonLayerState := fun _ => x

/-- A nondegenerate two-coordinate quadratic potential centered at a C3 layer. -/
def liftedHStagePotential (center : ℝ) (x : CommonLayerState) : ℝ :=
  -(1 / 4 : ℝ) *
    ((x 0 - center) ^ 2 + (x 1 - center) ^ 2)

theorem commonDiagonal_difference_energy (x y : ℝ) :
    ((commonDiagonalAgentState x 0 - commonDiagonalAgentState y 0) ^ 2 +
      (commonDiagonalAgentState x 1 - commonDiagonalAgentState y 1) ^ 2) =
        2 * (x - y) ^ 2 := by
  simp [commonDiagonalAgentState]
  ring

/-- Along the diagonal, the lifted two-coordinate potential is exactly the
original scalar quadratic presence field, including its normalization. -/
theorem liftedHStagePotential_on_diagonal (center x : ℝ) :
    liftedHStagePotential center (commonDiagonalAgentState x) =
      -(1 / 2 : ℝ) * (x - center) ^ 2 := by
  simp [liftedHStagePotential, commonDiagonalAgentState]
  ring

/-- The lifted presence field is maximized at the lifted center, and nowhere
else. This verifies that the transverse coordinate is not flat. -/
theorem liftedHStagePotential_zero_iff
    (center : ℝ) (x : CommonLayerState) :
    liftedHStagePotential center x = 0 ↔
      x 0 = center ∧ x 1 = center := by
  constructor
  · intro h
    have hsum : (x 0 - center) ^ 2 + (x 1 - center) ^ 2 = 0 := by
      dsimp [liftedHStagePotential] at h
      nlinarith
    have h0 : (x 0 - center) ^ 2 = 0 := by
      have hn : 0 ≤ (x 1 - center) ^ 2 := sq_nonneg _
      nlinarith
    have h1 : (x 1 - center) ^ 2 = 0 := by
      have hn : 0 ≤ (x 0 - center) ^ 2 := sq_nonneg _
      nlinarith
    constructor <;> nlinarith
  · rintro ⟨h0, h1⟩
    simp [liftedHStagePotential, h0, h1]

/-- The second difference is strictly negative in every nonzero direction;
the lifted quadratic therefore has uniform curvature in both coordinates. -/
theorem liftedHStagePotential_second_difference
    (center : ℝ) (x v : CommonLayerState) :
    liftedHStagePotential center (x + v) +
      liftedHStagePotential center (x - v) -
        2 * liftedHStagePotential center x =
      -(1 / 2 : ℝ) * ((v 0) ^ 2 + (v 1) ^ 2) := by
  simp [liftedHStagePotential, Pi.add_apply, Pi.sub_apply]
  ring

/-- Gradient of the lifted presence field in each coordinate. -/
def liftedHStagePresenceGradient (center : ℝ) (x : CommonLayerState) :
    CommonLayerState := fun i => -(1 / 2 : ℝ) * (x i - center)

/-- The effective potential is minus the presence field, so its gradient has
the opposite sign. -/
def liftedHStageEffectiveGradient (center : ℝ) (x : CommonLayerState) :
    CommonLayerState := fun i => -liftedHStagePresenceGradient center x i

/-- Mobility two compensates for the factor one half in the normalized lifted
potential, preserving the original rate-one diagonal dynamics. -/
def liftedHStageMobility (v : CommonLayerState) : CommonLayerState := fun i => 2 * v i

def liftedHStageVectorField (center : ℝ) (x : CommonLayerState) :
    CommonLayerState := fun i =>
      -liftedHStageMobility (liftedHStageEffectiveGradient center x) i

theorem liftedHStageVectorField_formula (center : ℝ) (x : CommonLayerState) :
    liftedHStageVectorField center x = fun i => -(x i - center) := by
  funext i
  simp [liftedHStageVectorField, liftedHStageMobility,
    liftedHStageEffectiveGradient, liftedHStagePresenceGradient]

/-- The original exact scalar frozen orbit lifted diagonally solves the full
two-coordinate vector field at every real time. -/
def liftedHStageOrbit (center initial start t : ℝ) : CommonLayerState :=
  commonDiagonalAgentState
    (Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit center initial start t)

theorem liftedHStageOrbit_hasDerivAt
    (center initial start t : ℝ) :
    HasDerivAt (liftedHStageOrbit center initial start)
      (liftedHStageVectorField center
        (liftedHStageOrbit center initial start t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := Tomabechi.Examples.Theorem23B.hasDerivAt_quadraticFrozenOrbit
    center initial start t
  simpa [liftedHStageOrbit, commonDiagonalAgentState,
    liftedHStageVectorField_formula] using h

/-- C3のスカラー表象は、共通束の対角層の第一座標に一致する。 -/
theorem representation_eq_commonDiagonal_coordinate (n : ℕ) :
    representation (n : Atom) = (diagonalLayer n 0 : ℝ) := by
  simp [representation, diagonalLayer, layerRatio]

/-- 元H-stageの中心値は、共通束の対応Nat層の第一座標である。 -/
theorem hStageSequence_center_eq_commonDiagonal_coordinate (n : ℕ) :
    (hStageSequence n).center =
      (diagonalLayer (n + 1) 0 : ℝ) := by
  rw [hStageSequence_center, representation_eq_commonDiagonal_coordinate]

/-- 元H-stageの平均場が読む原子層を、同じ共通束上の層点へ送る。 -/
theorem hStageSequence_atomLayer_commonConcept (n : ℕ) :
    layerAddressEmbedding (((n + 1 : ℕ) : Atom)) = diagonalLayer (n + 1) := by
  change layerAddress (((n + 1 : ℕ) : WithTop ℕ)) = diagonalLayer (n + 1)
  exact layerAddress_nat (n + 1)

/-- H-stage中心のスカラーと、埋め込まれた原子層の座標は一致する。 -/
theorem hStageSequence_center_matches_embedded_atomLayer (n : ℕ) :
    (hStageSequence n).center =
      (layerAddressEmbedding (((n + 1 : ℕ) : Atom)) 0 : ℝ) := by
  rw [hStageSequence_center_eq_commonDiagonal_coordinate,
    hStageSequence_atomLayer_commonConcept]

/-- The original H-stage mean field agrees exactly with the lifted quadratic
potential when restricted to diagonal states. -/
theorem hStageSequence_meanField_matches_liftedPotential
    (n : ℕ) (x : ℝ) :
    (hStageSequence n).meanField x =
      liftedHStagePotential (hStageSequence n).center
        (commonDiagonalAgentState x) := by
  rw [liftedHStagePotential_on_diagonal]
  simp [hStageSequence, packageQuadraticStage,
    Tomabechi.Examples.Theorem23B.quadraticStage]

end

end Tomabechi.Consistency.R1
