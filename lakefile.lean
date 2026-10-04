import Lake
open Lake DSL

package tomabechi_theory

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

lean_lib Tomabechi where
  srcDir := "."
  roots := #[`Theorem1, `Theorem2, `Theorem3, `Theorem4, `Theorem1_4_HFlow, `Theorem19, `Theorem19_22, `Theorem19_Heterogeneous, `Theorem20, `Theorem21, `Theorem21_Model, `Theorem22, `Theorem23, `Theorem15,
    `Theorem15_23,
    `Theorem24_26, `Theorem24_26_27, `Theorem24_26_Model,
    `Theorem24_26_ControlledModel, `Theorem24_26_LinearFamily,
    `Theorem24_26_GainControl, `Theorem27, `Theorem16_25, `Theorem21_P13,
    `Theorem16_25_Core, `Theorem16_25_Model,
    `Tomabechi.Analysis.EntropyBalance, `Tomabechi.Information.Capacity,
    `Tomabechi.Analysis.StrongConvexity,
    `Tomabechi.Dynamics.GradientFlow,
    `Tomabechi.Dynamics.GlobalFlow,
    `Tomabechi.Dynamics.Theorem21GlobalResults,
    `Tomabechi.Theorem27.Abstract,
    `Tomabechi.Theorem27.Actuator,
    `Tomabechi.Theorem27.Connection,
    `Tomabechi.Information.MeanFieldDirectCMI,
    `Tomabechi.Information.FiniteCMI,
    `Tomabechi.Information.FiniteMeasureEntropy,
    `Tomabechi.Information.DeterministicOutput,
    `Tomabechi.Information.MeasureCMI,
    `Tomabechi.Information.MeasureCMICapacity,
    `Tomabechi.Dynamics.StageData,
    `Tomabechi.Dynamics.InvariantRegion,
    `Tomabechi.Dynamics.StageSwitching,
    `Tomabechi.Dynamics.MeanFieldReconstruction,
    `Tomabechi.Counterexamples.DecoderRegularity,
    `Theorem19_Counterexample, `Theorem22_InvariantRegion,
    `Theorem22_InvariantRegion_P13,
    `Theorem23_InvariantRegion, `Theorem22_InvariantRegion_Model,
    `Econlib.Math.Combinatorics.FreudenthalTriangulation,
    `Econlib.Math.Combinatorics.CubicalSperner,
    `Econlib.Math.Topology.ConvexHomeomorph, `Econlib.Math.Topology.Brouwer,
    `Econlib.Math.Topology.Kakutani,
    `Econlib.Math.Topology.FanGlicksberg,
    `Tomabechi.Examples.Theorem23B_QuadraticStages,
    `Tomabechi.Examples.Theorem22_GaussianStages,
    `Tomabechi.Examples.Theorem26_ValueZeroSet, `Tomabechi.Examples.Theorem26_RingModel, `Tomabechi.Examples.Theorem22_HStage,
    `Tomabechi.Examples.Theorem25_NoSelf, `Tomabechi.Examples.Theorem27_AvijjaSankhara, `Tomabechi.Examples.Theorem27_Operational, `Tomabechi.Examples.Theorem26_27_ControlClasses,
    `Tomabechi.Examples.Theorem16_Identity, `Tomabechi.Examples.Theorem20_SymbolicPresence, `Tomabechi.Examples.Theorem15_EntropyExchange, `Tomabechi.Examples.Theorem23_Impermanence, `Tomabechi.Examples.Gaussian, `Tomabechi.Examples.Theorem22_LubStaircase, `Tomabechi.Examples.Theorem4_PresenceWeight, `Tomabechi.Examples.Theorem24_Tracking, `Tomabechi.Examples.Theorem21_GaussianValley, `Tomabechi.Examples.Theorem19_FreeWillCapacity, `Tomabechi.Examples.Theorem16_Tower, `Tomabechi.Examples.Theorem16_TowerLayers, `Tomabechi.Examples.Theorem1_DoubleWell, `Tomabechi.Examples.Theorem3_LubConsensus, `Tomabechi.Examples.Theorem2_SharedTCZ, `Tomabechi.Examples.Theorem2_SubgradientFlow, `Tomabechi.Examples.Theorem15_A6Failure,
    `theorem1_example, `Theorem1_Model]
