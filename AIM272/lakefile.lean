import Lake

set_option warningAsError true

open Lake DSL

package aim272

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib AIM272 where
  roots := #[`AIM272, `AIM272_Rational, `AIM272_NewLemmas, `AIM272_Conditional, `AIM272_Unusable,
    `AIM272_Witness, `AIM272_Affine, `AIM272_Translation, `AIM272_Geometry, `AIM272_Analytic,
    `AIM272_Model, `AIM272_Occupation, `AIM272_Tails, `AIM272_Directions, `AIM272_Levels,
    `AIM272_Targets, `AIM272_Descent, `AIM272_Potential, `AIM272_Stationary, `AIM272_Rates,
    `AIM272_Budgets, `AIM272_ReturnEstimate, `AIM272_ContinuousTime, `AIM272_LevelRange,
    `AIM272_RankedRace, `AIM272_RankPaths, `AIM272_Thinning, `AIM272_ClockObservation,
    `AIM272_Sampling, `AIM272_StoppedExcursion, `AIM272_ActualSampling, `AIM272_Main,
    `AIM272_ClockResolvent, `AIM272_ClockStop, `AIM272_ClockBalance, `AIM272_LocalBarrier,
    `AIM272_LocalComparison, `AIM272_ShellBudget, `AIM272_Glued, `AIM272_Factorial, `AIM272_FiniteClasses]
