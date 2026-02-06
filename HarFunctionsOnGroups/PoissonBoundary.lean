import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Function.LpSpace.Basic

noncomputable section

structure MeasuredGroup {G : Type*} [Group G] [TopologicalSpace G] [IsDiscrete G]
[MeasurableSpace G] [BorelSpace G] where
  prob : (μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
