import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.CDF
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Set.Lattice
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

noncomputable section

open MeasureTheory Measure Set

namespace ErgodicDecomposition

variable {X ι : Type*} [MeasurableSpace X]

def IsMeasurablePartition {P : ι → Set X} (hP : IndexedPartition P) : Prop :=
  ∀ i, MeasurableSet (P i)

def quotientMeasurableSpace {P : ι → Set X} {hP : IndexedPartition P}
  (hMP : IsMeasurablePartition hP) : MeasurableSpace ι :=
  MeasurableSpace.map (hP.index) ‹MeasurableSpace X›

def Disintegration (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
  {P : ι → (Set X)} {hP : IndexedPartition P} (hMP : IsMeasurablePartition hP)
  (disint : ι → MeasureTheory.ProbabilityMeasure X) :
  Prop :=
  letI : MeasurableSpace ι := quotientMeasurableSpace hMP
  let μ' := Measure.map hP.index μ
  (∀ (i : ι), (disint i).toMeasure (P i) = 1) ∧
  (∀ (A : Set X), MeasurableSet A → Measurable (fun i => (disint i).toMeasure A)) ∧
  (∀ (A : Set X), MeasurableSet A → μ A = ∫⁻ i, (disint i : Measure X) A ∂μ')

lemma Monotone_map.Iic {A : Type*} [Nonempty A] [LinearOrder A]
  {f : A → A} (hmon : StrictMono f) {g : A → A}
  (hrinv : g.RightInverse f) (x : A) :
  f⁻¹' (Iic x) = Iic (g x) := by
  ext y; simp only [mem_preimage, mem_Iic]
  constructor
  · intro h
    by_contra h'; push_neg at h'
    apply hmon at h';
    rw [hrinv x] at h'; grind
  · intro h
    apply (StrictMono.monotone hmon) at h
    exact le_of_le_of_eq h (hrinv x)

--credit to Aaron Liu
lemma GaloisConnection.preimage_Iic {α β : Type*} [Preorder α] [Preorder β]
    {l : α → β} {u : β → α} (h : GaloisConnection l u) (x : β) :
    l ⁻¹' (Iic x) = Iic (u x) :=
  Set.ext fun y => h y x

theorem CDF_map {f : ℝ → ℝ} (hmon : StrictMono f) {μ : Measure ℝ}
  {g : ℝ → ℝ} (hrinv : g.RightInverse f) [IsProbabilityMeasure μ] :
  ProbabilityTheory.cdf (μ.map f) = (ProbabilityTheory.cdf μ) ∘ g := by
  ext y; simp only [Function.comp_apply];
  have hprobmap : IsProbabilityMeasure (μ.map f) := by
    apply Measure.isProbabilityMeasure_map
    apply Measurable.aemeasurable;
    exact Monotone.measurable (StrictMono.monotone hmon)
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  refine (measureReal_eq_measureReal_iff ?_ ?_).mpr ?_
  · exact measure_ne_top (map f μ) (Iic y)
  · exact measure_ne_top μ (Iic (g y))
  · rw [μ.map_apply]
    · congr
      exact Monotone_map.Iic hmon hrinv y
    · apply StrictMono.monotone at hmon
      exact Monotone.measurable hmon
    · exact measurableSet_Iic

example (μ : Measure (Set.Icc (0 : ℝ) 1)) [IsProbabilityMeasure μ] :
  MeasurePreserving (fun (y : Set.Icc (0 : ℝ) 1) => y^2) μ μ →
  ∃ (a b : ENNReal), μ = a • (Measure.dirac 0) + b • (Measure.dirac 1) := by
  intro hpres
  have hpres2 : Measure.map (fun (y : Icc (0 : ℝ) 1) => y^2) μ = μ := hpres.map_eq
  have vanish1 : ∀ (a b : Icc 0 1), μ (Icc a b) = 0 := by sorry
  use (μ ({0}))
  use (μ ({1}))
  have vanish2 : μ (Ioo 0 1) = 0 := by sorry
  have interm1 : μ {0,1} = 1 := by sorry
  sorry

end ErgodicDecomposition
