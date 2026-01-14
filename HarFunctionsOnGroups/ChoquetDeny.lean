import HarFunctionsOnGroups.HarmonicPMF
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

lemma unif_bounded_diff (a : ℕ → ℝ) (b : ℝ) (abnd : ∃ C, ∀ n, |a n| ≤ C) (bpos : b ≥ 0) 
  (hdiff : ∀ n, (a (n + 1) - a n) ≥ b) : b = 0 := by
  by_contra bne0
  push_neg at bne0
  have bgt0 : b > 0 := Std.lt_of_le_of_ne bpos (id (Ne.symm bne0))
  have hbig : ∀ (n : ℕ), a n ≥ n * b + a 0 := by
    intro n
    induction n
    case zero =>
      simp
    case succ n ih =>
      calc
        a (n + 1) ≥ b + a n := le_sub_iff_add_le.mp (hdiff n)
        _ ≥ b + (n * b + a 0) := (add_le_add_iff_left b).mpr ih
        _ = (n + 1) * b + a 0 :=  by ring
      simp
  rcases abnd with ⟨C, abndC⟩
  have weird : ∀ (n : ℕ), n * b ≥ a 0 → |n * b + a 0| ≤ C := by
    intro n h1
    calc
      |n * b + a 0| ≤ |a n| := by sorry
      _ ≤ C := abndC n
  have bigN : ∃ (N : ℕ),  N * b ≥ max |a 0| (C - a 0) := by sorry
  rcases bigN with ⟨N, hN⟩
  specialize weird N
  sorry 


theorem ChoquetDeny {G : Type*} [AddCommGroup G] [TopologicalSpace G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hμreg : μ.Regular) (hfmeas : Measurable f)
(hfbnd : ∃ (C : ℝ), ∀ (x : G), |f x| ≤ C)
(hfint : ∀ (x : G), ∫ y, f (x + y) ∂μ = f x) : ∃ C, ∀ (x : G),f x = C := by
  set Φ := fun (r : G → ℝ) => (fun (x : G) => ∫ y, r (x + y) ∂μ) with hΦ
  have heq2 : Φ f = f := by
    rw [hΦ]
    dsimp
    ext x
    exact hfint x
  set g := fun (x : G) => ∫ (y : G), |(f x - f (x + y))| * |(f x - f (x + y))| ∂μ with hg
  have heq1 : ∀ (x : G), g x = ∫ (y : G), |f (x + y)| * |f (x + y)| ∂μ - |f (x)| * |f (x)| := by
    intro x
    rw [hg]
    dsimp
    simp only [abs_mul_abs_self]
    ring
    rw [MeasureTheory.integral_add]
    simp only [add_left_inj]
    rw [MeasureTheory.integral_add]
    simp
    sorry
    sorry
    sorry
    sorry
    sorry
  have hineq1 : ∀ (x : G), (Φ g) x ≥ g x := by sorry
  have gpos : ∀ (x : G), g x ≥ 0 := by sorry
  have h2 : ∀ (n : ℕ), ∀ (x : G), (Φ^[n+1] (fun (y : G) => |f y * f y|)) x - (Φ^[n] (|f * f|)) x ≥ g x := by sorry
  apply unif_bounded_diff g x at h2


  
    
    



theorem ChoquetDenyPMF {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [Countable G] (μ : PMF G) (f : G → ℝ)
(hhar : f ∈ BoundedHarmonicFunctions μ) (hgen : Subgroup.closure μ.support = G) :
∀ (x y : G), f x = f y := by sorry
