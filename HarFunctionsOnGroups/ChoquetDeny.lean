import HarFunctionsOnGroups.HarmonicPMF
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

-- Lemma : if a bounded sequence has differences of consequtive elements
-- bounded from below by a non-negative b then b = 0
lemma unif_bounded_diff (a : ℕ → ℝ) (b : ℝ) (abnd : ∃ C, ∀ n, |a n| ≤ C)
(bpos : b ≥ 0) (hdiff : ∀ n, (a (n + 1) - a n) ≥ b) : b = 0 := by
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
  contrapose! abndC
  let N := Nat.ceil ((|C| + |a 0|) / b) + 1
  use N
  specialize hbig N
  calc
    C ≤ |C| := le_abs_self C
    _ ≤ |C| + (|a 0| + a 0) := by
      simp only [le_add_iff_nonneg_right]
      refine neg_le_iff_add_nonneg.mp ?_
      exact neg_le_abs (a 0)
    _ = (|C| + |a 0|) + a 0 := by ring
    _ = ((|C| + |a 0|) / b) * b + a 0 := by
      simp only [add_left_inj]
      exact Eq.symm (div_mul_cancel₀ (|C| + |a 0|) bne0)
    _ ≤ (N - 1) * b + a 0 := by
      simp only [add_le_add_iff_right]
      unfold N
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      rw [mul_le_mul_iff_left₀ bgt0]
      exact Nat.le_ceil ((|C| + |a 0|) / b)
    _ < N * b + a 0 := by
      simp only [add_lt_add_iff_right]
      rw [mul_lt_mul_iff_left₀ bgt0]
      simp only [sub_lt_self_iff, zero_lt_one]
    _ ≤ a N := RCLike.ofReal_le_ofReal.mp hbig
    _ ≤ |a N| := by exact le_abs_self (a N)

lemma fxy_is_integrable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hfmeas : Measurable f) (C : ℝ)
(hfbnd : ∀ (x : G), |f x| ≤ C) :
∀ (x : G), MeasureTheory.Integrable (fun y => (f (x + y))) μ := by
  intro x
  apply MeasureTheory.Integrable.mono (MeasureTheory.integrable_const (C : ℝ)) _ _
  · apply Measurable.aestronglyMeasurable
    apply Measurable.comp' hfmeas _
    apply Continuous.measurable
    exact continuous_add_left x
  · apply MeasureTheory.ae_of_all μ _
    intro a
    simp only [Real.norm_eq_abs]
    trans C
    · exact hfbnd (x + a)
    exact le_abs_self C


lemma fxya_is_integrable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hfmeas : Measurable f) (C : ℝ)
(hfbnd : ∀ (x : G), |f x| ≤ C) :
∀ (x a : G), MeasureTheory.Integrable (fun y => (f (x + y + a))) μ := by
  intro x a
  apply MeasureTheory.Integrable.mono (MeasureTheory.integrable_const (C : ℝ)) _ _
  · apply Measurable.aestronglyMeasurable
    apply Measurable.comp' hfmeas _
    apply Continuous.measurable
    exact Continuous.comp (continuous_add_right a) (continuous_add_left x)
  · apply MeasureTheory.ae_of_all μ _
    intro a₁
    simp only [Real.norm_eq_abs]
    trans C
    · exact hfbnd (x + a₁ + a)
    exact le_abs_self C


lemma fxy2_is_integrable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hfmeas : Measurable f) (C : ℝ)
(hfbnd : ∀ (x : G), |f x| ≤ C) :
∀ (x : G), MeasureTheory.Integrable (fun y => (f (x + y))^2) μ := by
  intro x
  simp only [sq]
  apply MeasureTheory.Integrable.mono (MeasureTheory.integrable_const (C*C : ℝ)) _ _
  · apply MeasureTheory.AEStronglyMeasurable.mul _ _
    repeat
    · apply Measurable.aestronglyMeasurable
      apply Measurable.comp' hfmeas _
      apply Continuous.measurable
      exact continuous_add_left x
  · apply MeasureTheory.ae_of_all μ _
    intro a
    simp only [norm_mul, Real.norm_eq_abs]
    calc
      |f (x + a)| * |f (x + a)| = |f (x + a)|^2 := Eq.symm (pow_two |f (x + a)|)
      _ ≤ |C|^2 := by
        rw [sq_le_sq]
        simp only [abs_abs]
        trans C
        · exact hfbnd (x + a)
        exact le_abs_self C
      _ = |C| * |C| := by exact pow_two |C|

lemma fxydiff_is_measurable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(f : G → ℝ) (hfmeas : Measurable f) : ∀ (x z : G),
Measurable (fun x_1 ↦ (f (x + x_1) - f (x + x_1 + z))) := by
  intro x z
  apply Measurable.sub _ _
  · apply Measurable.comp' hfmeas _
    apply Continuous.measurable
    exact continuous_add_left x
  · apply Measurable.comp' hfmeas _
    apply Continuous.measurable
    exact Continuous.comp (continuous_add_right z) (continuous_add_left x)

lemma fxydiffprod_is_integrable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hfmeas : Measurable f) (C : ℝ)
(hfbnd : ∀ (x : G), |f x| ≤ C) : ∀ (x z : G), MeasureTheory.Integrable
  (fun x_1 ↦ (f (x + x_1) - f (x + x_1 + z)) * (f (x + x_1) - f (x + x_1 + z))) μ := by
  intro x z
  apply MeasureTheory.Integrable.mono (MeasureTheory.integrable_const (4*C*C : ℝ)) _ _
  · apply MeasureTheory.AEStronglyMeasurable.mul _ _
    repeat
    · apply Measurable.aestronglyMeasurable
      exact fxydiff_is_measurable f hfmeas x z
  · apply MeasureTheory.ae_of_all μ _
    intro a; simp only [norm_mul, Real.norm_eq_abs, abs_mul_abs_self]
    calc
      (f (x + a) - f (x + a + z)) * (f (x + a) - f (x + a + z))
        = (f (x + a) - f (x + a + z))^2 := by
        exact Eq.symm (pow_two (f (x + a) - f (x + a + z)))
      _ ≤ (|f (x + a)| + |f (x + a + z)|)^2 := by
        rw [sq_le_sq]
        trans |f (x + a)| + |f (x + a + z)|
        · exact abs_sub (f (x + a)) (f (x + a + z))
        exact le_abs_self (|f (x + a)| + |f (x + a + z)|)
      _ ≤ (2 * |C|)^2 := by
        rw [sq_le_sq, abs_of_nonneg];
        simp only [abs_mul, Nat.abs_ofNat, abs_abs]
        trans C + C
        · exact add_le_add (hfbnd (x + a)) (hfbnd (x + a + z))
        trans |C| + |C|
        · ring; simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀];
          exact le_abs_self C
        ring; rfl
        exact add_nonneg (abs_nonneg (f (x +a ))) (abs_nonneg (f (x + a + z)))
      _ = 4 * |C| * |C| := by ring
      _ = |4| * |C| * |C| := by simp only [Nat.abs_ofNat]

lemma fxydiff2prod_is_integrable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hfmeas : Measurable f) (C : ℝ)
(hfbnd : ∀ (x : G), |f x| ≤ C) : ∀ (x : G), MeasureTheory.Integrable
  (fun x_1 ↦ (f x - f (x + x_1)) * (f x - f (x + x_1))) μ := by
  intro x
  apply MeasureTheory.Integrable.mono (MeasureTheory.integrable_const (4*C*C : ℝ)) _ _
  · apply MeasureTheory.AEStronglyMeasurable.mul _ _
    repeat
    · apply Measurable.aestronglyMeasurable
      apply Measurable.sub
      · exact measurable_const
      · apply Measurable.comp' hfmeas _
        exact measurable_const_add x
  · apply MeasureTheory.ae_of_all μ _
    intro a; simp only [norm_mul, Real.norm_eq_abs, abs_mul_abs_self]
    calc
      (f (x) - f (x + a)) * (f (x) - f (x + a))
        = (f (x) - f (x + a))^2 := by
        exact Eq.symm (pow_two (f (x) - f (x + a)))
      _ ≤ (|f (x)| + |f (x + a)|)^2 := by
        rw [sq_le_sq]
        trans |f (x)| + |f (x + a)|
        · exact abs_sub (f (x)) (f (x + a))
        exact le_abs_self (|f (x)| + |f (x + a)|)
      _ ≤ (2 * |C|)^2 := by
        rw [sq_le_sq, abs_of_nonneg];
        simp only [abs_mul, Nat.abs_ofNat, abs_abs]
        trans C + C
        · exact add_le_add (hfbnd (x)) (hfbnd (x + a))
        trans |C| + |C|
        · ring; simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀];
          exact le_abs_self C
        ring; rfl
        exact add_nonneg (abs_nonneg (f (x))) (abs_nonneg (f (x + a)))
      _ = 4 * |C| * |C| := by ring
      _ = |4| * |C| * |C| := by simp only [Nat.abs_ofNat]

lemma intoffxydiffprod_is_integrable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hfmeas : Measurable f) (C : ℝ)
(hfbnd : ∀ (x : G), |f x| ≤ C) : ∀ (x : G), MeasureTheory.Integrable
  (fun x_1 ↦ (∫ (z : G), (f (x + z) - f (x + z + x_1)) * (f (x + z) - f (x + z + x_1)) ∂μ)) μ := by
  intro x
  apply MeasureTheory.Integrable.mono (MeasureTheory.integrable_const (4*C*C : ℝ)) _ _
  · have interm : MeasureTheory.AEStronglyMeasurable
      (fun (z : G × G) => (f (x + z.2) - f (x + z.2 + z.1))*(f (x + z.2) - f (x + z.2 + z.1)))
        (μ.prod μ):= by
      apply MeasureTheory.AEStronglyMeasurable.mul _ _
      repeat
      · apply MeasureTheory.AEStronglyMeasurable.sub _ _
        · apply Measurable.aestronglyMeasurable
          apply Measurable.comp' hfmeas _
          apply Continuous.measurable
          apply Continuous.comp (continuous_add_left x) continuous_snd
        · apply Measurable.aestronglyMeasurable
          apply Measurable.comp' hfmeas _
          apply Continuous.measurable
          simp only [add_assoc]
          apply Continuous.comp (continuous_add_left x) _
          apply Continuous.add (continuous_snd) (continuous_fst)
    apply MeasureTheory.AEStronglyMeasurable.integral_prod_right' interm
  · apply MeasureTheory.ae_of_all μ _
    intro a
    simp only [Real.norm_eq_abs, norm_mul]
    rw [abs_le]
    constructor
    · calc
        -(|4| * |C| * |C|) = -(4 * |C| * |C|) := by simp
        _ = - (∫ (z : G), (4 * |C| * |C|) ∂ μ) := by
          rw [MeasureTheory.integral_const (4 * |C| * |C|)]
          simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul]
        _ = (∫ (z : G), -(4 * |C| * |C|) ∂ μ) := by
          rw [MeasureTheory.integral_neg _]
        _ ≤ ∫ (z : G), (f (x + z) - f (x + z + a)) * (f (x + z) - f (x + z + a)) ∂μ := by
          apply MeasureTheory.integral_mono
            (MeasureTheory.integrable_const (-(4 * |C| * |C|) : ℝ)) _
          · intro y; dsimp
            rw [neg_le]
            trans (2 * |C|) * (2 * |C|)
            · calc
                -((f (x + y) - f (x + y + a)) * (f (x + y) - f (x + y + a))) =
                 - (f (x + y + a) - f (x + y))^2 := by ring
                _ ≤ (f (x + y + a) - f (x + y))^2 := by
                  simp only [neg_le_self_iff]
                  exact sq_nonneg (f (x + y + a) - f (x + y))
                _ ≤ (2 * |C|)^2 := by
                  rw [sq_le_sq]
                  simp only [abs_mul, Nat.abs_ofNat, abs_abs]
                  trans |f (x + y + a)| + |f (x + y)|
                  · exact abs_sub (f (x + y + a)) (f (x + y))
                  trans C + C
                  · exact add_le_add (hfbnd (x + y + a)) (hfbnd (x + y))
                  ring; simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
                  exact le_abs_self C
                _ = (2 * |C|) * (2 * |C|) := pow_two (2 * |C|)
            ring; rfl
          · exact fxydiffprod_is_integrable μ f hfmeas C hfbnd x a
    · calc
        ∫ (z : G), (f (x + z) - f (x + z + a)) * (f (x + z) - f (x + z + a)) ∂μ ≤
          (∫ (z : G), (4 * |C| * |C|) ∂ μ) := by
          apply MeasureTheory.integral_mono _
            (MeasureTheory.integrable_const (4 * |C| * |C|))
          · intro y; dsimp
            calc
              (f (x + y) - f (x + y + a)) * (f (x + y) - f (x + y + a))
                = (f (x + y) - f (x + y + a))^2 := by
                exact Eq.symm (pow_two (f (x + y) - f (x + y + a)))
              _ ≤ (|f (x + y)| + |f (x + y + a)|)^2 := by
                rw [sq_le_sq]
                trans |f (x + y)| + |f (x + y + a)|
                · exact abs_sub (f (x + y)) (f (x + y + a))
                exact le_abs_self (|f (x + y)| + |f (x + y + a)|)
              _ ≤ (2 * |C|)^2 := by
                rw [sq_le_sq, abs_of_nonneg];
                simp only [abs_mul, Nat.abs_ofNat, abs_abs]
                trans C + C
                · exact add_le_add (hfbnd (x + y)) (hfbnd (x + y + a))
                trans |C| + |C|
                · ring; simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀];
                  exact le_abs_self C
                ring; rfl
                exact add_nonneg (abs_nonneg (f (x + y))) (abs_nonneg (f (x + y + a)))
              _ = 4 * |C| * |C| := by ring
          · exact fxydiffprod_is_integrable μ f hfmeas C hfbnd x a
        _ = 4 * |C| * |C| := by
          rw [MeasureTheory.integral_const (4 * |C| * |C|)]
          simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul]
        _ = |4| * |C| * |C| := by simp

lemma intoffxydiffsqis_integrable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hfmeas : Measurable f) (C : ℝ)
(hfbnd : ∀ (x : G), |f x| ≤ C) : ∀ (x : G), MeasureTheory.Integrable
  (fun x_1 ↦ ((∫ (z : G),
    (f (x + z) - f (x + z + x_1)) ∂ μ) * ∫ (z : G), (f (x + z) - f (x + z + x_1)) ∂μ)) μ := by
  intro x
  apply MeasureTheory.Integrable.mono (MeasureTheory.integrable_const (4*C*C : ℝ)) _ _
  · apply MeasureTheory.AEStronglyMeasurable.mul _ _
    repeat
    · have interm : MeasureTheory.AEStronglyMeasurable
        (fun (z : G × G) => f (x + z.2) - f (x + z.2 + z.1)) (μ.prod μ):= by
        apply MeasureTheory.AEStronglyMeasurable.sub _ _
        · apply Measurable.aestronglyMeasurable
          apply Measurable.comp' hfmeas _
          apply Continuous.measurable
          apply Continuous.comp (continuous_add_left x) continuous_snd
        · apply Measurable.aestronglyMeasurable
          apply Measurable.comp' hfmeas _
          apply Continuous.measurable
          simp only [add_assoc]
          apply Continuous.comp (continuous_add_left x) _
          apply Continuous.add (continuous_snd) (continuous_fst)
      apply MeasureTheory.AEStronglyMeasurable.integral_prod_right' interm
  · apply MeasureTheory.ae_of_all (μ) _
    intro a
    simp only [norm_mul, Real.norm_eq_abs, abs_mul_abs_self]
    calc
      (∫ (z : G), f (x + z) - f (x + z + a) ∂μ) * (∫ (z : G), f (x + z) - f (x + z + a) ∂μ) =
      (∫ (z : G), f (x + z) - f (x + z + a) ∂μ)^2 := by
        simp only [sq]
      _ ≤ (∫ (z : G), 2 * |C| ∂μ)^2 := by
        rw [sq_le_sq]
        rw [abs_le]
        constructor
        · rw [abs_of_nonneg (by rw [MeasureTheory.integral_const (2 * |C|)]; simp)]
          rw [← MeasureTheory.integral_neg]
          apply MeasureTheory.integral_mono (MeasureTheory.integrable_const (-(2*|C|) : ℝ))
          · exact MeasureTheory.Integrable.sub
              (fxy_is_integrable μ f hfmeas C hfbnd x)
              (fxya_is_integrable μ f hfmeas C hfbnd x a)
          · intro y; dsimp
            calc
              -(2*|C|) ≤ (-C) + (-C) := by
                ring; simp only [neg_le_neg_iff, Nat.ofNat_pos, mul_le_mul_iff_left₀];
                exact le_abs_self C
              _ ≤ -|f (x + y)| - |f (x + y + a)| := by
                apply add_le_add
                · rw [neg_le]
                  simp only [neg_neg]; exact hfbnd (x + y)
                · rw [neg_le]; simp only [neg_neg]
                  exact hfbnd (x + y + a)
              _ ≤ f (x + y) - f (x + y + a) := by
                apply add_le_add
                · rw [neg_le]; exact neg_le_abs (f (x + y))
                · rw [neg_le]; simp only [neg_neg]; exact le_abs_self (f (x + y + a))
        · rw [abs_of_nonneg (by rw [MeasureTheory.integral_const (2 * |C|)]; simp)]
          apply MeasureTheory.integral_mono _ (MeasureTheory.integrable_const (2*|C| : ℝ))
          · intro y; dsimp
            calc
              f (x + y) - f (x + y + a) ≤ |f (x + y)| + |f (x + y + a)| := by
                exact add_le_add (le_abs_self (f (x + y))) (neg_le_abs (f (x + y + a)))
              _ ≤ C + C := by
                exact add_le_add (hfbnd (x + y)) (hfbnd (x + y + a))
              _ ≤ |C| + |C| := by
                ring; simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀];
                exact le_abs_self C
              _ = 2 * |C| := by ring
          · exact MeasureTheory.Integrable.sub (fxy_is_integrable μ f hfmeas C hfbnd x)
              (fxya_is_integrable μ f hfmeas C hfbnd x a)
      _ = (2 * |C|)^2 := by
        congr
        rw [MeasureTheory.integral_const (2 * |C|)]
        simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul]
      _ = 4 * |C| * |C| := by ring
      _ = |4| * |C| * |C| := by
        simp only [Nat.abs_ofNat]



lemma shift_operator_preserves_meas {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hfmeas : Measurable f) : Measurable (fun (x : G) => ∫ (y : G), f (x + y) ∂μ) := by
  rw [<- stronglyMeasurable_iff_measurable]
  rw [<- stronglyMeasurable_iff_measurable] at hfmeas
  apply MeasureTheory.StronglyMeasurable.integral_prod_left
  apply MeasureTheory.StronglyMeasurable.comp_measurable hfmeas _
  apply Continuous.measurable
  simp only [add_comm]
  apply Continuous.add (continuous_fst) (continuous_snd)

lemma shift_operator_bounded {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (C : ℝ) (hfmeas : Measurable f) (hfbnd : ∀ (x : G), |f x| ≤ C) :
∀ (x : G), |∫ (y : G), f (x + y) ∂μ| ≤ C := by
  intro x
  rw [abs_le]
  constructor
  · calc
    -C = ∫ (y : G), -C ∂μ := by
      rw [MeasureTheory.integral_const (-C)]
      simp
    _ ≤ ∫ (y : G), f (x + y) ∂μ := by
      apply MeasureTheory.integral_mono
      · exact MeasureTheory.integrable_const (-C)
      · exact fxy_is_integrable μ f hfmeas C hfbnd x
      · intro y; dsimp
        exact (abs_le.mp (hfbnd (x + y))).1
  · calc
    ∫ (y : G), f (x + y) ∂μ ≤ ∫ (y : G), C ∂μ := by
      apply MeasureTheory.integral_mono
      · exact fxy_is_integrable μ f hfmeas C hfbnd x
      · exact MeasureTheory.integrable_const C
      · intro y; dsimp
        exact (abs_le.mp (hfbnd (x + y))).2
    _ = C := by
      rw [MeasureTheory.integral_const C]
      simp

lemma shift_operator_is_monotone {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f₁ f₂ : G → ℝ) (hf₁meas : Measurable f₁) (hf₂meas : Measurable f₂)
(hf₁bnd : ∃ (C : ℝ), ∀ (x : G), |f₁ x| ≤ C) (hf₂bnd : ∃ (C : ℝ), ∀ (x : G), |f₂ x| ≤ C)
(hge : ∀ (x : G), f₁ x ≤ f₂ x) :
∀ (x : G), ∫ (y : G), f₁ (x + y) ∂μ ≤ ∫ (y : G), f₂ (x + y) ∂μ := by
  intro x
  rcases hf₁bnd with ⟨C₁, hf₁bndC⟩
  rcases hf₂bnd with ⟨C₂, hf₂bndC⟩
  apply MeasureTheory.integral_mono
  · exact fxy_is_integrable μ f₁ hf₁meas C₁ hf₁bndC x
  · exact fxy_is_integrable μ f₂ hf₂meas C₂ hf₂bndC x
  · exact Pi.le_def.mpr fun i ↦ hge (x + i)

lemma gismeasurable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hfmeas : Measurable f) :
Measurable (fun x ↦ ∫ (y : G), (f x - f (x + y)) * (f x - f (x + y)) ∂μ) := by
  have interm : MeasureTheory.StronglyMeasurable
    (fun (z : G × G) => (f (z.1) - f (z.1 + z.2)) * (f (z.1) - f (z.1 + z.2))):= by
    apply MeasureTheory.StronglyMeasurable.mul _ _
    · apply Measurable.stronglyMeasurable
      apply Measurable.sub
      · apply Measurable.comp' hfmeas _
        apply Continuous.measurable
        exact continuous_fst
      · apply Measurable.comp' hfmeas _
        apply Continuous.measurable
        exact Continuous.add (continuous_fst) (continuous_snd)
    · apply Measurable.stronglyMeasurable
      apply Measurable.sub
      · apply Measurable.comp' hfmeas _
        apply Continuous.measurable
        exact continuous_fst
      · apply Measurable.comp' hfmeas _
        apply Continuous.measurable
        exact Continuous.add (continuous_fst) (continuous_snd)
  exact stronglyMeasurable_iff_measurable.mp
    (MeasureTheory.StronglyMeasurable.integral_prod_right' interm)

theorem ChoquetDeny {G : Type*} [AddCommGroup G] [TopologicalSpace G]
[SecondCountableTopology G] [MeasurableSpace G]
[BorelSpace G] [IsTopologicalAddGroup G]
(μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
(f : G → ℝ) (hμreg : μ.Regular) (hfmeas : Measurable f)
(hfbnd : ∃ (C : ℝ), ∀ (x : G), |f x| ≤ C)
(hfint : ∀ (x : G), ∫ y, f (x + y) ∂μ = f x) : ∀ (x : G), ∀ᵐ (y : G) ∂μ, f x = f (x + y) := by
  set Φ := fun (r : G → ℝ) => (fun (x : G) => ∫ y, r (x + y) ∂μ) with hΦ
  rcases hfbnd with ⟨C, hfbndC⟩
  have heq2 : Φ f = f := by
    rw [hΦ]
    dsimp
    ext x
    exact hfint x
  set g := fun (x : G) => ∫ (y : G), (f x - f (x + y)) * (f x - f (x + y)) ∂μ with hg
  have hint0 : ∀ (x : G), MeasureTheory.Integrable (fun y => f (x + y)) μ :=
    fxy_is_integrable μ f hfmeas C hfbndC
  have heq1 : ∀ (x : G), g x = ∫ (y : G), f (x + y) * f (x + y) ∂μ - (f (x)) * (f (x)) := by
    intro x
    rw [hg]
    dsimp
    ring_nf
    have hint1 : ∀ (x : G), MeasureTheory.Integrable (fun y => (f x)^2) μ := by
      exact fun x ↦ MeasureTheory.integrable_const (f x ^ 2)
    have hint2 : ∀ (x : G), MeasureTheory.Integrable (fun y => (f (x + y))^2) μ :=
      fxy2_is_integrable μ f hfmeas C hfbndC
    have hint3 : ∀ (x : G), MeasureTheory.Integrable (fun y => -(f x * f (x + y) * 2)) μ := by
      intro x
      apply MeasureTheory.Integrable.neg
      simp only [mul_assoc]
      apply MeasureTheory.Integrable.smul (f x)
      exact MeasureTheory.Integrable.mul_const (hint0 x) 2
    have hint4 : ∀ (x : G),
    MeasureTheory.Integrable (fun y => -(f x * f (x + y) * 2) + (f x)^2) μ := by
      intro x
      exact MeasureTheory.Integrable.add (hint3 x) (hint1 x)
    rw [MeasureTheory.integral_add (hint4 x) (hint2 x)]
    simp only [add_left_inj]
    rw [MeasureTheory.integral_add (hint3 x) (hint1 x)]
    simp only [MeasureTheory.integral_const, MeasureTheory.probReal_univ,
    smul_eq_mul, one_mul]
    have hsimpl : ∫ (a : G), -(f x * f (x + a) * 2) ∂μ = - (f x * 2) * (f x) := by
      calc
        ∫ (a : G), -(f x * f (x + a) * 2) ∂μ = ∫ (a : G), (-(f x) * 2) * (f (x + a)) ∂μ := by
          congr
          ext a
          ring
        _ = (-(f x) * 2) * ∫ (a : G), f (x + a)  ∂μ :=
          MeasureTheory.integral_const_mul ((-f x) * 2) (fun a ↦ f (x + a))
        _ = (-(f x) * 2) * (f x) :=
          Real.ext_cauchy (congrArg Real.cauchy (congrArg (HMul.hMul (-f x * 2)) (hfint x)))
        _ = - (f x * 2) * (f x) := by ring
    rw [hsimpl]
    ring
  have hineq1 : ∀ (x : G), (Φ g) x ≥ g x := by
    intro x
    calc
      (Φ g) x = ∫ (z : G), g (x + z) ∂μ := by rw [hΦ]
      _ = ∫ (z : G), (∫ (y : G), (f (x + z) - f (x + z + y))^2 ∂μ) ∂μ := by
        rw [hg]
        dsimp
        simp only [sq]
      _ = ∫ (y : G), (∫ (z : G), (f (x + z) - f (x + z + y))^2 ∂μ) ∂μ := by
        rw [MeasureTheory.integral_integral_swap]
        apply MeasureTheory.Integrable.mono (MeasureTheory.integrable_const (4*C*C : ℝ)) _ _
        · simp only [sq]
          apply MeasureTheory.AEStronglyMeasurable.mul _ _
          repeat
          · apply Measurable.aestronglyMeasurable
            apply Measurable.sub
            · apply Measurable.comp' hfmeas _
              -- This is the only place we need second countable G (???)
              apply Continuous.measurable
              apply Continuous.comp (continuous_add_left x) continuous_fst
            · apply Measurable.comp' hfmeas _
              apply Continuous.measurable
              simp only [add_assoc]
              apply Continuous.comp (continuous_add_left x) _
              apply Continuous.add (continuous_fst) (continuous_snd)
        · apply MeasureTheory.ae_of_all (μ.prod μ) _
          intro a
          simp only [Real.norm_eq_abs, norm_mul]
          calc
            |Function.uncurry (fun z y ↦ (f (x + z) - f (x + z + y)) ^ 2) a| =
            |(f (x + a.1) - f (x + a.1 + a.2))^2| := by exact
              (sq_eq_sq_iff_abs_eq_abs
                    (Function.uncurry (fun z y ↦ (f (x + z) - f (x + z + y)) ^ 2) a)
                    ((f (x + a.1) - f (x + a.1 + a.2)) ^ 2)).mp rfl
            _ = |(f (x + a.1) - f (x + a.1 + a.2))|^2 :=
              Eq.symm (pow_abs (f (x + a.1) - f (x + a.1 + a.2)) 2)
            _ ≤ (|C| + |C|)^2 := by
              rw [sq_le_sq]
              simp only [abs_abs]
              trans |f (x + a.1)| + |f (x + a.1 + a.2)|
              · apply abs_sub (f (x + a.1)) (f (x + a.1 + a.2))
              trans C + C
              · exact add_le_add (hfbndC (x + a.1)) (hfbndC (x + a.1 + a.2))
              trans |C| + |C|
              · exact add_le_add (le_abs_self C) (le_abs_self C)
              exact le_abs_self (|C| + |C|)
            _ = |4| * |C| * |C| := by
              ring
      _ = ∫ (y : G), (∫ (z : G), (f (x + z) - f (x + z + y)) *
            (f (x + z) - f (x + z + y)) ∂μ) ∂μ := by
        simp only [sq]
      _ ≥ ∫ (y : G), (∫ (z : G), f (x + z) - f (x + z + y) ∂μ) *
            (∫ (z : G), f (x + z) - f (x + z + y) ∂μ) ∂μ := by
        apply MeasureTheory.integral_mono
        · exact intoffxydiffsqis_integrable μ f hfmeas C hfbndC x
        · exact intoffxydiffprod_is_integrable μ f hfmeas C hfbndC x
        · intro x_1
          dsimp
          calc
            (∫ (z : G), f (x + z) - f (x + z + x_1) ∂μ) *
              (∫ (z : G), f (x + z) - f (x + z + x_1) ∂μ) =
              (∫ (z : G), f (x + z) - f (x + z + x_1) ∂μ)^2 := by
              exact Eq.symm (pow_two (∫ (z : G), f (x + z) - f (x + z + x_1) ∂μ))
            _ ≤ (∫ (z : G), |f (x + z) - f (x + z + x_1)| ∂μ)^2 := by sorry
            _ = (∫ (z : G), |f (x + z) - f (x + z + x_1)| * 1 ∂μ)^2 := by
              simp only [mul_one]
            _ ≤ (Real.sqrt (∫ (z : G), |f (x + z) - f (x + z + x_1)|^2 ∂μ)
               * Real.sqrt (∫ (z : G), (1 ^ 2) ∂μ))^2 := by
              rw [sq_le_sq]
              rw [abs_of_nonneg]
              · rw [abs_of_nonneg]
                · sorry
                · sorry
              · sorry
            _ = (∫ (z : G), |f (x + z) - f (x + z + x_1)|^2 ∂μ) := by
              simp only [sq_abs, one_pow, MeasureTheory.integral_const, MeasureTheory.probReal_univ,
                smul_eq_mul, mul_one, Real.sqrt_one]
              rw [Real.sq_sqrt]
              apply MeasureTheory.integral_nonneg
              · intro y; dsimp
                exact sq_nonneg (f (x + y) - f (x + y + x_1))
            _ = (∫ (z : G), (f (x + z) - f (x + z + x_1)) *
              (f (x + z) - f (x + z + x_1)) ∂μ) := by
              congr
              ext y
              rw [sq_abs]
              ring
      _ = ∫ (y : G), (∫ (z : G), f (x + z) - f (x + z + y) ∂μ)^2 ∂μ := by
        simp only [<- sq]
      _ = ∫ (y : G), (∫ (z : G), f (x + z) - f (x + y + z) ∂μ)^2 ∂μ := by
        congr
        ext y
        congr
        ext z
        simp
        abel_nf
      _ = ∫ (y : G), (∫ (z : G), f (x + z) ∂μ - ∫ (z : G), f (x + y + z) ∂μ)^2 ∂μ := by
        congr
        ext y
        rw [MeasureTheory.integral_sub (hint0 x) (hint0 (x + y))]
      _ = ∫ (y : G), (f x - f (x+y))^2 ∂μ := by
        congr; ext y; congr;
        · exact Real.ext_cauchy (congrArg Real.cauchy (hfint x))
        · exact Real.ext_cauchy (congrArg Real.cauchy (hfint (x + y)))
      _ = g x := by
        rw [hg]
        congr; ext y;
        exact pow_two (f x - f (x + y))
  have hΦffmeasn : ∀ (n : ℕ), Measurable (Φ^[n] (f * f)) := by
    intro n
    induction n
    case zero =>
      apply Measurable.mul _ _
      repeat
      · exact hfmeas
    case succ n ih =>
      rw [Φ.iterate_succ']
      apply shift_operator_preserves_meas
      exact ih
  have hΦgmeasn : ∀ (n : ℕ), Measurable (Φ^[n] g) := by
    intro n
    induction n
    case zero =>
      exact gismeasurable μ f hfmeas
    case succ n ih =>
      rw [Φ.iterate_succ']
      apply shift_operator_preserves_meas
      exact ih
  have hΦbnd : ∃ (C : ℝ), ∀ (n : ℕ) (x : G), |(Φ^[n] (f * f)) x| ≤ C := by
    use C*C
    intro n
    induction n
    case zero =>
      simp only [Function.iterate_zero, id_eq, Pi.mul_apply, abs_mul,
        abs_mul_abs_self]
      intro x
      refine abs_le_iff_mul_self_le.mp ?_
      trans C
      · exact hfbndC x
      exact le_abs_self C
    case succ n ih =>
      rw [Φ.iterate_succ']
      apply shift_operator_bounded
      · induction n
        case zero =>
          simp only [Function.iterate_zero, id_eq]
          exact hΦffmeasn 0
        case succ n ih' =>
          exact hΦffmeasn (n + 1)
      · exact ih
  have hΦgbnd : ∀ (n : ℕ), ∃ (C : ℝ), ∀ (x : G), |(Φ^[n] g) x| ≤ C := by
    intro n
    use 4 * C * C
    induction n
    case zero =>
      intro x
      simp only [Function.iterate_zero, id_eq]
      rw [hg]; dsimp
      rw [abs_le]
      constructor
      · calc
          -(4 * C * C) = ∫ (z : G), -(4 * C * C) ∂μ := by
            rw [MeasureTheory.integral_const (-(4 * C * C))]
            simp
          _ ≤ ∫ (y : G), (f x - f (x + y)) * (f x - f (x + y)) ∂μ := by
            apply MeasureTheory.integral_mono (MeasureTheory.integrable_const (-(4 * C * C))) _ _
            · exact fxydiff2prod_is_integrable μ f hfmeas C hfbndC x
            · intro z
              dsimp
              rw [neg_le]
              trans |f x - f (x + z)| * |f x - f (x + z)|
              · simp only [abs_mul_abs_self, neg_le_self_iff]
                exact mul_self_nonneg (f x - f (x + z))
              trans (2 * C) * (2 * C)
              · refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
                · trans |f x| + |f (x + z)|
                  · exact abs_sub (f x) (f (x + z))
                  trans C + C
                  · exact add_le_add (hfbndC x) (hfbndC (x + z))
                  ring; rfl
                · trans |f x| + |f (x + z)|
                  · exact abs_sub (f x) (f (x + z))
                  trans C + C
                  · exact add_le_add (hfbndC x) (hfbndC (x + z))
                  ring; rfl
                · exact abs_nonneg (f x - f (x + z))
                · trans 2 * |f 0|
                  · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, abs_nonneg]
                  simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
                  exact hfbndC (0 : G)
              ring; rfl
      · calc
        ∫ (y : G), (f x - f (x + y)) * (f x - f (x + y)) ∂μ ≤ ∫ (y : G), 4 * C * C ∂μ := by
          apply MeasureTheory.integral_mono _ (MeasureTheory.integrable_const ((4 * C * C)))
          · intro y
            dsimp
            calc
              (f x - f (x + y)) * (f x - f (x + y)) = |f x - f (x + y)| * |f x - f (x + y)| := by
                exact Eq.symm (abs_mul_abs_self (f x - f (x + y)))
              _ ≤ (2 * C) * (2 * C) := by
                refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
                · trans |f x| + |f (x + y)|
                  · exact abs_sub (f x) (f (x + y))
                  trans C + C
                  · exact add_le_add (hfbndC x) (hfbndC (x + y))
                  ring_nf; rfl
                · trans |f x| + |f (x + y)|
                  · exact abs_sub (f x) (f (x + y))
                  trans C + C
                  · exact add_le_add (hfbndC x) (hfbndC (x + y))
                  ring_nf; rfl
                · exact abs_nonneg (f x - f (x + y))
                · trans 2 * |f 0|
                  · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, abs_nonneg]
                  simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
                  exact hfbndC (0 : G)
              _ = 4 * C * C := by ring
          · exact fxydiff2prod_is_integrable μ f hfmeas C hfbndC x
        _ = 4 * C * C := by
          rw [MeasureTheory.integral_const]
          simp
    case succ n ih =>
      simp only [Φ.iterate_succ']
      have : ∀ (x : G), |∫ (y : G), (Φ^[n]) g (x + y) ∂μ| ≤ 4 * C * C :=
        shift_operator_bounded μ (Φ^[n] g) (4 * C * C) (hΦgmeasn n) ih
      intro x
      specialize this x
      exact RCLike.ofReal_le_ofReal.mp this
  have hineq2 : ∀ (n : ℕ) (x : G), (Φ^[n] g) x ≥ g x := by
    intro n
    induction n
    case zero =>
      simp
    case succ n ih =>
      calc
        Φ^[n+1] g = Φ (Φ^[n] g) := by
          rw [Φ.iterate_succ' n]
          rfl
        _ ≥ Φ g := by
          apply shift_operator_is_monotone
          · rw [hg];
            exact gismeasurable μ f hfmeas
          · exact hΦgmeasn n
          · exact hΦgbnd 0
          · exact hΦgbnd n
          · exact ih
        _ ≥ g := hineq1
  have gpos : ∀ (x : G), g x ≥ 0 := by
    intro x
    unfold g
    apply MeasureTheory.integral_nonneg _
    intro x_1;
    simp only [Pi.zero_apply]
    exact mul_self_nonneg (f x - f (x + x_1))
  have hindlinΦ : ∀ (n : ℕ), Φ^[n + 1] (f * f) - Φ^[n] (f * f) = Φ^[n] (Φ (f * f) - (f * f)) := by
    intro n
    induction n
    case zero =>
      simp only [zero_add, Function.iterate_one, Function.iterate_zero, id_eq]
    case succ n ih =>
      rw [Φ.iterate_succ']
      calc
        (Φ ∘ Φ^[n + 1]) (f * f) - Φ^[n + 1] (f * f) =
          (Φ ∘ Φ^[n + 1]) (f * f) - (Φ ∘ Φ^[n]) (f * f) := by
          simp only [Function.iterate_succ, Function.comp_apply, sub_right_inj]
          exact Function.iterate_succ_apply' Φ n (f * f)
        _ = (fun (x : G) => ∫ (y : G), Φ^[n + 1] (f * f) (x + y) ∂μ -
          ∫ (y : G), Φ^[n] (f * f) (x + y) ∂μ) := by
          exact Pi.sub_def ((Φ ∘ Φ^[n + 1]) (f * f)) ((Φ ∘ Φ^[n]) (f * f))
        _ = (fun (x : G) => ∫ (y : G), Φ^[n + 1] (f * f) (x + y) - Φ^[n] (f * f) (x + y) ∂μ) := by
          ext x;
          rw [MeasureTheory.integral_sub]
          · constructor
            · apply Measurable.aestronglyMeasurable
              apply Measurable.comp' (hΦffmeasn (n + 1)) _
              apply Continuous.measurable
              exact continuous_add_left x
            · rcases hΦbnd with ⟨C₁, hΦbndC₁⟩
              have interm : ∀ᵐ (a : G) ∂μ, ‖Φ^[n + 1] (f * f) (x + a)‖ ≤ C₁ := by
                apply MeasureTheory.ae_of_all μ _
                intro a
                simp only [Real.norm_eq_abs]
                exact hΦbndC₁ (n + 1) (x + a)
              apply MeasureTheory.HasFiniteIntegral.of_bounded interm
          · constructor
            · apply Measurable.aestronglyMeasurable
              apply Measurable.comp' (hΦffmeasn n) _
              apply Continuous.measurable
              exact continuous_add_left x
            · rcases hΦbnd with ⟨C₁, hΦbndC₁⟩
              have interm : ∀ᵐ (a : G) ∂μ, ‖Φ^[n] (f * f) (x + a)‖ ≤ C₁ := by
                apply MeasureTheory.ae_of_all μ _
                intro a
                simp only [Real.norm_eq_abs]
                exact hΦbndC₁ n (x + a)
              apply MeasureTheory.HasFiniteIntegral.of_bounded interm
        _ = Φ (Φ^[n + 1] (f * f) - Φ^[n] (f * f)) := by exact List.map_inj.mp rfl
        _ = Φ (Φ^[n] (Φ (f * f) - (f * f))) := List.map_inj.mp (congrArg List.map (congrArg Φ ih))
        _ = Φ^[n+1] (Φ (f * f) - (f * f)) :=
          Eq.symm (Function.iterate_succ_apply' Φ n (Φ (f * f) - f * f))
  have h2 : ∀ (n : ℕ) (x : G), (Φ^[n+1] (f * f)) x - (Φ^[n] (f * f)) x ≥ g x := by
    intro n x
    calc
      Φ^[n + 1] (f * f) x - Φ^[n] (f * f) x = Φ^[n] (Φ (f * f) - (f * f)) x := by
        rw [<- hindlinΦ n]
        exact Real.ext_cauchy rfl
      _ = Φ^[n] g x := by
        congr!
        ext z
        rw [heq1 z, hΦ]; dsimp
      _ ≥ g x := hineq2 n x
  have gvanishes : ∀ (x : G), g x = 0 := by
    intro x
    apply unif_bounded_diff (fun (n : ℕ) => (Φ^[n] (f * f)) x) (g x) _ (gpos x)
    · intro n
      specialize h2 n x
      exact h2
    · dsimp;
      rcases hΦbnd with ⟨C, hΦbndC⟩
      use C
      intro n
      exact hΦbndC n x
  rw [hg] at gvanishes
  dsimp at gvanishes
  intro x
  specialize gvanishes x
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at gvanishes
  · have h3 : ∀ᵐ (y : G) ∂μ, (f x - f (x + y)) * (f x - f (x + y)) = 0 := gvanishes
    simp only [mul_self_eq_zero, sub_eq_zero] at h3
    exact h3
  · intro y; dsimp;
    exact mul_self_nonneg (f x - f (x + y))
  apply MeasureTheory.Integrable.mono (MeasureTheory.integrable_const (4*C*C : ℝ)) _ _
  · apply MeasureTheory.AEStronglyMeasurable.mul _ _
    repeat
    · apply MeasureTheory.AEStronglyMeasurable.sub _ _
      · exact MeasureTheory.aestronglyMeasurable_const
      · apply Measurable.aestronglyMeasurable
        apply Measurable.comp' hfmeas _
        apply Continuous.measurable
        exact continuous_add_left x
  · apply MeasureTheory.ae_of_all μ _
    intro a
    simp only [norm_mul, Real.norm_eq_abs, abs_mul_abs_self]
    calc
      (f x - f (x + a)) * (f x - f (x + a)) = (f x - f (x + a))^2 :=
        Eq.symm (pow_two (f x - f (x + a)))
      _ ≤ (|C| + |C|)^2 := by
        rw [sq_le_sq]
        trans |f x| + |f (x + a)|
        · exact abs_sub (f x) (f (x + a))
        trans C + C
        · apply add_le_add (hfbndC x) (hfbndC (x + a))
        trans |C| + |C|
        · ring
          simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
          exact le_abs_self C
        exact le_abs_self (|C| + |C|)
      _ = 4 * |C| * |C| := by ring
      _ = |4| * |C| * |C| := by simp


/-
theorem ChoquetDenyPMF {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [Countable G] (μ : PMF G) (f : G → ℝ)
(hhar : f ∈ BoundedHarmonicFunctions μ) (hgen : Subgroup.closure μ.support = G) :
∀ (x y : G), f x = f y := by sorry
-/
