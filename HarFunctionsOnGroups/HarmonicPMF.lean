import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.ContinuousMap.Bounded.Basic

noncomputable section

open ENNReal
-- Definition of a harmonic function, we require the convex
-- combination ∑ μ g f (x * g) to converge to f x for every x ∈ G
def IsHarmonicFunction {G : Type*} [Group G] [Countable G] (μ : PMF G) (f : G → ℝ) : Prop :=
∀ (x : G), HasSum (fun (g : G) => (μ g).toReal * f (x * g)) (f x)



-- A technical lemma to prove that the probability measure sums to 1 after coercion to ℝ
lemma HasSum_coe_toReal {α : Type*} (μ : PMF α) : HasSum (fun (x : α) => (μ x).toReal) 1 := by
  have hnetop : ∀ (g : α), μ g ≠ ⊤ := by exact fun g ↦ PMF.apply_ne_top μ g
  have hsum : ∑' (x : α), (μ x) ≠ ⊤ := PMF.tsum_coe_ne_top μ
  have have_sum_real :
  HasSum (fun (x : α) => (μ x).toReal) (∑' (x : α), (μ x).toReal) := ENNReal.hasSum_toReal hsum
  have h1 : ∑' (x : α), (μ x).toReal = (∑' (x : α), (μ x)).toReal := Eq.symm (tsum_toReal_eq hnetop)
  rw [h1, μ.tsum_coe] at have_sum_real
  simp only [toReal_one] at have_sum_real
  exact have_sum_real


-- Constant functions are harmonic for any measure μ
example {G : Type*} [Group G] [Countable G] (μ : PMF G) :
∀ (c : ℝ), IsHarmonicFunction μ (fun g => c) := by
  intro c hhar
  dsimp
  have h1 : HasSum (fun g => (μ g).toReal) 1 := HasSum_coe_toReal μ
  have h2 : HasSum (fun g => (μ g).toReal * c) (1 * c) := HasSum.mul_right c h1
  simp only [one_mul] at h2; exact h2


-- Any function is harmonic with respect to the delta measure at identity
open Classical in
theorem harmonic_delta_measure {G : Type*} [Group G] [Countable G] (f : G → ℝ) :
IsHarmonicFunction (PMF.pure 1) f := by
  intro x
  dsimp
  have hf : ∀ (g' : G),
  g' ≠ 1 → (fun g ↦ (if g = 1 then (1 : ENNReal) else (0: ENNReal)).toReal * f (x * g)) g' = 0
  := by
    intro g' hg'
    dsimp
    split
    · contradiction
    simp
  have h1 : (fun g ↦ (if g = 1 then (1 : ENNReal) else (0: ENNReal)).toReal * f (x * g)) 1 = f x
  := by
    dsimp
    split
    · simp
    contradiction
  rw [← h1]
  exact hasSum_single (1 : G) hf

-- Sum of μ harmonic functions is μ harmonic
lemma sum_of_harmonic {G : Type*} [Group G] [Countable G] (μ : PMF G) (f g : G → ℝ)
(hf : IsHarmonicFunction μ f) (hg : IsHarmonicFunction μ g) : IsHarmonicFunction μ (f + g) := by
  intro x
  simp only [Pi.add_apply]; ring
  apply HasSum.add (hf x) (hg x)

-- Multiplication by a constant preserves harmonicity

lemma mul_by_const_harmonic {G : Type*} [Group G] [Countable G] (μ : PMF G) (c : ℝ) (f : G → ℝ)
(hf : IsHarmonicFunction μ f) : IsHarmonicFunction μ (fun g => c * f g) := by
  intro x
  simp only;
  simp only [mul_comm, mul_assoc]
  apply HasSum.mul_left
  specialize hf x
  simp only [mul_comm] at hf
  exact hf

-- Using monadic structure to define the convolution of two measures on a group

def pmf_conv {G : Type*} [Group G] [Countable G] (μ ν : PMF G) : PMF G :=
  μ.bind (fun x => ν.map (fun (y : G) => x * y))

def iteratedConv {G : Type*} [Group G] [Countable G] (μ : PMF G) : ℕ → PMF G
  | 0 => PMF.pure 1
  | n + 1 => pmf_conv μ (iteratedConv μ n)

-- TODO: finish the proof of the fact that if a function is harmonic wrt μ and ν,
-- it is harmonic wrt the convolution. Requires Fubini's therorem for PMF measures it seems?
/- open Classical in
lemma harmonic_pmf_conv {G : Type*} [Group G] [Countable G] (μ ν : PMF G) (f : G → ℝ)
(hmu : IsHarmonicFunction μ f) (hnu : IsHarmonicFunction ν f) :
IsHarmonicFunction (pmf_conv μ ν) f := by
  intro x
  rw [pmf_conv]
  dsimp;
  simp only [PMF.map_apply]
  have h1 : ∀ (g a : G), ∑' (a_1 : G), (if g = a * a_1 then ν a_1 else 0) = ν (a⁻¹ * g) := by
    intro g a
    rw [tsum_eq_single (a⁻¹ * g)]
    · simp only [mul_inv_cancel_left, ite_true]
    intro b' hb'
    simp only [ite_eq_right_iff]
    intro h11
    simp only [ne_eq] at hb'
    rw [eq_inv_mul_iff_mul_eq] at hb';
    subst h11
    simp_all only [not_true_eq_false]
  simp only [h1]
  have hdsum : ∀ (x : G),
  HasSum (fun ((g, a): G × G) => ((μ a) * (ν (a⁻¹ * g))).toReal * f (x * g)) (f x) := by
    sorry
  sorry
-/


-- I have proven the weaker version of the above when ν = μ
/-lemma harmonic_iter_conv {G : Type*} [Group G] [Countable G] (μ : PMF G) (f : G → ℝ)
(hf : IsHarmonicFunction μ f): ∀ (n : ℕ), IsHarmonicFunction (iteratedConv μ n) f := by
  intro n
  induction n
  case zero =>
    rw [iteratedConv]
    exact harmonic_delta_measure f
  case succ ih =>
    rw [iteratedConv]
    apply harmonic_pmf_conv
    · exact hf
    exact ih
-/

lemma iterconv_gives_fullsupport {G : Type*} [Group G] [Finite G] (μ : PMF G)
(hgen : Subsemigroup.closure μ.support = G) : ∃ (n : ℕ), (iteratedConv μ n).support = G := by sorry

-- The idea is to prove that we can endow this with the structure of the Banach space and
-- a convex closed subset of it respectively.
def BoundedHarmonicFunctions {G : Type*} [Group G] [Countable G] (μ : PMF G) : Set (G → ℝ) :=
  { f | IsHarmonicFunction μ f ∧ ∃ c ≥ 0, ∀ x, |f x| ≤ c}

def BoundedHarmonicFunctions01 {G : Type*} [Group G] [Countable G] (μ : PMF G) : Set (G → ℝ) :=
  { f | IsHarmonicFunction μ f ∧ ∀ x, f x ∈ Set.Icc 0 1 }

noncomputable section AristotleLemmas

/-
If a harmonic function attains a maximum at x,
then it has the same value at all neighbors x*g where g is in the support of the measure.
-/

lemma harmonic_max_eq_neighbors {G : Type*} [Group G] [Countable G] (μ : PMF G) (f : G → ℝ) (x : G)
  (hhar : IsHarmonicFunction μ f) (hmax : ∀ y, f y ≤ f x) :
  ∀ g ∈ μ.support, f (x * g) = f x := by
    intro g hg
    have hsum : ∑' g, (μ g).toReal * (f x - f (x * g)) = 0 := by
      have hsum_zero : ∑' g, (μ g).toReal * f x - ∑' g, (μ g).toReal * f (x * g) = 0 := by
        have := hhar x;
        rw [ tsum_mul_right, this.tsum_eq, sub_eq_zero ];
        rw [ show ( ∑' g : G, ( μ g |> ENNReal.toReal ) ) = 1 by
          exact HasSum.tsum_eq ( by exact? ) ] ; simp +decide;
      simp only [ mul_sub ];
      rw [ Summable.tsum_sub, hsum_zero ];
      · refine' Summable.mul_right _ _;
        convert ENNReal.summable_toReal _;
        simp +decide [ PMF.tsum_coe ];
      · exact hhar x |> HasSum.summable;
    -- Since $f x - f (x * g) \geq 0$ for all $g$, and their sum is zero, each term must be zero.
    have h_zero : ∀ g, (μ g).toReal * (f x - f (x * g)) = 0 := by
      field_simp;
      intro g;
      contrapose! hsum;
      refine' ne_of_gt ( lt_of_lt_of_le _ ( Summable.le_tsum _ g
      ( fun y hy => mul_nonneg ( ENNReal.toReal_nonneg ) ( sub_nonneg.2 ( hmax _ ) ) ) ) );
      · exact lt_of_le_of_ne ( mul_nonneg ( ENNReal.toReal_nonneg )
        ( sub_nonneg.2 ( hmax _ ) ) ) hsum.symm;
      · have h_summable : Summable (fun g => (μ g).toReal * f (x * g)) := by
          have := hhar x;
          exact this.summable;
        convert h_summable.neg.add ( Summable.mul_left ( f x )
        ( show Summable fun g => ( μ g |> ENNReal.toReal ) from ?_ ) ) using 2 ; ring;
        convert ENNReal.summable_toReal _;
        simp +decide [ PMF.tsum_coe ];
    simp_all +decide [ sub_eq_zero ];
    cases h_zero g <;> simp_all +decide [ ENNReal.toReal_eq_zero_iff ];
    exact absurd ‹_› ( ne_of_lt ( PMF.apply_lt_top _ _ ) )

end AristotleLemmas


-- TODO: clean up the Aristotle proof, uses several refine', seems very ``hacky''
theorem FiniteGroupsAreLiuoville {G : Type*} [Group G] [Finite G] (μ : PMF G) (f : G → ℝ)
  (hhar : IsHarmonicFunction μ f)
  (hgen : Subsemigroup.closure μ.support = G) : ∀ (x y : G), f x = f y := by
  intro x y
  by_contra non_const; push_neg at non_const
  have hmax : ∃ (g : G), ∀ (g' : G), |f g'| ≤ |f g| := Finite.exists_max fun x ↦ |f x|
  rcases hmax with ⟨gₘ, hgmax⟩
  have small_value_in_support : ∃ (g : μ.support), |f (gₘ * g)| < |f gₘ| := by
    by_contra h1
    push_neg at h1
    revert hgen;
    -- Let $M$ be the maximum value of $f$ on $G$.
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, ∀ y : G, f y ≤ f x₀ := by
      -- Since $G$ is finite, the image of $f$ is also finite and hence must attain a maximum value.
      have h_max_exists : ∃ x₀ ∈ Set.range f, ∀ y ∈ Set.range f, y ≤ x₀ := by
        apply_rules [ Set.exists_max_image ];
        · exact Set.toFinite _;
        · exact ⟨ f x, Set.mem_range_self x ⟩;
      aesop;
    -- By `harmonic_max_eq_neighbors`, if $x \in S_{max}$,
    -- then for all $g \in \mu.support$, $f(x \cdot g) = f(x) = M$, so $x \cdot g \in S_{max}$.
    have h_subsemigroup : ∀ g ∈ μ.support, ∀ x ∈ {x : G | f x = f x₀}, x * g ∈ {x : G | f x = f x₀} := by
      intro g hg x hx;
      have := harmonic_max_eq_neighbors μ f x ( by aesop ) ( by aesop ) g hg; aesop;
    -- This means the property $P(g) \equiv \forall x \in S_{max},
    -- x \cdot g \in S_{max}$ holds for all $g \in \mu.support$.
    have h_property : ∀ g ∈ Subsemigroup.closure μ.support, ∀ x ∈ {x : G | f x = f x₀}, x * g ∈ {x : G | f x = f x₀} := by
      intro g hg;
      induction hg using Subsemigroup.closure_induction ; aesop;
      simp_all +decide [ ← mul_assoc ];
    intro h;
    -- Therefore, for any $x \in S_{max}$ and any $y \in G$, $x \cdot y \in S_{max}$.
    have h_all_max : ∀ x ∈ {x : G | f x = f x₀}, ∀ y : G, x * y ∈ {x : G | f x = f x₀} := by
      intro x hx y
      have hy : y ∈ Subsemigroup.closure μ.support := by
        replace h := congr_arg Cardinal.mk h; simp_all +decide ;
        have h_eq : Subsemigroup.closure μ.support = ⊤ := by
          have h_eq : ∀ (S : Subsemigroup G), Cardinal.mk S = Cardinal.mk G → S = ⊤ := by
            intro S hS; ext x; simp [hS];
            have h_eq : Set.ncard (S : Set G) = Set.ncard (Set.univ : Set G) := by
              simp_all +decide [ Set.ncard_eq_toFinset_card' ];
              convert congr_arg Cardinal.toNat hS using 1;
            have h_eq : (S : Set G) = Set.univ := by
              exact Set.eq_of_subset_of_ncard_le ( Set.subset_univ _ ) (
                by simpa [ Set.ncard_univ ] using h_eq.ge );
            exact Set.eq_univ_iff_forall.mp h_eq x;
          exact h_eq _ h;
        aesop
      exact h_property y hy x hx;
    exact non_const ( by have := h_all_max x₀ rfl ( x₀⁻¹ * x ) ; have := h_all_max x₀ rfl ( x₀⁻¹ * y ) ; simp_all +decide )
  have insta_Fyntype_from_finite : Fintype G := Fintype.ofFinite G
  have infsum_to_fin :
  ∑' (g : G), (μ g).toReal * f (gₘ * g) = ∑ (g : G), (μ g).toReal * f (gₘ * g) :=
    tsum_fintype fun b ↦ (μ b).toReal * f (gₘ * b)
  have infsum_to_fin1 : ∑' (g : G), (μ g).toReal = ∑ (g : G), (μ g).toReal :=
    tsum_fintype fun b ↦ (μ b).toReal
  have contr_ineq : |∑' (g : G), (μ g).toReal * f (gₘ * g)| < |f gₘ| := by
    calc
      _ = |∑ (g : G), (μ g).toReal * f (gₘ * g)| :=
        (sq_eq_sq_iff_abs_eq_abs (∑' (g : G), (μ g).toReal * f (gₘ * g))
              (∑ g, (μ g).toReal * f (gₘ * g))).mp
          (congrFun (congrArg HPow.hPow infsum_to_fin) 2)
      _ ≤ ∑ (g : G), |(μ g).toReal * f (gₘ * g)| :=
      Finset.abs_sum_le_sum_abs (fun i ↦ (μ i).toReal * f (gₘ * i)) Finset.univ
      _ = ∑ (g : G), |(μ g).toReal| * |f (gₘ * g)| := by simp only [abs_mul]
      _ = ∑ (g : G), (μ g).toReal * |f (gₘ * g)| := by norm_num
      _ < (∑ (g : G), (μ g).toReal) * |f gₘ| := by
        rw [ Finset.sum_mul _ _ _ ];
        refine' Finset.sum_lt_sum _ _;
        · exact fun g _ => mul_le_mul_of_nonneg_left ( hgmax _ ) ( ENNReal.toReal_nonneg );
        · norm_num +zetaDelta at *;
          exact ⟨ small_value_in_support.choose, mul_lt_mul_of_pos_left small_value_in_support.choose_spec.2 ( ENNReal.toReal_pos small_value_in_support.choose_spec.1 ( by exact? ) ) ⟩
      _ = (∑' (g : G), (μ g).toReal) * |f gₘ| := by
        symm
        rw [infsum_to_fin1]
      _ = 1 * |f gₘ| := by
        rw [HasSum.tsum_eq (HasSum_coe_toReal μ)]
      _ = |f gₘ| := by ring
  have hh11 : ∑' (g : G), (μ g).toReal * f (gₘ * g) = f gₘ := HasSum.tsum_eq (hhar gₘ)
  rw [hh11] at contr_ineq
  exact (lt_self_iff_false |f gₘ|).mp contr_ineq
