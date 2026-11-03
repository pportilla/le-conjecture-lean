/-
Copyright (c) 2026 The Tau Ceti contributors and Pablo Portilla Cuadrado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: The Tau Ceti contributors, Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullComplex

/-!
# Curvature of the differential with arbitrary square weights

Assign a weight in a commutative semiring to each grid square. Count all
empty rectangles with the product of their square weights. In characteristic
two the square of this operator is scalar multiplication by the sum of
the full-column products and the full-row products. The cancellation uses
the actual commuting and recutting operations and the explicit thin annuli.

The free-module construction follows the TauCeti rectangle differential,
whose source attribution is recorded in `GridFullDifferentialBasic`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} {R : Type*} [CommSemiring R]

/-- Multiplicative weight of the squares in a rectangle. -/
noncomputable def squareWeight (w : Fin n × Fin n → R) (r : GridRectangle n) : R :=
  ∏ p ∈ r.coveredSquares, w p

/-- The weighted count of all empty rectangles between two grid states. -/
noncomputable def squareWeightedCoefficient (w : Fin n × Fin n → R)
    (x y : GridState n) : R :=
  ∑ r ∈ GridRectangleBetween.emptyRectangles x y, squareWeight w r.toGridRectangle

/-- The rectangle operator on a grid-state generator. -/
noncomputable def squareWeightedOnGenerator (w : Fin n × Fin n → R)
    (x : GridState n) : GridState n →₀ R :=
  ∑ y : GridState n, Finsupp.single y (squareWeightedCoefficient w x y)

@[simp] theorem squareWeightedOnGenerator_apply (w : Fin n × Fin n → R)
    (x y : GridState n) : squareWeightedOnGenerator w x y = squareWeightedCoefficient w x y := by
  classical
  rw [squareWeightedOnGenerator, Finsupp.finsetSum_apply, Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz.symm]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- The linear operator counting every empty rectangle with its square weights. -/
noncomputable def squareWeightedDifferential (w : Fin n × Fin n → R) :
    (GridState n →₀ R) →ₗ[R] (GridState n →₀ R) :=
  Finsupp.lsum R fun x : GridState n =>
    (LinearMap.id : R →ₗ[R] R).smulRight (squareWeightedOnGenerator w x)

@[simp] theorem squareWeightedDifferential_single (w : Fin n × Fin n → R)
    (x : GridState n) :
    squareWeightedDifferential w (Finsupp.single x 1) = squareWeightedOnGenerator w x := by
  rw [squareWeightedDifferential, Finsupp.lsum_single]
  simp

theorem squareWeightedDifferential_apply_apply (w : Fin n × Fin n → R)
    (c : GridState n →₀ R) (y : GridState n) :
    squareWeightedDifferential w c y = c.sum fun x a => a * squareWeightedCoefficient w x y := by
  simp [squareWeightedDifferential, Finsupp.lsum_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, LinearMap.smulRight_apply]

/-- Multiplicative weight of two composable rectangles. -/
noncomputable def squareDecompositionWeight (w : Fin n × Fin n → R)
    {x z : GridState n} (D : GridRectangleDecomposition x z) : R :=
  squareWeight w D.first.toGridRectangle * squareWeight w D.second.toGridRectangle

theorem squareWeightedDifferential_sq_single_apply (w : Fin n × Fin n → R)
    (x z : GridState n) :
    squareWeightedDifferential w (squareWeightedDifferential w (Finsupp.single x 1)) z =
      ∑ D ∈ emptyDecompositions x z, squareDecompositionWeight w D := by
  rw [squareWeightedDifferential_single, squareWeightedDifferential_apply_apply,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp only [squareWeightedOnGenerator_apply, squareWeightedCoefficient,
    Finset.sum_mul_sum, squareDecompositionWeight]
  exact (sum_emptyDecompositions x z fun _ r₁ r₂ =>
    squareWeight w r₁.toGridRectangle * squareWeight w r₂.toGridRectangle).symm

theorem squareDecompositionWeight_commute (w : Fin n × Fin n → R)
    {x z : GridState n} (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    squareDecompositionWeight w (D.commute h) = squareDecompositionWeight w D := by
  rw [squareDecompositionWeight, squareDecompositionWeight,
    D.commute_first_toGridRectangle h, D.commute_second_toGridRectangle h, mul_comm]

theorem squareDecompositionWeight_recut (w : Fin n × Fin n → R)
    {x z : GridState n} (D : GridRectangleDecomposition x z) (h : D.HasOneCommonSide)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    squareDecompositionWeight w (D.recut h hfirst hsecond) = squareDecompositionWeight w D :=
  (D.isRecut_recut h hfirst hsecond).isRepartition.prod_coveredSquares_mul_prod_coveredSquares w

/-- Different source and target states have zero total two-step weight. -/
theorem sum_squareDecompositionWeight_eq_zero_of_ne [CharP R 2]
    (w : Fin n × Fin n → R) {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ emptyDecompositions x z, squareDecompositionWeight w D = 0 := by
  refine sum_emptyDecompositions_eq_zero hzx _ (fun D _ h => ?_)
    (fun D _ h hfirst hsecond => ?_)
  · rw [squareDecompositionWeight_commute]
    exact CharTwo.add_self_eq_zero _
  · rw [squareDecompositionWeight_recut]
    exact CharTwo.add_self_eq_zero _

theorem squareDecompositionWeight_columnAnnulus (w : Fin n × Fin n → R)
    (hn : 1 < n) (x : GridState n) (c : Fin n) :
    squareDecompositionWeight w (columnAnnulus hn x c) = ∏ r : Fin n, w (c, r) := by
  let D := columnAnnulus hn x c
  have hD := (mem_emptyDecompositions D).mp (columnAnnulus_mem hn x c)
  have hl : D.second.left = D.first.left := by simp [D]
  rw [squareDecompositionWeight, squareWeight, squareWeight,
    ← Finset.prod_union (D.first.disjoint_coveredSquares D.second),
    D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hl,
    GridEmptyAnnuli.coveredColumns_eq_singleton D.first D.second hD.1 hD.2 hl]
  simp [D]

theorem squareDecompositionWeight_rowAnnulus (w : Fin n × Fin n → R)
    (hn : 1 < n) (x : GridState n) (r : Fin n) :
    squareDecompositionWeight w (rowAnnulus hn x r) = ∏ c : Fin n, w (c, r) := by
  let D := rowAnnulus hn x r
  have hD := (mem_emptyDecompositions D).mp (rowAnnulus_mem hn x r)
  have hb : D.second.bottom = D.first.bottom := by simp [D]
  have hl : D.second.left = D.first.right := by
    rcases D.first.left_right_eq_cases D.second with ⟨h, _⟩ | ⟨h, _⟩
    · exact False.elim (D.first.bottom_ne_top
        (hb.symm.trans (D.first.bottom_eq_top_of_left_eq_left D.second h)))
    · exact h
  rw [squareDecompositionWeight, squareWeight, squareWeight,
    ← Finset.prod_union (D.first.disjoint_coveredSquares D.second),
    D.first.coveredSquares_union_coveredSquares_of_left_eq_right D.second hl,
    GridEmptyAnnuli.coveredRows_eq_singleton D.first D.second hD.1 hD.2 hl]
  simp [D]

/-- The scalar contributed by the full column and full row annuli. -/
noncomputable def squareWeightCurvature (w : Fin n × Fin n → R) : R :=
  (∑ c : Fin n, ∏ r : Fin n, w (c, r)) + (∑ r : Fin n, ∏ c : Fin n, w (c, r))

/-- For a grid with at least two rows, the returning decomposition sum
is exactly the curvature scalar. -/
theorem sum_squareDecompositionWeight_self (w : Fin n × Fin n → R)
    (hn : 1 < n) (x : GridState n) :
    ∑ D ∈ emptyDecompositions x x, squareDecompositionWeight w D = squareWeightCurvature w := by
  classical
  have hdisjoint : Disjoint (Finset.univ.image (columnAnnulus hn x))
      (Finset.univ.image (rowAnnulus hn x)) := by
    rw [Finset.disjoint_left]
    intro D hD hE
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨r, _, h⟩ := Finset.mem_image.mp hE
    exact columnAnnulus_ne_rowAnnulus hn x c r h.symm
  have hc : Function.Injective (columnAnnulus hn x) := by
    intro a b h
    simpa using congrArg (fun D : GridRectangleDecomposition x x => D.first.left) h
  have hr : Function.Injective (rowAnnulus hn x) := by
    intro a b h
    simpa using congrArg (fun D : GridRectangleDecomposition x x => D.first.bottom) h
  rw [emptyDecompositions_self hn x, Finset.sum_union hdisjoint,
    Finset.sum_image (fun a _ b _ h => hc h), Finset.sum_image (fun a _ b _ h => hr h)]
  simp only [squareDecompositionWeight_columnAnnulus, squareDecompositionWeight_rowAnnulus,
    squareWeightCurvature]

theorem squareWeightCurvature_eq_zero_of_le_one [CharP R 2]
    (w : Fin n × Fin n → R) (hn : n ≤ 1) : squareWeightCurvature w = 0 := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;>
    simp [squareWeightCurvature, CharTwo.add_self_eq_zero]

theorem sum_squareDecompositionWeight_self_all [CharP R 2]
    (w : Fin n × Fin n → R) (x : GridState n) :
    ∑ D ∈ emptyDecompositions x x, squareDecompositionWeight w D = squareWeightCurvature w := by
  by_cases hn : 1 < n
  · exact sum_squareDecompositionWeight_self w hn x
  · rw [squareWeightCurvature_eq_zero_of_le_one w (by omega)]
    apply Finset.sum_eq_zero
    intro D _
    have hcard : 1 < Fintype.card (Fin n) :=
      Fintype.one_lt_card_iff.mpr ⟨D.first.left, D.first.right, D.first.left_ne_right⟩
    exact (hn (by simpa using hcard)).elim

/-- The square of the weighted differential is multiplication by its
explicit curvature, for every grid size, including zero and one. -/
theorem squareWeightedDifferential_comp_self [CharP R 2]
    (w : Fin n × Fin n → R) :
    squareWeightedDifferential w ∘ₗ squareWeightedDifferential w =
      squareWeightCurvature w • (LinearMap.id : (GridState n →₀ R) →ₗ[R] (GridState n →₀ R)) := by
  classical
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  apply Finsupp.ext
  intro z
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Finsupp.smul_apply, smul_eq_mul,
    squareWeightedDifferential_sq_single_apply]
  by_cases hzx : z = x
  · subst z
    simp only [Finsupp.single_eq_same, mul_one]
    exact sum_squareDecompositionWeight_self_all w x
  · rw [Finsupp.single_eq_of_ne hzx, mul_zero]
    exact sum_squareDecompositionWeight_eq_zero_of_ne w hzx

theorem squareWeightedDifferential_sq_apply [CharP R 2]
    (w : Fin n × Fin n → R) (c : GridState n →₀ R) :
    squareWeightedDifferential w (squareWeightedDifferential w c) = squareWeightCurvature w • c :=
  LinearMap.congr_fun (squareWeightedDifferential_comp_self w) c

end OnLeConjecture.KnotFloer.GridFull
