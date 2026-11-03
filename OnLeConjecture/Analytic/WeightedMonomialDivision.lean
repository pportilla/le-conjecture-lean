/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableOrder
public import OnLeConjecture.Analytic.WeierstrassPreparation

/-!
# Division by a finite weighted monomial ideal

An analytic germ in two variables whose first coordinate coefficients have
the required orders in the second coordinate is a finite sum of monomials of
prescribed lower weighted degree. This is the analytic division needed for
weighted radial rescaling.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- The `k`th generator of the ideal of germs with weighted order at least
`D`. -/
@[expose]
noncomputable def weightedOrderGenerator
    (a D : ℕ) (k : Fin (D + 1)) : Germ 2 :=
  Germ.coordinate (0 : Fin 2) ^ (k : ℕ) *
    Germ.coordinate (1 : Fin 2) ^ (D - a * (k : ℕ))

/-- The finite monomial ideal of germs with weighted order at least `D`. -/
@[expose]
noncomputable def weightedOrderIdeal (a D : ℕ) : Ideal (Germ 2) :=
  Ideal.span (Set.range (Germ.weightedOrderGenerator a D))

/-- Membership in the weighted order ideal is equivalent to a finite
coefficient decomposition in its displayed generators. -/
theorem mem_weightedOrderIdeal_iff (a D : ℕ) (f : Germ 2) :
    f ∈ Germ.weightedOrderIdeal a D ↔
      ∃ c : Fin (D + 1) → Germ 2,
        ∑ k, c k * Germ.weightedOrderGenerator a D k = f := by
  change f ∈ Submodule.span (Germ 2)
      (Set.range (Germ.weightedOrderGenerator a D)) ↔ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [smul_eq_mul]

/-- Every analytic germ has an analytic function representative. -/
theorem exists_ofFunction {n : ℕ} (f : Germ n) :
    ∃ F : Source n → ℂ, ∃ hF : AnalyticAt ℂ F 0,
      f = Germ.ofFunction F hF := by
  rcases f with ⟨f, hf⟩
  change IsAnalyticGerm f at hf
  induction f using Filter.Germ.inductionOn with
  | _ F =>
      rw [isAnalyticGerm_ofFun] at hf
      exact ⟨F, hf, rfl⟩

/-- The coefficient condition for weighted order at least `D`. The first
source coordinate has weight `a` and the second has weight one. -/
def WeightedCoefficientDivisibility
    (a D : ℕ) (f : Germ 2) : Prop :=
  ∀ k < D,
    Germ.coordinate (0 : Fin 1) ^ (D - a * k) ∣
      Germ.firstCoordinateTaylorCoefficient k f

/-- The elementary equality expressing the weighted degree of the `k`th
term in the finite division. -/
theorem weightedExponent_eq (a D k : ℕ) :
    a * k + (D - a * k) = D + (a * k - D) := by
  omega

/-- The final power in the finite first coordinate expansion also has
weighted degree at least `D`. -/
theorem weightedTailExponent_eq
    (a D : ℕ) (ha : 0 < a) :
    a * D = D + (a * D - D) := by
  have hle : D ≤ a * D := by
    calc
      D = 1 * D := by simp
      _ ≤ a * D := Nat.mul_le_mul_right D ha
  exact (Nat.add_sub_of_le hle).symm

private theorem hyperplaneExtension_coordinate_one :
    Germ.hyperplaneExtension 1 (Germ.coordinate (0 : Fin 1)) =
      Germ.coordinate (1 : Fin 2) := by
  rw [Germ.hyperplaneExtension, PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  change
    ((MapGerm.ofFunction (Germ.hyperplaneTail 1)
      ((Germ.hyperplaneTail 1).analyticAt 0)).component 0).1 =
      (Germ.coordinate (1 : Fin 2)).1
  rw [MapGerm.component_ofFunction]
  rfl

/-- Finite weighted monomial division. Each term displayed before the tail
has weighted degree `D + (a * k - D)`, and the tail has weighted degree
`D + (a * D - D)`. -/
theorem exists_finite_weighted_monomial_decomposition
    (a D : ℕ) (f : Germ 2)
    (hdiv : WeightedCoefficientDivisibility a D f) :
    ∃ q : ℕ → Germ 1,
      (∀ k < D,
        Germ.firstCoordinateTaylorCoefficient k f =
          Germ.coordinate (0 : Fin 1) ^ (D - a * k) * q k) ∧
      f =
        ∑ k ∈ Finset.range D,
          Germ.coordinate (0 : Fin 2) ^ k *
            Germ.coordinate (1 : Fin 2) ^ (D - a * k) *
              Germ.hyperplaneExtension 1 (q k) +
        Germ.coordinate (0 : Fin 2) ^ D *
          Germ.firstCoordinateTailIterate D f := by
  have hquotient : ∀ k : ℕ, ∃ q : Germ 1,
      k < D →
        Germ.firstCoordinateTaylorCoefficient k f =
          Germ.coordinate (0 : Fin 1) ^ (D - a * k) * q := by
    intro k
    by_cases hk : k < D
    · obtain ⟨q, hq⟩ := hdiv k hk
      exact ⟨q, fun _ ↦ hq⟩
    · exact ⟨0, fun h ↦ (hk h).elim⟩
  choose q hq using hquotient
  refine ⟨q, fun k hk ↦ hq k hk, ?_⟩
  calc
    f =
        ∑ k ∈ Finset.range D,
            Germ.coordinate (0 : Fin 2) ^ k *
              Germ.hyperplaneExtension 1
                (Germ.firstCoordinateTaylorCoefficient k f) +
          Germ.coordinate (0 : Fin 2) ^ D *
            Germ.firstCoordinateTailIterate D f :=
      Germ.firstCoordinate_finite_expansion f
    _ =
        ∑ k ∈ Finset.range D,
            Germ.coordinate (0 : Fin 2) ^ k *
              Germ.coordinate (1 : Fin 2) ^ (D - a * k) *
                Germ.hyperplaneExtension 1 (q k) +
          Germ.coordinate (0 : Fin 2) ^ D *
            Germ.firstCoordinateTailIterate D f := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hkD : k < D := Finset.mem_range.mp hk
      rw [hq k hkD, map_mul, map_pow,
        hyperplaneExtension_coordinate_one]
      ring

/-- The coefficientwise divisibility condition implies membership in the
finite weighted order ideal. -/
theorem mem_weightedOrderIdeal_of_weightedCoefficientDivisibility
    (a D : ℕ) (ha : 0 < a) (f : Germ 2)
    (hdiv : WeightedCoefficientDivisibility a D f) :
    f ∈ Germ.weightedOrderIdeal a D := by
  obtain ⟨q, _, hf⟩ :=
    exists_finite_weighted_monomial_decomposition a D f hdiv
  rw [hf]
  apply Ideal.add_mem
  · apply Ideal.sum_mem
    intro k hk
    have hkD : k < D := Finset.mem_range.mp hk
    let j : Fin (D + 1) := ⟨k, by omega⟩
    have hj : Germ.weightedOrderGenerator a D j ∈
        Germ.weightedOrderIdeal a D :=
      Ideal.subset_span (Set.mem_range_self j)
    have heq :
        Germ.coordinate (0 : Fin 2) ^ k *
            Germ.coordinate (1 : Fin 2) ^ (D - a * k) *
              Germ.hyperplaneExtension 1 (q k) =
          Germ.hyperplaneExtension 1 (q k) *
            Germ.weightedOrderGenerator a D j := by
      simp only [Germ.weightedOrderGenerator, j]
      ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ hj
  · let j : Fin (D + 1) := ⟨D, by omega⟩
    have hj : Germ.weightedOrderGenerator a D j ∈
        Germ.weightedOrderIdeal a D :=
      Ideal.subset_span (Set.mem_range_self j)
    have hsub : D - a * D = 0 := by
      have hle : D ≤ a * D := by
        calc
          D = 1 * D := by simp
          _ ≤ a * D := Nat.mul_le_mul_right D ha
      omega
    have heq :
        Germ.coordinate (0 : Fin 2) ^ D *
            Germ.firstCoordinateTailIterate D f =
          Germ.firstCoordinateTailIterate D f *
            Germ.weightedOrderGenerator a D j := by
      simp [Germ.weightedOrderGenerator, j, hsub]
      ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ hj

end Germ

end OnLeConjecture.Analytic
