/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Residue
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The cotangent space of the analytic germ ring

The classes of the coordinate germs form a basis of the standard cotangent
space over the residue field.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- The class of a coordinate germ in the cotangent space of the local ring. -/
noncomputable def residueCotangentCoordinate {n : ℕ} (i : Fin n) :
    IsLocalRing.CotangentSpace (Germ n) :=
  (IsLocalRing.maximalIdeal (Germ n)).toCotangent
    ⟨Germ.coordinate i, by
      rw [← Germ.maximalIdeal_eq_isLocalRing n]
      exact Germ.coordinate_mem_maximalIdeal i⟩

/-- The coordinate classes span the cotangent space over the residue field. -/
theorem span_range_residueCotangentCoordinate_eq_top (n : ℕ) :
    Submodule.span (IsLocalRing.ResidueField (Germ n))
      (Set.range (Germ.residueCotangentCoordinate :
        Fin n → IsLocalRing.CotangentSpace (Germ n))) = ⊤ := by
  rw [eq_top_iff]
  intro q _hq
  obtain ⟨g, rfl⟩ :=
    (IsLocalRing.maximalIdeal (Germ n)).toCotangent_surjective q
  have hg : (g : Germ n) ∈ Germ.maximalIdeal n := by
    rw [Germ.maximalIdeal_eq_isLocalRing n]
    exact g.2
  obtain ⟨a, ha⟩ := Germ.exists_eq_sum_coordinate_mul hg
  have hsum :
      (IsLocalRing.maximalIdeal (Germ n)).toCotangent g =
        ∑ i, IsLocalRing.residue (Germ n) (a i) •
          Germ.residueCotangentCoordinate i := by
    have heq : g = ∑ i, a i •
        (⟨Germ.coordinate i, by
          rw [← Germ.maximalIdeal_eq_isLocalRing n]
          exact Germ.coordinate_mem_maximalIdeal i⟩ :
            IsLocalRing.maximalIdeal (Germ n)) := by
      apply Subtype.ext
      change (g : Germ n) =
        (IsLocalRing.maximalIdeal (Germ n)).subtype
          (∑ i, a i •
            (⟨Germ.coordinate i, by
              rw [← Germ.maximalIdeal_eq_isLocalRing n]
              exact Germ.coordinate_mem_maximalIdeal i⟩ :
                IsLocalRing.maximalIdeal (Germ n)))
      rw [map_sum]
      calc
        (g : Germ n) = ∑ i, Germ.coordinate i * a i := ha
        _ = ∑ i, a i * Germ.coordinate i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_comm]
        _ = ∑ i,
            (IsLocalRing.maximalIdeal (Germ n)).subtype
              (a i •
                (⟨Germ.coordinate i, by
                  rw [← Germ.maximalIdeal_eq_isLocalRing n]
                  exact Germ.coordinate_mem_maximalIdeal i⟩ :
                    IsLocalRing.maximalIdeal (Germ n))) := by
          apply Finset.sum_congr rfl
          intro i _
          rfl
    rw [heq, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (IsLocalRing.maximalIdeal (Germ n)).toCotangent
          (a i •
            (⟨Germ.coordinate i, by
              rw [← Germ.maximalIdeal_eq_isLocalRing n]
              exact Germ.coordinate_mem_maximalIdeal i⟩ :
                IsLocalRing.maximalIdeal (Germ n))) =
        a i • Germ.residueCotangentCoordinate i :=
          LinearMap.map_smul _ (a i) _
      _ = IsLocalRing.residue (Germ n) (a i) •
          Germ.residueCotangentCoordinate i := rfl
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i))

/-- The coordinate classes are linearly independent over the residue field. -/
theorem residueCotangentCoordinate_linearIndependent (n : ℕ) :
    LinearIndependent (IsLocalRing.ResidueField (Germ n))
      (Germ.residueCotangentCoordinate :
        Fin n → IsLocalRing.CotangentSpace (Germ n)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  choose a ha using fun i ↦
    IsLocalRing.residue_surjective (R := Germ n) (c i)
  have hc' : ∑ i, a i • Germ.residueCotangentCoordinate i = 0 := by
    calc
      ∑ i, a i • Germ.residueCotangentCoordinate i =
          ∑ i, IsLocalRing.residue (Germ n) (a i) •
            Germ.residueCotangentCoordinate i := by rfl
      _ = ∑ i, c i • Germ.residueCotangentCoordinate i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ha i]
      _ = 0 := hc
  let x : Fin n → IsLocalRing.maximalIdeal (Germ n) := fun i ↦
    ⟨Germ.coordinate i, by
      rw [← Germ.maximalIdeal_eq_isLocalRing n]
      exact Germ.coordinate_mem_maximalIdeal i⟩
  have hcotangent :
      (IsLocalRing.maximalIdeal (Germ n)).toCotangent
        (∑ i, a i • x i) = 0 := by
    rw [map_sum]
    calc
      ∑ i, (IsLocalRing.maximalIdeal (Germ n)).toCotangent
          (a i • x i) =
          ∑ i, a i • Germ.residueCotangentCoordinate i := by
            apply Finset.sum_congr rfl
            intro i _
            exact LinearMap.map_smul _ (a i) (x i)
      _ = 0 := hc'
  have hsquareStandard :
      ((∑ i, a i • x i : IsLocalRing.maximalIdeal (Germ n)) :
          Germ n) ∈ IsLocalRing.maximalIdeal (Germ n) ^ 2 :=
    ((IsLocalRing.maximalIdeal (Germ n)).toCotangent_eq_zero _).mp
      hcotangent
  have hsquare :
      ((∑ i, a i • x i : IsLocalRing.maximalIdeal (Germ n)) :
          Germ n) ∈ Germ.maximalIdeal n ^ 2 := by
    simpa only [Germ.maximalIdeal_eq_isLocalRing] using hsquareStandard
  have hdiff :
      Germ.differential
        (((∑ i, a i • x i : IsLocalRing.maximalIdeal (Germ n)) :
          Germ n)) = 0 :=
    (Germ.mem_firstOrderIdeal_iff.mp
      (Germ.maximalIdeal_sq_le_firstOrderIdeal n hsquare)).2
  have hcoe :
      (((∑ i, a i • x i : IsLocalRing.maximalIdeal (Germ n)) :
          Germ n)) = ∑ i, a i * Germ.coordinate i := by
    change ((IsLocalRing.maximalIdeal (Germ n)).subtype
      (∑ i, a i • x i)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    rfl
  rw [hcoe] at hdiff
  change Germ.differentialLinearMap n
      (∑ i, a i * Germ.coordinate i) = 0 at hdiff
  rw [map_sum] at hdiff
  have happ := congrArg
    (fun L : Source n →L[ℂ] ℂ ↦ L ((Pi.basisFun ℂ (Fin n)) j)) hdiff
  have hterm (i : Fin n) :
      (Germ.differentialLinearMap n
        (a i * Germ.coordinate i)) ((Pi.basisFun ℂ (Fin n)) j) =
          if j = i then Germ.valueRingHom n (a i) else 0 := by
    simp only [Germ.differentialLinearMap_apply,
      Germ.differential_mul, Germ.valueRingHom_coordinate,
      Pi.basisFun_apply]
    by_cases hji : j = i
    · subst i
      simp
    · have hij : i ≠ j := fun hij ↦ hji hij.symm
      simp [hji, hij]
  have hvalue : Germ.valueRingHom n (a j) = 0 := by
    rw [sum_apply, zero_apply] at happ
    simp_rw [hterm] at happ
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, if_true] using happ
  apply (Germ.residueFieldEquiv n).injective
  rw [map_zero]
  rw [← ha j, Germ.residueFieldEquiv_residue, hvalue]

/-- The coordinate classes form a basis of the cotangent space over the
residue field. -/
noncomputable def residueCotangentBasis (n : ℕ) :
    Module.Basis (Fin n) (IsLocalRing.ResidueField (Germ n))
      (IsLocalRing.CotangentSpace (Germ n)) :=
  Module.Basis.mk (Germ.residueCotangentCoordinate_linearIndependent n)
    (by rw [Germ.span_range_residueCotangentCoordinate_eq_top])

@[simp]
theorem residueCotangentBasis_apply (n : ℕ) (i : Fin n) :
    Germ.residueCotangentBasis n i =
      Germ.residueCotangentCoordinate i :=
  Module.Basis.mk_apply _ _ i

/-- The cotangent space has dimension `n` over the residue field. -/
theorem finrank_residueCotangentSpace (n : ℕ) :
    Module.finrank (IsLocalRing.ResidueField (Germ n))
      (IsLocalRing.CotangentSpace (Germ n)) = n := by
  rw [Module.finrank_eq_card_basis (Germ.residueCotangentBasis n),
    Fintype.card_fin]

end Germ

end OnLeConjecture.Analytic
