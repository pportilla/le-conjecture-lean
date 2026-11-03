/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.HomogeneousInitialForm
public import OnLeConjecture.Analytic.CoordinateOrder

/-!
# Homogeneous initial forms of a finite map germ

The components of a finite pointed map have homogeneous polynomial initial
forms in the common degree given by the order of their coordinate ideal. At
least one of these forms is nonzero.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- A finite pointed map admits homogeneous polynomial initial forms in its
coordinate ideal order, and at least one initial form is nonzero. -/
theorem exists_coordinateInitialForms
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    ∃ P : Fin m → MvPolynomial (Fin n) ℂ,
      (∀ i, (P i).IsHomogeneous (f.coordinateOrder hn hfinite)) ∧
      (∀ i, f.1.component i - Germ.coordinatePolynomialAlgHom n (P i) ∈
        Germ.maximalIdeal n ^ (f.coordinateOrder hn hfinite + 1)) ∧
      ∃ i, P i ≠ 0 := by
  have hexists : ∀ i : Fin m,
      ∃ p : MvPolynomial (Fin n) ℂ,
        p.IsHomogeneous (f.coordinateOrder hn hfinite) ∧
          f.1.component i - Germ.coordinatePolynomialAlgHom n p ∈
            Germ.maximalIdeal n ^ (f.coordinateOrder hn hfinite + 1) := by
    intro i
    exact Germ.exists_homogeneousInitialForm_of_mem_maximalIdeal_pow
      (f.1.component i)
      (f.component_mem_maximalIdeal_pow_coordinateOrder hn hfinite i)
  choose P hP htail using hexists
  refine ⟨P, hP, htail, ?_⟩
  obtain ⟨i, hi⟩ :=
    f.exists_component_not_mem_maximalIdeal_pow_coordinateOrder_add_one
      hn hfinite
  refine ⟨i, ?_⟩
  intro hzero
  have htaili := htail i
  rw [hzero, map_zero, sub_zero] at htaili
  exact hi htaili

/-- Under zero differential, the coordinate order is at least two and the
map has a nonzero tuple of homogeneous initial forms in that degree. -/
theorem exists_coordinateInitialForms_of_differential_eq_zero
    {n m : ℕ} (hn : 0 < n) (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) (hdf : f.differential = 0) :
    2 ≤ f.coordinateOrder hn hfinite ∧
      ∃ P : Fin m → MvPolynomial (Fin n) ℂ,
        (∀ i, (P i).IsHomogeneous (f.coordinateOrder hn hfinite)) ∧
        (∀ i, f.1.component i - Germ.coordinatePolynomialAlgHom n (P i) ∈
          Germ.maximalIdeal n ^ (f.coordinateOrder hn hfinite + 1)) ∧
        ∃ i, P i ≠ 0 := by
  exact ⟨f.two_le_coordinateOrder_of_differential_eq_zero hn hfinite hdf,
    f.exists_coordinateInitialForms hn hfinite⟩

end PointedMapGerm

end OnLeConjecture.Analytic
