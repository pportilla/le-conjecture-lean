/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ImageRing
public import OnLeConjecture.Analytic.Residue
public import OnLeConjecture.Analytic.Hadamard
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Finite analytic map germs

For a finite pointed map germ, the coordinate ideal is primary for the source
maximal ideal.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- For a finite pointed map germ, the radical of the coordinate ideal is the
source maximal ideal. -/
theorem radical_coordinateIdeal_eq_maximalIdeal {n m : ℕ}
    (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin) :
    f.1.coordinateIdeal.radical = Germ.maximalIdeal n := by
  let _ : Module.Finite f.ImageRing (Germ n) := hfinite
  apply le_antisymm
  · exact (Germ.maximalIdeal_isMaximal n).isPrime.radical_le_iff.mpr
      f.coordinateIdeal_le_maximalIdeal
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro Q hQ
    rcases hQ with ⟨hcoordinateQ, hQprime⟩
    let _ : Q.IsPrime := hQprime
    have himageQ :
        f.imageMaximalIdeal ≤ Ideal.comap f.ImageRing.subtype Q := by
      rw [← Ideal.map_le_iff_le_comap]
      rw [PointedMapGerm.map_imageMaximalIdeal_eq_coordinateIdeal f]
      exact hcoordinateQ
    have hcomapLe :
        Ideal.comap f.ImageRing.subtype Q ≤ f.imageMaximalIdeal := by
      rw [PointedMapGerm.imageMaximalIdeal_eq_isLocalRing f]
      exact IsLocalRing.le_maximalIdeal
        (Ideal.comap_ne_top f.ImageRing.subtype hQprime.ne_top)
    have hcomapEq :
        Ideal.comap f.ImageRing.subtype Q = f.imageMaximalIdeal :=
      le_antisymm hcomapLe himageQ
    have hQmaximal : Q.IsMaximal := by
      apply Ideal.IsIntegral.isMaximal_of_isMaximal_comap
        (R := f.ImageRing) Q
      rw [Algebra.algebraMap_ofSubring, hcomapEq]
      exact f.imageMaximalIdeal_isMaximal
    rw [Germ.maximalIdeal_eq_isLocalRing]
    exact (IsLocalRing.eq_maximalIdeal hQmaximal).symm.le

/-- The coordinate ideal of a finite pointed map germ is primary. -/
theorem coordinateIdeal_isPrimary_of_isFiniteAtOrigin {n m : ℕ}
    (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin) :
    f.1.coordinateIdeal.IsPrimary := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [f.radical_coordinateIdeal_eq_maximalIdeal hfinite]
  exact Germ.maximalIdeal_isMaximal n

end PointedMapGerm

namespace Germ

/-- The maximal ideal of the analytic germ ring is finitely generated. -/
theorem maximalIdeal_fg (n : ℕ) :
    (Germ.maximalIdeal n).FG := by
  rw [← Germ.span_range_coordinate_eq_maximalIdeal]
  exact Submodule.fg_span (Set.finite_range Germ.coordinate)

end Germ

namespace PointedMapGerm

/-- A power of the source maximal ideal is contained in the coordinate ideal
of a finite pointed map germ. -/
theorem exists_maximalIdeal_pow_le_coordinateIdeal {n m : ℕ}
    (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin) :
    ∃ N : ℕ, Germ.maximalIdeal n ^ N ≤ f.1.coordinateIdeal := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · rw [f.radical_coordinateIdeal_eq_maximalIdeal hfinite]
  · exact Germ.maximalIdeal_fg n

/-- For a finite pointed map germ with zero differential, the coordinate ideal
is primary for the source maximal ideal and is contained in its square. -/
theorem coordinateIdeal_primary_and_le_sq {n m : ℕ}
    (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin)
    (hdf : f.differential = 0) :
    f.1.coordinateIdeal.IsPrimary ∧
      f.1.coordinateIdeal ≤ Germ.maximalIdeal n ^ 2 := by
  exact ⟨f.coordinateIdeal_isPrimary_of_isFiniteAtOrigin hfinite,
    (f.differential_eq_zero_iff_coordinateIdeal_le_sq).mp hdf⟩

end PointedMapGerm

end OnLeConjecture.Analytic
