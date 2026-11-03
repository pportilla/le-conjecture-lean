/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteModuleDerivation
public import OnLeConjecture.Analytic.ImageConductorJacobian
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.Tactic.Module

/-!
# Coordinate Jacobians annihilate relative differentials

For a finite plane map, each coordinate Jacobian annihilates the module
of Kähler differentials of the source over the analytic image ring. The
analytic finite-module chain rule supplies the relations and a two-by-two
determinant calculation eliminates the coordinate differentials.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- The Jacobian of two germs in the kernel of a finite-module derivation
annihilates every value of that derivation. -/
theorem jacobian_smul_derivation_eq_zero
    {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (Germ 2) M]
    [IsScalarTower ℂ (Germ 2) M] [Module.Finite (Germ 2) M]
    (D : Derivation ℂ (Germ 2) M) (f h : Germ 2) (hf : D f = 0) (hh : D h = 0)
    (a : Germ 2) : jacobian f h • D a = 0 := by
  have hrowf := derivation_eq_sum_partialDerivatives_smul D f
  have hrowh := derivation_eq_sum_partialDerivatives_smul D h
  rw [hf, Fin.sum_univ_two] at hrowf
  rw [hh, Fin.sum_univ_two] at hrowh
  have hdx : jacobian f h • D (coordinate 0) = 0 := by
    calc
      _ = partialDerivative 1 h •
          (partialDerivative 0 f • D (coordinate 0) + partialDerivative 1 f • D (coordinate 1)) -
        partialDerivative 1 f •
          (partialDerivative 0 h • D (coordinate 0) +
            partialDerivative 1 h • D (coordinate 1)) := by
            rw [jacobian_eq]
            module
      _ = 0 := by rw [← hrowf, ← hrowh]; simp
  have hdy : jacobian f h • D (coordinate 1) = 0 := by
    calc
      _ = partialDerivative 0 f •
          (partialDerivative 0 h • D (coordinate 0) + partialDerivative 1 h • D (coordinate 1)) -
        partialDerivative 0 h •
          (partialDerivative 0 f • D (coordinate 0) +
            partialDerivative 1 f • D (coordinate 1)) := by
            rw [jacobian_eq]
            module
      _ = 0 := by rw [← hrowf, ← hrowh]; simp
  rw [derivation_eq_sum_partialDerivatives_smul D a, Fin.sum_univ_two, smul_add]
  rw [smul_comm (jacobian f h) (partialDerivative 0 a), hdx,
    smul_comm (jacobian f h) (partialDerivative 1 a), hdy]
  simp

namespace PointedMapGerm

/-- A coordinate Jacobian annihilates the actual relative differential
module of a finite analytic plane map. -/
theorem coordinate_jacobian_mem_annihilator_kaehler
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin) (i j : Fin m) :
    jacobian (g.1.component i) (g.1.component j) ∈
      Module.annihilator (Germ 2) (KaehlerDifferential g.ImageRing (Germ 2)) := by
  let _ : Module.Finite g.ImageRing (Germ 2) := hf
  let _ : Algebra ℂ g.ImageRing :=
    (g.pullbackToImageRing.comp (constRingHom m)).toAlgebra
  let _ : IsScalarTower ℂ g.ImageRing (Germ 2) :=
    IsScalarTower.of_algebraMap_eq fun c => (g.pullback_constRingHom c).symm
  let M := KaehlerDifferential g.ImageRing (Germ 2)
  let D₀ := KaehlerDifferential.D g.ImageRing (Germ 2)
  let D : Derivation ℂ (Germ 2) M := D₀.restrictScalars ℂ
  have hD (k : Fin m) : D (g.1.component k) = 0 := by
    have hk : algebraMap g.ImageRing (Germ 2) (g.pullbackToImageRing (coordinate k)) =
        g.1.component k := g.pullback_coordinate k
    change D₀ (g.1.component k) = 0
    rw [← hk]
    exact D₀.map_algebraMap _
  rw [Module.mem_annihilator]
  intro ω
  have hω : ω ∈ Submodule.span (Germ 2) (Set.range D₀) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, rfl⟩ := hv
    exact jacobian_smul_derivation_eq_zero D _ _ (hD i) (hD j) a
  | zero => exact smul_zero _
  | add a b _ _ ha hb => rw [smul_add, ha, hb, add_zero]
  | smul r a _ ha => rw [smul_comm, ha, smul_zero]

/-- The full ideal of coordinate minors annihilates relative differentials. -/
theorem coordinateMinorIdeal_le_annihilator_kaehler
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin) :
    g.coordinateMinorIdeal ≤
      Module.annihilator (Germ 2) (KaehlerDifferential g.ImageRing (Germ 2)) := by
  rw [coordinateMinorIdeal, Ideal.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact g.coordinate_jacobian_mem_annihilator_kaehler hf i j

/-- A finite plane map is unramified at every prime that omits a coordinate
Jacobian. -/
theorem isUnramifiedAt_of_coordinate_jacobian_not_mem
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin)
    (q : Ideal (Germ 2)) [q.IsPrime] (i j : Fin m)
    (hq : jacobian (g.1.component i) (g.1.component j) ∉ q) :
    Algebra.IsUnramifiedAt g.ImageRing q := by
  change (⟨q, inferInstance⟩ : PrimeSpectrum (Germ 2)) ∈
    Algebra.unramifiedLocus g.ImageRing (Germ 2)
  rw [Algebra.unramifiedLocus_eq_compl_support]
  intro hsupport
  exact hq (Module.annihilator_le_of_mem_support hsupport
    (g.coordinate_jacobian_mem_annihilator_kaehler hf i j))

end PointedMapGerm

end OnLeConjecture.Analytic
