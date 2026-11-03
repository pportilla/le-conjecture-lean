/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeakTransformIdealData
public import Mathlib.Algebra.Module.Submodule.Union

/-!
# Simultaneous finite linear conditions on a point-basis member

Exact order at each recorded center excludes a proper linear subspace of
target coefficients. Any finite collection of nonzero linear conditions
can be imposed simultaneously. This statement does not assert generic
smoothness or completeness of a resolution for the newly chosen member.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

theorem PointedMapGerm.pullback_complex_smul {n m : ℕ}
    (f : PointedMapGerm n m) (a : ℂ) (q : Germ m) :
    f.pullbackRingHom (a • q) = a • f.pullbackRingHom q := by
  change f.pullbackRingHom (constRingHom m a * q) =
    constRingHom n a * f.pullbackRingHom q
  rw [map_mul, PointedMapGerm.pullback_constRingHom]

@[expose] noncomputable def germLinearCombination {ι : Type*} [Fintype ι]
    (F : ι → Germ 2) : (ι → ℂ) →ₗ[ℂ] Germ 2 where
  toFun q := ∑ i, q i • F i
  map_add' q r := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a q := by simp [Finset.smul_sum, mul_smul]

theorem germLinearCombination_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Germ 2) (i : ι) : germLinearCombination F (Pi.single i 1) = F i := by
  simp [germLinearCombination, Pi.single_apply]

theorem germLinearCombination_mem {ι : Type*} [Fintype ι]
    (F : ι → Germ 2) (I : Ideal (Germ 2)) (hF : ∀ i, F i ∈ I) (q : ι → ℂ) :
    germLinearCombination F q ∈ I := by
  exact (I.restrictScalars ℂ).sum_mem fun i _ =>
    (I.restrictScalars ℂ).smul_mem (q i) (hF i)

namespace WeakTransformIdealData

theorem exists_coefficients_exact_orders_and_linear_conditions
    {N : ℕ} {c : AnalyticPointBasis N} {ι κ : Type*} [Fintype ι] [Finite κ]
    (d : WeakTransformIdealData c ι)
    (ell : κ → (ι → ℂ) →ₗ[ℂ] ℂ) (hell : ∀ j, ell j ≠ 0) :
    ∃ q : ι → ℂ,
      (∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1)) ∧
      ∀ j, ell j q ≠ 0 := by
  classical
  let bad : Fin N ⊕ κ → Submodule ℂ (ι → ℂ) := Sum.elim
    (fun p => ((maximalIdeal 2 ^ (c.multiplicity p + 1)).restrictScalars ℂ).comap
      (germLinearCombination (d.generators p)))
    (fun j => LinearMap.ker (ell j))
  have hbad : ∀ j, bad j ≠ ⊤ := by
    intro j
    cases j with
    | inl p =>
      obtain ⟨i, hi⟩ : ∃ i, d.generators p i ∉ maximalIdeal 2 ^ (c.multiplicity p + 1) := by
        by_contra! h
        apply d.ideal_not_le_succ p
        rw [WeakTransformIdealData.ideal, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact h i
      intro heq
      have hmem : Pi.single i (1 : ℂ) ∈ bad (.inl p) := by rw [heq]; trivial
      change germLinearCombination (d.generators p) (Pi.single i 1) ∈
        maximalIdeal 2 ^ (c.multiplicity p + 1) at hmem
      exact hi (by simpa only [germLinearCombination_single] using hmem)
    | inr j =>
      change LinearMap.ker (ell j) ≠ ⊤
      intro hj
      exact hell j (LinearMap.ker_eq_top.mp hj)
  obtain ⟨q, hq⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨q, fun p => ⟨?_, hq (.inl p)⟩, fun j => hq (.inr j)⟩
  exact germLinearCombination_mem _ _ (d.generator_mem_pow p) q

/-- The same coefficients at every center satisfy the original analytic
strict-transform identities. -/
theorem linearCombination_transform
    {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*} [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ) (p : Fin N) (hp : p ≠ c.root) :
    (pointBlowupChartGerm (c.chartCenter p)).pullbackRingHom
        ((c.sourceCoordinates p).forward.pullbackRingHom
          (germLinearCombination (d.generators (c.predecessor p)) q)) =
      coordinate (1 : Fin 2) ^ c.multiplicity (c.predecessor p) *
        germLinearCombination (d.generators p) q := by
  change (pointBlowupChartGerm (c.chartCenter p)).pullbackRingHom
      ((c.sourceCoordinates p).forward.pullbackRingHom
        (∑ i, q i • d.generators (c.predecessor p) i)) =
    coordinate (1 : Fin 2) ^ c.multiplicity (c.predecessor p) *
      ∑ i, q i • d.generators p i
  simp only [map_sum, PointedMapGerm.pullback_complex_smul, d.transform_identity p hp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (mul_smul_comm _ _ _).symm

end WeakTransformIdealData

end OnLeConjecture.Analytic
