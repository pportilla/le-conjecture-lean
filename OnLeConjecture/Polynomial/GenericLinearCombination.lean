/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericFiniteGermFamilyChoice
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import OnLeConjecture.Polynomial.GenericPencil
public import OnLeConjecture.Polynomial.CommonFactorResidual

/-!
# Simultaneous coprime polynomial combinations

A common coefficient vector can avoid the roots of finitely many nonzero
polynomials, provided the corresponding generator polynomials have no common
zero at those roots. The coefficient vector can be chosen in any prescribed
nonempty open set. This supplies coprime pencils for the restrictions to
finitely many exceptional divisors.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial
open scoped BigOperators

/-- The polynomial linear combination with a specified coefficient row. -/
@[expose] noncomputable def polynomialLinearCombination
    {ι : Type*} [Fintype ι] (F : ι → ℂ[X]) : (ι → ℂ) →ₗ[ℂ] ℂ[X] where
  toFun q := ∑ i, q i • F i
  map_add' q r := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a q := by simp [Finset.smul_sum, mul_smul]

theorem polynomialLinearCombination_single
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℂ[X]) (i : ι) :
    polynomialLinearCombination F (Pi.single i 1) = F i := by
  simp [polynomialLinearCombination, Pi.single_apply]

/-- A common coefficient row avoids the roots of each prescribed nonzero
polynomial, simultaneously for a finite list of polynomial families. -/
theorem exists_coprime_linear_combinations_mem_open
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (P : κ → ℂ[X]) (hP : ∀ k, P k ≠ 0) (F : κ → ι → ℂ[X])
    (havoid : ∀ k z, (P k).eval z = 0 → ∃ i, (F k i).eval z ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∀ k, IsCoprime (P k) (polynomialLinearCombination (F k) q) := by
  classical
  let Roots := Σ k : κ, (P k).roots.toFinset
  let ell : Roots → (ι → ℂ) →ₗ[ℂ] ℂ := fun r =>
    (aeval (r.2.val : ℂ)).toLinearMap.comp (polynomialLinearCombination (F r.1))
  have hell (r : Roots) : ell r ≠ 0 := by
    obtain ⟨i, hi⟩ := havoid r.1 r.2.val
      ((mem_roots (hP r.1)).mp (Multiset.mem_toFinset.mp r.2.property))
    intro hz
    have h := LinearMap.congr_fun hz (Pi.single i 1)
    change aeval r.2.val (polynomialLinearCombination (F r.1) (Pi.single i 1)) = 0 at h
    rw [polynomialLinearCombination_single] at h
    exact hi (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using h)
  obtain ⟨q, hqU, hq⟩ := Analytic.exists_coefficients_avoiding_submodules_mem_open
    (fun r => LinearMap.ker (ell r))
    (fun r h => hell r (LinearMap.ker_eq_top.mp h)) U hU hUne
  refine ⟨q, hqU, fun k => ?_⟩
  apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ (P k)
    (polynomialLinearCombination (F k) q)).mpr
  intro z
  by_cases hz : (P k).eval z ≠ 0
  · exact Or.inl (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hz)
  · right
    let r : Roots := ⟨k, z, Multiset.mem_toFinset.mpr
      ((mem_roots (hP k)).mpr (not_not.mp hz))⟩
    exact hq r

/-- Finitely many polynomial families without common zeros have
simultaneously squarefree members for one common coefficient row in any
prescribed nonempty open set. -/
theorem exists_squarefree_linear_combinations_mem_open
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (F : κ → ι → ℂ[X])
    (hbase : ∀ k z, ∃ i, (F k i).eval z ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∀ k, Squarefree (polynomialLinearCombination (F k) q) := by
  classical
  let ell : κ → (ι → ℂ) →ₗ[ℂ] ℂ := fun k =>
    (aeval (0 : ℂ)).toLinearMap.comp (polynomialLinearCombination (F k))
  have hell (k : κ) : ell k ≠ 0 := by
    obtain ⟨i, hi⟩ := hbase k 0
    intro hz
    have h := LinearMap.congr_fun hz (Pi.single i 1)
    change aeval (0 : ℂ) (polynomialLinearCombination (F k) (Pi.single i 1)) = 0 at h
    rw [polynomialLinearCombination_single] at h
    exact hi (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using h)
  obtain ⟨q₀, hq₀U, hq₀⟩ := Analytic.exists_coefficients_avoiding_submodules_mem_open
    (fun k => LinearMap.ker (ell k))
    (fun k h => hell k (LinearMap.ker_eq_top.mp h)) U hU hUne
  let P : κ → ℂ[X] := fun k => polynomialLinearCombination (F k) q₀
  have hP (k : κ) : P k ≠ 0 := by
    intro hz
    apply hq₀ k
    change aeval (0 : ℂ) (P k) = 0
    rw [hz, map_zero]
  obtain ⟨r, _, hr⟩ := exists_coprime_linear_combinations_mem_open P hP F
    (fun k z _ => hbase k z) Set.univ isOpen_univ Set.univ_nonempty
  let Q : κ → ℂ[X] := fun k => polynomialLinearCombination (F k) r
  let bad : Set ℂ := ⋃ k, {c | ¬ Squarefree (P k + C c * Q k)}
  have hbad : bad.Finite := Set.finite_iUnion (fun k =>
    finite_not_squarefree_pencil (P k) (Q k) (hr k))
  let path : ℂ → (ι → ℂ) := fun c => q₀ + c • r
  have hcontinuous : Continuous path := by fun_prop
  have hopen : IsOpen (path ⁻¹' U) := hU.preimage hcontinuous
  have hzero : 0 ∈ path ⁻¹' U := by simpa [path] using hq₀U
  have hinfinite : (path ⁻¹' U).Infinite := infinite_of_mem_nhds 0 (hopen.mem_nhds hzero)
  obtain ⟨c, hcU, hc⟩ := hinfinite.exists_notMem_finite hbad
  refine ⟨path c, hcU, fun k => ?_⟩
  have hgood : Squarefree (P k + C c * Q k) := by
    by_contra h
    exact hc (Set.mem_iUnion.mpr ⟨k, h⟩)
  simpa only [path, map_add, map_smul, smul_eq_C_mul, P, Q] using hgood

/-- After removing each family's common factor, one coefficient row gives
squarefree residual polynomials at every index. The common zero sets and
factorizations are constructed from the original nonzero families. -/
theorem exists_squarefree_residual_combinations_mem_open
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (F : κ → ι → ℂ[X]) (hne : ∀ k, ∃ i, F k i ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (q : ι → ℂ) (G R : κ → ℂ[X]), q ∈ U ∧
      ∀ k, G k ≠ 0 ∧ Squarefree (R k) ∧
        polynomialLinearCombination (F k) q = G k * R k ∧
        (∀ z, (G k).eval z = 0 ↔ ∀ i, (F k i).eval z = 0) := by
  classical
  choose G H hG hfactor hbase hzero using
    fun k => exists_common_factor_residual (F k) (hne k)
  obtain ⟨q, hqU, hq⟩ := exists_squarefree_linear_combinations_mem_open H hbase U hU hUne
  refine ⟨q, G, fun k => polynomialLinearCombination (H k) q, hqU, fun k =>
    ⟨hG k, hq k, ?_, hzero k⟩⟩
  simp only [polynomialLinearCombination, LinearMap.coe_mk, AddHom.coe_mk,
    hfactor, Finset.mul_sum, smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The simultaneous residual selection also preserves finitely many
nonzero linear conditions, such as avoidance of specified exceptional
crossings. -/
theorem exists_squarefree_residual_combinations_linear_conditions_mem_open
    {κ ι τ : Type*} [Finite κ] [Fintype ι] [Finite τ]
    (F : κ → ι → ℂ[X]) (hne : ∀ k, ∃ i, F k i ≠ 0)
    (ell : τ → (ι → ℂ) →ₗ[ℂ] ℂ) (hell : ∀ j, ell j ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (q : ι → ℂ) (G R : κ → ℂ[X]), q ∈ U ∧ (∀ j, ell j q ≠ 0) ∧
      ∀ k, G k ≠ 0 ∧ Squarefree (R k) ∧
        polynomialLinearCombination (F k) q = G k * R k ∧
        (∀ z, (G k).eval z = 0 ↔ ∀ i, (F k i).eval z = 0) := by
  let V : Set (ι → ℂ) := U ∩ ⋂ j, {q | ell j q ≠ 0}
  have hV : IsOpen V := hU.inter (isOpen_iInter_of_finite fun j =>
    isOpen_ne.preimage (ell j).continuous_of_finiteDimensional)
  have hVne : V.Nonempty := by
    obtain ⟨q, hqU, hq⟩ := Analytic.exists_coefficients_avoiding_submodules_mem_open
      (fun j => LinearMap.ker (ell j))
      (fun j h => hell j (LinearMap.ker_eq_top.mp h)) U hU hUne
    exact ⟨q, hqU, Set.mem_iInter.mpr hq⟩
  obtain ⟨q, G, R, hqV, h⟩ := exists_squarefree_residual_combinations_mem_open F hne V hV hVne
  exact ⟨q, G, R, hqV.1, Set.mem_iInter.mp hqV.2, h⟩

end OnLeConjecture.Polynomial
