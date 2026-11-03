/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericFiniteGermFamilyChoice
public import OnLeConjecture.Analytic.OneVariableOrder

/-!
# Common generic coefficient rows on finitely many parametrized branches

The order of a generic linear combination of one-variable analytic germs
is the minimum of their orders. One open dense coefficient set works for
every member of a finite family. It can therefore be intersected with the
open coefficient sets used to choose companion sections on a resolution.
-/

public noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Linear combinations of curve germs, with one common coefficient row. -/
@[expose] def curveGermLinearCombination {ι : Type*} [Fintype ι]
    (F : ι → Germ 1) : (ι → ℂ) →ₗ[ℂ] Germ 1 where
  toFun q := ∑ i, q i • F i
  map_add' q r := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a q := by simp [Finset.smul_sum, mul_smul]

theorem curveGermLinearCombination_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Germ 1) (i : ι) : curveGermLinearCombination F (Pi.single i 1) = F i := by
  simp [curveGermLinearCombination, Pi.single_apply]

/-- Exact orders hold simultaneously on an open dense coefficient set. -/
theorem exists_open_dense_curve_combinations_exact_order
    {α ι : Type*} [Finite α] [Fintype ι]
    (F : α → ι → Germ 1) (m : α → ℕ)
    (horder : ∀ p i, (m p : ℕ∞) ≤ vanishingOrder (F p i))
    (hexact : ∀ p, ∃ i, vanishingOrder (F p i) = m p) :
    ∃ U : Set (ι → ℂ), IsOpen U ∧ Dense U ∧
      ∀ q ∈ U, ∀ p, vanishingOrder (curveGermLinearCombination (F p) q) = m p := by
  classical
  let bad : α → Submodule ℂ (ι → ℂ) := fun p =>
    ((maximalIdeal 1 ^ (m p + 1)).restrictScalars ℂ).comap (curveGermLinearCombination (F p))
  have hbad (p : α) : bad p ≠ ⊤ := by
    obtain ⟨i, hi⟩ := hexact p
    intro htop
    have hmem : Pi.single i (1 : ℂ) ∈ bad p := by rw [htop]; trivial
    change curveGermLinearCombination (F p) (Pi.single i 1) ∈
      maximalIdeal 1 ^ (m p + 1) at hmem
    rw [curveGermLinearCombination_single, mem_maximalIdeal_one_pow_iff, hi] at hmem
    exact (not_le.mpr (by exact_mod_cast Nat.lt_succ_self (m p))) hmem
  let U : Set (ι → ℂ) := ⋂ p, (bad p : Set (ι → ℂ))ᶜ
  have hU : IsOpen U := isOpen_iInter_of_finite fun p =>
    (bad p).closed_of_finiteDimensional.isOpen_compl
  have hdense : Dense U := by
    rw [dense_iff_inter_open]
    intro V hV hVne
    obtain ⟨q, hqV, hq⟩ := exists_coefficients_avoiding_submodules_mem_open bad hbad V hV hVne
    exact ⟨q, hqV, mem_iInter.mpr hq⟩
  refine ⟨U, hU, hdense, ?_⟩
  intro q hq p
  have hlo : (m p : ℕ∞) ≤ vanishingOrder (curveGermLinearCombination (F p) q) := by
    rw [← mem_maximalIdeal_one_pow_iff]
    exact ((maximalIdeal 1 ^ m p).restrictScalars ℂ).sum_mem fun i _ =>
      ((maximalIdeal 1 ^ m p).restrictScalars ℂ).smul_mem (q i)
        (mem_maximalIdeal_one_pow_iff.mpr (horder p i))
  have hhi : ¬ ((m p + 1 : ℕ) : ℕ∞) ≤
      vanishingOrder (curveGermLinearCombination (F p) q) := by
    rw [← mem_maximalIdeal_one_pow_iff]
    exact (mem_iInter.mp hq) p
  apply le_antisymm _ hlo
  apply (ENat.lt_add_one_iff (ENat.natCast_ne_top (m p))).mp
  simpa only [Nat.cast_add, Nat.cast_one] using lt_of_not_ge hhi

/-- Each nonzero finite family has a finite attained minimum order. -/
theorem exists_minimum_curve_germ_order {ι : Type*} [Finite ι]
    (F : ι → Germ 1) (hne : ∃ i, F i ≠ 0) :
    ∃ m : ℕ, (∀ i, (m : ℕ∞) ≤ vanishingOrder (F i)) ∧
      (∃ i, vanishingOrder (F i) = m) ∧
      (m : ℕ∞) = ⨅ i, vanishingOrder (F i) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨j, hj⟩ := hne
  have : Nonempty ι := ⟨j⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i => vanishingOrder (F i)) Finset.univ_nonempty
  have hmin (k : ι) : vanishingOrder (F i) ≤ vanishingOrder (F k) :=
    hi k (Finset.mem_univ k)
  have hfinite : vanishingOrder (F i) ≠ ⊤ :=
    ne_top_of_le_ne_top (vanishingOrder_eq_top_iff.not.mpr hj) (hmin j)
  have hcast : ((vanishingOrder (F i)).toNat : ℕ∞) = vanishingOrder (F i) :=
    ENat.natCast_toNat hfinite
  refine ⟨(vanishingOrder (F i)).toNat, ?_, ⟨i, hcast.symm⟩, ?_⟩
  · intro k
    rw [hcast]
    exact hmin k
  · rw [hcast]
    exact le_antisymm (le_iInf hmin) (iInf_le _ i)

/-- A common coefficient row realizes the actual minimum order of every
branch on one open dense set. Zero generators are allowed. -/
theorem exists_open_dense_curve_combinations_minimum_order
    {α ι : Type*} [Finite α] [Fintype ι]
    (F : α → ι → Germ 1) (hne : ∀ p, ∃ i, F p i ≠ 0) :
    ∃ U : Set (ι → ℂ), IsOpen U ∧ Dense U ∧
      ∀ q ∈ U, ∀ p, vanishingOrder (curveGermLinearCombination (F p) q) =
        ⨅ i, vanishingOrder (F p i) := by
  choose m hm he hmin using fun p => exists_minimum_curve_germ_order (F p) (hne p)
  obtain ⟨U, hU, hdense, h⟩ := exists_open_dense_curve_combinations_exact_order F m hm he
  exact ⟨U, hU, hdense, fun q hq p => (h q hq p).trans (hmin p)⟩

/-- Restriction of a plane linear combination to a curve uses the same
coefficient row on the restricted germs. -/
theorem PointedMapGerm.pullback_germLinearCombination_curve
    {ι : Type*} [Fintype ι] (γ : PointedMapGerm 1 2)
    (F : ι → Germ 2) (q : ι → ℂ) :
    γ.pullbackRingHom (germLinearCombination F q) =
      curveGermLinearCombination (fun i => γ.pullbackRingHom (F i)) q := by
  simp only [germLinearCombination, curveGermLinearCombination, LinearMap.coe_mk,
    AddHom.coe_mk, map_sum, PointedMapGerm.pullback_complex_smul]

/-- One open dense coefficient set realizes all minimum orders on the
given finite collection of actual parametrized source branches. -/
theorem exists_open_dense_pullback_combinations_minimum_order
    {α ι : Type*} [Finite α] [Fintype ι]
    (F : ι → Germ 2) (γ : α → PointedMapGerm 1 2)
    (hne : ∀ p, ∃ i, (γ p).pullbackRingHom (F i) ≠ 0) :
    ∃ U : Set (ι → ℂ), IsOpen U ∧ Dense U ∧
      ∀ q ∈ U, ∀ p,
        vanishingOrder ((γ p).pullbackRingHom (germLinearCombination F q)) =
          ⨅ i, vanishingOrder ((γ p).pullbackRingHom (F i)) := by
  obtain ⟨U, hU, hdense, h⟩ := exists_open_dense_curve_combinations_minimum_order
    (fun p i => (γ p).pullbackRingHom (F i)) hne
  exact ⟨U, hU, hdense, fun q hq p => by
    rw [(γ p).pullback_germLinearCombination_curve]
    exact h q hq p⟩

end OnLeConjecture.Analytic
