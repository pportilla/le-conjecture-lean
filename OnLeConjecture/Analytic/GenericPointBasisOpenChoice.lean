/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericPointBasisReconstruction
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Baire.Lemmas

/-!
# Point-basis member selection in an open set of coefficients

The exact-order conditions and finitely many nonzero linear conditions can
be imposed inside any nonempty open set. Thus an imported open set of
general-member reduction data can be retained during this choice.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic.WeakTransformIdealData

open OnLeConjecture.Analytic.Germ

theorem exists_coefficients_exact_orders_linear_conditions_mem_open
    {N : ℕ} {c : AnalyticPointBasis N} {ι κ : Type*} [Fintype ι] [Finite κ]
    (d : WeakTransformIdealData c ι)
    (ell : κ → (ι → ℂ) →ₗ[ℂ] ℂ) (hell : ∀ j, ell j ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U,
      (∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1)) ∧
      ∀ j, ell j q ≠ 0 := by
  classical
  obtain ⟨q₀, hq₀, hcondition₀⟩ :=
    d.exists_coefficients_exact_orders_and_linear_conditions ell hell
  let bad : Fin N ⊕ κ → Submodule ℂ (ι → ℂ) := Sum.elim
    (fun p => ((maximalIdeal 2 ^ (c.multiplicity p + 1)).restrictScalars ℂ).comap
      (germLinearCombination (d.generators p)))
    (fun j => LinearMap.ker (ell j))
  have hbad : ∀ j, bad j ≠ ⊤ := by
    intro j htop
    have hmem : q₀ ∈ bad j := by rw [htop]; trivial
    cases j with
    | inl p => exact (hq₀ p).2 hmem
    | inr j => exact hcondition₀ j hmem
  have hclosed (j) : IsClosed (bad j : Set (ι → ℂ)) :=
    (bad j).closed_of_finiteDimensional
  have hdense (j) : Dense (bad j : Set (ι → ℂ))ᶜ := by
    rw [← interior_eq_empty_iff_dense_compl, ← Set.not_nonempty_iff_eq_empty]
    intro hnonempty
    have : NeBot (𝓝[{x : ℂ | IsUnit x}] 0) := by
      have hset : {x : ℂ | IsUnit x} = ({0} : Set ℂ)ᶜ := by ext x; simp
      rw [hset]
      infer_instance
    exact hbad j ((bad j).eq_top_of_nonempty_interior' hnonempty)
  have hinter : Dense (⋂ j, (bad j : Set (ι → ℂ))ᶜ) :=
    dense_iInter_of_isOpen (fun j => (hclosed j).isOpen_compl) hdense
  obtain ⟨q, hqU, hqgood⟩ := hinter.inter_open_nonempty U hU hUne
  refine ⟨q, hqU, fun p => ⟨?_, (Set.mem_iInter.mp hqgood) (.inl p)⟩,
    fun j => (Set.mem_iInter.mp hqgood) (.inr j)⟩
  exact germLinearCombination_mem _ _ (d.generator_mem_pow p) q

end OnLeConjecture.Analytic.WeakTransformIdealData
