/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericPointBasisMember
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Baire.Lemmas

/-!
# Generic exact orders for a finite family of analytic generator families

At each member of a finite index set, all generators have a prescribed
order bound and at least one attains that order. One coefficient vector
can be chosen to attain every order simultaneously, inside any prescribed
nonempty open coefficient set. Finitely many nonzero linear conditions
can be retained as well. No analytic point-basis record or resolution
assumption is required.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- A finite family of proper complex subspaces can be avoided inside
any nonempty open coefficient set. -/
theorem exists_coefficients_avoiding_submodules_mem_open
    {ι κ : Type*} [Finite ι] [Finite κ]
    (bad : κ → Submodule ℂ (ι → ℂ)) (hbad : ∀ j, bad j ≠ ⊤)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∀ j, q ∉ bad j := by
  classical
  let := Fintype.ofFinite ι
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
  exact ⟨q, hqU, fun j => (Set.mem_iInter.mp hqgood) j⟩

/-- Exact orders at every index and all specified linear nonvanishing
conditions are achieved by a single coefficient vector in the supplied
open set. The orders may be zero, and the index sets may be empty. -/
theorem exists_coefficients_exact_orders_linear_conditions_mem_open
    {α ι κ : Type*} [Finite α] [Fintype ι] [Finite κ]
    (F : α → ι → Germ 2) (m : α → ℕ)
    (horder : ∀ p i, F p i ∈ maximalIdeal 2 ^ m p)
    (hexact : ∀ p, ∃ i, F p i ∉ maximalIdeal 2 ^ (m p + 1))
    (ell : κ → (ι → ℂ) →ₗ[ℂ] ℂ) (hell : ∀ j, ell j ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U,
      (∀ p, germLinearCombination (F p) q ∈ maximalIdeal 2 ^ m p ∧
        germLinearCombination (F p) q ∉ maximalIdeal 2 ^ (m p + 1)) ∧
      ∀ j, ell j q ≠ 0 := by
  classical
  let bad : α ⊕ κ → Submodule ℂ (ι → ℂ) := Sum.elim
    (fun p => ((maximalIdeal 2 ^ (m p + 1)).restrictScalars ℂ).comap
      (germLinearCombination (F p)))
    (fun j => LinearMap.ker (ell j))
  have hbad : ∀ j, bad j ≠ ⊤ := by
    intro j
    cases j with
    | inl p =>
        obtain ⟨i, hi⟩ := hexact p
        intro htop
        have hmem : Pi.single i (1 : ℂ) ∈ bad (.inl p) := by rw [htop]; trivial
        change germLinearCombination (F p) (Pi.single i 1) ∈
          maximalIdeal 2 ^ (m p + 1) at hmem
        exact hi (by simpa only [germLinearCombination_single] using hmem)
    | inr j =>
        change LinearMap.ker (ell j) ≠ ⊤
        exact fun htop => hell j (LinearMap.ker_eq_top.mp htop)
  obtain ⟨q, hqU, hq⟩ :=
    exists_coefficients_avoiding_submodules_mem_open bad hbad U hU hUne
  exact ⟨q, hqU, fun p => ⟨germLinearCombination_mem _ _ (horder p) q, hq (.inl p)⟩,
    fun j => hq (.inr j)⟩

theorem exists_coefficients_exact_orders_mem_open
    {α ι : Type*} [Finite α] [Fintype ι]
    (F : α → ι → Germ 2) (m : α → ℕ)
    (horder : ∀ p i, F p i ∈ maximalIdeal 2 ^ m p)
    (hexact : ∀ p, ∃ i, F p i ∉ maximalIdeal 2 ^ (m p + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∀ p,
      germLinearCombination (F p) q ∈ maximalIdeal 2 ^ m p ∧
      germLinearCombination (F p) q ∉ maximalIdeal 2 ^ (m p + 1) := by
  obtain ⟨q, hqU, hq, _⟩ := exists_coefficients_exact_orders_linear_conditions_mem_open
    F m horder hexact (fun j : Empty => j.elim) (fun j => j.elim) U hU hUne
  exact ⟨q, hqU, hq⟩

theorem exists_coefficients_exact_orders
    {α ι : Type*} [Finite α] [Fintype ι]
    (F : α → ι → Germ 2) (m : α → ℕ)
    (horder : ∀ p i, F p i ∈ maximalIdeal 2 ^ m p)
    (hexact : ∀ p, ∃ i, F p i ∉ maximalIdeal 2 ^ (m p + 1)) :
    ∃ q : ι → ℂ, ∀ p,
      germLinearCombination (F p) q ∈ maximalIdeal 2 ^ m p ∧
      germLinearCombination (F p) q ∉ maximalIdeal 2 ^ (m p + 1) := by
  obtain ⟨q, _, hq⟩ := exists_coefficients_exact_orders_mem_open
    F m horder hexact Set.univ isOpen_univ Set.univ_nonempty
  exact ⟨q, hq⟩

end OnLeConjecture.Analytic
