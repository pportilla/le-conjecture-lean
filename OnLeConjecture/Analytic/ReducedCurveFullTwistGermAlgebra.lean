/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.BranchCountAdditivity
public import OnLeConjecture.PlaneCurve.FirstAxisFiniteIntersection
public import OnLeConjecture.Analytic.IntersectionAdditivity
public import OnLeConjecture.Analytic.PointBlowupIntersection
public import OnLeConjecture.Analytic.ProjectiveBlowupSquareFactor
public import OnLeConjecture.Analytic.TeissierPolarIdentity
public import OnLeConjecture.Analytic.IntersectionParametrizationMultiplicity
public import OnLeConjecture.Analytic.RegularIrreducibleFactorization
public import OnLeConjecture.Analytic.SourceConservation
public import OnLeConjecture.Analytic.PlaneSectionSpecialization
import all OnLeConjecture.PlaneCurve.AnalyticBranchCount

/-!
# Algebraic preliminaries for the transverse reduced germ

For a reduced plane germ `f`, the irreducible branch count `b` of
`PlaneCurve.irreducibleBranchCount` is realized by a factorization `f = u ∏_{i < b} f_i` into
pairwise nonassociated irreducible germs and a unit (`exists_branch_factorization`). This
module proves the additivity of the intersection multiplicity with a fixed germ over such a
finite product, and the additivity of exact maximal-ideal orders.

These are the algebraic inputs of Lemma `J14:lem:packaging` of the written proof: the
degrees `a_i = i₀(f_i, ξ)` sum to `i₀(f, ξ)`, and the multiplicities of the branches sum to the
multiplicity of `f`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve UniqueFactorizationMonoid

/-- A reduced germ is a unit times the product of `irreducibleBranchCount f` pairwise
nonassociated irreducible germs. -/
theorem exists_branch_factorization (f : Germ 2) (hsq : Squarefree f) :
    ∃ (F : Fin (irreducibleBranchCount f) → Germ 2) (u : Germ 2), IsUnit u ∧
      f = u * ∏ i, F i ∧ (∀ i, Irreducible (F i)) ∧
      (∀ i j, i ≠ j → ¬ Associated (F i) (F j)) := by
  classical
  have hf0 : f ≠ 0 := hsq.ne_zero
  have hmk0 : Associates.mk f ≠ 0 := by simpa using hf0
  have hsqA : Squarefree (Associates.mk f) := by
    intro y hy
    obtain ⟨y', rfl⟩ := Associates.mk_surjective y
    rw [Associates.mk_mul_mk, Associates.mk_dvd_mk] at hy
    exact Associates.isUnit_mk.mpr (hsq y' hy)
  set A := normalizedFactors (Associates.mk f) with hA
  have hnodup : A.Nodup := (squarefree_iff_nodup_normalizedFactors hmk0).mp hsqA
  set T := A.toFinset with hT
  have hcard : T.card = irreducibleBranchCount f := by
    rw [irreducibleBranchCount]
  let e : T ≃ Fin (irreducibleBranchCount f) := T.equivFin.trans (finCongr hcard)
  let F : Fin (irreducibleBranchCount f) → Germ 2 := fun i =>
    Classical.choose (Associates.mk_surjective ((e.symm i : T) : Associates (Germ 2)))
  have hmkF : ∀ i, Associates.mk (F i) = (e.symm i : Associates (Germ 2)) := fun i =>
    Classical.choose_spec (Associates.mk_surjective ((e.symm i : T) : Associates (Germ 2)))
  have hirr : ∀ i, Irreducible (F i) := by
    intro i
    rw [← Associates.irreducible_mk, hmkF]
    exact irreducible_of_normalized_factor _ (Multiset.mem_toFinset.mp (e.symm i).2)
  have hprodA : Associates.mk (∏ i, F i) = Associates.mk f := by
    rw [← Associates.mkMonoidHom_apply, map_prod]
    simp only [Associates.mkMonoidHom_apply, hmkF]
    rw [Equiv.prod_comp e.symm (fun x : T => (x : Associates (Germ 2))),
      Finset.prod_coe_sort T (fun x => x)]
    have hTval : T.val = A := by
      rw [hT, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
    change (T.val.map id).prod = _
    rw [Multiset.map_id, hTval]
    exact associated_iff_eq.mp (prod_normalizedFactors hmk0)
  obtain ⟨u, hu⟩ := Associates.mk_eq_mk_iff_associated.mp hprodA
  refine ⟨F, (u : Germ 2), u.isUnit, ?_, hirr, ?_⟩
  · rw [mul_comm]
    exact hu.symm
  · intro i j hij hass
    apply hij
    apply e.symm.injective
    apply Subtype.ext
    rw [← hmkF, ← hmkF]
    exact Associates.mk_eq_mk_iff_associated.mpr hass

/-- Finite intersection with a product implies finite intersection with every factor. -/
theorem hasFiniteIntersection_prod_iff (h : Germ 2) {n : ℕ} (F : Fin n → Germ 2) :
    HasFiniteIntersection h (∏ i, F i) ↔ ∀ i, HasFiniteIntersection h (F i) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, IsEmpty.forall_iff, iff_true]
    exact hasFiniteIntersection_of_isUnit_right isUnit_one
  | succ n ih =>
    rw [Fin.prod_univ_succ, hasFiniteIntersection_mul_right_iff, ih, Fin.forall_fin_succ]

/-- Additivity of the intersection multiplicity with `h` over a finite product. -/
theorem intersectionMultiplicity_prod (h : Germ 2) {n : ℕ} (F : Fin n → Germ 2)
    (hfin : HasFiniteIntersection h (∏ i, F i))
    (hfin' : ∀ i, HasFiniteIntersection h (F i)) :
    intersectionMultiplicity h (∏ i, F i) hfin =
      ∑ i, intersectionMultiplicity h (F i) (hfin' i) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact intersectionMultiplicity_eq_zero_of_isUnit_right h _ (by simp) hfin
  | succ n ih =>
    have hprod : HasFiniteIntersection h ((F 0) * ∏ i : Fin n, F i.succ) := by
      rw [← Fin.prod_univ_succ]
      exact hfin
    have htail : HasFiniteIntersection h (∏ i : Fin n, F i.succ) :=
      ((hasFiniteIntersection_mul_right_iff _ _ _).mp hprod).2
    rw [Fin.sum_univ_succ, ← ih (fun i => F i.succ) htail (fun i => hfin' i.succ),
      ← intersectionMultiplicity_mul_right h (F 0) _ (hfin' 0) htail hprod]
    exact intersectionMultiplicity_congr rfl (Fin.prod_univ_succ F) hfin hprod

/-- Exact maximal-ideal orders add over finite products. -/
theorem exact_maximalIdeal_order_prod {n : ℕ} (F : Fin n → Germ 2) (m : Fin n → ℕ)
    (hm : ∀ i, F i ∈ maximalIdeal 2 ^ m i) (hmn : ∀ i, F i ∉ maximalIdeal 2 ^ (m i + 1)) :
    ∏ i, F i ∈ maximalIdeal 2 ^ (∑ i, m i) ∧ ∏ i, F i ∉ maximalIdeal 2 ^ (∑ i, m i + 1) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, pow_zero,
      Ideal.one_eq_top, Submodule.mem_top, zero_add, pow_one, true_and]
    intro h1
    rw [mem_maximalIdeal_iff] at h1
    simp at h1
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (fun i => F i.succ) (fun i => m i.succ) (fun i => hm i.succ)
      (fun i => hmn i.succ)
    have h := exact_maximalIdeal_order_mul (m 0) (∑ i : Fin n, m i.succ) (F 0)
      (∏ i : Fin n, F i.succ) (hm 0) (hmn 0) h1 h2
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    exact h

end OnLeConjecture.Analytic
