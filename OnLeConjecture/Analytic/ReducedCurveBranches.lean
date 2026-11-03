/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CriticalDivisorZeroSet
public import OnLeConjecture.PlaneCurve.IrreducibleFiniteIntersection
public import OnLeConjecture.Analytic.WeightedMonomialDivision

/-!
# Representatives of the irreducible branches of a reduced plane curve

Unique factorization constructs a finite family of distinct irreducible
equations. Their representative zero sets cover the original zero set near
the origin. Finite intersection proves that two distinct branches have no
common point in a sufficiently small punctured neighborhood.
-/

public noncomputable section

open Filter Set UniqueFactorizationMonoid
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic.Germ

/-- Distinct irreducible analytic branches meet only at the origin nearby. -/
theorem eventually_common_zero_imp_eq_zero_of_nonassociated
    (F G : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (hf : Irreducible (ofFunction F hF)) (hg : Irreducible (ofFunction G hG))
    (hfg : ¬ Associated (ofFunction F hF) (ofFunction G hG)) :
    ∀ᶠ z in 𝓝 (0 : Source 2), F z = 0 → G z = 0 → z = 0 := by
  let P : Fin 2 → Source 2 → ℂ := ![F, G]
  have hP : ∀ i, AnalyticAt ℂ (P i) 0 := by
    intro i
    fin_cases i
    · exact hF
    · exact hG
  have heq : Set.range (fun i => ofFunction (P i) (hP i)) =
      {ofFunction F hF, ofFunction G hG} := by
    ext f
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [P]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hfinite : Module.Finite ℂ
      (Germ 2 ⧸ Ideal.span (Set.range (fun i => ofFunction (P i) (hP i)))) := by
    rw [heq]
    exact PlaneCurve.hasFiniteIntersection_of_irreducible_not_associated _ _ hf hg hfg
  filter_upwards [eventually_common_zero_imp_eq_zero_of_finite_colength P hP hfinite]
    with z hz hFz hGz
  apply hz
  intro i
  fin_cases i
  · exact hFz
  · exact hGz

/-- A reduced analytic equation admits finitely many distinct irreducible
branch representatives, with the exact local union and punctured separation. -/
theorem exists_separated_branch_representatives_of_squarefree
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∃ (s : Finset (Germ 2)) (P : s → Source 2 → ℂ)
      (hP : ∀ i, AnalyticAt ℂ (P i) 0),
      (∀ i : s, (i : Germ 2) = ofFunction (P i) (hP i)) ∧
      (∀ i, Irreducible (ofFunction (P i) (hP i))) ∧
      (∀ i j, i ≠ j → ¬ Associated (ofFunction (P i) (hP i))
        (ofFunction (P j) (hP j))) ∧
      (∀ᶠ z in 𝓝 (0 : Source 2), H z = 0 ↔ ∃ i, P i z = 0) ∧
      (∀ᶠ z in 𝓝 (0 : Source 2), ∀ i j, i ≠ j → P i z = 0 → P j z = 0 → z = 0) := by
  classical
  let : StrongNormalizationMonoid (Germ 2) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let f := ofFunction H hH
  let s : Finset (Germ 2) := (normalizedFactors f).toFinset
  have hmem (i : s) : (i : Germ 2) ∈ normalizedFactors f :=
    Multiset.mem_toFinset.mp i.property
  have hirr (i : s) : Irreducible (i : Germ 2) :=
    irreducible_of_normalized_factor _ (hmem i)
  have hsep (i j : s) (hij : i ≠ j) : ¬ Associated (i : Germ 2) (j : Germ 2) := by
    intro h
    exact hij (Subtype.ext (mem_normalizedFactors_eq_of_associated (hmem i) (hmem j) h))
  have hnodup : (normalizedFactors f).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hsq.ne_zero).mp hsq
  have hprod : (∏ i : s, (i : Germ 2)) = (normalizedFactors f).prod := by
    rw [Finset.prod_coe_sort s (fun x => x)]
    change (s.val.map id).prod = _
    rw [Multiset.map_id]
    change (normalizedFactors f).toFinset.val.prod = _
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  obtain ⟨u, hu⟩ := prod_normalizedFactors hsq.ne_zero
  choose P hP hp using fun i : s => exists_ofFunction (i : Germ 2)
  obtain ⟨U, hU, huU⟩ := exists_ofFunction (u : Germ 2)
  have hU0 : U 0 ≠ 0 := by
    simpa only [huU, valueRingHom_ofFunction] using valueRingHom_ne_zero_of_isUnit u.isUnit
  let Q : Source 2 → ℂ := fun z => ∏ i, P i z
  have hQ : AnalyticAt ℂ Q 0 := Finset.univ.analyticAt_fun_prod fun i _ => hP i
  have hQgerm : ofFunction Q hQ = ∏ i, ofFunction (P i) (hP i) := by
    apply Subtype.ext
    change (Filter.Germ.coeRingHom (𝓝 (0 : Source 2))) Q =
      (analyticGermSubring 2).subtype (∏ i, ofFunction (P i) (hP i))
    have hQfun : Q = ∏ i, P i := by ext z; simp only [Q, Finset.prod_apply]
    rw [hQfun, map_prod, map_prod]
    rfl
  have hfactor : ofFunction H hH = ofFunction (fun z => U z * Q z) (hU.mul hQ) := by
    change f = ofFunction U hU * ofFunction Q hQ
    rw [hQgerm, ← huU, ← funext hp]
    rw [hprod, mul_comm]
    exact hu.symm
  have hpoint := Filter.Germ.coe_eq.mp (congrArg Subtype.val hfactor)
  refine ⟨s, P, hP, hp, fun i => hp i ▸ hirr i,
    fun i j hij => by simpa only [← hp] using hsep i j hij, ?_, ?_⟩
  · filter_upwards [hpoint, hU.continuousAt.eventually_ne hU0] with z hz hUz
    rw [hz, mul_eq_zero, or_iff_right hUz]
    simp only [Q, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  · have hpair (i j : s) : ∀ᶠ z in 𝓝 (0 : Source 2),
        i ≠ j → P i z = 0 → P j z = 0 → z = 0 := by
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
      · exact (eventually_common_zero_imp_eq_zero_of_nonassociated (P i) (P j)
          (hP i) (hP j) (hp i ▸ hirr i) (hp j ▸ hirr j)
          (by simpa only [← hp] using hsep i j hij)).mono fun _ hz _ => hz
    exact Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hpair i)

end OnLeConjecture.Analytic.Germ
