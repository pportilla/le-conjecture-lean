/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Polynomial.GenericLinearCombination

/-!
# Companion combinations without additional common zeros

For each of finitely many nonzero polynomials, a companion combination
can avoid all its roots except the common zeros of the generator family.
The same coefficient row works for every family throughout a nonempty
open subset of any prescribed nonempty open coefficient set.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

theorem exists_open_companion_common_zeros
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (P : κ → ℂ[X]) (hP : ∀ k, P k ≠ 0) (F : κ → ι → ℂ[X])
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V, ∀ k z, (P k).eval z = 0 →
        (polynomialLinearCombination (F k) q).eval z = 0 →
          ∀ i, (F k i).eval z = 0 := by
  classical
  let := Fintype.ofFinite κ
  let roots (k : κ) : Finset ℂ := (P k).roots.toFinset.filter
    (fun z => ∃ i, (F k i).eval z ≠ 0)
  let Roots := Σ k : κ, roots k
  let ell : Roots → (ι → ℂ) →ₗ[ℂ] ℂ := fun r =>
    (aeval (r.2.val : ℂ)).toLinearMap.comp (polynomialLinearCombination (F r.1))
  have hell (r : Roots) : ell r ≠ 0 := by
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp r.2.property).2
    intro hz
    have h := LinearMap.congr_fun hz (Pi.single i 1)
    change aeval r.2.val (polynomialLinearCombination (F r.1) (Pi.single i 1)) = 0 at h
    rw [polynomialLinearCombination_single] at h
    exact hi (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using h)
  let V : Set (ι → ℂ) := U ∩ {q | ∀ r, ell r q ≠ 0}
  have hVopen : IsOpen V := by
    apply hU.inter
    have hset : {q : ι → ℂ | ∀ r, ell r q ≠ 0} = ⋂ r, {q | ell r q ≠ 0} := by
      ext q
      simp
    rw [hset]
    apply isOpen_iInter_of_finite
    intro r
    exact isOpen_ne.preimage ((ell r).continuous_of_finiteDimensional)
  have hVne : V.Nonempty := by
    obtain ⟨q, hqU, hq⟩ := Analytic.exists_coefficients_avoiding_submodules_mem_open
      (fun r => LinearMap.ker (ell r))
      (fun r h => hell r (LinearMap.ker_eq_top.mp h)) U hU hUne
    exact ⟨q, hqU, hq⟩
  refine ⟨V, hVopen, hVne, fun _ h => h.1, ?_⟩
  intro q hq k z hzP hzQ
  by_contra hnot
  push Not at hnot
  let r : Roots := ⟨k, z, Finset.mem_filter.mpr
    ⟨Multiset.mem_toFinset.mpr ((mem_roots (hP k)).mpr hzP), hnot⟩⟩
  apply hq.2 r
  change aeval z (polynomialLinearCombination (F k) q) = 0
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hzQ

end OnLeConjecture.Polynomial
