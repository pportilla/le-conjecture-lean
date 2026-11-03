/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TransverseSectionOrder
public import OnLeConjecture.Analytic.CoordinatePermutation

/-!
# Target coordinates for a transverse section

A selected transverse target component is moved to the first coordinate
by an explicit linear permutation. The common-minor factor and a unit
residual persist under that permutation, so the section order construction
does not require a preassigned transverse target coordinate.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Every component of the explicit target coordinate swap. -/
theorem coordinateSwap_comp_component {l n : ℕ}
    (i : Fin (n + 1)) (g : PointedMapGerm l (n + 1)) (j : Fin (n + 1)) :
    ((coordinateSwapPointedEquiv i).forward.comp g).1.component j =
      g.1.component (Equiv.swap 0 i j) := by
  have hswap : (coordinateSwapPointedEquiv i).forward.1.component j =
      coordinate (Equiv.swap 0 i j) := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    apply Filter.Eventually.of_forall
    intro z
    change coordinateSwapEquiv i z j = z (Equiv.swap 0 i j)
    have h := Equiv.piCongrLeft_apply_apply
      (fun _ : Fin (n + 1) => ℂ) (Equiv.swap 0 i) z (Equiv.swap 0 i j)
    change (Equiv.piCongrLeft (fun _ : Fin (n + 1) => ℂ) (Equiv.swap 0 i)) z j = _
    simpa using h
  rw [PointedMapGerm.component_comp_general, hswap, PointedMapGerm.pullback_coordinate]

namespace Germ

/-- A unit residual of any ordered minor is, up to sign, a unit residual
of one of the three increasing-index minors. -/
theorem unit_residual_of_some_minor_implies_three
    (F : Fin 3 → Germ 2) (p : Germ 2) (hp : p ≠ 0) (k : ℕ)
    (R : Fin 3 → Fin 3 → Germ 2)
    (hR : ∀ i j, jacobian (F i) (F j) = p ^ k * R i j)
    (hunit : ∃ i j, IsUnit (R i j)) :
    IsUnit (R 0 1) ∨ IsUnit (R 0 2) ∨ IsUnit (R 1 2) := by
  have hpow : p ^ k ≠ 0 := pow_ne_zero k hp
  have hdiag (i : Fin 3) : R i i = 0 := by
    apply mul_left_cancel₀ hpow
    rw [← hR, jacobian_self, mul_zero]
  have hswap (i j : Fin 3) : R i j = -R j i := by
    apply mul_left_cancel₀ hpow
    rw [← hR, mul_neg, ← hR]
    exact jacobian_swap _ _
  obtain ⟨i, j, hij⟩ := hunit
  fin_cases i <;> fin_cases j
  · exact (not_isUnit_zero ((hdiag 0) ▸ hij)).elim
  · exact Or.inl hij
  · exact Or.inr (Or.inl hij)
  · exact Or.inl ((IsUnit.neg_iff _).mp ((hswap 1 0) ▸ hij))
  · exact (not_isUnit_zero ((hdiag 1) ▸ hij)).elim
  · exact Or.inr (Or.inr hij)
  · exact Or.inr (Or.inl ((IsUnit.neg_iff _).mp ((hswap 2 0) ▸ hij)))
  · exact Or.inr (Or.inr ((IsUnit.neg_iff _).mp ((hswap 2 1) ▸ hij)))
  · exact (not_isUnit_zero ((hdiag 2) ▸ hij)).elim

end Germ

namespace PointedMapGerm

/-- Any transverse target component yields a constructed locally
injective section whose parameter order is the common-minor exponent
plus one. The target change is an explicit coordinate swap. -/
theorem exists_transverse_section_order_at_component
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (p : Germ 2) (hp : p ∈ maximalIdeal 2) (hpne : p ≠ 0)
    (k : ℕ) (R : Fin 3 → Fin 3 → Germ 2)
    (hR : ∀ i j, jacobian (g.1.component i) (g.1.component j) = p ^ k * R i j)
    (hunit : ∃ i j, IsUnit (R i j))
    (i : Fin 3) (hip : IsUnit (jacobian (g.1.component i) p)) :
    ∃ (e : PointedEquivGerm 2) (β : PointedMapGerm 1 2),
      e.forward.pullbackRingHom (g.1.component i) = coordinate 0 ∧
      e.forward.pullbackRingHom p = coordinate 1 ∧
      (hyperplaneInclusionGerm 2).comp β =
        ((coordinateSwapPointedEquiv i).forward.comp g).comp
          (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
      β.HasInjectiveRepresentative ∧
      min (vanishingOrder (β.1.component 0)) (vanishingOrder (β.1.component 1)) =
        (k + 1 : ℕ) := by
  let τ := coordinateSwapPointedEquiv i
  let g' := τ.forward.comp g
  let R' (a b : Fin 3) := R (Equiv.swap 0 i a) (Equiv.swap 0 i b)
  have hg' : g'.HasInjectiveRepresentative :=
    τ.forward.comp_hasInjectiveRepresentative g τ.forward_hasInjectiveRepresentative hi
  have hR' (a b : Fin 3) : jacobian (g'.1.component a) (g'.1.component b) = p ^ k * R' a b := by
    simpa only [g', τ, R', coordinateSwap_comp_component] using
      hR (Equiv.swap 0 i a) (Equiv.swap 0 i b)
  have hunit' : ∃ a b, IsUnit (R' a b) := by
    obtain ⟨a, b, hab⟩ := hunit
    exact ⟨Equiv.swap 0 i a, Equiv.swap 0 i b, by simpa only [R', Equiv.swap_apply_self] using hab⟩
  have hthree := unit_residual_of_some_minor_implies_three g'.1.component p hpne k R' hR' hunit'
  have hzero : g'.1.component 0 = g.1.component i := coordinateSwap_comp_component_zero i g
  obtain ⟨e, β, he, hep, hfactor, hβ, horder⟩ :=
    g'.exists_injective_transverse_section_with_order hg' p (R' 0 1) (R' 0 2) (R' 1 2) k hp
      (hzero ▸ hip) (hR' 0 1) (hR' 0 2) (hR' 1 2) hthree
  exact ⟨e, β, hzero ▸ he, hep, hfactor, hβ, horder⟩

end PointedMapGerm

end OnLeConjecture.Analytic
