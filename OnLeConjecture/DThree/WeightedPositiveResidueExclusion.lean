/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.PositiveResiduePointedMap
public import OnLeConjecture.DThree.WeightedClassifiedRescaling

/-!
# Exclusion after weighted classification

The analytic classification carries the cubic and quartic initial forms to
the E or H pair. If the weighted degree of the third initial form has positive
residue, the corresponding pointed map collision excludes injectivity.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Rescaling the first source coordinate by a nonzero scalar preserves
nonvanishing of a form. -/
theorem rescaleForm_ne_zero_of_ne_zero
    {R : Form ℂ} (s u : ℂ) (hs : s ≠ 0) (hu : u ≠ 0)
    (hR : R ≠ 0) :
    rescaleForm s u R ≠ 0 := by
  intro hzero
  have hproduct :
      MvPolynomial.C u *
          diagonalPolynomialSubstitution (sourceRescaleVector s) R = 0 := by
    simpa [rescaleForm, diagonalPolynomialSubstitution_sourceRescale] using
      hzero
  have hconstant : (MvPolynomial.C u : Form ℂ) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr hu
  have hsubstitution :
      diagonalPolynomialSubstitution (sourceRescaleVector s) R = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left hconstant
  exact hR <| diagonalPolynomialSubstitution_injective
    (sourceRescaleVector s) (sourceRescaleVector_ne_zero hs) hsubstitution

/-- Classified weighted cubic and quartic initial forms and a third form of
positive residue exclude an injective representative. -/
theorem
    classifiedWeightedThreeForms_positiveResidue_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a) (R : Form ℂ)
    (hR : R.IsWeightedHomogeneous ![a, 1] D) (hRzero : R ≠ 0)
    (hresidue : 0 < D % a)
    (A B c₄ c₃ c₂ c₁ c₀ : ℂ)
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hquartic : weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨s, h, hs, _hequivalent, hinjective, hRscaled,
      hE | hH⟩ :=
    exists_rightLeft_weightedRescaling_to_E_or_H_of_analytic_initialForms
      g a D ha R hR A B c₄ c₃ c₂ c₁ c₀ hAB hquartic
        htailZero htailOne htailTwo hdiv
  · have hRscaledZero : rescaleForm s 1 R ≠ 0 :=
      rescaleForm_ne_zero_of_ne_zero s 1 hs one_ne_zero hRzero
    rcases hE with ⟨hzeroTail, honeTail, htwoTail⟩
    intro hg
    exact ePositiveResiduePointedMap_not_hasInjectiveRepresentative
      h a D ha (rescaleForm s 1 R) hRscaled hRscaledZero hresidue
        hzeroTail honeTail htwoTail (hinjective.mpr hg)
  · have hRscaledZero : rescaleForm s 1 R ≠ 0 :=
      rescaleForm_ne_zero_of_ne_zero s 1 hs one_ne_zero hRzero
    rcases hH with ⟨hzeroTail, honeTail, htwoTail⟩
    intro hg
    exact hPositiveResiduePointedMap_not_hasInjectiveRepresentative
      h a D ha (rescaleForm s 1 R) hRscaled hRscaledZero hresidue
        hzeroTail honeTail htwoTail (hinjective.mpr hg)

end OnLeConjecture.DThree
