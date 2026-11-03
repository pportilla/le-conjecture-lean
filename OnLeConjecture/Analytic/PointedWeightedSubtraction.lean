/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightPairElimination
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction

/-!
# Pointedness of weighted target corrections

An initial polynomial outside a pair algebra has positive degree for
positive source weights. A correction producing a positive-order
remainder vanishes at the origin, so the target subtraction is pointed.
-/

public section

namespace OnLeConjecture.Analytic

theorem twoWeight_degree_pos_of_not_mem_pair_algebra
    (a b d : ℕ) (ha : 0 < a) (hb : 0 < b)
    (P : MvPolynomial (Fin 2) ℂ) (hP : P.IsWeightedHomogeneous ![a, b] d)
    (Q : Fin 2 → MvPolynomial (Fin 2) ℂ)
    (houtside : P ∉ Set.range (MvPolynomial.aeval Q :
      MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ)) : 0 < d := by
  by_contra h
  have hd : d = 0 := by omega
  subst d
  have hw : ∀ i : Fin 2, (![a, b] : Fin 2 → ℕ) i ≠ 0 := by
    intro i
    fin_cases i
    · exact ha.ne'
    · exact hb.ne'
  have hconstant : P = MvPolynomial.C (P.coeff 0) := by
    calc
      P = MvPolynomial.weightedHomogeneousComponent ![a, b] 0 P :=
        (MvPolynomial.weightedHomogeneousComponent_eq_self hP).symm
      _ = MvPolynomial.C (P.coeff 0) := MvPolynomial.weightedHomogeneousComponent_zero P hw
  apply houtside
  refine ⟨MvPolynomial.C (P.coeff 0), ?_⟩
  rw [MvPolynomial.aeval_C]
  exact hconstant.symm

namespace Germ

theorem target_correction_mem_maximalIdeal_of_twoWeight_tail
    (f : PointedMapGerm 2 2) (H Φ : Germ 2) (hH : H ∈ maximalIdeal 2)
    (a b d : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (P : MvPolynomial (Fin 2) ℂ) (hP : P.IsWeightedHomogeneous ![a, b] d)
    (htail : H - f.pullbackRingHom Φ - coordinatePolynomialAlgHom 2 P ∈
      twoWeightOrderIdeal a b (d + 1)) : Φ ∈ maximalIdeal 2 := by
  have hpoly := coordinatePolynomial_mem_twoWeightOrderIdeal a b d ha hb hP
  have htail' := twoWeightOrderIdeal_antitone a b d (d + 1) ha hb (by omega) htail
  have hrem : H - f.pullbackRingHom Φ ∈ twoWeightOrderIdeal a b d := by
    simpa only [sub_add_cancel] using (twoWeightOrderIdeal a b d).add_mem htail' hpoly
  have hrem' := twoWeightOrderIdeal_antitone a b 1 d ha hb hd hrem
  rw [twoWeightOrderIdeal_one_eq_maximalIdeal a b ha hb, mem_maximalIdeal_iff,
    map_sub, PointedMapGerm.valueRingHom_pullback, mem_maximalIdeal_iff.mp hH,
    zero_sub, neg_eq_zero] at hrem'
  exact mem_maximalIdeal_iff.mpr hrem'

end Germ

end OnLeConjecture.Analytic
