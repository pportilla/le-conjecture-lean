/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentXMarkingHomotopy
public import OnLeConjecture.KnotFloer.GridFullLaurentPerturbation

/-!
# Blocking selected X markings in the full Laurent complex

Setting the weights of selected X squares to zero preserves square zero after all O
variables have been identified. The omitted rectangle terms form a perturbation that
strictly lowers the Alexander coordinate. Thus the invertibility condition of the
basic perturbation lemma follows for every degree-one filtered contracting homotopy.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- The usual O weight, with the selected X squares assigned weight zero. -/
noncomputable def xBlockedSquareWeight (S : Finset (Fin n)) (p : Fin n × Fin n) :
    LaurentPolynomial R :=
  oSquareWeight G p * if p.1 ∈ S ∧ p.2 = G.X p.1 then 0 else 1

theorem xBlockedSquareWeight_column (S : Finset (Fin n)) (c : Fin n) :
    ∏ r : Fin n, xBlockedSquareWeight G R S (c, r) =
      if c ∈ S then 0 else LaurentPolynomial.T 1 := by
  classical
  simp only [xBlockedSquareWeight, Finset.prod_mul_distrib, oSquareWeight_column]
  by_cases hc : c ∈ S <;> simp [hc]

theorem xBlockedSquareWeight_row (S : Finset (Fin n)) (r : Fin n) :
    ∏ c : Fin n, xBlockedSquareWeight G R S (c, r) =
      if G.X.toPerm.symm r ∈ S then 0 else LaurentPolynomial.T 1 := by
  classical
  have heq (c : Fin n) : r = G.X c ↔ c = G.X.toPerm.symm r :=
    eq_comm.trans G.X.toPerm.eq_symm_apply.symm
  simp only [xBlockedSquareWeight, Finset.prod_mul_distrib, oSquareWeight_row]
  simp_rw [heq]
  have hf (c : Fin n) :
      (if c ∈ S ∧ c = G.X.toPerm.symm r then (0 : LaurentPolynomial R) else 1) =
        if c = G.X.toPerm.symm r then (if G.X.toPerm.symm r ∈ S then 0 else 1) else 1 := by
    by_cases hc : c = G.X.toPerm.symm r <;> simp [hc]
  simp_rw [hf]
  simp

/-- Each removed X contributes once to the row annuli and once to the column annuli. -/
theorem xBlockedSquareWeight_curvature [CharP R 2] (S : Finset (Fin n)) :
    squareWeightCurvature (xBlockedSquareWeight G R S) = 0 := by
  classical
  rw [squareWeightCurvature]
  simp_rw [xBlockedSquareWeight_column, xBlockedSquareWeight_row]
  rw [Equiv.sum_comp G.X.toPerm.symm
    (fun c => if c ∈ S then (0 : LaurentPolynomial R) else LaurentPolynomial.T 1)]
  exact CharTwo.add_self_eq_zero _

/-- The differential counting empty rectangles avoiding the selected X markings. -/
noncomputable def laurentXBlockedDifferential (S : Finset (Fin n)) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  squareWeightedDifferential (xBlockedSquareWeight G R S)

/-- Blocking any collection of X markings gives a genuine differential. -/
theorem laurentXBlockedDifferential_comp_self [CharP R 2] (S : Finset (Fin n)) :
    laurentXBlockedDifferential G R S ∘ₗ laurentXBlockedDifferential G R S = 0 := by
  rw [laurentXBlockedDifferential, squareWeightedDifferential_comp_self,
    xBlockedSquareWeight_curvature, zero_smul]

/-- A rectangle survives exactly when it avoids all selected X squares. -/
theorem squareWeight_xBlockedSquareWeight (S : Finset (Fin n)) (r : GridRectangle n) :
    squareWeight (xBlockedSquareWeight G R S) r =
      if ∃ a ∈ S, (a, G.X a) ∈ r.coveredSquares then 0
        else LaurentPolynomial.T ((G.OColumns r).card : ℤ) := by
  classical
  rw [squareWeight]
  simp only [xBlockedSquareWeight, Finset.prod_mul_distrib]
  change squareWeight (oSquareWeight G) r * _ = _
  rw [squareWeight_oSquareWeight, laurentSpecialization_OMonomial]
  split_ifs with h
  · obtain ⟨a, ha, hr⟩ := h
    have hz : ∏ p ∈ r.coveredSquares,
        (if p.1 ∈ S ∧ p.2 = G.X p.1 then (0 : LaurentPolynomial R) else 1) = 0 :=
      Finset.prod_eq_zero hr (by simp [ha])
    rw [hz, mul_zero]
  · have hprod : ∏ p ∈ r.coveredSquares,
        (if p.1 ∈ S ∧ p.2 = G.X p.1 then (0 : LaurentPolynomial R) else 1) = 1 := by
      apply Finset.prod_eq_one
      rintro ⟨a, b⟩ hp
      rw [if_neg]
      intro hab
      change a ∈ S ∧ b = G.X a at hab
      obtain ⟨ha, rfl⟩ := hab
      exact h ⟨a, ha, hp⟩
    rw [hprod, mul_one]

open Classical in
/-- The coefficient formula uses the selected-X avoidance condition only. -/
theorem laurentXBlockedDifferential_apply_apply (S : Finset (Fin n))
    (c : LaurentChain R n) (y : GridState n) :
    laurentXBlockedDifferential G R S c y = c.sum fun x p => p *
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter
        (fun r => ¬∃ a ∈ S, (a, G.X a) ∈ r.toGridRectangle.coveredSquares),
          LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  simp only [laurentXBlockedDifferential, squareWeightedDifferential_apply_apply,
    squareWeightedCoefficient, squareWeight_xBlockedSquareWeight, Finset.sum_filter,
    ite_not]

variable (K : Type*) [CommRing K]

/-- The terms removed by blocking the selected X markings. -/
noncomputable def laurentXCrossingDifferential (S : Finset (Fin n)) :
    LaurentChain K n →ₗ[LaurentPolynomial K] LaurentChain K n :=
  laurentDifferential G K - laurentXBlockedDifferential G K S

open Classical in
/-- The perturbation counts precisely the empty rectangles crossing a selected X marking. -/
theorem laurentXCrossingDifferential_apply_apply (S : Finset (Fin n))
    (c : LaurentChain K n) (y : GridState n) :
    laurentXCrossingDifferential G K S c y = c.sum fun x p => p *
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter
        (fun r => ∃ a ∈ S, (a, G.X a) ∈ r.toGridRectangle.coveredSquares),
          LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  simp only [laurentXCrossingDifferential, LinearMap.sub_apply, Finsupp.sub_apply,
    laurentDifferential_apply_apply, laurentCoefficient_eq,
    laurentXBlockedDifferential_apply_apply, Finsupp.sum, ← Finset.sum_sub_distrib,
    ← mul_sub, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> simp

/-- Adding the omitted rectangle terms recovers the full differential. -/
theorem laurentXBlocked_add_crossing (S : Finset (Fin n)) :
    laurentXBlockedDifferential G K S + laurentXCrossingDifferential G K S =
      laurentDifferential G K := by
  unfold laurentXCrossingDifferential
  abel

/-- The selected-X crossing operator is a perturbation in the precise sense of the BPL. -/
theorem laurentXCrossing_perturbation [CharP K 2] (S : Finset (Fin n)) :
    (laurentXBlockedDifferential G K S + laurentXCrossingDifferential G K S) ∘ₗ
        (laurentXBlockedDifferential G K S + laurentXCrossingDifferential G K S) =
      laurentXBlockedDifferential G K S ∘ₗ laurentXBlockedDifferential G K S := by
  rw [laurentXBlocked_add_crossing, laurentDifferential_comp_self_eq_zero,
    laurentXBlockedDifferential_comp_self]

/-- Every surviving perturbation coefficient comes from a selected-X crossing rectangle. -/
theorem exists_rectangle_of_mem_support_laurentXCrossingDifferential
    (S : Finset (Fin n)) (c : LaurentChain K n) {y : GridState n} {k : ℤ}
    (hk : k ∈ (laurentXCrossingDifferential G K S c y).coeff.support) :
    ∃ x : GridState n, ∃ j ∈ (c x).coeff.support, ∃ r : GridRectangleBetween x y,
      r.IsEmpty ∧ (∃ a ∈ S, (a, G.X a) ∈ r.toGridRectangle.coveredSquares) ∧
        k = j + ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [laurentXCrossingDifferential_apply_apply, Finsupp.sum,
    AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨j, hj, d, hd, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hx)
  rw [AddMonoidAlgebra.coeff_sum] at hd
  obtain ⟨r, hr, hd⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hd)
  obtain ⟨hre, hrX⟩ := Finset.mem_filter.mp hr
  change d ∈ (Finsupp.single ((G.OColumns r.toGridRectangle).card : ℤ) (1 : K)).support at hd
  have hd' := Finset.mem_singleton.mp (Finsupp.support_single_subset hd)
  exact ⟨x, j, hj, r, (GridRectangleBetween.mem_emptyRectangles r).mp hre, hrX,
    congrArg (fun d => j + d) hd'⟩

/-- The concrete perturbation lowers Maslov degree by one. -/
theorem laurentXCrossingDifferential_mem_maslovPiece (S : Finset (Fin n))
    {m : ℤ} {c : LaurentChain K n} (hc : c ∈ laurentMaslovPiece G K m) :
    laurentXCrossingDifferential G K S c ∈ laurentMaslovPiece G K (m - 1) := by
  intro y k hk
  obtain ⟨x, j, hj, r, hre, _, rfl⟩ :=
    exists_rectangle_of_mem_support_laurentXCrossingDifferential G K S c hk
  rw [laurentMaslovDegree_add_card_OColumns G r hre]
  exact congrArg (fun m : ℤ => m - 1) (hc x j hj)

/-- Crossing a selected X lowers the Alexander coordinate by at least one. -/
theorem laurentXCrossingDifferential_mem_bifiltrationLevel (S : Finset (Fin n))
    {u v : ℝ} {c : LaurentChain K n} (hc : c ∈ laurentBifiltrationLevel G K u v) :
    laurentXCrossingDifferential G K S c ∈ laurentBifiltrationLevel G K u (v - 1) := by
  intro y k hk
  obtain ⟨x, j, hj, r, _, ⟨a, _, hrX⟩, rfl⟩ :=
    exists_rectangle_of_mem_support_laurentXCrossingDifferential G K S c hk
  have hb := hc x j hj
  constructor
  · exact (laurentRectangle_coordinates_le G r j).1.trans hb.1
  · have h := G.alexander_sub_alexander_eq_card_sub_card r
    rw [← G.card_OColumns r.toGridRectangle] at h
    have hreal : (G.alexander x : ℝ) - (G.alexander y : ℝ) =
        ((G.XSet ∩ r.toGridRectangle.coveredSquares).card : ℝ) -
          (G.OColumns r.toGridRectangle).card := by exact_mod_cast h
    have hx : (1 : ℝ) ≤ ((G.XSet ∩ r.toGridRectangle.coveredSquares).card : ℝ) :=
      by exact_mod_cast one_le_card_X_of_mem G a r hrX
    push_cast
    linarith [hb.2]

/-- The HPL inverse exists for the concrete selected-X perturbation and a filtered homotopy. -/
theorem isUnit_one_add_laurentXCrossing_comp_homotopy (S : Finset (Fin n))
    (h : LaurentChain K n →ₗ[LaurentPolynomial K] LaurentChain K n)
    (hhdegree : ∀ (m : ℤ) (c : LaurentChain K n), c ∈ laurentMaslovPiece G K m →
      h c ∈ laurentMaslovPiece G K (m + 1))
    (hhfiltration : ∀ (u v : ℝ) (c : LaurentChain K n),
      c ∈ laurentBifiltrationLevel G K u v → h c ∈ laurentBifiltrationLevel G K u v) :
    IsUnit (1 + laurentXCrossingDifferential G K S * h) :=
  isUnit_one_add_laurent_perturbation_comp_homotopy G K _ h
    (fun _ _ hc => laurentXCrossingDifferential_mem_maslovPiece G K S hc)
    hhdegree (fun _ _ _ hc => laurentXCrossingDifferential_mem_bifiltrationLevel G K S hc)
    hhfiltration

/-- Blocking a singleton removes exactly the single X-square derivative. -/
theorem laurentXCrossingDifferential_singleton (a : Fin n) :
    laurentXCrossingDifferential G K {a} = laurentXMarkingHomotopy G K a := by
  classical
  ext c y
  simp [laurentXCrossingDifferential_apply_apply, laurentXMarkingHomotopy_apply_apply]

end OnLeConjecture.KnotFloer.GridFull
