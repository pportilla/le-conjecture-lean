/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingThreePathEquiv
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingWeights
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingPaths
public import OnLeConjecture.KnotFloer.GridLaurentMapBounds

/-! # Laurent coefficients of the three-rectangle matching paths -/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The admissible rectangles represented by a three-rectangle matching path. -/
def stabilizationMatchingThreeRectangles (x y : GridState n) :=
  (stabilizationAdmissibleRectangles G s x y).filter fun r =>
    (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior ∧ r.bottom ≠ (G.X s).castSucc

@[simp]
theorem mem_stabilizationMatchingThreeRectangles {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ)) :
    r ∈ stabilizationMatchingThreeRectangles G s x y ↔
      StabilizationAdmissibleRectangle G s r ∧
        (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior ∧ r.bottom ≠ (G.X s).castSucc := by
  classical
  rw [stabilizationMatchingThreeRectangles, Finset.mem_filter,
    mem_stabilizationAdmissibleRectangles]

/-- All actual entry-advance-exit paths. -/
def stabilizationMatchingThreePaths (x y : GridState n) :
    Finset (StabilizationMatchingThreePath G s x y) :=
  @Finset.univ _ (Fintype.ofFinite _)

@[simp]
theorem mem_stabilizationMatchingThreePaths {x y : GridState n}
    (p : StabilizationMatchingThreePath G s x y) : p ∈ stabilizationMatchingThreePaths G s x y :=
  @Finset.mem_univ _ (Fintype.ofFinite _) p

variable (R : Type*) [CommRing R]

/-- The product of the three full rectangle weights. -/
def stabilizationMatchingThreePathWeight {x y : GridState n}
    (p : StabilizationMatchingThreePath G s x y) : LaurentPolynomial R :=
  LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        p.2.2.1.val.toGridRectangle).card : ℤ) *
    LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        p.2.2.2.1.val.toGridRectangle).card : ℤ) *
    LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        p.2.2.2.2.val.toGridRectangle).card : ℤ)

/-- The reconstruction preserves the full Laurent weight. -/
theorem stabilizationMatchingThreePathWeight_eq {x y : GridState n}
    (p : StabilizationMatchingThreePath G s x y) :
    stabilizationMatchingThreePathWeight G s R p =
      stabilizationStandardWeight G s R (stabilizationMatchingThreePathRectangle G s p) := by
  obtain ⟨r, hr, hrect⟩ := exists_old_rectangle_of_matching_entry_advance_exit G s x y
    p.1 p.2.1.val p.2.1.property p.2.2.1.val p.2.2.1.property
    p.2.2.2.1.val p.2.2.2.1.property.1 p.2.2.2.1.property.2
    p.2.2.2.2.val p.2.2.2.2.property
  change _ = stabilizationStandardWeight G s R
    (stabilizationMatchingThreeCenterRectangle G s x y p.1 p.2.1.val p.2.1.property
      p.2.2.1.val p.2.2.1.property p.2.2.2.1.val p.2.2.2.1.property.2
      p.2.2.2.2.val p.2.2.2.2.property)
  rw [← hrect, stabilizationStandardWeight_insertPoint]
  exact stabilizationMatching_three_rectangle_weight G s R p.1 p.2.1.val r hr
    p.2.2.1.val p.2.2.1.property p.2.2.2.1.val p.2.2.2.1.property.1
    p.2.2.2.2.val p.2.2.2.2.property

set_option backward.isDefEq.respectTransparency false in
/-- Expanding the two linear maps gives the actual internal transition coefficients. -/
theorem stabilizationMatchingExit_transition_entry_single_apply_eq_sum_nodes
    (x y : GridState n) :
    letI := Classical.decEq (StabilizationMatchingNode G s)
    letI := Fintype.ofFinite (StabilizationMatchingNode G s)
    stabilizationMatchingExit G s R
        (stabilizationMatchingTransition G s R (stabilizationMatchingEntry G s R (single x 1))) y =
      ∑ a : StabilizationMatchingNode G s, ∑ b : StabilizationMatchingNode G s,
        laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R
            (x.insertPoint s.succ (G.X s).succ) (stabilizationMatchingTargetState G s a) *
          (if a = b then 0 else
            laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R
              a.val (stabilizationMatchingTargetState G s b)) *
          laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R
            b.val (y.insertPoint s.succ (G.X s).succ) := by
  classical
  let := Fintype.ofFinite (StabilizationMatchingNode G s)
  rw [laurentMap_apply_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  have ht (b : StabilizationMatchingNode G s) :
      stabilizationMatchingTransition G s R (stabilizationMatchingEntry G s R (single x 1)) b =
        ∑ a : StabilizationMatchingNode G s,
          stabilizationMatchingEntry G s R (single x 1) a *
            stabilizationMatchingTransition G s R (single a 1) b :=
    finiteEnd_apply_apply _ _ _
  simp_rw [ht, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [stabilizationMatchingEntry_single_apply,
    stabilizationMatchingTransition_single_apply, stabilizationMatchingExit_single_apply]

/-- The three-path bijection preserves the entire Laurent coefficient sum. -/
theorem sum_stabilizationMatchingThreePathWeight (x y : GridState n) :
    ∑ p ∈ stabilizationMatchingThreePaths G s x y, stabilizationMatchingThreePathWeight G s R p =
      ∑ r ∈ stabilizationMatchingThreeRectangles G s x y, stabilizationStandardWeight G s R r := by
  classical
  apply Finset.sum_nbij (stabilizationMatchingThreePathRectangle G s)
  · intro p _
    exact (mem_stabilizationMatchingThreeRectangles G s _).mpr
      (stabilizationMatchingThreePathRectangle_properties G s p)
  · intro p _ q _ h
    exact stabilizationMatchingThreePathRectangle_injective G s h
  · intro r hr
    change r ∈ stabilizationMatchingThreeRectangles G s x y at hr
    rw [mem_stabilizationMatchingThreeRectangles] at hr
    obtain ⟨p, hp⟩ := exists_matchingThreePath_of_bottom_ne G s r hr.1 hr.2.1 hr.2.2
    exact ⟨p, mem_stabilizationMatchingThreePaths G s p, hp⟩
  · intro p _
    exact stabilizationMatchingThreePathWeight_eq G s R p

private theorem mul_sum_mul_sum {A B : Type*} [Fintype A] [Fintype B]
    (c : LaurentPolynomial R) (f : A → LaurentPolynomial R) (g : B → LaurentPolynomial R) :
    c * (∑ a, f a) * (∑ b, g b) =
      ∑ p ∈ (Finset.univ : Finset A).product (Finset.univ : Finset B), c * f p.1 * g p.2 := by
  have h : c * (∑ a, f a) = ∑ a, c * f a := Finset.mul_sum _ _ _
  rw [h]
  exact (Finset.sum_mul_sum Finset.univ Finset.univ (fun a => c * f a) g).trans
    (Finset.sum_product Finset.univ Finset.univ (fun p => c * f p.1 * g p.2)).symm

private theorem coefficient_eq_advancing_sum {x : GridState n}
    (a b : StabilizationMatchingNode G s) (hab : a ≠ b)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : e.IsEmpty)
    [Fintype { m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b) //
      m.IsEmpty ∧ m.top = (G.X s).castSucc }] :
    laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R
        a.val (stabilizationMatchingTargetState G s b) =
      ∑ m : { m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b) //
          m.IsEmpty ∧ m.top = (G.X s).castSucc },
        LaurentPolynomial.T
          (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            m.val.toGridRectangle).card : ℤ) := by
  classical
  rw [laurentCoefficient_eq]
  apply Finset.sum_subtype
  intro m
  rw [GridRectangleBetween.mem_emptyRectangles]
  exact ⟨fun hm => ⟨hm, stabilizationMatchingEntry_advancing G s x a b hab e m he hm⟩,
    fun hm => hm.1⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual composition counts all three-rectangle matching paths once. -/
theorem stabilizationMatchingExit_transition_entry_single_apply_eq_sum_paths
    (x y : GridState n) :
    stabilizationMatchingExit G s R
        (stabilizationMatchingTransition G s R (stabilizationMatchingEntry G s R (single x 1))) y =
      ∑ p ∈ stabilizationMatchingThreePaths G s x y,
        stabilizationMatchingThreePathWeight G s R p := by
  classical
  let := Fintype.ofFinite (StabilizationMatchingNode G s)
  let B (a : StabilizationMatchingNode G s) := { b : StabilizationMatchingNode G s // a ≠ b }
  let E (a : StabilizationMatchingNode G s) :=
    { e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
        (stabilizationMatchingTargetState G s a) // e.IsEmpty }
  let M (a b : StabilizationMatchingNode G s) :=
    { m : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b) //
      m.IsEmpty ∧ m.top = (G.X s).castSucc }
  let F (b : StabilizationMatchingNode G s) :=
    { f : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ) // f.IsEmpty }
  let (a : StabilizationMatchingNode G s) :
      Fintype { b : StabilizationMatchingNode G s // a ≠ b } :=
    Fintype.ofFinite _
  let (a : StabilizationMatchingNode G s) : Fintype (E a) := Fintype.ofFinite _
  let (a b : StabilizationMatchingNode G s) : Fintype (M a b) := Fintype.ofFinite _
  let (b : StabilizationMatchingNode G s) : Fintype (F b) := Fintype.ofFinite _
  have huniv : stabilizationMatchingThreePaths G s x y =
      Finset.univ.sigma (fun a : StabilizationMatchingNode G s =>
        Finset.univ.sigma (fun b : B a =>
          (Finset.univ : Finset (E a)).product
            ((Finset.univ : Finset (M a b.val)).product (Finset.univ : Finset (F b.val))))) := by
    ext p
    constructor
    · intro _
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
        Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩⟩⟩
    · intro _
      exact mem_stabilizationMatchingThreePaths G s p
  let C := fun a b : GridState (n + 1) =>
    laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R a b
  let ce (a : StabilizationMatchingNode G s) :=
    C (x.insertPoint s.succ (G.X s).succ) (stabilizationMatchingTargetState G s a)
  let cm (a b : StabilizationMatchingNode G s) := C a.val (stabilizationMatchingTargetState G s b)
  let cf (b : StabilizationMatchingNode G s) := C b.val (y.insertPoint s.succ (G.X s).succ)
  have hdiag (a : StabilizationMatchingNode G s) :
      (∑ b : StabilizationMatchingNode G s, ce a * (if a = b then 0 else cm a b) * cf b) =
        ∑ b : B a, ce a * cm a b.val * cf b.val := by
    have hsub := Finset.sum_subtype (p := fun b => a ≠ b)
      (F := Fintype.ofFinite _) (Finset.univ.filter fun b => a ≠ b)
      (fun b => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun b => ce a * cm a b * cf b)
    rw [← hsub, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : a = b <;> simp [h]
  rw [stabilizationMatchingExit_transition_entry_single_apply_eq_sum_nodes, huniv, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b, ce a * (if a = b then 0 else cm a b) * cf b) = _
  rw [hdiag, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  have heq : ce a = ∑ e : E a, LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns e.val.toGridRectangle).card : ℤ) := by
    rw [show ce a = laurentCoefficient _ R _ _ from rfl, laurentCoefficient_eq]
    exact Finset.sum_subtype _ (fun e => GridRectangleBetween.mem_emptyRectangles e) _
  rw [heq, Finset.sum_mul, Finset.sum_mul]
  refine Eq.trans ?_ (Finset.sum_product (Finset.univ : Finset (E a))
    ((Finset.univ : Finset (M a b.val)).product (Finset.univ : Finset (F b.val)))
    (fun p => stabilizationMatchingThreePathWeight G s R ⟨a, b, p⟩)).symm
  apply Finset.sum_congr rfl
  intro e _
  have hmeq := coefficient_eq_advancing_sum G s R a b.val b.property e.val e.property
  have hfeq : cf b.val = ∑ f : F b.val, LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns f.val.toGridRectangle).card : ℤ) := by
    rw [show cf b.val = laurentCoefficient _ R _ _ from rfl, laurentCoefficient_eq]
    exact Finset.sum_subtype _ (fun f => GridRectangleBetween.mem_emptyRectangles f) _
  change _ * cm a b.val * cf b.val = _
  rw [show cm a b.val = laurentCoefficient _ R _ _ from rfl, hmeq, hfeq]
  exact mul_sum_mul_sum R
    (LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns e.val.toGridRectangle).card : ℤ))
    (fun m : M a b.val => LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns m.val.toGridRectangle).card : ℤ))
    (fun f : F b.val => LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns f.val.toGridRectangle).card : ℤ))

/-- The three-rectangle term is the remaining nonempty portion of the old coefficient. -/
theorem stabilizationMatchingExit_transition_entry_single_apply_eq_sum (x y : GridState n) :
    stabilizationMatchingExit G s R
        (stabilizationMatchingTransition G s R (stabilizationMatchingEntry G s R (single x 1))) y =
      ∑ r ∈ stabilizationMatchingThreeRectangles G s x y,
        stabilizationStandardWeight G s R r := by
  rw [stabilizationMatchingExit_transition_entry_single_apply_eq_sum_paths,
    sum_stabilizationMatchingThreePathWeight]

end OnLeConjecture.KnotFloer.GridFull
