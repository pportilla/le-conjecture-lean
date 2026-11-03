/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingTwoPath
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingWeights
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingPaths
public import OnLeConjecture.KnotFloer.GridLaurentMapBounds

/-!
# The coefficient contributed by an entry-exit path

The composition of the actual entry and exit maps counts each admissible lifted
rectangle with lower matching-row bottom once, with its old Laurent weight.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The admissible rectangles represented by a two-rectangle matching path. -/
def stabilizationMatchingTwoRectangles (x y : GridState n) :=
  (stabilizationAdmissibleRectangles G s x y).filter fun r =>
    (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior ∧ r.bottom = (G.X s).castSucc

@[simp]
theorem mem_stabilizationMatchingTwoRectangles {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ)) :
    r ∈ stabilizationMatchingTwoRectangles G s x y ↔
      StabilizationAdmissibleRectangle G s r ∧
        (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior ∧ r.bottom = (G.X s).castSucc := by
  classical
  rw [stabilizationMatchingTwoRectangles, Finset.mem_filter,
    mem_stabilizationAdmissibleRectangles]

/-- All actual entry-exit paths, including their empty-rectangle witnesses. -/
def stabilizationMatchingTwoPaths (x y : GridState n) :
    Finset (StabilizationMatchingTwoPath G s x y) :=
  @Finset.univ _ (Fintype.ofFinite _)

@[simp]
theorem mem_stabilizationMatchingTwoPaths {x y : GridState n}
    (p : StabilizationMatchingTwoPath G s x y) : p ∈ stabilizationMatchingTwoPaths G s x y :=
  @Finset.mem_univ _ (Fintype.ofFinite _) p

variable (R : Type*) [CommRing R]

/-- The Laurent monomial contributed by the two empty rectangles of a path. -/
def stabilizationMatchingTwoPathWeight {x y : GridState n}
    (p : StabilizationMatchingTwoPath G s x y) : LaurentPolynomial R :=
  LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        p.2.1.val.toGridRectangle).card : ℤ) *
    LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        p.2.2.val.toGridRectangle).card : ℤ)

/-- The reconstructed rectangle carries exactly the product of the two path weights. -/
theorem stabilizationMatchingTwoPathWeight_eq {x y : GridState n}
    (p : StabilizationMatchingTwoPath G s x y) :
    stabilizationMatchingTwoPathWeight G s R p =
      stabilizationStandardWeight G s R (stabilizationMatchingTwoPathRectangle G s p) := by
  obtain ⟨r, hr, hrect⟩ := exists_old_rectangle_of_matching_entry_exit G s x y
    p.1 p.2.1.val p.2.1.property p.2.2.val p.2.2.property
  change _ = stabilizationStandardWeight G s R
    (stabilizationMatchingTwoCenterRectangle G s x y p.1 p.2.1.val p.2.1.property
      p.2.2.val p.2.2.property)
  rw [← hrect, stabilizationStandardWeight_insertPoint]
  exact stabilizationMatching_two_rectangle_weight G s R p.1 r hr
    p.2.1.val p.2.1.property p.2.2.val p.2.2.property

/-- The path bijection preserves the entire Laurent coefficient sum. -/
theorem sum_stabilizationMatchingTwoPathWeight (x y : GridState n) :
    ∑ p ∈ stabilizationMatchingTwoPaths G s x y, stabilizationMatchingTwoPathWeight G s R p =
      ∑ r ∈ stabilizationMatchingTwoRectangles G s x y, stabilizationStandardWeight G s R r := by
  classical
  apply Finset.sum_nbij (stabilizationMatchingTwoPathRectangle G s)
  · intro p _
    exact (mem_stabilizationMatchingTwoRectangles G s _).mpr
      (stabilizationMatchingTwoPathRectangle_properties G s p)
  · intro p _ q _ h
    exact stabilizationMatchingTwoPathRectangle_injective G s h
  · intro r hr
    change r ∈ stabilizationMatchingTwoRectangles G s x y at hr
    rw [mem_stabilizationMatchingTwoRectangles] at hr
    obtain ⟨p, hp⟩ := exists_matchingTwoPath_of_bottom G s r hr.1 hr.2.1 hr.2.2
    exact ⟨p, mem_stabilizationMatchingTwoPaths G s p, hp⟩
  · intro p _
    exact stabilizationMatchingTwoPathWeight_eq G s R p

set_option backward.isDefEq.respectTransparency false in
/-- Expanding the actual entry and exit maps counts their empty rectangle witnesses. -/
theorem stabilizationMatchingExit_entry_single_apply_eq_sum_paths (x y : GridState n) :
    stabilizationMatchingExit G s R (stabilizationMatchingEntry G s R (single x 1)) y =
      ∑ p ∈ stabilizationMatchingTwoPaths G s x y,
        stabilizationMatchingTwoPathWeight G s R p := by
  classical
  let := Fintype.ofFinite (StabilizationMatchingNode G s)
  let E (z : StabilizationMatchingNode G s) :=
    { e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
        (stabilizationMatchingTargetState G s z) // e.IsEmpty }
  let F (z : StabilizationMatchingNode G s) :=
    { f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ) // f.IsEmpty }
  let (z : StabilizationMatchingNode G s) : Fintype (E z) := Fintype.ofFinite _
  let (z : StabilizationMatchingNode G s) : Fintype (F z) := Fintype.ofFinite _
  have huniv : stabilizationMatchingTwoPaths G s x y =
      Finset.univ.sigma (fun z : StabilizationMatchingNode G s =>
        (Finset.univ : Finset (E z)).product (Finset.univ : Finset (F z))) := by
    ext p
    constructor
    · intro _
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
        Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩
    · intro _
      exact mem_stabilizationMatchingTwoPaths G s p
  rw [laurentMap_apply_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _), huniv,
    Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  rw [stabilizationMatchingEntry_single_apply, stabilizationMatchingExit_single_apply,
    laurentCoefficient_eq, laurentCoefficient_eq,
    Finset.sum_subtype _ (fun e => GridRectangleBetween.mem_emptyRectangles e),
    Finset.sum_subtype _ (fun f => GridRectangleBetween.mem_emptyRectangles f)]
  · let a (e : E z) : LaurentPolynomial R := LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns e.val.toGridRectangle).card : ℤ)
    let b (f : F z) : LaurentPolynomial R := LaurentPolynomial.T
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns f.val.toGridRectangle).card : ℤ)
    change (∑ e, a e) * (∑ f, b f) =
      ∑ p ∈ (Finset.univ : Finset (E z)).product (Finset.univ : Finset (F z)), a p.1 * b p.2
    exact (Finset.sum_mul_sum Finset.univ Finset.univ a b).trans
      (Finset.sum_product Finset.univ Finset.univ (fun p => a p.1 * b p.2)).symm

/-- The two-rectangle term is exactly the lower-bottom portion of the old coefficient. -/
theorem stabilizationMatchingExit_entry_single_apply_eq_sum (x y : GridState n) :
    stabilizationMatchingExit G s R (stabilizationMatchingEntry G s R (single x 1)) y =
      ∑ r ∈ stabilizationMatchingTwoRectangles G s x y,
        stabilizationStandardWeight G s R r := by
  rw [stabilizationMatchingExit_entry_single_apply_eq_sum_paths,
    sum_stabilizationMatchingTwoPathWeight]

end OnLeConjecture.KnotFloer.GridFull
