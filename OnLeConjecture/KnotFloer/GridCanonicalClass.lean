/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridAuxiliaryColumnNormalization
public import OnLeConjecture.KnotFloer.GridAntiDiagonalSpectralNormalization
public import OnLeConjecture.KnotFloer.GridStabilizationCanonicalFiltered

/-!
# The normalized class of a native grid complex

For a grid of size at least two, the degree-zero polynomial homology image
over F₂ has a unique nonzero class. This class is independent of the selected
O variable. Its threshold at parameter zero is zero. The constructed marking,
commutation and first-summand stabilization maps transport the class exactly.
These results concern native grid complexes and do not identify grid diagrams
with geometric knots.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable {n k : ℕ}

/-- The unique nonzero degree-zero polynomial-image class, initially selected using column zero. -/
def gridCanonicalClass (G : GridDiagram n) (hn : 2 ≤ n) :
    (laurentMaslovComplex G (ZMod 2)).homology 0 :=
  (grid_existsUnique_polynomialHomologyImage_class G hn ⟨0, by omega⟩).choose

/-- The selected class is nonzero in full Laurent homology. -/
theorem gridCanonicalClass_ne_zero (G : GridDiagram n) (hn : 2 ≤ n) :
    gridCanonicalClass G hn ≠ 0 :=
  (grid_existsUnique_polynomialHomologyImage_class G hn ⟨0, by omega⟩).choose_spec.1.2

/-- The class belongs to the polynomial image for every selected O variable. -/
theorem gridCanonicalClass_mem_polynomialImage (G : GridDiagram n) (hn : 2 ≤ n) (a : Fin n) :
    gridCanonicalClass G hn ∈ polynomialHomologyImage (ZMod 2) G a 0 := by
  have h := (grid_existsUnique_polynomialHomologyImage_class G hn ⟨0, by omega⟩).choose_spec.1.1
  exact (polynomialHomologyImage_eq (ZMod 2) G ⟨0, by omega⟩ a 0).le h

/-- Every nonzero degree-zero polynomial-image class is the selected class. -/
theorem gridCanonicalClass_unique (G : GridDiagram n) (hn : 2 ≤ n) (a : Fin n)
    (ξ : (laurentMaslovComplex G (ZMod 2)).homology 0)
    (hmem : ξ ∈ polynomialHomologyImage (ZMod 2) G a 0) (hne : ξ ≠ 0) :
    ξ = gridCanonicalClass G hn := by
  obtain ⟨η, _, hη⟩ := grid_existsUnique_polynomialHomologyImage_class G hn a
  exact (hη ξ ⟨hmem, hne⟩).trans
    (hη _ ⟨gridCanonicalClass_mem_polynomialImage G hn a,
      gridCanonicalClass_ne_zero G hn⟩).symm

/-- Choosing any O variable in the uniqueness theorem selects exactly the same class. -/
theorem gridCanonicalClass_eq_choose (G : GridDiagram n) (hn : 2 ≤ n) (a : Fin n) :
    gridCanonicalClass G hn = (grid_existsUnique_polynomialHomologyImage_class G hn a).choose :=
  (gridCanonicalClass_unique G hn a _
    (grid_existsUnique_polynomialHomologyImage_class G hn a).choose_spec.1.1
    (grid_existsUnique_polynomialHomologyImage_class G hn a).choose_spec.1.2).symm

/-- The general normalization agrees with the previously constructed anti-diagonal corner. -/
theorem gridCanonicalClass_eq_antiDiagonalCorner (G : GridDiagram n) (hn : 2 ≤ n)
    (hO : ∀ c, G.O c = c.rev) :
    gridCanonicalClass G hn = antiDiagonalCornerNativeClass (ZMod 2) G hn hO := by
  let a : Fin n := ⟨0, by omega⟩
  exact (gridCanonicalClass_unique G hn a _
    (antiDiagonalCornerNativeClass_mem_polynomialHomologyImage (ZMod 2) G hn hO a)
    (antiDiagonalCornerNativeClass_ne_zero (ZMod 2) G hn hO)).symm

/-- The general normalization agrees with the existing reflected torus anchor. -/
theorem gridCanonicalClass_reflectedTorus (j : ℕ) :
    gridCanonicalClass (reflectedTorusGrid j) (by unfold consecutiveTorusGridSize; omega) =
      reflectedTorusAnchorClass j (ZMod 2) := by
  rw [reflectedTorusAnchorClass_eq_antiDiagonalCornerNativeClass]
  exact gridCanonicalClass_eq_antiDiagonalCorner _ _ (reflectedTorusGrid_O_apply j)

/-- The normalized class has weighted spectral threshold zero at parameter zero. -/
theorem gridCanonicalClass_spectralThreshold_zero (G : GridDiagram n) (hn : 2 ≤ n) :
    ((laurentMaslovBifiltration G (ZMod 2)).weighted 0).spectralThreshold 0
      (gridCanonicalClass G hn) = 0 := by
  let a : Fin n := ⟨0, by omega⟩
  exact weighted_zero_spectralThreshold_eq_zero_of_polynomialImage (ZMod 2) G a
    (grid_polynomialHomologyImage_eq_bot (ZMod 2) G hn a 2 (by decide)) _
    (gridCanonicalClass_ne_zero G hn) (gridCanonicalClass_mem_polynomialImage G hn a)

/-- Actual same-O marking transport sends the normalized class to the normalized class. -/
theorem gridCanonicalClass_markingIso (G H : GridDiagram n) (hn : 2 ≤ n) (hO : G.O = H.O) :
    homologyMap (laurentMaslovMarkingIso (ZMod 2) hO).hom 0 (gridCanonicalClass G hn) =
      gridCanonicalClass H hn := by
  let a : Fin n := ⟨0, by omega⟩
  apply gridCanonicalClass_unique H hn a
  · exact (homology_marking_mem_polynomialHomologyImage_iff (ZMod 2) hO a a 0 _).mpr
      (gridCanonicalClass_mem_polynomialImage G hn a)
  · exact (map_ne_zero_iff _
      (homologyMapIso (laurentMaslovMarkingIso (ZMod 2) hO) 0).toLinearEquiv.injective).mpr
        (gridCanonicalClass_ne_zero G hn)

/-- A native homotopy equivalence with zero forward first shift transports the normalized class. -/
theorem gridCanonicalClass_homotopyEquiv (G : GridDiagram n) (H : GridDiagram k)
    (hn : 2 ≤ n) (hk : 2 ≤ k)
    (e : HomotopyEquiv (laurentMaslovComplex G (ZMod 2)) (laurentMaslovComplex H (ZMod 2)))
    (s : ℝ) (he : (laurentMaslovBifiltration G (ZMod 2)).Shifts
      (laurentMaslovBifiltration H (ZMod 2)) e.hom 0 s) :
    homologyMap e.hom 0 (gridCanonicalClass G hn) = gridCanonicalClass H hk := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin k := ⟨0, by omega⟩
  apply gridCanonicalClass_unique H hk b
  · exact polynomialHomologyImage_map_le_of_shifts (ZMod 2) G H a b e.hom s he 0
      ⟨_, gridCanonicalClass_mem_polynomialImage G hn a, rfl⟩
  · exact (map_ne_zero_iff _ (e.toHomologyIso 0).toLinearEquiv.injective).mpr
      (gridCanonicalClass_ne_zero G hn)

/-- Every actual X-switch sequence transports the normalized native class. -/
theorem XSwitchSequence.gridCanonicalClass_map {G H : GridDiagram n} {l : ℕ}
    (s : XSwitchSequence G H l) (hn : 2 ≤ n) :
    homologyMap (s.chainIso (ZMod 2)).hom 0 (gridCanonicalClass G hn) =
      gridCanonicalClass H hn :=
  gridCanonicalClass_markingIso G H hn s.O_eq

/-- A sequence of twice the genus has the required shift and normalized-class transport. -/
theorem XSwitchSequence.gridCanonicalClass_shift_and_map {G H : GridDiagram n}
    (g : ℕ) (s : XSwitchSequence G H (2 * g)) (hn : 2 ≤ n) :
    (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2))
        (s.chainIso (ZMod 2)).hom 0 (g : ℝ) ∧
      homologyMap (s.chainIso (ZMod 2)).hom 0 (gridCanonicalClass G hn) =
        gridCanonicalClass H hn :=
  ⟨s.chainIso_shifts_of_twice g (ZMod 2), s.gridCanonicalClass_map hn⟩

/-- The actual native commutation map transports the normalized class. -/
theorem gridCanonicalClass_commutation (G : GridDiagram n) (hn : 2 ≤ n)
    (C : GridDiagram.ColumnCommutationData G) :
    homologyMap (laurentMaslovCommutationHom G (ZMod 2) C) 0 (gridCanonicalClass G hn) =
      gridCanonicalClass (G.swapColumns C.column (finRotate n C.column)) hn :=
  gridCanonicalClass_homotopyEquiv G _ hn hn
    (laurentMaslovCommutationHomotopyEquiv G (ZMod 2) C) 0
    (Bifiltration.shifts_zero_zero_iff.mpr (laurentMaslovCommutationHom_preserves G (ZMod 2) C))

/-- The normalized weighted threshold is unchanged under validated column commutation. -/
theorem gridCanonicalClass_spectralThreshold_commutation (G : GridDiagram n) (hn : 2 ≤ n)
    (C : GridDiagram.ColumnCommutationData G) (t : ℝ) :
    RealFiltration.spectralThreshold
      ((laurentMaslovBifiltration
        (G.swapColumns C.column (finRotate n C.column)) (ZMod 2)).weighted t) 0
          (gridCanonicalClass (G.swapColumns C.column (finRotate n C.column)) hn) =
      ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
        (gridCanonicalClass G hn) := by
  rw [← gridCanonicalClass_commutation G hn C]
  exact spectralThreshold_laurentMaslovCommutation G (ZMod 2) C 0 _ t

/-- The constructed first-summand inclusion transports the normalized class under stabilization. -/
theorem gridCanonicalClass_stabilization (G : GridDiagram n) (hn : 2 ≤ n) (s : Fin n) :
    homologyMap (stabilizationCanonicalInclusion (ZMod 2) G s) 0 (gridCanonicalClass G hn) =
      gridCanonicalClass (G.stabilizeX s.castSucc (G.X s).castSucc s) (by omega) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin (n + 1) := ⟨0, by omega⟩
  apply gridCanonicalClass_unique _ (by omega) b
  · exact polynomialHomologyImage_map_le_of_shifts (ZMod 2) G _ a b
      (stabilizationCanonicalInclusion (ZMod 2) G s) 0
      (stabilizationCanonicalInclusion_shifts (ZMod 2) G s) 0
        ⟨_, gridCanonicalClass_mem_polynomialImage G hn a, rfl⟩
  · exact (stabilizationCanonical_homology_ne_zero_iff (ZMod 2) G s 0 _).mpr
      (gridCanonicalClass_ne_zero G hn)

/-- The first-summand projection recovers the normalized old class. -/
theorem gridCanonicalClass_stabilization_projection (G : GridDiagram n) (hn : 2 ≤ n)
    (s : Fin n) :
    homologyMap (stabilizationCanonicalProjection (ZMod 2) G s) 0
        (gridCanonicalClass (G.stabilizeX s.castSucc (G.X s).castSucc s) (by omega)) =
      gridCanonicalClass G hn := by
  rw [← gridCanonicalClass_stabilization G hn s]
  exact stabilizationCanonical_homology_retraction (ZMod 2) G s 0 _

/-- The normalized weighted threshold is unchanged under the supported X stabilization. -/
theorem gridCanonicalClass_spectralThreshold_stabilization (G : GridDiagram n) (hn : 2 ≤ n)
    (s : Fin n) (t : ℝ) :
    RealFiltration.spectralThreshold
      ((laurentMaslovBifiltration (G.stabilizeX s.castSucc (G.X s).castSucc s) (ZMod 2)).weighted t)
        0 (gridCanonicalClass (G.stabilizeX s.castSucc (G.X s).castSucc s) (by omega)) =
      ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
        (gridCanonicalClass G hn) := by
  rw [← gridCanonicalClass_stabilization G hn s]
  exact stabilizationCanonical_spectralThreshold (ZMod 2) G s 0 _ t

end OnLeConjecture.KnotFloer.GridFull
