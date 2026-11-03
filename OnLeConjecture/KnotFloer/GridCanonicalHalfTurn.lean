/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridCanonicalClass
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Grading.HalfTurn

/-!
# Half-turn and the opposite stabilization corner

The half-turn of marking squares is `GridDiagram.rotate`, while states move by
`GridState.halfTurn`. The existing rectangle bijection preserves O counts, and
the pinned grading theorem preserves both absolute gradings. These give a native
bifiltered chain isomorphism and canonical class transport. Rotating the opposite
X stabilization reduces its normalized threshold to the previously proved corner.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex GridRectangleBetween

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R]

/-- Half-turn preserves the number of O markings in each oriented rectangle. -/
theorem card_OColumns_halfTurn {x y : GridState n} (r : GridRectangleBetween x y) :
    (G.rotate.OColumns (halfTurnEquiv x y r).toGridRectangle).card =
      (G.OColumns r.toGridRectangle).card := by
  rw [GridDiagram.card_OColumns, GridDiagram.card_OColumns,
    GridDiagram.OSet_def, GridDiagram.OSet_def, GridDiagram.rotate_O,
    card_pointSet_inter_halfTurnEquiv]

/-- The half-turn preserves every full Laurent matrix coefficient. -/
@[simp] theorem laurentCoefficient_halfTurn (x y : GridState n) :
    laurentCoefficient G.rotate R x.halfTurn y.halfTurn = laurentCoefficient G R x y := by
  classical
  rw [laurentCoefficient_eq, laurentCoefficient_eq]
  refine (Finset.sum_equiv (halfTurnEquiv x y) (fun r => ?_) (fun r _ => ?_)).symm
  · simp only [mem_emptyRectangles, isEmpty_halfTurnEquiv]
  · rw [card_OColumns_halfTurn]

/-- Laurent-linear relabeling by the half-turn. -/
def laurentHalfTurnEquiv : LaurentChain R n ≃ₗ[LaurentPolynomial R] LaurentChain R n :=
  Finsupp.domLCongr (Function.Involutive.toPerm _ GridState.halfTurn_halfTurn)

@[simp] theorem laurentHalfTurnEquiv_apply (c : LaurentChain R n) (x : GridState n) :
    laurentHalfTurnEquiv R c x = c x.halfTurn := by
  rw [laurentHalfTurnEquiv, Finsupp.domLCongr_apply]
  rfl

@[simp] theorem laurentHalfTurnEquiv_single (x : GridState n) (a : LaurentPolynomial R) :
    laurentHalfTurnEquiv R (Finsupp.single x a) = Finsupp.single x.halfTurn a := by
  rw [laurentHalfTurnEquiv, Finsupp.domLCongr_single]
  rfl

/-- The full differential intertwines the half-turn, including X-crossing terms. -/
theorem laurentDifferential_halfTurn :
    laurentDifferential G.rotate R ∘ₗ (laurentHalfTurnEquiv R).toLinearMap =
      (laurentHalfTurnEquiv R).toLinearMap ∘ₗ laurentDifferential G R := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.halfTurn = y := ⟨y.halfTurn, by simp⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    laurentHalfTurnEquiv_single, laurentDifferential_single,
    laurentOnGenerator_apply, laurentHalfTurnEquiv_apply,
    GridState.halfTurn_halfTurn, laurentCoefficient_halfTurn]

@[simp] theorem laurentDifferential_halfTurn_apply (c : LaurentChain R n) :
    laurentDifferential G.rotate R (laurentHalfTurnEquiv R c) =
      laurentHalfTurnEquiv R (laurentDifferential G R c) :=
  LinearMap.congr_fun (laurentDifferential_halfTurn G R) c

omit R in
@[simp] theorem laurentMaslovDegree_halfTurn (k : ℤ) (x : GridState n) :
    laurentMaslovDegree G.rotate k x.halfTurn = laurentMaslovDegree G k x := by
  simp only [laurentMaslovDegree, GridDiagram.maslovOℤ_rotate_halfTurn]

/-- The half-turn preserves and reflects the homogeneous submodules. -/
theorem laurentHalfTurnEquiv_mem_maslovPiece_iff (m : ℤ) (c : LaurentChain R n) :
    laurentHalfTurnEquiv R c ∈ laurentMaslovPiece G.rotate R m ↔
      c ∈ laurentMaslovPiece G R m := by
  simp only [mem_laurentMaslovPiece]
  constructor
  · intro h x k hk
    simpa using h x.halfTurn k (by simpa using hk)
  · intro h y k hk
    obtain ⟨x, rfl⟩ : ∃ x, x.halfTurn = y := ⟨y.halfTurn, by simp⟩
    simpa using h x k (by simpa using hk)

/-- The half-turn restricted to an integer Maslov degree. -/
def laurentHalfTurnPieceEquiv (m : ℤ) :
    laurentMaslovPiece G R m ≃ₗ[R] laurentMaslovPiece G.rotate R m :=
  ((laurentHalfTurnEquiv R).restrictScalars R).ofSubmodules _ _ (by
    ext c
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact (laurentHalfTurnEquiv_mem_maslovPiece_iff G R m d).mpr hd
    · intro hc
      refine ⟨(laurentHalfTurnEquiv R).symm c, ?_,
        (laurentHalfTurnEquiv R).apply_symm_apply c⟩
      exact (laurentHalfTurnEquiv_mem_maslovPiece_iff G R m _).mp (by simpa using hc))

@[simp] theorem coe_laurentHalfTurnPieceEquiv (m : ℤ) (c : laurentMaslovPiece G R m) :
    (laurentHalfTurnPieceEquiv G R m c : LaurentChain R n) = laurentHalfTurnEquiv R c := rfl

/-- The half-turn commutes with the restricted differential. -/
theorem laurentGradedDifferential_halfTurn (m : ℤ) (c : laurentMaslovPiece G R (m + 1)) :
    laurentGradedDifferential G.rotate R m (laurentHalfTurnPieceEquiv G R (m + 1) c) =
      laurentHalfTurnPieceEquiv G R m (laurentGradedDifferential G R m c) := by
  apply Subtype.ext
  simp

/-- The half-turn gives an isomorphism of native Maslov-graded complexes. -/
def laurentMaslovHalfTurnIso (S : Type*) [CommRing S] [CharP S 2] :
    laurentMaslovComplex G S ≅ laurentMaslovComplex G.rotate S :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (laurentHalfTurnPieceEquiv G S m).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      simp only [laurentMaslovComplex_d]
      ext c : 2
      exact laurentGradedDifferential_halfTurn G S j c)

/-- The total chain map preserves and reflects both filtration bounds. -/
theorem laurentHalfTurnEquiv_mem_bifiltrationLevel_iff (a b : ℝ) (c : LaurentChain R n) :
    laurentHalfTurnEquiv R c ∈ laurentBifiltrationLevel G.rotate R a b ↔
      c ∈ laurentBifiltrationLevel G R a b := by
  simp only [mem_laurentBifiltrationLevel_iff]
  constructor
  · intro h x k hk
    simpa only [GridDiagram.alexander_rotate_halfTurn] using h x.halfTurn k (by simpa using hk)
  · intro h y k hk
    obtain ⟨x, rfl⟩ : ∃ x, x.halfTurn = y := ⟨y.halfTurn, by simp⟩
    simpa only [GridDiagram.alexander_rotate_halfTurn] using h x k (by simpa using hk)

variable [CharP R 2]

/-- The native half-turn preserves and reflects both filtration levels. -/
theorem laurentMaslovHalfTurn_mem_level_iff (a b : ℝ) (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovHalfTurnIso G R).hom.f m c ∈
        (laurentMaslovBifiltration G.rotate R).level a b m ↔
      c ∈ (laurentMaslovBifiltration G R).level a b m := by
  change laurentHalfTurnEquiv R (laurentMaslovChainEquiv G R m c) ∈
    laurentBifiltrationLevel G.rotate R a b ↔ _
  rw [laurentHalfTurnEquiv_mem_bifiltrationLevel_iff]
  rfl

/-- The native forward half-turn map preserves both filtrations. -/
theorem laurentMaslovHalfTurn_preserves :
    (laurentMaslovBifiltration G R).Preserves (laurentMaslovBifiltration G.rotate R)
      (laurentMaslovHalfTurnIso G R).hom := by
  intro a b m c hc
  exact (laurentMaslovHalfTurn_mem_level_iff G R a b m c).mpr hc

/-- The native inverse half-turn map preserves both filtrations. -/
theorem laurentMaslovHalfTurn_inv_preserves :
    (laurentMaslovBifiltration G.rotate R).Preserves (laurentMaslovBifiltration G R)
      (laurentMaslovHalfTurnIso G R).inv := by
  intro a b m c hc
  apply (laurentMaslovHalfTurn_mem_level_iff G R a b m _).mp
  have h := congrArg (fun f => f.f m c) (laurentMaslovHalfTurnIso G R).inv_hom_id
  change (laurentMaslovHalfTurnIso G R).hom.f m
    ((laurentMaslovHalfTurnIso G R).inv.f m c) = c at h
  rwa [h]

/-- The half-turn preserves the weighted threshold of every specified native class. -/
theorem spectralThreshold_laurentMaslovHalfTurn (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) (t : ℝ) :
    ((laurentMaslovBifiltration G.rotate R).weighted t).spectralThreshold m
      (homologyMap (laurentMaslovHalfTurnIso G R).hom m ξ) =
        ((laurentMaslovBifiltration G R).weighted t).spectralThreshold m ξ :=
  RealFiltration.spectralThreshold_eq_of_homotopyEquiv
    (HomotopyEquiv.ofIso (laurentMaslovHalfTurnIso G R))
    ((laurentMaslovHalfTurn_preserves G R).weighted t)
    ((laurentMaslovHalfTurn_inv_preserves G R).weighted t) m ξ

omit R [CharP R 2] in
/-- The half-turn transports the unique nonzero polynomial-image class. -/
theorem gridCanonicalClass_halfTurn (hn : 2 ≤ n) :
    homologyMap (laurentMaslovHalfTurnIso G (ZMod 2)).hom 0 (gridCanonicalClass G hn) =
      gridCanonicalClass G.rotate hn :=
  gridCanonicalClass_homotopyEquiv G G.rotate hn hn
    (HomotopyEquiv.ofIso (laurentMaslovHalfTurnIso G (ZMod 2))) 0
    (Bifiltration.shifts_zero_zero_iff.mpr (laurentMaslovHalfTurn_preserves G (ZMod 2)))

omit R [CharP R 2] in
/-- The normalized spectral threshold is invariant under the half-turn. -/
theorem gridCanonicalClass_spectralThreshold_halfTurn (hn : 2 ≤ n) (t : ℝ) :
    ((laurentMaslovBifiltration G.rotate (ZMod 2)).weighted t).spectralThreshold 0
      (gridCanonicalClass G.rotate hn) =
        ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
          (gridCanonicalClass G hn) := by
  rw [← gridCanonicalClass_halfTurn G hn]
  exact spectralThreshold_laurentMaslovHalfTurn G (ZMod 2) 0 _ t

omit R [CharP R 2] in
/-- The opposite X corner has the same normalized threshold as the old grid. -/
theorem gridCanonicalClass_spectralThreshold_stabilization_succ (hn : 2 ≤ n)
    (s : Fin n) (t : ℝ) :
    RealFiltration.spectralThreshold
      ((laurentMaslovBifiltration (G.stabilizeX s.succ (G.X s).succ s) (ZMod 2)).weighted t) 0
      (gridCanonicalClass (G.stabilizeX s.succ (G.X s).succ s) (by omega)) =
        ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
          (gridCanonicalClass G hn) := by
  rw [← gridCanonicalClass_spectralThreshold_halfTurn _ (by omega) t,
    GridDiagram.rotate_stabilizeX_succ,
    gridCanonicalClass_spectralThreshold_stabilization G.rotate hn s.rev t,
    gridCanonicalClass_spectralThreshold_halfTurn G hn t]

end OnLeConjecture.KnotFloer.GridFull
