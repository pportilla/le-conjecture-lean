/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorFourMarkRemoval
public import OnLeConjecture.KnotFloer.GridExteriorTotalHet
public import OnLeConjecture.KnotFloer.GridStabilizationColourNatural
public import OnLeConjecture.KnotFloer.GridExteriorOSwitchAnyX
public import OnLeConjecture.KnotFloer.GridExteriorODeterminant

/-!
# The removal map of a four-mark block

Let `K` be a four-mark insertion of a grid diagram `G` of size `n` at the column `c`
(`IsFourMarkInsertion`), let `A₁` and `A₂` be the two south-west stabilizations of
`GridExteriorFourMarkRemoval`, and let `B` be the auxiliary pair with the `O` markings of `A₂` and
the `X` markings of `K`. The removal map is the Laurent map

  `M = R₁ R₂ Φ_{c + 1} Φ_c F : C(K) → C(G)`,

where `F` is the `O` switch of the columns `c, c + 1` of `K`, the maps `Φ_c` and `Φ_{c+1}` are the
derivatives of `A₂` at the two `O` markings of the block, which coincide with `X` markings of `B`,
and `R₂` and `R₁` are the canonical destabilization maps of `A₂` and `A₁`.

This file introduces `PieceShift`: a Laurent map between grids of possibly different sizes that
raises the Maslov degree of every homogeneous chain by `d` and the second filtration coordinate
by at most `s`, with respect to given Alexander functions. Composition adds the degrees and the
shifts. The removal map has degree `1` and second shift `1/2` from the Alexander function of `K`
to that of `G` (`pieceShift_fourMarkRemovalMap`). This is the count of the written proof of
Statement E (`statement_E_complete_proof.tex`, Section 12, "Complete operation count"): a
four-mark normalization of shift zero followed by a singleton contraction of shift `1/2`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp

/-! ### Degree and filtration bounds of Laurent maps -/

section PieceShift

variable {R : Type*} [CommRing R] [CharP R 2]

/-- A Laurent map raising the Maslov degree of every homogeneous chain by `d` and the second
filtration coordinate by at most `s`, for the Alexander functions `α` and `β`. -/
def PieceShift {n k : ℕ} (G : GridDiagram n) (H : GridDiagram k) (α : GridState n → ℚ)
    (β : GridState k → ℚ) (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (d : ℤ) (s : ℝ) : Prop :=
  ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
    f c ∈ laurentMaslovPiece H R (m + d) ∧
      ∀ u v, c ∈ alexanderLevel R α u v → f c ∈ alexanderLevel R β u (v + s)

omit [CharP R 2] in
theorem PieceShift.comp {n k l : ℕ} {G : GridDiagram n} {H : GridDiagram k} {K : GridDiagram l}
    {α : GridState n → ℚ} {β : GridState k → ℚ} {γ : GridState l → ℚ}
    {f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k}
    {g : LaurentChain R k →ₗ[LaurentPolynomial R] LaurentChain R l} {d d' : ℤ} {s s' : ℝ}
    (hf : PieceShift G H α β f d s) (hg : PieceShift H K β γ g d' s') :
    PieceShift G K α γ (g ∘ₗ f) (d + d') (s + s') := by
  intro m c hc
  obtain ⟨h1, h2⟩ := hf m c hc
  obtain ⟨h3, h4⟩ := hg (m + d) (f c) h1
  refine ⟨?_, fun u v hcl => ?_⟩
  · rw [← add_assoc]
    exact h3
  · rw [← add_assoc]
    exact h4 u (v + s) (h2 u v hcl)

omit [CharP R 2] in
theorem PieceShift.of_levelShift {n : ℕ} {G H : GridDiagram n} {α β : GridState n → ℚ}
    {f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n} {d : ℤ} {s : ℝ}
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R (m + d))
    (hlev : LevelShift R α β f s) : PieceShift G H α β f d s :=
  fun m c hc => ⟨hdeg m c hc, fun u v hcl => hlev u v c hcl⟩

/-- A native morphism with filtration shifts `(0, s)` gives a degree-zero piece shift of any
Laurent map agreeing with it on every Maslov piece. -/
theorem PieceShift.of_graded {n k : ℕ} {G : GridDiagram n} {H : GridDiagram k}
    (φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R)
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hcompat : ∀ (m : ℤ) (x : (laurentMaslovComplex G R).X m),
      (laurentMaslovChainEquiv H R m (φ.f m x) : LaurentChain R k) =
        f (laurentMaslovChainEquiv G R m x)) {s : ℝ}
    (hφ : (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R) φ 0 s) :
    PieceShift G H G.alexander H.alexander f 0 s := by
  intro m c hc
  set x := (laurentMaslovChainEquiv G R m).symm ⟨c, hc⟩ with hx
  have hxc : (laurentMaslovChainEquiv G R m x : LaurentChain R n) = c := by
    rw [hx, LinearEquiv.apply_symm_apply]
  have hfc : f c = (laurentMaslovChainEquiv H R m (φ.f m x) : LaurentChain R k) := by
    rw [hcompat, hxc]
  refine ⟨?_, fun u v hcl => ?_⟩
  · rw [add_zero, hfc]
    exact (laurentMaslovChainEquiv H R m (φ.f m x)).property
  · have h := hφ u v m x (by
      change (laurentMaslovChainEquiv G R m x : LaurentChain R n) ∈
        laurentBifiltrationLevel G R u v
      rw [hxc, laurentBifiltrationLevel_eq_alexanderLevel]
      exact hcl)
    rw [add_zero] at h
    change (laurentMaslovChainEquiv H R m (φ.f m x) : LaurentChain R k) ∈
      laurentBifiltrationLevel H R u (v + s) at h
    rw [hfc, ← laurentBifiltrationLevel_eq_alexanderLevel]
    exact h

omit [CharP R 2] in
theorem PieceShift.degree_zero {n k : ℕ} {G : GridDiagram n} {H : GridDiagram k}
    {α : GridState n → ℚ} {β : GridState k → ℚ}
    {f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k} {s : ℝ}
    (hf : PieceShift G H α β f 0 s) :
    ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m → f c ∈ laurentMaslovPiece H R m :=
  fun m c hc => by simpa using (hf m c hc).1

/-- A degree-zero piece shift for the native Alexander functions gives the filtration shifts of
the corresponding native morphism. -/
theorem laurentMaslovHomOfMapHet_shifts_of_pieceShift {n k : ℕ} {G : GridDiagram n}
    {H : GridDiagram k} {f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k} {s : ℝ}
    (hf : PieceShift G H G.alexander H.alexander f 0 s)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) :
    (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R)
      (laurentMaslovHomOfMapHet G H f hf.degree_zero hcomm) 0 s := by
  intro u v m x hx
  have hp := (hf m _ (laurentMaslovChainEquiv G R m x).property).2 u v (by
    change (laurentMaslovChainEquiv G R m x : LaurentChain R n) ∈
      laurentBifiltrationLevel G R u v at hx
    rwa [laurentBifiltrationLevel_eq_alexanderLevel] at hx)
  rw [add_zero]
  change (laurentMaslovChainEquiv H R m
    ((laurentMaslovHomOfMapHet G H f hf.degree_zero hcomm).f m x) :
    LaurentChain R k) ∈ laurentBifiltrationLevel H R u (v + s)
  rw [laurentMaslovChainEquiv_homOfMapHet, laurentBifiltrationLevel_eq_alexanderLevel]
  exact hp

end PieceShift

/-! ### Derivatives depend only on the O markings -/

theorem oDerivative_congr_O {n : ℕ} {R : Type*} [CommRing R] {G H : GridDiagram n}
    (h : G.O = H.O) (P : Finset (Fin n)) : oDerivative R G P = oDerivative R H P := by
  have hset : G.OSet = H.OSet := by rw [GridDiagram.OSet, GridDiagram.OSet, h]
  unfold oDerivative oDeformWeight oSquareWeight
  rw [hset]

/-! ### The removal map -/

section Removal

variable {n : ℕ} (G : GridDiagram n) (c : Fin n)

/-- The auxiliary pair after the `O` switch of the block: the `O` markings of the double
stabilization and the `X` markings of the four-mark insertion. -/
def fourMarkSwitchPair (K : GridDiagram (n + 2)) : AuxiliaryPair (n + 2) :=
  ⟨(fourMarkStabTwo G c).O, K.X⟩

variable {G c} {K : GridDiagram (n + 2)}

theorem fourMarkStabTwo_O_castSucc_castSucc :
    (fourMarkStabTwo G c).O c.castSucc.castSucc = (G.X c).succ.castSucc := by
  rw [fourMarkStabTwo_O, GridState.insertPoint_apply_newColumn]

theorem fourMarkStabTwo_O_castSucc_succ :
    (fourMarkStabTwo G c).O c.castSucc.succ = (G.X c).castSucc.castSucc := by
  apply Fin.ext
  rw [← gridRowVal_val, fourMarkStabTwo_O]
  have h := gridRowVal_insertPoint_of_gt (G.O.insertPoint c.castSucc (G.X c).castSucc)
    c.castSucc.castSucc (G.X c).succ.castSucc
    (k := c.castSucc.succ.val) (by simp) (by simp)
  rw [h]
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel]
  have h0 := gridRowVal_insertPoint_self G.O c.castSucc (G.X c).castSucc
  simp only [Fin.val_castSucc] at h0
  rw [h0]
  simp [natSuccAbove]

theorem fourMarkInsertion_X_castSucc_castSucc (hK : IsFourMarkInsertion G c K) :
    K.X c.castSucc.castSucc = (G.X c).succ.castSucc := by
  apply Fin.ext
  have hc := c.isLt
  rw [← gridRowVal_val, hK.2, gridRowVal_swapRows _ _ _ _ (by simp; omega)]
  have h1 := gridRowVal_insertPoint_of_lt (G.X.insertPoint c.castSucc (G.X c).castSucc)
    c.castSucc.succ (G.X c).castSucc.succ (k := c.castSucc.castSucc.val) (by simp)
  have h0 := gridRowVal_insertPoint_self G.X c.castSucc (G.X c).castSucc
  simp only [Fin.val_castSucc, Fin.val_succ] at h1 h0 ⊢
  rw [h1, h0]
  simp [natSuccAbove]

theorem fourMarkInsertion_X_castSucc_succ (hK : IsFourMarkInsertion G c K) :
    K.X c.castSucc.succ = (G.X c).castSucc.castSucc := by
  apply Fin.ext
  have hc := c.isLt
  rw [← gridRowVal_val, hK.2, gridRowVal_swapRows _ _ _ _ (by simp)]
  have h1 := gridRowVal_insertPoint_self (G.X.insertPoint c.castSucc (G.X c).castSucc)
    c.castSucc.succ (G.X c).castSucc.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h1 ⊢
  rw [h1]
  simp

/-- The first `O` marking of the switched block coincides with an `X` marking. -/
theorem fourMarkSwitchPair_coincident_left (hK : IsFourMarkInsertion G c K) :
    (fourMarkSwitchPair G c K).O c.castSucc.castSucc =
      (fourMarkSwitchPair G c K).X c.castSucc.castSucc := by
  change (fourMarkStabTwo G c).O _ = K.X _
  rw [fourMarkStabTwo_O_castSucc_castSucc, fourMarkInsertion_X_castSucc_castSucc hK]

/-- The second `O` marking of the switched block coincides with an `X` marking. -/
theorem fourMarkSwitchPair_coincident_right (hK : IsFourMarkInsertion G c K) :
    (fourMarkSwitchPair G c K).O c.castSucc.succ =
      (fourMarkSwitchPair G c K).X c.castSucc.succ := by
  change (fourMarkStabTwo G c).O _ = K.X _
  rw [fourMarkStabTwo_O_castSucc_succ, fourMarkInsertion_X_castSucc_succ hK]

/-- Passing from the switched pair to the double stabilization raises the Alexander function by
at most one. -/
theorem fourMarkStabTwo_alexander_le (hK : IsFourMarkInsertion G c K) (x : GridState (n + 2)) :
    (fourMarkStabTwo G c).alexander x ≤ (fourMarkSwitchPair G c K).alexander x + 1 := by
  have ha1 : c.castSucc.succ ≠ finRotate (n + 2) c.castSucc.succ := by
    rw [finRotate_castSucc_succ]
    intro h
    have := congrArg Fin.val h
    simp at this
  have ha0 : c.castSucc.castSucc ≠ finRotate (n + 2) c.castSucc.castSucc := by
    rw [finRotate_castSucc_castSucc]
    intro h
    have := congrArg Fin.val h
    simp at this
  have h2 := markingMaslovℤ_swapColumns_sub_le K.X ha1 x
  set S₁ := K.X.swapColumns c.castSucc.succ (finRotate (n + 2) c.castSucc.succ) with hS₁
  set S₂ := S₁.swapColumns c.castSucc.castSucc (finRotate (n + 2) c.castSucc.castSucc)
    with hS₂
  have h1 : markingMaslovℤ S₂ x - markingMaslovℤ S₁ x ≤ 1 ∧
      -1 ≤ markingMaslovℤ S₂ x - markingMaslovℤ S₁ x :=
    markingMaslovℤ_swapColumns_sub_le S₁ ha0 x
  rw [← alexander_toAuxiliaryPair]
  simp only [AuxiliaryPair.alexander, toAuxiliaryPair_O, toAuxiliaryPair_X, fourMarkSwitchPair]
  rw [fourMarkStabTwo_X_eq_swapColumns G c hK, ← hS₁, ← hS₂]
  have hint : (markingMaslovℤ K.X x : ℚ) - (markingMaslovℤ S₂ x : ℚ) ≤ 2 := by
    exact_mod_cast (by omega)
  push_cast
  linarith

end Removal

/-! ### Chain maps between grids of different sizes -/

section ChainHet

variable {n k l : ℕ} {G : GridDiagram n} {H : GridDiagram k} {L : GridDiagram l}

theorem laurentChainHet_comp
    {f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) k}
    {g : LaurentChain (ZMod 2) k →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) l}
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    (hg : laurentDifferential L (ZMod 2) ∘ₗ g = g ∘ₗ laurentDifferential H (ZMod 2)) :
    laurentDifferential L (ZMod 2) ∘ₗ (g ∘ₗ f) = (g ∘ₗ f) ∘ₗ laurentDifferential G (ZMod 2) := by
  rw [← LinearMap.comp_assoc, hg, LinearMap.comp_assoc, hf, LinearMap.comp_assoc]

theorem PieceShift.congr {R : Type*} [CommRing R] {α : GridState n → ℚ} {β : GridState k → ℚ}
    {f g : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k} {d d' : ℤ} {s s' : ℝ}
    (h : PieceShift G H α β f d s) (hfg : f = g) (hd : d = d') (hs : s = s') :
    PieceShift G H α β g d' s' := by
  subst hfg hd hs
  exact h

/-- For grids of the same size, the heterogeneous induced map is the induced map. -/
theorem laurentTotalHomologyMapHet_eq {G H : GridDiagram n}
    (f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2)) :
    laurentTotalHomologyMapHet f hf = laurentTotalHomologyMap f hf := rfl

end ChainHet

/-! ### The first component of the stabilization projection -/

section StabilizationProjection

variable {n : ℕ}

/-- The first component of the full stabilization projection, as a Laurent map. -/
def stabilizationFstProj (G : GridDiagram n) (s : Fin n) :
    LaurentChain (ZMod 2) (n + 1) →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n :=
  LinearMap.fst (LaurentPolynomial (ZMod 2)) (LaurentChain (ZMod 2) n)
      (LaurentChain (ZMod 2) n) ∘ₗ
    (fullStabilizationTransferredRetraction G s (ZMod 2)).proj

theorem laurentDifferential_comp_stabilizationFstProj (G : GridDiagram n) (s : Fin n) :
    laurentDifferential G (ZMod 2) ∘ₗ stabilizationFstProj G s =
      stabilizationFstProj G s ∘ₗ
        laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) (ZMod 2) := by
  have hfst := fst_comp_stabilizationTransferredDifferential G s (ZMod 2)
  apply LinearMap.ext
  intro z
  have h1 := LinearMap.congr_fun
    (fullStabilizationTransferredRetraction G s (ZMod 2)).proj_comp_dM z
  have h2 := LinearMap.congr_fun hfst
    ((fullStabilizationTransferredRetraction G s (ZMod 2)).proj z)
  simp only [LinearMap.comp_apply] at h1 h2
  simp only [stabilizationFstProj, LinearMap.comp_apply]
  rw [h1, h2]

theorem pieceShift_stabilizationFstProj (G : GridDiagram n) (s : Fin n) :
    PieceShift (G.stabilizeX s.castSucc (G.X s).castSucc s) G
      (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander G.alexander
      (stabilizationFstProj G s) 0 0 :=
  PieceShift.of_graded (stabilizationCanonicalProjection (ZMod 2) G s) _
    (fun m x => stabilizationCanonicalProjection_apply (ZMod 2) G s m x)
    (stabilizationCanonicalProjection_shifts (ZMod 2) G s)

/-- The first component of the stabilization projection carries the total canonical class to
the total canonical class. -/
theorem stabilizationFstProj_totalCanonicalClass (G : GridDiagram n) (hn : 2 ≤ n) (s : Fin n) :
    laurentTotalHomologyMapHet (stabilizationFstProj G s)
        (laurentDifferential_comp_stabilizationFstProj G s)
        (totalCanonicalClass (G.stabilizeX s.castSucc (G.X s).castSucc s) (by omega)) =
      totalCanonicalClass G hn := by
  unfold totalCanonicalClass
  rw [← laurentGradedToTotal_naturality_of_compat
    (stabilizationCanonicalProjection (ZMod 2) G s) _ _
    (fun m x => stabilizationCanonicalProjection_apply (ZMod 2) G s m x),
    gridCanonicalClass_stabilization_projection G hn s]

end StabilizationProjection

/-! ### The removal map: chain property, degree and shift -/

section RemovalMap

variable {n : ℕ}

theorem castSucc_castSucc_ne_finRotate (c : Fin n) :
    c.castSucc.castSucc ≠ finRotate (n + 2) c.castSucc.castSucc := by
  rw [finRotate_castSucc_castSucc]
  intro h
  have := congrArg Fin.val h
  simp at this

variable (G : GridDiagram n) (c : Fin n) (K : GridDiagram (n + 2))

/-- The composite `R₁ R₂` of the two stabilization projections of the four-mark block. -/
def fourMarkProjections :
    LaurentChain (ZMod 2) (n + 2) →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n :=
  stabilizationFstProj G c ∘ₗ stabilizationFstProj (fourMarkStabOne G c) c.castSucc

/-- The removal map `R₁ R₂ Φ_{c + 1} Φ_c F` of the four-mark block. -/
def fourMarkRemovalMap :
    LaurentChain (ZMod 2) (n + 2) →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n :=
  fourMarkProjections G c ∘ₗ
    (oDerivative (ZMod 2) (fourMarkStabTwo G c) {finRotate (n + 2) c.castSucc.castSucc} ∘ₗ
      oDerivative (ZMod 2) (fourMarkStabTwo G c) {c.castSucc.castSucc} ∘ₗ
      oSwitchMap (ZMod 2) K c.castSucc.castSucc)

/-- The normalization `R₁ R₂ Φ_c F` of the four-mark block, of degree zero. -/
def fourMarkNormalizationMap :
    LaurentChain (ZMod 2) (n + 2) →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n :=
  fourMarkProjections G c ∘ₗ
    (oDerivative (ZMod 2) (fourMarkStabTwo G c) {c.castSucc.castSucc} ∘ₗ
      oSwitchMap (ZMod 2) K c.castSucc.castSucc)

variable {G c K}

theorem laurentDifferential_comp_fourMarkProjections :
    laurentDifferential G (ZMod 2) ∘ₗ fourMarkProjections G c =
      fourMarkProjections G c ∘ₗ laurentDifferential (fourMarkStabTwo G c) (ZMod 2) :=
  laurentChainHet_comp (laurentDifferential_comp_stabilizationFstProj (fourMarkStabOne G c)
    c.castSucc) (laurentDifferential_comp_stabilizationFstProj G c)

theorem laurentDifferential_comp_fourMarkSwitchDerivative (hK : IsFourMarkInsertion G c K) :
    laurentDifferential (fourMarkStabTwo G c) (ZMod 2) ∘ₗ
        (oDerivative (ZMod 2) (fourMarkStabTwo G c) {c.castSucc.castSucc} ∘ₗ
          oSwitchMap (ZMod 2) K c.castSucc.castSucc) =
      (oDerivative (ZMod 2) (fourMarkStabTwo G c) {c.castSucc.castSucc} ∘ₗ
          oSwitchMap (ZMod 2) K c.castSucc.castSucc) ∘ₗ laurentDifferential K (ZMod 2) :=
  laurentChainHet_comp (laurentDifferential_comp_oSwitchMap (ZMod 2)
    (castSucc_castSucc_ne_finRotate c) (fourMarkStabTwo_O_eq_swapColumns G c hK))
    (laurentDifferential_comp_oDerivative_eq _ _)

theorem laurentDifferential_comp_fourMarkDoubleDerivative (hK : IsFourMarkInsertion G c K) :
    laurentDifferential (fourMarkStabTwo G c) (ZMod 2) ∘ₗ
        (oDerivative (ZMod 2) (fourMarkStabTwo G c) {finRotate (n + 2) c.castSucc.castSucc} ∘ₗ
          oDerivative (ZMod 2) (fourMarkStabTwo G c) {c.castSucc.castSucc} ∘ₗ
          oSwitchMap (ZMod 2) K c.castSucc.castSucc) =
      (oDerivative (ZMod 2) (fourMarkStabTwo G c) {finRotate (n + 2) c.castSucc.castSucc} ∘ₗ
          oDerivative (ZMod 2) (fourMarkStabTwo G c) {c.castSucc.castSucc} ∘ₗ
          oSwitchMap (ZMod 2) K c.castSucc.castSucc) ∘ₗ laurentDifferential K (ZMod 2) :=
  laurentChainHet_comp (laurentDifferential_comp_fourMarkSwitchDerivative hK)
    (laurentDifferential_comp_oDerivative_eq _ _)

theorem laurentDifferential_comp_fourMarkRemovalMap (hK : IsFourMarkInsertion G c K) :
    laurentDifferential G (ZMod 2) ∘ₗ fourMarkRemovalMap G c K =
      fourMarkRemovalMap G c K ∘ₗ laurentDifferential K (ZMod 2) :=
  laurentChainHet_comp (laurentDifferential_comp_fourMarkDoubleDerivative hK)
    laurentDifferential_comp_fourMarkProjections

theorem laurentDifferential_comp_fourMarkNormalizationMap (hK : IsFourMarkInsertion G c K) :
    laurentDifferential G (ZMod 2) ∘ₗ fourMarkNormalizationMap G c K =
      fourMarkNormalizationMap G c K ∘ₗ laurentDifferential K (ZMod 2) :=
  laurentChainHet_comp (laurentDifferential_comp_fourMarkSwitchDerivative hK)
    laurentDifferential_comp_fourMarkProjections

/-- **Degree and shift of the removal map.** The removal map raises the Maslov degree by one and
the second filtration coordinate by at most `1/2`. -/
theorem pieceShift_fourMarkRemovalMap (hK : IsFourMarkInsertion G c K) (hn : 2 ≤ n) :
    PieceShift K G K.alexander G.alexander (fourMarkRemovalMap G c K) 1 (1 / 2) := by
  have hn2 : 2 ≤ n + 2 := by omega
  have ha := castSucc_castSucc_ne_finRotate c
  have hO := fourMarkStabTwo_O_eq_swapColumns G c hK
  have hF : PieceShift K (fourMarkStabTwo G c) K.alexander (fourMarkSwitchPair G c K).alexander
      (oSwitchMap (ZMod 2) K c.castSucc.castSucc) (-1) (-1 / 2) := by
    refine PieceShift.of_levelShift (fun m x hx => ?_) ?_
    · have := oSwitchMap_mem_maslovPiece (R := ZMod 2) ha hO hx
      simpa [sub_eq_add_neg] using this
    · exact levelShift_oSwitchMap_auxiliary (R := ZMod 2) (B := fourMarkSwitchPair G c K) ha hO
        rfl
  have hΦ : ∀ h : Fin (n + 2), (fourMarkSwitchPair G c K).O h = (fourMarkSwitchPair G c K).X h →
      PieceShift (fourMarkStabTwo G c) (fourMarkStabTwo G c) (fourMarkSwitchPair G c K).alexander
        (fourMarkSwitchPair G c K).alexander
        (oDerivative (ZMod 2) (fourMarkStabTwo G c) {h}) 1 0 := by
    intro h hh
    refine PieceShift.of_levelShift
      (fun m x hx => oDerivative_singleton_mem_maslovPiece _ h hx) ?_
    have := levelShift_oDerivative_of_coincident (R := ZMod 2) (fourMarkSwitchPair G c K) hn2 hh
    rwa [oDerivative_congr_O (show ((fourMarkSwitchPair G c K).carrier hn2).O =
      (fourMarkStabTwo G c).O from rfl)] at this
  have hid : PieceShift (fourMarkStabTwo G c) (fourMarkStabTwo G c)
      (fourMarkSwitchPair G c K).alexander (fourMarkStabTwo G c).alexander
      (LinearMap.id : LaurentChain (ZMod 2) (n + 2) →ₗ[LaurentPolynomial (ZMod 2)] _) 0 1 :=
    PieceShift.of_levelShift (fun m x hx => by simpa using hx)
      (levelShift_id fun x => by exact_mod_cast fourMarkStabTwo_alexander_le hK x)
  have hright : (fourMarkSwitchPair G c K).O (finRotate (n + 2) c.castSucc.castSucc) =
      (fourMarkSwitchPair G c K).X (finRotate (n + 2) c.castSucc.castSucc) := by
    rw [finRotate_castSucc_castSucc]
    exact fourMarkSwitchPair_coincident_right hK
  have hR := (pieceShift_stabilizationFstProj (fourMarkStabOne G c) c.castSucc).comp
    (pieceShift_stabilizationFstProj G c)
  have h := (((hF.comp (hΦ _ (fourMarkSwitchPair_coincident_left hK))).comp
    (hΦ _ hright)).comp hid).comp hR
  refine h.congr ?_ (by norm_num) (by norm_num)
  rw [LinearMap.id_comp]
  rfl

end RemovalMap

/-! ### Colour derivatives on total homology -/

section TotalDerivative

variable {n : ℕ}

/-- The colour derivative of a set of columns on total homology. -/
def totalODerivative (G : GridDiagram n) (P : Finset (Fin n)) :
    laurentTotalHomology G (ZMod 2) →ₗ[LaurentPolynomial (ZMod 2)]
      laurentTotalHomology G (ZMod 2) :=
  laurentTotalHomologyMap (oDerivative (ZMod 2) G P) (laurentDifferential_comp_oDerivative_eq _ _)

theorem laurentTotalHomologyMap_comp_apply {G H L : GridDiagram n}
    {f g : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n}
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    (hg : laurentDifferential L (ZMod 2) ∘ₗ g = g ∘ₗ laurentDifferential H (ZMod 2))
    (hgf : laurentDifferential L (ZMod 2) ∘ₗ (g ∘ₗ f) = (g ∘ₗ f) ∘ₗ laurentDifferential G (ZMod 2))
    (ξ : laurentTotalHomology G (ZMod 2)) :
    laurentTotalHomologyMap (g ∘ₗ f) hgf ξ =
      laurentTotalHomologyMap g hg (laurentTotalHomologyMap f hf ξ) :=
  LinearMap.congr_fun (laurentTotalHomologyMap_comp f g hf hg hgf) ξ

theorem laurentTotalHomologyMapHet_comp_apply {k l : ℕ} {G : GridDiagram n} {H : GridDiagram k}
    {L : GridDiagram l}
    {f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) k}
    {g : LaurentChain (ZMod 2) k →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) l}
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    (hg : laurentDifferential L (ZMod 2) ∘ₗ g = g ∘ₗ laurentDifferential H (ZMod 2))
    (hgf : laurentDifferential L (ZMod 2) ∘ₗ (g ∘ₗ f) = (g ∘ₗ f) ∘ₗ laurentDifferential G (ZMod 2))
    (ξ : laurentTotalHomology G (ZMod 2)) :
    laurentTotalHomologyMapHet (g ∘ₗ f) hgf ξ =
      laurentTotalHomologyMapHet g hg (laurentTotalHomologyMapHet f hf ξ) :=
  LinearMap.congr_fun (laurentTotalHomologyMapHet_comp f g hf hg hgf) ξ

theorem totalODerivative_eq_sum (G : GridDiagram n) (P : Finset (Fin n)) :
    totalODerivative G P = ∑ h ∈ P, totalODerivative G {h} := by
  unfold totalODerivative
  have hs : laurentDifferential G (ZMod 2) ∘ₗ (∑ h ∈ P, oDerivative (ZMod 2) G {h}) =
      (∑ h ∈ P, oDerivative (ZMod 2) G {h}) ∘ₗ laurentDifferential G (ZMod 2) := by
    rw [← oDerivative_eq_sum]
    exact laurentDifferential_comp_oDerivative_eq _ _
  rw [laurentTotalHomologyMap_congr (oDerivative_eq_sum G P) _ hs]
  exact laurentTotalHomologyMap_finsetSum P _ (fun h => laurentDifferential_comp_oDerivative_eq _ _)
    hs

/-- The derivatives of two columns commute on total homology. -/
theorem totalODerivative_singleton_comm (G : GridDiagram n) (h k : Fin n)
    (ξ : laurentTotalHomology G (ZMod 2)) :
    totalODerivative G {h} (totalODerivative G {k} ξ) =
      totalODerivative G {k} (totalODerivative G {h} ξ) := by
  by_cases hk : h = k
  · subst hk
    rfl
  have hh := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) G {h}
  have hk' := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) G {k}
  have e := laurentTotalHomologyMap_eq_of_homotopy _ _ (isChain_comp hk' hh) (isChain_comp hh hk')
    (oSecondDerivative (ZMod 2) G {h, k}) (oDerivative_anticommutator_homotopy G hk)
  have := LinearMap.congr_fun e ξ
  rwa [laurentTotalHomologyMap_comp_apply hk' hh, laurentTotalHomologyMap_comp_apply hh hk'] at this

/-- The derivative of a set of columns commutes with the derivative of a column on total
homology. -/
theorem totalODerivative_comm_singleton (G : GridDiagram n) (P : Finset (Fin n)) (h : Fin n)
    (ξ : laurentTotalHomology G (ZMod 2)) :
    totalODerivative G P (totalODerivative G {h} ξ) =
      totalODerivative G {h} (totalODerivative G P ξ) := by
  rw [totalODerivative_eq_sum G P, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => totalODerivative_singleton_comm G k h ξ

/-- The square of the derivative of a column vanishes on total homology. -/
theorem totalODerivative_singleton_self (G : GridDiagram n) (h : Fin n)
    (ξ : laurentTotalHomology G (ZMod 2)) :
    totalODerivative G {h} (totalODerivative G {h} ξ) = 0 := by
  have hh := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) G {h}
  unfold totalODerivative
  rw [← laurentTotalHomologyMap_comp_apply hh hh (isChain_comp hh hh),
    laurentTotalHomologyMap_congr (oDerivative_singleton_comp_self G h) _
      (by rw [LinearMap.comp_zero, LinearMap.zero_comp]),
    laurentTotalHomologyMap_zero]
  rfl

/-! ### Total homology relations of an O switch -/

variable {K A : GridDiagram n} {a : Fin n}

/-- With `F` the O switch of the columns `a, a + 1`, the composite `Φ_{a+1} Φ_a F` equals
`Φ_a F Φ_{a, a+1}` on total homology. -/
theorem total_oDerivative_pair_switch (ha : a ≠ finRotate n a)
    (hO : A.O = K.O.swapColumns a (finRotate n a)) (ξ : laurentTotalHomology K (ZMod 2)) :
    totalODerivative A {finRotate n a} (totalODerivative A {a}
        (laurentTotalHomologyMap (oSwitchMap (ZMod 2) K a)
          (laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO) ξ)) =
      totalODerivative A {a} (laurentTotalHomologyMap (oSwitchMap (ZMod 2) K a)
        (laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO)
        (totalODerivative K {a, finRotate n a} ξ)) := by
  have hn1 : a ∉ ({finRotate n a} : Finset (Fin n)) := by
    rw [Finset.mem_singleton]
    exact ha
  have hn2 : finRotate n a ∉ ({a} : Finset (Fin n)) := by
    rw [Finset.mem_singleton]
    exact Ne.symm ha
  have e1 := fun ξ => LinearMap.congr_fun (laurentTotalHomologyMap_colour_switch ha hO
    {finRotate n a} {a} (by simp) 1
    (by rw [if_neg hn1, if_pos (Finset.mem_singleton_self _), zero_add])) ξ
  have e2 := fun ξ => LinearMap.congr_fun (laurentTotalHomologyMap_colour_switch ha hO
    {a} {finRotate n a} (by simp) 1
    (by rw [if_pos (Finset.mem_singleton_self _), if_neg hn2, add_zero])) ξ
  have e3 := fun ξ => LinearMap.congr_fun (laurentTotalHomologyMap_colour_detecting ha hO
    {a} {finRotate n a} (by simp)) ξ
  simp only [LinearMap.comp_apply, LinearMap.add_apply, one_smul] at e1 e2 e3
  have hsum : totalODerivative K {a, finRotate n a} ξ =
      totalODerivative K {a} ξ + totalODerivative K {finRotate n a} ξ := by
    rw [totalODerivative_eq_sum, Finset.sum_pair ha, LinearMap.add_apply]
  unfold totalODerivative at hsum ⊢
  rw [e1, map_add, e2, e3, hsum, map_add, map_add, e1, e1]
  have hsq := totalODerivative_singleton_self K (finRotate n a) ξ
  have hcm := totalODerivative_singleton_comm K a (finRotate n a) ξ
  unfold totalODerivative at hsq hcm
  rw [hsq, map_zero, hcm]
  abel

/-- For a set of columns containing neither `a` nor `a + 1`, the derivative commutes with
`Φ_a F` on total homology. -/
theorem total_oDerivative_switch_of_not_mem (ha : a ≠ finRotate n a)
    (hO : A.O = K.O.swapColumns a (finRotate n a)) {P : Finset (Fin n)} (h1 : a ∉ P)
    (h2 : finRotate n a ∉ P) (ξ : laurentTotalHomology K (ZMod 2)) :
    totalODerivative A P (totalODerivative A {a}
        (laurentTotalHomologyMap (oSwitchMap (ZMod 2) K a)
          (laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO) ξ)) =
      totalODerivative A {a} (laurentTotalHomologyMap (oSwitchMap (ZMod 2) K a)
        (laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO) (totalODerivative K P ξ)) := by
  have hP : P = P.map (Equiv.swap a (finRotate n a)).toEmbedding := by
    ext x
    rw [Finset.mem_map_equiv, Equiv.symm_swap]
    by_cases hxa : x = a
    · rw [hxa, Equiv.swap_apply_left]
      exact iff_of_false h1 h2
    by_cases hxb : x = finRotate n a
    · rw [hxb, Equiv.swap_apply_right]
      exact iff_of_false h2 h1
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have e1 := fun ξ => LinearMap.congr_fun (laurentTotalHomologyMap_colour_switch ha hO
    P P hP 0 (by rw [if_neg h1, if_neg h2, add_zero])) ξ
  simp only [LinearMap.comp_apply, zero_smul, add_zero] at e1
  rw [totalODerivative_comm_singleton]
  unfold totalODerivative
  rw [e1]

end TotalDerivative

/-! ### The removal map on total homology -/

section RemovalHomology

variable {n : ℕ} {G : GridDiagram n} {c : Fin n} {K : GridDiagram (n + 2)}

/-- The first component of the stabilization projection intertwines the colour derivatives on
total homology when the new column and the split column have the same colour. -/
theorem stabilizationFstProj_totalODerivative (G : GridDiagram n) (s : Fin n)
    (P : Finset (Fin (n + 1))) (hP : s.castSucc ∈ P ↔ s.succ ∈ P)
    (ξ : laurentTotalHomology (G.stabilizeX s.castSucc (G.X s).castSucc s) (ZMod 2)) :
    laurentTotalHomologyMapHet (stabilizationFstProj G s)
        (laurentDifferential_comp_stabilizationFstProj G s)
        (totalODerivative (G.stabilizeX s.castSucc (G.X s).castSucc s) P ξ) =
      totalODerivative G (P.preimage s.castSucc.succAbove
          s.castSucc.succAbove_right_injective.injOn)
        (laurentTotalHomologyMapHet (stabilizationFstProj G s)
          (laurentDifferential_comp_stabilizationFstProj G s) ξ) := by
  have hR := laurentDifferential_comp_stabilizationFstProj G s
  have hA := laurentDifferential_comp_oDerivative_eq (R := ZMod 2)
    (G.stabilizeX s.castSucc (G.X s).castSucc s) P
  have hG := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) G
    (P.preimage s.castSucc.succAbove s.castSucc.succAbove_right_injective.injOn)
  have e := laurentTotalHomologyMapHet_eq_of_isNullHomotopic _ _ (laurentChainHet_comp hA hR)
    (laurentChainHet_comp hR hG)
    (isNullHomotopic_stabilization_projection_colour G s (ZMod 2) P hP)
  have := LinearMap.congr_fun e ξ
  rw [laurentTotalHomologyMapHet_comp_apply hA hR, laurentTotalHomologyMapHet_comp_apply hR hG]
    at this
  exact this

theorem fourMarkNormalizationMap_total_eq (hK : IsFourMarkInsertion G c K)
    (ξ : laurentTotalHomology K (ZMod 2)) :
    laurentTotalHomologyMapHet (fourMarkNormalizationMap G c K)
        (laurentDifferential_comp_fourMarkNormalizationMap hK) ξ =
      laurentTotalHomologyMapHet _ laurentDifferential_comp_fourMarkProjections
        (laurentTotalHomologyMapHet _ (laurentDifferential_comp_fourMarkSwitchDerivative hK) ξ) :=
  laurentTotalHomologyMapHet_comp_apply (laurentDifferential_comp_fourMarkSwitchDerivative hK)
    laurentDifferential_comp_fourMarkProjections
    (laurentDifferential_comp_fourMarkNormalizationMap hK) ξ

theorem fourMarkNormalizationMap_total_apply (hK : IsFourMarkInsertion G c K)
    (ξ : laurentTotalHomology K (ZMod 2)) :
    laurentTotalHomologyMapHet (fourMarkNormalizationMap G c K)
        (laurentDifferential_comp_fourMarkNormalizationMap hK) ξ =
      laurentTotalHomologyMapHet _ laurentDifferential_comp_fourMarkProjections
        (totalODerivative (fourMarkStabTwo G c) {c.castSucc.castSucc}
          (laurentTotalHomologyMap (oSwitchMap (ZMod 2) K c.castSucc.castSucc)
            (laurentDifferential_comp_oSwitchMap (ZMod 2) (castSucc_castSucc_ne_finRotate c)
              (fourMarkStabTwo_O_eq_swapColumns G c hK)) ξ)) := by
  rw [fourMarkNormalizationMap_total_eq hK,
    laurentTotalHomologyMapHet_eq (G := K) (H := fourMarkStabTwo G c),
    laurentTotalHomologyMap_comp_apply (laurentDifferential_comp_oSwitchMap (ZMod 2)
      (castSucc_castSucc_ne_finRotate c) (fourMarkStabTwo_O_eq_swapColumns G c hK))
      (laurentDifferential_comp_oDerivative_eq _ _)]
  rfl

/-- **The removal map factors through the block derivative.** On total homology, the removal
map is the normalization map after the derivative of the two block columns. -/
theorem fourMarkRemovalMap_total_apply (hK : IsFourMarkInsertion G c K)
    (ξ : laurentTotalHomology K (ZMod 2)) :
    laurentTotalHomologyMapHet (fourMarkRemovalMap G c K)
        (laurentDifferential_comp_fourMarkRemovalMap hK) ξ =
      laurentTotalHomologyMapHet (fourMarkNormalizationMap G c K)
        (laurentDifferential_comp_fourMarkNormalizationMap hK)
        (totalODerivative K {c.castSucc.castSucc, finRotate (n + 2) c.castSucc.castSucc} ξ) := by
  have ha := castSucc_castSucc_ne_finRotate c
  have hO := fourMarkStabTwo_O_eq_swapColumns G c hK
  have hF := laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO
  have h1 := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) (fourMarkStabTwo G c)
    {c.castSucc.castSucc}
  have h2 := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) (fourMarkStabTwo G c)
    {finRotate (n + 2) c.castSucc.castSucc}
  have e := laurentTotalHomologyMapHet_comp_apply
    (laurentDifferential_comp_fourMarkDoubleDerivative hK)
    laurentDifferential_comp_fourMarkProjections
    (laurentDifferential_comp_fourMarkRemovalMap hK) ξ
  rw [fourMarkNormalizationMap_total_apply hK]
  refine e.trans (congrArg (laurentTotalHomologyMapHet (fourMarkProjections G c)
    laurentDifferential_comp_fourMarkProjections) ?_)
  change laurentTotalHomologyMap _ (laurentChainHet_comp (laurentChainHet_comp hF h1) h2) ξ = _
  rw [laurentTotalHomologyMap_comp_apply (laurentChainHet_comp hF h1) h2,
    laurentTotalHomologyMap_comp_apply hF h1]
  exact total_oDerivative_pair_switch ha hO ξ

/-- The normalization map carries the total canonical class to the total canonical class. -/
theorem fourMarkNormalizationMap_totalCanonicalClass (hK : IsFourMarkInsertion G c K)
    (hn : 2 ≤ n) :
    laurentTotalHomologyMapHet (fourMarkNormalizationMap G c K)
        (laurentDifferential_comp_fourMarkNormalizationMap hK) (totalCanonicalClass K (by omega)) =
      totalCanonicalClass G hn := by
  have ha := castSucc_castSucc_ne_finRotate c
  have hO := fourMarkStabTwo_O_eq_swapColumns G c hK
  have hn2 : 2 ≤ n + 2 := by omega
  have hrow : (fourMarkStabTwo G c).O c.castSucc.castSucc =
      K.O (finRotate (n + 2) c.castSucc.castSucc) := by
    rw [hO, GridState.swapColumns_apply, Equiv.swap_apply_left]
  have hcan := homologyMap_labelDerivativeSwitch_gridCanonicalClass_anyX hn2 ha hO
    ha hrow
  have h1 := laurentTotalHomologyMap_totalCanonicalClass hn2 _
    (oDerivativeSwitch_mem_maslovPiece ha hO c.castSucc.castSucc)
    (laurentDifferential_comp_oDerivativeSwitch ha hO c.castSucc.castSucc) hcan
  rw [fourMarkNormalizationMap_total_apply hK]
  have e := laurentTotalHomologyMap_comp_apply
    (laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO)
    (laurentDifferential_comp_oDerivative_eq (R := ZMod 2) (fourMarkStabTwo G c)
      {c.castSucc.castSucc}) (laurentDifferential_comp_oDerivativeSwitch ha hO c.castSucc.castSucc)
    (totalCanonicalClass K hn2)
  unfold totalODerivative
  rw [← e, h1]
  have hn1 : 2 ≤ n + 1 := by omega
  have e2 := stabilizationFstProj_totalCanonicalClass (fourMarkStabOne G c) hn1 c.castSucc
  have e1 := stabilizationFstProj_totalCanonicalClass G hn c
  exact (laurentTotalHomologyMapHet_comp_apply
    (laurentDifferential_comp_stabilizationFstProj (fourMarkStabOne G c) c.castSucc)
    (laurentDifferential_comp_stabilizationFstProj G c)
    laurentDifferential_comp_fourMarkProjections _).trans ((congrArg _ e2).trans e1)

end RemovalHomology

/-! ### Colour naturality of the normalization map -/

section Naturality

variable {n : ℕ} {G : GridDiagram n} {c : Fin n} {K : GridDiagram (n + 2)}

/-- The columns of `G` inside the four-mark insertion at the column `c`. -/
def fourMarkEmbedding (c : Fin n) (j : Fin n) : Fin (n + 2) :=
  c.castSucc.succ.succAbove (c.castSucc.succAbove j)

theorem fourMarkEmbedding_injective (c : Fin n) : Function.Injective (fourMarkEmbedding c) :=
  c.castSucc.succ.succAbove_right_injective.comp c.castSucc.succAbove_right_injective

/-- The embedding of the two stabilizations agrees with the embedding of the insertion. -/
theorem succAbove_succAbove_eq_fourMarkEmbedding (c j : Fin n) :
    c.castSucc.castSucc.succAbove (c.castSucc.succAbove j) = fourMarkEmbedding c j := by
  unfold fourMarkEmbedding
  by_cases hj : j.val < c.val
  · have e0 : c.castSucc.succAbove j = j.castSucc :=
      Fin.succAbove_of_castSucc_lt c.castSucc j (by rw [Fin.lt_def]; simpa using hj)
    rw [e0, Fin.succAbove_of_castSucc_lt c.castSucc.castSucc j.castSucc
        (by rw [Fin.lt_def]; simpa using hj),
      Fin.succAbove_of_castSucc_lt c.castSucc.succ j.castSucc (by rw [Fin.lt_def]; simp; omega)]
  · have e0 : c.castSucc.succAbove j = j.succ :=
      Fin.succAbove_of_le_castSucc c.castSucc j (by rw [Fin.le_def]; simp; omega)
    rw [e0, Fin.succAbove_of_le_castSucc c.castSucc.castSucc j.succ
        (by rw [Fin.le_def]; simp; omega),
      Fin.succAbove_of_le_castSucc c.castSucc.succ j.succ (by rw [Fin.le_def]; simp; omega)]

theorem fourMarkProjections_total_apply
    (y : laurentTotalHomology (fourMarkStabTwo G c) (ZMod 2)) :
    laurentTotalHomologyMapHet (fourMarkProjections G c)
        laurentDifferential_comp_fourMarkProjections y =
      laurentTotalHomologyMapHet (stabilizationFstProj G c)
        (laurentDifferential_comp_stabilizationFstProj G c)
        (laurentTotalHomologyMapHet (stabilizationFstProj (fourMarkStabOne G c) c.castSucc)
          (laurentDifferential_comp_stabilizationFstProj (fourMarkStabOne G c) c.castSucc) y) :=
  laurentTotalHomologyMapHet_comp_apply _ _ laurentDifferential_comp_fourMarkProjections y

/-- **Colour naturality of the normalization map.** For a set of columns of `K` containing
neither block column nor the column of the old `X` marking next to the block, the normalization
map intertwines its derivative with the derivative of its preimage in `G`. -/
theorem fourMarkNormalizationMap_totalODerivative (hK : IsFourMarkInsertion G c K)
    (P : Finset (Fin (n + 2))) (h0 : c.castSucc.castSucc ∉ P) (h1 : c.castSucc.succ ∉ P)
    (h2 : c.succ.succ ∉ P) (ξ : laurentTotalHomology K (ZMod 2)) :
    laurentTotalHomologyMapHet (fourMarkNormalizationMap G c K)
        (laurentDifferential_comp_fourMarkNormalizationMap hK) (totalODerivative K P ξ) =
      totalODerivative G (P.preimage (fourMarkEmbedding c) (fourMarkEmbedding_injective c).injOn)
        (laurentTotalHomologyMapHet (fourMarkNormalizationMap G c K)
          (laurentDifferential_comp_fourMarkNormalizationMap hK) ξ) := by
  have ha := castSucc_castSucc_ne_finRotate c
  have hO := fourMarkStabTwo_O_eq_swapColumns G c hK
  have h1' : finRotate (n + 2) c.castSucc.castSucc ∉ P := by
    rwa [finRotate_castSucc_castSucc]
  rw [fourMarkNormalizationMap_total_apply hK, fourMarkNormalizationMap_total_apply hK,
    ← total_oDerivative_switch_of_not_mem ha hO h0 h1' ξ]
  generalize totalODerivative (fourMarkStabTwo G c) {c.castSucc.castSucc}
    (laurentTotalHomologyMap (oSwitchMap (ZMod 2) K c.castSucc.castSucc)
      (laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO) ξ) = y
  rw [fourMarkProjections_total_apply, fourMarkProjections_total_apply]
  have hP2 : c.castSucc.castSucc ∈ P ↔ c.castSucc.succ ∈ P := iff_of_false h0 h1
  have e2 : laurentTotalHomologyMapHet (stabilizationFstProj (fourMarkStabOne G c) c.castSucc)
      (laurentDifferential_comp_stabilizationFstProj (fourMarkStabOne G c) c.castSucc)
      (totalODerivative (fourMarkStabTwo G c) P y) =
      totalODerivative (fourMarkStabOne G c) (P.preimage c.castSucc.castSucc.succAbove
          c.castSucc.castSucc.succAbove_right_injective.injOn)
        (laurentTotalHomologyMapHet (stabilizationFstProj (fourMarkStabOne G c) c.castSucc)
          (laurentDifferential_comp_stabilizationFstProj (fourMarkStabOne G c) c.castSucc) y) :=
    stabilizationFstProj_totalODerivative (fourMarkStabOne G c) c.castSucc P hP2 y
  rw [e2]
  have hP1 : c.castSucc ∈ P.preimage c.castSucc.castSucc.succAbove
        c.castSucc.castSucc.succAbove_right_injective.injOn ↔
      c.succ ∈ P.preimage c.castSucc.castSucc.succAbove
        c.castSucc.castSucc.succAbove_right_injective.injOn := by
    rw [Finset.mem_preimage, Finset.mem_preimage, Fin.succAbove_castSucc_self,
      Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp)]
    exact iff_of_false h1 h2
  erw [stabilizationFstProj_totalODerivative G c _ hP1]
  have hset : (P.preimage c.castSucc.castSucc.succAbove
        c.castSucc.castSucc.succAbove_right_injective.injOn).preimage c.castSucc.succAbove
        c.castSucc.succAbove_right_injective.injOn =
      P.preimage (fourMarkEmbedding c) (fourMarkEmbedding_injective c).injOn := by
    ext j
    simp only [Finset.mem_preimage, succAbove_succAbove_eq_fourMarkEmbedding]
  rw [hset]

end Naturality

end OnLeConjecture.KnotFloer.GridFull
