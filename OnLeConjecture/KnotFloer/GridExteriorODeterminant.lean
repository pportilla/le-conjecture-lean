/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorTotalHomology
public import OnLeConjecture.KnotFloer.GridExteriorOSwitchAnyX
public import OnLeConjecture.KnotFloer.ExteriorIncidencePairingFamily

/-!
# The determinant formula for a sequence of O switches

This file proves equation `determinant-pairing` of Section 4 of the written proof of Statement E
(`statement_E_complete_proof.tex`, Lemma `nativeOSaddleIncidence`) for a sequence of adjacent O
switches, in the total homology of the native Laurent complexes over `ZMod 2`.

Let `G 0, G 1, …, G d` be grid diagrams of size `n ≥ 2`, where `G (e + 1)` is `G e` with the O
markings of the columns `a e` and `a e + 1` exchanged. The X markings are arbitrary. Colour the
O markings of `G 0` by a function on columns. Colours travel with their O markings
(`colourAt`). For colours `c 0, …, c (d - 1)` let `B r e` be the number, modulo two, of the two
O markings exchanged by the `e`-th switch that have colour `c r`. Then
(`oSwitchChain_determinant`)

  `Ψ_{c 0} ⋯ Ψ_{c (d - 1)} F_{d - 1} ⋯ F_0 can(G 0) = det B • can(G d)`

in the total homology of `G d`, where `F_e` is the O-switch map, `Ψ_c` is the colour derivative
of the colour `c`, and `can` denotes the image of the canonical class. When `det B = 1`, for
instance when `B` is the reduced incidence matrix of a rooted forest, the left side is the
nonzero image of the canonical class (`oSwitchChain_determinant_eq_canonical`).

The proof checks the hypotheses of `derivativeProduct_familyProduct_eq_det`:

* the colour-switch relation `Ψ F = F Ψ + b K` on total homology, from the exact chain identity
  `oDerivative_colour_switch` and the homotopy `K_i ≃ K_j` (`labelDetecting_add_labelDetecting`),
* the intertwining `Ψ K = K Ψ` on total homology, from `oDerivative_comp_labelDetecting` and
  `oDerivative_labelDetecting_homotopy`,
* `Ψ can = 0`, from `exists_oDerivative_eq_laurentDifferential`,

and that each detecting map `K` carries the canonical class to the canonical class
(`homologyMap_labelDetecting_gridCanonicalClass_anyX`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp

variable {n : ℕ}

/-! ### The canonical class in total homology -/

/-- The image of the canonical class in the total homology. -/
def totalCanonicalClass (G : GridDiagram n) (hn : 2 ≤ n) : laurentTotalHomology G (ZMod 2) :=
  laurentGradedToTotal G (ZMod 2) 0 (gridCanonicalClass G hn)

theorem totalCanonicalClass_ne_zero (G : GridDiagram n) (hn : 2 ≤ n) :
    totalCanonicalClass G hn ≠ 0 := by
  intro h
  apply gridCanonicalClass_ne_zero G hn
  apply laurentGradedToTotal_injective G (ZMod 2) 0
  rw [map_zero]
  exact h

/-- Every colour derivative annihilates the total canonical class. -/
theorem laurentTotalHomologyMap_oDerivative_totalCanonicalClass (G : GridDiagram n)
    (hn : 2 ≤ n) (P : Finset (Fin n)) :
    laurentTotalHomologyMap (oDerivative (ZMod 2) G P)
      (laurentDifferential_comp_oDerivative_eq G P) (totalCanonicalClass G hn) = 0 := by
  obtain ⟨z, hzpoly, hz⟩ := (mem_polynomialHomologyImage_iff_exists_cycle (ZMod 2) G
    ⟨0, by omega⟩ 0 _).mp (gridCanonicalClass_mem_polynomialImage G hn ⟨0, by omega⟩)
  have hcD := laurentDifferential_laurentMaslovChainEquiv_iCycles G (ZMod 2) 0 z
  rw [totalCanonicalClass, ← hz, laurentGradedToTotal_homologyπ]
  set c : LaurentChain (ZMod 2) n :=
    (laurentMaslovChainEquiv G (ZMod 2) 0 ((laurentMaslovComplex G (ZMod 2)).iCycles 0 z) :
      LaurentChain (ZMod 2) n)
  have hc : c ∈ laurentMaslovPiece G (ZMod 2) 0 :=
    (laurentMaslovChainEquiv G (ZMod 2) 0 ((laurentMaslovComplex G (ZMod 2)).iCycles 0 z)).property
  obtain ⟨w, hw⟩ := exists_oDerivative_eq_laurentDifferential hn P hc hcD hzpoly
  have hΦD : laurentDifferential G (ZMod 2) (oDerivative (ZMod 2) G P c) = 0 := by
    rw [hw]
    exact laurentDifferential_sq_eq_zero G (ZMod 2) w
  rw [laurentTotalHomologyMap_class _ _ c hcD hΦD, laurentTotalClass_eq_zero_iff]
  exact ⟨w, hw⟩

/-- A degree-preserving chain map carrying the canonical class to the canonical class carries the
total canonical class to the total canonical class. -/
theorem laurentTotalHomologyMap_totalCanonicalClass {G H : GridDiagram n} (hn : 2 ≤ n)
    (f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
    (hdeg : ∀ m (c : LaurentChain (ZMod 2) n), c ∈ laurentMaslovPiece G (ZMod 2) m →
      f c ∈ laurentMaslovPiece H (ZMod 2) m)
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    (hcan : homologyMap (laurentMaslovHomOfMap G H f hdeg hf) 0 (gridCanonicalClass G hn) =
      gridCanonicalClass H hn) :
    laurentTotalHomologyMap f hf (totalCanonicalClass G hn) = totalCanonicalClass H hn := by
  rw [totalCanonicalClass, ← laurentGradedToTotal_naturality G H (ZMod 2) f hdeg hf, hcan]
  rfl

/-- The induced map of a finite sum is the sum of the induced maps. -/
theorem laurentTotalHomologyMap_finsetSum {G H : GridDiagram n} {ι : Type*} (s : Finset ι)
    (f : ι → LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
    (hf : ∀ i, laurentDifferential H (ZMod 2) ∘ₗ f i = f i ∘ₗ laurentDifferential G (ZMod 2))
    (hs : laurentDifferential H (ZMod 2) ∘ₗ (∑ i ∈ s, f i) =
      (∑ i ∈ s, f i) ∘ₗ laurentDifferential G (ZMod 2)) :
    laurentTotalHomologyMap (∑ i ∈ s, f i) hs = ∑ i ∈ s, laurentTotalHomologyMap (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact laurentTotalHomologyMap_zero _
  | insert i s hi ih =>
    have hs' : laurentDifferential H (ZMod 2) ∘ₗ (∑ i ∈ s, f i) =
        (∑ i ∈ s, f i) ∘ₗ laurentDifferential G (ZMod 2) := by
      have hf' := fun j => hf j
      simp only [← Module.End.mul_eq_comp] at hf' ⊢
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => hf' j
    simp only [Finset.sum_insert hi]
    rw [laurentTotalHomologyMap_add (f i) (∑ i ∈ s, f i) (hf i) hs', ih hs']

theorem laurentTotalHomologyMap_congr {G H : GridDiagram n}
    {f g : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n}
    (hfg : f = g)
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    (hg : laurentDifferential H (ZMod 2) ∘ₗ g = g ∘ₗ laurentDifferential G (ZMod 2)) :
    laurentTotalHomologyMap f hf = laurentTotalHomologyMap g hg := by
  subst hfg
  rfl

/-! ### Chain-map bookkeeping -/

section Chain

variable {G H K : GridDiagram n}
  {f g : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n}

theorem isChain_comp
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    (hg : laurentDifferential K (ZMod 2) ∘ₗ g = g ∘ₗ laurentDifferential H (ZMod 2)) :
    laurentDifferential K (ZMod 2) ∘ₗ (g ∘ₗ f) = (g ∘ₗ f) ∘ₗ laurentDifferential G (ZMod 2) := by
  rw [← LinearMap.comp_assoc, hg, LinearMap.comp_assoc, hf, LinearMap.comp_assoc]

theorem isChain_add
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    (hg : laurentDifferential H (ZMod 2) ∘ₗ g = g ∘ₗ laurentDifferential G (ZMod 2)) :
    laurentDifferential H (ZMod 2) ∘ₗ (f + g) = (f + g) ∘ₗ laurentDifferential G (ZMod 2) := by
  rw [LinearMap.comp_add, LinearMap.add_comp, hf, hg]

theorem isChain_smul (p : LaurentPolynomial (ZMod 2))
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2)) :
    laurentDifferential H (ZMod 2) ∘ₗ (p • f) = (p • f) ∘ₗ laurentDifferential G (ZMod 2) := by
  rw [LinearMap.comp_smul, LinearMap.smul_comp, hf]

end Chain

/-! ### Sequences of O switches -/

/-- A sequence of `d` adjacent O switches between grid diagrams of size `n`. The grids and
columns after the first `d` steps are not used. -/
structure OSwitchChain (n d : ℕ) where
  /-- The grids `G 0, G 1, …`. -/
  grid : ℕ → GridDiagram n
  /-- The column `a e` of the `e`-th switch, which exchanges the columns `a e` and `a e + 1`. -/
  col : ℕ → Fin n
  ne : ∀ e, e < d → col e ≠ finRotate n (col e)
  O_eq : ∀ e, e < d → (grid (e + 1)).O = (grid e).O.swapColumns (col e) (finRotate n (col e))

namespace OSwitchChain

variable {d : ℕ} (S : OSwitchChain n d) {C : Type*} [DecidableEq C] (colour : Fin n → C)

/-- The exchange of the two columns of the `e`-th switch. -/
abbrev swapAt (e : ℕ) : Equiv.Perm (Fin n) := Equiv.swap (S.col e) (finRotate n (S.col e))

/-- The colours of the O markings of `G e`, indexed by columns: colours travel with markings. -/
def colourAt : ℕ → Fin n → C
  | 0 => colour
  | e + 1 => fun h => colourAt e (S.swapAt e h)

/-- The columns of `G e` whose O marking has colour `c`. -/
def colourSet (e : ℕ) (c : C) : Finset (Fin n) :=
  Finset.univ.filter fun h => S.colourAt colour e h = c

theorem colourSet_succ (e : ℕ) (c : C) :
    S.colourSet colour (e + 1) c = (S.colourSet colour e c).map (S.swapAt e).toEmbedding := by
  ext h
  rw [Finset.mem_map_equiv, Equiv.symm_swap]
  simp only [colourSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- The entry `B c e`: the number, modulo two, of the two O markings exchanged by the `e`-th
switch that have colour `c`. -/
def incidence (c : C) (e : ℕ) : LaurentPolynomial (ZMod 2) :=
  (if S.colourAt colour e (S.col e) = c then 1 else 0) +
    if S.colourAt colour e (finRotate n (S.col e)) = c then 1 else 0

/-- The colour derivative on the total homology of `G e`. -/
def derivTH (e : ℕ) (c : C) :
    laurentTotalHomology (S.grid e) (ZMod 2) →ₗ[LaurentPolynomial (ZMod 2)]
      laurentTotalHomology (S.grid e) (ZMod 2) :=
  laurentTotalHomologyMap (oDerivative (ZMod 2) (S.grid e) (S.colourSet colour e c))
    (laurentDifferential_comp_oDerivative_eq _ _)

/-- The O-switch map on total homology, zero after the first `d` steps. -/
def switchTH (e : ℕ) :
    laurentTotalHomology (S.grid e) (ZMod 2) →ₗ[LaurentPolynomial (ZMod 2)]
      laurentTotalHomology (S.grid (e + 1)) (ZMod 2) :=
  if h : e < d then
    laurentTotalHomologyMap (oSwitchMap (ZMod 2) (S.grid e) (S.col e))
      (laurentDifferential_comp_oSwitchMap (ZMod 2) (S.ne e h) (S.O_eq e h))
  else 0

/-- The detecting map on total homology, zero after the first `d` steps. -/
def detectTH (e : ℕ) :
    laurentTotalHomology (S.grid e) (ZMod 2) →ₗ[LaurentPolynomial (ZMod 2)]
      laurentTotalHomology (S.grid (e + 1)) (ZMod 2) :=
  if h : e < d then
    laurentTotalHomologyMap
      (labelDetecting (ZMod 2) (S.grid e) (S.grid (e + 1)) (S.col e) (S.col e)
        (finRotate n (S.col e)))
      (laurentDifferential_comp_labelDetecting (S.ne e h) (S.O_eq e h) _ _)
  else 0

end OSwitchChain

/-! ### The colour-switch and intertwining relations on total homology -/

section Relations

variable {G H : GridDiagram n} {a : Fin n}

/-- In a module over a ring of characteristic two, `x + x = 0`. -/
theorem endo_add_self'
    (f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n) :
    f + f = 0 := by
  have h2 : (2 : LaurentPolynomial (ZMod 2)) = 0 := CharTwo.two_eq_zero
  rw [← two_smul (LaurentPolynomial (ZMod 2)) f, h2, zero_smul]

/-- The chain-level form of the colour-switch relation with its homotopy. -/
theorem colour_switch_homotopy (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (P : Finset (Fin n)) :
    oDerivative (ZMod 2) H (P.map (Equiv.swap a (finRotate n a)).toEmbedding) ∘ₗ
          oSwitchMap (ZMod 2) G a +
        (oSwitchMap (ZMod 2) G a ∘ₗ oDerivative (ZMod 2) G P +
          ((if a ∈ P then 1 else 0) + if finRotate n a ∈ P then 1 else 0 :
            LaurentPolynomial (ZMod 2)) • labelDetecting (ZMod 2) G H a a (finRotate n a)) +
        (laurentDifferential H (ZMod 2) ∘ₗ ((if finRotate n a ∈ P then 1 else 0 :
            LaurentPolynomial (ZMod 2)) • oSwitchIndicatorMap (ZMod 2) G a) +
          ((if finRotate n a ∈ P then 1 else 0 : LaurentPolynomial (ZMod 2)) •
            oSwitchIndicatorMap (ZMod 2) G a) ∘ₗ laurentDifferential G (ZMod 2)) = 0 := by
  have hcs := oDerivative_colour_switch (R := ZMod 2) ha hO P
  have hlab := labelDetecting_add_labelDetecting (R := ZMod 2) ha hO
  generalize oDerivative (ZMod 2) H (P.map (Equiv.swap a (finRotate n a)).toEmbedding) ∘ₗ
    oSwitchMap (ZMod 2) G a = A at hcs ⊢
  generalize oSwitchMap (ZMod 2) G a ∘ₗ oDerivative (ZMod 2) G P = B at hcs ⊢
  generalize labelDetecting (ZMod 2) G H a a (finRotate n a) = Ki at hcs hlab ⊢
  generalize labelDetecting (ZMod 2) G H a (finRotate n a) a = Kj at hcs hlab ⊢
  rw [LinearMap.comp_smul, LinearMap.smul_comp, ← smul_add]
  generalize laurentDifferential H (ZMod 2) ∘ₗ oSwitchIndicatorMap (ZMod 2) G a +
    oSwitchIndicatorMap (ZMod 2) G a ∘ₗ laurentDifferential G (ZMod 2) = E at hlab ⊢
  have hE : E = Ki + Kj := by
    have := congrArg (· + (Ki + Kj)) hlab
    simp only [zero_add] at this
    rw [← this]
    calc E = E + 0 := (add_zero _).symm
      _ = E + ((Ki + Kj) + (Ki + Kj)) := by rw [endo_add_self']
      _ = Ki + Kj + E + (Ki + Kj) := by abel
  rw [hE]
  have hA : A = (A + B) + B := by rw [add_assoc, endo_add_self', add_zero]
  rw [hA, hcs]
  have h2x : ∀ x : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n,
      (2 : ℤ) • x = 0 := fun x => by rw [two_zsmul]; exact endo_add_self' x
  have h11 : (1 + 1 : LaurentPolynomial (ZMod 2)) = 0 := CharTwo.add_self_eq_zero 1
  by_cases h1 : a ∈ P <;> by_cases h2 : finRotate n a ∈ P <;>
    simp only [h1, h2, if_true, if_false, add_zero, zero_add, one_smul, zero_smul, h11] <;>
    abel_nf <;> simp only [h2x, add_zero]

/-- The colour-switch relation `Ψ F = F Ψ + b K` on total homology. -/
theorem laurentTotalHomologyMap_colour_switch (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (P P' : Finset (Fin n))
    (hP' : P' = P.map (Equiv.swap a (finRotate n a)).toEmbedding) (b : LaurentPolynomial (ZMod 2))
    (hb : b = (if a ∈ P then 1 else 0) + if finRotate n a ∈ P then 1 else 0) :
    laurentTotalHomologyMap (oDerivative (ZMod 2) H P')
        (laurentDifferential_comp_oDerivative_eq _ _) ∘ₗ
      laurentTotalHomologyMap (oSwitchMap (ZMod 2) G a)
        (laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO) =
      laurentTotalHomologyMap (oSwitchMap (ZMod 2) G a)
          (laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO) ∘ₗ
        laurentTotalHomologyMap (oDerivative (ZMod 2) G P)
          (laurentDifferential_comp_oDerivative_eq _ _) +
      b • laurentTotalHomologyMap (labelDetecting (ZMod 2) G H a a (finRotate n a))
          (laurentDifferential_comp_labelDetecting ha hO _ _) := by
  subst hP' hb
  have hF := laurentDifferential_comp_oSwitchMap (ZMod 2) ha hO
  have hΦH := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) H
    (P.map (Equiv.swap a (finRotate n a)).toEmbedding)
  have hΦG := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) G P
  have hKi := laurentDifferential_comp_labelDetecting (R := ZMod 2) ha hO a (finRotate n a)
  rw [← laurentTotalHomologyMap_comp _ _ hF hΦH (isChain_comp hF hΦH),
    ← laurentTotalHomologyMap_comp _ _ hΦG hF (isChain_comp hΦG hF),
    ← laurentTotalHomologyMap_smul _ _ hKi (isChain_smul _ hKi),
    ← laurentTotalHomologyMap_add _ _ (isChain_comp hΦG hF) (isChain_smul _ hKi)
      (isChain_add (isChain_comp hΦG hF) (isChain_smul _ hKi))]
  exact laurentTotalHomologyMap_eq_of_homotopy _ _ _ _ _ (colour_switch_homotopy ha hO P)

/-- The colour derivatives commute with the detecting map on total homology. -/
theorem laurentTotalHomologyMap_colour_detecting (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (P P' : Finset (Fin n))
    (hP' : P' = P.map (Equiv.swap a (finRotate n a)).toEmbedding) :
    laurentTotalHomologyMap (oDerivative (ZMod 2) H P')
        (laurentDifferential_comp_oDerivative_eq _ _) ∘ₗ
      laurentTotalHomologyMap (labelDetecting (ZMod 2) G H a a (finRotate n a))
        (laurentDifferential_comp_labelDetecting ha hO _ _) =
      laurentTotalHomologyMap (labelDetecting (ZMod 2) G H a a (finRotate n a))
          (laurentDifferential_comp_labelDetecting ha hO _ _) ∘ₗ
        laurentTotalHomologyMap (oDerivative (ZMod 2) G P)
          (laurentDifferential_comp_oDerivative_eq _ _) := by
  classical
  subst hP'
  have hKi := laurentDifferential_comp_labelDetecting (R := ZMod 2) ha hO a (finRotate n a)
  have hKj := laurentDifferential_comp_labelDetecting (R := ZMod 2) ha hO (finRotate n a) a
  have hij : laurentTotalHomologyMap _ hKi = laurentTotalHomologyMap _ hKj :=
    laurentTotalHomologyMap_eq_of_homotopy _ _ hKi hKj (oSwitchIndicatorMap (ZMod 2) G a)
      (labelDetecting_add_labelDetecting (R := ZMod 2) ha hO)
  have hΦ : ∀ (K' : GridDiagram n) (h' : Fin n), laurentDifferential K' (ZMod 2) ∘ₗ
      oDerivative (ZMod 2) K' {h'} = oDerivative (ZMod 2) K' {h'} ∘ₗ
        laurentDifferential K' (ZMod 2) := fun K' h' =>
    laurentDifferential_comp_oDerivative_eq _ _
  have hcol : ∀ h' : Fin n,
      laurentTotalHomologyMap (oDerivative (ZMod 2) H {Equiv.swap a (finRotate n a) h'} ∘ₗ
          labelDetecting (ZMod 2) G H a a (finRotate n a)) (isChain_comp hKi (hΦ H _)) =
        laurentTotalHomologyMap (labelDetecting (ZMod 2) G H a a (finRotate n a) ∘ₗ
          oDerivative (ZMod 2) G {h'}) (isChain_comp (hΦ G h') hKi) := by
    intro h'
    by_cases h1 : h' = a
    · subst h1
      apply laurentTotalHomologyMap_congr
      rw [Equiv.swap_apply_left]
      exact oDerivative_comp_labelDetecting G H _ _ _
    · by_cases h2 : h' = finRotate n a
      · subst h2
        have hsw : Equiv.swap a (finRotate n a) (finRotate n a) = a := Equiv.swap_apply_right _ _
        rw [laurentTotalHomologyMap_congr (show oDerivative (ZMod 2) H
            {Equiv.swap a (finRotate n a) (finRotate n a)} ∘ₗ
              labelDetecting (ZMod 2) G H a a (finRotate n a) =
            oDerivative (ZMod 2) H {a} ∘ₗ labelDetecting (ZMod 2) G H a a (finRotate n a)
              by rw [hsw]) _ (isChain_comp hKi (hΦ H a)),
          laurentTotalHomologyMap_comp _ _ hKi (hΦ H a),
          laurentTotalHomologyMap_comp _ _ (hΦ G _) hKi, hij,
          ← laurentTotalHomologyMap_comp _ _ hKj (hΦ H a) (isChain_comp hKj (hΦ H a)),
          ← laurentTotalHomologyMap_comp _ _ (hΦ G _) hKj (isChain_comp (hΦ G _) hKj)]
        exact laurentTotalHomologyMap_congr (oDerivative_comp_labelDetecting G H _ _ _) _ _
      · rw [laurentTotalHomologyMap_congr (show oDerivative (ZMod 2) H
            {Equiv.swap a (finRotate n a) h'} ∘ₗ labelDetecting (ZMod 2) G H a a (finRotate n a) =
            oDerivative (ZMod 2) H {h'} ∘ₗ labelDetecting (ZMod 2) G H a a (finRotate n a)
              by rw [Equiv.swap_apply_of_ne_of_ne h1 h2]) _ (isChain_comp hKi (hΦ H h'))]
        exact laurentTotalHomologyMap_eq_of_homotopy _ _ _ _ _
          (oDerivative_labelDetecting_homotopy (R := ZMod 2) ha hO
            (oSwitch_O_of_ne hO h1 h2) h2 h1)
  have hsumH : oDerivative (ZMod 2) H (P.map (Equiv.swap a (finRotate n a)).toEmbedding) ∘ₗ
        labelDetecting (ZMod 2) G H a a (finRotate n a) =
      ∑ h' ∈ P, oDerivative (ZMod 2) H {Equiv.swap a (finRotate n a) h'} ∘ₗ
        labelDetecting (ZMod 2) G H a a (finRotate n a) := by
    rw [oDerivative_eq_sum, Finset.sum_map]
    simp only [← Module.End.mul_eq_comp, Finset.sum_mul]
    rfl
  have hsumG : labelDetecting (ZMod 2) G H a a (finRotate n a) ∘ₗ oDerivative (ZMod 2) G P =
      ∑ h' ∈ P, labelDetecting (ZMod 2) G H a a (finRotate n a) ∘ₗ
        oDerivative (ZMod 2) G {h'} := by
    rw [oDerivative_eq_sum]
    simp only [← Module.End.mul_eq_comp, Finset.mul_sum]
  rw [← laurentTotalHomologyMap_comp _ _ hKi (laurentDifferential_comp_oDerivative_eq _ _)
      (isChain_comp hKi (laurentDifferential_comp_oDerivative_eq _ _)),
    ← laurentTotalHomologyMap_comp _ _ (laurentDifferential_comp_oDerivative_eq _ _) hKi
      (isChain_comp (laurentDifferential_comp_oDerivative_eq _ _) hKi),
    laurentTotalHomologyMap_congr hsumH _ (hsumH ▸ isChain_comp hKi
      (laurentDifferential_comp_oDerivative_eq _ _)),
    laurentTotalHomologyMap_congr hsumG _ (hsumG ▸ isChain_comp
      (laurentDifferential_comp_oDerivative_eq _ _) hKi),
    laurentTotalHomologyMap_finsetSum P _ (fun h' => isChain_comp hKi (hΦ H _)),
    laurentTotalHomologyMap_finsetSum P _ (fun h' => isChain_comp (hΦ G h') hKi)]
  exact Finset.sum_congr rfl fun h' _ => hcol h'

end Relations

/-! ### The three hypotheses of the determinant formula -/

namespace OSwitchChain

variable {d : ℕ} (S : OSwitchChain n d) {C : Type*} [DecidableEq C] (colour : Fin n → C)

/-- The colour-switch relation on total homology: `Ψ F = F Ψ + b K`. -/
theorem derivTH_comp_switchTH (c : C) (e : ℕ) :
    S.derivTH colour (e + 1) c ∘ₗ S.switchTH e =
      S.switchTH e ∘ₗ S.derivTH colour e c + S.incidence colour c e • S.detectTH e := by
  by_cases h : e < d
  · have hb : S.incidence colour c e =
        (if S.col e ∈ S.colourSet colour e c then 1 else 0) +
          if finRotate n (S.col e) ∈ S.colourSet colour e c then 1 else 0 := by
      simp only [incidence, colourSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [switchTH, detectTH, dif_pos h, dif_pos h, derivTH, derivTH]
    exact laurentTotalHomologyMap_colour_switch (S.ne e h) (S.O_eq e h) _ _
      (S.colourSet_succ colour e c) _ hb
  · rw [switchTH, detectTH, dif_neg h, dif_neg h]
    simp

/-- The colour derivatives commute with the detecting maps on total homology. -/
theorem derivTH_comp_detectTH (c : C) (e : ℕ) :
    S.derivTH colour (e + 1) c ∘ₗ S.detectTH e = S.detectTH e ∘ₗ S.derivTH colour e c := by
  by_cases h : e < d
  · rw [detectTH, dif_pos h, derivTH, derivTH]
    exact laurentTotalHomologyMap_colour_detecting (S.ne e h) (S.O_eq e h) _ _
      (S.colourSet_succ colour e c)
  · rw [detectTH, dif_neg h]
    simp

/-- The colour derivatives annihilate the total canonical class of `G 0`. -/
theorem derivTH_totalCanonicalClass (hn : 2 ≤ n) (c : C) :
    S.derivTH colour 0 c (totalCanonicalClass (S.grid 0) hn) = 0 :=
  laurentTotalHomologyMap_oDerivative_totalCanonicalClass _ hn _

/-- The detecting maps carry the total canonical class along the sequence. -/
theorem familyProduct_detectTH (hn : 2 ≤ n) (e : ℕ) (he : e ≤ d) :
    familyProduct S.detectTH e (totalCanonicalClass (S.grid 0) hn) =
      totalCanonicalClass (S.grid e) hn := by
  induction e with
  | zero => rfl
  | succ e ih =>
    have h : e < d := by omega
    rw [familyProduct_succ, LinearMap.comp_apply, ih (by omega), detectTH, dif_pos h]
    exact laurentTotalHomologyMap_totalCanonicalClass hn _
      (labelDetecting_mem_maslovPiece (S.ne e h) (S.O_eq e h) _ _) _
      (homologyMap_labelDetecting_gridCanonicalClass_anyX hn (S.ne e h) (S.O_eq e h)
        (S.ne e h).symm (oSwitchLabel_left (S.O_eq e h)))

/-- **The determinant formula for a sequence of O switches.** -/
theorem oSwitchChain_determinant (hn : 2 ≤ n) (cs : Fin d → C) :
    derivativeProduct (S.derivTH colour d) cs
        (familyProduct S.switchTH d (totalCanonicalClass (S.grid 0) hn)) =
      (Matrix.of fun r e : Fin d => S.incidence colour (cs r) e).det •
        totalCanonicalClass (S.grid d) hn := by
  rw [derivativeProduct_familyProduct_eq_det (V := fun e =>
      laurentTotalHomology (S.grid e) (ZMod 2)) S.switchTH S.detectTH
      (fun e c => S.derivTH colour e c) (S.incidence colour)
      (totalCanonicalClass (S.grid 0) hn) (S.derivTH_comp_switchTH colour)
      (S.derivTH_comp_detectTH colour) (S.derivTH_totalCanonicalClass colour hn) cs,
    S.familyProduct_detectTH hn d le_rfl]

/-- If the incidence matrix has determinant one, the product of the colour derivatives and the
O switches sends the canonical class of `G 0` to the canonical class of `G d`. -/
theorem oSwitchChain_determinant_eq_canonical (hn : 2 ≤ n) (cs : Fin d → C)
    (hdet : (Matrix.of fun r e : Fin d => S.incidence colour (cs r) e).det = 1) :
    derivativeProduct (S.derivTH colour d) cs
        (familyProduct S.switchTH d (totalCanonicalClass (S.grid 0) hn)) =
      totalCanonicalClass (S.grid d) hn := by
  rw [S.oSwitchChain_determinant colour hn cs, hdet, one_smul]

end OSwitchChain

end OnLeConjecture.KnotFloer.GridFull
