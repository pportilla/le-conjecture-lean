/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorColourTransport
public import OnLeConjecture.KnotFloer.GridMovesToCanonicalMap

/-!
# Colour transport along grid moves: the general framework

This file prepares the proof of `ColourMovesToStatement` (`GridExteriorColourTransport`).

`ColourTransportData G χ H χ'` strengthens `ColourCanonicalTransport G χ H χ'` by the requirement
that the underlying Laurent map `f` commutes with the full Laurent differentials. With this
requirement the data compose (`ColourTransportData.trans`): the colour defect of a composite
`g f` is `g (f Φ - Φ' f) + (g Φ' - Φ'' g) f`, and composition with chain maps preserves
null-homotopy.

`ColourPullback G H` states that every component colouring `χ'` of `H` comes from a component
colouring `χ` of `G` with the same colour values, exact exactly when `χ'` is exact, together with
`ColourTransportData G χ H χ'`. Weakening `ColourTransportData` to `ColourCanonicalTransport`
gives the conclusion of `ColourMovesToStatement` for the pair `G`, `H`
(`ColourPullback.colourCanonicalTransport`). Colour pullbacks compose (`ColourPullback.trans`).

The colour bookkeeping of a move is recorded by a *component map* (`ComponentMap G H p`), a local
notion of this file: a surjection `p` from the columns of `H` to the columns of `G` such that two
columns of `H` lie on the same component of `H` exactly when their images lie on the same
component of `G`. The components are the cycles of `gridComponentPerm`. Every component colouring
of `H` then factors through `p` (`ComponentMap.eq_comp_surjInv`), and composing with `p` preserves
component colourings, exactness and colour values. Consequently a component map together with
colour transport data from every component colouring `χ` of `G` to `χ ∘ p` gives a colour pullback
from `G` to `H` (`ColourPullback.of_componentMap`), and colour transport data from `χ ∘ p` to `χ`
give a colour pullback from `H` to `G` (`ColourPullback.of_componentMap_symm`).

Finally, a native isomorphism whose underlying Laurent equivalence commutes with the
differentials and carries the derivative maps `Φ_P` to `Φ_{σ P}` for a permutation `σ` of the
columns gives colour transport data in both directions (`colourTransportData_of_iso`,
`colourTransportData_of_iso_inv`).
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable {n m k : ℕ}

/-! ### Component colourings and cycles -/

/-- A colouring is a component colouring exactly when it is constant on the cycles of
`gridComponentPerm G`. -/
theorem componentColouring_iff (G : GridDiagram n) (χ : Fin n → ℕ) :
    ComponentColouring G χ ↔ ∀ c d, (gridComponentPerm G).SameCycle c d → χ c = χ d := by
  constructor
  · intro h c d hcd
    obtain ⟨i, rfl⟩ := hcd.exists_nat_pow_eq
    clear hcd
    induction i with
    | zero => rfl
    | succ i ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, h]
        exact ih
  · intro h c
    exact (h c _ ⟨1, by simp⟩).symm

/-- The colour class of `χ ∘ σ.symm` is the image of the colour class of `χ` under `σ`. -/
theorem colourClass_comp_symm (χ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (v : ℕ) :
    colourClass (χ ∘ σ.symm) v = (colourClass χ v).map σ.toEmbedding := by
  ext x
  simp [colourClass, Finset.mem_map_equiv]

/-- The preimage of a colour class under a map of columns is the colour class of the composite
colouring. -/
theorem colourClass_preimage (χ : Fin k → ℕ) (e : Fin n → Fin k) (he : Function.Injective e)
    (v : ℕ) : (colourClass χ v).preimage e he.injOn = colourClass (χ ∘ e) v := by
  ext x
  simp [colourClass]

/-- A component map from `H` to `G`: a surjection `p` from the columns of `H` onto the columns of
`G` such that two columns of `H` lie on the same component exactly when their images under `p`
lie on the same component of `G`. -/
def ComponentMap (G : GridDiagram n) (H : GridDiagram k) (p : Fin k → Fin n) : Prop :=
  Function.Surjective p ∧
    ∀ x y, (gridComponentPerm H).SameCycle x y ↔ (gridComponentPerm G).SameCycle (p x) (p y)

namespace ComponentMap

variable {G : GridDiagram n} {H : GridDiagram k} {p : Fin k → Fin n}

/-- The identity of the columns is a component map from a grid to itself. -/
theorem id (G : GridDiagram n) : ComponentMap G G _root_.id :=
  ⟨Function.surjective_id, fun _ _ => Iff.rfl⟩

/-- Composing a component colouring of `G` with a component map gives a component colouring of
`H`. -/
theorem componentColouring_comp (hp : ComponentMap G H p) {χ : Fin n → ℕ}
    (hχ : ComponentColouring G χ) : ComponentColouring H (χ ∘ p) := by
  rw [componentColouring_iff] at hχ ⊢
  intro x y hxy
  exact hχ _ _ ((hp.2 x y).mp hxy)

/-- If `χ ∘ p` is a component colouring of `H`, then `χ` is a component colouring of `G`. -/
theorem componentColouring_of_comp (hp : ComponentMap G H p) {χ : Fin n → ℕ}
    (hχ : ComponentColouring H (χ ∘ p)) : ComponentColouring G χ := by
  rw [componentColouring_iff] at hχ ⊢
  intro c d hcd
  obtain ⟨x, rfl⟩ := hp.1 c
  obtain ⟨y, rfl⟩ := hp.1 d
  exact hχ x y ((hp.2 x y).mpr hcd)

/-- The colouring `χ ∘ p` of `H` is exact exactly when `χ` is exact. -/
theorem exactColouring_comp_iff (hp : ComponentMap G H p) (χ : Fin n → ℕ) :
    ExactColouring H (χ ∘ p) ↔ ExactColouring G χ := by
  constructor
  · intro h c d
    obtain ⟨x, rfl⟩ := hp.1 c
    obtain ⟨y, rfl⟩ := hp.1 d
    exact (h x y).trans (hp.2 x y)
  · intro h x y
    exact (h (p x) (p y)).trans (hp.2 x y).symm

/-- The colourings `χ ∘ p` and `χ` take the same values. -/
theorem exists_comp_eq_iff (hp : ComponentMap G H p) (χ : Fin n → ℕ) (v : ℕ) :
    (∃ x, (χ ∘ p) x = v) ↔ ∃ c, χ c = v :=
  ⟨fun ⟨x, hx⟩ => ⟨p x, hx⟩, fun ⟨c, hc⟩ => by
    obtain ⟨x, rfl⟩ := hp.1 c
    exact ⟨x, hc⟩⟩

/-- Every component colouring of `H` factors through a component map. -/
theorem eq_comp_surjInv (hp : ComponentMap G H p) {χ' : Fin k → ℕ}
    (hχ' : ComponentColouring H χ') : χ' = (χ' ∘ Function.surjInv hp.1) ∘ p := by
  funext x
  rw [componentColouring_iff] at hχ'
  refine hχ' _ _ ((hp.2 _ _).mpr ?_)
  rw [Function.surjInv_eq hp.1]

end ComponentMap

/-- A permutation `σ` of the columns with `gridComponentPerm H = σ * gridComponentPerm G * σ⁻¹`
gives the component map `σ.symm` from `H` to `G`. -/
theorem ComponentMap.of_conj {G H : GridDiagram n} (σ : Equiv.Perm (Fin n))
    (h : gridComponentPerm H = σ * gridComponentPerm G * σ⁻¹) : ComponentMap G H σ.symm := by
  refine ⟨σ.symm.surjective, fun x y => ?_⟩
  rw [h, Equiv.Perm.sameCycle_conj]
  rfl

/-- A permutation `σ` of the columns with
`gridComponentPerm H = σ * (gridComponentPerm G)⁻¹ * σ⁻¹` gives the component map `σ.symm` from
`H` to `G`. -/
theorem ComponentMap.of_conj_inv {G H : GridDiagram n} (σ : Equiv.Perm (Fin n))
    (h : gridComponentPerm H = σ * (gridComponentPerm G)⁻¹ * σ⁻¹) :
    ComponentMap G H σ.symm := by
  refine ⟨σ.symm.surjective, fun x y => ?_⟩
  rw [h, Equiv.Perm.sameCycle_conj, Equiv.Perm.sameCycle_inv]
  rfl

/-! ### Colour transport data -/

/-- The colour-natural canonical map data of `ColourCanonicalTransport G χ H χ'`, together with
the requirement that the underlying Laurent map `f` commutes with the full Laurent
differentials. -/
def ColourTransportData (G : GridDiagram n) (χ : Fin n → ℕ) (H : GridDiagram k)
    (χ' : Fin k → ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) (hk : 2 ≤ k),
    ∃ (φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2))
      (f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) k),
      (∀ (m : ℤ) (x : (laurentMaslovComplex G (ZMod 2)).X m),
        (laurentMaslovChainEquiv H (ZMod 2) m (φ.f m x) : LaurentChain (ZMod 2) k) =
          f (laurentMaslovChainEquiv G (ZMod 2) m x)) ∧
      laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2) ∧
      (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2)) φ 0 0 ∧
      homologyMap φ 0 (gridCanonicalClass G hn) = gridCanonicalClass H hk ∧
      ∀ v : ℕ, IsNullHomotopic (laurentDifferential G (ZMod 2)) (laurentDifferential H (ZMod 2))
        (f ∘ₗ oDerivative (ZMod 2) G (colourClass χ v) -
          oDerivative (ZMod 2) H (colourClass χ' v) ∘ₗ f)

namespace ColourTransportData

/-- Colour transport data give a colour-natural canonical map. -/
theorem colourCanonicalTransport {G : GridDiagram n} {χ : Fin n → ℕ} {H : GridDiagram k}
    {χ' : Fin k → ℕ} (h : ColourTransportData G χ H χ') : ColourCanonicalTransport G χ H χ' := by
  intro hn hk
  obtain ⟨φ, f, hf, -, hφ, hξ, hv⟩ := h hn hk
  exact ⟨φ, f, hf, hφ, hξ, hv⟩

/-- The identity map gives colour transport data from a colouring to itself. -/
theorem refl (G : GridDiagram n) (χ : Fin n → ℕ) : ColourTransportData G χ G χ := by
  intro hn _
  refine ⟨𝟙 _, LinearMap.id, fun _ _ => rfl, by rw [LinearMap.id_comp, LinearMap.comp_id], ?_,
    ?_, fun v => .of_eq_zero (by rw [LinearMap.id_comp, LinearMap.comp_id, sub_self])⟩
  · intro a b i x hx
    rw [add_zero, add_zero]
    exact hx
  · rw [homologyMap_id, CategoryTheory.id_apply]

/-- Colour transport data compose. The intermediate grid must have size at least two whenever the
source grid has. -/
theorem trans {G : GridDiagram n} {χ : Fin n → ℕ} {H : GridDiagram m} {χ' : Fin m → ℕ}
    {K : GridDiagram k} {χ'' : Fin k → ℕ} (h₁ : ColourTransportData G χ H χ')
    (h₂ : ColourTransportData H χ' K χ'') (hm : 2 ≤ n → 2 ≤ m) :
    ColourTransportData G χ K χ'' := by
  intro hn hk
  obtain ⟨φ, f, hf, hfd, hφ, hφξ, hfv⟩ := h₁ hn (hm hn)
  obtain ⟨ψ, g, hg, hgd, hψ, hψξ, hgv⟩ := h₂ (hm hn) hk
  refine ⟨φ ≫ ψ, g ∘ₗ f, fun i x => ?_, ?_, ?_, ?_, fun v => ?_⟩
  · rw [HomologicalComplex.comp_f, CategoryTheory.comp_apply, hg, hf]
    rfl
  · rw [← LinearMap.comp_assoc, hgd, LinearMap.comp_assoc, hfd, LinearMap.comp_assoc]
  · simpa only [add_zero] using hφ.comp hψ
  · rw [homologyMap_comp, CategoryTheory.comp_apply, hφξ, hψξ]
  · have A := (hfv v).comp_left (g := g) hgd.symm
    have B := (hgv v).comp_right (g := f) hfd
    convert A.add B using 1
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, map_sub]
    abel

end ColourTransportData

/-! ### Colour pullbacks -/

/-- Every component colouring of `H` comes from a component colouring of `G` with the same colour
values, exact exactly when it is exact, together with colour transport data from `G` to `H`. -/
def ColourPullback (G : GridDiagram n) (H : GridDiagram k) : Prop :=
  ∀ χ' : Fin k → ℕ, ComponentColouring H χ' →
    ∃ χ : Fin n → ℕ, ComponentColouring G χ ∧ (ExactColouring G χ ↔ ExactColouring H χ') ∧
      (∀ v, (∃ c, χ c = v) ↔ ∃ c, χ' c = v) ∧ ColourTransportData G χ H χ'

namespace ColourPullback

/-- Every grid admits the identity colour pullback to itself. -/
theorem refl (G : GridDiagram n) : ColourPullback G G :=
  fun χ hχ => ⟨χ, hχ, Iff.rfl, fun _ => Iff.rfl, .refl G χ⟩

/-- Colour pullbacks compose. The intermediate grid must have size at least two whenever the
source grid has. -/
theorem trans {G : GridDiagram n} {H : GridDiagram m} {K : GridDiagram k}
    (h₁ : ColourPullback G H) (h₂ : ColourPullback H K) (hm : 2 ≤ n → 2 ≤ m) :
    ColourPullback G K := by
  intro χ'' hχ''
  obtain ⟨χ', hχ', hex', hval', hT'⟩ := h₂ χ'' hχ''
  obtain ⟨χ, hχ, hex, hval, hT⟩ := h₁ χ' hχ'
  exact ⟨χ, hχ, hex.trans hex', fun v => (hval v).trans (hval' v), hT.trans hT' hm⟩

/-- Colour pullbacks between grids of one size compose. -/
theorem trans_of_size_eq {G H K : GridDiagram n} (h₁ : ColourPullback G H)
    (h₂ : ColourPullback H K) : ColourPullback G K :=
  h₁.trans h₂ _root_.id

/-- A component map from `H` to `G` and colour transport data from every component colouring `χ`
of `G` to `χ ∘ p` give a colour pullback from `G` to `H`. -/
theorem of_componentMap {G : GridDiagram n} {H : GridDiagram k} {p : Fin k → Fin n}
    (hp : ComponentMap G H p)
    (hT : ∀ χ : Fin n → ℕ, ComponentColouring G χ → ColourTransportData G χ H (χ ∘ p)) :
    ColourPullback G H := by
  intro χ' hχ'
  obtain ⟨χ, rfl⟩ : ∃ χ : Fin n → ℕ, χ' = χ ∘ p := ⟨_, hp.eq_comp_surjInv hχ'⟩
  have hχ := hp.componentColouring_of_comp hχ'
  exact ⟨χ, hχ, (hp.exactColouring_comp_iff χ).symm, fun v => (hp.exists_comp_eq_iff χ v).symm,
    hT χ hχ⟩

/-- A component map from `H` to `G` and colour transport data from `χ ∘ p` to every component
colouring `χ` of `G` give a colour pullback from `H` to `G`. -/
theorem of_componentMap_symm {G : GridDiagram n} {H : GridDiagram k} {p : Fin k → Fin n}
    (hp : ComponentMap G H p)
    (hT : ∀ χ : Fin n → ℕ, ComponentColouring G χ → ColourTransportData H (χ ∘ p) G χ) :
    ColourPullback H G := fun χ hχ =>
  ⟨χ ∘ p, hp.componentColouring_comp hχ, hp.exactColouring_comp_iff χ, hp.exists_comp_eq_iff χ,
    hT χ hχ⟩

/-- A colour pullback gives the conclusion of `ColourMovesToStatement` for one pair of grids. -/
theorem colourCanonicalTransport {G : GridDiagram n} {H : GridDiagram k}
    (h : ColourPullback G H) (χ' : Fin k → ℕ) (hχ' : ComponentColouring H χ') :
    ∃ χ : Fin n → ℕ, ComponentColouring G χ ∧ (ExactColouring G χ ↔ ExactColouring H χ') ∧
      (∀ v, (∃ c, χ c = v) ↔ ∃ c, χ' c = v) ∧ ColourCanonicalTransport G χ H χ' := by
  obtain ⟨χ, hχ, hex, hval, hT⟩ := h χ' hχ'
  exact ⟨χ, hχ, hex, hval, hT.colourCanonicalTransport⟩

end ColourPullback

/-! ### Isomorphisms that relabel the columns -/

section Iso

variable {G H : GridDiagram n}
  (e : laurentMaslovComplex G (ZMod 2) ≅ laurentMaslovComplex H (ZMod 2))
  (L : LaurentChain (ZMod 2) n ≃ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
  (σ : Equiv.Perm (Fin n))

/-- A native isomorphism whose underlying Laurent equivalence `L` commutes with the differentials
and carries `Φ^G_P` to `Φ^H_{σ P}` gives colour transport data from `χ` to `χ ∘ σ.symm`. -/
theorem colourTransportData_of_iso
    (hL : ∀ (m : ℤ) (x : (laurentMaslovComplex G (ZMod 2)).X m),
      (laurentMaslovChainEquiv H (ZMod 2) m (e.hom.f m x) : LaurentChain (ZMod 2) n) =
        L (laurentMaslovChainEquiv G (ZMod 2) m x))
    (hd : laurentDifferential H (ZMod 2) ∘ₗ L.toLinearMap =
      L.toLinearMap ∘ₗ laurentDifferential G (ZMod 2))
    (hpres : (laurentMaslovBifiltration G (ZMod 2)).Preserves
      (laurentMaslovBifiltration H (ZMod 2)) e.hom)
    (hΦ : ∀ P : Finset (Fin n), L.toLinearMap ∘ₗ oDerivative (ZMod 2) G P =
      oDerivative (ZMod 2) H (P.map σ.toEmbedding) ∘ₗ L.toLinearMap)
    (χ : Fin n → ℕ) : ColourTransportData G χ H (χ ∘ σ.symm) := by
  intro hn hk
  refine ⟨e.hom, L.toLinearMap, hL, hd, Bifiltration.shifts_zero_zero_iff.mpr hpres,
    gridCanonicalClass_homotopyEquiv G H hn hk (HomotopyEquiv.ofIso e) 0
      (Bifiltration.shifts_zero_zero_iff.mpr hpres), fun v => .of_eq_zero ?_⟩
  rw [colourClass_comp_symm, hΦ, sub_self]

/-- The inverse of a native isomorphism as in `colourTransportData_of_iso` gives colour transport
data from `χ ∘ σ.symm` to `χ`. -/
theorem colourTransportData_of_iso_inv
    (hL : ∀ (m : ℤ) (x : (laurentMaslovComplex G (ZMod 2)).X m),
      (laurentMaslovChainEquiv H (ZMod 2) m (e.hom.f m x) : LaurentChain (ZMod 2) n) =
        L (laurentMaslovChainEquiv G (ZMod 2) m x))
    (hd : laurentDifferential H (ZMod 2) ∘ₗ L.toLinearMap =
      L.toLinearMap ∘ₗ laurentDifferential G (ZMod 2))
    (hpres : (laurentMaslovBifiltration H (ZMod 2)).Preserves
      (laurentMaslovBifiltration G (ZMod 2)) e.inv)
    (hΦ : ∀ P : Finset (Fin n), L.toLinearMap ∘ₗ oDerivative (ZMod 2) G P =
      oDerivative (ZMod 2) H (P.map σ.toEmbedding) ∘ₗ L.toLinearMap)
    (χ : Fin n → ℕ) : ColourTransportData H (χ ∘ σ.symm) G χ := by
  intro hk hn
  refine ⟨e.inv, L.symm.toLinearMap, fun i x => ?_, ?_, Bifiltration.shifts_zero_zero_iff.mpr hpres,
    gridCanonicalClass_homotopyEquiv H G hk hn (HomotopyEquiv.ofIso e.symm) 0
      (Bifiltration.shifts_zero_zero_iff.mpr hpres), fun v => .of_eq_zero ?_⟩
  · apply L.injective
    have h := congrArg (fun g => g.f i x) e.inv_hom_id
    change e.hom.f i (e.inv.f i x) = x at h
    rw [LinearEquiv.coe_coe, L.apply_symm_apply, ← hL, h]
  · apply LinearMap.ext
    intro z
    apply L.injective
    have h := LinearMap.congr_fun hd (L.symm z)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, L.apply_symm_apply] at h ⊢
    exact h.symm
  · rw [colourClass_comp_symm]
    apply LinearMap.ext
    intro z
    apply L.injective
    have h := LinearMap.congr_fun (hΦ (colourClass χ v)) (L.symm z)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, L.apply_symm_apply] at h
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub,
      L.apply_symm_apply, LinearMap.zero_apply, map_zero, h, sub_self]

/-- A native isomorphism as in `colourTransportData_of_iso`, whose inverse also preserves both
filtrations, and whose column permutation `σ` matches the components, gives colour pullbacks in
both directions. -/
theorem colourPullback_of_iso
    (hL : ∀ (m : ℤ) (x : (laurentMaslovComplex G (ZMod 2)).X m),
      (laurentMaslovChainEquiv H (ZMod 2) m (e.hom.f m x) : LaurentChain (ZMod 2) n) =
        L (laurentMaslovChainEquiv G (ZMod 2) m x))
    (hd : laurentDifferential H (ZMod 2) ∘ₗ L.toLinearMap =
      L.toLinearMap ∘ₗ laurentDifferential G (ZMod 2))
    (hpres : (laurentMaslovBifiltration G (ZMod 2)).Preserves
      (laurentMaslovBifiltration H (ZMod 2)) e.hom)
    (hpres' : (laurentMaslovBifiltration H (ZMod 2)).Preserves
      (laurentMaslovBifiltration G (ZMod 2)) e.inv)
    (hΦ : ∀ P : Finset (Fin n), L.toLinearMap ∘ₗ oDerivative (ZMod 2) G P =
      oDerivative (ZMod 2) H (P.map σ.toEmbedding) ∘ₗ L.toLinearMap)
    (hσ : ComponentMap G H σ.symm) : ColourPullback G H ∧ ColourPullback H G :=
  ⟨.of_componentMap hσ fun χ _ => colourTransportData_of_iso e L σ hL hd hpres hΦ χ,
    .of_componentMap_symm hσ fun χ _ => colourTransportData_of_iso_inv e L σ hL hd hpres' hΦ χ⟩

end Iso

end OnLeConjecture.KnotFloer.GridFull
