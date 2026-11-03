/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorFourMarkTower
public import OnLeConjecture.KnotFloer.GridColourMovesSymmetry
public import OnLeConjecture.KnotFloer.GridFullMarkingIndependence

/-!
# The map of a scissor phase and its determinant identity

Let `ScissorPhase H K k E` be a scissor phase (`GridExteriorScissorSteps`) between grids of size
`n ≥ 2`, and let `χ` be a colouring of the columns. Every step of the phase keeps each marking in
its column, so the colour classes of `χ` are the same column sets in every grid of the phase.
This file constructs a Laurent chain map `S : C(H) → C(K)` that lowers the Maslov degree by the
number `|E|` of `O` switches and raises the second filtration coordinate by at most
`k / 2 - |E| / 2` (`scissorPhase_map`). For every sequence `c` of `|E|` colours,

  `Ψ_{c 0} ⋯ Ψ_{c (|E| - 1)} S_* can(H) = det B • can(K)`

in the total homology of `K`, where `Ψ_v` is the colour derivative of the colour `v` and
`B r e` is the number, modulo two, of the two `O` markings exchanged by the `e`-th switch whose
column has colour `c r`. This is equation `determinant-pairing` of Section 4 of the written proof
of Statement E (`statement_E_complete_proof.tex`), for the star scissors of Section 9.

The steps of the phase are realized as follows.

* An `X` switch is the identity map. It has filtration shifts `(0, 1/2)`.
* An `O` switch of two adjacent rows is the `O` switch of the corresponding columns of the
  transposed grids, conjugated by the transposition maps. It has degree `-1` and second shift
  `-1/2`, and it satisfies the colour-switch relation `Ψ F = F Ψ + b K` on total homology.
* Row commutations and cyclic row rotations are the colour transport maps of
  `GridColourMovesSymmetry`, with the same colouring on both sides.

The proof applies `derivativeProduct_switchProduct_eq_det` to the product of the total homologies
of all grids of size `n`. The steps other than `O` switches commute with every colour derivative
and are composed into the next `O` switch.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex OnLeConjecture.KnotFloer

variable {n : ℕ}

/-! ### Total homology consequences of chain-level data -/

section TotalTransport

/-- Two composites of chain maps that agree induce the same composite on total homology. -/
theorem laurentTotalHomologyMap_comm {G H H' L : GridDiagram n}
    {f g f' g' : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n}
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    (hg : laurentDifferential L (ZMod 2) ∘ₗ g = g ∘ₗ laurentDifferential H (ZMod 2))
    (hf' : laurentDifferential H' (ZMod 2) ∘ₗ f' = f' ∘ₗ laurentDifferential G (ZMod 2))
    (hg' : laurentDifferential L (ZMod 2) ∘ₗ g' = g' ∘ₗ laurentDifferential H' (ZMod 2))
    (h : g ∘ₗ f = g' ∘ₗ f') (ξ : laurentTotalHomology G (ZMod 2)) :
    laurentTotalHomologyMap g hg (laurentTotalHomologyMap f hf ξ) =
      laurentTotalHomologyMap g' hg' (laurentTotalHomologyMap f' hf' ξ) := by
  rw [← laurentTotalHomologyMap_comp_apply hf hg (laurentChainHet_comp hf hg),
    ← laurentTotalHomologyMap_comp_apply hf' hg' (laurentChainHet_comp hf' hg')]
  exact LinearMap.congr_fun (laurentTotalHomologyMap_congr h _ _) ξ

/-- A chain map intertwining two derivatives up to homotopy intertwines them on total
homology. -/
theorem totalODerivative_transport {G H : GridDiagram n}
    {f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n}
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    {P Q : Finset (Fin n)}
    (h : IsNullHomotopic (laurentDifferential G (ZMod 2)) (laurentDifferential H (ZMod 2))
      (f ∘ₗ oDerivative (ZMod 2) G P - oDerivative (ZMod 2) H Q ∘ₗ f))
    (ξ : laurentTotalHomology G (ZMod 2)) :
    laurentTotalHomologyMap f hf (totalODerivative G P ξ) =
      totalODerivative H Q (laurentTotalHomologyMap f hf ξ) := by
  have hP := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) G P
  have hQ := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) H Q
  have e := laurentTotalHomologyMapHet_eq_of_isNullHomotopic _ _ (laurentChainHet_comp hP hf)
    (laurentChainHet_comp hf hQ) h
  have := LinearMap.congr_fun e ξ
  rw [laurentTotalHomologyMapHet_comp_apply hP hf, laurentTotalHomologyMapHet_comp_apply hf hQ]
    at this
  exact this

/-- A chain map agreeing with a native morphism that carries the canonical class to the canonical
class carries the total canonical class to the total canonical class. -/
theorem totalCanonicalClass_of_compat {G H : GridDiagram n} (hn : 2 ≤ n)
    (φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2))
    (f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    (hcompat : ∀ (m : ℤ) (x : (laurentMaslovComplex G (ZMod 2)).X m),
      (laurentMaslovChainEquiv H (ZMod 2) m (φ.f m x) : LaurentChain (ZMod 2) n) =
        f (laurentMaslovChainEquiv G (ZMod 2) m x))
    (hcan : homologyMap φ 0 (gridCanonicalClass G hn) = gridCanonicalClass H hn) :
    laurentTotalHomologyMap f hf (totalCanonicalClass G hn) = totalCanonicalClass H hn := by
  unfold totalCanonicalClass
  rw [← laurentTotalHomologyMapHet_eq, ← laurentGradedToTotal_naturality_of_compat φ f hf hcompat,
    hcan]

/-- A degree-zero piece shift of a Laurent map agreeing with a native morphism gives the
filtration shifts of the morphism. -/
theorem shifts_of_pieceShift {G H : GridDiagram n}
    (φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2))
    (f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
    (hcompat : ∀ (m : ℤ) (x : (laurentMaslovComplex G (ZMod 2)).X m),
      (laurentMaslovChainEquiv H (ZMod 2) m (φ.f m x) : LaurentChain (ZMod 2) n) =
        f (laurentMaslovChainEquiv G (ZMod 2) m x)) {s : ℝ}
    (hf : PieceShift G H G.alexander H.alexander f 0 s) :
    (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2)) φ 0 s := by
  intro u v m x hx
  have hp := (hf m _ (laurentMaslovChainEquiv G (ZMod 2) m x).property).2 u v (by
    change (laurentMaslovChainEquiv G (ZMod 2) m x : LaurentChain (ZMod 2) n) ∈
      laurentBifiltrationLevel G (ZMod 2) u v at hx
    rwa [laurentBifiltrationLevel_eq_alexanderLevel] at hx)
  rw [add_zero]
  change (laurentMaslovChainEquiv H (ZMod 2) m (φ.f m x) : LaurentChain (ZMod 2) n) ∈
    laurentBifiltrationLevel H (ZMod 2) u (v + s)
  rw [hcompat, laurentBifiltrationLevel_eq_alexanderLevel]
  exact hp

/-- The form of `totalODerivative_transport` for grids of different sizes. -/
theorem totalODerivative_transportHet {k : ℕ} {G : GridDiagram n} {H : GridDiagram k}
    {f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) k}
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    {P : Finset (Fin n)} {Q : Finset (Fin k)}
    (h : IsNullHomotopic (laurentDifferential G (ZMod 2)) (laurentDifferential H (ZMod 2))
      (f ∘ₗ oDerivative (ZMod 2) G P - oDerivative (ZMod 2) H Q ∘ₗ f))
    (ξ : laurentTotalHomology G (ZMod 2)) :
    laurentTotalHomologyMapHet f hf (totalODerivative G P ξ) =
      totalODerivative H Q (laurentTotalHomologyMapHet f hf ξ) := by
  have hP := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) G P
  have hQ := laurentDifferential_comp_oDerivative_eq (R := ZMod 2) H Q
  have e := laurentTotalHomologyMapHet_eq_of_isNullHomotopic _ _ (laurentChainHet_comp hP hf)
    (laurentChainHet_comp hf hQ) h
  have := LinearMap.congr_fun e ξ
  rw [laurentTotalHomologyMapHet_comp_apply hP hf, laurentTotalHomologyMapHet_comp_apply hf hQ]
    at this
  exact this

/-- The form of `totalCanonicalClass_of_compat` for grids of different sizes. -/
theorem totalCanonicalClass_of_compatHet {k : ℕ} {G : GridDiagram n} {H : GridDiagram k}
    (hn : 2 ≤ n) (hk : 2 ≤ k)
    (φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2))
    (f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) k)
    (hf : laurentDifferential H (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G (ZMod 2))
    (hcompat : ∀ (m : ℤ) (x : (laurentMaslovComplex G (ZMod 2)).X m),
      (laurentMaslovChainEquiv H (ZMod 2) m (φ.f m x) : LaurentChain (ZMod 2) k) =
        f (laurentMaslovChainEquiv G (ZMod 2) m x))
    (hcan : homologyMap φ 0 (gridCanonicalClass G hn) = gridCanonicalClass H hk) :
    laurentTotalHomologyMapHet f hf (totalCanonicalClass G hn) = totalCanonicalClass H hk := by
  unfold totalCanonicalClass
  rw [← laurentGradedToTotal_naturality_of_compat φ f hf hcompat, hcan]

end TotalTransport

/-! ### The product of all total homologies -/

section Module

/-- Equality of grid diagrams is decided classically in this section. -/
local instance : DecidableEq (GridDiagram n) := Classical.decEq _

/-- The product of the total homologies of all grid diagrams of size `n`. -/
abbrev ScissorModule (n : ℕ) : Type _ := (G : GridDiagram n) → laurentTotalHomology G (ZMod 2)

/-- The colour derivative of the colour `v` of a column colouring, acting on every factor. -/
def scissorDeriv (χ : Fin n → ℕ) (v : ℕ) :
    ScissorModule n →ₗ[LaurentPolynomial (ZMod 2)] ScissorModule n :=
  LinearMap.pi fun G => totalODerivative G (colourClass χ v) ∘ₗ LinearMap.proj G

/-- The map of the product given by a map from the factor of `G₁` to the factor of `G₂`. -/
def scissorBlock (G₁ G₂ : GridDiagram n)
    (T : laurentTotalHomology G₁ (ZMod 2) →ₗ[LaurentPolynomial (ZMod 2)]
      laurentTotalHomology G₂ (ZMod 2)) :
    ScissorModule n →ₗ[LaurentPolynomial (ZMod 2)] ScissorModule n :=
  LinearMap.single (LaurentPolynomial (ZMod 2))
      (fun G : GridDiagram n => laurentTotalHomology G (ZMod 2)) G₂ ∘ₗ T ∘ₗ LinearMap.proj G₁

theorem scissorDeriv_single (χ : Fin n → ℕ) (v : ℕ) (G : GridDiagram n)
    (ξ : laurentTotalHomology G (ZMod 2)) :
    scissorDeriv χ v (Pi.single G ξ) = Pi.single G (totalODerivative G (colourClass χ v) ξ) := by
  funext G'
  by_cases h : G' = G
  · subst h
    simp [scissorDeriv]
  · simp [scissorDeriv, Pi.single_eq_of_ne h]

theorem scissorBlock_single (G₁ G₂ : GridDiagram n)
    (T : laurentTotalHomology G₁ (ZMod 2) →ₗ[LaurentPolynomial (ZMod 2)]
      laurentTotalHomology G₂ (ZMod 2)) (ξ : laurentTotalHomology G₁ (ZMod 2)) :
    scissorBlock G₁ G₂ T (Pi.single G₁ ξ) = Pi.single G₂ (T ξ) := by
  simp [scissorBlock]

theorem scissorDeriv_comp_block (χ : Fin n → ℕ) (v : ℕ) {G₁ G₂ : GridDiagram n}
    {T Kd : laurentTotalHomology G₁ (ZMod 2) →ₗ[LaurentPolynomial (ZMod 2)]
      laurentTotalHomology G₂ (ZMod 2)} {b : LaurentPolynomial (ZMod 2)}
    (h : ∀ ξ, totalODerivative G₂ (colourClass χ v) (T ξ) =
      T (totalODerivative G₁ (colourClass χ v) ξ) + b • Kd ξ) :
    scissorDeriv χ v ∘ₗ scissorBlock G₁ G₂ T =
      scissorBlock G₁ G₂ T ∘ₗ scissorDeriv χ v + b • scissorBlock G₁ G₂ Kd := by
  apply LinearMap.ext
  intro m
  funext G
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, scissorDeriv,
    scissorBlock, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.coe_single,
    Pi.add_apply, Pi.smul_apply]
  by_cases hG : G = G₂
  · subst hG
    simp only [Pi.single_eq_same]
    exact h (m G₁)
  · simp only [Pi.single_eq_of_ne hG, map_zero, smul_zero, add_zero]

/-- The incidence of a colour with the pair of columns of one `O` switch. -/
def pairIncidence (χ : Fin n → ℕ) (p : Fin n × Fin n) (v : ℕ) : LaurentPolynomial (ZMod 2) :=
  (if χ p.1 = v then 1 else 0) + if χ p.2 = v then 1 else 0

/-- The incidence of a colour with the `e`-th `O` switch of a list, zero beyond the list. -/
def scissorIncidence (χ : Fin n → ℕ) (E : List (Fin n × Fin n)) (v e : ℕ) :
    LaurentPolynomial (ZMod 2) :=
  if h : e < E.length then pairIncidence χ E[e] v else 0

theorem scissorIncidence_nil (χ : Fin n → ℕ) (v e : ℕ) : scissorIncidence χ [] v e = 0 := by
  simp [scissorIncidence]

theorem scissorIncidence_append_self (χ : Fin n → ℕ) (E : List (Fin n × Fin n))
    (p : Fin n × Fin n) (v : ℕ) :
    scissorIncidence χ (E ++ [p]) v E.length = pairIncidence χ p v := by
  rw [scissorIncidence, dif_pos (by simp)]
  simp

theorem scissorIncidence_append_of_ne (χ : Fin n → ℕ) (E : List (Fin n × Fin n))
    (p : Fin n × Fin n) (v : ℕ) {e : ℕ} (he : e ≠ E.length) :
    scissorIncidence χ (E ++ [p]) v e = scissorIncidence χ E v e := by
  unfold scissorIncidence
  by_cases h : e < E.length
  · rw [dif_pos (by simp; omega), dif_pos h, List.getElem_append_left h]
  · rw [dif_neg (by simp; omega), dif_neg h]

theorem switchProduct_congr {M : Type*} [AddCommGroup M] [Module (LaurentPolynomial (ZMod 2)) M]
    {F F' : ℕ → M →ₗ[LaurentPolynomial (ZMod 2)] M} :
    ∀ d, (∀ e < d, F e = F' e) → switchProduct F d = switchProduct F' d
  | 0, _ => rfl
  | d + 1, h => by
    rw [switchProduct_succ, switchProduct_succ, h d (Nat.lt_succ_self d),
      switchProduct_congr d fun e he => h e (by omega)]

/-! ### The invariant of a scissor phase -/

/-- The data carried along a scissor phase from `H` to `G` with `O`-switch list `E` and second
shift `s`: a Laurent chain map `S` of degree `-|E|` and shift `s`, and maps of the product module
satisfying the hypotheses of the determinant pairing. -/
def ScissorInv (χ : Fin n → ℕ) (hn : 2 ≤ n) (H G : GridDiagram n) (E : List (Fin n × Fin n))
    (s : ℝ) : Prop :=
  ∃ (S : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
    (hS : laurentDifferential G (ZMod 2) ∘ₗ S = S ∘ₗ laurentDifferential H (ZMod 2)),
    PieceShift H G H.alexander G.alexander S (-(E.length : ℤ)) s ∧
    ∃ (F K : ℕ → ScissorModule n →ₗ[LaurentPolynomial (ZMod 2)] ScissorModule n)
      (x₀ : ScissorModule n) (tl : ScissorModule n →ₗ[LaurentPolynomial (ZMod 2)] ScissorModule n),
      (∀ v e, scissorDeriv χ v ∘ₗ F e = F e ∘ₗ scissorDeriv χ v + scissorIncidence χ E v e • K e) ∧
      (∀ v e, scissorDeriv χ v ∘ₗ K e = K e ∘ₗ scissorDeriv χ v) ∧
      (∀ v, scissorDeriv χ v x₀ = 0) ∧
      (∀ v, scissorDeriv χ v ∘ₗ tl = tl ∘ₗ scissorDeriv χ v) ∧
      tl (switchProduct F E.length x₀) =
        Pi.single G (laurentTotalHomologyMap S hS (totalCanonicalClass H hn)) ∧
      tl (switchProduct K E.length x₀) = Pi.single G (totalCanonicalClass G hn)

variable {χ : Fin n → ℕ} {hn : 2 ≤ n}

theorem ScissorInv.of_eq {H G : GridDiagram n} {E : List (Fin n × Fin n)} {s s' : ℝ}
    (h : ScissorInv χ hn H G E s) (hs : s = s') : ScissorInv χ hn H G E s' :=
  hs ▸ h

theorem scissorInv_refl (χ : Fin n → ℕ) (hn : 2 ≤ n) (H : GridDiagram n) :
    ScissorInv χ hn H H [] 0 := by
  have h0 : PieceShift H H H.alexander H.alexander
      (LinearMap.id : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] _) 0 0 :=
    PieceShift.of_levelShift (fun m x hx => by simpa using hx) (levelShift_id fun x => by simp)
  refine ⟨LinearMap.id, by rw [LinearMap.id_comp, LinearMap.comp_id], h0.congr rfl (by simp) rfl,
    fun _ => 0, fun _ => 0, Pi.single H (totalCanonicalClass H hn), LinearMap.id,
    fun v e => by simp [scissorIncidence_nil], fun v e => by simp, fun v => ?_,
    fun v => by rw [LinearMap.id_comp, LinearMap.comp_id], ?_, rfl⟩
  · rw [scissorDeriv_single]
    unfold totalODerivative
    rw [laurentTotalHomologyMap_oDerivative_totalCanonicalClass, Pi.single_zero]
  · rw [List.length_nil, switchProduct_zero, LinearMap.id_apply, LinearMap.id_apply,
      laurentTotalHomologyMap_id]
    rfl

/-- A step that commutes with the colour derivatives and preserves the canonical class. -/
theorem scissorInv_free {H G₁ G₂ : GridDiagram n} {E : List (Fin n × Fin n)} {s t : ℝ}
    (hI : ScissorInv χ hn H G₁ E s)
    (f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
    (hf : laurentDifferential G₂ (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G₁ (ZMod 2))
    (hfs : PieceShift G₁ G₂ G₁.alexander G₂.alexander f 0 t)
    (hcomm : ∀ v ξ, totalODerivative G₂ (colourClass χ v) (laurentTotalHomologyMap f hf ξ) =
      laurentTotalHomologyMap f hf (totalODerivative G₁ (colourClass χ v) ξ))
    (hcan : laurentTotalHomologyMap f hf (totalCanonicalClass G₁ hn) = totalCanonicalClass G₂ hn) :
    ScissorInv χ hn H G₂ E (s + t) := by
  obtain ⟨S, hS, hSs, F, K, x₀, tl, hF, hK, hx, htl, hFx, hKx⟩ := hI
  refine ⟨f ∘ₗ S, laurentChainHet_comp hS hf, (hSs.comp hfs).congr rfl (by simp) rfl, F, K, x₀,
    scissorBlock G₁ G₂ (laurentTotalHomologyMap f hf) ∘ₗ tl, hF, hK, hx, fun v => ?_, ?_, ?_⟩
  · have hb := scissorDeriv_comp_block χ v (T := laurentTotalHomologyMap f hf)
      (Kd := laurentTotalHomologyMap f hf) (b := 0) (fun ξ => by rw [hcomm, zero_smul, add_zero])
    rw [zero_smul, add_zero] at hb
    rw [← LinearMap.comp_assoc, hb, LinearMap.comp_assoc, htl, LinearMap.comp_assoc]
  · rw [LinearMap.comp_apply, hFx, scissorBlock_single, laurentTotalHomologyMap_comp_apply hS hf]
  · rw [LinearMap.comp_apply, hKx, scissorBlock_single, hcan]

/-- An `O`-switch step. -/
theorem scissorInv_switch {H G₁ G₂ : GridDiagram n} {E : List (Fin n × Fin n)} {s t : ℝ}
    (hI : ScissorInv χ hn H G₁ E s)
    (f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
    (hf : laurentDifferential G₂ (ZMod 2) ∘ₗ f = f ∘ₗ laurentDifferential G₁ (ZMod 2))
    (hfs : PieceShift G₁ G₂ G₁.alexander G₂.alexander f (-1) t) (p : Fin n × Fin n)
    (Kd : laurentTotalHomology G₁ (ZMod 2) →ₗ[LaurentPolynomial (ZMod 2)]
      laurentTotalHomology G₂ (ZMod 2))
    (hrel : ∀ v ξ, totalODerivative G₂ (colourClass χ v) (laurentTotalHomologyMap f hf ξ) =
      laurentTotalHomologyMap f hf (totalODerivative G₁ (colourClass χ v) ξ) +
        pairIncidence χ p v • Kd ξ)
    (hKd : ∀ v ξ, totalODerivative G₂ (colourClass χ v) (Kd ξ) =
      Kd (totalODerivative G₁ (colourClass χ v) ξ))
    (hcan : Kd (totalCanonicalClass G₁ hn) = totalCanonicalClass G₂ hn) :
    ScissorInv χ hn H G₂ (E ++ [p]) (s + t) := by
  obtain ⟨S, hS, hSs, F, K, x₀, tl, hF, hK, hx, htl, hFx, hKx⟩ := hI
  have hlen : (E ++ [p]).length = E.length + 1 := by simp
  refine ⟨f ∘ₗ S, laurentChainHet_comp hS hf,
    (hSs.comp hfs).congr rfl (by rw [hlen]; push_cast; ring) rfl,
    Function.update F E.length (scissorBlock G₁ G₂ (laurentTotalHomologyMap f hf) ∘ₗ tl),
    Function.update K E.length (scissorBlock G₁ G₂ Kd ∘ₗ tl), x₀, LinearMap.id,
    fun v e => ?_, fun v e => ?_, hx, fun v => by rw [LinearMap.id_comp, LinearMap.comp_id],
    ?_, ?_⟩
  · by_cases he : e = E.length
    · subst he
      rw [Function.update_self, Function.update_self, scissorIncidence_append_self]
      apply LinearMap.ext
      intro m
      have h1 := LinearMap.congr_fun (scissorDeriv_comp_block χ v (hrel v)) (tl m)
      have h2 := LinearMap.congr_fun (htl v) m
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at h1 h2 ⊢
      rw [h1, h2]
    · rw [Function.update_of_ne he, Function.update_of_ne he,
        scissorIncidence_append_of_ne χ E p v he]
      exact hF v e
  · by_cases he : e = E.length
    · subst he
      rw [Function.update_self]
      have hb := scissorDeriv_comp_block χ v (T := Kd) (Kd := Kd) (b := 0)
        (fun ξ => by rw [hKd, zero_smul, add_zero])
      rw [zero_smul, add_zero] at hb
      rw [← LinearMap.comp_assoc, hb, LinearMap.comp_assoc, htl, LinearMap.comp_assoc]
    · rw [Function.update_of_ne he]
      exact hK v e
  · rw [hlen, switchProduct_succ, LinearMap.comp_apply,
      switchProduct_congr (F' := F) E.length fun e he => Function.update_of_ne (ne_of_lt he) _ _,
      Function.update_self, LinearMap.comp_apply, hFx, scissorBlock_single, LinearMap.id_apply,
      laurentTotalHomologyMap_comp_apply hS hf]
  · rw [hlen, switchProduct_succ, LinearMap.comp_apply,
      switchProduct_congr (F' := K) E.length fun e he => Function.update_of_ne (ne_of_lt he) _ _,
      Function.update_self, LinearMap.comp_apply, hKx, scissorBlock_single, LinearMap.id_apply,
      hcan]

/-- The determinant identity carried by the invariant. -/
theorem ScissorInv.derivativeProduct_eq {H K : GridDiagram n} {E : List (Fin n × Fin n)} {s : ℝ}
    (hI : ScissorInv χ hn H K E s) :
    ∃ (S : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
      (hS : laurentDifferential K (ZMod 2) ∘ₗ S = S ∘ₗ laurentDifferential H (ZMod 2)),
      PieceShift H K H.alexander K.alexander S (-(E.length : ℤ)) s ∧
      ∀ cs : Fin E.length → ℕ,
        derivativeProduct (fun v => totalODerivative K (colourClass χ v)) cs
            (laurentTotalHomologyMap S hS (totalCanonicalClass H hn)) =
          (Matrix.of fun r e : Fin E.length => scissorIncidence χ E (cs r) e).det •
            totalCanonicalClass K hn := by
  obtain ⟨S, hS, hSs, F, K', x₀, tl, hF, hK, hx, htl, hFx, hKx⟩ := hI
  refine ⟨S, hS, hSs, fun cs => ?_⟩
  have key := congrArg tl (derivativeProduct_switchProduct_eq_det hF hK hx cs)
  have htl' := LinearMap.congr_fun (derivativeProduct_intertwine tl (scissorDeriv χ)
    (scissorDeriv χ) cs fun i => (htl (cs i)).symm) (switchProduct F E.length x₀)
  have hsingle := derivativeProduct_intertwine
    (LinearMap.single (LaurentPolynomial (ZMod 2))
      (fun G : GridDiagram n => laurentTotalHomology G (ZMod 2)) K)
    (scissorDeriv χ) (fun v => totalODerivative K (colourClass χ v)) cs fun i =>
      LinearMap.ext fun ξ => (scissorDeriv_single χ (cs i) K ξ).symm
  simp only [LinearMap.comp_apply] at htl'
  rw [htl', hFx, map_smul, hKx] at key
  have hs := LinearMap.congr_fun hsingle (laurentTotalHomologyMap S hS (totalCanonicalClass H hn))
  simp only [LinearMap.comp_apply, LinearMap.coe_single] at hs
  rw [← hs, ← Pi.single_smul] at key
  exact Pi.single_injective K key

end Module

/-! ### The steps of a scissor phase -/

section Steps

variable {χ : Fin n → ℕ} {hn : 2 ≤ n}

/-- Colour transport data with the same colouring on both sides give a step of the invariant. -/
theorem scissorInv_of_transport {H G₁ G₂ : GridDiagram n} {E : List (Fin n × Fin n)} {s : ℝ}
    (hI : ScissorInv χ hn H G₁ E s) (hT : ColourTransportData G₁ χ G₂ χ) :
    ScissorInv χ hn H G₂ E s := by
  obtain ⟨φ, f, hcompat, hf, hsh, hcan, hv⟩ := hT hn hn
  refine (scissorInv_free hI f hf (PieceShift.of_graded φ f hcompat hsh) (fun v ξ => ?_)
    (totalCanonicalClass_of_compat hn φ f hf hcompat hcan)).of_eq (add_zero s)
  exact (totalODerivative_transport hf (hv v) ξ).symm

/-- The cyclic row isomorphism and its inverse give colour transport data with the same
colouring. -/
theorem colourTransportData_cyclicRows (G : GridDiagram n) (χ : Fin n → ℕ) :
    ColourTransportData G χ (G.relabelRows (finRotate n)) χ ∧
      ColourTransportData (G.relabelRows (finRotate n)) χ G χ := by
  have hΦ : ∀ P : Finset (Fin n), (laurentCyclicRowsEquiv (ZMod 2)).toLinearMap ∘ₗ
      oDerivative (ZMod 2) G P = oDerivative (ZMod 2) (G.relabelRows (finRotate n))
        (P.map (Equiv.refl (Fin n)).toEmbedding) ∘ₗ
          (laurentCyclicRowsEquiv (ZMod 2)).toLinearMap := by
    intro P
    have hP : P.map (Equiv.refl (Fin n)).toEmbedding = P := by
      ext x
      simp
    rw [hP]
    exact laurentCyclicRowsEquiv_comp_oDerivative (ZMod 2) G P
  exact ⟨colourTransportData_of_iso (laurentMaslovCyclicRowsIso G (ZMod 2))
      (laurentCyclicRowsEquiv (ZMod 2)) (Equiv.refl (Fin n))
      (laurentMaslovChainEquiv_cyclicRows G (ZMod 2))
      (laurentDifferential_relabelRows_finRotate G (ZMod 2))
      (laurentMaslovCyclicRows_preserves G (ZMod 2)) hΦ χ,
    colourTransportData_of_iso_inv (laurentMaslovCyclicRowsIso G (ZMod 2))
      (laurentCyclicRowsEquiv (ZMod 2)) (Equiv.refl (Fin n))
      (laurentMaslovChainEquiv_cyclicRows G (ZMod 2))
      (laurentDifferential_relabelRows_finRotate G (ZMod 2))
      (laurentMaslovCyclicRows_inv_preserves G (ZMod 2)) hΦ χ⟩

theorem swapRows_toPerm_symm_apply (x : GridState n) (a b y : Fin n) :
    (x.swapRows a b).toPerm.symm y = x.toPerm.symm (Equiv.swap a b y) := by
  rw [Equiv.symm_apply_eq]
  change y = Equiv.swap a b (x.toPerm (x.toPerm.symm (Equiv.swap a b y)))
  rw [Equiv.apply_symm_apply, Equiv.swap_apply_self]

/-- A row commutation gives colour transport data with the same colouring, through
transposition. -/
theorem colourTransportData_rowCommutation {G₁ G₂ : GridDiagram n}
    (h : GridDiagram.IsRowCommutation G₁ G₂) (χ : Fin n → ℕ) : ColourTransportData G₁ χ G₂ χ := by
  obtain ⟨C, hC⟩ := GridDiagram.isColumnCommutation_iff_exists_columnCommutationData.mp
    ((GridDiagram.isColumnCommutation_transpose G₁ G₂).mpr h)
  have T1 := colourTransportData_of_iso (laurentMaslovTransposeIso G₁ (ZMod 2))
    (laurentTransposeEquiv (ZMod 2)) G₁.O.toPerm (fun _ _ => rfl)
    (laurentDifferential_transpose G₁ (ZMod 2)) (laurentMaslovTranspose_preserves G₁ (ZMod 2))
    (laurentTransposeEquiv_comp_oDerivative_finset (ZMod 2) G₁) χ
  have T2 := colourTransportData_columnCommutation G₁.transpose C (χ ∘ ⇑G₁.O.toPerm.symm)
  have T3 := colourTransportData_of_iso_inv (laurentMaslovTransposeIso G₂ (ZMod 2))
    (laurentTransposeEquiv (ZMod 2)) G₂.O.toPerm (fun _ _ => rfl)
    (laurentDifferential_transpose G₂ (ZMod 2)) (laurentMaslovTranspose_inv_preserves G₂ (ZMod 2))
    (laurentTransposeEquiv_comp_oDerivative_finset (ZMod 2) G₂) χ
  rw [← hC] at T2
  have hC' : G₂ = G₁.swapRows C.column (finRotate n C.column) := by
    have := congrArg GridDiagram.transpose hC
    simpa using this
  have hχ : (χ ∘ ⇑G₁.O.toPerm.symm) ∘ ⇑(Equiv.swap C.column (finRotate n C.column)).symm =
      χ ∘ ⇑G₂.O.toPerm.symm := by
    funext y
    simp only [Function.comp_apply, Equiv.symm_swap]
    rw [hC']
    exact congrArg χ (swapRows_toPerm_symm_apply G₁.O _ _ y).symm
  rw [hχ] at T2
  exact (T1.trans T2 id).trans T3 id

/-- An `X` switch of two adjacent rows is the identity map, with second shift `1/2`. -/
theorem scissorInv_xSwitch {H G₁ G₂ : GridDiagram n} {E : List (Fin n × Fin n)} {s : ℝ}
    (hI : ScissorInv χ hn H G₁ E s) {r : Fin n} (hr : r ≠ finRotate n r) (hO : G₂.O = G₁.O)
    (hX : G₂.X = G₁.X.swapRows r (finRotate n r)) : ScissorInv χ hn H G₂ E (s + 1 / 2) := by
  have hd : laurentDifferential G₂ (ZMod 2) = laurentDifferential G₁ (ZMod 2) :=
    laurentDifferential_eq_of_O_eq (ZMod 2) hO
  have hf : laurentDifferential G₂ (ZMod 2) ∘ₗ LinearMap.id =
      LinearMap.id ∘ₗ laurentDifferential G₁ (ZMod 2) := by
    rw [hd, LinearMap.id_comp, LinearMap.comp_id]
  have halex : ∀ x : GridState n, (G₂.alexander x : ℝ) ≤ G₁.alexander x + 1 / 2 := by
    intro x
    have hq : G₂.alexander x ≤ G₁.alexander x + 1 / 2 := by
      rw [← GridDiagram.alexander_transpose G₂ x, ← GridDiagram.alexander_transpose G₁ x,
        ← alexander_toAuxiliaryPair, ← alexander_toAuxiliaryPair]
      simp only [AuxiliaryPair.alexander, toAuxiliaryPair_O, toAuxiliaryPair_X,
        GridDiagram.transpose_O, GridDiagram.transpose_X]
      rw [hO, hX, GridState.swapRows_transpose]
      have h1 := markingMaslovℤ_swapColumns_sub_le G₁.X.transpose hr x.transpose
      have h2 : ((markingMaslovℤ G₁.O.transpose x.transpose -
          markingMaslovℤ (G₁.X.transpose.swapColumns r (finRotate n r)) x.transpose : ℤ) : ℚ) ≤
          ((markingMaslovℤ G₁.O.transpose x.transpose -
            markingMaslovℤ G₁.X.transpose x.transpose : ℤ) : ℚ) + 1 := by
        exact_mod_cast (by omega)
      linarith
    have h' := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at h'
    linarith
  have hfs : PieceShift G₁ G₂ G₁.alexander G₂.alexander
      (LinearMap.id : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] _) 0 (1 / 2) :=
    PieceShift.of_levelShift (fun m x hx => by
      rw [add_zero, LinearMap.id_apply, laurentMaslovPiece_eq_of_O_eq (ZMod 2) hO]
      exact hx) (levelShift_id halex)
  refine scissorInv_free hI LinearMap.id hf hfs (fun v ξ => ?_) ?_
  · unfold totalODerivative
    exact laurentTotalHomologyMap_comm hf (laurentDifferential_comp_oDerivative_eq _ _)
      (laurentDifferential_comp_oDerivative_eq _ _) hf
      (by rw [oDerivative_congr_O hO, LinearMap.comp_id, LinearMap.id_comp]) ξ
  · refine totalCanonicalClass_of_compat hn (laurentMaslovMarkingIso (ZMod 2) hO.symm).hom
      LinearMap.id hf (fun m x => rfl) ?_
    exact gridCanonicalClass_homotopyEquiv G₁ G₂ hn hn
      (HomotopyEquiv.ofIso (laurentMaslovMarkingIso (ZMod 2) hO.symm)) (1 / 2)
      (shifts_of_pieceShift _ _ (fun m x => rfl) hfs)

/-- An `O` switch of two adjacent rows, through transposition. -/
theorem scissorInv_oSwitch {H G₁ G₂ : GridDiagram n} {E : List (Fin n × Fin n)} {s : ℝ}
    (hI : ScissorInv χ hn H G₁ E s) {r : Fin n} (hr : r ≠ finRotate n r)
    (hO : G₂.O = G₁.O.swapRows r (finRotate n r)) (hX : G₂.X = G₁.X) :
    ScissorInv χ hn H G₂ (E ++ [(G₁.O.transpose r, G₁.O.transpose (finRotate n r))])
      (s + -1 / 2) := by
  obtain ⟨φ₁, f₁, hc₁, hd₁, hs₁, hcl₁, hv₁⟩ := colourTransportData_of_iso
    (laurentMaslovTransposeIso G₁ (ZMod 2)) (laurentTransposeEquiv (ZMod 2)) G₁.O.toPerm
    (fun _ _ => rfl) (laurentDifferential_transpose G₁ (ZMod 2))
    (laurentMaslovTranspose_preserves G₁ (ZMod 2))
    (laurentTransposeEquiv_comp_oDerivative_finset (ZMod 2) G₁) χ hn hn
  obtain ⟨φ₂, f₂, hc₂, hd₂, hs₂, hcl₂, hv₂⟩ := colourTransportData_of_iso_inv
    (laurentMaslovTransposeIso G₂ (ZMod 2)) (laurentTransposeEquiv (ZMod 2)) G₂.O.toPerm
    (fun _ _ => rfl) (laurentDifferential_transpose G₂ (ZMod 2))
    (laurentMaslovTranspose_inv_preserves G₂ (ZMod 2))
    (laurentTransposeEquiv_comp_oDerivative_finset (ZMod 2) G₂) χ hn hn
  have hO' : G₂.transpose.O = G₁.transpose.O.swapColumns r (finRotate n r) := by
    rw [GridDiagram.transpose_O, GridDiagram.transpose_O, hO]
    rfl
  have hX' : G₂.transpose.X = G₁.transpose.X := by
    rw [GridDiagram.transpose_X, GridDiagram.transpose_X, hX]
  have hF := laurentDifferential_comp_oSwitchMap (ZMod 2) hr hO'
  have hFs : PieceShift G₁.transpose G₂.transpose G₁.transpose.alexander
      G₂.transpose.alexander (oSwitchMap (ZMod 2) G₁.transpose r) (-1) (-1 / 2) := by
    refine PieceShift.of_levelShift (fun m x hx => ?_) ?_
    · have := oSwitchMap_mem_maslovPiece (R := ZMod 2) hr hO' hx
      simpa [sub_eq_add_neg] using this
    · have h := levelShift_oSwitchMap_auxiliary (R := ZMod 2)
        (B := toAuxiliaryPair G₂.transpose) hr hO' hX'
      have hB : (toAuxiliaryPair G₂.transpose).alexander = G₂.transpose.alexander :=
        funext (alexander_toAuxiliaryPair _)
      rwa [hB] at h
  have hf := laurentChainHet_comp (laurentChainHet_comp hd₁ hF) hd₂
  have hfs := ((PieceShift.of_graded φ₁ f₁ hc₁ hs₁).comp hFs).comp
    (PieceShift.of_graded φ₂ f₂ hc₂ hs₂)
  have hK := laurentDifferential_comp_labelDetecting (R := ZMod 2) hr hO' r (finRotate n r)
  have hT : ∀ η, laurentTotalHomologyMap (f₂ ∘ₗ oSwitchMap (ZMod 2) G₁.transpose r ∘ₗ f₁) hf η =
      laurentTotalHomologyMap f₂ hd₂ (laurentTotalHomologyMap _ hF
        (laurentTotalHomologyMap f₁ hd₁ η)) := fun η => by
    rw [laurentTotalHomologyMap_comp_apply (laurentChainHet_comp hd₁ hF) hd₂,
      laurentTotalHomologyMap_comp_apply hd₁ hF]
  have hQ : ∀ v, colourClass (χ ∘ ⇑G₂.O.toPerm.symm) v =
      (colourClass (χ ∘ ⇑G₁.O.toPerm.symm) v).map (Equiv.swap r (finRotate n r)).toEmbedding := by
    intro v
    ext y
    rw [Finset.mem_map_equiv, Equiv.symm_swap]
    simp only [colourClass, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    rw [hO, swapRows_toPerm_symm_apply]
  refine (scissorInv_switch hI (f₂ ∘ₗ oSwitchMap (ZMod 2) G₁.transpose r ∘ₗ f₁) hf
    (hfs.congr rfl (by norm_num) (by norm_num)) _
    (laurentTotalHomologyMap f₂ hd₂ ∘ₗ laurentTotalHomologyMap _ hK ∘ₗ
      laurentTotalHomologyMap f₁ hd₁) (fun v ξ => ?_) (fun v ξ => ?_) ?_).of_eq rfl
  · have e1 := totalODerivative_transport hd₁ (hv₁ v) ξ
    have e2 := totalODerivative_transport hd₂ (hv₂ v)
    have e3 := LinearMap.congr_fun (laurentTotalHomologyMap_colour_switch hr hO'
      (colourClass (χ ∘ ⇑G₁.O.toPerm.symm) v) (colourClass (χ ∘ ⇑G₂.O.toPerm.symm) v) (hQ v)
      (pairIncidence χ (G₁.O.transpose r, G₁.O.transpose (finRotate n r)) v)
      (by
        simp only [pairIncidence, colourClass, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.comp_apply, GridState.transpose_apply]
        by_cases h1 : χ (G₁.O.toPerm.symm r) = v <;>
          by_cases h2 : χ (G₁.O.toPerm.symm (finRotate n r)) = v <;> simp [*]))
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at e3 ⊢
    rw [hT, hT, ← e2]
    unfold totalODerivative at e1 ⊢
    rw [e3, map_add, map_smul, e1]
  · have e1 := totalODerivative_transport hd₁ (hv₁ v) ξ
    have e2 := totalODerivative_transport hd₂ (hv₂ v)
    have e4 := LinearMap.congr_fun (laurentTotalHomologyMap_colour_detecting hr hO'
      (colourClass (χ ∘ ⇑G₁.O.toPerm.symm) v) (colourClass (χ ∘ ⇑G₂.O.toPerm.symm) v)
      (hQ v))
    simp only [LinearMap.comp_apply] at e4 ⊢
    rw [← e2]
    unfold totalODerivative at e1 ⊢
    rw [e4, e1]
  · simp only [LinearMap.comp_apply]
    rw [totalCanonicalClass_of_compat hn φ₁ f₁ hd₁ hc₁ hcl₁,
      laurentTotalHomologyMap_totalCanonicalClass hn _
        (labelDetecting_mem_maslovPiece hr hO' _ _) _
        (homologyMap_labelDetecting_gridCanonicalClass_anyX hn hr hO' hr.symm
          (oSwitchLabel_left hO')),
      totalCanonicalClass_of_compat hn φ₂ f₂ hd₂ hc₂ hcl₂]

/-- **The invariant along a scissor phase.** -/
theorem scissorPhase_inv (χ : Fin n → ℕ) (hn : 2 ≤ n) {H K : GridDiagram n} {k : ℕ}
    {E : List (Fin n × Fin n)} (h : ScissorPhase H K k E) :
    ScissorInv χ hn H K E ((k : ℝ) / 2 - (E.length : ℝ) / 2) := by
  induction h with
  | refl => exact (scissorInv_refl χ hn _).of_eq (by simp)
  | xSwitch h r hr hO hX ih => exact (scissorInv_xSwitch ih hr hO hX).of_eq (by push_cast; ring)
  | oSwitch h r hr hO hX ih =>
    exact (scissorInv_oSwitch ih hr hO hX).of_eq
      (by rw [List.length_append, List.length_singleton]; push_cast; ring)
  | rowCommutation h hc ih =>
    exact scissorInv_of_transport ih (colourTransportData_rowCommutation hc χ)
  | cyclicRows h hc ih =>
    rcases hc with rfl | rfl
    · exact scissorInv_of_transport ih (colourTransportData_cyclicRows _ χ).1
    · exact scissorInv_of_transport ih (colourTransportData_cyclicRows _ χ).2

/-- **The map of a scissor phase.** -/
theorem scissorPhase_map (χ : Fin n → ℕ) (hn : 2 ≤ n) {H K : GridDiagram n} {k : ℕ}
    {E : List (Fin n × Fin n)} (h : ScissorPhase H K k E) :
    ∃ (S : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) n)
      (hS : laurentDifferential K (ZMod 2) ∘ₗ S = S ∘ₗ laurentDifferential H (ZMod 2)),
      PieceShift H K H.alexander K.alexander S (-(E.length : ℤ))
        ((k : ℝ) / 2 - (E.length : ℝ) / 2) ∧
      ∀ cs : Fin E.length → ℕ,
        derivativeProduct (fun v => totalODerivative K (colourClass χ v)) cs
            (laurentTotalHomologyMap S hS (totalCanonicalClass H hn)) =
          (Matrix.of fun r e : Fin E.length => scissorIncidence χ E (cs r) e).det •
            totalCanonicalClass K hn :=
  (scissorPhase_inv χ hn h).derivativeProduct_eq

end Steps

end OnLeConjecture.KnotFloer.GridFull
