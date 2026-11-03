/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorScissorMap
public import OnLeConjecture.KnotFloer.GridColourMovesTo
public import OnLeConjecture.KnotFloer.GridScissorSequenceRoute

/-!
# The scissor and cleanup statement from its combinatorial route

This file proves `ScissorCleanupStatement` (`GridExteriorReduction`) from its combinatorial part
`ScissorRouteStatement` (`GridExteriorScissorSteps`), following Section 12 of the written proof
of Statement E (`statement_E_complete_proof.tex`, "Construction of the complete map and proof of
Statement E").

For a signed word grid `H`, the route gives a scissor phase `H → K` with `k` adjacent `X`
switches and a list `E` of `O` switches forming a spanning tree of the components of `K`, grid
moves `K → K'`, and a tower of `|E|` four-mark blocks over the iterated seam `G₀`. The native map
is the composite

  `ψ = M ∘ f ∘ S : C(H) → C(K) → C(K') → C(G₀)`

of the scissor-phase map `S` (degree `-|E|`, second shift `k/2 - |E|/2`,
`scissorPhase_map`), a colour-natural move map `f` (shifts `(0, 0)`,
`exists_colourTransportData_of_movesTo`) and the tower removal map `M` (degree `|E|`, second
shift `|E|/2`, `fourMarkTower_removal`). On total homology `M_* = Q ∘ Ψ_1 ⋯ Ψ_{|E|}`, the colour
derivatives pass through `f`, and the determinant identity of the scissor phase gives
`ψ_* can(H) = det B • can(G₀)`. The matrix `B` is the reduced incidence matrix of the components
of `K` and the edges `E`, with the root at the component of colour `0`. Its determinant is one
(`det_scissorIncidence_eq_one`): a vector in its left kernel is a function on the components that
is constant along every edge, hence constant, and it vanishes at the root.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex OnLeConjecture.KnotFloer OnLeConjecture.KnotTheory

variable {n : ℕ}

/-! ### The reduced incidence determinant -/

section Determinant

/-- A component colouring is constant on the cycles of the component permutation. -/
theorem ComponentColouring.eq_of_sameCycle {K : GridDiagram n} {χ : Fin n → ℕ}
    (hχ : ComponentColouring K χ) {a b : Fin n} (h : (gridComponentPerm K).SameCycle a b) :
    χ a = χ b := by
  obtain ⟨i, rfl⟩ := h
  suffices hs : ∀ i : ℤ, χ ((gridComponentPerm K ^ i) a) = χ a from (hs i).symm
  intro i
  induction i using Int.induction_on with
  | zero => simp
  | succ i ih => rw [add_comm, zpow_one_add, Equiv.Perm.mul_apply, hχ, ih]
  | pred i ih =>
    rw [← ih, ← hχ ((gridComponentPerm K ^ (-(i : ℤ) - 1)) a), ← Equiv.Perm.mul_apply,
      ← zpow_one_add, show (1 : ℤ) + (-(i : ℤ) - 1) = -(i : ℤ) by ring]

/-- The incidence matrix over `ZMod 2` of the colours `cs` with the `O` switches `E`. -/
def incidenceMatrix (χ : Fin n → ℕ) (E : List (Fin n × Fin n)) (cs : Fin E.length → ℕ) :
    Matrix (Fin E.length) (Fin E.length) (ZMod 2) :=
  Matrix.of fun r e => (if χ (E[e]).1 = cs r then 1 else 0) + if χ (E[e]).2 = cs r then 1 else 0

theorem incidenceMatrix_map (χ : Fin n → ℕ) (E : List (Fin n × Fin n)) (cs : Fin E.length → ℕ) :
    (Matrix.of fun r e : Fin E.length => scissorIncidence χ E (cs r) e) =
      (algebraMap (ZMod 2) (LaurentPolynomial (ZMod 2))).mapMatrix (incidenceMatrix χ E cs) := by
  ext r e
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, scissorIncidence,
    dif_pos e.isLt, incidenceMatrix, Matrix.of_apply, pairIncidence, map_add]
  simp only [Fin.getElem_fin]
  congr 1
  split_ifs <;> simp

/-- **The reduced incidence determinant of a spanning tree is one.** Let `χ` be a component
colouring of `K`, let the edges `E` connect the components, let the colours `cs` be distinct,
each taken by some column, and let some column have a colour `v₀` outside `cs`. Then the
incidence matrix has determinant one. -/
theorem det_incidenceMatrix_ne_zero {K : GridDiagram n} {χ : Fin n → ℕ}
    (hχ : ComponentColouring K χ) {E : List (Fin n × Fin n)}
    (hconn : ∀ a b : Fin n,
      Relation.EqvGen (fun a b => (gridComponentPerm K).SameCycle a b ∨ (a, b) ∈ E) a b)
    (cs : Fin E.length → ℕ) (hcs : Function.Injective cs) (hval : ∀ r, ∃ c, χ c = cs r)
    {c₀ : Fin n} (hc₀ : ∀ r, χ c₀ ≠ cs r) : (incidenceMatrix χ E cs).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  let W : ℕ → ZMod 2 := fun u => ∑ r, if u = cs r then w r else 0
  have hedge : ∀ e : Fin E.length, W (χ (E[e]).1) = W (χ (E[e]).2) := by
    intro e
    have h := congrFun hw e
    simp only [Matrix.vecMul, dotProduct, incidenceMatrix, Matrix.of_apply, mul_add, mul_ite,
      mul_one, mul_zero, Finset.sum_add_distrib, Pi.zero_apply] at h
    have h2 := eq_neg_of_add_eq_zero_left h
    rwa [ZMod.neg_eq_self_mod_two] at h2
  have hrel : ∀ a b, Relation.EqvGen
      (fun a b => (gridComponentPerm K).SameCycle a b ∨ (a, b) ∈ E) a b → W (χ a) = W (χ b) := by
    intro a b h
    induction h with
    | rel a b h =>
      rcases h with h | h
      · rw [hχ.eq_of_sameCycle h]
      · obtain ⟨i, hi, hab⟩ := List.getElem_of_mem h
        have := hedge ⟨i, hi⟩
        simp only [Fin.getElem_fin, hab] at this
        exact this
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  have hroot : W (χ c₀) = 0 := Finset.sum_eq_zero fun r _ => if_neg (hc₀ r)
  apply hw0
  funext r
  obtain ⟨a, ha⟩ := hval r
  have hWr : W (cs r) = w r := by
    refine (Finset.sum_eq_single r (fun r' _ hr' => if_neg fun h => hr' (hcs h).symm)
      (fun h => absurd (Finset.mem_univ r) h)).trans (if_pos rfl)
  rw [Pi.zero_apply, ← hWr, ← ha, hrel a c₀ (hconn a c₀), hroot]

theorem det_scissorIncidence_eq_one {K : GridDiagram n} {χ : Fin n → ℕ}
    (hχ : ComponentColouring K χ) {E : List (Fin n × Fin n)}
    (hconn : ∀ a b : Fin n,
      Relation.EqvGen (fun a b => (gridComponentPerm K).SameCycle a b ∨ (a, b) ∈ E) a b)
    (cs : Fin E.length → ℕ) (hcs : Function.Injective cs) (hval : ∀ r, ∃ c, χ c = cs r)
    {c₀ : Fin n} (hc₀ : ∀ r, χ c₀ ≠ cs r) :
    (Matrix.of fun r e : Fin E.length => scissorIncidence χ E (cs r) e).det = 1 := by
  have h := det_incidenceMatrix_ne_zero hχ hconn cs hcs hval hc₀
  have h1 : (incidenceMatrix χ E cs).det = 1 := by
    generalize (incidenceMatrix χ E cs).det = d at h
    revert d
    decide
  rw [incidenceMatrix_map, ← RingHom.map_det, h1, map_one]

end Determinant

/-! ### The final assembly -/

/-- **The scissor and cleanup statement from its combinatorial route.** -/
theorem scissorCleanupStatement_of_scissorRoute (h : ScissorRouteStatement) :
    ScissorCleanupStatement := by
  intro S N B hS hN F hzero htrans
  obtain ⟨sizes, D, hprep, hD, hmoves, hroute⟩ := h S N B hS hN F hzero htrans
  refine ⟨sizes, D, hprep, hD, hmoves, fun H hH2 hHsig => ?_⟩
  obtain ⟨K, E, k, m, K', e, hk, hphase, htree, hKK', htower⟩ := hroute H hHsig
  have hn₀ := two_le_iteratedSeamSize hN hD
  obtain ⟨hle, M, hM, χ', Qt, hMs, hχ', he0, -, hex, hQt, hfac⟩ :=
    fourMarkTower_removal hn₀ htower
  have hm : 2 ≤ m := le_trans hn₀ hle
  obtain ⟨χ, hχ, -, hval, hT⟩ := exists_colourTransportData_of_movesTo hKK' χ' hχ'
  obtain ⟨φ, f, hcompat, hf, hsh, hcan, hv⟩ := hT hH2 hm
  obtain ⟨Sm, hS, hSs, hdet⟩ := scissorPhase_map χ hH2 hphase
  -- the composite Laurent map
  have hfS := laurentChainHet_comp hS hf
  have hψ := laurentChainHet_comp hfS hM
  have hk' : (k : ℝ) = (F.scissorShiftCount : ℝ) := by exact_mod_cast hk
  have hps := ((hSs.comp (PieceShift.of_graded φ f hcompat hsh)).comp hMs).congr
    (d' := 0) (s' := (F.scissorShiftCount : ℝ) / 2) rfl (by ring) (by rw [← hk']; ring)
  refine ⟨laurentMaslovHomOfMapHet H (iteratedSeamGrid D hprep) (M ∘ₗ f ∘ₗ Sm)
    hps.degree_zero hψ, ?_, ?_⟩
  · exact laurentMaslovHomOfMapHet_shifts_of_pieceShift hps hψ
  · apply laurentGradedToTotal_injective _ (ZMod 2) 0
    rw [laurentGradedToTotal_naturality_of_compat _ (M ∘ₗ f ∘ₗ Sm) hψ
      (fun m x => laurentMaslovChainEquiv_homOfMapHet _ _ _ _ _ m x)]
    change laurentTotalHomologyMapHet (M ∘ₗ f ∘ₗ Sm) hψ (totalCanonicalClass H hH2) =
      totalCanonicalClass (iteratedSeamGrid D hprep) hn₀
    rw [laurentTotalHomologyMapHet_comp_apply hfS hM, hfac,
      laurentTotalHomologyMapHet_comp_apply hS hf]
    -- the colour derivatives pass through the move map
    have hint := derivativeProduct_intertwine (laurentTotalHomologyMapHet f hf)
      (fun v => totalODerivative K' (colourClass χ' v))
      (fun v => totalODerivative K (colourClass χ v)) (fun i : Fin E.length => i.val + 1)
      (fun i => LinearMap.ext fun ξ => totalODerivative_transportHet hf (hv (i.val + 1)) ξ)
    have h1 := LinearMap.congr_fun hint
      (laurentTotalHomologyMapHet Sm hS (totalCanonicalClass H hH2))
    simp only [LinearMap.comp_apply] at h1
    rw [← h1]
    have hd := hdet (fun i : Fin E.length => i.val + 1)
    rw [laurentTotalHomologyMapHet_eq, hd]
    have hone : (Matrix.of fun r e : Fin E.length =>
        scissorIncidence χ E (r.val + 1) e).det = 1 := by
      obtain ⟨c₀, hc₀⟩ := (hval 0).mpr ⟨e ⟨0, by omega⟩, he0 _⟩
      refine det_scissorIncidence_eq_one hχ htree.1 (fun i : Fin E.length => i.val + 1)
        (fun i j hij => Fin.ext (by simp only at hij; omega)) (fun r => (hval _).mpr (hex r))
        (c₀ := c₀) (fun r => by rw [hc₀]; omega)
    rw [hone, one_smul, totalCanonicalClass_of_compatHet hH2 hm φ f hf hcompat hcan]
    exact hQt hm

/-- **The scissor and cleanup statement from the cleanup of the scissor endpoint.** The scissor
phase is `exists_scissorPhase` (`GridScissorSequenceRoute`). -/
theorem scissorCleanupStatement_of_endpointCleanup (h : ScissorEndpointCleanupStatement) :
    ScissorCleanupStatement :=
  scissorCleanupStatement_of_scissorRoute (scissorRouteStatement_of_cleanup h)

end OnLeConjecture.KnotFloer.GridFull
