/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ImmersionImageRing
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Extension using two regular elements of an image ring

If `x` is nonzero and `y` is regular modulo `(x)`, powers of `y` do not
introduce divisibility by powers of `x`. Consequently an element of an
ambient domain belongs to the subring whenever multiplying it by a power
of either `x` or `y` puts it in the subring.

For an analytic image this proves surjectivity of pullback when such a
pair lies in the radical of the image conductor. The existence of the
pair and its membership in that radical are explicit hypotheses.
-/

public section

namespace OnLeConjecture

/-- Powers of the second member of a regular pair can be cancelled from
divisibility by powers of the first member. -/
theorem pow_dvd_of_regular_pair
    {R : Type*} [CommRing R] [IsDomain R] {x y a : R}
    (hx : x ≠ 0) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
    (n m : ℕ) (h : x ^ n ∣ y ^ m * a) : x ^ n ∣ a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have hxa : x ∣ a := by
      apply Ideal.mem_span_singleton.mp
      apply mem_of_isSMulRegular_quotient_of_smul_mem (hy.pow m)
      change y ^ m * a ∈ Ideal.span {x}
      exact Ideal.mem_span_singleton.mpr
        ((dvd_pow_self x (Nat.succ_ne_zero n)).trans h)
    obtain ⟨c, rfl⟩ := hxa
    obtain ⟨b, hb⟩ := h
    have hbc : y ^ m * c = x ^ n * b := by
      apply mul_left_cancel₀ hx
      calc
        x * (y ^ m * c) = y ^ m * (x * c) := by ring
        _ = x ^ (n + 1) * b := hb
        _ = x * (x ^ n * b) := by ring
    obtain ⟨d, hd⟩ := ih ⟨b, hbc⟩
    exact ⟨d, by rw [hd]; ring⟩

/-- A regular pair detects membership in a subring by clearing a power
of either member. -/
theorem mem_subring_of_regular_pair_powers
    {S : Type*} [CommRing S] [IsDomain S] (A : Subring S)
    {x y : A} (hx : x ≠ 0) (hy : IsSMulRegular (A ⧸ Ideal.span {x}) y)
    {z : S} (n m : ℕ) (hxz : (x : S) ^ n * z ∈ A)
    (hyz : (y : S) ^ m * z ∈ A) : z ∈ A := by
  let a : A := ⟨(x : S) ^ n * z, hxz⟩
  let b : A := ⟨(y : S) ^ m * z, hyz⟩
  have hab : x ^ n ∣ y ^ m * a := by
    refine ⟨b, ?_⟩
    apply Subtype.ext
    change (y : S) ^ m * ((x : S) ^ n * z) =
      (x : S) ^ n * ((y : S) ^ m * z)
    ring
  obtain ⟨c, hc⟩ := pow_dvd_of_regular_pair hx hy n m hab
  have hxS : (x : S) ≠ 0 := fun h => hx (Subtype.ext h)
  have hcz : z = (c : S) := by
    apply mul_left_cancel₀ (pow_ne_zero n hxS)
    exact congrArg Subtype.val hc
  exact hcz ▸ c.property

namespace Analytic.PointedMapGerm

/-- A regular pair in the radical of the conductor makes every source
germ a pullback. No normality assumption is used. -/
theorem pullback_surjective_of_regular_pair_in_conductor_radical
    {n m : ℕ} (g : PointedMapGerm n m) (x y : g.ImageRing)
    (hx : x ≠ 0) (hy : IsSMulRegular (g.ImageRing ⧸ Ideal.span {x}) y)
    (hxc : (x : Germ n) ∈ g.imageConductor.radical)
    (hyc : (y : Germ n) ∈ g.imageConductor.radical) :
    Function.Surjective g.pullbackRingHom := by
  obtain ⟨k, hk⟩ := hxc
  obtain ⟨l, hl⟩ := hyc
  intro a
  exact mem_subring_of_regular_pair_powers g.ImageRing hx hy k l (hk a) (hl a)

/-- A regular pair in the radical of the image conductor forces the
analytic map to be an immersion. -/
theorem differential_injective_of_regular_pair_in_conductor_radical
    {n m : ℕ} (g : PointedMapGerm n m) (x y : g.ImageRing)
    (hx : x ≠ 0) (hy : IsSMulRegular (g.ImageRing ⧸ Ideal.span {x}) y)
    (hxc : (x : Germ n) ∈ g.imageConductor.radical)
    (hyc : (y : Germ n) ∈ g.imageConductor.radical) :
    Function.Injective g.differential :=
  g.differential_injective_of_pullback_surjective
    (g.pullback_surjective_of_regular_pair_in_conductor_radical x y hx hy hxc hyc)

end Analytic.PointedMapGerm

end OnLeConjecture
