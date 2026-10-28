/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Polynomial.Hensel
public import AdicModules.RingTheory.HenselianTransport
import AdicModules.Polynomial.Evaluation
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.RingTheory.Ideal.Operations

/-!
# Polynomial images on smaller ideal neighborhoods

For a Henselian pair `(R, I)` and `d = P.derivative.eval₂ φ a`, every ideal
`J ≤ (d)I` defines a neighborhood on which polynomial evaluation has image
`P.eval₂ φ a + (d)J`. A regular derivative makes this map a bijection.

The coefficient semiring need not be commutative, and the point `a` need not
belong to the image of the coefficient homomorphism.

## Usage

Given `hJ : J ≤ Ideal.span {P.derivative.eval₂ φ a} * I`, use
`HenselianRing.image_eval₂_eq_setOf_sub_mem_of_le_span_derivative_mul I φ P a J hJ`
to identify the image. With `hd : P.derivative.eval₂ φ a ∈ nonZeroDivisors R`,
`HenselianRing.bijOn_eval₂_of_le_span_derivative_mul I φ P a J hJ hd`
gives a bijection between the same neighborhoods. Its proof uses the image equality
and restricts injectivity from the larger neighborhood.

## Examples and boundaries

* In `ℤ/256`, take `C = ℕ` with its cast map, `P = 4X + X²`, `a = 0`,
  `I = (2)`, and `J = (16)`. Then `d = 4` and `J ≤ (8) = (d)I`.
  The 16 source points `16k` map to `64k`, giving exactly the four elements
  of `(64) = (d)J`, each with four preimages. The image theorem needs no regularity.
* In `𝔽₃[[s,t]]`, take `I = (s,t)`, `C = 𝔽₃[U]`, and let `φ` send `U` to zero.
  For `P = X²`, `a = s`, and nonprincipal `J = s²(s,t)`, the derivative `2s`
  is regular but not a unit. The bijection is from `s + s²(s,t)` to `s² + s³(s,t)`;
  the coefficient map is noninjective and `a` is outside its image.
* `J = 0` gives singleton neighborhoods, while `J = (d)I` recovers the full-neighborhood
  statements. If `d = 0`, the containment forces `J = 0`. The zero ring is also allowed.

These are mathematical examples, not additional hypotheses on the theorems.
-/

@[expose] public section

universe u v

namespace HenselianRing

/-- Over a Henselian pair, polynomial evaluation maps the `J` neighborhood of `a`
onto the `(d)J` neighborhood of its value whenever `J ≤ (d)I`, where `d` is the
derivative at `a`. No regularity or invertibility of the derivative is required. -/
theorem image_eval₂_eq_setOf_sub_mem_of_le_span_derivative_mul
    {C : Type u} {R : Type v} [Semiring C] [CommRing R]
    (I : Ideal R) [HenselianRing R I]
    (φ : C →+* R) (P : Polynomial C) (a : R) (J : Ideal R)
    (hJ : J ≤ Ideal.span {P.derivative.eval₂ φ a} * I) :
    (P.eval₂ φ) '' {b : R | b - a ∈ J} =
      {y : R | y - P.eval₂ φ a ∈ Ideal.span {P.derivative.eval₂ φ a} * J} := by
  let f : R →ₗ[R] R := LinearMap.mulLeft R (P.derivative.eval₂ φ a)
  let K : Ideal R := I ⊓ Submodule.comap f J
  have hmap (L : Ideal R) :
      Submodule.map f L = Ideal.span {P.derivative.eval₂ φ a} * L := by
    ext x
    simp only [Submodule.mem_map, f, LinearMap.mulLeft_apply, Ideal.mem_span_singleton_mul]
  have hK : Ideal.span {P.derivative.eval₂ φ a} * K = J := by
    rw [← hmap]
    change Submodule.map f (I ⊓ Submodule.comap f J) = J
    rw [← Submodule.map_inf_eq_map_inf_comap, hmap]
    exact inf_eq_right.mpr hJ
  let : HenselianRing R K := HenselianRing.of_le (show K ≤ I from inf_le_left)
  have hsq : Ideal.span {P.derivative.eval₂ φ a ^ 2} * K =
      Ideal.span {P.derivative.eval₂ φ a} * J := by
    rw [pow_two, ← Ideal.span_singleton_mul_span_singleton, mul_assoc, hK]
  simpa only [hK, hsq] using
    image_eval₂_eq_setOf_sub_mem_span_derivative_sq_mul K φ P a

/-- A regular evaluated derivative makes polynomial evaluation a bijection on any
ideal neighborhood `J ≤ (d)I`, with target the `(d)J` neighborhood of the value.
The derivative need not be a unit, and the coefficient semiring may be noncommutative. -/
theorem bijOn_eval₂_of_le_span_derivative_mul
    {C : Type u} {R : Type v} [Semiring C] [CommRing R]
    (I : Ideal R) [HenselianRing R I]
    (φ : C →+* R) (P : Polynomial C) (a : R) (J : Ideal R)
    (hJ : J ≤ Ideal.span {P.derivative.eval₂ φ a} * I)
    (hd : P.derivative.eval₂ φ a ∈ nonZeroDivisors R) :
    Set.BijOn (P.eval₂ φ)
      {b : R | b - a ∈ J}
      {y : R | y - P.eval₂ φ a ∈ Ideal.span {P.derivative.eval₂ φ a} * J} := by
  have hinj : Set.InjOn (P.eval₂ φ) {b : R | b - a ∈ J} := by
    intro b hb c hc hbc
    exact (bijOn_eval₂_of_mem_nonZeroDivisors_derivative I φ P a hd).injOn
      (hJ hb) (hJ hc) hbc
  rw [← image_eval₂_eq_setOf_sub_mem_of_le_span_derivative_mul I φ P a J hJ]
  exact hinj.bijOn_image

/-- The image of the derivative branch at `a`, constrained to the residue slice of `c`
modulo `J`, is centered at `P.eval₂ φ c`. The branch ideal is intersected with `J`
before multiplication by the derivative at `a`. -/
theorem image_eval₂_eq_setOf_sub_mem_and_sub_mem_of_sub_mem_span_derivative_mul
    {C : Type u} {R : Type v} [Semiring C] [CommRing R]
    (I : Ideal R) [HenselianRing R I]
    (φ : C →+* R) (P : Polynomial C) (a c : R) (J : Ideal R)
    (hc : c - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I) :
    (P.eval₂ φ) ''
        {b : R | b - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I ∧
          b - c ∈ J} =
      {y : R | y - P.eval₂ φ c ∈
        Ideal.span {P.derivative.eval₂ φ a} *
          (Ideal.span {P.derivative.eval₂ φ a} * I ⊓ J)} := by
  have hassoc : Associated (P.derivative.eval₂ φ c) (P.derivative.eval₂ φ a) := by
    simpa only [Polynomial.eval_map] using
      (Polynomial.associated_eval_of_sub_mem_span_mul I
        (HenselianRing.jac (R := R) (I := I)) (P.derivative.map φ) a c
        (by simpa only [Polynomial.eval_map] using hc))
  have hspan :
      Ideal.span {P.derivative.eval₂ φ c} = Ideal.span {P.derivative.eval₂ φ a} := by
    apply le_antisymm
    · apply (Ideal.span_singleton_le_iff_mem _).2
      exact (Ideal.mem_iff_of_associated hassoc).2
        (Ideal.mem_span_singleton_self _)
    · apply (Ideal.span_singleton_le_iff_mem _).2
      exact (Ideal.mem_iff_of_associated hassoc).1
        (Ideal.mem_span_singleton_self _)
  let L : Ideal R := Ideal.span {P.derivative.eval₂ φ a} * I
  let K : Ideal R := L ⊓ J
  have hsource :
      {b : R | b - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I ∧ b - c ∈ J} =
        {b : R | b - c ∈ K} := by
    ext b
    change (b - a ∈ L ∧ b - c ∈ J) ↔ (b - c ∈ L ∧ b - c ∈ J)
    constructor
    · rintro ⟨hba, hbc⟩
      exact ⟨by simpa only [sub_sub_sub_cancel_right] using L.sub_mem hba hc, hbc⟩
    · rintro ⟨hbcL, hbcJ⟩
      exact ⟨by simpa only [sub_add_sub_cancel] using L.add_mem hbcL hc, hbcJ⟩
  have hK : K ≤ Ideal.span {P.derivative.eval₂ φ c} * I := by
    rw [hspan]
    exact inf_le_left
  rw [hsource]
  change (P.eval₂ φ) '' {b : R | b - c ∈ K} =
    {y : R | y - P.eval₂ φ c ∈ Ideal.span {P.derivative.eval₂ φ a} * K}
  simpa only [hspan] using
    (image_eval₂_eq_setOf_sub_mem_of_le_span_derivative_mul I φ P c K hK)

/-- A root in the derivative branch at `a` with prescribed residue `c` modulo `J`
exists exactly when `P.eval₂ φ c` lies in the scaled intersection ideal. This
characterizes existence in the slice, without asserting uniqueness. -/
theorem exists_root_in_ideal_slice_iff
    {C : Type u} {R : Type v} [Semiring C] [CommRing R]
    (I : Ideal R) [HenselianRing R I]
    (φ : C →+* R) (P : Polynomial C) (a c : R) (J : Ideal R)
    (hc : c - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I) :
    (∃ b : R, b - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I ∧
      b - c ∈ J ∧ P.eval₂ φ b = 0) ↔
      P.eval₂ φ c ∈
        Ideal.span {P.derivative.eval₂ φ a} *
          (Ideal.span {P.derivative.eval₂ φ a} * I ⊓ J) := by
  simpa only [Set.mem_image, Set.mem_ofPred_eq, and_assoc, zero_sub, neg_mem_iff] using
    (Set.ext_iff.mp
      (image_eval₂_eq_setOf_sub_mem_and_sub_mem_of_sub_mem_span_derivative_mul
        I φ P a c J hc) (0 : R))

end HenselianRing
