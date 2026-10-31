/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Canonical ideal quotients and additive squares

The kernel of a nested quotient factor is the image ideal times the whole
quotient module, using its quotient-ring action. An additive commutative square
with surjective source projection and the prescribed ideal-multiple kernels
transports residual bijectivity to bijectivity of `LinearMap.reduceModIdeal`.
The residual groups need not be commutative and carry no scalar action.

The image of an ideal in its power quotient is nilpotent, including at exponent
zero in the zero quotient ring.

## References

These results use Mathlib's quotient and kernel APIs by Johannes Hölzl,
Mario Carneiro, Kevin Buzzard and Yury Kudryashov; its quotient-ring module
action by Pierre-Alexandre Bazin; its ideal-image and scalar-restriction APIs;
and Judith Ludwig and Christian Merten's `LinearMap.reduceModIdeal`.
-/

@[expose] public section

universe uR uM uA uX uY uX₀ uY₀

/-- The kernel of a nested quotient factor is the image ideal times the whole
module, with the canonical quotient-ring scalar action. -/
theorem Submodule.factor_eq_zero_iff_mem_map_smul_top
    {R : Type uR} [CommRing R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (J K : Ideal R) (hJK : J ≤ K)
    (x : M ⧸ (J • (⊤ : Submodule R M))) :
    Submodule.factor
        (Submodule.smul_mono_left hJK :
          J • (⊤ : Submodule R M) ≤ K • ⊤) x = 0 ↔
      x ∈ (K.map (Ideal.Quotient.mk J)) •
        (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))) := by
  have hker :
      (Submodule.factor (Submodule.smul_mono_left hJK) :
        (M ⧸ (J • (⊤ : Submodule R M))) →ₗ[R]
          M ⧸ (K • (⊤ : Submodule R M))).ker =
        K • (⊤ : Submodule R (M ⧸ (J • (⊤ : Submodule R M)))) := by
    rw [Submodule.ker_mapQ, Submodule.comap_id, Submodule.map_smul'', Submodule.map_top,
      Submodule.range_mkQ]
  have hsmul := Submodule.restrictScalars_map_smul_eq (R := R ⧸ J) K
    (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))))
  change x ∈ (Submodule.factor (Submodule.smul_mono_left hJK)).ker ↔ _
  rw [hker]
  exact Iff.symm (SetLike.ext_iff.mp hsmul x)

namespace LinearMap

section QuotientSquare

variable {A : Type uA} [CommRing A]
variable {X : Type uX} [AddCommGroup X] [Module A X]
variable {Y : Type uY} [AddCommGroup Y] [Module A Y]
variable {X₀ : Type uX₀} [AddGroup X₀]
variable {Y₀ : Type uY₀} [AddGroup Y₀]

/-- An additive residual isomorphism detects bijectivity modulo an ideal.
Only the source quotient map needs an explicit surjectivity hypothesis. -/
theorem bijective_reduceModIdeal_of_addHom_square
    (J : Ideal A) (f : X →ₗ[A] Y) (rX : X →+ X₀) (rY : Y →+ Y₀)
    (hX : Function.Surjective rX)
    (kX : ∀ x, rX x = 0 ↔ x ∈ J • (⊤ : Submodule A X))
    (kY : ∀ y, rY y = 0 ↔ y ∈ J • (⊤ : Submodule A Y))
    (g₀ : X₀ →+ Y₀) (hg₀ : Function.Bijective g₀)
    (comm : ∀ x, rY (f x) = g₀ (rX x)) :
    Function.Bijective (f.reduceModIdeal J) := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A X)) x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A X)) y
    apply (Submodule.Quotient.eq _).2
    apply (kX (x - y)).1
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply hg₀.1
    have hmem : f x - f y ∈ J • (⊤ : Submodule A Y) :=
      (Submodule.Quotient.eq _).1 (by
        simpa only [LinearMap.reduceModIdeal_apply] using hxy)
    have hzero := (kY (f x - f y)).2 hmem
    rw [map_sub] at hzero
    rw [← comm x, ← comm y]
    exact sub_eq_zero.mp hzero
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A Y)) y
    obtain ⟨x₀, hx₀⟩ := hg₀.2 (rY y)
    obtain ⟨x, hx⟩ := hX x₀
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [LinearMap.reduceModIdeal_apply]
    apply (Submodule.Quotient.eq _).2
    apply (kY (f x - y)).1
    rw [map_sub, comm x, hx, hx₀, sub_self]

end QuotientSquare

end LinearMap

/-- The image of an ideal in the quotient by its nth power is nilpotent. -/
theorem Ideal.isNilpotent_map_quotient_pow
    {R : Type uR} [CommRing R] (I : Ideal R) (n : ℕ) :
    IsNilpotent (I.map (Ideal.Quotient.mk (I ^ n))) := by
  use n
  simp only [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]
