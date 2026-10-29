/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localization at elements congruent to one modulo an ideal

Localizing a commutative ring at the elements congruent to `1` modulo an ideal sends that
ideal into the Jacobson radical of the localized ring.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type v} [CommRing A] [Algebra R A]

/-- Localizing at the elements congruent to `1` modulo `I` sends `I` into the Jacobson
radical. -/
theorem map_le_jacobson_of_isLocalization
    [IsLocalization ((⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) A] :
    Ideal.map (algebraMap R A) I ≤ (⊥ : Ideal A).jacobson := by
  let S : Submonoid R := (⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change algebraMap R A x ∈ (⊥ : Ideal A).jacobson
  rw [Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj S y
  have hx0 : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hs1 : Ideal.Quotient.mk I (s : R) = 1 := by
    simpa only [S, Submonoid.mem_comap, Submonoid.mem_bot] using s.property
  have hnum : x * r + (s : R) ∈ S := by
    simp only [S, Submonoid.mem_comap, Submonoid.mem_bot, map_add, map_mul, hx0,
      zero_mul, zero_add, hs1]
  have hprod :
      (algebraMap R A x * y + 1) * algebraMap R A (s : R) =
        algebraMap R A (x * r + (s : R)) := by
    rw [add_mul, one_mul, mul_assoc, hrs, map_add, map_mul]
  have hunit : IsUnit ((algebraMap R A x * y + 1) * algebraMap R A (s : R)) := by
    rw [hprod]
    exact IsLocalization.map_units (M := S) A ⟨x * r + (s : R), hnum⟩
  exact isUnit_of_mul_isUnit_left hunit

end Ideal
