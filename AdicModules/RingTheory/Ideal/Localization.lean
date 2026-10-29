/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localization at elements congruent to one modulo an ideal

For a localization of a commutative ring at the elements congruent to `1` modulo an
ideal `I`, a base-ring element becomes a unit exactly when it has a multiplicative
inverse modulo `I`. The Jacobson radical of the localization contracts to `I.jacobson`
and is the extension of `I.jacobson`. In particular, the extension of `I` lies in that
Jacobson radical.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type v} [CommRing A] [Algebra R A]

/-- An element becomes a unit after localization at the elements congruent to `1`
modulo `I` if and only if it has a multiplicative inverse modulo `I`. -/
theorem isUnit_algebraMap_iff_of_isLocalization
    [IsLocalization ((⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) A]
    (r : R) : IsUnit (algebraMap R A r) ↔ ∃ t : R, t * r - 1 ∈ I := by
  rw [IsLocalization.algebraMap_isUnit_iff
    (M := (⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I))]
  constructor
  · rintro ⟨s, hs, hdiv⟩
    obtain ⟨t, rfl⟩ := dvd_iff_exists_eq_mul_left.mp hdiv
    refine ⟨t, ?_⟩
    apply (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := I) (t * r)).mp
    simpa only [Submonoid.mem_comap, Submonoid.mem_bot] using hs
  · rintro ⟨t, ht⟩
    refine ⟨t * r, ?_, dvd_iff_exists_eq_mul_left.mpr ⟨t, rfl⟩⟩
    simpa only [Submonoid.mem_comap, Submonoid.mem_bot] using
      (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := I) (t * r)).mpr ht

/-- The Jacobson radical of a localization at the elements congruent to `1` modulo
`I` contracts to the Jacobson radical of `I`. -/
theorem comap_jacobson_bot_of_isLocalization
    [IsLocalization ((⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) A] :
    Ideal.comap (algebraMap R A) (⊥ : Ideal A).jacobson = I.jacobson := by
  apply Ideal.ext
  intro x
  rw [Ideal.mem_comap, Ideal.mem_jacobson_bot, Ideal.mem_jacobson_iff]
  constructor
  · intro h y
    have hu : IsUnit (algebraMap R A (x * y + 1)) := by
      simpa only [RingHom.map_add, RingHom.map_mul, RingHom.map_one] using
        h (algebraMap R A y)
    obtain ⟨t, ht⟩ := (I.isUnit_algebraMap_iff_of_isLocalization (A := A) (x * y + 1)).mp hu
    refine ⟨t, ?_⟩
    convert ht using 1
    ring
  · intro h y
    let S : Submonoid R := (⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)
    -- Clear a denominator to apply the relative unit criterion to a base-ring element.
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj S y
    have hx : x ∈ I.jacobson := Ideal.mem_jacobson_iff.mpr h
    have hs : (s : R) - 1 ∈ I := by
      apply (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := I) (s : R)).mp
      simpa only [S, Submonoid.mem_comap, Submonoid.mem_bot] using s.property
    have hnum : (s : R) + x * r - 1 ∈ I.jacobson := by
      have hm := I.jacobson.add_mem (Ideal.le_jacobson hs) (I.jacobson.mul_mem_left r hx)
      convert hm using 1
      ring
    obtain ⟨t, ht⟩ := Ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson
      ((s : R) + x * r) hnum
    have hu : IsUnit (algebraMap R A ((s : R) + x * r)) :=
      (I.isUnit_algebraMap_iff_of_isLocalization (A := A) _).mpr ⟨t, ht⟩
    have hprod :
        (algebraMap R A x * y + 1) * algebraMap R A (s : R) =
          algebraMap R A ((s : R) + x * r) := by
      rw [RingHom.map_add, RingHom.map_mul]
      calc
        (algebraMap R A x * y + 1) * algebraMap R A (s : R) =
            algebraMap R A x * (y * algebraMap R A (s : R)) +
              algebraMap R A (s : R) := by ring
        _ = _ := by rw [hrs]; ring
    rw [← hprod] at hu
    obtain ⟨⟨b, hb⟩, ⟨c, hc⟩⟩ := isUnit_iff_exists_and_exists.mp hu
    apply isUnit_iff_exists_and_exists.mpr
    constructor
    · refine ⟨algebraMap R A (s : R) * b, ?_⟩
      calc
        (algebraMap R A x * y + 1) * (algebraMap R A (s : R) * b) =
            ((algebraMap R A x * y + 1) * algebraMap R A (s : R)) * b := by ring
        _ = 1 := hb
    · refine ⟨c * algebraMap R A (s : R), ?_⟩
      calc
        (c * algebraMap R A (s : R)) * (algebraMap R A x * y + 1) =
            c * ((algebraMap R A x * y + 1) * algebraMap R A (s : R)) := by ring
        _ = 1 := hc

/-- The Jacobson radical of a localization at the elements congruent to `1` modulo
`I` is the extension of the Jacobson radical of `I`. -/
theorem jacobson_bot_eq_map_of_isLocalization
    [IsLocalization ((⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) A] :
    (⊥ : Ideal A).jacobson = Ideal.map (algebraMap R A) I.jacobson := by
  rw [← I.comap_jacobson_bot_of_isLocalization (A := A)]
  simpa only [Ideal.under_def] using
    (IsLocalization.map_under
      ((⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) A
      (⊥ : Ideal A).jacobson).symm

/-- Localizing at the elements congruent to `1` modulo `I` sends `I` into the Jacobson
radical. -/
theorem map_le_jacobson_of_isLocalization
    [IsLocalization ((⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) A] :
    Ideal.map (algebraMap R A) I ≤ (⊥ : Ideal A).jacobson := by
  rw [Ideal.map_le_iff_le_comap, I.comap_jacobson_bot_of_isLocalization (A := A)]
  exact Ideal.le_jacobson

end Ideal
