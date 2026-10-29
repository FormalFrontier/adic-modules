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

namespace Ideal

variable {R : Type u} [CommRing R] (I J : Ideal R)
variable {A : Type v} [CommRing A] [Algebra R A]

/-- Contracting the Jacobson radical of an extended ideal from a localization at `1 + I`
gives the Jacobson radical of its sum with `I`. -/
theorem comap_jacobson_map_of_isLocalization
    [IsLocalization ((⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) A] :
    Ideal.comap (algebraMap R A) (Ideal.map (algebraMap R A) J).jacobson =
      (I ⊔ J).jacobson := by
  let S : Submonoid R := (⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)
  have hden (s : S) : (s : R) - 1 ∈ I := by
    apply Ideal.Quotient.eq.mp
    simpa using Submonoid.mem_bot.mp (Submonoid.mem_comap.mp s.property)
  apply le_antisymm
  · intro x hx
    change algebraMap R A x ∈ (Ideal.map (algebraMap R A) J).jacobson at hx
    rw [mem_jacobson_iff] at hx ⊢
    intro r
    obtain ⟨b, hb⟩ := hx (algebraMap R A r)
    obtain ⟨⟨z, s⟩, hs⟩ := IsLocalization.surj S b
    have hz : algebraMap R A (z * r * x + z - (s : R)) ∈
        Ideal.map (algebraMap R A) J := by
      have heq : algebraMap R A (z * r * x + z - (s : R)) =
          (b * algebraMap R A r * algebraMap R A x + b - 1) *
            algebraMap R A (s : R) := by
        simp only [map_sub, map_add, map_mul]
        rw [← hs]
        ring
      rw [heq]
      exact (Ideal.map (algebraMap R A) J).mul_mem_right _ hb
    obtain ⟨t, ht, htJ⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff S A J _).mp hz
    refine ⟨t * z, ?_⟩
    have hts : t * (s : R) - 1 ∈ I := hden (⟨t, ht⟩ * s)
    have heq : t * z * r * x + t * z - 1 =
        t * (z * r * x + z - (s : R)) + (t * (s : R) - 1) := by ring
    rw [heq]
    exact (I ⊔ J).add_mem
      ((show J ≤ I ⊔ J from le_sup_right) htJ)
      ((show I ≤ I ⊔ J from le_sup_left) hts)
  · intro x hx
    change algebraMap R A x ∈ (Ideal.map (algebraMap R A) J).jacobson
    rw [mem_jacobson_iff] at hx ⊢
    intro a
    obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj S a
    obtain ⟨z, hz⟩ := hx r
    have hcert : z * r * x + z * (s : R) - 1 ∈ I ⊔ J := by
      have hi : z * ((s : R) - 1) ∈ I := I.mul_mem_left z (hden s)
      have hi' : z * ((s : R) - 1) ∈ I ⊔ J :=
        (show I ≤ I ⊔ J from le_sup_left) hi
      convert (I ⊔ J).add_mem hz hi' using 1
      ring
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hcert
    have hu : IsUnit (algebraMap R A (1 + i)) :=
      (isUnit_algebraMap_iff_of_isLocalization I (1 + i)).mpr ⟨1, by simpa using hi⟩
    obtain ⟨c, hc⟩ := hu.exists_left_inv
    have hij' : z * r * x + z * (s : R) = 1 + i + j := by
      calc
        _ = (z * r * x + z * (s : R) - 1) + 1 := by ring
        _ = (i + j) + 1 := by rw [← hij]
        _ = _ := by ring
    have heq : algebraMap R A z * algebraMap R A r * algebraMap R A x +
        algebraMap R A z * algebraMap R A (s : R) =
          algebraMap R A (1 + i) + algebraMap R A j := by
      simpa only [map_add, map_mul] using congrArg (algebraMap R A) hij'
    refine ⟨c * algebraMap R A z * algebraMap R A (s : R), ?_⟩
    have hcalc :
        c * algebraMap R A z * algebraMap R A (s : R) * a * algebraMap R A x +
            c * algebraMap R A z * algebraMap R A (s : R) - 1 =
          c * algebraMap R A j := by
      calc
        _ = c * (algebraMap R A z * (a * algebraMap R A (s : R)) *
            algebraMap R A x + algebraMap R A z * algebraMap R A (s : R)) - 1 := by ring
        _ = c * (algebraMap R A z * algebraMap R A r * algebraMap R A x +
            algebraMap R A z * algebraMap R A (s : R)) - 1 := by rw [hs]
        _ = c * (algebraMap R A (1 + i) + algebraMap R A j) - 1 := by rw [heq]
        _ = (c * algebraMap R A (1 + i) - 1) + c * algebraMap R A j := by ring
        _ = c * algebraMap R A j := by rw [hc]; ring
    rw [hcalc]
    exact (Ideal.map (algebraMap R A) J).mul_mem_left c (Ideal.mem_map_of_mem _ hj)

/-- In a localization at `1 + I`, the Jacobson radical of an extended ideal is the
extension of the Jacobson radical of its sum with `I`. -/
theorem jacobson_map_eq_map_of_isLocalization
    [IsLocalization ((⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) A] :
    (Ideal.map (algebraMap R A) J).jacobson =
      Ideal.map (algebraMap R A) (I ⊔ J).jacobson := by
  have h := IsLocalization.map_under
    ((⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) A
    (Ideal.map (algebraMap R A) J).jacobson
  rw [Ideal.under_def, comap_jacobson_map_of_isLocalization I J] at h
  exact h.symm

end Ideal
