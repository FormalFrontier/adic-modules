/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Composite valuation subrings

This file constructs the composite of a valuation subring of a field and a
valuation subring of its residue field.
-/

@[expose] public section

open IsLocalRing

namespace ValuationSubring

universe u

variable {K : Type u} [Field K]

/-- The composite of a valuation subring `A` of a field with a valuation
subring `W` of the residue field of `A`. Its elements are exactly the elements
of `A` whose residue belongs to `W`. -/
noncomputable def composite (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) : ValuationSubring K where
  carrier := {x | ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∈ W}
  zero_mem' := ⟨A.zero_mem, by
    change residue A (0 : A) ∈ W
    simp⟩
  one_mem' := ⟨A.one_mem, by
    change residue A (1 : A) ∈ W
    simp⟩
  add_mem' := by
    rintro x y ⟨hxA, hxW⟩ ⟨hyA, hyW⟩
    refine ⟨A.add_mem x y hxA hyA, ?_⟩
    change residue A (⟨x, hxA⟩ + ⟨y, hyA⟩) ∈ W
    simpa only [map_add] using W.add_mem _ _ hxW hyW
  neg_mem' := by
    rintro x ⟨hxA, hxW⟩
    refine ⟨A.neg_mem x hxA, ?_⟩
    change residue A (-⟨x, hxA⟩) ∈ W
    simpa only [map_neg] using W.neg_mem _ hxW
  mul_mem' := by
    rintro x y ⟨hxA, hxW⟩ ⟨hyA, hyW⟩
    refine ⟨A.mul_mem x y hxA hyA, ?_⟩
    change residue A (⟨x, hxA⟩ * ⟨y, hyA⟩) ∈ W
    simpa only [map_mul] using W.mul_mem _ _ hxW hyW
  mem_or_inv_mem' := by
    intro x
    by_cases hxA : x ∈ A
    · let xA : A := ⟨x, hxA⟩
      by_cases hxW : residue A xA ∈ W
      · exact Or.inl ⟨hxA, hxW⟩
      · right
        have hx0 : residue A xA ≠ 0 := fun h ↦ hxW (h ▸ W.zero_mem)
        have hxUnit : IsUnit xA := (residue_ne_zero_iff_isUnit xA).mp hx0
        obtain ⟨ux, hux⟩ := hxUnit
        have hInvW : (residue A xA)⁻¹ ∈ W :=
          (W.mem_or_inv_mem (residue A xA)).resolve_left hxW
        have huxK : ((ux : A) : K) = x := by
          simpa only [xA] using congrArg Subtype.val hux
        have huxInvK : ((↑(ux⁻¹) : A) : K) = x⁻¹ := by
          calc
            ((↑(ux⁻¹) : A) : K) =
                ↑(Units.map A.subtype.toMonoidHom (ux⁻¹)) :=
              (Units.coe_map A.subtype.toMonoidHom (ux⁻¹)).symm
            _ = ↑((Units.map A.subtype.toMonoidHom ux)⁻¹) := by rw [map_inv]
            _ = (↑(Units.map A.subtype.toMonoidHom ux) : K)⁻¹ :=
              Units.val_inv_eq_inv_val _
            _ = ((ux : A) : K)⁻¹ := by rfl
            _ = x⁻¹ := by rw [huxK]
        have hxInvA : x⁻¹ ∈ A := by
          rw [← huxInvK]
          exact (↑(ux⁻¹) : A).property
        refine ⟨hxInvA, ?_⟩
        have hxInvEq : (⟨x⁻¹, hxInvA⟩ : A) = ↑(ux⁻¹) := by
          ext
          exact huxInvK.symm
        rw [hxInvEq]
        have hResidueInv : residue A (↑(ux⁻¹) : A) = (residue A xA)⁻¹ := by
          calc
            residue A (↑(ux⁻¹) : A) =
                ↑(Units.map (residue A).toMonoidHom (ux⁻¹)) :=
              (Units.coe_map (residue A).toMonoidHom (ux⁻¹)).symm
            _ = ↑((Units.map (residue A).toMonoidHom ux)⁻¹) := by rw [map_inv]
            _ = (↑(Units.map (residue A).toMonoidHom ux) : ResidueField A)⁻¹ :=
              Units.val_inv_eq_inv_val _
            _ = (residue A (↑ux : A))⁻¹ := by rfl
            _ = (residue A xA)⁻¹ := by rw [hux]
        rw [hResidueInv]
        exact hInvW
    · right
      have hxInvNonunit : x⁻¹ ∈ A.nonunits :=
        A.inv_mem_nonunits_iff.mpr (Or.inr hxA)
      have hxInvA : x⁻¹ ∈ A := A.nonunits_subset hxInvNonunit
      refine ⟨hxInvA, ?_⟩
      rw [(residue_eq_zero_iff _).mpr (A.coe_mem_nonunits_iff.mp hxInvNonunit)]
      exact W.zero_mem

@[simp]
theorem mem_composite {A : ValuationSubring K} {W : ValuationSubring (ResidueField A)}
    {x : K} : x ∈ A.composite W ↔ ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∈ W :=
  Iff.rfl

/-- A composite valuation subring is contained in its first factor. -/
theorem composite_le (A : ValuationSubring K) (W : ValuationSubring (ResidueField A)) :
    A.composite W ≤ A := fun _ hx ↦ (mem_composite.mp hx).choose

/-- The algebra structure on the first factor induced by the inclusion of the
composite valuation subring. -/
noncomputable instance compositeAlgebra (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) : Algebra (A.composite W) A :=
  (A.composite W).inclusion A (A.composite_le W) |>.toAlgebra

@[simp]
theorem composite_top (A : ValuationSubring K) : A.composite ⊤ = A := by
  apply le_antisymm (A.composite_le ⊤)
  intro x hx
  exact ⟨hx, ValuationSubring.mem_top _⟩

/-- The canonical residue map from a composite valuation subring to its second
factor. -/
noncomputable def compositeResidue (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) : A.composite W →+* W :=
  ((residue A).comp ((A.composite W).inclusion A (A.composite_le W))).codRestrict W
    fun x ↦ (mem_composite.mp x.property).choose_spec

@[simp]
theorem compositeResidue_apply (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) (x : A.composite W) :
    A.compositeResidue W x = residue A ⟨x, (A.composite_le W) x.property⟩ :=
  rfl

/-- The canonical residue map from a composite valuation subring onto its
second factor is surjective. -/
theorem compositeResidue_surjective (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) :
    Function.Surjective (A.compositeResidue W) := by
  intro w
  obtain ⟨a, ha⟩ := residue_surjective (R := A) (w : ResidueField A)
  let x : A.composite W := ⟨a, a.property, by simpa only [ha] using w.property⟩
  refine ⟨x, ?_⟩
  ext
  exact ha

/-- The distinguished prime of a composite valuation subring: the maximal
ideal of its first factor, pulled back along the inclusion. -/
noncomputable def compositeIdeal (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) :
    Ideal (A.composite W) :=
  (A.composite W).idealOfLE A (A.composite_le W)

noncomputable instance compositeIdeal_isPrime (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) : (A.compositeIdeal W).IsPrime :=
  ValuationSubring.prime_idealOfLE _ _ _

/-- Localizing a composite valuation subring at its distinguished prime
recovers its first factor as a valuation subring of the ambient field. -/
@[simp]
theorem ofPrime_compositeIdeal (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) :
    (A.composite W).ofPrime (A.compositeIdeal W) = A :=
  (A.composite W).ofPrime_idealOfLE A (A.composite_le W)

/-- The first factor is canonically equivalent, over the composite, to the
coarsening at the distinguished prime. -/
noncomputable def ofPrimeCompositeIdealAlgEquiv (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) :
    (A.composite W).ofPrime (A.compositeIdeal W) ≃ₐ[A.composite W] A where
  __ := RingEquiv.subringCongr <|
    congrArg ValuationSubring.toSubring (A.ofPrime_compositeIdeal W)
  commutes' _ := rfl

/-- The first factor is a localization of the composite at the distinguished
prime. -/
noncomputable instance composite_isLocalizationAtPrime (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) :
    IsLocalization.AtPrime A (A.compositeIdeal W) :=
  IsLocalization.isLocalization_of_algEquiv _ (A.ofPrimeCompositeIdealAlgEquiv W)

/-- The kernel of the composite residue map is its distinguished prime. -/
theorem ker_compositeResidue (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) :
    RingHom.ker (A.compositeResidue W) = A.compositeIdeal W := by
  ext x
  rw [RingHom.mem_ker]
  change A.compositeResidue W x = 0 ↔
    (A.composite W).inclusion A (A.composite_le W) x ∈ maximalIdeal A
  rw [Subtype.ext_iff]
  exact residue_eq_zero_iff _

@[simp]
theorem mem_compositeIdeal (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) (x : A.composite W) :
    x ∈ A.compositeIdeal W ↔
      residue A ⟨x, (A.composite_le W) x.property⟩ = 0 := by
  rw [← A.ker_compositeResidue W, RingHom.mem_ker, Subtype.ext_iff]
  rfl

/-- Quotienting a composite valuation subring by its distinguished prime
recovers its second factor. -/
noncomputable def quotientCompositeIdealEquiv (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) :
    (A.composite W ⧸ A.compositeIdeal W) ≃+* W :=
  (Ideal.quotEquivOfEq (A.ker_compositeResidue W).symm).trans
    (RingHom.quotientKerEquivOfSurjective (A.compositeResidue_surjective W))

@[simp]
theorem quotientCompositeIdealEquiv_mk (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) (x : A.composite W) :
    A.quotientCompositeIdealEquiv W (Ideal.Quotient.mk (A.compositeIdeal W) x) =
      A.compositeResidue W x := by
  rfl

/-- A local inclusion between valuation subrings of the same field is an
equality. -/
theorem eq_of_le_of_isLocalHom {R S : ValuationSubring K} (h : R ≤ S)
    [IsLocalHom (R.inclusion S h)] : R = S := by
  have hlocal : IsLocalHom (R.inclusion S h) := inferInstance
  change IsLocalHom (Subring.inclusion h) at hlocal
  apply ValuationSubring.toLocalSubring_injective
  exact R.isMax_toLocalSubring.eq_of_le ((LocalSubring.le_def).2 ⟨h, hlocal⟩)

end ValuationSubring
