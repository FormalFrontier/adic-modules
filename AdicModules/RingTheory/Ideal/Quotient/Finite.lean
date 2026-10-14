/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Kenny Lau, Patrick Massot, Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import AdicModules.RingTheory.Ideal.Operations

/-!
# Finite Chinese remainder equivalence for two-sided ideals

For a finite pairwise comaximal family of two-sided ideals in a ring, the
canonical map from the quotient by their intersection to the product of the
individual quotients is bijective and determines a ring equivalence. The ring
need not be commutative.

The map, its formulas on representatives and its injectivity are Mathlib's
`Ideal.quotientInfToPiQuotient`, `Ideal.quotientInfToPiQuotient_mk`,
`Ideal.quotientInfToPiQuotient_mk'` and `Ideal.quotientInfToPiQuotient_inj`.
The proof extends Mathlib's commutative `Ideal.quotientInfToPiQuotient_surj`,
using `Ideal.sup_iInf_eq_top` for the finite-intersection step.

`Ideal.quotientInfRingEquivPiQuotientOfPairwiseSupEqTop` packages this same
canonical map as a ring equivalence. In a commutative ring it agrees with
Mathlib's `Ideal.quotientInfRingEquivPiQuotient` after converting the coprimality
guard to pairwise comaximality.

For the common left action of `R`, the image of the class of `1` generates the
product as a module. Its scalar kernel is the intersection of the ideals.

The same canonical map is surjective for independently chosen natural powers
of the original pairwise comaximal family. Zeroth powers are allowed; the
pairwise comaximality of powers follows from `Ideal.pow_sup_pow_eq_top`.
-/

@[expose] public section

universe u v

namespace Ideal

/-- Each component of the canonical Chinese remainder map is the quotient factor. -/
theorem quotientInfToPiQuotient_apply_apply
    {R : Type u} {ι : Type v} [Ring R]
    (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
    (q : R ⧸ ⨅ j, I j) (i : ι) :
    quotientInfToPiQuotient I q i = Quotient.factor (iInf_le I i) q := by
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective q
  rw [quotientInfToPiQuotient_mk', Quotient.factor_mk]

/-- The canonical Chinese remainder map commutes componentwise with quotient factors
for a pointwise inclusion of two-sided ideal families. -/
theorem quotientInfToPiQuotient_factor_apply_apply
    {R : Type u} {ι : Type v} [Ring R]
    (I J : ι → Ideal R) [∀ i, (I i).IsTwoSided] [∀ i, (J i).IsTwoSided]
    (h : ∀ i, I i ≤ J i) (q : R ⧸ ⨅ j, I j) (i : ι) :
    Quotient.factor (h i) (quotientInfToPiQuotient I q i) =
      quotientInfToPiQuotient J (Quotient.factor (iInf_mono h) q) i := by
  simp only [quotientInfToPiQuotient_apply_apply, Quotient.factor_comp_apply]

/-- The canonical Chinese remainder map is surjective for a finite pairwise
comaximal family of two-sided ideals in a possibly noncommutative ring.
This extends Mathlib's `Ideal.quotientInfToPiQuotient_surj`, with comaximality
expressed directly as a supremum equal to the top ideal. -/
theorem quotientInfToPiQuotient_surj_of_pairwise_sup_eq_top
    {R : Type u} {ι : Type v} [Ring R] [Finite ι]
    {I : ι → Ideal R} [∀ i, (I i).IsTwoSided]
    (hI : Pairwise (fun i j => I i ⊔ I j = ⊤)) :
    Function.Surjective (quotientInfToPiQuotient I) := by
  classical
  cases nonempty_fintype ι
  intro g
  choose f hf using fun i ↦ Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, Quotient.mk (I i) e = 1 ∧
      ∀ j, j ≠ i → Quotient.mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, I i ⊔ I j = ⊤ := by
      intro j hj
      exact hI (by simpa [ne_comm] using hj)
    obtain ⟨u, hu, e, he, hue⟩ :=
      Submodule.mem_sup.mp ((eq_top_iff_one _).mp (sup_iInf_eq_top hI'))
    replace he : ∀ j, j ≠ i → e ∈ I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, Quotient.eq_zero_iff_mem.mpr hu]
    · exact fun j hj ↦ Quotient.eq_zero_iff_mem.mpr (he j hj)
  choose e he using key
  refine ⟨Quotient.mk _ (∑ i, f i * e i), ?_⟩
  funext i
  rw [quotientInfToPiQuotient_mk', map_sum, Fintype.sum_eq_single i]
  · simp [(he i).1, hf]
  · intro j hj
    simp [(he j).2 i hj.symm]

section Equivalence

variable {R : Type u} {ι : Type v} [Ring R] [Finite ι]
  (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
  (hI : Pairwise (fun i j => I i ⊔ I j = ⊤))

/-- The Chinese remainder ring equivalence for a finite pairwise comaximal family
of two-sided ideals in a possibly noncommutative ring. Its forward homomorphism
is Mathlib's `Ideal.quotientInfToPiQuotient`. -/
noncomputable def quotientInfRingEquivPiQuotientOfPairwiseSupEqTop :
    (R ⧸ ⨅ i, I i) ≃+* ((i : ι) → R ⧸ I i) :=
  { Equiv.ofBijective _ ⟨quotientInfToPiQuotient_inj I,
      quotientInfToPiQuotient_surj_of_pairwise_sup_eq_top hI⟩,
    quotientInfToPiQuotient I with }

@[simp]
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_toRingHom :
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).toRingHom =
      quotientInfToPiQuotient I :=
  rfl

@[simp]
theorem coe_quotientInfRingEquivPiQuotientOfPairwiseSupEqTop :
    ⇑(quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI) =
      ⇑(quotientInfToPiQuotient I) :=
  rfl

theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_apply
    (z : R ⧸ ⨅ i, I i) :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI z =
      quotientInfToPiQuotient I z :=
  rfl

@[simp]
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_mk (r : R) :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI
        (Quotient.mk (⨅ i, I i) r) =
      fun i => Quotient.mk (I i) r :=
  rfl

@[simp]
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_mk_apply (r : R) (i : ι) :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI
        (Quotient.mk (⨅ j, I j) r) i =
      Quotient.mk (I i) r :=
  rfl

/-- Each component of the equivalence is the canonical quotient factor. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_apply_apply
    (z : R ⧸ ⨅ j, I j) (i : ι) :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI z i =
      Quotient.factor (iInf_le I i) z := by
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective z
  rfl

@[simp]
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_mk (r : R) :
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm
        (fun i => Quotient.mk (I i) r) =
      Quotient.mk (⨅ i, I i) r :=
  (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm_apply_apply
    (Quotient.mk (⨅ i, I i) r)

/-! ## Inverse classes and representatives -/

/-- The inverse class has the prescribed image under the canonical quotient map. -/
@[simp]
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_apply_symm_apply
    (g : (i : ι) → R ⧸ I i) :
    quotientInfToPiQuotient I
        ((quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g) = g :=
  (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).apply_symm_apply g

/-- Each canonical factor of the inverse class is the prescribed component. -/
@[simp]
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_factor_symm_apply
    (g : (i : ι) → R ⧸ I i) (i : ι) :
    Quotient.factor (iInf_le I i)
        ((quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g) = g i := by
  rw [← quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_apply_apply I hI,
    RingEquiv.apply_symm_apply]

/-- A quotient class is the inverse image exactly when its canonical image is
the prescribed tuple. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_apply_eq_iff
    (g : (i : ι) → R ⧸ I i) (z : R ⧸ ⨅ i, I i) :
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g = z ↔
      quotientInfToPiQuotient I z = g := by
  rw [RingEquiv.symm_apply_eq,
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_apply, eq_comm]

/-- A ring element represents the inverse class exactly when all its residues
are the prescribed components. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_apply_eq_mk_iff
    (g : (i : ι) → R ⧸ I i) (r : R) :
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g =
        Quotient.mk (⨅ i, I i) r ↔
      ∀ i, Quotient.mk (I i) r = g i := by
  rw [quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_apply_eq_iff,
    quotientInfToPiQuotient_mk]
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- The representative criterion with the quotient class on the left. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_mk_eq_symm_apply_iff
    (g : (i : ι) → R ⧸ I i) (r : R) :
    Quotient.mk (⨅ i, I i) r =
        (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g ↔
      ∀ i, Quotient.mk (I i) r = g i :=
  eq_comm.trans
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_apply_eq_mk_iff I hI g r)

/-- Every tuple has a unique preimage as a quotient class. Ring representatives
need not be unique. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_existsUnique_preimage
    {R : Type u} {ι : Type v} [Ring R] [Finite ι]
    (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
    (hI : Pairwise (fun i j => I i ⊔ I j = ⊤)) (g : (i : ι) → R ⧸ I i) :
    ∃! z : R ⧸ ⨅ i, I i, quotientInfToPiQuotient I z = g := by
  refine ⟨(quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g,
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_apply_symm_apply I hI g, ?_⟩
  intro z hz
  exact ((quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_apply_eq_iff
    I hI g z).mpr hz).symm

/-- Every tuple of quotient classes admits a simultaneous ring representative. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_exists_forall_mk_eq
    {R : Type u} {ι : Type v} [Ring R] [Finite ι]
    (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
    (hI : Pairwise (fun i j => I i ⊔ I j = ⊤)) (g : (i : ι) → R ⧸ I i) :
    ∃ r : R, ∀ i, Quotient.mk (I i) r = g i := by
  obtain ⟨r, hr⟩ := Quotient.mk_surjective
    ((quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g)
  exact ⟨r, (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_mk_eq_symm_apply_iff
    I hI g r).mp hr⟩

/-- Relative to any representative of the inverse class, all simultaneous
representatives form its additive coset modulo the intersection ideal. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_forall_mk_eq_iff_sub_mem
    (g : (i : ι) → R ⧸ I i) {r₀ : R}
    (hr₀ : Quotient.mk (⨅ i, I i) r₀ =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g) (r : R) :
    (∀ i, Quotient.mk (I i) r = g i) ↔ r - r₀ ∈ ⨅ i, I i := by
  rw [← quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_mk_eq_symm_apply_iff I hI g r,
    ← hr₀, Quotient.mk_eq_mk_iff_sub_mem]

/-- Equivalently, simultaneous representatives differ from a fixed one by an
element of every ideal in the family. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_forall_mk_eq_iff_forall_sub_mem
    (g : (i : ι) → R ⧸ I i) {r₀ : R}
    (hr₀ : Quotient.mk (⨅ i, I i) r₀ =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g) (r : R) :
    (∀ i, Quotient.mk (I i) r = g i) ↔ ∀ i, r - r₀ ∈ I i :=
  (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_forall_mk_eq_iff_sub_mem
    I hI g hr₀ r).trans mem_iInf

end Equivalence

/-- All solutions of an arbitrary system of ideal congruences form the additive
coset of the intersection through any one solution. No finiteness,
comaximality or two-sidedness assumption is needed. -/
theorem forall_sub_mem_iff_sub_mem_iInf
    {R : Type u} {ι : Type v} [Ring R] (I : ι → Ideal R)
    (a : ι → R) {r₀ : R} (hr₀ : ∀ i, r₀ - a i ∈ I i) (r : R) :
    (∀ i, r - a i ∈ I i) ↔ r - r₀ ∈ ⨅ i, I i := by
  rw [mem_iInf]
  constructor
  · intro h i
    simpa only [sub_sub_sub_cancel_right] using (I i).sub_mem (h i) (hr₀ i)
  · intro h i
    simpa only [sub_add_sub_cancel] using (I i).add_mem (h i) (hr₀ i)

/-- In a commutative ring the equivalence for pairwise comaximal ideals agrees
with Mathlib's Chinese remainder equivalence for pairwise coprime ideals. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_eq_quotientInfRingEquivPiQuotient
    {R : Type u} {ι : Type v} [CommRing R] [Finite ι]
    (I : ι → Ideal R) (hI : Pairwise (fun i j => IsCoprime (I i) (I j))) :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I
        (fun i j hij => isCoprime_iff_sup_eq.mp (hI hij)) =
      quotientInfRingEquivPiQuotient I hI := by
  apply RingEquiv.ext
  intro z
  exact quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_apply I _ z

/-- In a commutative ring the inverse equivalence agrees with Mathlib's inverse
as a ring equivalence, not merely on its range. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_eq_quotientInfRingEquivPiQuotient_symm
    {R : Type u} {ι : Type v} [CommRing R] [Finite ι]
    (I : ι → Ideal R) (hI : Pairwise (fun i j => IsCoprime (I i) (I j))) :
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I
        (fun i j hij => isCoprime_iff_sup_eq.mp (hI hij))).symm =
      (quotientInfRingEquivPiQuotient I hI).symm :=
  congrArg RingEquiv.symm
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_eq_quotientInfRingEquivPiQuotient I hI)

/-- Mathlib's commutative inverse is computed by the same simultaneous-residue
criterion as the pairwise comaximal equivalence. -/
theorem quotientInfRingEquivPiQuotient_symm_apply_eq_mk_iff
    {R : Type u} {ι : Type v} [CommRing R] [Finite ι]
    (I : ι → Ideal R) (hI : Pairwise (fun i j => IsCoprime (I i) (I j)))
    (g : (i : ι) → R ⧸ I i) (r : R) :
    (quotientInfRingEquivPiQuotient I hI).symm g = Quotient.mk (⨅ i, I i) r ↔
      ∀ i, Quotient.mk (I i) r = g i := by
  rw [← quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_eq_quotientInfRingEquivPiQuotient
    I hI]
  exact quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_apply_eq_mk_iff I _ g r

/-- The canonical Chinese remainder map is surjective for independently chosen
natural powers of a finite pairwise comaximal family of two-sided ideals.
Comaximality is required only of the original family, and exponents may be zero. -/
theorem quotientInfToPiQuotient_pow_surj_of_pairwise_sup_eq_top
    {R : Type u} {ι : Type v} [Ring R] [Finite ι]
    {I : ι → Ideal R} [∀ i, (I i).IsTwoSided]
    (hI : Pairwise (fun i j => I i ⊔ I j = ⊤)) (n : ι → ℕ) :
    Function.Surjective (quotientInfToPiQuotient (fun i => I i ^ n i)) := by
  apply quotientInfToPiQuotient_surj_of_pairwise_sup_eq_top (I := fun i => I i ^ n i)
  intro i j hij
  exact pow_sup_pow_eq_top (hI hij)

section Reduction

variable {R : Type u} {ι : Type v} [Ring R] [Finite ι]
  (I J : ι → Ideal R) [∀ i, (I i).IsTwoSided] [∀ i, (J i).IsTwoSided]
  (hI : Pairwise (fun i j => I i ⊔ I j = ⊤))
  (hJ : Pairwise (fun i j => J i ⊔ J j = ⊤)) (h : ∀ i, I i ≤ J i)

/-- The canonical equivalences commute componentwise with reduction from a finer
family of ideals to a coarser family. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_factor_apply_apply
    (q : R ⧸ ⨅ j, I j) (i : ι) :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop J hJ
        (Quotient.factor (iInf_mono h) q) i =
      Quotient.factor (h i)
        (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI q i) := by
  simpa only [quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_apply] using
    (quotientInfToPiQuotient_factor_apply_apply I J h q i).symm

/-- The forward Chinese remainder square commutes as an equality of functions. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_comp_factor :
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop J hJ) ∘
        Quotient.factor (iInf_mono h) =
      (fun g : (i : ι) → R ⧸ I i => fun i => Quotient.factor (h i) (g i)) ∘
        (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI) := by
  funext q i
  exact quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_factor_apply_apply I J hI hJ h q i

/-- Reduction of the inverse Chinese remainder class equals the inverse class of
the reduced coordinates. No choice of representatives is involved. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_factor_symm_apply_of_le
    (g : (i : ι) → R ⧸ I i) :
    Quotient.factor (iInf_mono h)
        ((quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g) =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop J hJ).symm
        (fun i => Quotient.factor (h i) (g i)) := by
  apply (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop J hJ).injective
  rw [(quotientInfRingEquivPiQuotientOfPairwiseSupEqTop J hJ).apply_symm_apply]
  funext i
  rw [quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_factor_apply_apply I J hI hJ h,
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).apply_symm_apply]

/-- The inverse Chinese remainder square commutes as an equality of functions. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_factor_comp_symm :
    Quotient.factor (iInf_mono h) ∘
        (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop J hJ).symm ∘
        (fun g : (i : ι) → R ⧸ I i => fun i => Quotient.factor (h i) (g i)) := by
  funext g
  exact quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_factor_symm_apply_of_le I J hI hJ h g

end Reduction

section PowerReduction

variable {R : Type u} {ι : Type v} [Ring R] [Finite ι]
  (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
  (hI : Pairwise (fun i j => I i ⊔ I j = ⊤))
  (n m : ι → ℕ) (hnm : ∀ i, n i ≤ m i)

/-- Reducing independent coordinate precisions commutes with the canonical
Chinese remainder equivalences. Larger exponents are the finer precision. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_pow_factor_apply_apply
    (q : R ⧸ ⨅ j, I j ^ m j) (i : ι) :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop (fun j => I j ^ n j)
        (pairwise_sup_eq_top_pow I hI n)
        (Quotient.factor
          (iInf_mono (fun j => pow_le_pow_right (I := I j) (hnm j))) q) i =
      Quotient.factor (pow_le_pow_right (I := I i) (hnm i))
        (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop (fun j => I j ^ m j)
          (pairwise_sup_eq_top_pow I hI m) q i) := by
  exact quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_factor_apply_apply
    (fun j => I j ^ m j) (fun j => I j ^ n j)
    (pairwise_sup_eq_top_pow I hI m) (pairwise_sup_eq_top_pow I hI n)
    (fun j => pow_le_pow_right (hnm j)) q i

/-- The forward precision-reduction square is an equality of functions, with no
positivity requirement on either family of precisions. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_pow_comp_factor :
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop (fun i => I i ^ n i)
        (pairwise_sup_eq_top_pow I hI n)) ∘
        Quotient.factor (iInf_mono (fun i => pow_le_pow_right (I := I i) (hnm i))) =
      (fun g : (i : ι) → R ⧸ I i ^ m i =>
        fun i => Quotient.factor (pow_le_pow_right (I := I i) (hnm i)) (g i)) ∘
        (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop (fun i => I i ^ m i)
          (pairwise_sup_eq_top_pow I hI m)) := by
  funext q i
  exact quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_pow_factor_apply_apply I hI n m hnm q i

/-- Reducing the inverse class at fine coordinate precisions gives the inverse
class of the reduced residues at coarse precisions, including zero precisions. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_pow_factor_symm_apply
    (g : (i : ι) → R ⧸ I i ^ m i) :
    Quotient.factor (iInf_mono (fun i => pow_le_pow_right (I := I i) (hnm i)))
        ((quotientInfRingEquivPiQuotientOfPairwiseSupEqTop (fun i => I i ^ m i)
          (pairwise_sup_eq_top_pow I hI m)).symm g) =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop (fun i => I i ^ n i)
        (pairwise_sup_eq_top_pow I hI n)).symm
        (fun i => Quotient.factor (pow_le_pow_right (I := I i) (hnm i)) (g i)) := by
  exact quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_factor_symm_apply_of_le
    (fun i => I i ^ m i) (fun i => I i ^ n i)
    (pairwise_sup_eq_top_pow I hI m) (pairwise_sup_eq_top_pow I hI n)
    (fun i => pow_le_pow_right (hnm i)) g

/-- The inverse precision-reduction square commutes as an equality of functions. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_pow_factor_comp_symm :
    Quotient.factor (iInf_mono (fun i => pow_le_pow_right (I := I i) (hnm i))) ∘
        (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop (fun i => I i ^ m i)
          (pairwise_sup_eq_top_pow I hI m)).symm =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop (fun i => I i ^ n i)
        (pairwise_sup_eq_top_pow I hI n)).symm ∘
        (fun g : (i : ι) → R ⧸ I i ^ m i =>
          fun i => Quotient.factor (pow_le_pow_right (I := I i) (hnm i)) (g i)) := by
  funext g
  exact quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_pow_factor_symm_apply I hI n m hnm g

end PowerReduction

/-! ## The canonical scalar action -/

/-- The canonical Chinese remainder homomorphism has the same underlying function
as the product of the canonical linear quotient factors. No finiteness or
comaximality is needed for this identification. -/
theorem quotientInfToPiQuotient_eq_pi_factor
    {R : Type u} {ι : Type v} [Ring R]
    (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] :
    (quotientInfToPiQuotient I : (R ⧸ ⨅ i, I i) → ((i : ι) → R ⧸ I i)) =
      (LinearMap.pi (fun i => Submodule.factor (iInf_le I i)) :
        (R ⧸ ⨅ i, I i) → ((i : ι) → R ⧸ I i)) := by
  funext z
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective z
  rfl

/-- The canonical Chinese remainder map preserves the common left action of `R`
on the quotient modules and their product, for an arbitrary index type. -/
@[simp]
theorem quotientInfToPiQuotient_smul
    {R : Type u} {ι : Type v} [Ring R]
    (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
    (r : R) (z : R ⧸ ⨅ i, I i) :
    quotientInfToPiQuotient I (r • z) = r • quotientInfToPiQuotient I z := by
  rw [quotientInfToPiQuotient_eq_pi_factor I]
  exact (LinearMap.pi (fun i => Submodule.factor (iInf_le I i))).map_smul r z

section LinearEquivalence

variable {R : Type u} {ι : Type v} [Ring R] [Finite ι]
  (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
  (hI : Pairwise (fun i j => I i ⊔ I j = ⊤))

/-- The Chinese remainder ring equivalence preserves the canonical left action
of the common base ring on all the quotient modules. -/
@[simp]
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_smul
    (r : R) (z : R ⧸ ⨅ i, I i) :
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI (r • z) =
      r • quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI z :=
  quotientInfToPiQuotient_smul I r z

/-- The inverse Chinese remainder equivalence preserves the canonical left action
of the common base ring on the quotient modules and their product. -/
@[simp]
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_smul
    (r : R) (g : (i : ι) → R ⧸ I i) :
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm (r • g) =
      r • (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g := by
  apply (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).injective
  rw [RingEquiv.apply_symm_apply,
    quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_smul, RingEquiv.apply_symm_apply]

/-- A scalar kills the image of the class of `1` under the Chinese remainder
equivalence exactly when it belongs to the intersection of the ideals. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_smul_mk_one_eq_zero_iff
    (a : R) :
    a • quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI
        (Quotient.mk (⨅ i, I i) (1 : R)) = 0 ↔ a ∈ ⨅ i, I i := by
  rw [← quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_smul]
  have hsmul : a • Quotient.mk (⨅ i, I i) (1 : R) =
      Quotient.mk (⨅ i, I i) a := by
    simpa only [smul_eq_mul, mul_one, Submodule.mkQ_apply, Quotient.mk_eq_mk] using
      ((⨅ i, I i).mkQ.map_smul a (1 : R)).symm
  rw [hsmul]
  constructor
  · intro ha
    apply Quotient.eq_zero_iff_mem.mp
    apply (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).injective
    simpa only [map_zero] using ha
  · intro ha
    rw [Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-- The image of the class of `1` under the Chinese remainder equivalence spans
the product of quotients as a module over the common base ring. -/
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_span_singleton_mk_one :
    Submodule.span R
      {quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI
        (Quotient.mk (⨅ i, I i) (1 : R))} = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨r, hr⟩ := Quotient.mk_surjective
    ((quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm x)
  apply Submodule.mem_span_singleton.mpr
  refine ⟨r, ?_⟩
  rw [← quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_smul]
  have hsmul : r • Quotient.mk (⨅ i, I i) (1 : R) =
      Quotient.mk (⨅ i, I i) r := by
    simpa only [smul_eq_mul, mul_one, Submodule.mkQ_apply, Quotient.mk_eq_mk] using
      ((⨅ i, I i).mkQ.map_smul r (1 : R)).symm
  rw [hsmul, hr, RingEquiv.apply_symm_apply]

/-- The canonical Chinese remainder equivalence as a linear equivalence over
`R`. Its underlying additive equivalence is that of
`quotientInfRingEquivPiQuotientOfPairwiseSupEqTop`, with the canonical quotient
module actions and the coordinatewise action of the same base ring. -/
noncomputable def quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop :
    (R ⧸ ⨅ i, I i) ≃ₗ[R] ((i : ι) → R ⧸ I i) :=
  (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).toAddEquiv.toLinearEquiv
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_smul I hI)

/-- The linear and ring Chinese remainder equivalences have the same underlying
equivalence of types. -/
@[simp]
theorem quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_toEquiv :
    (quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI).toEquiv =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).toEquiv :=
  rfl

/-- The additive equivalence underlying the linear Chinese remainder equivalence
is the additive equivalence underlying the ring equivalence. -/
@[simp]
theorem quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_toAddEquiv :
    (quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI).toAddEquiv =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).toAddEquiv :=
  rfl

/-- The function underlying the linear Chinese remainder equivalence is the
canonical Chinese remainder homomorphism. -/
@[simp]
theorem coe_quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop :
    ⇑(quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI) =
      ⇑(quotientInfToPiQuotient I) :=
  (AddEquiv.coe_toLinearEquiv (R := R)
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).toAddEquiv
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_smul I hI)).trans
      (coe_quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI)

/-- Applying the linear Chinese remainder equivalence gives the canonical image
in the product of quotient rings. -/
theorem quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_apply
    (z : R ⧸ ⨅ i, I i) :
    quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI z =
      quotientInfToPiQuotient I z :=
  congrFun (coe_quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI) z

/-- The inverse linear Chinese remainder equivalence gives the same quotient
class as the inverse ring equivalence. -/
@[simp]
theorem quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_symm_apply
    (g : (i : ι) → R ⧸ I i) :
    (quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI).symm g =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm g :=
  rfl

/-- Each component of the linear Chinese remainder equivalence is the canonical
quotient factor. -/
theorem quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_apply_apply
    (z : R ⧸ ⨅ j, I j) (i : ι) :
    quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI z i =
      Quotient.factor (iInf_le I i) z :=
  (congrFun (quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_apply I hI z) i).trans
    (quotientInfToPiQuotient_apply_apply I z i)

/-- A representative maps to its class in every quotient of the family. -/
@[simp]
theorem quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_mk (r : R) :
    quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI
        (Quotient.mk (⨅ i, I i) r) =
      fun i => Quotient.mk (I i) r :=
  (quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_apply I hI _).trans
    (quotientInfToPiQuotient_mk I r)

/-- The linear Chinese remainder equivalence preserves the canonical left action
of the common base ring. -/
@[simp]
theorem quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_smul
    (r : R) (z : R ⧸ ⨅ i, I i) :
    quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI (r • z) =
      r • quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI z :=
  (quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI).map_smul r z

end LinearEquivalence

end Ideal
