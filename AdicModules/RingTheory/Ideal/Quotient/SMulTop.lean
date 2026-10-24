/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Algebra quotients by scalar ideals

For an ideal `J` of a commutative semiring `R` and an `R`-algebra `A`,
`Ideal.smulTop` regards `J • ⊤ : Submodule R A` as a two-sided ideal of `A`.
When `R` and `A` are rings, the existing submodule quotient
`A ⧸ (J • (⊤ : Submodule R A))` consequently carries a ring and an `R`-algebra
structure. Its additive group and scalar action are those of the submodule quotient.

The projection is Mathlib's `Ideal.Quotient.mkₐ R (J.smulTop A)`. The three
`smulTop` projection lemmas identify it with the original submodule projection
`(J • (⊤ : Submodule R A)).mkQ`. In particular, ideal-power quotients use these
same constructions with `J := I ^ n`, including `n = 0`.

## References

This construction uses Mathlib's `Submodule.smul_top_le_comap_smul_top` and
`LinearMap.mulLeft`/`LinearMap.mulRight` for multiplicative stability, and its
ideal-quotient ring, algebra and projection constructions. It follows the
submodule-quotient formalization by Johannes Hölzl, Mario Carneiro, Kevin Buzzard
and Yury Kudryashov, and the ideal-quotient formalization by Kenny Lau,
Chris Hughes, Mario Carneiro, Anne Baanen and Patrick Massot. The whole-module
comparisons use Mathlib's `Module.ext'` after fixing the additive structure.
-/

@[expose] public section

universe u v

namespace Ideal

section Semiring

variable {R : Type u} [CommSemiring R] (J : Ideal R)
variable (A : Type v) [Semiring A] [Algebra R A]

/-- The two-sided ideal of an algebra consisting of the scalar ideal times the
whole algebra, with the additive submonoid of `J • ⊤`. -/
def smulTop : Ideal A where
  toAddSubmonoid := (J • (⊤ : Submodule R A)).toAddSubmonoid
  smul_mem' a _ hx :=
    (Submodule.smul_top_le_comap_smul_top J (LinearMap.mulLeft R a)) hx

/-- The scalar ideal times the whole algebra is stable under right multiplication. -/
instance smulTop_isTwoSided : (J.smulTop A).IsTwoSided where
  mul_mem_of_left a hx :=
    (Submodule.smul_top_le_comap_smul_top J (LinearMap.mulRight R a)) hx

/-- Membership in the ideal view is membership in the scalar-image submodule. -/
@[simp]
theorem mem_smulTop (a : A) :
    a ∈ J.smulTop A ↔ a ∈ (J • (⊤ : Submodule R A)) :=
  Iff.rfl

private theorem smulTop_toAddSubmonoid :
    (J.smulTop A).toAddSubmonoid = (J • (⊤ : Submodule R A)).toAddSubmonoid :=
  rfl

end Semiring

section Ring

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable (J : Ideal R)

private theorem smulTop_toAddSubgroup :
    (J.smulTop A).toAddSubgroup = (J • (⊤ : Submodule R A)).toAddSubgroup :=
  rfl

private theorem smulTop_quotientRel :
    (J.smulTop A).quotientRel = (J • (⊤ : Submodule R A)).quotientRel :=
  rfl

end Ring

end Ideal

namespace Submodule.Quotient

section Ring

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable (J : Ideal R)

/-- The ring on the submodule quotient by a scalar ideal times the whole algebra. -/
instance (priority := 100) ringSmulTop : Ring (A ⧸ (J • (⊤ : Submodule R A))) :=
  Ideal.Quotient.ring (J.smulTop A)

-- These compare entire records, including both additive scalar operations.
private theorem ringSmulTop_toAddCommGroup :
    (ringSmulTop (A := A) J).toAddCommGroup =
      Submodule.Quotient.addCommGroup (J • (⊤ : Submodule R A)) := by
  with_unfolding_all rfl

private theorem ringSmulTop_nsmul :
    (ringSmulTop (A := A) J).toAddCommGroup.nsmul =
      (Submodule.Quotient.addCommGroup (J • (⊤ : Submodule R A))).nsmul := by
  exact congrArg
    (fun s : AddCommGroup (A ⧸ (J • (⊤ : Submodule R A))) => s.nsmul)
    (ringSmulTop_toAddCommGroup (A := A) J)

private theorem ringSmulTop_zsmul :
    (ringSmulTop (A := A) J).toAddCommGroup.zsmul =
      (Submodule.Quotient.addCommGroup (J • (⊤ : Submodule R A))).zsmul := by
  exact congrArg
    (fun s : AddCommGroup (A ⧸ (J • (⊤ : Submodule R A))) => s.zsmul)
    (ringSmulTop_toAddCommGroup (A := A) J)

-- The type ascription fixes the old additive index before applying Module.ext'.
private theorem smulTop_module'_eq_module :
    (Submodule.Quotient.module' (S := R) (J.smulTop A) :
      @Module R (A ⧸ (J • (⊤ : Submodule R A))) _
        (Submodule.Quotient.addCommGroup (J • (⊤ : Submodule R A))).toAddCommMonoid) =
      Submodule.Quotient.module (J • (⊤ : Submodule R A)) := by
  apply Module.ext'
  intro r x
  refine Quotient.inductionOn' x ?_
  intro a
  rfl

private theorem smulTop_module'_toSMul :
    (Submodule.Quotient.module' (S := R) (J.smulTop A)).toSMul =
      (Submodule.Quotient.module (J • (⊤ : Submodule R A))).toSMul := by
  exact congrArg
    (fun m : @Module R (A ⧸ (J • (⊤ : Submodule R A))) _
      (Submodule.Quotient.addCommGroup (J • (⊤ : Submodule R A))).toAddCommMonoid =>
        m.toSMul)
    (smulTop_module'_eq_module (A := A) J)

/-- The algebra on the submodule quotient by a scalar ideal times the whole algebra. -/
instance (priority := 100) algebraSmulTop :
    Algebra R (A ⧸ (J • (⊤ : Submodule R A))) :=
  Ideal.Quotient.algebra R (I := J.smulTop A)

private theorem algebraSmulTop_toModule :
    (@Algebra.toModule R (A ⧸ (J • (⊤ : Submodule R A))) _
      (ringSmulTop (A := A) J).toSemiring (algebraSmulTop (A := A) J) :
      @Module R (A ⧸ (J • (⊤ : Submodule R A))) _
        (Submodule.Quotient.addCommGroup (J • (⊤ : Submodule R A))).toAddCommMonoid) =
      Submodule.Quotient.module (J • (⊤ : Submodule R A)) := by
  apply Module.ext'
  intro r x
  refine Quotient.inductionOn' x ?_
  intro a
  rfl

private theorem algebraSmulTop_toSMul :
    (algebraSmulTop (A := A) J).toSMul =
      (Submodule.Quotient.module (J • (⊤ : Submodule R A))).toSMul := by
  exact congrArg
    (fun m : @Module R (A ⧸ (J • (⊤ : Submodule R A))) _
      (Submodule.Quotient.addCommGroup (J • (⊤ : Submodule R A))).toAddCommMonoid =>
        m.toSMul)
    (algebraSmulTop_toModule (A := A) J)

end Ring

section CommRing

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private theorem ringSmulTop_eq_commRing_toRing (J : Ideal R) :
    ringSmulTop (A := A) J = (Ideal.Quotient.commRing (J.smulTop A)).toRing := by
  with_reducible_and_instances rfl

end CommRing

section Self

variable {R : Type u} [CommRing R] (J : Ideal R)

-- All four comparisons below keep the denominator J • ⊤ fixed.
private theorem smulTop_self : J.smulTop R = (J • (⊤ : Submodule R R)) := by
  dsimp only [Ideal.smulTop]

private theorem ringSmulTop_self :
    ringSmulTop (A := R) J = Ideal.Quotient.ring (J • (⊤ : Submodule R R)) := by
  dsimp only [ringSmulTop, Ideal.smulTop]

private theorem algebraSmulTop_self :
    algebraSmulTop (A := R) J =
      Ideal.Quotient.algebra R (I := J • (⊤ : Submodule R R)) := by
  dsimp only [algebraSmulTop, Ideal.smulTop]

private theorem ringSmulTop_self_toAddCommGroup :
    (ringSmulTop (A := R) J).toAddCommGroup =
      (Ideal.Quotient.ring (J • (⊤ : Submodule R R))).toAddCommGroup := by
  exact congrArg
    (fun s : Ring (R ⧸ (J • (⊤ : Submodule R R))) => s.toAddCommGroup)
    (ringSmulTop_self J)

private theorem algebraSmulTop_self_toModule :
    (@Algebra.toModule R (R ⧸ (J • (⊤ : Submodule R R))) _
      (ringSmulTop (A := R) J).toSemiring (algebraSmulTop (A := R) J) :
      @Module R (R ⧸ (J • (⊤ : Submodule R R))) _
        (Submodule.Quotient.addCommGroup (J • (⊤ : Submodule R R))).toAddCommMonoid) =
      @Algebra.toModule R (R ⧸ (J • (⊤ : Submodule R R))) _
        (Ideal.Quotient.ring (J • (⊤ : Submodule R R))).toSemiring
        (Ideal.Quotient.algebra R (I := J • (⊤ : Submodule R R))) := by
  apply Module.ext'
  intro r x
  refine Quotient.inductionOn' x ?_
  intro a
  rfl

-- Normalizing the denominator is a separate, propositional comparison.
private theorem smul_top_self_eq : (J • (⊤ : Submodule R R)) = J := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

private theorem quotientEquivAlgOfEq_smul_top_self_apply (r : R) :
    Ideal.quotientEquivAlgOfEq R (smul_top_self_eq J)
        (Ideal.Quotient.mkₐ R (J.smulTop R) r) =
      Ideal.Quotient.mkₐ R J r := by
  exact Ideal.quotientEquivAlgOfEq_mk R (smul_top_self_eq J) r

end Self

end Submodule.Quotient

namespace Ideal.Quotient

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

private theorem mkₐ_smulTop_toRingHom (J : Ideal R) :
    (Ideal.Quotient.mkₐ R (J.smulTop A)).toRingHom =
      Ideal.Quotient.mk (J.smulTop A) :=
  Ideal.Quotient.mkₐ_toRingHom R (J.smulTop A)

/-- The algebra projection agrees on elements with the submodule projection. -/
@[simp]
theorem mkₐ_smulTop_apply (J : Ideal R) (a : A) :
    Ideal.Quotient.mkₐ R (J.smulTop A) a =
      (J • (⊤ : Submodule R A)).mkQ a :=
  rfl

/-- The linear map of the algebra projection is the original submodule projection. -/
@[simp]
theorem mkₐ_smulTop_toLinearMap (J : Ideal R) :
    (Ideal.Quotient.mkₐ R (J.smulTop A)).toLinearMap =
      (J • (⊤ : Submodule R A)).mkQ := by
  apply LinearMap.ext
  intro a
  rfl

/-- The algebra and submodule projections have the same underlying function. -/
theorem coe_mkₐ_smulTop (J : Ideal R) :
    (Ideal.Quotient.mkₐ R (J.smulTop A) :
        A → A ⧸ (J • (⊤ : Submodule R A))) =
      ((J • (⊤ : Submodule R A)).mkQ : A → A ⧸ (J • (⊤ : Submodule R A))) :=
  rfl

end Ideal.Quotient
