/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Localized coordinate algebras of square polynomial systems

For `P : ι → MvPolynomial ι R`, the coordinate algebra is the localization of
`MvPolynomial ι R ⧸ Ideal.span (Set.range P)` away from the image of
`Matrix.det (fun i j => pderiv j (P i))`. The scalar action is the localization's
coefficient action through this quotient. No separate coordinate-carrier definition
or scalar action is introduced.

`etale_localizationAway_jacobian` states étaleness of this algebra.
`residuePoint` and `residuePoint_apply_X` prescribe its point over `R ⧸ I` from
an approximate solution modulo `I` whose evaluated Jacobian determinant has unit image
in `R ⧸ I`.
They do not assert the existence of an `R`-point.

## Universal property

The constructors are Mathlib's `Ideal.Quotient.liftₐ` and
`IsLocalization.Away.liftAlgHom`, with original base ring `R`. For any commutative
`R`-algebra `S`, compose an algebra map from the localized coordinate algebra to `S`
with the localization and quotient maps. `MvPolynomial.aeval_unique` identifies
this composite with evaluation at the coordinate images. Thus these images satisfy
the equations, and the determinant has unit image. Conversely, an `S`-valued solution
with unit determinant gives a map by the two constructors. Uniqueness uses
`IsLocalization.ringHom_ext` and `Ideal.Quotient.algHom_ext`, followed by polynomial
extensionality. These existing universal-property APIs are not duplicated here.

## Limitations

The construction gives a point over the coefficient quotient. It does not assert
a lift to the coefficient ring or a Henselian lifting theorem.

## References

The quotient and localization constructions and their universal properties are from
Mathlib's `RingTheory.Ideal.Quotient.Operations` and
`RingTheory.Localization.Away.Basic`; polynomial evaluation is from
`Algebra.MvPolynomial.Eval`. The étaleness proof uses the quotient and localization
presentations in `RingTheory.Extension.Presentation.Submersive` and the
dimension-zero criterion in `RingTheory.Smooth.StandardSmoothCotangent`.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The coordinate algebra of a finite square polynomial system, localized away from
its Jacobian determinant, is étale over its coefficient ring. -/
theorem etale_localizationAway_jacobian (P : ι → MvPolynomial ι R) :
    let J := Ideal.span (Set.range P)
    Algebra.Etale R (Localization.Away
      (Ideal.Quotient.mk J (Matrix.det (fun i j => pderiv j (P i))))) := by
  let J : Ideal (MvPolynomial ι R) := Ideal.span (Set.range P)
  let d : MvPolynomial ι R ⧸ J :=
    Ideal.Quotient.mk J (Matrix.det (fun i j => pderiv j (P i)))
  let A := Localization.Away d
  change Algebra.Etale R A
  let p : Algebra.PreSubmersivePresentation R (MvPolynomial ι R ⧸ J) ι ι :=
    Algebra.PreSubmersivePresentation.naive (v := P) id Function.injective_id
  have hp : p.jacobian = d := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have hM : p.jacobiMatrix = Matrix.transpose (fun i j => pderiv j (P i)) := by
      funext i j
      exact Algebra.PreSubmersivePresentation.jacobiMatrix_naive
        (v := P) id Function.injective_id
        (Function.surjInv Ideal.Quotient.mk_surjective)
        (by apply Function.surjInv_eq) i j
    rw [hM, Matrix.det_transpose (fun i j => pderiv j (P i))]
    rfl
  let q : Algebra.PreSubmersivePresentation (MvPolynomial ι R ⧸ J) A Unit Unit :=
    Algebra.PreSubmersivePresentation.localizationAway A d
  have hd : IsUnit (algebraMap (MvPolynomial ι R ⧸ J) A d) :=
    IsLocalization.Away.algebraMap_isUnit d
  -- Composition adds one variable and one relation, and its Jacobian is the square of a unit.
  let s : Algebra.SubmersivePresentation R A (Unit ⊕ ι) (Unit ⊕ ι) :=
    { toPreSubmersivePresentation := q.comp p
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, hp]
        dsimp only [q]
        rw [Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
        exact hd.mul hd }
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 R A :=
    s.isStandardSmoothOfRelativeDimension (by
      simp only [Algebra.Presentation.dimension, Nat.sub_self])
  infer_instance

/-- The prescribed quotient-ring point of the localized coordinate algebra.
The equations need only vanish modulo `I`, and the evaluated Jacobian determinant
need only be a unit modulo `I`; no solution in `R` is assumed. -/
noncomputable def residuePoint (P : ι → MvPolynomial ι R) (I : Ideal R) (a : ι → R)
    (hP : ∀ i, eval a (P i) ∈ I)
    (hD : IsUnit (Ideal.Quotient.mk I
      (eval a (Matrix.det (fun i j => pderiv j (P i)))))) :
    let J := Ideal.span (Set.range P)
    Localization.Away (Ideal.Quotient.mk J
      (Matrix.det (fun i j => pderiv j (P i)))) →ₐ[R] R ⧸ I := by
  let J : Ideal (MvPolynomial ι R) := Ideal.span (Set.range P)
  let e : MvPolynomial ι R →ₐ[R] R ⧸ I :=
    (Ideal.Quotient.mkₐ R I).comp (aeval a)
  have hJ : J ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change Ideal.Quotient.mk I (eval a (P i)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hP i)
  let q : MvPolynomial ι R ⧸ J →ₐ[R] R ⧸ I :=
    Ideal.Quotient.liftₐ J e (fun p hp => hJ hp)
  have hqD : IsUnit (q (Ideal.Quotient.mk J
      (Matrix.det (fun i j => pderiv j (P i))))) := by
    change IsUnit (Ideal.Quotient.mk I
      (eval a (Matrix.det (fun i j => pderiv j (P i)))))
    exact hD
  exact IsLocalization.Away.liftAlgHom
    (Ideal.Quotient.mk J (Matrix.det (fun i j => pderiv j (P i)))) hqD

/-- The prescribed quotient-ring point sends each coordinate to the corresponding
residue class of the approximate solution. -/
@[simp]
theorem residuePoint_apply_X (P : ι → MvPolynomial ι R) (I : Ideal R) (a : ι → R)
    (hP : ∀ i, eval a (P i) ∈ I)
    (hD : IsUnit (Ideal.Quotient.mk I
      (eval a (Matrix.det (fun i j => pderiv j (P i)))))) (i : ι) :
    let J := Ideal.span (Set.range P)
    let d := Ideal.Quotient.mk J (Matrix.det (fun i j => pderiv j (P i)))
    residuePoint P I a hP hD
      (algebraMap (MvPolynomial ι R ⧸ J) (Localization.Away d)
        (Ideal.Quotient.mk J (X i))) = Ideal.Quotient.mk I (a i) := by
  simp only [residuePoint, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
  change Ideal.Quotient.mk I ((aeval a) (X i)) = Ideal.Quotient.mk I (a i)
  rw [aeval_X]

end MvPolynomial
