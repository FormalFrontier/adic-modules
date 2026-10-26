/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.MvPolynomial.Jacobian
public import AdicModules.RingTheory.Etale.PolynomialSystem
public import AdicModules.RingTheory.HenselianEtale

/-!
# Hensel lifting for finite polynomial systems

A square finite polynomial system over a Henselian pair has a unique root in a
prescribed ideal-congruence class when its Jacobian determinant is a unit there.
The coefficient ring and the finite index type have independent universes.

The proof lifts the residue point of the coordinate algebra localized away from
its Jacobian determinant. Its coordinate images give a root, and Jacobian
injectivity on the ideal-congruence class gives uniqueness.

## Limitations

The determinant must be a unit in the coefficient ring. This theorem does not
assert strong Hensel lifting with errors divisible by the square of a nonunit
determinant, nor does it assert polynomial factorization with fixed degrees or
leading coefficients.

## References

The coordinate algebra and residue point are from
`AdicModules.RingTheory.Etale.PolynomialSystem`, and the Henselian lifting of
étale points is from `AdicModules.RingTheory.HenselianEtale`. The uniqueness
argument uses `AdicModules.MvPolynomial.Jacobian`. Polynomial evaluation and
the quotient and localization constructions are Mathlib's.
-/

@[expose] public section

universe u v

namespace HenselianRing

/-- A simple approximate root of a square finite polynomial system over a
Henselian pair lifts uniquely within its ideal-congruence class.

The determinant is taken over the coefficient ring. No locality or adic
completeness hypothesis is required. Existence follows by lifting the residue
point of the localized coordinate algebra using
`HenselianRing.existsUnique_algHom_lift_of_etale`; uniqueness follows from
`MvPolynomial.injOn_eval_of_isUnit_det_jacobian`. -/
theorem existsUnique_root_of_isUnit_det_jacobian
    {R : Type u} [CommRing R] {I : Ideal R} [HenselianRing R I]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (P : ι → MvPolynomial ι R) (a : ι → R)
    (ha : ∀ i, MvPolynomial.eval a (P i) ∈ I)
    (hj : IsUnit (Matrix.det
      (fun i j => MvPolynomial.eval a (MvPolynomial.pderiv j (P i))))) :
    ∃! b : ι → R,
      (∀ i, MvPolynomial.eval b (P i) = 0) ∧ ∀ i, b i - a i ∈ I := by
  classical
  let J : Ideal (MvPolynomial ι R) := Ideal.span (Set.range P)
  let M : Matrix ι ι (MvPolynomial ι R) :=
    fun i j => MvPolynomial.pderiv j (P i)
  let D : MvPolynomial ι R := M.det
  let Q := MvPolynomial ι R ⧸ J
  let d : Q := Ideal.Quotient.mk J D
  let A := Localization.Away d
  let x : ι → A := fun i =>
    algebraMap Q A (Ideal.Quotient.mk J (MvPolynomial.X i))
  let e : MvPolynomial ι R →ₐ[R] A :=
    (IsScalarTower.toAlgHom R Q A).comp (Ideal.Quotient.mkₐ R J)
  have hD : IsUnit (Ideal.Quotient.mk I (MvPolynomial.eval a D)) := by
    apply IsUnit.map (Ideal.Quotient.mk I)
    exact ((MvPolynomial.eval a).map_det M).symm ▸ hj
  let : Algebra.Etale R A := MvPolynomial.etale_localizationAway_jacobian P
  obtain ⟨ψ, hψ⟩ :=
    (existsUnique_algHom_lift_of_etale
      (MvPolynomial.residuePoint P I a ha hD)).exists
  let b : ι → R := fun i => ψ (x i)
  let g : MvPolynomial ι R →ₐ[R] R := ψ.comp e
  have hg : g = MvPolynomial.aeval b := MvPolynomial.aeval_unique g
  have hb : ∀ i, MvPolynomial.eval b (P i) = 0 := by
    intro i
    change MvPolynomial.aeval b (P i) = 0
    rw [← hg]
    change ψ (algebraMap Q A (Ideal.Quotient.mk J (P i))) = 0
    have hPi : Ideal.Quotient.mk J (P i) = 0 :=
      Ideal.Quotient.mk_span_range P i
    rw [hPi, map_zero, map_zero]
  have hba : ∀ i, b i - a i ∈ I := by
    intro i
    apply Ideal.Quotient.eq.mp
    have hi := DFunLike.congr_fun hψ (x i)
    change Ideal.Quotient.mk I (b i) =
      MvPolynomial.residuePoint P I a ha hD (x i) at hi
    exact hi.trans (MvPolynomial.residuePoint_apply_X P I a ha hD i)
  refine ⟨b, ⟨hb, hba⟩, ?_⟩
  intro c hc
  apply MvPolynomial.injOn_eval_of_isUnit_det_jacobian I
    (HenselianRing.jac (R := R) (I := I)) P a hj hc.2 hba
  funext i
  exact (hc.1 i).trans (hb i).symm

end HenselianRing
