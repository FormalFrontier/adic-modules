/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.StandardEtale
public import AdicModules.RingTheory.HenselianEtale

/-!
# Henselian pairs and étale point lifting

The pair formed by a commutative ring `R` and an ideal `I` is Henselian if and
only if every specified `R ⧸ I`-point of an étale `R`-algebra in the universe
of `R` lifts to an `R`-point.

For the converse, lifting points of principal localizations makes the quotient map
reflect units, forcing `I` into the Jacobson radical. Lifting points of the standard
étale pair associated to a monic polynomial and its derivative lifts simple roots.

## References

The point-lifting condition is condition (2) in
[The Stacks Project, Lemma 15.11.6, tag 09XI](https://stacks.math.columbia.edu/tag/09XI).
-/

@[expose] public section

universe u

namespace StandardEtalePair

/-- If every quotient point of an étale algebra lifts to the base ring, then the
points described by a standard étale pair lift as well. -/
theorem exists_hasMap_lift_of_etale_point_lifting
    {R : Type u} [CommRing R] (I : Ideal R)
    (hLift : ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
      (g : A →ₐ[R] R ⧸ I),
      ∃ x : A →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp x = g)
    (P : StandardEtalePair R) {a : R ⧸ I} (ha : P.HasMap a) :
    ∃ b : R, P.HasMap b ∧ (Ideal.Quotient.mk I) b = a := by
  obtain ⟨x, hx⟩ := hLift P.Ring (P.lift a ha)
  refine ⟨x P.X, (hasMap_X (P := P)).map x, ?_⟩
  have hxX := congrArg (fun k : P.Ring →ₐ[R] R ⧸ I => k P.X) hx
  exact hxX.trans (P.lift_X a ha)

end StandardEtalePair

namespace HenselianRing

/-- If every specified quotient point of an étale algebra lifts, then every
simple root modulo the ideal of a monic polynomial lifts to a root over the base ring. -/
theorem exists_root_of_etale_point_lifting
    {R : Type u} [CommRing R] (I : Ideal R)
    (hLift : ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
      (g : A →ₐ[R] R ⧸ I),
      ∃ x : A →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp x = g)
    (f : Polynomial R) (hf : f.Monic) (a0 : R)
    (hfa : Polynomial.eval a0 f ∈ I)
    (hderiv : IsUnit ((Ideal.Quotient.mk I) (Polynomial.eval a0 f.derivative))) :
    ∃ a : R, f.IsRoot a ∧ a - a0 ∈ I := by
  let P : StandardEtalePair R :=
    StandardEtalePair.mk f hf f.derivative ⟨1, 0, 1, by simp⟩
  have hzero : (Ideal.Quotient.mk I) (Polynomial.eval a0 f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hfa
  have hpoint : P.HasMap ((Ideal.Quotient.mk I) a0) := by
    constructor
    · simpa [P, Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hzero
    · simpa [P, Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hderiv
  obtain ⟨a, ha, hres⟩ :=
    StandardEtalePair.exists_hasMap_lift_of_etale_point_lifting I hLift P hpoint
  refine ⟨a, ?_, ?_⟩
  · simpa [P, Polynomial.aeval_def] using ha.left
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hres, sub_self]

/-- The quotient map reflects units if every specified quotient point of an étale
algebra in the base universe lifts to a point over the base ring.

The test algebra for an element `s` is the principal localization `R[1/s]`. -/
theorem isUnit_of_etale_point_lifting (R : Type u) [CommRing R] (I : Ideal R)
    (hLift : ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
      (g : A →ₐ[R] R ⧸ I),
      ∃ x : A →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp x = g)
    {s : R} (hs : IsUnit ((Ideal.Quotient.mkₐ R I) s)) : IsUnit s := by
  let g : Localization.Away s →ₐ[R] R ⧸ I :=
    IsLocalization.Away.liftAlgHom s (f := Ideal.Quotient.mkₐ R I) hs
  obtain ⟨x, _⟩ := hLift (Localization.Away s) g
  simpa using (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away s) s).map x

/-- Étale point lifting forces the ideal of the quotient to lie in the Jacobson
radical. -/
theorem le_jacobson_of_etale_point_lifting (R : Type u) [CommRing R] (I : Ideal R)
    (hLift : ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
      (g : A →ₐ[R] R ⧸ I),
      ∃ x : A →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp x = g) :
    I ≤ (⊥ : Ideal R).jacobson := by
  intro a ha
  apply Ideal.mem_jacobson_bot.mpr
  intro y
  apply isUnit_of_etale_point_lifting R I hLift (s := a * y + 1)
  have ha' : (Ideal.Quotient.mkₐ R I) a = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr ha
  simpa only [map_add, map_mul, map_one, ha', zero_mul, zero_add] using
    (isUnit_one : IsUnit (1 : R ⧸ I))

/-- Lifting every specified quotient point of every étale algebra in the base
universe makes the pair Henselian. -/
theorem of_etale_point_lifting (R : Type u) [CommRing R] (I : Ideal R)
    (hLift : ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
      (g : A →ₐ[R] R ⧸ I),
      ∃ x : A →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp x = g) :
    HenselianRing R I := by
  exact HenselianRing.mk
    (le_jacobson_of_etale_point_lifting R I hLift)
    (exists_root_of_etale_point_lifting I hLift)

/-- The Henselian condition is equivalent to lifting every specified quotient
point of every étale algebra in the base universe. -/
theorem iff_etale_point_lifting (R : Type u) [CommRing R] (I : Ideal R) :
    HenselianRing R I ↔
      ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
        (g : A →ₐ[R] R ⧸ I),
        ∃ x : A →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp x = g := by
  constructor
  · intro h
    let : HenselianRing R I := h
    intro A _ _ _ g
    exact (existsUnique_algHom_lift_of_etale g).exists
  · exact of_etale_point_lifting R I

end HenselianRing
