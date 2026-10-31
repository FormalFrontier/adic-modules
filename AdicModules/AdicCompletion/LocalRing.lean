/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Units, ideal extension, and locality in adic completions

For every ideal `I` of a commutative ring `R`, the canonical first reduction
`AdicCompletion.evalOneₐ I` detects units. Consequently it is a local homomorphism,
its kernel lies in the Jacobson radical, and the completion is local whenever `R ⧸ I`
is local. No finite-generation hypothesis on `I` is needed.

For any ideal `J`, extension along the canonical coefficient map is the top ideal exactly
when `I ⊔ J = ⊤`. The first reduction is surjective and reflects units, so it detects
whether an ideal of the completion is top. The image of the extended ideal under this
reduction is the image of `J` in `R ⧸ I`, giving the ideal-sum criterion.

Unit detection is proved by lifting the unit condition to every positive finite quotient using
`Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk`. Inverses in these quotients form a compatible
family: a transition map sends an inverse to an inverse, which is unique. Stage `0` is
the quotient by the top ideal and is treated separately. This argument uses the
compatible-family description of the completion, not completeness for the extended ideal.

## References

The compatible families and canonical projections are from Mathlib's
`Mathlib.RingTheory.AdicCompletion.Basic` and `Mathlib.RingTheory.AdicCompletion.Algebra`,
by Kenny Lau, Judith Ludwig, Christian Merten, and Jiedong Jiang. Finite-quotient unit
lifting uses Oliver Nash's `Mathlib.RingTheory.Ideal.Quotient.Nilpotent`.
The local-homomorphism API is from `Mathlib.Algebra.Group.Units.Hom`, by Johan Commelin,
Chris Hughes, and Kevin Buzzard. Locality transport uses
`Mathlib.RingTheory.LocalRing.RingHom.Basic`, by Kenny Lau, Chris Hughes, and Mario Carneiro;
the Jacobson criterion is from `Mathlib.RingTheory.Jacobson.Ideal`, by Kenny Lau,
Devon Tuma, and Wojciech Nawrocki. The ideal-map and quotient APIs are from
`Mathlib.RingTheory.Ideal.Maps`, by Kenny Lau, and
`Mathlib.RingTheory.Ideal.Quotient.Operations`, by Kenny Lau and Patrick Massot.
-/

@[expose] public section

set_option warningAsError true

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

private lemma isUnit_val_of_isUnit_evalOne (x : AdicCompletion I R)
    (hx : IsUnit (evalOneₐ I x)) (n : ℕ) : IsUnit (x.val n) := by
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (R ⧸ (I ^ 0 • ⊤ : Ideal R)) := by
      simpa only [pow_zero, Ideal.one_eq_top, Ideal.smul_eq_mul, Ideal.mul_top] using
        (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
    exact @isUnit_of_subsingleton _ _ this _
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (x.val n)
  have h1 : x.val 1 = Ideal.Quotient.mk (I ^ 1 • ⊤ : Ideal R) r := by
    calc
      x.val 1 = transitionMap I R (Nat.one_le_iff_ne_zero.mpr hn) (x.val n) :=
        (x.property (Nat.one_le_iff_ne_zero.mpr hn)).symm
      _ = Ideal.Quotient.mk (I ^ 1 • ⊤ : Ideal R) r :=
        congrArg (transitionMap I R (Nat.one_le_iff_ne_zero.mpr hn)) hr.symm
  have hred : evalOneₐ I x = Ideal.Quotient.mk I r := by
    rw [← factor_evalOneₛₗ_eq_evalOneₐ I x, evalOneₛₗ_apply]
    simp only [eval_apply, h1]
    rfl
  have hu : IsUnit (Ideal.Quotient.mk (I ^ n) r) :=
    (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk I hn).mpr (hred ▸ hx)
  have hraw : I ^ n ≤ (I ^ n • ⊤ : Ideal R) :=
    le_of_eq (Ideal.mul_top (I ^ n)).symm
  have hu_raw : IsUnit (Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) r) := by
    simpa only [Ideal.Quotient.factor_mk] using
      hu.map (Ideal.Quotient.factor (T := (I ^ n • ⊤ : Ideal R)) hraw)
  exact hr ▸ hu_raw

private lemma isUnit_of_isUnit_evalOne (x : AdicCompletion I R)
    (hx : IsUnit (evalOneₐ I x)) : IsUnit x := by
  classical
  have hu : ∀ n, IsUnit (x.val n) := isUnit_val_of_isUnit_evalOne I x hx
  let y : ∀ n : ℕ, R ⧸ (I ^ n • ⊤ : Ideal R) := fun n ↦ ↑(hu n).unit⁻¹
  have hy (n : ℕ) : x.val n * y n = 1 := (hu n).mul_val_inv
  -- Compatibility follows by cancelling the unit at the target coordinate.
  have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n), transitionMap I R hmn (y n) = y m := by
    intro m n hmn
    apply (hu m).mul_left_cancel
    calc
      x.val m * transitionMap I R hmn (y n) =
          transitionMap I R hmn (x.val n * y n) := by
        rw [transitionMap_map_mul, x.property hmn]
      _ = 1 := by rw [hy n, transitionMap_map_one]
      _ = x.val m * y m := (hy m).symm
  let z : AdicCompletion I R := ⟨y, hcompat⟩
  apply IsUnit.of_mul_eq_one z
  apply AdicCompletion.ext
  intro n
  exact hy n

/-- The canonical first reduction of an adic completion reflects units. -/
instance isLocalHom_evalOne : IsLocalHom (evalOneₐ I).toRingHom where
  map_nonunit x hx := isUnit_of_isUnit_evalOne I x hx

/-- An element of an adic completion is a unit exactly when its first reduction is a unit. -/
@[simp]
theorem isUnit_evalOne_iff (x : AdicCompletion I R) :
    IsUnit (evalOneₐ I x) ↔ IsUnit x :=
  isUnit_map_iff (evalOneₐ I).toRingHom x

/-- The kernel of the first reduction lies in the Jacobson radical of the adic completion. -/
theorem ker_evalOne_le_jacobson :
    RingHom.ker (evalOneₐ I).toRingHom ≤
      Ideal.jacobson (⊥ : Ideal (AdicCompletion I R)) := by
  intro x hx
  apply Ideal.mem_jacobson_bot.mpr
  intro y
  apply (isUnit_evalOne_iff I (x * y + 1)).mp
  have hx0 : evalOneₐ I x = 0 := hx
  simpa only [map_add, map_mul, map_one, hx0, zero_mul, zero_add] using
    (isUnit_one : IsUnit (1 : R ⧸ I))

/-- Extension of `J` to the `I`-adic completion is the unit ideal exactly when `I` and `J`
are comaximal. No finite-generation hypothesis on either ideal is needed. -/
@[simp]
theorem map_algebraMap_eq_top_iff (J : Ideal R) :
    J.map (algebraMap R (AdicCompletion I R)) = ⊤ ↔ I ⊔ J = ⊤ := by
  calc
    J.map (algebraMap R (AdicCompletion I R)) = ⊤ ↔
        (J.map (algebraMap R (AdicCompletion I R))).map
          (evalOneₐ I).toRingHom = ⊤ := by
      constructor
      · intro h
        rw [h, Ideal.map_top]
      · intro h
        obtain ⟨x, hx, hx1⟩ :=
          (Ideal.mem_map_iff_of_surjective (evalOneₐ I).toRingHom
            (evalOneₐ_surjective I)).mp ((Ideal.eq_top_iff_one _).mp h)
        apply Ideal.eq_top_of_isUnit_mem _ hx
        apply IsUnit.of_map (evalOneₐ I).toRingHom x
        rw [hx1]
        exact isUnit_one
    _ ↔ I ⊔ J = ⊤ := by
      rw [Ideal.map_map, evalOneₐ_comp_algebraMap_eq_mk,
        ← Ideal.comap_eq_top_iff (f := Ideal.Quotient.mk I),
        Ideal.comap_map_quotientMk]

/-- The adic completion is local if the quotient by its defining ideal is local. -/
theorem isLocalRing_of_quotient [IsLocalRing (R ⧸ I)] :
    IsLocalRing (AdicCompletion I R) :=
  RingHom.domain_isLocalRing (evalOneₐ I).toRingHom

end AdicCompletion
