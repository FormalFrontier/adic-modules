/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Polynomial.Hensel
public import AdicModules.RingTheory.HenselianRadical
public import AdicModules.RingTheory.HenselianTransport
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Locality and Henselian ascent along integral homomorphisms

An integral domain integral over a Henselian local ring is local. Integrality is
with respect to an explicit ring homomorphism; the extension need not be
module-finite.

A local ring integral over a Henselian local ring is itself Henselian.

The hypotheses use Mathlib's `HenselianLocalRing` class and `RingHom.IsIntegral`
predicate.
-/

@[expose] public section

universe u v

namespace HenselianLocalRing

/-- An integral domain integral over a Henselian local ring is local.

The domain hypothesis is essential: the diagonal map from a nonzero Henselian
local ring to its square is integral, but the square is not local. -/
theorem isLocalRing_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [HenselianLocalRing R] [IsDomain S]
    (f : R →+* S) (hf : f.IsIntegral) : IsLocalRing S := by
  let m := IsLocalRing.maximalIdeal R
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let π := Ideal.Quotient.mk m
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  obtain ⟨F, hFm, hFx⟩ := hf x
  -- Separate the maximal power of X from the reduction, then lift the coprime factors.
  let p := F.map π
  let n := p.rootMultiplicity 0
  obtain ⟨q, hpq, hqX⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p (hFm.map π).ne_zero 0
  simp only [Polynomial.C_0, sub_zero] at hpq hqX
  have hfac : F.map π = Polynomial.X ^ n * q := hpq
  have hqm : q.Monic :=
    (Polynomial.monic_X.pow n).of_mul_monic_left (hfac ▸ hFm.map π)
  have hcopX : IsCoprime Polynomial.X q :=
    (EuclideanDomain.dvd_or_coprime Polynomial.X q Polynomial.irreducible_X).resolve_left hqX
  obtain ⟨G, H, _, _, hGH, hG, hH⟩ :=
    HenselianRing.exists_monic_factorization m hFm (Polynomial.monic_X.pow n) hqm
      hcopX.pow_left hfac
  -- A vanishing factor has a unit value at either 1 or 0.
  have hprod : G.eval₂ f x * H.eval₂ f x = 0 := by
    rw [← Polynomial.eval₂_mul, ← hGH]
    exact hFx
  rcases mul_eq_zero.mp hprod with hGx | hHx
  · right
    have hGunit : IsUnit (G.eval 1) := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      change π (G.eval 1) ≠ 0
      rw [← Polynomial.eval₂_at_one, Polynomial.eval₂_eq_eval_map, hG]
      simp
    have hdvd : 1 - x ∣ f (G.eval 1) := by
      simpa only [Polynomial.eval_map, Polynomial.eval₂_at_one, hGx, sub_zero] using
        Polynomial.sub_dvd_eval_sub (1 : S) x (G.map f)
    exact isUnit_of_dvd_unit hdvd (hGunit.map f)
  · left
    have hHunit : IsUnit (H.coeff 0) := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      change π (H.coeff 0) ≠ 0
      rw [← Polynomial.coeff_map, hH]
      exact Polynomial.X_dvd_iff.not.mp hqX
    have hroot : (H.map f).IsRoot x := by
      simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hHx
    have hdvd : x ∣ f (H.coeff 0) := by
      simpa only [Polynomial.coeff_map] using hroot.dvd_coeff_zero
    exact isUnit_of_dvd_unit hdvd (hHunit.map f)

end HenselianLocalRing

namespace Ideal

/-- For an integral homomorphism from a local ring, the radical of the extended
maximal ideal is the Jacobson radical of the target ring. -/
theorem radical_map_maximalIdeal_eq_jacobson_bot
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R]
    (f : R →+* S) (hf : f.IsIntegral) :
    ((IsLocalRing.maximalIdeal R).map f).radical = Ideal.jacobson (⊥ : Ideal S) := by
  rw [radical_eq_sInf, jacobson]
  apply congrArg sInf
  ext P
  constructor
  · rintro ⟨hmap, hprime⟩
    let : P.IsPrime := hprime
    have heq : IsLocalRing.maximalIdeal R = P.comap f :=
      (show (IsLocalRing.maximalIdeal R).IsMaximal from inferInstance).eq_of_le
        (hprime.comap f).ne_top (map_le_iff_le_comap.mp hmap)
    have hcomax : (P.comap f).IsMaximal := by
      rw [← heq]
      infer_instance
    exact ⟨bot_le, isMaximal_of_isIntegral_of_isMaximal_comap f hf P hcomax⟩
  · rintro ⟨_, hmax⟩
    let : P.IsMaximal := hmax
    have hcomax := isMaximal_comap_of_isIntegral_of_isMaximal f hf P
    exact ⟨map_le_iff_le_comap.mpr
      (le_of_eq (IsLocalRing.eq_maximalIdeal hcomax).symm), hmax.isPrime⟩

end Ideal

namespace HenselianLocalRing

/-- A local ring integral over a Henselian local ring is Henselian. -/
theorem of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [HenselianLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hf : f.IsIntegral) : HenselianLocalRing S := by
  have hmap : HenselianRing S ((IsLocalRing.maximalIdeal R).map f) :=
    HenselianRing.map_of_isIntegral (IsLocalRing.maximalIdeal R) f hf
  have hrad : HenselianRing S (((IsLocalRing.maximalIdeal R).map f).radical) :=
    (HenselianRing.iff_radical ((IsLocalRing.maximalIdeal R).map f)).mp hmap
  have hj : Ideal.jacobson (⊥ : Ideal S) = IsLocalRing.maximalIdeal S :=
    IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal S) bot_ne_top
  rw [Ideal.radical_map_maximalIdeal_eq_jacobson_bot f hf, hj] at hrad
  let : HenselianRing S (IsLocalRing.maximalIdeal S) := hrad
  exact HenselianRing.toHenselianLocalRing S

end HenselianLocalRing
