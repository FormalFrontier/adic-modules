/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent

import AdicModules.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.Choose

/-!
# Cotangent finiteness and lifting generators

A family in an ideal whose images generate its cotangent module expresses the ideal as
its original span modulo the square. The indexing type need not be finite; finiteness is
needed only when deducing finite generation of the lift ideal. Finite cotangent modules admit
finite families of original representatives, and finitely generated ideals have finite cotangent
modules over their quotient rings. Noetherianity of any power quotient of exponent at least two
also makes the original cotangent finite, without finite generation of the ideal.
If the original cotangent is finite, every power has finite cotangent over its own
quotient ring, including the zeroth power.

## References

The proof uses the quotient, scalar-restriction and cotangent APIs in Mathlib, including
Andrew Yang's formalization of ideal cotangent modules and Johan Commelin's finiteness API.
-/

@[expose] public section

universe uR uι

namespace Ideal

variable {R : Type uR} [CommRing R]

/-- A finite cotangent has a finite family of representatives in the original ideal. -/
theorem exists_fin_span_toCotangent_eq_top (I : Ideal R)
    [Module.Finite (R ⧸ I) I.Cotangent] :
    ∃ (r : ℕ) (v : Fin r → I),
      Submodule.span (R ⧸ I)
        (Set.range (fun i : Fin r => I.toCotangent (v i))) = ⊤ := by
  obtain ⟨r, w, hw⟩ := Module.Finite.exists_fin (R := R ⧸ I) (M := I.Cotangent)
  choose v hv using fun i : Fin r => I.toCotangent_surjective (w i)
  exact ⟨r, v, by simpa only [hv] using hw⟩

/-- The cotangent of a finitely generated ideal is finite over the quotient ring. -/
theorem finite_cotangent_of_fg (I : Ideal R) (hI : I.FG) :
    Module.Finite (R ⧸ I) I.Cotangent := by
  let : Module.Finite R I := Module.Finite.of_fg hI
  let : Module.Finite R I.Cotangent :=
    Module.Finite.of_surjective I.toCotangent I.toCotangent_surjective
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) I.Cotangent

/-- A Noetherian power quotient of exponent at least two makes the cotangent
finite over the residue ring. -/
theorem finite_cotangent_of_isNoetherianRing_quotient_pow
    (I : Ideal R) {n : ℕ} (hn : 2 ≤ n)
    [IsNoetherianRing (R ⧸ I ^ n)] :
    Module.Finite (R ⧸ I) I.Cotangent := by
  let : IsNoetherianRing (R ⧸ I ^ 2) :=
    isNoetherianRing_of_surjective (R ⧸ I ^ n) (R ⧸ I ^ 2)
      (Quotient.factorPow I hn) (Quotient.factor_surjective (pow_le_pow_right hn))
  have hfg : (I.cotangentIdeal.restrictScalars R).FG :=
    Submodule.FG.restrictScalars_of_surjective I.cotangentIdeal.fg_of_isNoetherianRing
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (algebraMap R (R ⧸ I ^ 2)))
  let : Module.Finite R I.cotangentIdeal := Module.Finite.of_fg hfg
  let : Module.Finite R I.Cotangent := Module.Finite.equiv I.cotangentEquivIdeal.symm
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) I.Cotangent

/-- Cotangent generators express an ideal as their span modulo its square. -/
theorem eq_span_sup_sq_of_span_toCotangent_eq_top
    (I : Ideal R) {ι : Type uι} (v : ι → I)
    (hv : Submodule.span (R ⧸ I)
      (Set.range (fun i : ι => I.toCotangent (v i))) = ⊤) :
    I = Ideal.span (Set.range (fun i : ι => (v i : R))) ⊔ I ^ 2 := by
  have hvR : Submodule.span R
      (Set.range (fun i : ι => I.toCotangent (v i))) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I)
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (algebraMap R (R ⧸ I))),
      hv, Submodule.restrictScalars_top]
  let P : Submodule R I := Submodule.span R (Set.range v)
  have hPmap : P.map I.toCotangent = ⊤ := by
    dsimp only [P]
    rw [Submodule.map_span, ← Set.range_comp]
    exact hvR
  have hsup : P ⊔ I.toCotangent.ker = ⊤ :=
    (LinearMap.map_eq_top_iff I.toCotangent_range).mp hPmap
  have hP : P.map I.subtype = Ideal.span (Set.range (fun i : ι => (v i : R))) := by
    dsimp only [P]
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  calc
    I = (⊤ : Submodule R I).map I.subtype := (Submodule.map_subtype_top I).symm
    _ = (P ⊔ I.toCotangent.ker).map I.subtype := by rw [hsup]
    _ = Ideal.span (Set.range (fun i : ι => (v i : R))) ⊔ I ^ 2 := by
      rw [Submodule.map_sup, hP, I.map_toCotangent_ker]

private theorem fg_of_isNilpotent_of_finite_cotangent (J : Ideal R)
    (hJnil : IsNilpotent J) [Module.Finite (R ⧸ J) J.Cotangent] : J.FG := by
  obtain ⟨r, v, hv⟩ := exists_fin_span_toCotangent_eq_top J
  let H : Ideal R := Ideal.span (Set.range (fun i : Fin r => (v i : R)))
  have hHJ : H ≤ J := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (v i).property)
  have hJ : J = H ⊔ J ^ 2 := eq_span_sup_sq_of_span_toCotangent_eq_top J v hv
  -- Modulo the finite span, the image is both idempotent and nilpotent.
  have hidem : IsIdempotentElem (J.map (Quotient.mk H)) := by
    have he := congrArg (Ideal.map (Quotient.mk H)) hJ
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow] at he
    exact (pow_two _).symm.trans he.symm
  have hzero : J.map (Quotient.mk H) = ⊥ :=
    hidem.eq_zero_of_isNilpotent (hJnil.map (Ideal.mapHom (Quotient.mk H)))
  have hJH : J ≤ H := by
    simpa only [Ideal.mk_ker] using (Ideal.map_eq_bot_iff_le_ker (Quotient.mk H)).mp hzero
  have hEq : J = H := le_antisymm hJH hHJ
  rw [hEq]
  exact Submodule.fg_span (Set.finite_range _)

/-- Every ideal power has finite cotangent if the original ideal does. The scalar
ring is the quotient by that power, acting on its existing cotangent module. -/
theorem finite_cotangent_pow (I : Ideal R)
    [Module.Finite (R ⧸ I) I.Cotangent] (n : ℕ) :
    Module.Finite (R ⧸ I ^ n) (I ^ n).Cotangent := by
  cases n with
  | zero =>
    apply finite_cotangent_of_fg (I ^ 0)
    rw [pow_zero, Ideal.one_eq_top]
    exact Ideal.fg_top R
  | succ n =>
    let A := R ⧸ I ^ (2 * (n + 1))
    let J : Ideal A := I.map (algebraMap R A)
    have hsurj : Function.Surjective (algebraMap R A) := Quotient.mk_surjective
    have hcomap : J.comap (algebraMap R A) = RingHom.ker (algebraMap R A) ⊔ I := by
      simpa only [J, sup_comm] using
        Ideal.comap_map_of_surjective' (algebraMap R A) hsurj I
    let f := Ideal.mapCotangent I J (Algebra.ofId R A)
      (le_of_le_of_eq le_sup_right hcomap.symm)
    let : Module.Finite R I.Cotangent := Module.Finite.trans (R ⧸ I) I.Cotangent
    let : Module.Finite R J.Cotangent := Module.Finite.of_surjective f
      (Ideal.mapCotangent_surjective_of_comap_eq hsurj hcomap)
    let : Module.Finite A J.Cotangent :=
      Module.Finite.of_restrictScalars_finite R A J.Cotangent
    let : Module.Finite (A ⧸ J) J.Cotangent :=
      Module.Finite.of_restrictScalars_finite A (A ⧸ J) J.Cotangent
    have hJnil : IsNilpotent J := I.isNilpotent_map_quotient_pow (2 * (n + 1))
    have hJfg : J.FG := fg_of_isNilpotent_of_finite_cotangent J hJnil
    let K : Ideal A := (I ^ (n + 1)).map (algebraMap R A)
    have hKfg : K.FG := by
      have hpow : K = J ^ (n + 1) := Ideal.map_pow (algebraMap R A) I (n + 1)
      exact hpow.symm ▸ hJfg.pow (n := n + 1)
    let : Module.Finite A K := Module.Finite.of_fg hKfg
    let : Module.Finite A K.Cotangent :=
      Module.Finite.of_surjective K.toCotangent K.toCotangent_surjective
    let : Module.Finite R K.Cotangent := Module.Finite.trans A K.Cotangent
    have hcomapK : K.comap (algebraMap R A) =
        RingHom.ker (algebraMap R A) ⊔ I ^ (n + 1) := by
      simpa only [K, sup_comm] using
        Ideal.comap_map_of_surjective' (algebraMap R A) hsurj (I ^ (n + 1))
    let g := Ideal.mapCotangent (I ^ (n + 1)) K (Algebra.ofId R A)
      (le_of_le_of_eq le_sup_right hcomapK.symm)
    have hgSurj : Function.Surjective g :=
      Ideal.mapCotangent_surjective_of_comap_eq hsurj hcomapK
    -- The quotient kernel is exactly the square killed in the source cotangent.
    have hker : RingHom.ker (algebraMap R A) = (I ^ (n + 1)) ^ 2 := by
      change RingHom.ker (Quotient.mk (I ^ (2 * (n + 1)))) = _
      rw [Ideal.mk_ker, ← pow_mul, Nat.mul_comm 2 (n + 1)]
    have hgInj : Function.Injective g := by
      apply LinearMap.ker_eq_bot.mp
      change (Ideal.mapCotangent (I ^ (n + 1)) K (Algebra.ofId R A)
        (le_of_le_of_eq le_sup_right hcomapK.symm)).ker = ⊥
      rw [Ideal.mapCotangent_ker_of_surjective hsurj hcomapK]
      apply le_antisymm _ bot_le
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      change (I ^ (n + 1)).toCotangent x = 0
      exact ((I ^ (n + 1)).toCotangent_eq_zero x).mpr (hker ▸ hx.1)
    let : Module.Finite R (I ^ (n + 1)).Cotangent :=
      Module.Finite.equiv (LinearEquiv.ofBijective g ⟨hgInj, hgSurj⟩).symm
    exact Module.Finite.of_restrictScalars_finite R (R ⧸ I ^ (n + 1))
      (I ^ (n + 1)).Cotangent

end Ideal
