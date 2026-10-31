/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent

import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
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

end Ideal
