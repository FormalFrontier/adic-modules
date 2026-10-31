/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Lifting cotangent generators

A family in an ideal whose images generate its cotangent module expresses the ideal as
its original span modulo the square. The indexing type need not be finite; finiteness is
needed only when deducing finite generation of the lift ideal.

## References

The proof uses the quotient, scalar-restriction and cotangent APIs in Mathlib, including
Andrew Yang's formalization of ideal cotangent modules.
-/

@[expose] public section

universe uR uι

namespace Ideal

variable {R : Type uR} [CommRing R]

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
