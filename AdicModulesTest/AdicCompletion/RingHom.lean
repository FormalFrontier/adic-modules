/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

/-!
# Coefficient algebras on an iterated completion

At `A = AdicCompletion I R` and `J = I.map (algebraMap R A)`, ordinary imports
retain the stock coefficient-`A` map and action on `AdicCompletion J A`. Explicitly
selecting `AdicCompletion.extendedAlgebra` instead uses the completion of the
original map `R → A`. The check below identifies both maps and their actions;
it does not identify the two algebra structures with one another.

## References

The coefficient algebra and its scalar law are from Mathlib's adic-completion
and algebra APIs. The opt-in construction and its characteristic map law are
from `AdicModules.AdicCompletion.RingHom`.
-/

noncomputable section

universe u

namespace AdicModulesTest.AdicCompletion.RingHom

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "A" => AdicCompletion I R
local notation "J" => I.map (algebraMap R A)
local notation "B" => AdicCompletion J A

/-- The inferred coefficient algebra and the explicitly selected completed-original-map
algebra keep their respective maps and scalar actions on the same stock ring. -/
example (a : A) (b : B) :
    (algebraMap A B a = AdicCompletion.of J A a ∧
      a • b = AdicCompletion.of J A a * b) ∧
    (@algebraMap A B _ _ (AdicCompletion.extendedAlgebra (T := A) I) a =
        AdicCompletion.mapRingHom I J (algebraMap R A) Ideal.le_comap_map a ∧
      @SMul.smul A B (AdicCompletion.extendedAlgebra (T := A) I).toSMul a b =
        AdicCompletion.mapRingHom I J (algebraMap R A) Ideal.le_comap_map a * b) := by
  constructor
  · constructor
    · simp only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
    · simp only [Algebra.smul_def, AdicCompletion.algebraMap_apply,
        Algebra.algebraMap_self_apply]
  · constructor
    · exact AdicCompletion.extendedAlgebra_algebraMap_apply (T := A) I a
    · calc
        _ = @algebraMap A B _ _ (AdicCompletion.extendedAlgebra (T := A) I) a * b :=
          @Algebra.smul_def A B _ _ (AdicCompletion.extendedAlgebra (T := A) I) a b
        _ = _ := congrArg (fun c : B ↦ c * b)
          (AdicCompletion.extendedAlgebra_algebraMap_apply (T := A) I a)

end AdicModulesTest.AdicCompletion.RingHom
