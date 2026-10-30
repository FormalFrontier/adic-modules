/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.ChangeIdeal
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Algebra maps induced by inclusions of ideals

The inclusion-induced linear map between completions of a commutative ring is an
algebra homomorphism. Its quotient evaluations are the canonical factor maps.
The construction bundles the existing linear map, using Mathlib's algebra
structures and quotient evaluation maps throughout.
-/

@[expose] public section

noncomputable section

universe u

namespace AdicCompletion

variable (A : Type u) [CommRing A] {J K L : Ideal A}

private theorem evalₐ_mapOfLE (hJK : J ≤ K) (n : ℕ) (x : AdicCompletion J A) :
    evalₐ K n (mapOfLE A hJK x) =
      Ideal.Quotient.factorₐ A (Ideal.pow_right_mono hJK n) (evalₐ J n x) := by
  have hJ : (J ^ n • ⊤ : Ideal A) ≤ J ^ n := by simp
  have hK : (K ^ n • ⊤ : Ideal A) ≤ K ^ n := by simp
  rw [← factor_eval_eq_evalₐ K (mapOfLE A hJK x) hK, mapOfLE_eval,
    ← factor_eval_eq_evalₐ J x hJ]
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
    (J ^ n • ⊤ : Submodule A A) (eval J A n x)
  rw [← ha]
  rfl

/-- An inclusion of ideals induces an algebra homomorphism between completions,
whose underlying linear map is the inclusion-induced map. -/
def mapOfLEₐ (hJK : J ≤ K) : AdicCompletion J A →ₐ[A] AdicCompletion K A :=
  AlgHom.ofLinearMap (mapOfLE A hJK)
    (by
      apply ext_evalₐ
      intro n
      simp only [evalₐ_mapOfLE, map_one])
    (by
      intro x y
      apply ext_evalₐ
      intro n
      simp only [evalₐ_mapOfLE, map_mul])

/-- Bundling the inclusion map does not change its underlying linear map. -/
@[simp]
theorem mapOfLEₐ_toLinearMap (hJK : J ≤ K) :
    (mapOfLEₐ A hJK).toLinearMap = mapOfLE A hJK := rfl

/-- The algebra inclusion map is the existing linear inclusion map on every input. -/
theorem mapOfLEₐ_apply (hJK : J ≤ K) (x : AdicCompletion J A) :
    mapOfLEₐ A hJK x = mapOfLE A hJK x := rfl

/-- Inclusion maps preserve canonical images of ring elements. -/
@[simp]
theorem mapOfLEₐ_of (hJK : J ≤ K) (a : A) :
    mapOfLEₐ A hJK (of J A a) = of K A a :=
  mapOfLE_of A hJK a

/-- Evaluation in the ideal quotient is the canonical algebra factor map. -/
theorem mapOfLEₐ_evalₐ (hJK : J ≤ K) (n : ℕ) (x : AdicCompletion J A) :
    evalₐ K n (mapOfLEₐ A hJK x) =
      Ideal.Quotient.factorₐ A (Ideal.pow_right_mono hJK n) (evalₐ J n x) :=
  evalₐ_mapOfLE A hJK n x

/-- Evaluation in the module quotient is the existing module factor map. -/
theorem mapOfLEₐ_eval (hJK : J ≤ K) (n : ℕ) (x : AdicCompletion J A) :
    eval K A n (mapOfLEₐ A hJK x) =
      Submodule.factor (Submodule.smul_mono_left (Ideal.pow_right_mono hJK n))
        (eval J A n x) :=
  mapOfLE_eval A hJK n x

/-- Changing an ideal to itself gives the identity algebra homomorphism. -/
@[simp]
theorem mapOfLEₐ_id (J : Ideal A) :
    mapOfLEₐ A (le_refl J) = AlgHom.id A (AdicCompletion J A) := by
  apply AlgHom.ext
  intro x
  exact LinearMap.congr_fun (mapOfLE_id A J) x

/-- Algebra inclusion maps compose in the order of the ideal inclusions. -/
theorem mapOfLEₐ_comp (hJK : J ≤ K) (hKL : K ≤ L) :
    (mapOfLEₐ A hKL).comp (mapOfLEₐ A hJK) = mapOfLEₐ A (hJK.trans hKL) := by
  apply AlgHom.ext
  intro x
  exact LinearMap.congr_fun (mapOfLE_comp A hJK hKL) x

end AdicCompletion
