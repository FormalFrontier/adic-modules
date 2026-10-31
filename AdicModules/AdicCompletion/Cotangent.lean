/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Ideal.Cotangent
public import AdicModules.AdicCompletion.TensorProduct
public import AdicModules.AdicCompletion.Completeness

import AdicModules.AdicCompletion.Kernel
import AdicModules.AdicCompletion.Quotient
import AdicModules.Noetherian
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Finite cotangent modules and adic completion

Let `I` be an arbitrary ideal of a commutative ring `R`. If the original cotangent
module `I.Cotangent` is finite over `R ⧸ I`, then the extension of `I` to its raw
completion is finitely generated. Specified original cotangent generators generate
this extended ideal. Every power of the extended ideal is the kernel of the
corresponding evaluation, and the completion is intrinsically complete for that ideal.

Consequently, the raw completion is Noetherian exactly when the original residue
ring is Noetherian and the original cotangent module is finite. No finite generation
of the original ideal, or completeness or separatedness of the original ring, is assumed.
Equivalently, at any exponent at least two, the original power quotient is Noetherian.
The pure ideal cotangent-finiteness bridge and unconditional evaluation surjectivity
reduce this criterion to the residue-and-cotangent criterion.

The structural argument chooses a finitely generated ideal `H ≤ I` with
`I = H ⊔ I ^ 2`. The shared fixed-stage kernel theorem in
`AdicModules.AdicCompletion.Kernel` identifies its completed scalar span with the
first evaluation kernel. This proves the specified-generator statement without a
separate completed-range argument. The same kernel theorem computes every ideal-power
filtration on every completed module, and the shared diagonal argument gives intrinsic
completeness.

## References

The proof uses Andrew Yang's cotangent-module APIs in Mathlib, together with Mathlib's
completion functor, shifted-power inclusion and quotient APIs. The finite-first-quotient
and specified-generator results are from `AdicModules.AdicCompletion.TensorProduct`.
The forward Noetherian implication uses the finitely generated ideal criterion in
`AdicModules.Noetherian`, formalizing the criterion of K. Fujiwara and F. Kato,
*Foundations of Rigid Geometry I*, arXiv:1308.4734v5.
-/

@[expose] public section

universe uR uι

namespace AdicCompletion

variable {R : Type uR} [CommRing R]

/-- Original cotangent generators generate the extended ideal in the raw completion. -/
theorem map_eq_span_of_span_toCotangent_eq_top (I : Ideal R)
    {ι : Type uι} [Finite ι] (v : ι → I)
    (hv : Submodule.span (R ⧸ I)
      (Set.range (fun i : ι => I.toCotangent (v i))) = ⊤) :
    I.map (algebraMap R (AdicCompletion I R)) =
      Ideal.span (Set.range (fun i : ι =>
        algebraMap R (AdicCompletion I R) (v i : R))) := by
  let H : Ideal R := Ideal.span (Set.range (fun i : ι => (v i : R)))
  have hHI : H ≤ I := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (v i).property)
  have hI : I = H ⊔ I ^ 2 := Ideal.eq_span_sup_sq_of_span_toCotangent_eq_top I v hv
  have hH : H.FG := Submodule.fg_span (Set.finite_range _)
  have hHker : H • (⊤ : Submodule R (AdicCompletion I R)) = (eval I R 1).ker := by
    apply smul_top_eq_ker_eval_of_fg_sup_pow I H R 1 hH
    simpa only [pow_one] using hI.symm
  have hle : I • (⊤ : Submodule R (AdicCompletion I R)) ≤
      H • (⊤ : Submodule R (AdicCompletion I R)) := by
    rw [hHker]
    simpa only [pow_one] using (pow_smul_top_le_ker_eval (I := I) (M := R) 1)
  have hmap : I.map (algebraMap R (AdicCompletion I R)) =
      H.map (algebraMap R (AdicCompletion I R)) := by
    apply Submodule.restrictScalars_injective R (AdicCompletion I R) (AdicCompletion I R)
    rw [← Ideal.smul_top_eq_map, ← Ideal.smul_top_eq_map]
    exact le_antisymm hle (Submodule.smul_mono_left hHI)
  rw [hmap]
  dsimp only [H]
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- Finite original cotangent makes the extended ideal finitely generated. -/
theorem fg_map_of_finite_cotangent (I : Ideal R)
    [Module.Finite (R ⧸ I) I.Cotangent] :
    (I.map (algebraMap R (AdicCompletion I R))).FG := by
  obtain ⟨k, v, hv⟩ := Ideal.exists_fin_span_toCotangent_eq_top I
  rw [map_eq_span_of_span_toCotangent_eq_top I v hv]
  exact Submodule.fg_span (Set.finite_range _)

/-- Finite original cotangent identifies every power of the extended ideal with
the kernel of canonical coefficient evaluation. -/
theorem map_pow_eq_ker_evalₐ_of_finite_cotangent (I : Ideal R)
    [Module.Finite (R ⧸ I) I.Cotangent] (n : ℕ) :
    (I.map (algebraMap R (AdicCompletion I R))) ^ n =
      RingHom.ker (evalₐ I n).toRingHom :=
  map_pow_eq_ker_evalₐ I n (pow_smul_top_eq_ker_eval_of_finite_cotangent I R n)

/-- Noetherian residue and finite original cotangent imply Noetherian raw completion.
The proof applies the finitely generated ideal criterion of Fujiwara–Kato,
*Foundations of Rigid Geometry I*, to the extended ideal. -/
theorem isNoetherianRing_of_finite_cotangent (I : Ideal R)
    [IsNoetherianRing (R ⧸ I)] [Module.Finite (R ⧸ I) I.Cotangent] :
    IsNoetherianRing (AdicCompletion I R) := by
  let J : Ideal (AdicCompletion I R) := I.map (algebraMap R (AdicCompletion I R))
  let : IsAdicComplete J (AdicCompletion I R) := isAdicComplete_map_of_finite_cotangent I R
  let e : (AdicCompletion I R ⧸ J) ≃+* (R ⧸ I) :=
    ((Ideal.quotientEquivAlgOfEq R (pow_one J).symm).trans
      ((Ideal.quotientEquivAlgOfEq R (map_pow_eq_ker_evalₐ_of_finite_cotangent I 1)).trans
        ((Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I 1)).trans
          (Ideal.quotientEquivAlgOfEq R (pow_one I))))).toRingEquiv
  let : IsNoetherianRing (AdicCompletion I R ⧸ J) :=
    isNoetherianRing_of_ringEquiv (R ⧸ I) e.symm
  exact IsAdicComplete.isNoetherianRing_of_fg J (fg_map_of_finite_cotangent I)

/-- Noetherian raw completion implies finiteness of the original cotangent module
for its original residue action. -/
theorem finite_cotangent_of_isNoetherianRing (I : Ideal R)
    [IsNoetherianRing (AdicCompletion I R)] :
    Module.Finite (R ⧸ I) I.Cotangent := by
  let : IsNoetherianRing (R ⧸ I ^ 2) :=
    isNoetherianRing_of_surjective (AdicCompletion I R) (R ⧸ I ^ 2)
      (evalₐ I 2).toRingHom (surjective_evalₐ I 2)
  exact Ideal.finite_cotangent_of_isNoetherianRing_quotient_pow I (le_refl 2)

/-- Noetherianity of raw completion is equivalent to Noetherian residue and
finite original cotangent, with no original ideal-finiteness or completeness premise.
The implication from the residue and cotangent uses the finitely generated
ideal criterion of Fujiwara–Kato, *Foundations of Rigid Geometry I*. -/
theorem isNoetherianRing_iff_quotient_and_finite_cotangent (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) ↔
      IsNoetherianRing (R ⧸ I) ∧ Module.Finite (R ⧸ I) I.Cotangent := by
  constructor
  · intro hS
    let : IsNoetherianRing (AdicCompletion I R) := hS
    exact ⟨isNoetherianRing_of_surjective (AdicCompletion I R) (R ⧸ I)
      (evalOneₐ I).toRingHom (evalOneₐ_surjective I),
      finite_cotangent_of_isNoetherianRing I⟩
  · rintro ⟨hquot, hcot⟩
    let : IsNoetherianRing (R ⧸ I) := hquot
    let : Module.Finite (R ⧸ I) I.Cotangent := hcot
    exact isNoetherianRing_of_finite_cotangent I

/-- At every exponent at least two, Noetherianity of the original power quotient
is equivalent to Noetherianity of the adic completion. -/
theorem isNoetherianRing_iff_quotient_pow
    (I : Ideal R) {n : ℕ} (hn : 2 ≤ n) :
    IsNoetherianRing (AdicCompletion I R) ↔
      IsNoetherianRing (R ⧸ I ^ n) := by
  constructor
  · intro hS
    let : IsNoetherianRing (AdicCompletion I R) := hS
    exact isNoetherianRing_of_surjective (AdicCompletion I R) (R ⧸ I ^ n)
      (evalₐ I n).toRingHom (surjective_evalₐ I n)
  · intro hquot
    let : IsNoetherianRing (R ⧸ I ^ n) := hquot
    have hle : I ^ n ≤ I :=
      Ideal.pow_le_self (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn))
    let : IsNoetherianRing (R ⧸ I) :=
      isNoetherianRing_of_surjective (R ⧸ I ^ n) (R ⧸ I)
        (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    let : Module.Finite (R ⧸ I) I.Cotangent :=
      Ideal.finite_cotangent_of_isNoetherianRing_quotient_pow I hn
    exact isNoetherianRing_of_finite_cotangent I

end AdicCompletion
