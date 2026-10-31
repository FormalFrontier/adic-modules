/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Kernel

/-!
# Evaluation of stationary adic completions

For any ideal `I` of a commutative ring `R` and any `R`-module `M`, evaluation at `n`
is injective exactly when the original power submodules at `n` and `n + 1` agree.
Since evaluation is always surjective, this equality identifies the whole completion
with `M ⧸ (I ^ n • ⊤)`, through the evaluation map. The inverse sends the residue
of an original element to its image under `AdicCompletion.of`.

Equality of the ideal powers themselves gives an algebra equivalence from
`AdicCompletion I R` to `R ⧸ I ^ n`, through the coefficient evaluation.

## Implementation notes

All natural indices, including zero, are allowed. Neither ideal finite generation,
Noetherianity, finite generation of the module, nor completeness or separation of the
original module is required. The module condition alone does not identify the completed
coefficient ring with `R ⧸ I ^ n`.

## References

The sufficient direction specializes the finite-coefficient kernel argument in
`AdicModules.AdicCompletion.Kernel` to the zero auxiliary ideal. That argument adapts
Bingyu Xia's Mathlib formalization in `RingTheory/AdicCompletion/Completeness.lean`.
The necessary direction uses the canonical map and evaluations from Mathlib's completion
formalization by Kenny Lau, Judith Ludwig, Christian Merten and Jiedong Jiang.
The equivalences bundle these evaluations using Mathlib's linear and algebra equivalence
APIs; the algebra refinement uses its coefficient-quotient normalization.
-/

@[expose] public section

universe uR uM

namespace AdicCompletion

variable {R : Type uR} [CommRing R]

/-- Evaluation at `n` is injective exactly when the original power submodules at
`n` and `n + 1` agree. -/
theorem eval_injective_iff_pow_smul_top_eq
    (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M] (n : ℕ) :
    Function.Injective (AdicCompletion.eval I M n) ↔
      (I ^ (n + 1) • (⊤ : Submodule R M)) = I ^ n • ⊤ := by
  constructor
  · intro hinj
    refine le_antisymm (Submodule.pow_smul_top_le I M (Nat.le_succ n)) ?_
    intro m hm
    have heval : eval I M n (of I M m) = eval I M n 0 := by
      rw [_root_.map_zero, eval_of]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hm
    have hof : of I M m = 0 := hinj heval
    apply (Submodule.Quotient.mk_eq_zero _).mp
    simpa only [eval_of, _root_.map_zero, Submodule.mkQ_apply] using
      congrArg (eval I M (n + 1)) hof
  · intro h
    apply LinearMap.ker_eq_bot.mp
    have hker := smul_top_eq_ker_eval_of_fg_sup_pow_smul I ⊥ M n
      Submodule.fg_bot (by simpa only [Submodule.bot_smul, bot_sup_eq] using h)
    simpa only [Submodule.bot_smul] using hker.symm

/-- Evaluation identifies the whole completion with the original module modulo
`I ^ n • ⊤` when two consecutive original power submodules agree. -/
noncomputable def linearEquivQuotientOfPowSMulTopEq
    (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M] (n : ℕ)
    (h : I ^ (n + 1) • (⊤ : Submodule R M) = I ^ n • (⊤ : Submodule R M)) :
    AdicCompletion I M ≃ₗ[R] (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
  LinearEquiv.ofBijective (eval I M n)
    ⟨(eval_injective_iff_pow_smul_top_eq I M n).mpr h, eval_surjective I M n⟩

/-- The forward linear equivalence is evaluation at `n`. -/
@[simp]
theorem linearEquivQuotientOfPowSMulTopEq_apply
    (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M] (n : ℕ)
    (h : I ^ (n + 1) • (⊤ : Submodule R M) = I ^ n • (⊤ : Submodule R M))
    (x : AdicCompletion I M) :
    linearEquivQuotientOfPowSMulTopEq I M n h x = AdicCompletion.eval I M n x :=
  rfl

/-- The inverse linear equivalence sends an original residue to its canonical
image in the completion. -/
@[simp]
theorem linearEquivQuotientOfPowSMulTopEq_symm_apply_mkQ
    (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M] (n : ℕ)
    (h : I ^ (n + 1) • (⊤ : Submodule R M) = I ^ n • (⊤ : Submodule R M))
    (m : M) :
    (linearEquivQuotientOfPowSMulTopEq I M n h).symm
      (Submodule.Quotient.mk m) = AdicCompletion.of I M m := by
  apply (linearEquivQuotientOfPowSMulTopEq I M n h).injective
  rw [LinearEquiv.apply_symm_apply, linearEquivQuotientOfPowSMulTopEq_apply, eval_of,
    Submodule.mkQ_apply]

/-- Equality of consecutive ideal powers identifies the whole coefficient completion
with the original ideal-power quotient as an algebra over the original ring. -/
noncomputable def algEquivQuotientOfPowEq
    (I : Ideal R) (n : ℕ) (h : I ^ (n + 1) = I ^ n) :
    AdicCompletion I R ≃ₐ[R] (R ⧸ I ^ n) :=
  AlgEquiv.ofBijective (evalₐ I n) ⟨by
    intro x y hxy
    apply (linearEquivQuotientOfPowSMulTopEq I R n
      (congrArg (fun J : Ideal R => J • (⊤ : Submodule R R)) h)).injective
    rw [linearEquivQuotientOfPowSMulTopEq_apply, linearEquivQuotientOfPowSMulTopEq_apply]
    have htop : (I ^ n • ⊤ : Ideal R) = I ^ n := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [← factor_evalₐ_eq_eval I x htop.ge, ← factor_evalₐ_eq_eval I y htop.ge, hxy],
    surjective_evalₐ I n⟩

/-- The forward algebra equivalence is coefficient evaluation at `n`. -/
@[simp]
theorem algEquivQuotientOfPowEq_apply
    (I : Ideal R) (n : ℕ) (h : I ^ (n + 1) = I ^ n)
    (x : AdicCompletion I R) :
    algEquivQuotientOfPowEq I n h x = AdicCompletion.evalₐ I n x :=
  rfl

/-- The inverse algebra equivalence sends an original residue to its image under
the canonical algebra map into the completion. -/
@[simp]
theorem algEquivQuotientOfPowEq_symm_apply_mk
    (I : Ideal R) (n : ℕ) (h : I ^ (n + 1) = I ^ n) (r : R) :
    (algEquivQuotientOfPowEq I n h).symm (Ideal.Quotient.mk (I ^ n) r) =
      algebraMap R (AdicCompletion I R) r := by
  simpa only [Ideal.Quotient.algebraMap_eq] using
    (algEquivQuotientOfPowEq I n h).symm.commutes r

end AdicCompletion
