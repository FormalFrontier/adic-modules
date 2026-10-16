/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Exactness
public import AdicModules.AdicCompletion.FinitePresentation
public import AdicModules.AdicCompletion.TensorProduct
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Completion and tensor products for the integer residue module

The integer residue module `ZMod 2` over `ℤ` is finitely presented but not projective.
Its completion at `(2)` has a nonzero canonical element. The sequence
`ℤ --(×2)→ ℤ → ZMod 2` is exact, its quotient map is surjective, its range has
induced/intrinsic adic cofinality, and its completed sequence is exact.

The canonical completion–tensor comparison is bijective by the finite-presentation
comparison applied to Artin–Rees finite-free cofinality over `ℤ`. Its forward map is the
completed-ring-linear `AdicCompletion.ofTensorProduct`.

## Implementation notes

These examples use Mathlib's algebraic inverse-limit adic completion, without identifying
another intrinsic or universal completeness convention.

## References

The models use Mathlib's finite-presentation and projective-lifting APIs and the
Artin–Rees lemma `Ideal.exists_pow_inf_eq_pow_smul`. Completed exactness uses
`AdicCompletion.map_exact_of_range_cofinal`, following the Cauchy-sequence proof of
Judith Ludwig and Christian Merten in `Mathlib.RingTheory.AdicCompletion.Exactness`.
The comparison uses `AdicCompletion.ofTensorProduct_bijective_of_finitePresentation`
and Mathlib's finite-presentation and Artin–Rees inputs.
-/

set_option warningAsError true

namespace IntegerResidue

/-- The integer residue module modulo two is finitely presented. -/
public theorem finitePresentation : Module.FinitePresentation ℤ (ZMod 2) :=
  Module.finitePresentation_of_finite ℤ (ZMod 2)

private def quotient : ℤ →ₗ[ℤ] ZMod 2 :=
  { toFun := fun z => z
    map_add' := Int.cast_add
    map_smul' := fun z w => by simp [zsmul_eq_mul] }

private theorem quotient_surjective : Function.Surjective quotient :=
  ZMod.intCast_surjective

private def double : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id

private theorem double_apply (z : ℤ) : double z = 2 * z := by
  change (2 : ℤ) • z = 2 * z
  exact smul_eq_mul _ _

private theorem double_injective : Function.Injective double := by
  intro a b h
  have hmul : (2 : ℤ) * a = 2 * b :=
    (double_apply a).symm.trans (h.trans (double_apply b))
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) hmul

private theorem residue_exact : Function.Exact double quotient := by
  intro z
  change (z : ZMod 2) = 0 ↔ ∃ a : ℤ, double a = z
  simp only [double_apply]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.symm⟩

private theorem finite_free_cofinality :
    ∀ (n : ℕ) (N : Submodule ℤ (Fin n → ℤ)), N.FG →
      ∀ k : ℕ, ∃ l : ℕ,
        N ⊓ ((Ideal.span {(2 : ℤ)}) ^ l • ⊤ : Submodule ℤ (Fin n → ℤ)) ≤
          (Ideal.span {(2 : ℤ)}) ^ k • N := by
  intro n N _ k
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.span {(2 : ℤ)}) N
  refine ⟨k + c, ?_⟩
  rw [inf_comm, hc (k + c) (Nat.le_add_left c k), Nat.add_sub_cancel]
  exact smul_mono_right _ inf_le_right

private theorem range_cofinality :
    ∀ k : ℕ, ∃ l : ℕ,
      LinearMap.range double ⊓
          ((Ideal.span {(2 : ℤ)}) ^ l • ⊤ : Submodule ℤ ℤ) ≤
        (Ideal.span {(2 : ℤ)}) ^ k • LinearMap.range double := by
  intro k
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul
    (Ideal.span {(2 : ℤ)}) (LinearMap.range double)
  refine ⟨k + c, ?_⟩
  rw [inf_comm, hc (k + c) (Nat.le_add_left c k), Nat.add_sub_cancel]
  exact smul_mono_right _ inf_le_right

private theorem completed_residue_exact :
    Function.Exact (AdicCompletion.map (Ideal.span {(2 : ℤ)}) double)
      (AdicCompletion.map (Ideal.span {(2 : ℤ)}) quotient) :=
  AdicCompletion.map_exact_of_range_cofinal residue_exact quotient_surjective range_cofinality

private theorem not_projective : ¬ Module.Projective ℤ (ZMod 2) := by
  intro hp
  let : Module.Projective ℤ (ZMod 2) := hp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property quotient
    (LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2) quotient_surjective
  have htwo : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
  have ht_smul := s.map_smul (2 : ℤ) (1 : ZMod 2)
  rw [htwo, map_zero] at ht_smul
  have ht : (2 : ℤ) * s 1 = 0 := by
    simpa only [smul_eq_mul] using ht_smul.symm
  have hs1 : s (1 : ZMod 2) = 0 :=
    (mul_eq_zero.mp ht).resolve_left (by decide)
  have hsplit : quotient (s 1) = 1 := LinearMap.congr_fun hs 1
  have hzero : (0 : ZMod 2) = 1 := by
    simpa only [hs1, map_zero] using hsplit
  exact zero_ne_one hzero

private theorem two_span_smul_top :
    (Ideal.span {(2 : ℤ)}) • (⊤ : Submodule ℤ (ZMod 2)) = ⊥ := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  apply le_antisymm _ bot_le
  refine Submodule.smul_le.mpr ?_
  intro r hr m _
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hr
  simp [zsmul_eq_mul, htwo]

private theorem completed_generator_ne_zero :
    AdicCompletion.of (Ideal.span {(2 : ℤ)}) (ZMod 2) 1 ≠ 0 := by
  intro h
  have he := congrArg (AdicCompletion.eval (Ideal.span {(2 : ℤ)}) (ZMod 2) 1) h
  have hmem : (1 : ZMod 2) ∈
      (Ideal.span {(2 : ℤ)}) ^ 1 • (⊤ : Submodule ℤ (ZMod 2)) :=
    (Submodule.Quotient.mk_eq_zero _).mp (by
      simpa only [AdicCompletion.eval_of, map_zero, Submodule.mkQ_apply] using he)
  exact one_ne_zero (by simpa only [pow_one, two_span_smul_top, Submodule.mem_bot] using hmem)

private theorem canonical_comparison_bijective :
    Function.Bijective (AdicCompletion.ofTensorProduct (Ideal.span {(2 : ℤ)}) (ZMod 2)) := by
  let : Module.FinitePresentation ℤ (ZMod 2) := finitePresentation
  exact AdicCompletion.ofTensorProduct_bijective_of_finitePresentation _ _ finite_free_cofinality

end IntegerResidue
