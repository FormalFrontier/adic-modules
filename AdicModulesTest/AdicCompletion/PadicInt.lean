/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.PadicInt
public import AdicModules.AdicCompletion.PadicIntTopology
public import AdicModules.Topology.Algebra.PadicInt
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Nonzero integer-completion and p-adic inputs

The canonical image of `1` in the `(2)`-adic completion of `ℤ` is nonzero: the existing
completion evaluation at precision one detects its nonzero residue in `ZMod 2`.
The p-adic integer `1` is independently nonzero. Neither assertion uses the comparison
or any of its characteristic laws.

At precision zero the residue ring is `ZMod 1`, so the same nonzero element has zero
coordinate there. The unit generator also has only the trivial residue ring.
-/

namespace AdicModulesTest.AdicCompletion.PadicInt

private theorem integer_completion_two_one_ne_zero :
    AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ 1 ≠ 0 := by
  intro h
  have heval := congrArg (AdicCompletion.evalₐ (Ideal.span {(2 : ℤ)}) 1) h
  rw [AdicCompletion.evalₐ_of, map_zero] at heval
  have hres := congrArg (Ideal.quotEquivOfEq (pow_one (Ideal.span {(2 : ℤ)}))) heval
  have hmod : (1 : ZMod 2) = 0 := by
    simpa using congrArg (Int.quotientSpanNatEquivZMod 2) hres
  exact one_ne_zero hmod

private theorem padicInt_two_one_ne_zero : (1 : ℤ_[2]) ≠ 0 := one_ne_zero

private theorem integer_completion_precision_zero :
    AdicCompletion.evalZModPow 2 0
      (AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ 1) = 0 := by
  have : Subsingleton (ZMod (2 ^ 0)) := by
    rw [pow_zero]
    infer_instance
  exact Subsingleton.elim _ _

private theorem integer_completion_unit_residue (n : ℕ)
    (x : AdicCompletion (Ideal.span {(1 : ℤ)}) ℤ) :
    AdicCompletion.evalZModPow 1 n x = 0 := by
  have : Subsingleton (ZMod (1 ^ n)) := by
    rw [one_pow]
    infer_instance
  exact Subsingleton.elim _ _

/-- The canonical integer-completion input and the p-adic integer input at two are nonzero. -/
public theorem integer_completion_and_padicInt_two_one_ne_zero :
    AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ 1 ≠ 0 ∧ (1 : ℤ_[2]) ≠ 0 :=
  ⟨integer_completion_two_one_ne_zero, padicInt_two_one_ne_zero⟩

private theorem integer_completion_two_comparison (a : ℤ) (n : ℕ) :
    AdicCompletion.padicIntEquiv 2
        (AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ a) = (a : ℤ_[2]) ∧
      PadicInt.toZModPow n
        (AdicCompletion.padicIntEquiv 2
          (AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ a)) = (a : ZMod (2 ^ n)) ∧
      AdicCompletion.evalZModPow 2 n
        ((AdicCompletion.padicIntEquiv 2).symm (a : ℤ_[2])) = (a : ZMod (2 ^ n)) ∧
      (AdicCompletion.padicIntEquiv 2).symm (a : ℤ_[2]) =
        AdicCompletion.of (Ideal.span {(2 : ℤ)}) ℤ a := by
  refine ⟨AdicCompletion.padicIntEquiv_of 2 a, ?_, ?_,
    AdicCompletion.padicIntEquiv_symm_intCast 2 a⟩
  · rw [AdicCompletion.toZModPow_padicIntEquiv 2 n]
    exact AdicCompletion.evalZModPow_of 2 n a
  · rw [AdicCompletion.evalZModPow_padicIntEquiv_symm 2 n]
    exact map_intCast (PadicInt.toZModPow n) a

end AdicModulesTest.AdicCompletion.PadicInt

/-!
## A proper mod-four neighborhood under the same comparison

The domain has the adic topology for the mapped ideal and the target keeps its usual
norm topology. The proper neighborhoods and their residue equations follow from the
power-kernel theorem, the norm-neighborhood basis, and the algebraic comparison laws,
independently of continuity of the comparison.
-/

open scoped Topology

namespace AdicModulesTest.AdicCompletion.PadicInt

local notation "I₂" => (Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ)
local notation "C₂" => AdicCompletion I₂ ℤ
local notation "J₂" => Ideal.map (algebraMap ℤ C₂) I₂
local notation "U₂" => (RingHom.ker (AdicCompletion.evalZModPow 2 2) : Set C₂)
local notation "V₂" => (RingHom.ker (PadicInt.toZModPow (p := 2) 2) : Set ℤ_[2])

private theorem integer_completion_two_mod_four_mem_iff (x : C₂) :
    x ∈ U₂ ↔ x ∈ (J₂ ^ 2 : Ideal C₂) := by
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem ℤ,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton ((2 : ℕ) : ℤ)),
    LinearMap.mem_ker]
  change AdicCompletion.evalZModPow 2 2 x = 0 ↔ AdicCompletion.eval I₂ ℤ 2 x = 0
  constructor
  · intro hx
    have ha : AdicCompletion.evalₐ I₂ 2 x = 0 := by
      simpa [AdicCompletion.evalZModPow] using hx
    rw [← AdicCompletion.factor_evalₐ_eq_eval I₂ x (by simp), ha, map_zero]
  · intro hx
    have ha : AdicCompletion.evalₐ I₂ 2 x = 0 := by
      rw [← AdicCompletion.factor_eval_eq_evalₐ I₂ x (by simp), hx, map_zero]
    simpa [AdicCompletion.evalZModPow] using ha

private theorem integer_completion_two_mod_four_model :
    U₂ ∈ @nhds C₂ (J₂).adicTopology 0 ∧
      AdicCompletion.of I₂ ℤ 4 ∈ U₂ ∧
      AdicCompletion.of I₂ ℤ 1 ∉ U₂ ∧
      V₂ ∈ 𝓝 (0 : ℤ_[2]) ∧
      (4 : ℤ_[2]) ∈ V₂ ∧ (1 : ℤ_[2]) ∉ V₂ ∧
      (AdicCompletion.padicIntEquiv 2) ⁻¹' V₂ = U₂ ∧
      (AdicCompletion.of I₂ ℤ 1 ≠ 0 ∧ (1 : ℤ_[2]) ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    integer_completion_and_padicInt_two_one_ne_zero⟩
  · have hU : U₂ = (↑(J₂ ^ 2) : Set C₂) :=
      Set.ext integer_completion_two_mod_four_mem_iff
    rw [hU]
    exact (Ideal.hasBasis_nhds_zero_adic J₂).mem_iff.mpr ⟨2, trivial, Set.Subset.rfl⟩
  · change AdicCompletion.evalZModPow 2 2 (AdicCompletion.of I₂ ℤ 4) = 0
    rw [AdicCompletion.evalZModPow_of 2 2 4]
    decide
  · change AdicCompletion.evalZModPow 2 2 (AdicCompletion.of I₂ ℤ 1) ≠ 0
    rw [AdicCompletion.evalZModPow_of 2 2 1]
    exact (by decide : (1 : ZMod (2 ^ 2)) ≠ 0)
  · rw [PadicInt.ker_toZModPow]
    exact (PadicInt.hasBasis_nhds_zero_span_pow 2).mem_iff.mpr
      ⟨2, trivial, Set.Subset.rfl⟩
  · change PadicInt.toZModPow (p := 2) 2 (4 : ℤ_[2]) = 0
    rw [map_ofNat]
    decide
  · change PadicInt.toZModPow (p := 2) 2 (1 : ℤ_[2]) ≠ 0
    rw [map_one]
    decide
  · ext x
    change PadicInt.toZModPow 2 (AdicCompletion.padicIntEquiv 2 x) = 0 ↔
      AdicCompletion.evalZModPow 2 2 x = 0
    rw [AdicCompletion.toZModPow_padicIntEquiv]

/-- The mod-four kernel is open in the mapped-ideal topology; the same comparison
sends it onto the proper open mod-four kernel in the usual norm topology. -/
private theorem integer_completion_two_mod_four_open_image :
    U₂ ∈ @nhds C₂ (J₂).adicTopology 0 ∧
      @IsOpen C₂ (J₂).adicTopology U₂ ∧
      (AdicCompletion.padicIntEquiv 2) '' U₂ = V₂ ∧
      IsOpen V₂ ∧ V₂ ≠ Set.univ := by
  let : WithIdeal C₂ := ⟨J₂⟩
  have hU : U₂ ∈ @nhds C₂ (J₂).adicTopology 0 := by
    rw [← Ideal.adicModuleTopology_eq_adicTopology_map]
    apply (AdicCompletion.hasBasis_nhds_zero_ker_eval I₂ ℤ
      (Submodule.fg_span_singleton ((2 : ℕ) : ℤ))).mem_iff.mpr
    refine ⟨2, trivial, ?_⟩
    intro x hx
    apply (integer_completion_two_mod_four_mem_iff x).mpr
    rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem ℤ,
      ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval
        (Submodule.fg_span_singleton ((2 : ℕ) : ℤ))]
    exact hx
  have hUopen : IsOpen U₂ :=
    (RingHom.ker (AdicCompletion.evalZModPow 2 2)).toAddSubgroup.isOpen_of_mem_nhds hU
  have himage : (AdicCompletion.padicIntEquiv 2) '' U₂ = V₂ := by
    rw [← integer_completion_two_mod_four_model.2.2.2.2.2.2.1]
    exact Set.image_preimage_eq _ (AdicCompletion.padicIntEquiv 2).surjective
  refine ⟨hU, hUopen, himage, ?_, ?_⟩
  · rw [← himage]
    exact (AdicCompletion.isHomeomorph_padicIntEquiv 2).isOpenMap _ hUopen
  · intro hV
    exact integer_completion_two_mod_four_model.2.2.2.2.2.1
      (hV ▸ Set.mem_univ (1 : ℤ_[2]))

end AdicModulesTest.AdicCompletion.PadicInt
