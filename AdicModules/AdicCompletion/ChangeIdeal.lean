/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Changing the ideal of an adic completion

A uniform power containment on the original module induces an original-ring-linear
map between adic completions. Ambient ideal containments are special cases. Its value at every
  admissible quotient level is the canonical
factor map, independently of the power witness used in its construction.
-/

@[expose] public section

noncomputable section

universe uR uM uN

open Submodule

namespace AdicCompletion

variable {R : Type uR} [CommRing R]

/-- A uniform power bound on the original module gives bounds at every power.
The exponent `a` may be zero. -/
theorem pow_mul_smul_top_le (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] {a : ℕ}
    (h : (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (n : ℕ) :
    (I ^ (a * n) • ⊤ : Submodule R M) ≤ J ^ n • ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (I ^ (a * (n + 1)) • ⊤ : Submodule R M) =
          I ^ (a * n) • (I ^ a • ⊤ : Submodule R M) := by
        rw [Nat.mul_succ, pow_add, ← Ideal.smul_eq_mul, Submodule.smul_assoc]
      _ ≤ I ^ (a * n) • (J • ⊤ : Submodule R M) := smul_mono le_rfl h
      _ = J • (I ^ (a * n) • ⊤ : Submodule R M) := by
        rw [← Submodule.smul_assoc, ← Submodule.smul_assoc,
          Ideal.smul_eq_mul, Ideal.smul_eq_mul, mul_comm]
      _ ≤ J • (J ^ n • ⊤ : Submodule R M) := smul_mono le_rfl ih
      _ = J ^ (n + 1) • (⊤ : Submodule R M) := by
        rw [← Submodule.smul_assoc, Ideal.smul_eq_mul, pow_succ']

/-- Uniform power comparison on a module is equivalent to cofinality of its
ideal-power submodules. No finiteness assumption is needed. -/
theorem exists_pow_smul_top_le_iff (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] :
    (∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) ↔
      ∀ n : ℕ, ∃ m : ℕ, (I ^ m • ⊤ : Submodule R M) ≤ J ^ n • ⊤ := by
  constructor
  · rintro ⟨a, ha⟩ n
    exact ⟨a * n, pow_mul_smul_top_le I J M ha n⟩
  · intro h
    obtain ⟨a, ha⟩ := h 1
    exact ⟨a, by simpa only [pow_one] using ha⟩

private theorem mapOfPowSMulLE_compatible (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (a : ℕ)
    (H : ∀ n : ℕ, (I ^ (a * n) • ⊤ : Submodule R M) ≤ J ^ n • ⊤) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      transitionMap J M hmn ∘ₗ ((factor (H n)).comp (eval I M (a * n))) =
        (factor (H m)).comp (eval I M (a * m)) := by
  intro m n hmn
  apply LinearMap.ext
  intro x
  change factor (pow_smul_top_le J M hmn)
      (factor (H n) (x.val (a * n))) = factor (H m) (x.val (a * m))
  rw [factor_comp_apply]
  rw [← transitionMap_comp_eval_apply (I := I) (M := M)
    (Nat.mul_le_mul_left a hmn) x]
  change factor ((H n).trans (pow_smul_top_le J M hmn)) (x.val (a * n)) =
    factor (H m)
      (factor (pow_smul_top_le I M (Nat.mul_le_mul_left a hmn)) (x.val (a * n)))
  rw [factor_comp_apply]

/-- A uniform power bound on the original module induces an original-ring-linear
map between its adic completions. The exponent may be zero. -/
noncomputable def mapOfPowSMulLE (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) :
    AdicCompletion I M →ₗ[R] AdicCompletion J M := by
  let a := hIJ.choose
  let H : ∀ n : ℕ, (I ^ (a * n) • ⊤ : Submodule R M) ≤ J ^ n • ⊤ :=
    fun n ↦ pow_mul_smul_top_le I J M hIJ.choose_spec n
  exact lift J (fun n ↦ (factor (H n)).comp (eval I M (a * n)))
    (by exact mapOfPowSMulLE_compatible I J M a H)

/-- At every admissible pair of stages, comparison is the quotient factor map.
The stage bound is on the original module, not on the ambient ideals. -/
theorem eval_mapOfPowSMulLE (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    {m n : ℕ} (h : (I ^ m • ⊤ : Submodule R M) ≤ J ^ n • ⊤)
    (x : AdicCompletion I M) :
    eval J M n (mapOfPowSMulLE I J M hIJ x) = factor h (eval I M m x) := by
  let a := hIJ.choose
  have hchosen : (I ^ (a * n) • ⊤ : Submodule R M) ≤ J ^ n • ⊤ :=
    pow_mul_smul_top_le I J M hIJ.choose_spec n
  have hstage : eval J M n (mapOfPowSMulLE I J M hIJ x) =
      factor hchosen (eval I M (a * n) x) := by
    let H : ∀ k : ℕ, (I ^ (a * k) • ⊤ : Submodule R M) ≤ J ^ k • ⊤ :=
      fun k ↦ pow_mul_smul_top_le I J M hIJ.choose_spec k
    exact LinearMap.congr_fun
      (AdicCompletion.eval_lift J
        (fun k ↦ (factor (H k)).comp (eval I M (a * k)))
        (mapOfPowSMulLE_compatible I J M a H) n) x
  rw [hstage]
  change factor hchosen (x.val (a * n)) = factor h (x.val m)
  rcases le_total m (a * n) with hma | ham
  · rw [← transitionMap_comp_eval_apply (I := I) (M := M) hma x]
    change factor hchosen (x.val (a * n)) =
      factor h (factor (pow_smul_top_le I M hma) (x.val (a * n)))
    rw [factor_comp_apply]
  · rw [← transitionMap_comp_eval_apply (I := I) (M := M) ham x]
    change factor hchosen (factor (pow_smul_top_le I M ham) (x.val m)) =
      factor h (x.val m)
    rw [factor_comp_apply]

/-- The evaluation equation for comparison, as an equality of linear maps. -/
theorem eval_comp_mapOfPowSMulLE (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    {m n : ℕ} (h : (I ^ m • ⊤ : Submodule R M) ≤ J ^ n • ⊤) :
    (eval J M n).comp (mapOfPowSMulLE I J M hIJ) = (factor h).comp (eval I M m) := by
  apply LinearMap.ext
  intro x
  exact eval_mapOfPowSMulLE I J M hIJ h x

/-- The equations at all admissible stages uniquely characterize comparison. -/
theorem mapOfPowSMulLE_unique (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (f : AdicCompletion I M →ₗ[R] AdicCompletion J M)
    (hf : ∀ {m n : ℕ} (h : (I ^ m • ⊤ : Submodule R M) ≤ J ^ n • ⊤)
      (x : AdicCompletion I M), eval J M n (f x) = factor h (eval I M m x)) :
    f = mapOfPowSMulLE I J M hIJ := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  have h := pow_mul_smul_top_le I J M hIJ.choose_spec n
  change eval J M n (f x) = eval J M n (mapOfPowSMulLE I J M hIJ x)
  rw [hf h x, eval_mapOfPowSMulLE I J M hIJ h]

/-- Comparison is independent of the uniform power bound used to construct it. -/
theorem mapOfPowSMulLE_congr (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ hIJ' : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) :
    mapOfPowSMulLE I J M hIJ = mapOfPowSMulLE I J M hIJ' := by
  apply mapOfPowSMulLE_unique
  intro m n h x
  exact eval_mapOfPowSMulLE I J M hIJ h x

/-- Changing the ideal commutes with the canonical map from the original module. -/
@[simp]
theorem mapOfPowSMulLE_of (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (x : M) :
    mapOfPowSMulLE I J M hIJ (of I M x) = of J M x := by
  apply AdicCompletion.ext
  intro n
  have h := pow_mul_smul_top_le I J M hIJ.choose_spec n
  change eval J M n (mapOfPowSMulLE I J M hIJ (of I M x)) = eval J M n (of J M x)
  rw [eval_mapOfPowSMulLE I J M hIJ h]
  rfl

/-- Every uniform power bound from a module filtration to itself gives the identity. -/
@[simp]
theorem mapOfPowSMulLE_self (I : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (hII : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ I • ⊤) :
    mapOfPowSMulLE I I M hII = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change eval I M n (mapOfPowSMulLE I I M hII x) = eval I M n x
  rw [eval_mapOfPowSMulLE I I M hII (le_refl (I ^ n • (⊤ : Submodule R M))) x]
  exact Quotient.inductionOn' (eval I M n x) (fun _ ↦ rfl)

/-- Maps induced by power containments compose, for any witness of the direct
containment. In particular, the resulting map does not depend on its witnesses. -/
theorem mapOfPowSMulLE_comp (I J K : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (hJK : ∃ b : ℕ, (J ^ b • ⊤ : Submodule
      R M) ≤ K • ⊤)
    (hIK : ∃ c : ℕ, (I ^ c • ⊤ : Submodule R M) ≤ K • ⊤) :
    (mapOfPowSMulLE J K M hJK).comp (mapOfPowSMulLE I J M hIJ) =
      mapOfPowSMulLE I K M hIK := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  have hJK_n := pow_mul_smul_top_le J K M hJK.choose_spec n
  have hIJ_bn := pow_mul_smul_top_le I J M hIJ.choose_spec (hJK.choose * n)
  change eval K M n (mapOfPowSMulLE J K M hJK (mapOfPowSMulLE I J M hIJ x)) =
    eval K M n (mapOfPowSMulLE I K M hIK x)
  rw [eval_mapOfPowSMulLE J K M hJK hJK_n,
    eval_mapOfPowSMulLE I J M hIJ hIJ_bn,
    eval_mapOfPowSMulLE I K M hIK (hIJ_bn.trans hJK_n)]
  rw [factor_comp_apply]

/-- Pointwise identity for comparison with the same ideal. -/
theorem mapOfPowSMulLE_self_apply (I : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hII : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ I • ⊤)
    (x : AdicCompletion I M) : mapOfPowSMulLE I I M hII x = x := by
  rw [mapOfPowSMulLE_self]
  rfl

/-- Pointwise composition of module comparisons. -/
theorem mapOfPowSMulLE_comp_apply (I J K : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hJK : ∃ a : ℕ, (J ^ a • ⊤ : Submodule R M) ≤ K • ⊤)
    (hIK : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ K • ⊤)
    (x : AdicCompletion I M) :
    mapOfPowSMulLE J K M hJK (mapOfPowSMulLE I J M hIJ x) =
      mapOfPowSMulLE I K M hIK x :=
  LinearMap.congr_fun (mapOfPowSMulLE_comp I J K M hIJ hJK hIK) x

/-- Mutual uniform power bounds on a module identify the two adic completions as modules over
  the original ring. -/
def equivOfCofinalSMul (I J : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule
      R M) ≤ I • ⊤) :
    AdicCompletion I M ≃ₗ[R] AdicCompletion J M where
  toLinearMap := mapOfPowSMulLE I J M hIJ
  invFun := mapOfPowSMulLE J I M hJI
  left_inv x := by
    have hII : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ I • ⊤ := ⟨1, by simp only [pow_one, le_refl]⟩
    change ((mapOfPowSMulLE J I M hJI).comp (mapOfPowSMulLE I J M hIJ)) x = x
    rw [mapOfPowSMulLE_comp I J I M hIJ hJI hII, mapOfPowSMulLE_self I M hII]
    rfl
  right_inv x := by
    have hJJ : ∃ a : ℕ, (J ^ a • ⊤ : Submodule R M) ≤ J • ⊤ :=
      ⟨1, by simp only [pow_one, le_refl]⟩
    change ((mapOfPowSMulLE I J M hIJ).comp (mapOfPowSMulLE J I M hJI)) x = x
    rw [mapOfPowSMulLE_comp J I J M hJI hIJ hJJ, mapOfPowSMulLE_self J M hJJ]
    rfl

@[simp]
theorem equivOfCofinalSMul_toLinearMap (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule
      R M) ≤ I • ⊤) :
    (equivOfCofinalSMul I J M hIJ hJI).toLinearMap = mapOfPowSMulLE I J M hIJ := rfl

@[simp]
theorem equivOfCofinalSMul_apply (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule
      R M) ≤ I • ⊤)
    (x : AdicCompletion I M) :
    equivOfCofinalSMul I J M hIJ hJI x = mapOfPowSMulLE I J M hIJ x := rfl

theorem equivOfCofinalSMul_of (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule
      R M) ≤ I • ⊤) (x : M) :
    equivOfCofinalSMul I J M hIJ hJI (of I M x) = of J M x := by
  exact mapOfPowSMulLE_of I J M hIJ x

@[simp]
theorem equivOfCofinalSMul_symm (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule
      R M) ≤ I • ⊤) :
    (equivOfCofinalSMul I J M hIJ hJI).symm = equivOfCofinalSMul J I M hJI hIJ := by
  ext x
  rfl

@[simp]
theorem equivOfCofinalSMul_symm_toLinearMap (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule
      R M) ≤ I • ⊤) :
    (equivOfCofinalSMul I J M hIJ hJI).symm.toLinearMap = mapOfPowSMulLE J I M hJI := rfl

@[simp]
theorem equivOfCofinalSMul_symm_apply (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule
      R M) ≤ I • ⊤)
    (x : AdicCompletion J M) :
    (equivOfCofinalSMul I J M hIJ hJI).symm x = mapOfPowSMulLE J I M hJI x := rfl

theorem equivOfCofinalSMul_symm_of (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule
      R M) ≤ I • ⊤) (x : M) :
    (equivOfCofinalSMul I J M hIJ hJI).symm (of J M x) = of I M x := by
  rw [equivOfCofinalSMul_symm]
  exact equivOfCofinalSMul_of J I M hJI hIJ x

@[simp]
theorem equivOfCofinalSMul_refl (I : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hII hII' : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ I • ⊤) :
    equivOfCofinalSMul I I M hII hII' = LinearEquiv.refl R (AdicCompletion I M) := by
  apply LinearEquiv.ext
  intro x
  change mapOfPowSMulLE I I M hII x = x
  rw [mapOfPowSMulLE_self I M hII]
  rfl

/-- Replacing either uniform power bound does not change the cofinal equivalence. -/
theorem equivOfCofinalSMul_congr (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ hIJ' : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hJI hJI' : ∃ a : ℕ, (J ^ a • ⊤ : Submodule R M) ≤ I • ⊤) :
    equivOfCofinalSMul I J M hIJ hJI = equivOfCofinalSMul I J M hIJ' hJI' := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (mapOfPowSMulLE_congr I J M hIJ hIJ') x

/-- Every admissible stage computes the cofinal equivalence. -/
theorem eval_equivOfCofinalSMul (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule R M) ≤ I • ⊤)
    {m n : ℕ} (h : (I ^ m • ⊤ : Submodule R M) ≤ J ^ n • ⊤)
    (x : AdicCompletion I M) :
    eval J M n (equivOfCofinalSMul I J M hIJ hJI x) = factor h (eval I M m x) :=
  eval_mapOfPowSMulLE I J M hIJ h x

/-- Every admissible stage also computes the inverse cofinal equivalence. -/
theorem eval_equivOfCofinalSMul_symm (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hJI : ∃ b : ℕ, (J ^ b • ⊤ : Submodule R M) ≤ I • ⊤)
    {m n : ℕ} (h : (J ^ m • ⊤ : Submodule R M) ≤ I ^ n • ⊤)
    (x : AdicCompletion J M) :
    eval I M n ((equivOfCofinalSMul I J M hIJ hJI).symm x) =
      factor h (eval J M m x) :=
  eval_mapOfPowSMulLE J I M hJI h x

/-- Cofinal equivalences compose for any valid direct bounds. -/
theorem equivOfCofinalSMul_trans (I J K : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hJI : ∃ a : ℕ, (J ^ a • ⊤ : Submodule R M) ≤ I • ⊤)
    (hJK : ∃ a : ℕ, (J ^ a • ⊤ : Submodule R M) ≤ K • ⊤)
    (hKJ : ∃ a : ℕ, (K ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hIK : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ K • ⊤)
    (hKI : ∃ a : ℕ, (K ^ a • ⊤ : Submodule R M) ≤ I • ⊤) :
    (equivOfCofinalSMul I J M hIJ hJI).trans (equivOfCofinalSMul J K M hJK hKJ) =
      equivOfCofinalSMul I K M hIK hKI := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (mapOfPowSMulLE_comp I J K M hIJ hJK hIK) x

section ModuleNaturality

variable (I J : Ideal R)
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/-- Comparison is natural for maps of the original modules, given separate
uniform power bounds on the source and target modules. -/
theorem mapOfPowSMulLE_map
    (hM : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hN : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R N) ≤ J • ⊤)
    (f : M →ₗ[R] N) (x : AdicCompletion I M) :
    mapOfPowSMulLE I J N hN (map I f x) = map J f (mapOfPowSMulLE I J M hM x) := by
  apply AdicCompletion.ext
  intro n
  let m := max (hM.choose * n) (hN.choose * n)
  have hMm : (I ^ m • ⊤ : Submodule R M) ≤ J ^ n • ⊤ :=
    (pow_smul_top_le I M (le_max_left _ _)).trans
      (pow_mul_smul_top_le I J M hM.choose_spec n)
  have hNm : (I ^ m • ⊤ : Submodule R N) ≤ J ^ n • ⊤ :=
    (pow_smul_top_le I N (le_max_right _ _)).trans
      (pow_mul_smul_top_le I J N hN.choose_spec n)
  change eval J N n (mapOfPowSMulLE I J N hN (map I f x)) =
    f.reduceModIdeal (J ^ n) (eval J M n (mapOfPowSMulLE I J M hM x))
  rw [eval_mapOfPowSMulLE I J N hN hNm, eval_mapOfPowSMulLE I J M hM hMm]
  change factor hNm (f.reduceModIdeal (I ^ m) (eval I M m x)) =
    f.reduceModIdeal (J ^ n) (factor hMm (eval I M m x))
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective
    (I ^ m • ⊤ : Submodule R M) (eval I M m x)
  rw [← hy]
  rfl

/-- Cofinal equivalences are natural, with both bounds supplied separately on
both original modules. No completed coefficient action is transported. -/
theorem equivOfCofinalSMul_map
    (hM : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hM' : ∃ a : ℕ, (J ^ a • ⊤ : Submodule R M) ≤ I • ⊤)
    (hN : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R N) ≤ J • ⊤)
    (hN' : ∃ a : ℕ, (J ^ a • ⊤ : Submodule R N) ≤ I • ⊤)
    (f : M →ₗ[R] N) (x : AdicCompletion I M) :
    equivOfCofinalSMul I J N hN hN' (map I f x) =
      map J f (equivOfCofinalSMul I J M hM hM' x) :=
  mapOfPowSMulLE_map I J hM hN f x

end ModuleNaturality

/-- Adjoining an ideal that annihilates the original module does not change its
completion: the canonical comparison to the enlarged ideal is bijective.
This requires no ambient power containment in the reverse direction. -/
theorem mapOfPowSMulLE_sup_bijective (I A : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (hA : (A • ⊤ : Submodule R M) = ⊥)
    (h : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ (I ⊔ A) • ⊤) :
    Function.Bijective (mapOfPowSMulLE I (I ⊔ A) M h) := by
  have hrev : ∃ a : ℕ, ((I ⊔ A) ^ a • ⊤ : Submodule R M) ≤ I • ⊤ := by
    refine ⟨1, ?_⟩
    simpa only [pow_one, sup_smul, hA, sup_bot_eq] using
      (le_rfl : (I • ⊤ : Submodule R M) ≤ I • ⊤)
  exact (equivOfCofinalSMul I (I ⊔ A) M h hrev).bijective

/-- A power containment induces a map of adic completions, linear over the
original ring. The power witness is allowed to be zero. -/
noncomputable def mapOfPowLE (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (hIJ : ∃ a : ℕ, I ^ a ≤ J) :
    AdicCompletion I M →ₗ[R] AdicCompletion J M :=
  mapOfPowSMulLE I J M (hIJ.imp fun _ ha ↦ smul_mono_left ha)

/-- At any pair of quotient levels related by a power containment, the map
between completions is the canonical quotient factor map. -/
theorem eval_mapOfPowLE (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (hIJ : ∃ a : ℕ, I ^ a ≤ J)
    {m n : ℕ} (h : I ^ m ≤ J ^ n) (x : AdicCompletion I M) :
    eval J M n (mapOfPowLE I J M hIJ x) =
      factor (smul_mono_left h) (eval I M m x) := by
  exact eval_mapOfPowSMulLE I J M _ (smul_mono_left h) x

/-- Changing the ideal commutes with the canonical map from the original module. -/
@[simp]
theorem mapOfPowLE_of (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (hIJ : ∃ a : ℕ, I ^ a ≤ J) (x : M) :
    mapOfPowLE I J M hIJ (of I M x) = of J M x := by
  apply AdicCompletion.ext
  intro n
  have h : I ^ (hIJ.choose * n) ≤ J ^ n := by
    simpa only [← pow_mul] using Ideal.pow_right_mono hIJ.choose_spec n
  change eval J M n (mapOfPowLE I J M hIJ (of I M x)) = eval J M n (of J M x)
  rw [eval_mapOfPowLE I J M hIJ h]
  rfl

/-- Every power witness for an ideal's containment in itself gives the identity. -/
@[simp]
theorem mapOfPowLE_self (I : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (hII : ∃ a : ℕ, I ^ a ≤ I) :
    mapOfPowLE I I M hII = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change eval I M n (mapOfPowLE I I M hII x) = eval I M n x
  rw [eval_mapOfPowLE I I M hII (le_refl (I ^ n)) x]
  exact Quotient.inductionOn' (eval I M n x) (fun _ ↦ rfl)

/-- Maps induced by power containments compose, for any witness of the direct
containment. In particular, the resulting map does not depend on its witnesses. -/
theorem mapOfPowLE_comp (I J K : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJK : ∃ b : ℕ, J ^ b ≤ K)
    (hIK : ∃ c : ℕ, I ^ c ≤ K) :
    (mapOfPowLE J K M hJK).comp (mapOfPowLE I J M hIJ) =
      mapOfPowLE I K M hIK := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  have hJK_n : J ^ (hJK.choose * n) ≤ K ^ n := by
    simpa only [← pow_mul] using Ideal.pow_right_mono hJK.choose_spec n
  have hIJ_bn : I ^ (hIJ.choose * (hJK.choose * n)) ≤ J ^ (hJK.choose * n) := by
    simpa only [← pow_mul] using
      Ideal.pow_right_mono hIJ.choose_spec (hJK.choose * n)
  change eval K M n (mapOfPowLE J K M hJK (mapOfPowLE I J M hIJ x)) =
    eval K M n (mapOfPowLE I K M hIK x)
  rw [eval_mapOfPowLE J K M hJK hJK_n,
    eval_mapOfPowLE I J M hIJ hIJ_bn,
    eval_mapOfPowLE I K M hIK (hIJ_bn.trans hJK_n)]
  rw [factor_comp_apply]

/-- Mutual power containment identifies the two adic completions as modules over
  the original ring. -/
def equivOfCofinal (I J : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ b : ℕ, J ^ b ≤ I) :
    AdicCompletion I M ≃ₗ[R] AdicCompletion J M :=
  equivOfCofinalSMul I J M (hIJ.imp fun _ ha ↦ smul_mono_left ha)
    (hJI.imp fun _ hb ↦ smul_mono_left hb)

@[simp]
theorem equivOfCofinal_toLinearMap (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ b : ℕ, J ^ b ≤ I) :
    (equivOfCofinal I J M hIJ hJI).toLinearMap = mapOfPowLE I J M hIJ := rfl

@[simp]
theorem equivOfCofinal_apply (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ b : ℕ, J ^ b ≤ I)
    (x : AdicCompletion I M) :
    equivOfCofinal I J M hIJ hJI x = mapOfPowLE I J M hIJ x := rfl

theorem equivOfCofinal_of (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ b : ℕ, J ^ b ≤ I) (x : M) :
    equivOfCofinal I J M hIJ hJI (of I M x) = of J M x := by
  exact mapOfPowLE_of I J M hIJ x

@[simp]
theorem equivOfCofinal_symm (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ b : ℕ, J ^ b ≤ I) :
    (equivOfCofinal I J M hIJ hJI).symm = equivOfCofinal J I M hJI hIJ := by
  ext x
  rfl

@[simp]
theorem equivOfCofinal_symm_toLinearMap (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ b : ℕ, J ^ b ≤ I) :
    (equivOfCofinal I J M hIJ hJI).symm.toLinearMap = mapOfPowLE J I M hJI := rfl

@[simp]
theorem equivOfCofinal_symm_apply (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ b : ℕ, J ^ b ≤ I)
    (x : AdicCompletion J M) :
    (equivOfCofinal I J M hIJ hJI).symm x = mapOfPowLE J I M hJI x := rfl

theorem equivOfCofinal_symm_of (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ b : ℕ, J ^ b ≤ I) (x : M) :
    (equivOfCofinal I J M hIJ hJI).symm (of J M x) = of I M x := by
  rw [equivOfCofinal_symm]
  exact equivOfCofinal_of J I M hJI hIJ x

@[simp]
theorem equivOfCofinal_refl (I : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hII hII' : ∃ a : ℕ, I ^ a ≤ I) :
    equivOfCofinal I I M hII hII' = LinearEquiv.refl R (AdicCompletion I M) := by
  apply LinearEquiv.ext
  intro x
  change mapOfPowLE I I M hII x = x
  rw [mapOfPowLE_self I M hII]
  rfl

section Naturality

variable (I J : Ideal R)
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/-- Changing the ideal commutes pointwise with the original map on completions. -/
theorem mapOfPowLE_map (hIJ : ∃ a : ℕ, I ^ a ≤ J) (f : M →ₗ[R] N)
    (x : AdicCompletion I M) :
    mapOfPowLE I J N hIJ (map I f x) = map J f (mapOfPowLE I J M hIJ x) := by
  exact mapOfPowSMulLE_map I J _ _ f x

/-- The cofinal comparison is natural for maps of the original modules.
The assertion is pointwise: the two stock maps have different completed scalar rings. -/
theorem equivOfCofinal_map (hIJ : ∃ a : ℕ, I ^ a ≤ J)
    (hJI : ∃ b : ℕ, J ^ b ≤ I) (f : M →ₗ[R] N) (x : AdicCompletion I M) :
    equivOfCofinal I J N hIJ hJI (map I f x) =
      map J f (equivOfCofinal I J M hIJ hJI x) := by
  change mapOfPowLE I J N hIJ (map I f x) = map J f (mapOfPowLE I J M hIJ x)
  exact mapOfPowLE_map I J hIJ f x

end Naturality

/-- Under an ambient power bound, module comparison agrees on every completed
input with the ambient comparison, independently of the two chosen bounds. -/
theorem mapOfPowSMulLE_eq_mapOfPowLE (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hM : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) :
    mapOfPowSMulLE I J M hM = mapOfPowLE I J M hIJ := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  have h : I ^ (hIJ.choose * n) ≤ J ^ n := by
    simpa only [← pow_mul] using Ideal.pow_right_mono hIJ.choose_spec n
  change eval J M n (mapOfPowSMulLE I J M hM x) = eval J M n (mapOfPowLE I J M hIJ x)
  rw [eval_mapOfPowSMulLE I J M hM (smul_mono_left h), eval_mapOfPowLE I J M hIJ h]

/-- Pointwise ambient specialization on arbitrary completed inputs. -/
theorem mapOfPowSMulLE_eq_mapOfPowLE_apply (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hM : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (x : AdicCompletion I M) :
    mapOfPowSMulLE I J M hM x = mapOfPowLE I J M hIJ x :=
  LinearMap.congr_fun (mapOfPowSMulLE_eq_mapOfPowLE I J M hM hIJ) x

/-- Mutual module comparison specializes to the ambient cofinal equivalence. -/
theorem equivOfCofinalSMul_eq_equivOfCofinal (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hM : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hM' : ∃ a : ℕ, (J ^ a • ⊤ : Submodule R M) ≤ I • ⊤)
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ a : ℕ, J ^ a ≤ I) :
    equivOfCofinalSMul I J M hM hM' = equivOfCofinal I J M hIJ hJI := by
  apply LinearEquiv.ext
  intro x
  exact mapOfPowSMulLE_eq_mapOfPowLE_apply I J M hM hIJ x

/-- Pointwise specialization of the cofinal equivalence. -/
theorem equivOfCofinalSMul_eq_equivOfCofinal_apply (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M]
    (hM : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (hM' : ∃ a : ℕ, (J ^ a • ⊤ : Submodule R M) ≤ I • ⊤)
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ a : ℕ, J ^ a ≤ I)
    (x : AdicCompletion I M) :
    equivOfCofinalSMul I J M hM hM' x = equivOfCofinal I J M hIJ hJI x :=
  congrArg (fun e : AdicCompletion I M ≃ₗ[R] AdicCompletion J M ↦ e x)
    (equivOfCofinalSMul_eq_equivOfCofinal I J M hM hM' hIJ hJI)

section Inclusion

variable (M : Type uM) [AddCommGroup M] [Module R M]
variable {I J K : Ideal R}

/-- An inclusion of ideals induces the canonical map on adic inverse limits. -/
noncomputable def mapOfLE (hIJ : I ≤ J) : AdicCompletion I M →ₗ[R] AdicCompletion J M :=
  mapOfPowLE I J M ⟨1, by simpa only [pow_one] using hIJ⟩

/-- Evaluation of the inclusion-induced map is the quotient factor. -/
@[simp]
theorem mapOfLE_eval (hIJ : I ≤ J) (n : ℕ) (x : AdicCompletion I M) :
    eval J M n (mapOfLE M hIJ x) =
      Submodule.factor (Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n))
        (eval I M n x) := by
  exact eval_mapOfPowLE I J M ⟨1, by simpa only [pow_one] using hIJ⟩
    (Ideal.pow_right_mono hIJ n) x

/-- The inclusion-induced map preserves elements coming from the module. -/
@[simp]
theorem mapOfLE_of (hIJ : I ≤ J) (m : M) :
    mapOfLE M hIJ (of I M m) = of J M m := by
  exact mapOfPowLE_of I J M ⟨1, by simpa only [pow_one] using hIJ⟩ m

/-- Changing an ideal to itself gives the identity. -/
@[simp]
theorem mapOfLE_id (I : Ideal R) :
    mapOfLE M (le_refl I) = LinearMap.id := by
  exact mapOfPowLE_self I M ⟨1, le_of_eq (pow_one I)⟩

/-- Inclusion-induced maps compose in the same order as the ideal inclusions. -/
theorem mapOfLE_comp (hIJ : I ≤ J) (hJK : J ≤ K) :
    (mapOfLE M hJK).comp (mapOfLE M hIJ) = mapOfLE M (hIJ.trans hJK) := by
  exact mapOfPowLE_comp I J K M
    ⟨1, by simpa only [pow_one] using hIJ⟩
    ⟨1, by simpa only [pow_one] using hJK⟩
    ⟨1, by simpa only [pow_one] using hIJ.trans hJK⟩

/-- Changing the ideal commutes with the stock map induced by a module map. -/
theorem mapOfLE_natural {N : Type uN} [AddCommGroup N] [Module R N]
    (hIJ : I ≤ J) (f : M →ₗ[R] N) (x : AdicCompletion I M) :
    mapOfLE N hIJ (AdicCompletion.map I f x) =
      AdicCompletion.map J f (mapOfLE M hIJ x) := by
  exact mapOfPowLE_map I J ⟨1, by simpa only [pow_one] using hIJ⟩ f x

/-- Under an ideal inclusion, every power witness gives its inclusion-induced map.
The equality holds on arbitrary completed inputs, not just canonical images. -/
theorem mapOfPowLE_eq_mapOfLE (hIJ : I ≤ J) (hPow : ∃ a : ℕ, I ^ a ≤ J) :
    mapOfPowLE I J M hPow = mapOfLE M hIJ := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change eval J M n (mapOfPowLE I J M hPow x) =
    eval J M n (mapOfLE M hIJ x)
  rw [eval_mapOfPowLE I J M hPow (Ideal.pow_right_mono hIJ n), mapOfLE_eval]

/-- Module comparison agrees with inclusion comparison on arbitrary completed
inputs whenever the ideals are included. -/
theorem mapOfPowSMulLE_eq_mapOfLE (hIJ : I ≤ J)
    (hM : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤) :
    mapOfPowSMulLE I J M hM = mapOfLE M hIJ := by
  rw [mapOfPowSMulLE_eq_mapOfPowLE I J M hM
    ⟨1, by simpa only [pow_one] using hIJ⟩]
  exact mapOfPowLE_eq_mapOfLE M hIJ _

/-- Pointwise agreement with inclusion comparison. -/
theorem mapOfPowSMulLE_eq_mapOfLE_apply (hIJ : I ≤ J)
    (hM : ∃ a : ℕ, (I ^ a • ⊤ : Submodule R M) ≤ J • ⊤)
    (x : AdicCompletion I M) :
    mapOfPowSMulLE I J M hM x = mapOfLE M hIJ x :=
  LinearMap.congr_fun (mapOfPowSMulLE_eq_mapOfLE M hIJ hM) x

end Inclusion

/-- Completion at a positive power of an ideal is canonically equivalent, over the
original ring, to completion at the ideal. -/
def powEquiv (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M]
    (k : ℕ) (hk : 0 < k) : AdicCompletion I M ≃ₗ[R] AdicCompletion (I ^ k) M :=
  equivOfCofinal I (I ^ k) M ⟨k, le_rfl⟩
    ⟨1, by simpa only [pow_one] using (Ideal.pow_le_self (I := I) (Nat.ne_of_gt hk))⟩

section PositivePower

variable (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M]
variable (k : ℕ) (hk : 0 < k)

@[simp]
theorem powEquiv_toLinearMap :
    (powEquiv I M k hk).toLinearMap = mapOfPowLE I (I ^ k) M ⟨k, le_rfl⟩ :=
  rfl

@[simp]
theorem powEquiv_apply (x : AdicCompletion I M) :
    powEquiv I M k hk x = mapOfPowLE I (I ^ k) M ⟨k, le_rfl⟩ x :=
  rfl

@[simp]
theorem powEquiv_symm_toLinearMap :
    (powEquiv I M k hk).symm.toLinearMap = mapOfPowLE (I ^ k) I M
      ⟨1, by simpa only [pow_one] using (Ideal.pow_le_self (I := I) (Nat.ne_of_gt hk))⟩ :=
  rfl

@[simp]
theorem powEquiv_symm_apply (x : AdicCompletion (I ^ k) M) :
    (powEquiv I M k hk).symm x = mapOfPowLE (I ^ k) I M
      ⟨1, by simpa only [pow_one] using (Ideal.pow_le_self (I := I) (Nat.ne_of_gt hk))⟩ x :=
  rfl

theorem powEquiv_of (x : M) : powEquiv I M k hk (of I M x) = of (I ^ k) M x := by
  change mapOfPowLE I (I ^ k) M ⟨k, le_rfl⟩ (of I M x) = of (I ^ k) M x
  exact mapOfPowLE_of I (I ^ k) M ⟨k, le_rfl⟩ x

theorem powEquiv_symm_of (x : M) :
    (powEquiv I M k hk).symm (of (I ^ k) M x) = of I M x := by
  change mapOfPowLE (I ^ k) I M
    ⟨1, by simpa only [pow_one] using (Ideal.pow_le_self (I := I) (Nat.ne_of_gt hk))⟩
      (of (I ^ k) M x) = of I M x
  exact mapOfPowLE_of (I ^ k) I M _ x

/-- Every admissible pair of stages computes the positive-power comparison. -/
theorem eval_powEquiv {m n : ℕ} (h : I ^ m ≤ (I ^ k) ^ n)
    (x : AdicCompletion I M) :
    eval (I ^ k) M n (powEquiv I M k hk x) =
      Submodule.factor (Submodule.smul_mono h le_rfl) (eval I M m x) := by
  exact eval_mapOfPowLE I (I ^ k) M ⟨k, le_rfl⟩ h x

/-- Every admissible pair of stages also computes the inverse comparison. -/
theorem eval_powEquiv_symm {m n : ℕ} (h : (I ^ k) ^ m ≤ I ^ n)
    (x : AdicCompletion (I ^ k) M) :
    eval I M n ((powEquiv I M k hk).symm x) =
      Submodule.factor (Submodule.smul_mono h le_rfl) (eval (I ^ k) M m x) := by
  exact eval_mapOfPowLE (I ^ k) I M
    ⟨1, by simpa only [pow_one] using (Ideal.pow_le_self (I := I) (Nat.ne_of_gt hk))⟩ h x

/-- The inverse comparison at stage `k * n`, with the quotient transport displayed
as the factor map induced by the equality of the two ideal powers. -/
theorem eval_powEquiv_symm_mul (n : ℕ) (x : AdicCompletion (I ^ k) M) :
    eval I M (k * n) ((powEquiv I M k hk).symm x) =
      Submodule.factor (Submodule.smul_mono
        (show (I ^ k) ^ n ≤ I ^ (k * n) from by
          simpa only [pow_mul] using (le_rfl : (I ^ k) ^ n ≤ (I ^ k) ^ n)) le_rfl)
        (eval (I ^ k) M n x) := by
  exact eval_powEquiv_symm I M k hk
    (show (I ^ k) ^ n ≤ I ^ (k * n) from by
      simpa only [pow_mul] using (le_rfl : (I ^ k) ^ n ≤ (I ^ k) ^ n)) x

end PositivePower

/-- Positive-power comparison commutes with maps of the original modules. -/
theorem powEquiv_map (I : Ideal R) (k : ℕ) (hk : 0 < k)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (x : AdicCompletion I M) :
    powEquiv I N k hk (map I f x) = map (I ^ k) f (powEquiv I M k hk x) := by
  exact equivOfCofinal_map I (I ^ k) ⟨k, le_rfl⟩
    ⟨1, by simpa only [pow_one] using (Ideal.pow_le_self (I := I) (Nat.ne_of_gt hk))⟩ f x

/-- Evaluation of an element transported along an equality of ideals explicitly
transports its value in the stage quotient. -/
theorem eval_ideal_eq (I J : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M]
    (h : I = J) (n : ℕ) (x : AdicCompletion I M) :
    eval J M n (h ▸ x) =
      cast (congrArg (fun L : Ideal R => M ⧸ (L ^ n • ⊤ : Submodule R M)) h)
        (eval I M n x) := by
  subst J
  rfl

/-- After explicit ideal-equality transport, the positive-power equivalence agrees
with the cofinal comparison for any valid cofinality witnesses. -/
theorem powEquiv_eq_equivOfCofinal (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (k : ℕ) (hk : 0 < k) (hpow : I ^ k = J)
    (hIJ : ∃ a : ℕ, I ^ a ≤ J) (hJI : ∃ b : ℕ, J ^ b ≤ I) :
    (hpow ▸ powEquiv I M k hk) = equivOfCofinal I J M hIJ hJI := by
  subst J
  rfl

end AdicCompletion
