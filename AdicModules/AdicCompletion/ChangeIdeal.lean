/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Changing the ideal of an adic completion

A power containment between ideals induces an original-ring-linear map between
adic completions. Its value at every admissible quotient level is the canonical
factor map, independently of the power witness used in its construction.
-/

@[expose] public section

noncomputable section

universe uR uM uN

open Submodule

namespace AdicCompletion

variable {R : Type uR} [CommRing R]

private theorem mapOfPowLE_compatible (I J : Ideal R) (M : Type uM)
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

/-- A power containment induces a map of adic completions, linear over the
original ring. The power witness is allowed to be zero. -/
noncomputable def mapOfPowLE (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (hIJ : ∃ a : ℕ, I ^ a ≤ J) :
    AdicCompletion I M →ₗ[R] AdicCompletion J M := by
  let a := hIJ.choose
  have ha : I ^ a ≤ J := hIJ.choose_spec
  let H : ∀ n : ℕ, (I ^ (a * n) • ⊤ : Submodule R M) ≤ J ^ n • ⊤ :=
    fun n ↦ smul_mono_left (by
      simpa only [← pow_mul] using Ideal.pow_right_mono ha n)
  exact lift J (fun n ↦ (factor (H n)).comp (eval I M (a * n)))
    (by exact mapOfPowLE_compatible I J M a H)

/-- At any pair of quotient levels related by a power containment, the map
between completions is the canonical quotient factor map. -/
theorem eval_mapOfPowLE (I J : Ideal R) (M : Type uM)
    [AddCommGroup M] [Module R M] (hIJ : ∃ a : ℕ, I ^ a ≤ J)
    {m n : ℕ} (h : I ^ m ≤ J ^ n) (x : AdicCompletion I M) :
    eval J M n (mapOfPowLE I J M hIJ x) =
      factor (smul_mono_left h) (eval I M m x) := by
  let a := hIJ.choose
  have hchosen : I ^ (a * n) ≤ J ^ n := by
    simpa only [← pow_mul] using Ideal.pow_right_mono hIJ.choose_spec n
  have hstage : eval J M n (mapOfPowLE I J M hIJ x) =
      factor (smul_mono_left hchosen) (eval I M (a * n) x) := by
    let H : ∀ k : ℕ, (I ^ (a * k) • ⊤ : Submodule R M) ≤ J ^ k • ⊤ :=
      fun k ↦ smul_mono_left (by
        simpa only [← pow_mul] using Ideal.pow_right_mono hIJ.choose_spec k)
    exact LinearMap.congr_fun
      (AdicCompletion.eval_lift J
        (fun k ↦ (factor (H k)).comp (eval I M (a * k)))
        (mapOfPowLE_compatible I J M a H) n) x
  rw [hstage]
  change factor (smul_mono_left hchosen) (x.val (a * n)) =
    factor (smul_mono_left h) (x.val m)
  rcases le_total m (a * n) with hma | ham
  · rw [← transitionMap_comp_eval_apply (I := I) (M := M) hma x]
    change factor (smul_mono_left hchosen) (x.val (a * n)) =
      factor (smul_mono_left h)
        (factor (pow_smul_top_le I M hma) (x.val (a * n)))
    rw [factor_comp_apply]
  · rw [← transitionMap_comp_eval_apply (I := I) (M := M) ham x]
    change factor (smul_mono_left hchosen)
        (factor (pow_smul_top_le I M ham) (x.val m)) =
      factor (smul_mono_left h) (x.val m)
    rw [factor_comp_apply]

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
    AdicCompletion I M ≃ₗ[R] AdicCompletion J M where
  toLinearMap := mapOfPowLE I J M hIJ
  invFun := mapOfPowLE J I M hJI
  left_inv x := by
    have hII : ∃ a : ℕ, I ^ a ≤ I := ⟨1, le_of_eq (pow_one I)⟩
    change ((mapOfPowLE J I M hJI).comp (mapOfPowLE I J M hIJ)) x = x
    rw [mapOfPowLE_comp I J I M hIJ hJI hII, mapOfPowLE_self I M hII]
    rfl
  right_inv x := by
    have hJJ : ∃ a : ℕ, J ^ a ≤ J := ⟨1, le_of_eq (pow_one J)⟩
    change ((mapOfPowLE I J M hIJ).comp (mapOfPowLE J I M hJI)) x = x
    rw [mapOfPowLE_comp J I J M hJI hIJ hJJ, mapOfPowLE_self J M hJJ]
    rfl

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
  let a := hIJ.choose
  have ha : I ^ a ≤ J := hIJ.choose_spec
  apply AdicCompletion.ext
  intro n
  have h : I ^ (a * n) ≤ J ^ n := by
    simpa only [pow_mul] using Ideal.pow_right_mono ha n
  change eval J N n (mapOfPowLE I J N hIJ (map I f x)) =
    f.reduceModIdeal (J ^ n) (eval J M n (mapOfPowLE I J M hIJ x))
  rw [eval_mapOfPowLE I J N hIJ h, eval_mapOfPowLE I J M hIJ h]
  change Submodule.factor _
      (f.reduceModIdeal (I ^ (a * n)) (eval I M (a * n) x)) =
    f.reduceModIdeal (J ^ n) (Submodule.factor _ (eval I M (a * n) x))
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective
    (I ^ (a * n) • ⊤ : Submodule R M) (eval I M (a * n) x)
  rw [← hy]
  rfl

/-- The cofinal comparison is natural for maps of the original modules.
The assertion is pointwise: the two stock maps have different completed scalar rings. -/
theorem equivOfCofinal_map (hIJ : ∃ a : ℕ, I ^ a ≤ J)
    (hJI : ∃ b : ℕ, J ^ b ≤ I) (f : M →ₗ[R] N) (x : AdicCompletion I M) :
    equivOfCofinal I J N hIJ hJI (map I f x) =
      map J f (equivOfCofinal I J M hIJ hJI x) := by
  change mapOfPowLE I J N hIJ (map I f x) = map J f (mapOfPowLE I J M hIJ x)
  exact mapOfPowLE_map I J hIJ f x

end Naturality

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
