/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Adic separation of quotients

A quotient by a submodule `N` is `I`-Hausdorff exactly when the intersection of
`N ⊔ I ^ n • ⊤` is `N`. Membership in `N` can therefore be detected by congruence
to elements of `N` modulo every power of `I`; the representative may vary with
the power. Separation of the quotient is preserved on taking inverse images
under arbitrary linear maps.

The proofs use Mathlib's quotient, congruence and ideal-power APIs, in particular
the surjective power-comap formula. No topology or completeness is required.

## References

Mathlib's adic completion formalization by Kenny Lau, Judith Ludwig, Christian
Merten and Jiedong Jiang, and its quotient formalization by Johannes Hölzl,
Mario Carneiro, Kevin Buzzard and Yury Kudryashov.
-/

@[expose] public section

universe u v w

variable {R : Type u} {M : Type v}
  [CommRing R] [AddCommGroup M] [Module R M]

/-- A quotient is adically separated exactly when the intersection of the
submodule plus each ideal-power submodule equals the submodule. -/
theorem Submodule.isHausdorff_quotient_iff_iInf_sup
    (I : Ideal R) (N : Submodule R M) :
    IsHausdorff I (M ⧸ N) ↔
      (⨅ n : ℕ, N ⊔ (I ^ n • (⊤ : Submodule R M))) = N := by
  have hcomap (n : ℕ) :
      Submodule.comap N.mkQ (I ^ n • (⊤ : Submodule R (M ⧸ N))) =
        N ⊔ (I ^ n • (⊤ : Submodule R M)) := by
    rw [Submodule.comap_smul_top_of_surjective (I ^ n) N.mkQ N.mkQ_surjective,
      Submodule.ker_mkQ, sup_comm]
  constructor
  · intro h
    have hh := congrArg (Submodule.comap N.mkQ) h.iInf_pow_smul
    simpa only [Submodule.comap_iInf, hcomap, Submodule.comap_bot,
      Submodule.ker_mkQ] using hh
  · intro h
    refine isHausdorff_iff.mpr ?_
    intro x hx
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    rw [← h, Submodule.mem_iInf]
    intro n
    rw [← hcomap n]
    change N.mkQ y ∈ I ^ n • (⊤ : Submodule R (M ⧸ N))
    exact SModEq.zero.mp (hx n)

/-- In a submodule with adically separated quotient, membership is equivalent
to having a congruent element of the submodule at every ideal power.
The chosen element may depend on the power. -/
theorem Submodule.mem_iff_forall_exists_smodEq_of_isHausdorff_quotient
    (I : Ideal R) (N : Submodule R M)
    [IsHausdorff I (M ⧸ N)] (x : M) :
    x ∈ N ↔ ∀ n : ℕ, ∃ y : M,
      y ∈ N ∧ x ≡ y [SMOD (I ^ n • (⊤ : Submodule R M))] := by
  constructor
  · intro hx n
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← (Submodule.isHausdorff_quotient_iff_iInf_sup I N).mp inferInstance,
      Submodule.mem_iInf]
    intro n
    obtain ⟨y, hy, hxy⟩ := hx n
    exact Submodule.mem_sup.mpr ⟨y, hy, x - y, SModEq.sub_mem.mp hxy,
      by rw [add_comm, sub_add_cancel]⟩

/-- A submodule with adically separated quotient has an adically separated
inverse-image quotient under any linear map. -/
theorem IsHausdorff.quotient_comap
    {P : Type w} [AddCommGroup P] [Module R P]
    (I : Ideal R) (N : Submodule R M) (F : P →ₗ[R] M)
    [IsHausdorff I (M ⧸ N)] :
    IsHausdorff I (P ⧸ N.comap F) := by
  apply (Submodule.isHausdorff_quotient_iff_iInf_sup I (N.comap F)).mpr
  apply le_antisymm
  · intro x hx
    change F x ∈ N
    rw [← (Submodule.isHausdorff_quotient_iff_iInf_sup I N).mp inferInstance,
      Submodule.mem_iInf]
    rw [Submodule.mem_iInf] at hx
    intro n
    have hle : N.comap F ⊔ (I ^ n • (⊤ : Submodule R P)) ≤
        (N ⊔ (I ^ n • (⊤ : Submodule R M))).comap F :=
      sup_le (Submodule.comap_mono le_sup_left)
        ((Submodule.smul_top_le_comap_smul_top (I ^ n) F).trans
          (Submodule.comap_mono le_sup_right))
    exact hle (hx n)
  · exact le_iInf fun _ ↦ le_sup_left
