/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.Completeness
public import AdicModules.LinearAlgebra.Quotient.Hausdorff
public import AdicModules.Topology.Algebra.Module.AdicTopology
public import AdicModules.Topology.Algebra.Submodule
public import CoherentModules.RingTheory.Ideal.AdicKrull

import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Separation criteria for finite modules

For an ideal satisfying finite-submodule adic cofinality, containment in the
Jacobson radical is equivalent to adic Hausdorffness of every finite module,
and to closedness of every submodule of every finite module in the ambient
power topology.
The universal condition uses modules in the ring's universe. A finite module in
any independent universe has a representative there, with an equivalence for
its original scalar action, by `Module.Finite.reprEquiv`.

The converse tests the cyclic quotients by the principal ideals `(1 - a)`.
Neither finite generation of the ideal nor finite presentation of the modules
is required. All module structures are the given structures or the ordinary
quotient structures.

## References

* Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*,
  arXiv:1308.4734v5, Proposition 0.7.4.16, for the equivalence of the Zariskian
  condition and separation of every finite module.
* Coherent Modules' finite-submodule adic cofinality and Krull intersection
  API, generalizing Andrew Yang's Mathlib Krull intersection formalization.
* Mathlib's Jacobson-radical, unit-action and quotient-module APIs.
-/

@[expose] public section

universe uR

namespace Ideal.HasFiniteSubmoduleAdicCofinality

/-- For an ideal satisfying finite-submodule adic cofinality, containment in the
Jacobson radical is equivalent to adic Hausdorffness of every finite module in
the ring's universe. Finite modules in independent universes can be transported
through `Module.Finite.reprEquiv` and `IsHausdorff.of_injective`.

This is the separation equivalence in Fujiwara--Kato, *Foundations of Rigid
Geometry I*, arXiv:1308.4734v5, Proposition 0.7.4.16. The proof uses the
finite-submodule cofinality Krull criterion and Mathlib's Jacobson unit criterion;
the converse tests the original-action cyclic quotients by `(1 - a)`. -/
theorem le_jacobson_bot_iff_forall_isHausdorff
    {R : Type uR} [CommRing R] {I : Ideal R}
    (hAPf : I.HasFiniteSubmoduleAdicCofinality) :
    (I ≤ (⊥ : Ideal R).jacobson) ↔
      ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X],
        IsHausdorff I X := by
  constructor
  · intro hJ X _ _ _
    refine isHausdorff_iff.mpr ?_
    intro x hx
    have hx' : x ∈ ⨅ n : ℕ, (I ^ n) • (⊤ : Submodule R X) :=
      (Submodule.mem_iInf _).mpr fun n => SModEq.zero.mp (hx n)
    obtain ⟨a, ha, hax⟩ :=
      (hAPf.mem_iInf_pow_smul_top_iff (I := I) x).mp hx'
    have hu : IsUnit (1 - a) :=
      Ideal.isUnit_of_sub_one_mem_jacobson_bot (1 - a) (by simpa using hJ ha)
    apply hu.smul_eq_zero.mp
    rw [sub_smul, one_smul, hax, sub_self]
  · intro hsep
    -- Test a finite cyclic quotient rather than only the regular module.
    have hunit (a : R) (ha : a ∈ I) : IsUnit (1 - a) := by
      let J : Ideal R := Ideal.span ({1 - a} : Set R)
      let q : R ⧸ J := J.mkQ 1
      have hfix : a • q = q := by
        change a • (Submodule.Quotient.mk (1 : R) : R ⧸ J) =
          Submodule.Quotient.mk (1 : R)
        rw [← Submodule.Quotient.mk_smul]
        apply (Submodule.Quotient.eq J).mpr
        simpa only [smul_eq_mul, mul_one, neg_sub] using
          J.neg_mem (Ideal.mem_span_singleton_self (1 - a))
      have hq : q = 0 := by
        have hqmem :=
          (hAPf.mem_iInf_pow_smul_top_iff (I := I) q).mpr ⟨a, ha, hfix⟩
        rw [IsHausdorff.iInf_pow_smul (I := I) (M := R ⧸ J)
          (hsep (R ⧸ J))] at hqmem
        exact (Submodule.mem_bot R).mp hqmem
      have hone : (1 : R) ∈ J := (Submodule.Quotient.mk_eq_zero J).mp hq
      exact Ideal.span_singleton_eq_top.mp ((Ideal.eq_top_iff_one J).mpr hone)
    intro x hx
    apply Ideal.mem_jacobson_bot.mpr
    intro y
    simpa only [sub_neg_eq_add, add_comm] using
      hunit (-(x * y)) (I.neg_mem (I.mul_mem_right y hx))

/-- For an ideal with finite-submodule adic cofinality, containment in the
Jacobson radical is equivalent to closedness of every submodule of every finite
module in its adic topology. This is the closedness equivalence of
Fujiwara--Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
Proposition 0.7.4.16. The universal condition uses the ring's universe and the
canonical power topology, with no finite-generation assumption on the submodule. -/
theorem le_jacobson_bot_iff_forall_isClosed_adicModuleTopology
    {R : Type uR} [CommRing R] {I : Ideal R}
    (hAPf : I.HasFiniteSubmoduleAdicCofinality) :
    (I ≤ (⊥ : Ideal R).jacobson) ↔
      ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
        (N : Submodule R X),
        @IsClosed X (I.adicModuleTopology X) (N : Set X) := by
  constructor
  · intro hJ M _ _ _ N
    have hQ : IsHausdorff I (M ⧸ N) :=
      (Ideal.HasFiniteSubmoduleAdicCofinality.le_jacobson_bot_iff_forall_isHausdorff
        hAPf).mp hJ (M ⧸ N)
    let : TopologicalSpace R := I.adicTopology
    let : TopologicalSpace M := I.adicModuleTopology M
    have hInf : (⨅ n : ℕ, N ⊔ (I ^ n • (⊤ : Submodule R M))) = N :=
      (Submodule.isHausdorff_quotient_iff_iInf_sup I N).mp hQ
    have hclosure : N.topologicalClosure =
        ⨅ n : ℕ, N ⊔ (I ^ n • (⊤ : Submodule R M)) := by
      simpa using N.topologicalClosure_eq_iInf_sup
        (I.hasBasis_nhds_zero_adicModuleTopology M)
    have hfix : N.topologicalClosure = N := hclosure.trans hInf
    exact hfix ▸ N.isClosed_topologicalClosure
  · intro hclosed
    apply
      (Ideal.HasFiniteSubmoduleAdicCofinality.le_jacobson_bot_iff_forall_isHausdorff
        hAPf).mpr
    intro X _ _ _
    let B : Submodule R X := ⊥
    let : TopologicalSpace R := I.adicTopology
    let : TopologicalSpace X := I.adicModuleTopology X
    have hB : IsClosed (B : Set X) := hclosed X B
    have hclosure : B.topologicalClosure =
        ⨅ n : ℕ, B ⊔ (I ^ n • (⊤ : Submodule R X)) := by
      simpa using B.topologicalClosure_eq_iInf_sup
        (I.hasBasis_nhds_zero_adicModuleTopology X)
    have hInf : (⨅ n : ℕ, B ⊔ (I ^ n • (⊤ : Submodule R X))) = B :=
      hclosure.symm.trans hB.submodule_topologicalClosure_eq
    let : IsHausdorff I (X ⧸ B) :=
      (Submodule.isHausdorff_quotient_iff_iInf_sup I B).mpr hInf
    let e : (X ⧸ B) ≃ₗ[R] X := B.quotEquivOfEqBot rfl
    exact IsHausdorff.of_injective I e.symm.toLinearMap e.symm.injective

end Ideal.HasFiniteSubmoduleAdicCofinality
