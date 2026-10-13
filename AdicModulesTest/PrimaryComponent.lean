/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules
public import Mathlib.Data.ZMod.Basic

/-!
# Integer-ideal and subgroup primary components

The ordinary `p`-primary subgroup of an abelian group is the primary component for the integer
ideal `(p)`. The restricted-map formula identifies the two realizations on underlying elements,
using the canonical integer-linear map attached to an additive homomorphism. The kernel
criterion combines that formula with the underlying-element API of the subgroup restriction.
The exactness applications retain torsion only on the source, not on the middle or target group.

For the canonical reduction `ℤ/4ℤ → ℤ/2ℤ`, the class of two is a nonzero `2`-primary
element killed by the integer-ideal restricted map, whereas the class of one has nonzero image.
This gives a nontrivial kernel and a nonzero image for the same reduction homomorphism.

The proofs use the primary-component APIs of AdicModules and Mathlib, with Mathlib's canonical
integer action and `ZMod.castHom` reduction.

## References

* Mathlib's `ZMod` development by Chris Hughes, integer-module development by Nathaniel Thomas
  and collaborators, group-torsion development by Julian Berman, and module-torsion development
  by Pierre-Alexandre Bazin and collaborators supply the formalization interfaces used here.
-/

set_option warningAsError true

open Function IsDedekindDomain

private theorem idealExactClient {R M N Q : Type*} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R Q] (hM : Module.IsTorsion R M)
    (prime : HeightOneSpectrum R) (f : M →ₗ[R] N) (g : N →ₗ[R] Q)
    (hfg : Function.Exact f g) :
    Function.Exact (Ideal.primaryComponent.map prime.asIdeal f)
      (Ideal.primaryComponent.map prime.asIdeal g) :=
  Ideal.primaryComponent.exact hM prime f g hfg

private theorem subgroupMemberClient {G : Type*} [AddCommGroup G]
    (p : ℕ) [Fact p.Prime] (x : G) :
    x ∈ Ideal.primaryComponent G (AddCommGroup.integerPrime p).asIdeal ↔
      x ∈ AddCommGroup.primaryComponent G p :=
  AddCommGroup.mem_integerPrime_iff p x

private theorem restrictedMapClient {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) [Fact p.Prime] (f : G →+ H)
    (x : AddCommGroup.primaryComponent G p) :
    ((Ideal.primaryComponent.map (AddCommGroup.integerPrime p).asIdeal f.toIntLinearMap)
      (⟨x, (AddCommGroup.mem_integerPrime_iff p (x : G)).2 x.property⟩ :
        Ideal.primaryComponent G (AddCommGroup.integerPrime p).asIdeal) : H) =
      (AddCommGroup.primaryComponent.map p f x : H) :=
  AddCommGroup.integerPrime_map_agrees p f x

private theorem ordinaryExactClient {G H K : Type*}
    [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
    (hG : IsAddTorsion G) (p : ℕ) [Fact p.Prime]
    (f : G →+ H) (g : H →+ K) (hfg : Function.Exact f g) :
    Function.Exact (AddCommGroup.primaryComponent.map p f)
      (AddCommGroup.primaryComponent.map p g) :=
  AddCommGroup.primaryComponent.exact hG p f g hfg

/-- Reduction from `ℤ/4ℤ` to `ℤ/2ℤ` kills the nonzero `2`-primary class of two,
also when restricted to the primary components for the integer ideal `(2)`, but has nonzero
image at one. The prime proof and the reduction homomorphism are canonical values. -/
public theorem ZMod.integerPrimary_reduction_four_to_two :
    let hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let f : ZMod 4 →+ ZMod 2 :=
      (ZMod.castHom (show 2 ∣ 4 from ⟨2, rfl⟩) (ZMod 2)).toAddMonoidHom
    ∃ x : AddCommGroup.primaryComponent (ZMod 4) 2,
      (x : ZMod 4) = 2 ∧ x ≠ 0 ∧
      Ideal.primaryComponent.map (@AddCommGroup.integerPrime 2 hp).asIdeal f.toIntLinearMap
          (⟨x, (@AddCommGroup.mem_integerPrime_iff (ZMod 4) _ 2 hp (x : ZMod 4)).2
            x.property⟩ : Ideal.primaryComponent (ZMod 4)
              (@AddCommGroup.integerPrime 2 hp).asIdeal) = 0 ∧
      f 1 ≠ 0 := by
  dsimp only
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ZMod 4 →+ ZMod 2 :=
    (ZMod.castHom (show 2 ∣ 4 from ⟨2, rfl⟩) (ZMod 2)).toAddMonoidHom
  have hTwo : (2 : ZMod 4) ∈ AddCommGroup.primaryComponent (ZMod 4) 2 := by
    apply AddCommGroup.mem_primaryComponent.mpr
    refine ⟨1, ?_⟩
    change (2 : ℕ) • (2 : ZMod 4) = 0
    rw [nsmul_eq_mul]
    decide
  let x : AddCommGroup.primaryComponent (ZMod 4) 2 := ⟨2, hTwo⟩
  have hx : x ≠ 0 := by
    intro h
    have hTwoZero := congrArg
      (fun y : AddCommGroup.primaryComponent (ZMod 4) 2 ↦ (y : ZMod 4)) h
    exact (show (2 : ZMod 4) ≠ 0 from by decide) hTwoZero
  refine ⟨x, rfl, hx, ?_, ?_⟩
  · apply (AddCommGroup.integerPrime_map_eq_zero_iff 2 f x).2
    change ZMod.castHom (show 2 ∣ 4 from ⟨2, rfl⟩) (ZMod 2) (2 : ZMod 4) = 0
    simpa only [map_ofNat] using (show (2 : ZMod 2) = 0 from by decide)
  · change ZMod.castHom (show 2 ∣ 4 from ⟨2, rfl⟩) (ZMod 2) 1 ≠ 0
    rw [map_one]
    exact one_ne_zero
