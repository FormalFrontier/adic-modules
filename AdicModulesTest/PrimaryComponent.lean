/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

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
