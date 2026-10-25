/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.HenselianRadical
public import AdicModules.RingTheory.HenselianTransport
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Suprema of Henselian ideals

The Henselian ideals of a commutative ring are closed under arbitrary suprema.
Their supremum `Ideal.henselianRadical R` is the greatest Henselian ideal of `R`.
It is radical, contains the nilradical and lies in the Jacobson radical. Use
`HenselianRing.henselianRadical` to supply its Henselian structure.

This construction is distinct from ordinary ideal radical and from
`HenselianRing.iff_radical`. The defining inclusion and Jacobson upper bound use only
this supremum and `HenselianRing.jac`; the standard p-adic integer identification can
therefore be established independently of supremum closure.

The arbitrary-supremum proof uses finite support twice in the finite-algebra
idempotent criterion: first for a representative's defect, then separately for the
difference of two lifts. `Ideal.map_sSup` and `Submodule.iSup_induction` provide the
lattice interfaces. Finite joins and recovery use the surjective Henselian-kernel
transport equivalence.

## References

* `AdicModules.RingTheory.HenselianCriterion` formalizes the finite-algebra
  idempotent criterion as `HenselianRing.iff_existsUnique_isIdempotentElem_map`.
  See [Stacks Project, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI) for this
  criterion, not for the new supremum-closure or greatest-ideal statements.
* Mathlib supplies the named lattice interfaces and the stock Henselian
  maximal-ideal inputs for the independent p-adic integer model; see
  [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/).

The supremum-closure and greatest-ideal statements are deductions from these ingredients.
-/

@[expose] public section

universe u v

namespace Ideal

/-- The supremum of all Henselian ideals of a commutative ring. -/
noncomputable def henselianRadical (R : Type u) [CommRing R] : Ideal R :=
  sSup {I : Ideal R | HenselianRing R I}

variable {R : Type u} [CommRing R]

/-- A Henselian ideal belongs to the defining supremum. This bound is independent of
any claim that the supremum itself is Henselian. -/
theorem le_henselianRadical (I : Ideal R) (hI : HenselianRing R I) :
    I ≤ henselianRadical R :=
  le_sSup hI

/-- Every member of the defining supremum lies in the Jacobson radical. This bound is
independent of arbitrary-supremum closure. -/
theorem henselianRadical_le_jacobson (R : Type u) [CommRing R] :
    henselianRadical R ≤ jacobson (⊥ : Ideal R) :=
  sSup_le fun I hI => @HenselianRing.jac R _ I hI

end Ideal

private theorem exists_finset_of_mem_map_sSup
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Set (Ideal R)) {x : S}
    (hx : x ∈ (sSup A).map f) :
    ∃ T : Finset (Ideal R), (↑T : Set (Ideal R)) ⊆ A ∧
      x ∈ (sSup (↑T : Set (Ideal R))).map f := by
  classical
  let P : S → Prop := fun y =>
    ∃ T : Finset (Ideal R), (↑T : Set (Ideal R)) ⊆ A ∧
      y ∈ (sSup (↑T : Set (Ideal R))).map f
  have hzero : P 0 := ⟨∅, by simp, zero_mem _⟩
  have hadd : ∀ y z, P y → P z → P (y + z) := by
    rintro y z ⟨T, hT, hy⟩ ⟨U, hU, hz⟩
    refine ⟨T ∪ U, ?_, ?_⟩
    · simpa only [Finset.coe_union] using Set.union_subset hT hU
    · exact add_mem
        (Ideal.map_mono (sSup_le fun I hI =>
          le_sSup (Finset.mem_union_left U hI)) hy)
        (Ideal.map_mono (sSup_le fun I hI =>
          le_sSup (Finset.mem_union_right T hI)) hz)
  rw [Ideal.map_sSup] at hx
  refine Submodule.iSup_induction (fun I : Ideal R => ⨆ _ : I ∈ A, I.map f)
    (motive := P) hx ?_ hzero hadd
  intro I y hy
  refine Submodule.iSup_induction (fun _ : I ∈ A => I.map f)
    (motive := P) hy ?_ hzero hadd
  intro hI z hz
  refine ⟨{I}, ?_, ?_⟩
  · simpa only [Finset.coe_singleton, Set.singleton_subset_iff] using hI
  · simpa only [Finset.coe_singleton, sSup_singleton] using hz

private theorem idempotent_eq_of_map_eq_sSup
    {R : Type u} [CommRing R] (A : Set (Ideal R))
    (hfin : ∀ T : Finset (Ideal R), (↑T : Set (Ideal R)) ⊆ A →
      HenselianRing R (sSup (↑T : Set (Ideal R))))
    (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B]
    {e e' : B} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (hEq : Ideal.Quotient.mk ((sSup A).map (algebraMap R B)) e =
      Ideal.Quotient.mk ((sSup A).map (algebraMap R B)) e') : e = e' := by
  have hdiff : e - e' ∈ (sSup A).map (algebraMap R B) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem e e').mp hEq
  obtain ⟨T, hTA, hdiffT⟩ :=
    exists_finset_of_mem_map_sSup (algebraMap R B) A hdiff
  let qT := Ideal.Quotient.mk ((sSup (↑T : Set (Ideal R))).map (algebraMap R B))
  have hEqT : qT e = qT e' :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem e e').mpr hdiffT
  obtain ⟨d, hd, huniq⟩ :=
    (HenselianRing.iff_existsUnique_isIdempotentElem_map.{u, v}
      (sSup (↑T : Set (Ideal R)))).mp (hfin T hTA) B (qT e) (he.map qT)
  exact (huniq e ⟨he, rfl⟩).trans (huniq e' ⟨he', hEqT.symm⟩).symm

namespace HenselianRing

variable {R : Type u} [CommRing R]

/-- The join of two Henselian ideals is Henselian. -/
theorem sup (I J : Ideal R) (hI : HenselianRing R I) (hJ : HenselianRing R J) :
    HenselianRing R (I ⊔ J) := by
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  let : HenselianRing R J := hJ
  let : HenselianRing R (RingHom.ker q) := by
    simpa only [q, Ideal.mk_ker] using hI
  apply (HenselianRing.iff_map_of_surjective_of_henselian_ker
    (I ⊔ J) q hq).2
  simpa only [Ideal.map_sup, q, Ideal.map_quotient_self, bot_sup_eq] using
    (HenselianRing.map_of_surjective J q hq)

/-- arbitrary suprema of Henselian ideals are Henselian, including the empty
supremum. There is no finiteness, locality, completeness, or nontriviality assumption. -/
theorem sSup (S : Set (Ideal R)) (hS : ∀ I ∈ S, HenselianRing R I) :
    HenselianRing R (sSup S) := by
  classical
  have hfin : ∀ T : Finset (Ideal R),
      (↑T : Set (Ideal R)) ⊆ S → HenselianRing R (SupSet.sSup (↑T : Set (Ideal R))) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      let : IsAdicComplete (⊥ : Ideal R) R := IsAdicComplete.bot R
      simpa only [Finset.coe_empty, sSup_empty] using
        (inferInstance : HenselianRing R (⊥ : Ideal R))
    | @insert I T _ ih =>
      intro hT
      have hI : HenselianRing R I := hS I (hT (by simp))
      have hT' : (↑T : Set (Ideal R)) ⊆ S := fun J hJ => hT (by simp [hJ])
      simpa only [Finset.coe_insert, sSup_insert] using
        HenselianRing.sup I (SupSet.sSup (↑T : Set (Ideal R))) hI (ih hT')
  apply (HenselianRing.iff_existsUnique_isIdempotentElem_map.{u, u} (SupSet.sSup S)).mpr
  intro B _ _ _ e0 he0
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective e0
  have hdef : b * b - b ∈ (SupSet.sSup S).map (algebraMap R B) := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (b * b) b).mp
    simpa only [isIdempotentElem_iff, map_mul] using he0
  obtain ⟨T, hTS, hdefT⟩ :=
    exists_finset_of_mem_map_sSup (algebraMap R B) S hdef
  let K : Ideal B := (SupSet.sSup (↑T : Set (Ideal R))).map (algebraMap R B)
  have hTIdem : IsIdempotentElem (Ideal.Quotient.mk K b) := by
    have hh := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := K) (b * b) b).mpr hdefT
    simpa only [isIdempotentElem_iff, map_mul] using hh
  obtain ⟨e, he, _⟩ :=
    ((HenselianRing.iff_existsUnique_isIdempotentElem_map.{u, u}
      (SupSet.sSup (↑T : Set (Ideal R)))).mp (hfin T hTS)) B
        (Ideal.Quotient.mk K b) hTIdem
  have hTSup : SupSet.sSup (↑T : Set (Ideal R)) ≤ SupSet.sSup S :=
    sSup_le fun I hI => le_sSup (hTS hI)
  have heSup : Ideal.Quotient.mk ((SupSet.sSup S).map (algebraMap R B)) e =
      Ideal.Quotient.mk ((SupSet.sSup S).map (algebraMap R B)) b := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem e b).mpr
    exact Ideal.map_mono hTSup ((Ideal.Quotient.mk_eq_mk_iff_sub_mem e b).mp he.2)
  refine ⟨e, ⟨he.1, heSup⟩, ?_⟩
  intro e' he'
  exact idempotent_eq_of_map_eq_sSup S hfin B he'.1 he.1 (he'.2.trans heSup.symm)

/-- The indexed formulation allows an independent index universe and an
empty index sort. -/
theorem iSup {ι : Sort v} (I : ι → Ideal R) (hI : ∀ i, HenselianRing R (I i)) :
    HenselianRing R (⨆ i, I i) := by
  change HenselianRing R (SupSet.sSup (Set.range I))
  exact sSup (Set.range I) fun J hJ => by
    obtain ⟨i, rfl⟩ := hJ
    exact hI i

/-- The unconditional defining supremum is itself Henselian. -/
theorem henselianRadical (R : Type u) [CommRing R] :
    HenselianRing R (Ideal.henselianRadical R) := by
  exact sSup {I : Ideal R | HenselianRing R I} fun _ hI => hI

/-- The defining supremum is the greatest Henselian ideal. -/
theorem iff_le_henselianRadical (I : Ideal R) :
    HenselianRing R I ↔ I ≤ Ideal.henselianRadical R := by
  constructor
  · exact Ideal.le_henselianRadical I
  · intro hI
    let : HenselianRing R (Ideal.henselianRadical R) := henselianRadical R
    exact of_le hI

end HenselianRing

namespace Ideal

variable {R : Type u} [CommRing R]

/-- membership is detected by Henselianity of the principal ideal. -/
theorem mem_henselianRadical_iff (r : R) :
    r ∈ henselianRadical R ↔ HenselianRing R (span {r}) := by
  rw [HenselianRing.iff_le_henselianRadical, span_singleton_le_iff_mem]

/-- ordinary radical does not enlarge the greatest Henselian ideal. -/
theorem henselianRadical_radical (R : Type u) [CommRing R] :
    (henselianRadical R).radical = henselianRadical R := by
  apply le_antisymm
  · exact le_henselianRadical _
      ((HenselianRing.iff_radical _).mp (HenselianRing.henselianRadical R))
  · exact le_radical

/-- Every nilpotent element belongs to the greatest Henselian ideal. -/
theorem nilradical_le_henselianRadical (R : Type u) [CommRing R] :
    (⊥ : Ideal R).radical ≤ henselianRadical R := by
  have hbot : HenselianRing R (⊥ : Ideal R) :=
    IsAdicComplete.henselianRing R ⊥
  exact le_henselianRadical _ ((HenselianRing.iff_radical _).mp hbot)

/-- A surjection with independently Henselian kernel recovers the greatest
Henselian ideal by inverse image. The source and target universes are independent.
Quotienting by a Henselian ideal is the standard special case. -/
theorem comap_henselianRadical_of_surjective_of_henselian_ker
    {S : Type v} [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    [HenselianRing R (RingHom.ker f)] :
    (henselianRadical S).comap f = henselianRadical R := by
  apply le_antisymm
  · apply le_henselianRadical ((henselianRadical S).comap f)
    apply (HenselianRing.iff_map_of_surjective_of_henselian_ker
      ((henselianRadical S).comap f) f hf).mpr
    rw [map_comap_of_surjective f hf]
    exact HenselianRing.henselianRadical S
  · let : HenselianRing R (henselianRadical R) :=
      HenselianRing.henselianRadical R
    exact map_le_iff_le_comap.mp
      (le_henselianRadical _
        (HenselianRing.map_of_surjective (henselianRadical R) f hf))

/-- A surjective ring homomorphism with Henselian kernel carries the greatest
Henselian ideal onto the greatest Henselian ideal of the target. The source and
target universes are independent. -/
theorem map_henselianRadical_of_surjective_of_henselian_ker
    {S : Type v} [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    [HenselianRing R (RingHom.ker f)] :
    (henselianRadical R).map f = henselianRadical S := by
  simpa only [comap_henselianRadical_of_surjective_of_henselian_ker f hf] using
    (map_comap_of_surjective f hf (henselianRadical S))

end Ideal
