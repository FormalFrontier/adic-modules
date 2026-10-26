/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.HenselianTransport
public import AdicModules.RingTheory.Idempotents
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Finite algebras over Henselian local rings

A commutative algebra finite over a Henselian local ring decomposes as a finite
product of local quotient algebras. The indexing set may be empty, so the zero
algebra is included. Each quotient algebra is finite over the base ring by the
standard instance for quotients of finite modules.

This is the finite-algebra characterization of Henselian local rings, formulated
using quotient factors.

## References

* The Stacks Project, [Tag 04GE](https://stacks.math.columbia.edu/tag/04GE).
-/

@[expose] public section

universe u v
universe w

open scoped BigOperators

section IdempotentLifting

variable {R : Type u} [CommRing R] {I : Ideal R}

namespace HenselianRing

/-- Orthogonal families lift modulo a Henselian ideal, even with an infinite index type. -/
theorem lift_orthogonalIdempotents [HenselianRing R I]
    {ι : Type v} (e : ι → R ⧸ I) (he : OrthogonalIdempotents e) :
    ∃ a : ι → R, OrthogonalIdempotents a ∧
      ∀ i, Ideal.Quotient.mk I (a i) = e i := by
  classical
  choose a ha hq using fun i => (existsUnique_isIdempotentElem I (he.idem i)).exists
  have hzero : ∃! b : R, IsIdempotentElem b ∧ Ideal.Quotient.mk I b = 0 :=
    existsUnique_isIdempotentElem I (by
      change (0 : R ⧸ I) * 0 = 0
      exact mul_zero 0)
  refine ⟨a, ⟨ha, ?_⟩, hq⟩
  intro i j hij
  apply hzero.unique
  · refine ⟨(ha i).mul (ha j), ?_⟩
    rw [map_mul, hq i, hq j]
    exact he.ortho hij
  · refine ⟨?_, map_zero _⟩
    change (0 : R) * 0 = 0
    exact mul_zero 0

/-- Lift a complete finite orthogonal family modulo a Henselian ideal.

The complementary idempotent of the sum vanishes by uniqueness of the lift of zero. -/
theorem lift_completeOrthogonalIdempotents [HenselianRing R I]
    {ι : Type v} [Fintype ι] (e : ι → R ⧸ I)
    (he : CompleteOrthogonalIdempotents e) :
    ∃ a : ι → R, CompleteOrthogonalIdempotents a ∧
      ∀ i, Ideal.Quotient.mk I (a i) = e i := by
  classical
  obtain ⟨a, hortho, hq⟩ := lift_orthogonalIdempotents e he.toOrthogonalIdempotents
  have hsum : IsIdempotentElem (∑ i, a i) := hortho.isIdempotentElem_sum
  have hzero : ∃! b : R, IsIdempotentElem b ∧ Ideal.Quotient.mk I b = 0 :=
    existsUnique_isIdempotentElem I (by
      change (0 : R ⧸ I) * 0 = 0
      exact mul_zero 0)
  have hsum_zero : 1 - ∑ i, a i = 0 := by
    apply hzero.unique
    · refine ⟨hsum.one_sub, ?_⟩
      simp only [map_sub, map_one, map_sum]
      simp_rw [hq]
      rw [he.complete, sub_self]
    · refine ⟨?_, map_zero _⟩
      change (0 : R) * 0 = 0
      exact mul_zero 0
  exact ⟨a, ⟨hortho, (sub_eq_zero.mp hsum_zero).symm⟩, hq⟩

end HenselianRing

end IdempotentLifting

namespace Ideal.Quotient

/-- A quotient by a positive power of a maximal ideal is local. -/
theorem isLocalRing_pow_of_isMaximal
    {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal]
    {n : ℕ} (hn : n ≠ 0) : IsLocalRing (R ⧸ I ^ n) := by
  classical
  have hproper : I ^ n ≠ ⊤ :=
    ne_top_of_le_ne_top ‹I.IsMaximal›.ne_top (Ideal.pow_le_self hn)
  let : Nontrivial (R ⧸ I ^ n) :=
    (Ideal.Quotient.nontrivial_iff (I := I ^ n)).mpr hproper
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  change ¬ IsUnit (Ideal.Quotient.mk (I ^ n) x) at ha
  change ¬ IsUnit (Ideal.Quotient.mk (I ^ n) y) at hb
  change ¬ IsUnit (Ideal.Quotient.mk (I ^ n) x + Ideal.Quotient.mk (I ^ n) y)
  intro hab
  have hx : x ∈ I := by
    by_contra hx
    exact ha ((Ideal.Quotient.isUnit_mk_pow_iff_notMem I hn).mpr hx)
  have hy : y ∈ I := by
    by_contra hy
    exact hb ((Ideal.Quotient.isUnit_mk_pow_iff_notMem I hn).mpr hy)
  have hxy : x + y ∉ I :=
    (Ideal.Quotient.isUnit_mk_pow_iff_notMem I hn).mp
      (by simpa only [map_add] using hab)
  exact hxy (I.add_mem hx hy)

end Ideal.Quotient

namespace IsArtinianRing

/-- A commutative Artinian ring decomposes into local quotients by positive powers
of its maximal ideals. The maximal spectrum may be empty. -/
theorem exists_local_quotient_pi
    (R : Type*) [CommRing R] [IsArtinianRing R] :
    ∃ n : ℕ, 0 < n ∧
      (⨅ m : MaximalSpectrum R, m.asIdeal ^ n) = ⊥ ∧
      (∀ m : MaximalSpectrum R, IsLocalRing (R ⧸ m.asIdeal ^ n)) ∧
      Nonempty (R ≃ₐ[R] (∀ m : MaximalSpectrum R, R ⧸ m.asIdeal ^ n)) := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
  have hpow : nilradical R ^ (n + 1) = ⊥ := by
    simp [pow_succ, hn]
  refine ⟨n + 1, Nat.succ_pos n, ?_, ?_, ?_⟩
  · rw [← IsArtinianRing.nilradical_pow_eq_iInf R (n + 1)]
    exact hpow
  · intro m
    exact Ideal.Quotient.isLocalRing_pow_of_isMaximal m.asIdeal (Nat.succ_ne_zero n)
  · exact ⟨((AlgEquiv.quotientBot R R).symm.trans
      (Ideal.quotientEquivAlgOfEq R hpow.symm)).trans
      (IsArtinianRing.quotNilradicalPowEquivPi R (n + 1))⟩

end IsArtinianRing

/-- The complete-idempotent quotient decomposition respects the base algebra.
Its coordinates are the canonical quotient maps. -/
theorem CompleteOrthogonalIdempotents.exists_algEquiv_pi_quotient
    {R : Type u} {S : Type v} {ι : Type w}
    [CommSemiring R] [CommRing S] [Algebra R S] [Fintype ι]
    {e : ι → S} (he : CompleteOrthogonalIdempotents e) :
    ∃ E : S ≃ₐ[R] Π i : ι, S ⧸ Ideal.span {1 - e i},
      ∀ (s : S) (i : ι),
        E s i = Ideal.Quotient.mk (Ideal.span {1 - e i}) s := by
  refine ⟨AlgEquiv.ofBijective
    (AlgHom.pi fun i : ι =>
      Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))
    he.bijective_pi, ?_⟩
  intro s i
  rfl

/-- Pull back coordinate idempotents along a finite product equivalence with local
factors. The corresponding canonical quotient rings are local. -/
theorem CompleteOrthogonalIdempotents.exists_of_pi_ringEquiv_local
    {T : Type u} {ι : Type w} (L : ι → Type v)
    [CommRing T] [∀ i, CommRing (L i)] [∀ i, IsLocalRing (L i)]
    [Fintype ι] (E : T ≃+* ∀ i, L i) :
    ∃ t : ι → T,
      CompleteOrthogonalIdempotents t ∧
      (∀ i, E (t i) i = 1) ∧
      (∀ i j, i ≠ j → E (t i) j = 0) ∧
      ∀ i, IsLocalRing (T ⧸ Ideal.span {1 - t i}) := by
  classical
  let t : ι → T := fun i => E.symm (Pi.single i (1 : L i))
  have ht : CompleteOrthogonalIdempotents t :=
    (CompleteOrthogonalIdempotents.single L).map E.symm.toRingHom
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro i
    simp [t]
  · intro i j hij
    simp [t, Ne.symm hij]
  · intro i
    let f : T →+* L i := (Pi.evalRingHom L i).comp E.toRingHom
    have hf : Function.Surjective f := by
      intro y
      refine ⟨E.symm (Pi.single i y), ?_⟩
      change E (E.symm (Pi.single i y)) i = y
      simp
    have hker : RingHom.ker f = Ideal.span {1 - t i} := by
      ext x
      constructor
      · intro hx
        change E x i = 0 at hx
        apply Ideal.mem_span_singleton'.mpr
        refine ⟨x, ?_⟩
        apply E.injective
        ext j
        by_cases hji : j = i
        · subst j
          simp [t, hx]
        · simp [t, hji]
      · intro hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
        change E (a * (1 - t i)) i = 0
        simp [t]
    rw [← hker]
    exact (RingHom.quotientKerEquivOfSurjective (f := f) hf).symm.isLocalRing

namespace HenselianRing

private theorem isArtinianRing_quotient_map_maximalIdeal
    (R : Type u) (S : Type v) [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsArtinianRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let J : Ideal S := m.map (algebraMap R S)
  let k : Type u := R ⧸ m
  let T : Type v := S ⧸ J
  let : Field k := Ideal.Quotient.field m
  have hmJ : m ≤ J.comap (algebraMap R S) := Ideal.le_comap_map
  let : Algebra k T :=
    Ideal.Quotient.algebraQuotientOfLEComap (R := R) (A := S) (p := m) (P := J) hmJ
  let : IsScalarTower R k T := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change Ideal.Quotient.mk J (algebraMap R S r) =
      Ideal.quotientMap J (algebraMap R S) hmJ (Ideal.Quotient.mk m r)
    exact Ideal.quotientMap_mk.symm
  let : Module.Finite R T := inferInstance
  let : Module.Finite k T := Module.Finite.of_restrictScalars_finite R k T
  exact IsArtinianRing.of_finite k T

private theorem isLocalRing_quotient_of_isLocalRing_quotientQuotient
    {R : Type u} [CommRing R] (I J : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥)
    [IsLocalRing ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))] :
    IsLocalRing (R ⧸ J) := by
  have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J :=
    Ideal.mk_ker
  have hmap : I.map (Ideal.Quotient.mk J) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap,
      Ideal.comap_jacobson_of_surjective Ideal.Quotient.mk_surjective, hker]
    exact hI.trans (Ideal.jacobson_mono bot_le)
  let : IsLocalRing ((R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J)) :=
    (DoubleQuot.quotQuotEquivComm I J).isLocalRing
  let := isLocalHom_of_le_jacobson_bot (I.map (Ideal.Quotient.mk J)) hmap
  exact (Ideal.Quotient.mk (I.map (Ideal.Quotient.mk J))).domain_isLocalRing

/-- A finite commutative algebra over a Henselian local ring is isomorphic, as an
algebra over the base ring, to a finite product of local quotient algebras.
The product is allowed to be empty. This is the finite-algebra characterization of
Henselian local rings in the Stacks Project,
[Tag 04GE](https://stacks.math.columbia.edu/tag/04GE), with the local factors
presented as quotients of `S`. -/
theorem exists_algEquiv_pi_quotient (R : Type u) (S : Type v)
    [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)]
    [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ (n : ℕ) (J : Fin n → Ideal S),
      (∀ i, IsLocalRing (S ⧸ J i)) ∧
        Nonempty (S ≃ₐ[R] ∀ i, S ⧸ J i) := by
  classical
  let I : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  let : HenselianRing S I :=
    HenselianRing.map_of_isIntegral (IsLocalRing.maximalIdeal R) (algebraMap R S)
      (algebraMap_isIntegral_iff.mpr inferInstance)
  let T : Type v := S ⧸ I
  let : IsArtinianRing T := isArtinianRing_quotient_map_maximalIdeal R S
  obtain ⟨p, _, _, hlocal, ⟨E⟩⟩ := IsArtinianRing.exists_local_quotient_pi T
  let ι : Type v := MaximalSpectrum T
  let : Fintype ι := Fintype.ofFinite ι
  let L : ι → Type v := fun i => T ⧸ i.asIdeal ^ p
  let : ∀ i, IsLocalRing (L i) := hlocal
  obtain ⟨t, ht, _, _, htlocal⟩ :=
    CompleteOrthogonalIdempotents.exists_of_pi_ringEquiv_local L E.toRingEquiv
  obtain ⟨a, ha, hq⟩ := lift_completeOrthogonalIdempotents (I := I) t ht
  let J : ι → Ideal S := fun i => Ideal.span {1 - a i}
  have hJ (i : ι) :
      (J i).map (Ideal.Quotient.mk I) = Ideal.span {1 - t i} := by
    simp only [J, Ideal.map_span, Set.image_singleton, map_sub, map_one, hq i]
    rfl
  have hlocalJ (i : ι) : IsLocalRing (S ⧸ J i) := by
    let : IsLocalRing (T ⧸ (J i).map (Ideal.Quotient.mk I)) := by
      rw [hJ]
      exact htlocal i
    exact isLocalRing_quotient_of_isLocalRing_quotientQuotient I (J i)
      (HenselianRing.jac (R := S) (I := I))
  obtain ⟨F, _⟩ :=
    CompleteOrthogonalIdempotents.exists_algEquiv_pi_quotient (R := R) ha
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => J (e.symm i), ?_, ?_⟩
  · intro i
    exact hlocalJ (e.symm i)
  · exact ⟨F.trans (AlgEquiv.piCongrLeft' R (fun i : ι => S ⧸ J i) e)⟩

end HenselianRing
