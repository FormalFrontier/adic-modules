/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Choose

/-!
# Canonical ideal quotients, nilpotent actions and additive squares

A submodule contained in its ideal multiple vanishes if a fixed power of the
ideal annihilates it. The ideal itself need not be nilpotent, and no finite
generation hypothesis is needed.

The kernel of a nested quotient factor is the image ideal times the whole
quotient module, using its quotient-ring action. An additive commutative square
with surjective source projection and the prescribed ideal-multiple kernels
transports residual bijectivity to bijectivity of `LinearMap.reduceModIdeal`.
The residual groups need not be commutative and carry no scalar action.

The image of an ideal in its power quotient is nilpotent, including at exponent
zero in the zero quotient ring.

Finite generation lifts from the quotient by an ideal when a uniform power of
the ideal annihilates the whole module.

## References

These results use Mathlib's quotient and kernel APIs by Johannes Hölzl,
Mario Carneiro, Kevin Buzzard and Yury Kudryashov; its quotient-ring module
action by Pierre-Alexandre Bazin; its ideal-image and scalar-restriction APIs;
and Judith Ludwig and Christian Merten's `LinearMap.reduceModIdeal`.
The action-nilpotent vanishing criterion uses the standard elementary iteration
of ideal multiplication, without a finite-generation form of Nakayama's lemma.
-/

@[expose] public section

universe u v uR uM uA uX uY uX₀ uY₀

namespace Submodule

/-- A submodule contained in its ideal multiple is zero if some fixed power of
the ideal annihilates the submodule. No finite generation or nilpotence of the
ideal itself is required. The exponent may be zero, and the scalar semiring need
not be commutative. -/
theorem eq_bot_of_le_smul_of_pow_smul_eq_bot
    {S : Type u} [Semiring S]
    {V : Type v} [AddCommMonoid V] [Module S V]
    (q : Ideal S) (n : ℕ) (P : Submodule S V)
    (hkill : (q ^ n) • P = ⊥) (hP : P ≤ q • P) : P = ⊥ := by
  have hpow (k : ℕ) : P ≤ q ^ k • P := by
    induction k with
    | zero => simpa only [Submodule.pow_zero, Submodule.one_smul] using (le_refl P)
    | succ k ih =>
      calc
        P ≤ q ^ k • P := ih
        _ ≤ q ^ k • (q • P) := Submodule.smul_mono (le_refl _) hP
        _ = q ^ (k + 1) • P := by rw [Submodule.pow_succ, Submodule.mul_smul]
  refine le_antisymm ?_ bot_le
  simpa only [hkill] using hpow n

end Submodule

/-- The kernel of a nested quotient factor is the image ideal times the whole
module, with the canonical quotient-ring scalar action. -/
theorem Submodule.factor_eq_zero_iff_mem_map_smul_top
    {R : Type uR} [CommRing R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (J K : Ideal R) (hJK : J ≤ K)
    (x : M ⧸ (J • (⊤ : Submodule R M))) :
    Submodule.factor
        (Submodule.smul_mono_left hJK :
          J • (⊤ : Submodule R M) ≤ K • ⊤) x = 0 ↔
      x ∈ (K.map (Ideal.Quotient.mk J)) •
        (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))) := by
  have hker :
      (Submodule.factor (Submodule.smul_mono_left hJK) :
        (M ⧸ (J • (⊤ : Submodule R M))) →ₗ[R]
          M ⧸ (K • (⊤ : Submodule R M))).ker =
        K • (⊤ : Submodule R (M ⧸ (J • (⊤ : Submodule R M)))) := by
    rw [Submodule.ker_mapQ, Submodule.comap_id, Submodule.map_smul'', Submodule.map_top,
      Submodule.range_mkQ]
  have hsmul := Submodule.restrictScalars_map_smul_eq (R := R ⧸ J) K
    (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))))
  change x ∈ (Submodule.factor (Submodule.smul_mono_left hJK)).ker ↔ _
  rw [hker]
  exact Iff.symm (SetLike.ext_iff.mp hsmul x)

namespace LinearMap

section QuotientSquare

variable {A : Type uA} [CommRing A]
variable {X : Type uX} [AddCommGroup X] [Module A X]
variable {Y : Type uY} [AddCommGroup Y] [Module A Y]
variable {X₀ : Type uX₀} [AddGroup X₀]
variable {Y₀ : Type uY₀} [AddGroup Y₀]

/-- An additive residual isomorphism detects bijectivity modulo an ideal.
Only the source quotient map needs an explicit surjectivity hypothesis. -/
theorem bijective_reduceModIdeal_of_addHom_square
    (J : Ideal A) (f : X →ₗ[A] Y) (rX : X →+ X₀) (rY : Y →+ Y₀)
    (hX : Function.Surjective rX)
    (kX : ∀ x, rX x = 0 ↔ x ∈ J • (⊤ : Submodule A X))
    (kY : ∀ y, rY y = 0 ↔ y ∈ J • (⊤ : Submodule A Y))
    (g₀ : X₀ →+ Y₀) (hg₀ : Function.Bijective g₀)
    (comm : ∀ x, rY (f x) = g₀ (rX x)) :
    Function.Bijective (f.reduceModIdeal J) := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A X)) x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A X)) y
    apply (Submodule.Quotient.eq _).2
    apply (kX (x - y)).1
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply hg₀.1
    have hmem : f x - f y ∈ J • (⊤ : Submodule A Y) :=
      (Submodule.Quotient.eq _).1 (by
        simpa only [LinearMap.reduceModIdeal_apply] using hxy)
    have hzero := (kY (f x - f y)).2 hmem
    rw [map_sub] at hzero
    rw [← comm x, ← comm y]
    exact sub_eq_zero.mp hzero
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A Y)) y
    obtain ⟨x₀, hx₀⟩ := hg₀.2 (rY y)
    obtain ⟨x, hx⟩ := hX x₀
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [LinearMap.reduceModIdeal_apply]
    apply (Submodule.Quotient.eq _).2
    apply (kY (f x - y)).1
    rw [map_sub, comm x, hx, hx₀, sub_self]

end QuotientSquare

end LinearMap

/-- The image of an ideal in the quotient by its nth power is nilpotent. -/
theorem Ideal.isNilpotent_map_quotient_pow
    {R : Type uR} [CommRing R] (I : Ideal R) (n : ℕ) :
    IsNilpotent (I.map (Ideal.Quotient.mk (I ^ n))) := by
  use n
  simp only [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]

/-- Finite generation lifts from reduction by an ideal whose power annihilates
the module. The scalar ring need not be commutative, and no finiteness or
two-sidedness assumption on the ideal is needed. -/
theorem Module.finite_iff_quotient_smul_of_pow_smul_top_eq_bot
    {S : Type uR} [Ring S]
    {V : Type uM} [AddCommGroup V] [Module S V]
    (q : Ideal S) (n : ℕ)
    (hkill : (q ^ n) • (⊤ : Submodule S V) = ⊥) :
    Module.Finite S V ↔ Module.Finite S (V ⧸ (q • (⊤ : Submodule S V))) := by
  classical
  constructor
  · intro hV
    let : Module.Finite S V := hV
    exact Module.Finite.quotient S (q • (⊤ : Submodule S V))
  · intro hquot
    let Q : Submodule S V := q • (⊤ : Submodule S V)
    let : Module.Finite S (V ⧸ Q) := hquot
    obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := S) (M := V ⧸ Q)
    choose t ht using fun i : Fin m => Q.mkQ_surjective (s i)
    let N : Submodule S V := Submodule.span S (Set.range t)
    have hNfg : N.FG :=
      Submodule.fg_def.mpr ⟨Set.range t, Set.finite_range t, rfl⟩
    have hmap : N.map Q.mkQ = ⊤ := by
      change (Submodule.span S (Set.range t)).map Q.mkQ = _
      rw [Submodule.map_span]
      have himage : Q.mkQ '' Set.range t = Set.range s := by
        ext y
        constructor
        · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, (ht i).symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨t i, ⟨i, rfl⟩, ht i⟩
      rw [himage]
      exact hs
    have hsup : Q ⊔ N = ⊤ := (Q.map_mkQ_eq_top N).mp hmap
    have hqmap : (q • (⊤ : Submodule S V)).map N.mkQ = ⊤ :=
      (N.map_mkQ_eq_top (q • (⊤ : Submodule S V))).mpr (by
        change N ⊔ Q = ⊤
        simpa only [sup_comm] using hsup)
    have hmaptop : (⊤ : Submodule S V).map N.mkQ = ⊤ :=
      (N.map_mkQ_eq_top ⊤).mpr (by simp only [sup_top_eq])
    have hqX : (⊤ : Submodule S (V ⧸ N)) ≤
        q • (⊤ : Submodule S (V ⧸ N)) := by
      have heq : q • (⊤ : Submodule S (V ⧸ N)) = ⊤ := by
        simpa only [Submodule.map_smul'', hmaptop] using hqmap
      exact le_of_eq heq.symm
    have hkillX : (q ^ n) • (⊤ : Submodule S (V ⧸ N)) = ⊥ := by
      have hm := congrArg (fun P : Submodule S V => P.map N.mkQ) hkill
      simpa only [Submodule.map_smul'', hmaptop, Submodule.map_bot] using hm
    have hX : (⊤ : Submodule S (V ⧸ N)) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_pow_smul_eq_bot q n _ hkillX hqX
    have hNtop : N = ⊤ := by
      have hbotmap : (⊥ : Submodule S V).map N.mkQ = ⊤ := by
        simpa only [Submodule.map_bot] using hX.symm
      simpa only [sup_bot_eq] using (N.map_mkQ_eq_top ⊥).mp hbotmap
    exact Module.finite_def.mpr (hNtop ▸ hNfg)
