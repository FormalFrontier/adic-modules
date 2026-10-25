/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianIdeal
import AdicModules.RingTheory.HenselianPi
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# A shared independent 2-adic model for the research statements

The model identifies the defining supremum with the stock maximal ideal using
only its two defining bounds and the independently available Henselian maximal-ideal
instance. The closure, greatestness, membership, radicality, nilradical inclusion,
and recovery interfaces are exercised only after the independent model is established.
-/

universe v

namespace HenselianIdealResearch

private abbrev Z2 := PadicInt 2
private noncomputable abbrev twoIdeal : Ideal Z2 := IsLocalRing.maximalIdeal Z2

/-- The stock maximal ideal is the principal ideal (2). -/
private theorem twoIdeal_eq_span : twoIdeal = Ideal.span {(2 : Z2)} :=
  PadicInt.maximalIdeal_eq_span_p (p := 2)

/-- The maximal ideal is recovered using only the defining bounds and stock input. -/
private theorem two_radical_eq : Ideal.henselianRadical Z2 = twoIdeal :=
  le_antisymm
    ((Ideal.henselianRadical_le_jacobson Z2).trans
      (show Ideal.jacobson (⊥ : Ideal Z2) ≤ twoIdeal from
        sInf_le ⟨bot_le, inferInstance⟩))
    (Ideal.le_henselianRadical twoIdeal
      (inferInstance : HenselianRing Z2 twoIdeal))

private theorem two_radical_eq_span :
    Ideal.henselianRadical Z2 = Ideal.span {(2 : Z2)} :=
  two_radical_eq.trans twoIdeal_eq_span

private theorem two_mem_radical : (2 : Z2) ∈ Ideal.henselianRadical Z2 :=
  two_radical_eq_span.symm ▸ Ideal.subset_span (Set.mem_singleton (2 : Z2))

private theorem two_ne_zero : (2 : Z2) ≠ 0 :=
  PadicInt.prime_p.ne_zero

/-- Positive boundaries: the greatest ideal is nonzero and proper, and contains a
nonnilpotent element. These facts follow from the independently identified maximal ideal. -/
example : Ideal.henselianRadical Z2 ≠ ⊥ ∧ Ideal.henselianRadical Z2 ≠ ⊤ ∧
    (2 : Z2) ∈ Ideal.henselianRadical Z2 ∧ ¬ IsNilpotent (2 : Z2) :=
  ⟨(fun h => two_ne_zero (Ideal.mem_bot.mp (h ▸ two_mem_radical))),
    (fun h => (Ideal.IsMaximal.ne_top (inferInstance : twoIdeal.IsMaximal))
      (two_radical_eq.symm.trans h)),
    two_mem_radical, fun h => two_ne_zero h.eq_zero⟩

/-- The powers use stock radical invariance and the independent maximal-ideal input. -/
private theorem twoIdeal_pow_henselian {n : ℕ} (hn : n ≠ 0) :
    HenselianRing Z2 (twoIdeal ^ n) :=
  (HenselianRing.iff_radical (twoIdeal ^ n)).mpr
    (Eq.mpr (congrArg (HenselianRing Z2)
      ((Ideal.radical_pow twoIdeal hn).trans
        (Ideal.radical_eq_iff.mpr (Ideal.IsPrime.isRadical inferInstance))))
      (inferInstance : HenselianRing Z2 twoIdeal))

/-- A genuine finite join of the known Henselian powers (4) and (8). -/
example : HenselianRing Z2 (twoIdeal ^ 2 ⊔ twoIdeal ^ 3) :=
  HenselianRing.sup _ _ (twoIdeal_pow_henselian (Nat.succ_ne_zero 1))
    (twoIdeal_pow_henselian (Nat.succ_ne_zero 2))

/-- An infinite standard family, without a manufactured Henselianity assumption. -/
example : HenselianRing Z2 (sSup (Set.range fun n : ℕ => twoIdeal ^ (n + 2))) :=
  HenselianRing.sSup _ fun _ h =>
    Exists.elim h fun n hn => hn ▸ twoIdeal_pow_henselian (Nat.succ_ne_zero (n + 1))

/-- The indexed interface includes arbitrary independent index universes and emptiness. -/
example {ι : Sort v} (n : ι → ℕ) :
    HenselianRing Z2 (⨆ i, twoIdeal ^ (n i + 2)) :=
  HenselianRing.iSup _ fun i => twoIdeal_pow_henselian (Nat.succ_ne_zero (n i + 1))

/-- The empty-supremum boundary requires no nonempty-family hypothesis. -/
example : HenselianRing Z2 (sSup (∅ : Set (Ideal Z2))) :=
  HenselianRing.sSup _ fun _ h => False.elim h

example : HenselianRing Z2 (Ideal.henselianRadical Z2) :=
  HenselianRing.henselianRadical Z2

/-- The universal property characterizes every ideal of this genuine standard ring. -/
example (I : Ideal Z2) : HenselianRing Z2 I ↔ I ≤ twoIdeal :=
  Eq.mp (congrArg (fun J : Ideal Z2 => HenselianRing Z2 I ↔ I ≤ J) two_radical_eq)
    (HenselianRing.iff_le_henselianRadical I)

example (x : Z2) : x ∈ twoIdeal ↔ HenselianRing Z2 (Ideal.span {x}) :=
  Eq.mp (congrArg (fun J : Ideal Z2 => x ∈ J ↔ HenselianRing Z2 (Ideal.span {x}))
    two_radical_eq) (Ideal.mem_henselianRadical_iff x)

example : (Ideal.henselianRadical Z2).radical = Ideal.henselianRadical Z2 :=
  Ideal.henselianRadical_radical Z2

example : (⊥ : Ideal Z2).radical ≤ twoIdeal :=
  (Ideal.nilradical_le_henselianRadical Z2).trans (le_of_eq two_radical_eq)

private noncomputable abbrev residueMap : Z2 →+* Z2 ⧸ twoIdeal :=
  Ideal.Quotient.mk twoIdeal

/-- Kernel Henselianity comes from the stock source ideal, not any research conclusion. -/
private instance : HenselianRing Z2 (RingHom.ker residueMap) :=
  Eq.mpr (congrArg (HenselianRing Z2) Ideal.mk_ker)
    (inferInstance : HenselianRing Z2 twoIdeal)

/-- Recovery through the nontrivial quotient by (2), not an identity-map example. -/
example : Nontrivial (Z2 ⧸ twoIdeal) ∧
    (Ideal.henselianRadical (Z2 ⧸ twoIdeal)).comap residueMap = twoIdeal :=
  ⟨Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance),
    (Ideal.comap_henselianRadical_of_surjective_of_henselian_ker residueMap
      (Ideal.Quotient.mk_surjective)).trans two_radical_eq⟩

/-- The component Jacobson radical lies in the maximal ideal. -/
private theorem two_jacobson_le :
    Ideal.jacobson (⊥ : Ideal Z2) ≤ twoIdeal :=
  sInf_le ⟨bot_le, inferInstance⟩

private theorem two_pi_henselian :
    HenselianRing (Bool → Z2) (Ideal.pi (fun _ : Bool => twoIdeal)) :=
  @HenselianRing.pi Bool (fun _ => Z2) (fun _ => inferInstance)
    (fun _ => twoIdeal) (fun _ => inferInstance)

/-- The two-coordinate supremum is computed from its defining bounds. -/
private theorem two_pi_radical_eq :
    Ideal.henselianRadical (Bool → Z2) = Ideal.pi (fun _ : Bool => twoIdeal) := by
  apply le_antisymm
  · intro x hx
    refine (Ideal.mem_pi _ x).mpr ?_
    intro b
    let e : (Bool → Z2) →+* Z2 := Pi.evalRingHom (fun _ => Z2) b
    have he : Function.Surjective e := fun a => ⟨fun _ => a, rfl⟩
    have hj : Ideal.jacobson (⊥ : Ideal (Bool → Z2)) ≤
        Ideal.comap e (Ideal.jacobson (⊥ : Ideal Z2)) := by
      calc
        _ ≤ Ideal.jacobson (RingHom.ker e) := Ideal.jacobson_mono bot_le
        _ = _ := (Ideal.comap_jacobson_of_surjective he).symm
    exact two_jacobson_le (hj (Ideal.henselianRadical_le_jacobson _ hx))
  · exact Ideal.le_henselianRadical _ two_pi_henselian

private noncomputable def twoEvaluation : (Bool → Z2) →+* (Z2 × Z2) :=
  (Pi.evalRingHom (fun _ => Z2) false).prod (Pi.evalRingHom (fun _ => Z2) true)

private theorem twoEvaluation_surjective : Function.Surjective twoEvaluation := by
  intro z
  exact ⟨fun b => cond b z.2 z.1, rfl⟩

private theorem twoEvaluation_map :
    (Ideal.pi (fun _ : Bool => twoIdeal)).map twoEvaluation = twoIdeal.prod twoIdeal := by
  ext z
  rw [Ideal.mem_map_iff_of_surjective twoEvaluation twoEvaluation_surjective,
    Ideal.mem_prod]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(Ideal.mem_pi _ x).mp hx false, (Ideal.mem_pi _ x).mp hx true⟩
  · rintro ⟨h0, h1⟩
    refine ⟨fun b => cond b z.2 z.1, ?_, rfl⟩
    exact (Ideal.mem_pi _ _).mpr (fun b => by cases b <;> assumption)

/-- The binary pair is obtained by mapping the Henselian two-coordinate pair. -/
private theorem two_prod_henselian :
    HenselianRing (Z2 × Z2) (twoIdeal.prod twoIdeal) := by
  have h := @HenselianRing.map_of_surjective (Bool → Z2) (Z2 × Z2)
    inferInstance inferInstance (Ideal.pi (fun _ : Bool => twoIdeal))
    two_pi_henselian twoEvaluation twoEvaluation_surjective
  rw [twoEvaluation_map] at h
  exact h

/-- The binary supremum is computed using the two projection surjections. -/
private theorem two_prod_radical_eq :
    Ideal.henselianRadical (Z2 × Z2) = twoIdeal.prod twoIdeal := by
  apply le_antisymm
  · intro z hz
    have hj := Ideal.henselianRadical_le_jacobson (Z2 × Z2) hz
    apply (Ideal.mem_prod _ _).mpr
    constructor
    · have hf : Function.Surjective (RingHom.fst Z2 Z2) :=
        fun a => ⟨(a, 0), rfl⟩
      have h : Ideal.jacobson (⊥ : Ideal (Z2 × Z2)) ≤
          Ideal.comap (RingHom.fst Z2 Z2) (Ideal.jacobson (⊥ : Ideal Z2)) := by
        calc
          _ ≤ Ideal.jacobson (RingHom.ker (RingHom.fst Z2 Z2)) :=
            Ideal.jacobson_mono bot_le
          _ = _ := (Ideal.comap_jacobson_of_surjective hf).symm
      exact two_jacobson_le (h hj)
    · have hf : Function.Surjective (RingHom.snd Z2 Z2) :=
        fun a => ⟨(0, a), rfl⟩
      have h : Ideal.jacobson (⊥ : Ideal (Z2 × Z2)) ≤
          Ideal.comap (RingHom.snd Z2 Z2) (Ideal.jacobson (⊥ : Ideal Z2)) := by
        calc
          _ ≤ Ideal.jacobson (RingHom.ker (RingHom.snd Z2 Z2)) :=
            Ideal.jacobson_mono bot_le
          _ = _ := (Ideal.comap_jacobson_of_surjective hf).symm
      exact two_jacobson_le (h hj)
  · exact Ideal.le_henselianRadical _ two_prod_henselian

/-- The binary supremum is nonzero and proper and contains a nonnilpotent element. -/
example : Ideal.henselianRadical (Z2 × Z2) ≠ ⊥ ∧
    Ideal.henselianRadical (Z2 × Z2) ≠ ⊤ ∧
    ((2 : Z2), (2 : Z2)) ∈ Ideal.henselianRadical (Z2 × Z2) ∧
    ¬ IsNilpotent ((2 : Z2), (2 : Z2)) := by
  have hm : (2 : Z2) ∈ twoIdeal := two_radical_eq ▸ two_mem_radical
  have hp : ((2 : Z2), (2 : Z2)) ∈ Ideal.henselianRadical (Z2 × Z2) := by
    rw [two_prod_radical_eq, Ideal.mem_prod]
    exact ⟨hm, hm⟩
  refine ⟨?_, ?_, hp, ?_⟩
  · intro h
    exact two_ne_zero (congrArg Prod.fst (Ideal.mem_bot.mp (h ▸ hp)))
  · intro h
    exact (Ideal.IsMaximal.ne_top (inferInstance : twoIdeal.IsMaximal))
      (Ideal.prod_eq_top_iff.mp (two_prod_radical_eq.symm.trans h)).1
  · intro h
    exact two_ne_zero (h.map (RingHom.fst Z2 Z2)).eq_zero

-- The product interfaces are exercised after the independent model.
example : HenselianRing (Z2 × Z2) (twoIdeal.prod twoIdeal) :=
  HenselianRing.prod twoIdeal twoIdeal

example : HenselianRing (Z2 × Z2) (twoIdeal.prod twoIdeal) ↔
    HenselianRing Z2 twoIdeal ∧ HenselianRing Z2 twoIdeal :=
  HenselianRing.prod_iff twoIdeal twoIdeal

example : Ideal.henselianRadical (Bool → Z2) = Ideal.pi (fun _ => twoIdeal) := by
  simpa only [two_radical_eq] using Ideal.henselianRadical_pi (fun _ : Bool => Z2)

example : Ideal.henselianRadical (Z2 × Z2) = twoIdeal.prod twoIdeal := by
  simpa only [two_radical_eq] using Ideal.henselianRadical_prod Z2 Z2

#print axioms two_pi_radical_eq
#print axioms two_prod_radical_eq

end HenselianIdealResearch
