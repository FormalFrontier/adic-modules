/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianIdeal
import Mathlib.NumberTheory.Padics.PadicIntegers
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

end HenselianIdealResearch
