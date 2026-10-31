/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.ChangeIdealAlgebra
public import Mathlib.Algebra.Algebra.Tower

/-!
# Ring homomorphisms between adic completions

A ring homomorphism `f : R →+* T` with `I ≤ K.comap f` induces
`AdicCompletion.mapRingHom I K f h`. Its evaluation at every natural precision,
including zero, is the homomorphism between the original ideal-power quotients.
These maps preserve original elements, identities and composition, and agree
with `mapOfLEₐ` for inclusions of ideals in one ring.

For an `R`-algebra `T`, `extendedAlgebra` is the named opt-in algebra over
`AdicCompletion I R` on the stock ring `AdicCompletion (I.map (algebraMap R T)) T`.
It is exactly the algebra of the completed coefficient ring map, not a global
instance. Select it locally or pass it explicitly; the accompanying algebra-map
laws and named scalar-tower theorem refer to this value. Its original-`R` tower
agrees with the existing `R`-algebra structure on the target completion.

This construction does not replace an existing coefficient algebra. In particular,
put `A = AdicCompletion I R` and `J = I.map (algebraMap R A)`. The stock coefficient
`A`-algebra on `AdicCompletion J A` has map `of J A`, whereas `extendedAlgebra`
uses the completion of the original map `R → A`. These maps need not coincide
for arbitrary ideals.

## References

The construction uses Mathlib's `AdicCompletion.liftRingHom` and completed ring
structures, formalized by Judith Ludwig, Christian Merten and Jiedong Jiang,
and the ideal and quotient maps of Kenny Lau and Patrick Massot. It also uses
Mathlib's scalar-tower API. No intrinsic completeness or finite-generation
hypothesis is used.
-/

@[expose] public section

noncomputable section

universe u v w

namespace AdicCompletion

variable {R : Type u} {T : Type v} [CommRing R] [CommRing T]

private theorem mapRingHom_compatible (I : Ideal R) (K : Ideal T)
    (f : R →+* T) (h : I ≤ K.comap f) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow K hmn).comp
          ((Ideal.quotientMap (K ^ n) f
            ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n))).comp
              (evalₐ I n).toRingHom) =
        (Ideal.quotientMap (K ^ m) f
          ((Ideal.pow_right_mono h m).trans (Ideal.le_comap_pow f m))).comp
            (evalₐ I m).toRingHom := by
  intro m n hmn
  apply RingHom.ext
  intro a
  have ha : Ideal.Quotient.factorPow I hmn (evalₐ I n a) = evalₐ I m a := by
    induction a using AdicCompletion.induction_on with
    | _ a =>
      simpa only [evalₐ_mk, Ideal.Quotient.factor_mk] using Ideal.mk_eq_mk I hmn a
  change Ideal.Quotient.factorPow K hmn
      (Ideal.quotientMap (K ^ n) f
        ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n)) (evalₐ I n a)) =
    Ideal.quotientMap (K ^ m) f
      ((Ideal.pow_right_mono h m).trans (Ideal.le_comap_pow f m)) (evalₐ I m a)
  rw [← ha]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n a)
  rw [← hr]
  rfl

/-- A ring homomorphism sending `I` into `K` induces a ring homomorphism of
adic completions, using the maps on the original ideal-power quotients. -/
def mapRingHom (I : Ideal R) (K : Ideal T) (f : R →+* T) (h : I ≤ K.comap f) :
    AdicCompletion I R →+* AdicCompletion K T :=
  liftRingHom K
    (fun n ↦ (Ideal.quotientMap (K ^ n) f
      ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n))).comp
        (evalₐ I n).toRingHom)
    (by exact mapRingHom_compatible I K f h)

/-- Evaluation of the completed ring map is the induced quotient map, at every
precision, including zero. -/
@[simp]
theorem evalₐ_mapRingHom (I : Ideal R) (K : Ideal T) (f : R →+* T)
    (h : I ≤ K.comap f) (n : ℕ) (a : AdicCompletion I R) :
    evalₐ K n (mapRingHom I K f h a) =
      Ideal.quotientMap (K ^ n) f
        ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n)) (evalₐ I n a) :=
  evalₐ_liftRingHom K _ (mapRingHom_compatible I K f h) n a

/-- The evaluation square for the completed map, as an equality of ring maps. -/
@[simp]
theorem evalₐ_comp_mapRingHom (I : Ideal R) (K : Ideal T) (f : R →+* T)
    (h : I ≤ K.comap f) (n : ℕ) :
    (evalₐ K n : AdicCompletion K T →+* T ⧸ K ^ n).comp (mapRingHom I K f h) =
      (Ideal.quotientMap (K ^ n) f
        ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n))).comp
          (evalₐ I n).toRingHom := by
  apply RingHom.ext
  intro a
  exact evalₐ_mapRingHom I K f h n a

/-- The completed ring map sends the image of an original element to the image
of its value under the original ring map. -/
@[simp]
theorem mapRingHom_of (I : Ideal R) (K : Ideal T) (f : R →+* T)
    (h : I ≤ K.comap f) (r : R) :
    mapRingHom I K f h (of I R r) = of K T (f r) := by
  apply ext_evalₐ
  intro n
  simp only [evalₐ_mapRingHom, evalₐ_of, Ideal.quotientMap_mk]

/-- The evaluation squares uniquely determine the completed ring map. -/
theorem eq_mapRingHom (I : Ideal R) (K : Ideal T) (f : R →+* T)
    (h : I ≤ K.comap f) (g : AdicCompletion I R →+* AdicCompletion K T)
    (hg : ∀ (n : ℕ) (a : AdicCompletion I R),
      evalₐ K n (g a) = Ideal.quotientMap (K ^ n) f
        ((Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n)) (evalₐ I n a)) :
    g = mapRingHom I K f h := by
  apply RingHom.ext
  intro a
  apply ext_evalₐ
  intro n
  rw [evalₐ_mapRingHom]
  exact hg n a

/-- Completing the identity ring map gives the identity. -/
@[simp]
theorem mapRingHom_id (I : Ideal R) :
    mapRingHom I I (RingHom.id R) (by
      intro r hr
      exact hr) = RingHom.id (AdicCompletion I R) := by
  apply RingHom.ext
  intro a
  apply ext_evalₐ
  intro n
  simp only [RingHom.id_apply]
  rw [evalₐ_mapRingHom]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n a)
  rw [← hr]
  rfl

/-- Completed ring maps compose in the same order as the original ring maps. -/
theorem mapRingHom_comp {U : Type w} [CommRing U]
    (I : Ideal R) (K : Ideal T) (L : Ideal U) (f : R →+* T) (g : T →+* U)
    (hf : I ≤ K.comap f) (hg : K ≤ L.comap g) :
    (mapRingHom K L g hg).comp (mapRingHom I K f hf) =
      mapRingHom I L (g.comp f) (by
        intro r hr
        exact hg (hf hr)) := by
  apply RingHom.ext
  intro a
  apply ext_evalₐ
  intro n
  simp only [RingHom.comp_apply, evalₐ_mapRingHom]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n a)
  rw [← hr]
  rfl

/-- For the identity coefficient map, the construction agrees with the existing
inclusion-induced algebra map between completions. -/
theorem mapRingHom_id_eq_mapOfLEₐ {I K : Ideal R} (h : I ≤ K) :
    mapRingHom I K (RingHom.id R) (by
      intro r hr
      exact h hr) = (mapOfLEₐ R h).toRingHom := by
  apply RingHom.ext
  intro a
  apply ext_evalₐ
  intro n
  rw [evalₐ_mapRingHom]
  change _ = evalₐ K n (mapOfLEₐ R h a)
  rw [mapOfLEₐ_evalₐ]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n a)
  rw [← hr]
  rfl

section Algebra

variable [Algebra R T]

/-- The named opt-in algebra over the completed coefficient ring on the completion
of an algebra along the extended ideal. It is exactly the algebra of `mapRingHom`
and is not registered as a global instance. In particular, it need not agree with
an existing coefficient algebra when `T` is itself a completed ring. -/
@[instance_reducible]
def extendedAlgebra (I : Ideal R) :
    Algebra (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R T)) T) :=
  (mapRingHom I (I.map (algebraMap R T)) (algebraMap R T) Ideal.le_comap_map).toAlgebra

section ExtendedAlgebra

attribute [local instance] extendedAlgebra

/-- The algebra map for `extendedAlgebra` is precisely the completed coefficient
ring map. -/
theorem extendedAlgebra_algebraMap (I : Ideal R) :
    algebraMap (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R T)) T) =
      mapRingHom I (I.map (algebraMap R T)) (algebraMap R T) Ideal.le_comap_map :=
  rfl

/-- The completed coefficient algebra map on an arbitrary element. -/
@[simp]
theorem extendedAlgebra_algebraMap_apply (I : Ideal R) (a : AdicCompletion I R) :
    algebraMap (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R T)) T) a =
      mapRingHom I (I.map (algebraMap R T)) (algebraMap R T) Ideal.le_comap_map a :=
  rfl

/-- On original coefficients the completed algebra map agrees with the original
algebra map followed by completion. -/
theorem extendedAlgebra_algebraMap_of (I : Ideal R) (r : R) :
    algebraMap (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R T)) T)
        (of I R r) =
      of (I.map (algebraMap R T)) T (algebraMap R T r) :=
  mapRingHom_of I _ _ _ r

/-- Evaluation of the completed coefficient algebra map is the original
coefficient map on ideal-power quotients. -/
theorem evalₐ_extendedAlgebra_algebraMap (I : Ideal R) (n : ℕ)
    (a : AdicCompletion I R) :
    evalₐ (I.map (algebraMap R T)) n
        (algebraMap (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R T)) T) a) =
      Ideal.quotientMap ((I.map (algebraMap R T)) ^ n) (algebraMap R T)
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans
          (Ideal.le_comap_pow (algebraMap R T) n)) (evalₐ I n a) :=
  evalₐ_mapRingHom I _ _ _ n a

/-- The named completed coefficient algebra retains the original-`R` algebra
structure on the target completion. -/
theorem extendedAlgebra_isScalarTower (I : Ideal R) :
    IsScalarTower R (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R T)) T) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp only [extendedAlgebra_algebraMap_apply, algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mapRingHom_of]

end ExtendedAlgebra

end Algebra

end AdicCompletion
