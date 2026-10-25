# adic-modules

Lean results on ideal-power torsion, adic completions, Hensel lifting, Witt vectors,
finite Chinese remainders and valuation rings, built on Lean and Mathlib.
See [results and models](docs/Results.md) and the [usage guide](docs/Guide.md).

## Headline results

- For an arbitrary dependent family of commutative rings and ideals, the product
  pair is Henselian if and only if every component pair is Henselian.
  [`HenselianRing.pi` and `HenselianRing.pi_iff`](AdicModules/RingTheory/HenselianPi.lean)
  provide the construction instance and characterization, with independent index
  and ring universes, including empty products and trivial rings. For binary
  products, `HenselianRing.prod` and `HenselianRing.prod_iff` give
  `HenselianRing (R × S) (I.prod J) ↔ HenselianRing R I ∧ HenselianRing S J`
  for arbitrary ideals in independently universed commutative rings.
  For an arbitrary ideal in a possibly infinite product, `HenselianRing.pi_iff_map`
  characterizes Henselianity by its coordinate-image ideals. The binary form
  `HenselianRing.prod_iff_map` also permits independent universes.

Rings are commutative; modules are additive commutative groups unless specified otherwise.

- **Completion and completeness** ([functor](AdicModules/AdicCompletion/Functor.lean),
  [completeness](AdicModules/AdicCompletion/Completeness.lean)): completion at any ideal
  is an additive, `R`-linear functor to modules over the completed ring. Precompleteness
  for arbitrary `I,J` implies it for `I ⊔ J`. On an `I`-adically complete module,
  endomorphisms congruent to the identity modulo `I • ⊤` are units
  ([criterion](AdicModules/AdicCompletion/Endomorphism.lean)).
- **Cofinal ideal powers** ([API](AdicModules/AdicCompletion/ChangeIdeal.lean), [integer
  model](AdicModulesTest/CofinalAdicCompletion.lean)): for arbitrary ideals and modules,
  the original-`R`-linear `mapOfPowLE` uses `∃ a : ℕ, I^a ≤ J`, including zero; mutual
  power containment gives `equivOfCofinal
  : AdicCompletion I M ≃ₗ[R] AdicCompletion J M`. No finite generation, Noetherianity or
  completeness is required. Evaluation on every admissible stage pair `I^m ≤ J^n` is the
  canonical quotient factor, on arbitrary completed inputs, independently of witnesses. The maps
  preserve `of`, have identity/composition laws and are natural in original `R`-linear maps; the
  reverse comparison supplies both inverse laws. The inclusion API is `mapOfLE`, `mapOfLE_eval`,
  `mapOfLE_of`, `mapOfLE_id`, `mapOfLE_comp`, `mapOfLE_natural`; `mapOfPowLE_eq_mapOfLE`
  identifies every power witness with that map on arbitrary inputs. `powEquiv` requires **`0 <
  k`**; its forward/inverse every-admissible-stage evaluations, `of` and naturality laws,
  explicit ideal-equality quotient transport and agreement with cofinal comparison are included.
  Naturality uses distinct completed-`I` and completed-`J` scalar rings, not a common completed
  ring. The model keeps the same original `ℤ` self-module and distinct proper nonnilpotent
  ideals `(2)=span{2}`, `(4)=span{4}`: stage `0` is zero; class `1` is nonzero at stages `1,2`,
  modulo `(2),(4)` and `(4),(16)` respectively. It gives explicit quotient transport,
  evaluation, `of`, both inverses, `timesThree` naturality and positive-power agreement, using
  the original quotient modules throughout.
- **Products, maps and quotients** ([products](AdicModules/AdicCompletion/Pi.lean),
  [maps](AdicModules/AdicCompletion/LinearMap.lean)): `I.FG` gives the canonical
  completed-ring-linear equivalence for arbitrary dependent products. Any ideal admits
  map extension to complete targets; `I.FG` gives uniqueness for Hausdorff targets
  and a Hom equivalence for complete targets.
  Finite generation of **only `I^n`** gives evaluation kernel `(I^n) • ⊤` and
  `C / (I.map (algebraMap R C))^n ≃ₐ[R] R / I^n`, for `C = AdicCompletion I R`,
  including zero precision ([kernels](AdicModules/AdicCompletion/Kernel.lean), [quotients](AdicModules/AdicCompletion/Quotient.lean)).
- **Tensor comparisons and finiteness** ([tensor](AdicModules/AdicCompletion/TensorProduct.lean),
  [finite presentation](AdicModules/AdicCompletion/FinitePresentation.lean)): the canonical
  completed-ring-linear comparison is injective for projective modules; it is an
  equivalence for finite projective modules, finite modules over Noetherian rings,
  or finitely presented modules with **finite-free induced/intrinsic cofinality**
  (supplied by Artin–Rees over Noetherian rings). Any finite module completes to a
  finite module over the **same canonical completed ring**; finite projective modules
  remain projective there, so the generic finite-projective finite-presentation lemma applies.
- **Coordinates and scalar restriction** ([coordinates](AdicModules/AdicCompletion/QuotientTorsion.lean),
  [restriction](AdicModules/AdicCompletion/RestrictScalars.lean)): for an additive commutative group `V`, subgroup
  `L` and integer `ℓ` acting bijectively on `V`, compatible `ℓ^n`-kernel sections on
  `V/L` identify linearly with `(ℓ)`-adic completion of `L`, via `[v] ↦ [ℓ^n • v]`
  with a sign twist for negative `ℓ`. For an `R`-algebra `S` and compatible module
  actions and scalar tower, completion at the mapped ideal agrees **`R`-linearly**
  with completion at `I`, without finiteness, flatness, separation or completeness.
- **Adic topology and compactness** ([module maps](AdicModules/Topology/Algebra/Module/AdicTopology.lean),
  [algebra topology](AdicModules/Topology/Algebra/AdicTopology.lean)): module and mapped-ideal
  topologies agree. Semilinear maps are continuous for `I.map φ ≤ J`, open if surjective
  and `J ≤ I.map φ`, and open quotient maps if surjective with equality. For `I.FG`,
  evaluation kernels give a neighborhood basis. The abstract completion package assumes
  a compatible uniform additive group, `IsAdic I` and `I.FG`.
  For a given compatible left additive-group uniformity with `IsAdic I`, compactness
  holds iff uniform completeness and finite `R / I^n` for all `n`; under `I.FG`, just finite
  `R / I` ([compactness](AdicModules/Topology/Algebra/AdicCompactness.lean)). For every ideal,
  level-one projection detects units and has Jacobson kernel; local residue makes
  completion local ([local structure](AdicModules/AdicCompletion/LocalRing.lean)). For prime `p`,
  integer `(p)`-adic completion is canonically `ℤ`-algebra isomorphic and homeomorphic
  to usual `ℤ_[p]` ([comparison](AdicModules/AdicCompletion/PadicIntTopology.lean)).
- **Congruences and Hensel lifting** ([congruences](AdicModules/LinearAlgebra/SModEq/Pow.lean),
  [evaluation](AdicModules/Polynomial/Evaluation.lean), [Hensel](AdicModules/Polynomial/Hensel.lean)):
  `(q : R) ∈ I` and `x ≡ y [SMOD I^m]`, **`m > 0`**, give precision `I^(m+n)`
  after raising to `q^n`. If `I ≤ Ideal.jacobson ⊥`, displacement in
  `Ideal.span {g.eval a} * I` preserves polynomial values up to association.
  Coprime monic residue factors of monic polynomials lift with both reductions over
  any Henselian pair or adically complete ring. Over Henselian pairs, simple residue
  roots lift for arbitrary polynomials. With `d = f.derivative.eval a`, the condition
  `f.eval a ∈ Ideal.span {d^2} * I` gives a root `b` with `b-a ∈ Ideal.span {d} * I`
  and `Associated (f.eval a) (d * (b-a))`, even for zero or nonunit `d`. At a maximal
  ideal, **global** coprime monic factor lifting makes monic irreducibles reduce to
  positive powers of monic irreducibles; adic completeness supplies that global property.
  On principal units of a Henselian pair, the `n`-th power map is bijective if `n` is
  a residue unit. For `I`-adically complete rings, prime `p` with `(p : R) ∈ I` gives canonical
  `ℤ_[p]`-powers that are jointly continuous for an `I`-adic topology
  ([principal units](AdicModules/Topology/Algebra/PrincipalUnits.lean)).
- **Uniqueness and idempotents** ([factors](AdicModules/Polynomial/Hensel.lean),
  [roots](AdicModules/Polynomial/RootUniqueness.lean), [idempotents](AdicModules/RingTheory/Idempotents.lean)):
  for a unit-reflecting ring map, `g*h = g'*h'`, monic `g,g'`, equal left-factor images
  and coprime images of `g,h` force equality of both factors, without right monicity
  or completeness. For a map from a commutative ring to any semiring, unit reflection,
  equal root images and a unit derivative image force root equality. Over a Henselian
  pair `(R,I)`, idempotents lift uniquely modulo the mapped ideal in **every given
  module-finite commutative `R`-algebra**, including `R` itself.

- **Henselian-pair criterion via finite algebras.** For any commutative ring
  `R : Type u` and ideal `I`, `HenselianRing R I` holds if and only if, for
  **every given** `B : Type (max u v)` with `[CommRing B]`, `[Algebra R B]`
  and `[Module.Finite R B]`, every idempotent
  `e0 : B ⧸ I.map (algebraMap R B)` has a unique idempotent lift `e : B`
  with `Ideal.Quotient.mk (I.map (algebraMap R B)) e = e0`.
  The lift belongs to the original algebra, with exactly the prescribed quotient
  image; `u` and `v` are independent. No locality, completeness, finite-free or
  projective algebra assumption is required. See the
  [finite-algebra criterion](AdicModules/RingTheory/HenselianCriterion.lean).
- **Radical invariance of Henselian pairs.** For any commutative ring `R` and ideal
  `I`, `HenselianRing R I ↔ HenselianRing R I.radical`. No uniform nilpotence exponent
  or finiteness condition on the ring or ideal is needed. See
  [`HenselianRing.iff_radical`](AdicModules/RingTheory/HenselianRadical.lean).

<a id="reduced-residue-teichmüller-image"></a>

- **Frobenius limits and Teichmüller maps** ([limits](AdicModules/RingTheory/Perfection.lean),
  [cores](AdicModules/RingTheory/FrobeniusCore.lean), [sections](AdicModules/RingTheory/Teichmuller.lean)):
  inverse-Frobenius limits of prime-characteristic fields are fields. In reduced rings
  of exponential characteristic (including one), iterated Frobenius ranges intersect
  in the largest perfect subring (subfield for fields). Surjective maps to perfect
  characteristic-`p` rings from kernel-adically complete rings have unique multiplicative
  zero-and-one sections for prime `p`, additive if the source has characteristic `p`.
  Their image is the intersection of `p^n`-power ranges. For complete rings with **reduced**
  characteristic-`p` residue, the injective Teichmüller map from residue perfection has
  the same image, including zero and independent roots at every depth. For valuation
  domains at a **maximal** ideal, this also holds in any specified fraction field,
  without perfect/finite residue ([ring](docs/Results.md#reduced-residue-teichmüller-image),
  [field](AdicModules/RingTheory/TeichmullerFractionField.lean)).
- **Witt vectors** ([criteria](AdicModules/RingTheory/WittVector.lean),
  [integer torsion](AdicModules/RingTheory/WittVector/Torsion.lean)): for prime `p`,
  Witt vectors over any characteristic-`p` ring have characteristic zero; units are
  detected by the constant coefficient, and locality is equivalent to coefficient-ring locality.
  Multiplication by `p^n` has kernel `∀ i, x.coeff i ^ (p^n) = 0`, including `n = 0`;
  regularity of `p` and integer torsion-freeness each characterize reduced coefficients.
  Witt reducedness itself is equivalent to coefficient reducedness **without** a
  characteristic hypothesis. Over reduced characteristic-`p` rings, Teichmüller digit
  expansions are unique. For arbitrary coefficients, Witt domainhood is equivalent to
  domainhood **and** characteristic `p`; the DVR condition (with a bound domain proof)
  is equivalent to perfect field coefficients of characteristic `p`
  ([domain](AdicModules/RingTheory/WittVector/Domain.lean), [DVR](AdicModules/RingTheory/WittVector/DiscreteValuationRing.lean)).
  In characteristic `p`, Witt Frobenius is bijective iff coefficients are perfect
  ([Frobenius](AdicModules/RingTheory/WittVector/Frobenius.lean)); Witt vectors are Hausdorff
  and complete for `(p)`. Membership in `(p)^n` means a zero prefix of length `n`
  **and independent `p^n`-th roots of every remaining coefficient**, without perfectness
  or reducedness. The constant-coefficient kernel is `(p)` iff Frobenius is surjective;
  `(p)` is prime iff coefficients are a domain with surjective Frobenius. A zero prefix
  alone is insufficient over nonperfect rings ([ideals](AdicModules/RingTheory/WittVector/Complete.lean)).
- **Torsion, spans, closure and CRT** ([torsion](AdicModules/BoundedIdealPowerTorsion.lean),
  [primary exactness](AdicModules/PrimaryComponent.lean), [spans and closure](docs/Results.md#headline-results)):
  for finite modules, uniform ideal-power annihilation iff the primary component is top.
  Submodule/image laws also hold for commutative semirings and additive commutative monoids;
  quotient/extension laws retain ring/group hypotheses. Over Dedekind domains, height-one
  primary components preserve exact pairs with torsion **source**; abelian groups use
  restricted `p`-primary maps. In a `NonAssocRing`, a top integer singleton span forces
  surjective integer casts. Semilinear kernel pullbacks give `comap f (map f N) = N ⊔ ker f`
  for additive commutative group sources, additive commutative monoid targets and surjective
  scalar maps. Over semirings, closure is the intersection of `N ⊔ U` for a given
  topological additive group, continuous
  fixed-scalar maps and a submodule zero-neighborhood basis. Dense-subsemiring span closures
  agree for additive commutative monoid modules with separately continuous addition
  and coefficient continuity at the generators. Comaximal ideal actions commute with
  intersections over commutative
  semirings, with a cap with `N` for empty finite selections. Arbitrary semiring left
  ideals stay comaximal under independent powers. In a given additive-group powers
  topology, `Dense J ↔ J ⊔ I = ⊤`. P-adic unit integer spans are dense, but all singleton
  integer spans are proper. Finite-family ring CRT needs a finite index type, pairwise comaximality
  and **all-family two-sidedness**, including zero powers; uniqueness is of quotient classes
  ([CRT](AdicModules/RingTheory/Ideal/Quotient/Finite.lean)). Scalar-ideal algebra quotients retain
  quotient module actions even for noncommutative algebras ([quotients](AdicModules/RingTheory/Ideal/Quotient/SMulTop.lean)).
- **Valuation completions** ([completeness](AdicModules/Valuation/Completeness.lean),
  [integers](AdicModules/CompletedIntegers.lean), [localization](AdicModules/LocalizedCompletion.lean)):
  for valuation integers, nonzero generator and separated principal powers give adic
  completeness iff completeness for the **given valuation uniformity**; the field-to-ring
  direction includes zero generators. For valuation domains, nonzero generator and
  separated powers identify the inverse limit with completed valuation integers;
  nonfield, faithful-flatness and spectrum laws also need the generator in the maximal
  ideal. Radical-disjoint denominators give base-power images between successive extended
  powers, not equality; with the same nonzero/separation hypotheses they give localized
  embeddings and residue comparison. At a nonzero prime, separation supplies radical-disjointness.
  Completed integers literally equal the residue-preimage composite of completed localization
  and transported residue factor ([composites](AdicModules/CompletedValuationComposite.lean)).

- **Transport of Henselian pairs.** For independently universed commutative
  rings and an integral homomorphism `f : R →+* S`,
  `HenselianRing.map_of_isIntegral` sends a Henselian pair `(R, I)` to
  `(S, I.map f)`, without a finiteness or locality assumption on the target.
  Integral faithfully flat maps also reflect Henselianity:
  `HenselianRing.iff_map_of_isIntegral_of_faithfullyFlat` gives
  `HenselianRing R I ↔ HenselianRing S (I.map f)`.
  Surjective maps are included via `HenselianRing.map_of_surjective`.
  If a surjection's kernel defines a Henselian pair over `R`,
  `HenselianRing.iff_map_of_surjective_of_henselian_ker` gives the same
  equivalence for every source ideal, without requiring it to contain the kernel.
  Elementwise-nil kernels are a special case, retained as
  `HenselianRing.iff_map_of_surjective_of_nil_ker`; no uniform nilpotence
  exponent or Noetherian assumption is required.
  Moreover, every subideal of a Henselian ideal is Henselian
  (`HenselianRing.of_le`).
  Henselian ideals also contract along integral faithfully flat maps.
  See [`HenselianTransport`](AdicModules/RingTheory/HenselianTransport.lean).
- The Henselian ideals of any commutative ring are closed under arbitrary suprema,
  including the empty supremum. Their greatest element `Ideal.henselianRadical R`
  is radical, contains the nilradical, and lies in the Jacobson radical. An ideal
  is Henselian exactly when it lies below this greatest ideal. Comap along a
  surjective ring homomorphism recovers the source's greatest Henselian ideal
  when the kernel is Henselian.
  See [`HenselianIdeal`](AdicModules/RingTheory/HenselianIdeal.lean).
  The greatest Henselian ideal is componentwise for arbitrary dependent products,
  including empty products, and for binary products of independently universed rings:
  `Ideal.henselianRadical (∀ i, R i) = Ideal.pi (fun i => Ideal.henselianRadical (R i))`
  and `Ideal.henselianRadical (R × S) = (Ideal.henselianRadical R).prod (Ideal.henselianRadical S)`.
  See [`Ideal.henselianRadical_pi` and `Ideal.henselianRadical_prod`](AdicModules/RingTheory/HenselianPi.lean).

## Using the library

Add a dependency to your project's `lakefile.toml`:

```toml
[[require]]
name = "adic-modules"
git = "https://github.com/FormalFrontier/adic-modules.git"
rev = "main"
```

GitHub `main` contains only reviewed releases. Lake resolves it when you first add
or update the dependency; your project's `lake-manifest.json` records that commit.
For an explicit version, replace `main` with a full release commit from its history.
Use the Lean toolchain of the selected release; libraries used together must share
a Mathlib revision.

Then `import AdicModules`, or choose an individual module from the table below.

From a [build-checked test module](AdicModulesTest/RingTheory/WittVector/Domain.lean),
not checked separately as a standalone snippet, this rules out a Witt-vector domain
over the zero ring:

```lean
module
public import AdicModules.RingTheory.WittVector.Domain
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section
namespace WittVector
private theorem zero_ring_not_domain : ¬ IsDomain (WittVector 3 (ZMod 1)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hWitt
  letI : IsDomain (ZMod 1) := ((isDomain_iff 3 (ZMod 1)).mp hWitt).1
  exact (one_ne_zero : (1 : ZMod 1) ≠ 0) (Subsingleton.elim _ _)
end WittVector
```

<a id="build-and-reference"></a>
## Building

With the pinned [toolchain](lean-toolchain), [manifest](lake-manifest.json) and matching cache:

```sh
lake exe cache get
lake build AdicModules AdicModulesTest
```

Do not silently rebuild Mathlib; see [cache/resource caveats](docs/Guide.md#reproduction-and-resources).

<a id="imports-and-module-map"></a>
## Contents

The public root is `AdicModules`; narrower leaves and related tests are below.
Test modules require separate imports and are not re-exported by the root.

| Library leaf (prefix `AdicModules.`) | Related modules (prefix `AdicModulesTest.`) |
| --- | --- |
| [BoundedIdealPowerTorsion](AdicModules/BoundedIdealPowerTorsion.lean) | [BoundedIdealPowerTorsion](AdicModulesTest/BoundedIdealPowerTorsion.lean) |
| [Polynomial.Coprime](AdicModules/Polynomial/Coprime.lean) | [Polynomial.FactorizationUniqueness](AdicModulesTest/Polynomial/FactorizationUniqueness.lean) (monic coprimeness criterion and factor uniqueness) |
| [Polynomial.Hensel](AdicModules/Polynomial/Hensel.lean) | [Polynomial.Hensel](AdicModulesTest/Polynomial/Hensel.lean), [Polynomial.FactorizationUniqueness](AdicModulesTest/Polynomial/FactorizationUniqueness.lean) (nonlocal power series, zero ring and product-projection boundary) |
| [Polynomial.Evaluation](AdicModules/Polynomial/Evaluation.lean) | [Polynomial.Evaluation](AdicModulesTest/Polynomial/Evaluation.lean) (derivative application, nonunit 3-adic derivative and zero boundary) |
| [Polynomial.RootUniqueness](AdicModules/Polynomial/RootUniqueness.lean) | [Polynomial.RootUniqueness](AdicModulesTest/Polynomial/RootUniqueness.lean) |
| [RingTheory.HenselianCriterion](AdicModules/RingTheory/HenselianCriterion.lean) | [RingTheory.HenselianCriterion](AdicModulesTest/RingTheory/HenselianCriterion.lean) |
| [RingTheory.Teichmuller](AdicModules/RingTheory/Teichmuller.lean) | [RingTheory.Teichmuller](AdicModulesTest/RingTheory/Teichmuller.lean) (usual normed 3-adic integers and perfect-field power series, with infinite residue fields) |
| [RingTheory.TeichmullerFractionField](AdicModules/RingTheory/TeichmullerFractionField.lean) | [RingTheory.TeichmullerFractionFieldModel](AdicModulesTest/RingTheory/TeichmullerFractionFieldModel.lean) (usual 3-adics; a power-series fraction field with imperfect infinite residue field) |
| [RingTheory.Perfection](AdicModules/RingTheory/Perfection.lean) | [RingTheory.TeichmullerCore](AdicModulesTest/RingTheory/TeichmullerCore.lean) (imperfect Laurent-series field, prime-field unit and zero boundaries) |
| [RingTheory.FrobeniusCore](AdicModules/RingTheory/FrobeniusCore.lean) | [RingTheory.FrobeniusCore](AdicModulesTest/RingTheory/FrobeniusCore.lean) (imperfect Laurent-series field, universal property, characteristic-one and reduced-product boundaries) |
| [RingTheory.WittVector](AdicModules/RingTheory/WittVector.lean) | [RingTheory.WittVector](AdicModulesTest/RingTheory/WittVector.lean) (nonzero casts of `3` over `ZMod 3` and `(ZMod 3)[X]`; reducedness over `ℤ × ZMod 2`, nonreduced `ZMod 4`, and the zero ring `ZMod 1`; injective multiplication by `3` over the reduced nonperfect `Polynomial (ZMod 3) × ZMod 3` with nonzero zero divisors; nonzero Teichmüller torsion killed by `3` and the coefficientwise kernel criterion over `TrivSqZeroExt (ZMod 3) (ZMod 3)`; the nonzero nonunit `2` over `ZMod 2`, units and nonunits over the local nonfield `PowerSeries (ZMod 2)` with nonsquare `X`, and the nonlocal product `ZMod 2 × ZMod 2`) |
| [RingTheory.WittVector.Complete](AdicModules/RingTheory/WittVector/Complete.lean) | [RingTheory.WittVector.Complete](AdicModulesTest/RingTheory/WittVector/Complete.lean) (prime-field, product and nonperfect polynomial coefficients, independent roots and zero precision; prime-field and nonperfect polynomial coefficients, independent roots and zero precision) |
| [RingTheory.WittVector.Domain](AdicModules/RingTheory/WittVector/Domain.lean) | [RingTheory.WittVector.Domain](AdicModulesTest/RingTheory/WittVector/Domain.lean) (imperfect polynomial domain, characteristic-zero integers and zero-ring boundary) |
| [RingTheory.WittVector.Torsion](AdicModules/RingTheory/WittVector/Torsion.lean) | [RingTheory.WittVector.Torsion](AdicModulesTest/RingTheory/WittVector/Torsion.lean) (reduced non-domain product and dual-number integer torsion) |
| [RingTheory.WittVector.Frobenius](AdicModules/RingTheory/WittVector/Frobenius.lean) | [WittVector.Frobenius](AdicModulesTest/WittVector/Frobenius.lean) (perfect non-domain product and nonperfect dual numbers) |
| [PrimaryComponent](AdicModules/PrimaryComponent.lean) | [PrimaryComponent](AdicModulesTest/PrimaryComponent.lean) |
| [AdicCompletion](AdicModules/AdicCompletion.lean) | [AdicCompletion](AdicModulesTest/AdicCompletion.lean) |
| [AdicCompletion.Functor](AdicModules/AdicCompletion/Functor.lean) | [AdicCompletion.Functor](AdicModulesTest/AdicCompletion/Functor.lean) (completed product inclusion and its nonzero integer boundary) |
| [AdicCompletion.ChangeIdeal](AdicModules/AdicCompletion/ChangeIdeal.lean) (cofinal ideal powers over the original ring) | [CofinalAdicCompletion](AdicModulesTest/CofinalAdicCompletion.lean) (one original `ℤ`-module with ideals `(2)` and `(4)`, nonzero first two positive quotient stages and zero level `0`) |
| [AdicCompletion.Completeness](AdicModules/AdicCompletion/Completeness.lean) | [AdicCompletion.CompletenessTheorems](AdicModulesTest/AdicCompletion/CompletenessTheorems.lean) |
| [AdicCompletion.Endomorphism](AdicModules/AdicCompletion/Endomorphism.lean) | [IdentityCongruence](AdicModulesTest/IdentityCongruence.lean) (private nonscalar `ZMod 4` shear and criterion application) |
| [AdicCompletion.Kernel](AdicModules/AdicCompletion/Kernel.lean) | [AdicCompletionKernel](AdicModulesTest/AdicCompletionKernel.lean) (private integer `(2)` kernel calibration, degree-zero boundary, finite-generation recovery and separate fixed-power use) |
| [AdicCompletion.LinearMap](AdicModules/AdicCompletion/LinearMap.lean) | [AdicCompletion.LinearMap](AdicModulesTest/AdicCompletion/LinearMap.lean) (independent nonzero integer `(2)`-adic map from `ℕ →₀ ℤ`) |
| [AdicCompletion.Quotient](AdicModules/AdicCompletion/Quotient.lean) | [AdicCompletionQuotient](AdicModulesTest/AdicCompletionQuotient.lean) (integer `(2)` completion quotient, `ZMod 2`, inverse formulas and degree zero) |
| [AdicCompletion.RestrictScalars](AdicModules/AdicCompletion/RestrictScalars.lean) | [AdicCompletion.RestrictScalars](AdicModulesTest/AdicCompletion/RestrictScalars.lean) |
| [AdicCompletion.LocalRing](AdicModules/AdicCompletion/LocalRing.lean) | [AdicCompletion.LocalRing](AdicModulesTest/AdicCompletion/LocalRing.lean) |
| [AdicCompletion.PadicInt](AdicModules/AdicCompletion/PadicInt.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) |
| [AdicCompletion.PadicIntTopology](AdicModules/AdicCompletion/PadicIntTopology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (proper open mod-four kernel and its image) |
| [AdicCompletion.Pi](AdicModules/AdicCompletion/Pi.lean) (algebraic arbitrary-product equivalence for `I.FG`; naturality for every ideal) | [AdicCompletionPi](AdicModulesTest/AdicCompletionPi.lean) (full `ℕ → ZMod 4` model for `I = Ideal.span {2}`, a nonzero proper square-zero ideal; empty-product boundary) and [AdicCompletion.DependentPi](AdicModulesTest/AdicCompletion/DependentPi.lean) (private generic `Prop` contracts and a nonzero `ℕ → ℤ` model, not a universal bijectivity proof) |
| Separate completeness contract/model file | [AdicCompletion.Completeness](AdicModulesTest/AdicCompletion/Completeness.lean) (three proposition `#check`s and completeness/boundary models) |
| [AdicCompletion.Topology](AdicModules/AdicCompletion/Topology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (evaluation-kernel basis application) |
| [AdicCompletion.QuotientTorsion](AdicModules/AdicCompletion/QuotientTorsion.lean) | [ScalarTorsionSections](AdicModulesTest/ScalarTorsionSections.lean) |
| [AdicCompletion.TensorProduct](AdicModules/AdicCompletion/TensorProduct.lean) | [AdicCompletion.TensorProduct](AdicModulesTest/AdicCompletion/TensorProduct.lean) (finite-projective comparison and non-finite countable Finsupp injectivity) |
| [Algebra.Module.Int](AdicModules/Algebra/Module/Int.lean) | [Algebra.Module.Int](AdicModulesTest/Algebra/Module/Int.lean) |
| [LinearAlgebra.Pi](AdicModules/LinearAlgebra/Pi.lean) (finitely generated ideal action on dependent products and coordinatewise reduction kernel) | See the `AdicCompletion.DependentPi` models above |
| [LinearAlgebra.Span.Basic](AdicModules/LinearAlgebra/Span/Basic.lean) | [KernelPullback](AdicModulesTest/KernelPullback.lean) |
| [LinearAlgebra.TensorProduct.Quotient](AdicModules/LinearAlgebra/TensorProduct/Quotient.lean) | [LinearAlgebra.TensorProduct.Quotient](AdicModulesTest/LinearAlgebra/TensorProduct/Quotient.lean) |
| [RingTheory.Ideal.IsPrincipalPowQuotient](AdicModules/RingTheory/Ideal/IsPrincipalPowQuotient.lean) (representatives and inverse formulas) | [RingTheory.Ideal.IsPrincipalPowQuotient](AdicModulesTest/RingTheory/Ideal/IsPrincipalPowQuotient.lean) (nonzero chosen-generator class for `(5)` in `ℤ`) |
| [RingTheory.Ideal.Operations](AdicModules/RingTheory/Ideal/Operations.lean) | [RingTheory.Ideal.Operations.MatrixNat](AdicModulesTest/RingTheory/Ideal/Operations/MatrixNat.lean) (independent original calculations; additional private comaximal-powers application) |
| [RingTheory.Ideal.Quotient.Finite](AdicModules/RingTheory/Ideal/Quotient/Finite.lean) | [RingTheory.Ideal.Quotient.Finite](AdicModulesTest/RingTheory/Ideal/Quotient/Finite.lean) (integer quotient and boundary calculations), [RingTheory.Ideal.Quotient.FiniteEquivalence](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteEquivalence.lean) (equivalence client), [RingTheory.Ideal.Quotient.FinitePowers](AdicModulesTest/RingTheory/Ideal/Quotient/FinitePowers.lean) (powers-surjectivity client), [RingTheory.Ideal.Quotient.FiniteInverse](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteInverse.lean) (inverse and representatives client), [RingTheory.Ideal.Quotient.FiniteLinear](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteLinear.lean) (linear definition and integer client), [RingTheory.Ideal.Quotient.FiniteReduction](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteReduction.lean) (precision-reduction client), [RingTheory.Ideal.Quotient.Matrix](AdicModulesTest/RingTheory/Ideal/Quotient/Matrix.lean) (two-sided matrix examples), [RingTheory.Ideal.Quotient.LeftIdeal](AdicModulesTest/RingTheory/Ideal/Quotient/LeftIdeal.lean) (left-ideal counterexample) |
| [RingTheory.Ideal.Quotient.SMulTop](AdicModules/RingTheory/Ideal/Quotient/SMulTop.lean) | [RingTheory.Ideal.Quotient.SMulTop](AdicModulesTest/RingTheory/Ideal/Quotient/SMulTop.lean) (noncommutative integer matrices at the bottom ideal, level one) |
| [Topology.Algebra.Ideal](AdicModules/Topology/Algebra/Ideal.lean) | [Topology.Algebra.Ideal.Int](AdicModulesTest/Topology/Algebra/Ideal/Int.lean), [Topology.Algebra.Ideal.Matrix](AdicModulesTest/Topology/Algebra/Ideal/Matrix.lean), [Topology.Algebra.Ideal.Boundary](AdicModulesTest/Topology/Algebra/Ideal/Boundary.lean) (independent original calculations; additional private density application in Int) |
| [Topology.Algebra.Module.AdicTopology](AdicModules/Topology/Algebra/Module/AdicTopology.lean) | [Topology.Algebra.Module.AdicTopology](AdicModulesTest/Topology/Algebra/Module/AdicTopology.lean) (integer-pair projection and quotient descent) |
| [Topology.Algebra.Submodule](AdicModules/Topology/Algebra/Submodule.lean) | [Topology.Algebra.SubmoduleClosure](AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean) |
| [Topology.Algebra.PadicInt](AdicModules/Topology/Algebra/PadicInt.lean) | [Topology.Algebra.PadicInt](AdicModulesTest/Topology/Algebra/PadicInt.lean) |
| [Topology.Algebra.AdicTopology](AdicModules/Topology/Algebra/AdicTopology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (module-to-mapped-ideal topology application) |
| [Topology.Algebra.AdicCompactness](AdicModules/Topology/Algebra/AdicCompactness.lean) | [Topology.Algebra.AdicCompactness](AdicModulesTest/Topology/Algebra/AdicCompactness.lean) (3-adic applications, complete discrete integers with infinite first quotient, and zero-ring/zeroth-power boundaries) |
| [Topology.Algebra.PrincipalUnits](AdicModules/Topology/Algebra/PrincipalUnits.lean) | [Topology.Algebra.PrincipalUnits](AdicModulesTest/Topology/Algebra/PrincipalUnits.lean) (`p`-adic integer, 2-torsion and `X`-adic power-series models); [Topology.Algebra.PrincipalUnits.Henselian](AdicModulesTest/Topology/Algebra/PrincipalUnits/Henselian.lean) (3-adic square roots, a `ZMod 9` nonunit-exponent boundary, bottom ideal and zero ring) |
| [Topology.Algebra.Module.Span](AdicModules/Topology/Algebra/Module/Span.lean) | [Topology.Algebra.Module.Span.Real](AdicModulesTest/Topology/Algebra/Module/Span/Real.lean), [Topology.Algebra.Module.Span.Discrete](AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean), [Topology.Algebra.Module.Span.PadicInt](AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean), [Topology.Algebra.Module.Span.Boundary](AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean), [Topology.Algebra.Module.Span.Indiscrete](AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean) (independent original calculations; additional private comparison application in Real) |
| [Valuation.Completeness](AdicModules/Valuation/Completeness.lean) | [Valuation.Completeness](AdicModulesTest/Valuation/Completeness.lean) (5-adic and discrete-valuation examples), [FractionFieldCompletenessPadicClient](AdicModulesTest/FractionFieldCompletenessPadicClient.lean) (3-adic maximal-ideal valuation), [FractionFieldCompletenessSeriesClient](AdicModulesTest/FractionFieldCompletenessSeriesClient.lean) (power/Laurent series over any field, with no coefficient topology) |
| [ValuationTopology](AdicModules/ValuationTopology.lean) | [ValuationTopology](AdicModulesTest/ValuationTopology.lean) |
| [CompletedIntegers](AdicModules/CompletedIntegers.lean) | [CompletedIntegers](AdicModulesTest/CompletedIntegers.lean) |
| [CompletedLocalStructure](AdicModules/CompletedLocalStructure.lean) | [CompletedLocalStructure](AdicModulesTest/CompletedLocalStructure.lean) |
| [PrincipalAdicSpectrum](AdicModules/PrincipalAdicSpectrum.lean) | [PrincipalAdicSpectrum](AdicModulesTest/PrincipalAdicSpectrum.lean) |
| [LocalizedFiltration](AdicModules/LocalizedFiltration.lean) | [LocalizedFiltration](AdicModulesTest/LocalizedFiltration.lean) |
| [LocalizedCompletion](AdicModules/LocalizedCompletion.lean) | [LocalizedCompletion](AdicModulesTest/LocalizedCompletion.lean) |
| [LocalizedValuationSubring](AdicModules/LocalizedValuationSubring.lean) | [LocalizedValuationSubring](AdicModulesTest/LocalizedValuationSubring.lean) |
| [LocalizedResidueField](AdicModules/LocalizedResidueField.lean) | [LocalizedResidueField](AdicModulesTest/LocalizedResidueField.lean) |
| [LocalizedQuotientValuationSubring](AdicModules/LocalizedQuotientValuationSubring.lean) | [LocalizedQuotientValuationSubring](AdicModulesTest/LocalizedQuotientValuationSubring.lean) |
| [CompositeValuationSubring](AdicModules/CompositeValuationSubring.lean) | [CompositeValuationSubring](AdicModulesTest/CompositeValuationSubring.lean) |
| [CompletedValuationComposite](AdicModules/CompletedValuationComposite.lean) | [CompletedValuationComposite](AdicModulesTest/CompletedValuationComposite.lean) |
| No library leaf; aggregate root import | [Axioms](AdicModulesTest/Axioms.lean) (import-only, not an axiom census) |

## Conventions and limitations

Universes are independent except the common-universe Mathlib finite-Noetherian comparison.
Scalar actions are canonical; scalar restriction is not tensor base change. No transported
topology is substituted; uniform and algebraic adic completeness are distinct.
[Scope limits](docs/Results.md#credits-references-and-scope) exclude general nonseparated
reduction, arbitrary-denominator localization and whole-source coverage/correspondence.
The [historical API](docs/API.md) and [generation notes](docs/README.md) cover 13 leaves,
28 modules and 103 display sites, not the current library; use current signatures.
Ordinary builds and that output are not full transitive axiom assurance or proof replay.

## References

- I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, second edition (2002).
- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I* (2017),
  [arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5).
- [Detailed bibliography and result-specific credits](docs/Results.md#credits-references-and-scope).

<a id="credits-references-and-scope"></a>
## Credits and license

Authors: Formal Frontier Agents. Developed and reviewed by Formal Frontier AI agents;
not human peer review, source-author endorsement or complete source formalization.
Reuses [Lean](https://lean-lang.org/), [Mathlib](https://github.com/leanprover-community/mathlib4)
and [Group Theory](https://github.com/FormalFrontier/group-theory)'s scalar-torsion interface.
[Credits and provenance](docs/CREDITS.md) preserve project/adaptation authorship and
upstream notices; [detailed credits](docs/Results.md#credits-references-and-scope) include
the endomorphism and Witt-vector constructions. Licensed under [Apache-2.0](LICENSE).
