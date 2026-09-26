# Generated API reference

This reference contains all 103 native library display sites: 75 theorems,
23 definitions and five instances. The root and fourteen test/audit modules
have no public display sites.
Import `AdicModules` for the library; the test-target modules are separate.
Private/generated proof declarations still require the separate complete audit.
Native display-site counts are not a complete kernel-declaration census.

Headers below are native doc-gen4 display signatures, not complete declarations
with proof bodies. All native visible tokens, including implicit parameters and
literal noncomputable modifiers, are retained; whitespace alone is normalized.
Native pretty-printing uses each source namespace, notation and type inference;
consult the linked source for suppressed inferred types and universe conventions.
These displayed fragments are not promised to elaborate alone in a fresh namespace.
Source links are relative to this same checkout.

The source/pin hashes and generation provenance are in [api-manifest.json](api-manifest.json).
See [generation instructions](README.md) and the [mathematical guide](Guide.md).
Where no source docstring exists, a separately authored **API note** is labeled explicitly.

## Complete module inventory

| Module | Display sites |
| --- | --- |
| `AdicModules.AdicCompletion` | 4 |
| `AdicModules.BoundedIdealPowerTorsion` | 10 |
| `AdicModules.CompletedIntegers` | 11 |
| `AdicModules.CompletedLocalStructure` | 10 |
| `AdicModules.CompletedValuationComposite` | 13 |
| `AdicModules.CompositeValuationSubring` | 18 |
| `AdicModules.LocalizedCompletion` | 8 |
| `AdicModules.LocalizedFiltration` | 8 |
| `AdicModules.LocalizedQuotientValuationSubring` | 4 |
| `AdicModules.LocalizedResidueField` | 2 |
| `AdicModules.LocalizedValuationSubring` | 4 |
| `AdicModules.PrincipalAdicSpectrum` | 7 |
| `AdicModules.ValuationTopology` | 4 |
| `AdicModules` | 0 |
| `AdicModulesTest.Axioms` | 0 |
| `AdicModulesTest.AdicCompletion` | 0 |
| `AdicModulesTest.BoundedIdealPowerTorsion` | 0 |
| `AdicModulesTest.CompletedIntegers` | 0 |
| `AdicModulesTest.CompletedLocalStructure` | 0 |
| `AdicModulesTest.CompletedValuationComposite` | 0 |
| `AdicModulesTest.CompositeValuationSubring` | 0 |
| `AdicModulesTest.LocalizedCompletion` | 0 |
| `AdicModulesTest.LocalizedFiltration` | 0 |
| `AdicModulesTest.LocalizedQuotientValuationSubring` | 0 |
| `AdicModulesTest.LocalizedResidueField` | 0 |
| `AdicModulesTest.LocalizedValuationSubring` | 0 |
| `AdicModulesTest.PrincipalAdicSpectrum` | 0 |
| `AdicModulesTest.ValuationTopology` | 0 |

Two generated equations have no native display site:
`Module.IsKilledByIdealPower.eq_1` and
`ValuationRing.localizedAdicCompletionResidueFieldEquiv.eq_1`.
They remain part of the separate raw-declaration proof inventory.

## AdicModules.AdicCompletion

Scope: library.

<a id="api-6e8e8b90ad48e55d"></a>

### AdicCompletion.abstractCompletion

```lean
noncomputable def AdicCompletion.abstractCompletion {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) : AbstractCompletion.{u, u} R
```

A finitely generated adic inverse limit, with the topology defined by the
image of the ideal, is a complete separated uniform-space completion of the
original ring with its adic topology.

[Source](../AdicModules/AdicCompletion.lean#L42-L103) (native source range).

<a id="api-c696e36ca7018e2d"></a>

### AdicCompletion.abstractCompletion_coe

```lean
theorem AdicCompletion.abstractCompletion_coe {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) : (abstractCompletion I hI hfg).coe = ⇑(algebraMap R (AdicCompletion I R))
```

**API note (not a source docstring):** The map underlying the abstract-completion package is exactly the canonical algebra map into the adic inverse limit, with the adic-topology and finite-generation hypotheses displayed above.

[Source](../AdicModules/AdicCompletion.lean#L105-L110) (native source range).

<a id="api-ac3ce79ccdf2aa01"></a>

### AdicCompletion.isUniformInducing_algebraMap

```lean
theorem AdicCompletion.isUniformInducing_algebraMap {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) : IsUniformInducing ⇑(algebraMap R (AdicCompletion I R))
```

The canonical map to a finitely generated adic inverse limit induces the original
uniform structure when that structure is adic.

[Source](../AdicModules/AdicCompletion.lean#L112-L122) (native source range).

<a id="api-422d40c77e5bf37e"></a>

### AdicCompletion.denseRange_algebraMap

```lean
theorem AdicCompletion.denseRange_algebraMap {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) : DenseRange ⇑(algebraMap R (AdicCompletion I R))
```

The canonical image is dense in a finitely generated adic inverse limit.

[Source](../AdicModules/AdicCompletion.lean#L124-L133) (native source range).

## AdicModules.BoundedIdealPowerTorsion

Scope: library.

<a id="api-89b535447cdff6e4"></a>

### Module.IsKilledByIdealPower

```lean
def Module.IsKilledByIdealPower (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M] (I : Ideal R) : Prop
```

`IsKilledByIdealPower R M I` means that one power of `I` annihilates the
whole module `M`.

[Source](../AdicModules/BoundedIdealPowerTorsion.lean#L28-L31) (native source range).

<a id="api-6d6d4b0f00f2dd1d"></a>

### Module.isKilledByIdealPower_iff_exists_pow_le_annihilator

```lean
theorem Module.isKilledByIdealPower_iff_exists_pow_le_annihilator (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M] (I : Ideal R) : IsKilledByIdealPower R M I ↔ ∃ (n : ℕ), I ^ n ≤ annihilator R M
```

A module is killed by a power of an ideal exactly when some ideal power is
contained in its annihilator.

[Source](../AdicModules/BoundedIdealPowerTorsion.lean#L33-L38) (native source range).

<a id="api-2ab0f83d1d7038b6"></a>

### Module.isTorsionBySet_ideal_pow_of_le

```lean
theorem Module.isTorsionBySet_ideal_pow_of_le (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M] (I : Ideal R) {n m : ℕ} (hnm : n ≤ m) (h : IsTorsionBySet R M ↑(I ^ n)) : IsTorsionBySet R M ↑(I ^ m)
```

Once a power of an ideal annihilates a module, every larger power does too.

[Source](../AdicModules/BoundedIdealPowerTorsion.lean#L40-L44) (native source range).

<a id="api-59bb779e5b2b833d"></a>

### Module.IsKilledByIdealPower.of_le

```lean
theorem Module.IsKilledByIdealPower.of_le {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {I J : Ideal R} (hI : IsKilledByIdealPower R M I) (hJI : J ≤ I) : IsKilledByIdealPower R M J
```

If a power of `I` annihilates a module, then a power of every smaller ideal
does as well.

[Source](../AdicModules/BoundedIdealPowerTorsion.lean#L48-L54) (native source range).

<a id="api-43044a707aa639c4"></a>

### Module.IsKilledByIdealPower.submodule

```lean
theorem Module.IsKilledByIdealPower.submodule {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {I : Ideal R} (h : IsKilledByIdealPower R M I) (N : Submodule R M) : IsKilledByIdealPower R (↥N) I
```

Every submodule of a module annihilated by an ideal power is annihilated by
the same ideal power.

[Source](../AdicModules/BoundedIdealPowerTorsion.lean#L56-L62) (native source range).

<a id="api-9ffece79ea423003"></a>

### Module.IsKilledByIdealPower.of_surjective

```lean
theorem Module.IsKilledByIdealPower.of_surjective {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Type w} [AddCommMonoid N] [Module R N] {I : Ideal R} (hM : IsKilledByIdealPower R M I) (f : M →ₗ[R] N) (hf : Function.Surjective ⇑f) : IsKilledByIdealPower R N I
```

Surjective linear images preserve annihilation by an ideal power.

[Source](../AdicModules/BoundedIdealPowerTorsion.lean#L64-L72) (native source range).

<a id="api-40eae4dd4383b713"></a>

### Module.isKilledByIdealPower_iff_primaryComponent_eq_top

```lean
theorem Module.isKilledByIdealPower_iff_primaryComponent_eq_top (R : Type u) (M : Type v) [CommRing R] [AddCommMonoid M] [Module R M] [Module.Finite R M] (I : Ideal R) : IsKilledByIdealPower R M I ↔ Ideal.primaryComponent M I = ⊤
```

On a finite module, elementwise annihilation by ideal powers is equivalent
to annihilation of the whole module by one uniform ideal power.

[Source](../AdicModules/BoundedIdealPowerTorsion.lean#L80-L103) (native source range).

<a id="api-95cca7b20a37a6d1"></a>

### Module.IsKilledByIdealPower.quotient

```lean
theorem Module.IsKilledByIdealPower.quotient {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] {I : Ideal R} (h : IsKilledByIdealPower R M I) (N : Submodule R M) : IsKilledByIdealPower R (M ⧸ N) I
```

Quotients of a module annihilated by an ideal power are annihilated by the
same ideal power.

[Source](../AdicModules/BoundedIdealPowerTorsion.lean#L113-L121) (native source range).

<a id="api-1fc54d3bbf69e6c7"></a>

### Module.isTorsionBySet_ideal_pow_extension

```lean
theorem Module.isTorsionBySet_ideal_pow_extension {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) {n m : ℕ} (hN : IsTorsionBySet R ↥N ↑(I ^ n)) (hQ : IsTorsionBySet R (M ⧸ N) ↑(I ^ m)) : IsTorsionBySet R M ↑(I ^ (n + m))
```

If `I ^ n` annihilates a submodule and `I ^ m` annihilates the quotient,
then `I ^ (n + m)` annihilates the whole module.

[Source](../AdicModules/BoundedIdealPowerTorsion.lean#L123-L142) (native source range).

<a id="api-900a03fb4e9b26ed"></a>

### Module.IsKilledByIdealPower.extension

```lean
theorem Module.IsKilledByIdealPower.extension {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hN : IsKilledByIdealPower R (↥N) I) (hQ : IsKilledByIdealPower R (M ⧸ N) I) : IsKilledByIdealPower R M I
```

An extension of modules annihilated by powers `I ^ n` and `I ^ m` is
annihilated by `I ^ (n + m)`.

[Source](../AdicModules/BoundedIdealPowerTorsion.lean#L144-L151) (native source range).

## AdicModules.CompletedIntegers

Scope: library.

<a id="api-2a27394468ac61d2"></a>

### ValuationRing.CompletionIntegers

```lean
noncomputable def ValuationRing.CompletionIntegers (V : Type u) (K : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] : Subring (UniformSpace.Completion K)
```

The valuation-integer subring in the completion of the fraction field of a valuation ring.

[Source](../AdicModules/CompletedIntegers.lean#L32-L39) (native source range).

<a id="api-a0f4e0e71fcc19eb"></a>

### ValuationRing.completionIntegersAlgebra

```lean
noncomputable instance ValuationRing.completionIntegersAlgebra {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] : Algebra V ↥(CompletionIntegers V K)
```

The canonical `V`-algebra structure on the completed valuation integers.

[Source](../AdicModules/CompletedIntegers.lean#L44-L52) (native source range).

<a id="api-5eaeaca2a54b23a2"></a>

### ValuationRing.algebraMap_completionIntegers_apply

```lean
theorem ValuationRing.algebraMap_completionIntegers_apply {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (x : ↥(CompletionIntegers V K)) : (algebraMap (↥(CompletionIntegers V K)) (UniformSpace.Completion K)) x = ↑x
```

The algebra map from the completed valuation integers to the completed fraction field is
the subring inclusion.

[Source](../AdicModules/CompletedIntegers.lean#L54-L60) (native source range).

<a id="api-70ee57f48f5354cd"></a>

### ValuationRing.coe_algebraMap_completionIntegers

```lean
theorem ValuationRing.coe_algebraMap_completionIntegers {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (x : V) : ↑((algebraMap V ↥(CompletionIntegers V K)) x) = (algebraMap K (UniformSpace.Completion K)) ((algebraMap V K) x)
```

The algebra map to the completed valuation integers is the composite through the fraction
field and its completion.

[Source](../AdicModules/CompletedIntegers.lean#L62-L71) (native source range).

<a id="api-4b08d486701af7c4"></a>

### ValuationRing.denseRange_algebraMap_completionIntegers

```lean
theorem ValuationRing.denseRange_algebraMap_completionIntegers {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] : DenseRange ⇑(algebraMap V ↥(CompletionIntegers V K))
```

The valuation ring has dense image in the completed valuation integers.

[Source](../AdicModules/CompletedIntegers.lean#L73-L88) (native source range).

<a id="api-2e4ddb96049f73a3"></a>

### ValuationRing.isUniformInducing_algebraMap_fractionRing

```lean
theorem ValuationRing.isUniformInducing_algebraMap_fractionRing {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] : IsUniformInducing ⇑(algebraMap V K)
```

The fraction-field embedding of a valuation ring induces the valuation uniformity on the
valuation ring.

[Source](../AdicModules/CompletedIntegers.lean#L90-L158) (native source range).

<a id="api-7b66a98226d7d885"></a>

### ValuationRing.completionIntegersAbstractCompletion

```lean
noncomputable def ValuationRing.completionIntegersAbstractCompletion {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] : AbstractCompletion.{v, u} V
```

The completed valuation integers are an abstract completion of the valuation ring.

[Source](../AdicModules/CompletedIntegers.lean#L160-L189) (native source range).

<a id="api-c48e1c1e861720bf"></a>

### ValuationRing.principalAdicCompletionRingEquiv

```lean
noncomputable def ValuationRing.principalAdicCompletionRingEquiv {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : AdicCompletion (Ideal.span {a}) V ≃+* ↥(CompletionIntegers V K)
```

The ring equivalence underlying `principalAdicCompletionEquiv`.

[Source](../AdicModules/CompletedIntegers.lean#L191-L265) (native source range).

<a id="api-53813c9e15999bcd"></a>

### ValuationRing.principalAdicCompletionRingEquiv_algebraMap

```lean
theorem ValuationRing.principalAdicCompletionRingEquiv_algebraMap {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : V) : (principalAdicCompletionRingEquiv a ha0) ((algebraMap V (AdicCompletion (Ideal.span {a}) V)) x) = (algebraMap V ↥(CompletionIntegers V K)) x
```

The underlying ring equivalence agrees with the canonical maps from the valuation ring.

[Source](../AdicModules/CompletedIntegers.lean#L267-L281) (native source range).

<a id="api-876654960142dbc5"></a>

### ValuationRing.principalAdicCompletionEquiv

```lean
noncomputable def ValuationRing.principalAdicCompletionEquiv {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : AdicCompletion (Ideal.span {a}) V ≃ₐ[V] ↥(CompletionIntegers V K)
```

A separated principal-adic completion of a valuation ring is canonically the
valuation-integer subring of the completion of its fraction field.

[Source](../AdicModules/CompletedIntegers.lean#L283-L289) (native source range).

<a id="api-41e40fda3a1c99db"></a>

### ValuationRing.principalAdicCompletionEquiv_algebraMap

```lean
theorem ValuationRing.principalAdicCompletionEquiv_algebraMap {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : V) : (principalAdicCompletionEquiv a ha0) ((algebraMap V (AdicCompletion (Ideal.span {a}) V)) x) = (algebraMap V ↥(CompletionIntegers V K)) x
```

The principal-adic comparison agrees with the canonical maps from the valuation ring.

[Source](../AdicModules/CompletedIntegers.lean#L291-L297) (native source range).

## AdicModules.CompletedLocalStructure

Scope: library.

<a id="api-db0bfce304a8cdf0"></a>

### ValuationRing.principalAdicCompletion_isDomain

```lean
theorem ValuationRing.principalAdicCompletion_isDomain {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : IsDomain (AdicCompletion (Ideal.span {a}) V)
```

A separated principal-adic completion of a valuation ring is a domain.

[Source](../AdicModules/CompletedLocalStructure.lean#L35-L41) (native source range).

<a id="api-5bfac63ecaa7272d"></a>

### ValuationRing.principalAdicCompletion_isValuationRing

```lean
theorem ValuationRing.principalAdicCompletion_isValuationRing {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : ValuationRing (AdicCompletion (Ideal.span {a}) V)
```

A separated principal-adic completion of a valuation ring is a valuation ring.

[Source](../AdicModules/CompletedLocalStructure.lean#L43-L58) (native source range).

<a id="api-12b6a71ca3815a2f"></a>

### ValuationRing.principalAdicCompletionFractionFieldAlgebra

```lean
noncomputable def ValuationRing.principalAdicCompletionFractionFieldAlgebra {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : Algebra (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K)
```

The algebra structure on the completed fraction field induced by the principal-adic
comparison and the inclusion of the completed valuation integers.

[Source](../AdicModules/CompletedLocalStructure.lean#L60-L69) (native source range).

<a id="api-bfbd6467d08d0e53"></a>

### ValuationRing.principalAdicCompletionFractionFieldAlgebra_algebraMap

```lean
theorem ValuationRing.principalAdicCompletionFractionFieldAlgebra_algebraMap {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : AdicCompletion (Ideal.span {a}) V) : (algebraMap (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K)) x = (algebraMap (↥(CompletionIntegers V K)) (UniformSpace.Completion K)) ((principalAdicCompletionRingEquiv a ha0) x)
```

The induced fraction-field algebra map is the principal-adic comparison followed by the
inclusion of the completed valuation integers.

[Source](../AdicModules/CompletedLocalStructure.lean#L71-L83) (native source range).

<a id="api-af5d258405ef25d4"></a>

### ValuationRing.principalAdicCompletionFractionFieldAlgebra_algebraMap_base

```lean
theorem ValuationRing.principalAdicCompletionFractionFieldAlgebra_algebraMap_base {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : V) : (algebraMap (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K)) ((algebraMap V (AdicCompletion (Ideal.span {a}) V)) x) = (algebraMap K (UniformSpace.Completion K)) ((algebraMap V K) x)
```

The induced fraction-field algebra map agrees with the original fraction-field embedding on
the valuation ring.

[Source](../AdicModules/CompletedLocalStructure.lean#L85-L100) (native source range).

<a id="api-18a2a5a496ce2537"></a>

### ValuationRing.principalAdicCompletion_isFractionRing

```lean
theorem ValuationRing.principalAdicCompletion_isFractionRing {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : IsFractionRing (AdicCompletion (Ideal.span {a}) V) (UniformSpace.Completion K)
```

The completion of the fraction field is a fraction field of the separated principal-adic
completion.

[Source](../AdicModules/CompletedLocalStructure.lean#L102-L117) (native source range).

<a id="api-5dedec56cc8e8206"></a>

### ValuationRing.principalAdicCompletion_maximalIdeal_eq_map

```lean
theorem ValuationRing.principalAdicCompletion_maximalIdeal_eq_map {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) [IsHausdorff (Ideal.span {a}) V] : IsLocalRing.maximalIdeal (AdicCompletion (Ideal.span {a}) V) = Ideal.map (algebraMap V (AdicCompletion (Ideal.span {a}) V)) (IsLocalRing.maximalIdeal V)
```

The maximal ideal of a separated principal-adic completion is the extension of the maximal
ideal of the valuation ring, provided the adic generator lies in that maximal ideal.

[Source](../AdicModules/CompletedLocalStructure.lean#L119-L139) (native source range).

<a id="api-cfc6aafda437d121"></a>

### ValuationRing.principalAdicCompletion_not_isField

```lean
theorem ValuationRing.principalAdicCompletion_not_isField {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) [IsHausdorff (Ideal.span {a}) V] : ¬IsField (AdicCompletion (Ideal.span {a}) V)
```

A separated principal-adic completion is not a field when the nonzero generator lies in the
maximal ideal.

[Source](../AdicModules/CompletedLocalStructure.lean#L141-L176) (native source range).

<a id="api-3d4327d85882323d"></a>

### ValuationRing.principalAdicCompletion_algebraMap_isLocalHom

```lean
theorem ValuationRing.principalAdicCompletion_algebraMap_isLocalHom {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) [IsHausdorff (Ideal.span {a}) V] : IsLocalHom (algebraMap V (AdicCompletion (Ideal.span {a}) V))
```

The canonical map to a separated principal-adic completion is local when the generator lies
in the maximal ideal.

[Source](../AdicModules/CompletedLocalStructure.lean#L178-L194) (native source range).

<a id="api-c8fa3858f83b98e3"></a>

### ValuationRing.principalAdicCompletion_residueFieldMap_bijective

```lean
theorem ValuationRing.principalAdicCompletion_residueFieldMap_bijective {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) [IsHausdorff (Ideal.span {a}) V] : Function.Bijective ⇑(IsLocalRing.ResidueField.map (algebraMap V (AdicCompletion (Ideal.span {a}) V)))
```

The canonical map to a separated principal-adic completion induces a bijection on residue
fields when the generator lies in the maximal ideal.

[Source](../AdicModules/CompletedLocalStructure.lean#L196-L231) (native source range).

## AdicModules.CompletedValuationComposite

Scope: library.

<a id="api-6c131e58a8d86e6a"></a>

### ValuationRing.completionIntegers_algebraMap_isLocalHom

```lean
theorem ValuationRing.completionIntegers_algebraMap_isLocalHom {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) [IsHausdorff (Ideal.span {a}) V] : IsLocalHom (algebraMap V ↥(CompletionIntegers V K))
```

The canonical map from a separated principal-adic valuation ring to the
valuation integers of its completed fraction field is local.

[Source](../AdicModules/CompletedValuationComposite.lean#L34-L62) (native source range).

<a id="api-62fe65fa6bb8a804"></a>

### ValuationRing.completionIntegers_residueFieldMap_bijective

```lean
theorem ValuationRing.completionIntegers_residueFieldMap_bijective {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) [IsHausdorff (Ideal.span {a}) V] : Function.Bijective ⇑(IsLocalRing.ResidueField.map (algebraMap V ↥(CompletionIntegers V K)))
```

The canonical map to the completed valuation integers induces a bijection
on residue fields.

[Source](../AdicModules/CompletedValuationComposite.lean#L64-L116) (native source range).

<a id="api-92d76a183d558d3a"></a>

### ValuationRing.completionIntegers_le_localizedAtPrime

```lean
theorem ValuationRing.completionIntegers_le_localizedAtPrime {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : have C := Valued.v.valuationSubring; have hDisj := ⋯; have A := localizedAdicCompletionValuationSubring p.primeCompl ha0 hDisj; C ≤ A
```

The completed valuation integers lie in the valuation subring obtained
from the completed localization at a nonzero prime.

[Source](../AdicModules/CompletedValuationComposite.lean#L126-L164) (native source range).

<a id="api-914c68f4095d24ad"></a>

### ValuationRing.completionIntegersValuationSubring_eq_localizedAtPrime_composite

```lean
theorem ValuationRing.completionIntegersValuationSubring_eq_localizedAtPrime_composite {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : have C := Valued.v.valuationSubring; have hDisj := ⋯; let A := localizedAdicCompletionValuationSubring p.primeCompl ha0 hDisj; have W := localizedAtPrimeQuotientValuationSubring p hp ha0; C = A.composite W
```

The completed valuation integers are literally the composite of the
completed localization at `p` and the transported quotient valuation ring.

[Source](../AdicModules/CompletedValuationComposite.lean#L166-L326) (native source range).

<a id="api-950672fbfbc03b4b"></a>

### ValuationRing.completionIntegersLocalizedPrime

```lean
noncomputable def ValuationRing.completionIntegersLocalizedPrime {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : have C := Valued.v.valuationSubring; Ideal ↥C
```

The distinguished prime of the completed valuation integers associated to
the completed localization at `p`.

[Source](../AdicModules/CompletedValuationComposite.lean#L328-L344) (native source range).

<a id="api-0d0bab4c0f8f500b"></a>

### ValuationRing.completionIntegersLocalizedPrime_isPrime

```lean
instance ValuationRing.completionIntegersLocalizedPrime_isPrime {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : Ideal.IsPrime (completionIntegersLocalizedPrime p hp ha0)
```

**API note (not a source docstring):** This instance proves that the distinguished ideal of the completed valuation integers is prime, under the displayed nonzero-prime, nonzero-generator and principal-adic separation hypotheses.

[Source](../AdicModules/CompletedValuationComposite.lean#L346-L353) (native source range).

<a id="api-a35db1ba2b31294b"></a>

### ValuationRing.completionIntegers_ofPrime_localizedPrime

```lean
theorem ValuationRing.completionIntegers_ofPrime_localizedPrime {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : let C := Valued.v.valuationSubring; have hDisj := ⋯; have A := localizedAdicCompletionValuationSubring p.primeCompl ha0 hDisj; C.ofPrime (completionIntegersLocalizedPrime p hp ha0) = A
```

Localizing the completed valuation integers at their distinguished prime
recovers the completed localization at `p`.

[Source](../AdicModules/CompletedValuationComposite.lean#L355-L379) (native source range).

<a id="api-09372448b9cace6e"></a>

### ValuationRing.completionIntegersCompositeResidue

```lean
noncomputable def ValuationRing.completionIntegersCompositeResidue {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : have C := Valued.v.valuationSubring; have W := localizedAtPrimeQuotientValuationSubring p hp ha0; ↥C →+* ↥W
```

The residue map from the completed valuation integers to the transported
quotient valuation ring.

[Source](../AdicModules/CompletedValuationComposite.lean#L381-L405) (native source range).

<a id="api-5213e7c9055c75d8"></a>

### ValuationRing.completionIntegersCompositeResidue_apply

```lean
theorem ValuationRing.completionIntegersCompositeResidue_apply {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : ↥Valued.v.valuationSubring) : let C := Valued.v.valuationSubring; have hDisj := ⋯; let A := localizedAdicCompletionValuationSubring p.primeCompl ha0 hDisj; have hCA := ⋯; ↑((completionIntegersCompositeResidue p hp ha0) x) = (IsLocalRing.residue ↥A) ((C.inclusion A hCA) x)
```

**API note (not a source docstring):** After including the completed valuation integers in the completed-localization valuation subring, applying its residue map gives the underlying value of the composite residue map. The displayed nonzero-prime, nonzero-generator and separation hypotheses remain required.

[Source](../AdicModules/CompletedValuationComposite.lean#L407-L425) (native source range).

<a id="api-c8f2dc338a5fefe2"></a>

### ValuationRing.completionIntegersCompositeResidue_surjective

```lean
theorem ValuationRing.completionIntegersCompositeResidue_surjective {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : Function.Surjective ⇑(completionIntegersCompositeResidue p hp ha0)
```

The completed composite residue map is onto the transported quotient
valuation ring.

[Source](../AdicModules/CompletedValuationComposite.lean#L427-L460) (native source range).

<a id="api-1ea309f2b71da2b8"></a>

### ValuationRing.ker_completionIntegersCompositeResidue

```lean
theorem ValuationRing.ker_completionIntegersCompositeResidue {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : RingHom.ker (completionIntegersCompositeResidue p hp ha0) = completionIntegersLocalizedPrime p hp ha0
```

The kernel of the completed composite residue map is the distinguished
prime corresponding to the completed localization.

[Source](../AdicModules/CompletedValuationComposite.lean#L462-L492) (native source range).

<a id="api-6c1e1c5b82cc9992"></a>

### ValuationRing.completionIntegersQuotientEquiv

```lean
noncomputable def ValuationRing.completionIntegersQuotientEquiv {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : let C := Valued.v.valuationSubring; have W := localizedAtPrimeQuotientValuationSubring p hp ha0; ↥C ⧸ completionIntegersLocalizedPrime p hp ha0 ≃+* ↥W
```

Quotienting the completed valuation integers by their distinguished prime
recovers the transported quotient valuation ring.

[Source](../AdicModules/CompletedValuationComposite.lean#L494-L508) (native source range).

<a id="api-6d065d0ec5803969"></a>

### ValuationRing.completionIntegersQuotientEquiv_mk

```lean
theorem ValuationRing.completionIntegersQuotientEquiv_mk {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : ↥Valued.v.valuationSubring) : (completionIntegersQuotientEquiv p hp ha0) ((Ideal.Quotient.mk (completionIntegersLocalizedPrime p hp ha0)) x) = (completionIntegersCompositeResidue p hp ha0) x
```

**API note (not a source docstring):** On a class represented by an element of the completed valuation integers, the quotient equivalence is the completed composite residue map. This is the computation rule for the equivalence, with the displayed hypotheses unchanged.

[Source](../AdicModules/CompletedValuationComposite.lean#L510-L523) (native source range).

## AdicModules.CompositeValuationSubring

Scope: library.

<a id="api-fc488472f1cb7dd5"></a>

### ValuationSubring.composite

```lean
noncomputable def ValuationSubring.composite {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : ValuationSubring K
```

The composite of a valuation subring `A` of a field with a valuation
subring `W` of the residue field of `A`. Its elements are exactly the elements
of `A` whose residue belongs to `W`.

[Source](../AdicModules/CompositeValuationSubring.lean#L26-L103) (native source range).

<a id="api-3f366b7361cf70c6"></a>

### ValuationSubring.mem_composite

```lean
theorem ValuationSubring.mem_composite {K : Type u} [Field K] {A : ValuationSubring K} {W : ValuationSubring (IsLocalRing.ResidueField ↥A)} {x : K} : x ∈ A.composite W ↔ ∃ (hx : x ∈ A), (IsLocalRing.residue ↥A) ⟨x, hx⟩ ∈ W
```

**API note (not a source docstring):** An ambient-field element belongs to the composite exactly when it belongs to the first valuation subring and its residue belongs to the second one.

[Source](../AdicModules/CompositeValuationSubring.lean#L105-L108) (native source range).

<a id="api-10789f8c8b81e750"></a>

### ValuationSubring.composite_le

```lean
theorem ValuationSubring.composite_le {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : A.composite W ≤ A
```

A composite valuation subring is contained in its first factor.

[Source](../AdicModules/CompositeValuationSubring.lean#L110-L112) (native source range).

<a id="api-dfb79f7ea71ddaf3"></a>

### ValuationSubring.compositeAlgebra

```lean
noncomputable instance ValuationSubring.compositeAlgebra {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : Algebra ↥(A.composite W) ↥A
```

The algebra structure on the first factor induced by the inclusion of the
composite valuation subring.

[Source](../AdicModules/CompositeValuationSubring.lean#L114-L118) (native source range).

<a id="api-7f1e9a470b20ad1b"></a>

### ValuationSubring.composite_top

```lean
theorem ValuationSubring.composite_top {K : Type u} [Field K] (A : ValuationSubring K) : A.composite ⊤ = A
```

**API note (not a source docstring):** Composing a valuation subring with the whole residue field, viewed as its top valuation subring, recovers the original valuation subring.

[Source](../AdicModules/CompositeValuationSubring.lean#L120-L124) (native source range).

<a id="api-4d0ef0b8114fef1f"></a>

### ValuationSubring.compositeResidue

```lean
noncomputable def ValuationSubring.compositeResidue {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : ↥(A.composite W) →+* ↥W
```

The canonical residue map from a composite valuation subring to its second
factor.

[Source](../AdicModules/CompositeValuationSubring.lean#L126-L131) (native source range).

<a id="api-02cc0e1245a0c0dc"></a>

### ValuationSubring.compositeResidue_apply

```lean
theorem ValuationSubring.compositeResidue_apply {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) (x : ↥(A.composite W)) : ↑((A.compositeResidue W) x) = (IsLocalRing.residue ↥A) ⟨↑x, ⋯⟩
```

**API note (not a source docstring):** The underlying residue-field value of the composite residue map is the residue of the same element viewed in the first valuation subring.

[Source](../AdicModules/CompositeValuationSubring.lean#L133-L137) (native source range).

<a id="api-8c8d468276f5e55f"></a>

### ValuationSubring.compositeResidue_surjective

```lean
theorem ValuationSubring.compositeResidue_surjective {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : Function.Surjective ⇑(A.compositeResidue W)
```

The canonical residue map from a composite valuation subring onto its
second factor is surjective.

[Source](../AdicModules/CompositeValuationSubring.lean#L139-L149) (native source range).

<a id="api-6f23fcb6a3064d43"></a>

### ValuationSubring.compositeIdeal

```lean
noncomputable def ValuationSubring.compositeIdeal {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : Ideal ↥(A.composite W)
```

The distinguished prime of a composite valuation subring: the maximal
ideal of its first factor, pulled back along the inclusion.

[Source](../AdicModules/CompositeValuationSubring.lean#L151-L156) (native source range).

<a id="api-f11d8e6a73fcbad1"></a>

### ValuationSubring.compositeIdeal_isPrime

```lean
instance ValuationSubring.compositeIdeal_isPrime {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : (A.compositeIdeal W).IsPrime
```

**API note (not a source docstring):** The distinguished ideal of the composite valuation subring is prime. It is the pullback of the first factor's maximal ideal along the inclusion of the composite.

[Source](../AdicModules/CompositeValuationSubring.lean#L158-L160) (native source range).

<a id="api-f14b4ce77fe64686"></a>

### ValuationSubring.ofPrime_compositeIdeal

```lean
theorem ValuationSubring.ofPrime_compositeIdeal {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : (A.composite W).ofPrime (A.compositeIdeal W) = A
```

Localizing a composite valuation subring at its distinguished prime
recovers its first factor as a valuation subring of the ambient field.

[Source](../AdicModules/CompositeValuationSubring.lean#L162-L168) (native source range).

<a id="api-65ea5b50562d97ab"></a>

### ValuationSubring.ofPrimeCompositeIdealAlgEquiv

```lean
noncomputable def ValuationSubring.ofPrimeCompositeIdealAlgEquiv {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : ↥((A.composite W).ofPrime (A.compositeIdeal W)) ≃ₐ[↥(A.composite W)] ↥A
```

The first factor is canonically equivalent, over the composite, to the
coarsening at the distinguished prime.

[Source](../AdicModules/CompositeValuationSubring.lean#L170-L177) (native source range).

<a id="api-c17074073c0540d6"></a>

### ValuationSubring.composite_isLocalizationAtPrime

```lean
instance ValuationSubring.composite_isLocalizationAtPrime {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : IsLocalization.AtPrime (↥A) (A.compositeIdeal W)
```

The first factor is a localization of the composite at the distinguished
prime.

[Source](../AdicModules/CompositeValuationSubring.lean#L179-L184) (native source range).

<a id="api-ade7427690f06b42"></a>

### ValuationSubring.ker_compositeResidue

```lean
theorem ValuationSubring.ker_compositeResidue {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : RingHom.ker (A.compositeResidue W) = A.compositeIdeal W
```

The kernel of the composite residue map is its distinguished prime.

[Source](../AdicModules/CompositeValuationSubring.lean#L186-L195) (native source range).

<a id="api-3c0ae8df79d52681"></a>

### ValuationSubring.mem_compositeIdeal

```lean
theorem ValuationSubring.mem_compositeIdeal {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) (x : ↥(A.composite W)) : x ∈ A.compositeIdeal W ↔ (IsLocalRing.residue ↥A) ⟨↑x, ⋯⟩ = 0
```

**API note (not a source docstring):** An element of the composite lies in its distinguished ideal exactly when its residue in the first factor's residue field is zero.

[Source](../AdicModules/CompositeValuationSubring.lean#L197-L203) (native source range).

<a id="api-df287e5d6bc382ed"></a>

### ValuationSubring.quotientCompositeIdealEquiv

```lean
noncomputable def ValuationSubring.quotientCompositeIdealEquiv {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) : ↥(A.composite W) ⧸ A.compositeIdeal W ≃+* ↥W
```

Quotienting a composite valuation subring by its distinguished prime
recovers its second factor.

[Source](../AdicModules/CompositeValuationSubring.lean#L205-L211) (native source range).

<a id="api-37f402e5bf5e5bf2"></a>

### ValuationSubring.quotientCompositeIdealEquiv_mk

```lean
theorem ValuationSubring.quotientCompositeIdealEquiv_mk {K : Type u} [Field K] (A : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField ↥A)) (x : ↥(A.composite W)) : (A.quotientCompositeIdealEquiv W) ((Ideal.Quotient.mk (A.compositeIdeal W)) x) = (A.compositeResidue W) x
```

**API note (not a source docstring):** On a quotient class represented by an element of the composite, the quotient equivalence agrees with the composite residue map into the second valuation subring.

[Source](../AdicModules/CompositeValuationSubring.lean#L213-L218) (native source range).

<a id="api-6aaacb2cc069995b"></a>

### ValuationSubring.eq_of_le_of_isLocalHom

```lean
theorem ValuationSubring.eq_of_le_of_isLocalHom {K : Type u} [Field K] {R S : ValuationSubring K} (h : R ≤ S) [IsLocalHom (R.inclusion S h)] : R = S
```

A local inclusion between valuation subrings of the same field is an
equality.

[Source](../AdicModules/CompositeValuationSubring.lean#L220-L227) (native source range).

## AdicModules.LocalizedCompletion

Scope: library.

<a id="api-5e961e89e9d8187e"></a>

### ValuationRing.isUniformInducing_mapToFractionRing

```lean
theorem ValuationRing.isUniformInducing_mapToFractionRing {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] : IsUniformInducing ⇑(Localization.mapToFractionRing K S Vₛ ⋯)
```

The canonical embedding of a localization into the fraction field induces the localized
principal-adic uniformity when the denominators avoid the radical of the generator.

[Source](../AdicModules/LocalizedCompletion.lean#L117-L168) (native source range).

<a id="api-8eedc5ebc9adefea"></a>

### ValuationRing.localizedAdicCompletionToFractionFieldCompletion

```lean
noncomputable def ValuationRing.localizedAdicCompletionToFractionFieldCompletion {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] : AdicCompletion (Ideal.span {(algebraMap V Vₛ) a}) Vₛ →+* UniformSpace.Completion K
```

The completion of a localization embeds canonically into the completion of the original
fraction field.

[Source](../AdicModules/LocalizedCompletion.lean#L170-L197) (native source range).

<a id="api-b541568469a1648e"></a>

### ValuationRing.localizedAdicCompletionToFractionFieldCompletion_algebraMap

```lean
theorem ValuationRing.localizedAdicCompletionToFractionFieldCompletion_algebraMap {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] (x : Vₛ) : (localizedAdicCompletionToFractionFieldCompletion S ha0 hSrad) ((algebraMap Vₛ (AdicCompletion (Ideal.span {(algebraMap V Vₛ) a}) Vₛ)) x) = (algebraMap K (UniformSpace.Completion K)) ((Localization.mapToFractionRing K S Vₛ ⋯) x)
```

The completion embedding extends the canonical localization map into the fraction field.

[Source](../AdicModules/LocalizedCompletion.lean#L199-L232) (native source range).

<a id="api-26a5773048c97eca"></a>

### ValuationRing.localizedAdicCompletionToFractionFieldCompletion_algebraMap_base

```lean
theorem ValuationRing.localizedAdicCompletionToFractionFieldCompletion_algebraMap_base {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] (x : V) : (localizedAdicCompletionToFractionFieldCompletion S ha0 hSrad) ((algebraMap Vₛ (AdicCompletion (Ideal.span {(algebraMap V Vₛ) a}) Vₛ)) ((algebraMap V Vₛ) x)) = (algebraMap K (UniformSpace.Completion K)) ((algebraMap V K) x)
```

On the original valuation ring, the localized completion embedding is the canonical map to
the completed fraction field.

[Source](../AdicModules/LocalizedCompletion.lean#L234-L247) (native source range).

<a id="api-d2e50a2221240540"></a>

### ValuationRing.localizedAdicCompletionToFractionFieldCompletion_injective

```lean
theorem ValuationRing.localizedAdicCompletionToFractionFieldCompletion_injective {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] : Function.Injective ⇑(localizedAdicCompletionToFractionFieldCompletion S ha0 hSrad)
```

The canonical map from the localized principal-adic completion to the completed fraction
field is injective.

[Source](../AdicModules/LocalizedCompletion.lean#L249-L284) (native source range).

<a id="api-41abdcca764c2004"></a>

### ValuationRing.completionIntegers_mem_range_localizedAdicCompletion

```lean
theorem ValuationRing.completionIntegers_mem_range_localizedAdicCompletion {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] (z : ↥(CompletionIntegers V K)) : ↑z ∈ Set.range ⇑(localizedAdicCompletionToFractionFieldCompletion S ha0 hSrad)
```

Every completed valuation integer lies in the image of the localized completion inside the
common completed fraction field.

[Source](../AdicModules/LocalizedCompletion.lean#L286-L331) (native source range).

<a id="api-72f729b7e8658cca"></a>

### ValuationRing.localizedAdicCompletionFractionFieldAlgebra

```lean
noncomputable def ValuationRing.localizedAdicCompletionFractionFieldAlgebra {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] : Algebra (AdicCompletion (Ideal.span {(algebraMap V Vₛ) a}) Vₛ) (UniformSpace.Completion K)
```

The algebra structure on the common completed fraction field induced by the localized
completion embedding.

[Source](../AdicModules/LocalizedCompletion.lean#L333-L345) (native source range).

<a id="api-401aa361edcb1396"></a>

### ValuationRing.localizedAdicCompletion_isFractionRing

```lean
theorem ValuationRing.localizedAdicCompletion_isFractionRing {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] : IsFractionRing (AdicCompletion (Ideal.span {(algebraMap V Vₛ) a}) Vₛ) (UniformSpace.Completion K)
```

The common completed fraction field is a fraction field of the localized principal-adic
completion.

[Source](../AdicModules/LocalizedCompletion.lean#L347-L387) (native source range).

## AdicModules.LocalizedFiltration

Scope: library.

<a id="api-f023427cc3ea978c"></a>

### ValuationRing.localizedPowerImage

```lean
def ValuationRing.localizedPowerImage {V : Type u} [CommRing V] (Vₛ : Type v) [CommRing Vₛ] [Algebra V Vₛ] (a : V) (n : ℕ) : Submodule V Vₛ
```

The literal image of `(a ^ n)` from the base ring in a localization.  Unlike `Ideal.map`,
this remembers only base-ring multiples.

[Source](../AdicModules/LocalizedFiltration.lean#L32-L35) (native source range).

<a id="api-0dd93b0a3c46c251"></a>

### ValuationRing.denominator_dvd_of_not_mem_radical

```lean
theorem ValuationRing.denominator_dvd_of_not_mem_radical {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (S : Submonoid V) {a : V} (hS : Disjoint ↑S ↑(Ideal.span {a}).radical) (s : ↥S) : ↑s ∣ a
```

A denominator disjoint from the radical of `(a)` divides `a` in a valuation ring.

[Source](../AdicModules/LocalizedFiltration.lean#L37-L44) (native source range).

<a id="api-e06ad0e9f883a281"></a>

### ValuationRing.pow_succ_mul_mem_localizedPowerImage

```lean
theorem ValuationRing.pow_succ_mul_mem_localizedPowerImage {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (S : Submonoid V) (Vₛ : Type v) [CommRing Vₛ] [Algebra V Vₛ] [IsLocalization S Vₛ] {a : V} (hS : Disjoint ↑S ↑(Ideal.span {a}).radical) (n : ℕ) (x : Vₛ) : (algebraMap V Vₛ) a ^ (n + 1) * x ∈ localizedPowerImage Vₛ a n
```

Multiplying an arbitrary localized element by `a ^ (n + 1)` lands in the literal image of
`a ^ n V`.  This is the substantive inclusion in the localized-filtration comparison.

[Source](../AdicModules/LocalizedFiltration.lean#L46-L70) (native source range).

<a id="api-bc6e1e14a5ede83c"></a>

### ValuationRing.localizedPowerImage_sandwich

```lean
theorem ValuationRing.localizedPowerImage_sandwich {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (S : Submonoid V) (Vₛ : Type v) [CommRing Vₛ] [Algebra V Vₛ] [IsLocalization S Vₛ] {a : V} (hS : Disjoint ↑S ↑(Ideal.span {a}).radical) (n : ℕ) : Submodule.restrictScalars V (Ideal.span {(algebraMap V Vₛ) a} ^ (n + 1)) ≤ localizedPowerImage Vₛ a n ∧ localizedPowerImage Vₛ a n ≤ Submodule.restrictScalars V (Ideal.span {(algebraMap V Vₛ) a} ^ n)
```

The powers of the extended principal ideal sandwich the literal images of the base powers.

[Source](../AdicModules/LocalizedFiltration.lean#L72-L92) (native source range).

<a id="api-3ef24c7b665f9f22"></a>

### ValuationRing.hasBasis_nhds_zero_adic_localizedPowerImage

```lean
theorem ValuationRing.hasBasis_nhds_zero_adic_localizedPowerImage {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (S : Submonoid V) (Vₛ : Type v) [CommRing Vₛ] [Algebra V Vₛ] [IsLocalization S Vₛ] {a : V} (hS : Disjoint ↑S ↑(Ideal.span {a}).radical) : (nhds 0).HasBasis (fun (_n : ℕ) => True) fun (n : ℕ) => ↑(localizedPowerImage Vₛ a n)
```

In the adic topology of the localized principal ideal, the literal images of `a ^ n V`
form a neighborhood basis at zero.

[Source](../AdicModules/LocalizedFiltration.lean#L94-L111) (native source range).

<a id="api-021171c6f995c5bc"></a>

### ValuationRing.isHausdorff_localization_span_singleton

```lean
theorem ValuationRing.isHausdorff_localization_span_singleton {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (S : Submonoid V) (Vₛ : Type v) [CommRing Vₛ] [Algebra V Vₛ] [IsLocalization S Vₛ] {a : V} (hS : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] : IsHausdorff (Ideal.span {(algebraMap V Vₛ) a}) Vₛ
```

Separatedness for a principal-adic filtration passes to any localization whose denominators
are disjoint from the radical of the principal ideal.

[Source](../AdicModules/LocalizedFiltration.lean#L113-L139) (native source range).

<a id="api-7c8f31ad5360bd66"></a>

### ValuationRing.isHausdorff_localizationAtPrime_span_singleton

```lean
theorem ValuationRing.isHausdorff_localizationAtPrime_span_singleton {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (p : Ideal V) [p.IsPrime] (Vₚ : Type v) [CommRing Vₚ] [Algebra V Vₚ] [IsLocalization p.primeCompl Vₚ] {a : V} (ha : (Ideal.span {a}).radical ≤ p) [IsHausdorff (Ideal.span {a}) V] : IsHausdorff (Ideal.span {(algebraMap V Vₚ) a}) Vₚ
```

The separatedness consequence specialized to an arbitrary model of localization at a prime
containing the radical of `(a)`.

[Source](../AdicModules/LocalizedFiltration.lean#L141-L151) (native source range).

<a id="api-bff0d4baef9754d3"></a>

### ValuationRing.isHausdorff_localizationAtNonzeroPrime_span_singleton

```lean
theorem ValuationRing.isHausdorff_localizationAtNonzeroPrime_span_singleton {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) (Vₚ : Type v) [CommRing Vₚ] [Algebra V Vₚ] [IsLocalization p.primeCompl Vₚ] {a : V} [IsHausdorff (Ideal.span {a}) V] : IsHausdorff (Ideal.span {(algebraMap V Vₚ) a}) Vₚ
```

Principal-adic separatedness passes to localization at every nonzero prime of a
valuation domain. The required containment of the principal radical follows automatically
from separatedness.

[Source](../AdicModules/LocalizedFiltration.lean#L153-L162) (native source range).

## AdicModules.LocalizedQuotientValuationSubring

Scope: library.

<a id="api-e9292611d5bda127"></a>

### ValuationRing.primeCompl_disjoint_radical_span_singleton_of_isHausdorff

```lean
theorem ValuationRing.primeCompl_disjoint_radical_span_singleton_of_isHausdorff {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} [IsHausdorff (Ideal.span {a}) V] : Disjoint ↑p.primeCompl ↑(Ideal.span {a}).radical
```

The complement of a nonzero prime is disjoint from the radical of every
principal ideal whose power filtration is separated.

[Source](../AdicModules/LocalizedQuotientValuationSubring.lean#L34-L43) (native source range).

<a id="api-56fa7923e08e48d8"></a>

### ValuationRing.localizedAtPrimeQuotientValuationSubring

```lean
noncomputable def ValuationRing.localizedAtPrimeQuotientValuationSubring {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : have A := localizedAdicCompletionValuationSubring p.primeCompl ha0 ⋯; ValuationSubring (IsLocalRing.ResidueField ↥A)
```

The quotient valuation ring `V / p`, transported into the residue field of
the completed localization at `p`.

The canonical valuation subring of `p.ResidueField`, with coefficient ring
`V / p`, is pulled back along the inverse of the completed-localization
residue-field equivalence. This inverse orientation makes the result a
valuation subring of the completed-localization residue field.

[Source](../AdicModules/LocalizedQuotientValuationSubring.lean#L45-L72) (native source range).

<a id="api-6b5181aa3ea10678"></a>

### ValuationRing.mem_localizedAtPrimeQuotientValuationSubring

```lean
theorem ValuationRing.mem_localizedAtPrimeQuotientValuationSubring {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : have A := localizedAdicCompletionValuationSubring p.primeCompl ha0 ⋯; IsLocalRing.ResidueField ↥A) : have hDisj := ⋯; let A := localizedAdicCompletionValuationSubring p.primeCompl ha0 hDisj; have e := localizedAdicCompletionResidueFieldEquiv p.primeCompl ha0 hDisj; x ∈ localizedAtPrimeQuotientValuationSubring p hp ha0 ↔ e.symm x ∈ (valuation (V ⧸ p) p.ResidueField).valuationSubring
```

An element belongs to the transported quotient valuation ring exactly when
its inverse image in `p.ResidueField` belongs to the canonical quotient
valuation subring.

[Source](../AdicModules/LocalizedQuotientValuationSubring.lean#L74-L112) (native source range).

<a id="api-6f6a4f959718fb39"></a>

### ValuationRing.localizedAtPrimeQuotientValuationSubring_algebraMap_mem

```lean
theorem ValuationRing.localizedAtPrimeQuotientValuationSubring_algebraMap_mem {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : V ⧸ p) : have hDisj := ⋯; let A := localizedAdicCompletionValuationSubring p.primeCompl ha0 hDisj; have e := localizedAdicCompletionResidueFieldEquiv p.primeCompl ha0 hDisj; e ((algebraMap (V ⧸ p) p.ResidueField) x) ∈ localizedAtPrimeQuotientValuationSubring p hp ha0
```

The transported quotient valuation ring contains the image of every
element of `V / p`.

[Source](../AdicModules/LocalizedQuotientValuationSubring.lean#L114-L144) (native source range).

## AdicModules.LocalizedResidueField

Scope: library.

<a id="api-4e69c18e9a8b2f4d"></a>

### ValuationRing.localizedAdicCompletionResidueFieldEquiv

```lean
noncomputable def ValuationRing.localizedAdicCompletionResidueFieldEquiv {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] : have hS0 := ⋯; have hSnzd := ⋯; IsLocalRing.ResidueField Vₛ ≃+* IsLocalRing.ResidueField ↥(localizedAdicCompletionValuationSubring S ha0 hSrad)
```

The residue field of a localization away from the radical of a nonzero
principal ideal is canonically equivalent to the residue field of its
principal-adic completion, realized as a valuation subring of the common
completed fraction field.

[Source](../AdicModules/LocalizedResidueField.lean#L34-L85) (native source range).

<a id="api-a8c96e1b939cd213"></a>

### ValuationRing.localizedAdicCompletionResidueFieldEquiv_residue

```lean
theorem ValuationRing.localizedAdicCompletionResidueFieldEquiv_residue {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] (x : Vₛ) : have hS0 := ⋯; have hSnzd := ⋯; (localizedAdicCompletionResidueFieldEquiv S ha0 hSrad) ((IsLocalRing.residue Vₛ) x) = (IsLocalRing.residue ↥(localizedAdicCompletionValuationSubring S ha0 hSrad)) ((localizedAdicCompletionValuationSubringEquiv S ha0 hSrad) ((algebraMap Vₛ (AdicCompletion (Ideal.span {(algebraMap V Vₛ) a}) Vₛ)) x))
```

The residue-field equivalence carries the residue of an element of the
localization to the residue of its image in the completed-localization
valuation subring.

[Source](../AdicModules/LocalizedResidueField.lean#L87-L140) (native source range).

## AdicModules.LocalizedValuationSubring

Scope: library.

<a id="api-32d7e0415ed7c37d"></a>

### ValuationRing.localization_isValuationRing

```lean
theorem ValuationRing.localization_isValuationRing {V : Type u} {Vₛ : Type v} [CommRing V] [IsDomain V] [ValuationRing V] (S : Submonoid V) [CommRing Vₛ] [Algebra V Vₛ] [IsLocalization S Vₛ] (hS : S ≤ nonZeroDivisors V) : ValuationRing Vₛ
```

Every localization of a valuation domain away from non-zero-divisors is
again a valuation domain. This is stated as a theorem rather than a global
instance so that arbitrary localization models do not introduce typeclass
search loops.

[Source](../AdicModules/LocalizedValuationSubring.lean#L30-L57) (native source range).

<a id="api-d207a33f1e35b174"></a>

### ValuationRing.localizedAdicCompletionValuationSubring

```lean
noncomputable def ValuationRing.localizedAdicCompletionValuationSubring {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] : ValuationSubring (UniformSpace.Completion K)
```

The localized principal-adic completion, regarded through its canonical
embedding as a valuation subring of the common completed fraction field.

[Source](../AdicModules/LocalizedValuationSubring.lean#L64-L96) (native source range).

<a id="api-17abbcfd6aceba1b"></a>

### ValuationRing.localizedAdicCompletionValuationSubringEquiv

```lean
noncomputable def ValuationRing.localizedAdicCompletionValuationSubringEquiv {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] : AdicCompletion (Ideal.span {(algebraMap V Vₛ) a}) Vₛ ≃+* ↥(localizedAdicCompletionValuationSubring S ha0 hSrad)
```

The localized principal-adic completion is canonically isomorphic to its
realization as a valuation subring of the common completed fraction field.

[Source](../AdicModules/LocalizedValuationSubring.lean#L98-L131) (native source range).

<a id="api-a227a2d936434a2a"></a>

### ValuationRing.coe_localizedAdicCompletionValuationSubringEquiv_apply

```lean
theorem ValuationRing.coe_localizedAdicCompletionValuationSubringEquiv_apply {V : Type u} {Vₛ : Type v} {K : Type w} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K] (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (hSrad : Disjoint ↑S ↑(Ideal.span {a}).radical) [IsHausdorff (Ideal.span {a}) V] (x : AdicCompletion (Ideal.span {(algebraMap V Vₛ) a}) Vₛ) : ↑((localizedAdicCompletionValuationSubringEquiv S ha0 hSrad) x) = (localizedAdicCompletionToFractionFieldCompletion S ha0 hSrad) x
```

The canonical equivalence onto the localized-completion valuation subring
is the accepted embedding into the common completed fraction field.

[Source](../AdicModules/LocalizedValuationSubring.lean#L133-L148) (native source range).

## AdicModules.PrincipalAdicSpectrum

Scope: library.

<a id="api-0ac84e04d10976a4"></a>

### ValuationRing.completionIntegers_exists_associated_algebraMap

```lean
theorem ValuationRing.completionIntegers_exists_associated_algebraMap {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (z : ↥(CompletionIntegers V K)) : ∃ (x : V), Associated ((algebraMap V ↥(CompletionIntegers V K)) x) z
```

Every element of the completed valuation integers is associated to the image of an element of
the original valuation ring.

[Source](../AdicModules/PrincipalAdicSpectrum.lean#L40-L76) (native source range).

<a id="api-3678166d6472beba"></a>

### ValuationRing.principalAdicCompletion_exists_associated_algebraMap

```lean
theorem ValuationRing.principalAdicCompletion_exists_associated_algebraMap {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (z : AdicCompletion (Ideal.span {a}) V) : ∃ (x : V), Associated ((algebraMap V (AdicCompletion (Ideal.span {a}) V)) x) z
```

Every element of a separated principal-adic completion of a valuation ring is associated to
the image of an element of the original ring.

[Source](../AdicModules/PrincipalAdicSpectrum.lean#L78-L96) (native source range).

<a id="api-a30039ebd5c17a69"></a>

### ValuationRing.principalAdicCompletion_map_comap_eq

```lean
theorem ValuationRing.principalAdicCompletion_map_comap_eq {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (J : Ideal (AdicCompletion (Ideal.span {a}) V)) : Ideal.map (algebraMap V (AdicCompletion (Ideal.span {a}) V)) (Ideal.comap (algebraMap V (AdicCompletion (Ideal.span {a}) V)) J) = J
```

Extension after contraction is the identity on every ideal of a separated principal-adic
completion of a valuation ring.

[Source](../AdicModules/PrincipalAdicSpectrum.lean#L98-L111) (native source range).

<a id="api-9659abc249d970e5"></a>

### ValuationRing.principalAdicCompletion_faithfullyFlat

```lean
theorem ValuationRing.principalAdicCompletion_faithfullyFlat {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) [IsHausdorff (Ideal.span {a}) V] : Module.FaithfullyFlat V (AdicCompletion (Ideal.span {a}) V)
```

A separated principal-adic completion map of a valuation ring is faithfully flat when its
nonzero generator belongs to the maximal ideal.

[Source](../AdicModules/PrincipalAdicSpectrum.lean#L113-L137) (native source range).

<a id="api-ef4b0b2239c2d137"></a>

### ValuationRing.principalAdicCompletion_extensionValuation_isEquiv

```lean
theorem ValuationRing.principalAdicCompletion_extensionValuation_isEquiv {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : let A := AdicCompletion (Ideal.span {a}) V; Valued.v.IsEquiv (valuation A (UniformSpace.Completion K))
```

The extension of the original valuation to the completed fraction field is equivalent to the
canonical valuation attached to the completed valuation ring. Applying
`Valuation.IsEquiv.orderMonoidIso` gives the canonical ordered value-group isomorphism.

[Source](../AdicModules/PrincipalAdicSpectrum.lean#L139-L181) (native source range).

<a id="api-1e51df795017da94"></a>

### ValuationRing.principalAdicCompletionPrimeSpectrumOrderIso

```lean
noncomputable def ValuationRing.principalAdicCompletionPrimeSpectrumOrderIso {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) [IsHausdorff (Ideal.span {a}) V] : PrimeSpectrum (AdicCompletion (Ideal.span {a}) V) ≃o PrimeSpectrum V
```

Contraction along a separated principal-adic completion map gives an order isomorphism on
prime spectra when the nonzero generator belongs to the maximal ideal.

[Source](../AdicModules/PrincipalAdicSpectrum.lean#L183-L218) (native source range).

<a id="api-0ce7a6768eda12ff"></a>

### ValuationRing.principalAdicCompletion_primeHeight_comap

```lean
theorem ValuationRing.principalAdicCompletion_primeHeight_comap {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K] (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) [IsHausdorff (Ideal.span {a}) V] (P : PrimeSpectrum (AdicCompletion (Ideal.span {a}) V)) : Order.height (PrimeSpectrum.comap (algebraMap V (AdicCompletion (Ideal.span {a}) V)) P) = Order.height P
```

Corresponding primes of a separated principal-adic valuation-ring completion have the same
height.

[Source](../AdicModules/PrincipalAdicSpectrum.lean#L220-L232) (native source range).

## AdicModules.ValuationTopology

Scope: library.

<a id="api-39b00fca2dd98e67"></a>

### Valuation.exists_pow_restrict_lt_of_isHausdorff

```lean
theorem Valuation.exists_pow_restrict_lt_of_isHausdorff {R : Type u} {Γ₀ : Type v} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀] (ν : Valuation R Γ₀) (hspan : ∀ (x y : R), x ∈ Ideal.span {y} ↔ ν x ≤ ν y) {a : R} [IsHausdorff (Ideal.span {a}) R] (γ : (MonoidWithZeroHom.ofClass ν).ValueGroup₀ˣ) : ∃ (n : ℕ), ν.restrict a ^ n < ↑γ
```

If a valuation detects membership in principal ideals and the powers of `(a)` are
separated, then the values of those powers are cofinal below every nonzero value-group
radius.

[Source](../AdicModules/ValuationTopology.lean#L31-L73) (native source range).

<a id="api-c2588652104cedcc"></a>

### ValuationRing.radical_span_singleton_le_prime_of_isHausdorff

```lean
theorem ValuationRing.radical_span_singleton_le_prime_of_isHausdorff {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {a : V} [IsHausdorff (Ideal.span {a}) V] (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) : (Ideal.span {a}).radical ≤ p
```

In a valuation domain separated for the powers of `(a)`, every nonzero prime ideal
contains the radical of `(a)`.

Indeed, if `a` were outside a nonzero prime `p`, choose a nonzero `x ∈ p`. Totality of
divisibility compares `x` with every power of `a`. The alternative `x ∣ a ^ n` would put
`a` in `p`, so every `a ^ n` divides `x`; separatedness then forces `x = 0`.

[Source](../AdicModules/ValuationTopology.lean#L79-L104) (native source range).

<a id="api-f6da159ebf919389"></a>

### ValuationRing.exists_pow_valuation_lt_of_isHausdorff

```lean
theorem ValuationRing.exists_pow_valuation_lt_of_isHausdorff {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] {a : V} [IsHausdorff (Ideal.span {a}) V] (γ : (MonoidWithZeroHom.ofClass (Valuation.comap (algebraMap V K) (valuation V K))).ValueGroup₀ˣ) : ∃ (n : ℕ), (Valuation.comap (algebraMap V K) (valuation V K)).restrict a ^ n < ↑γ
```

In a valuation ring separated for the powers of `(a)`, those powers are cofinal below
every nonzero radius for the valuation induced on the ring by its fraction-field valuation.

[Source](../AdicModules/ValuationTopology.lean#L106-L119) (native source range).

<a id="api-27aeaf6f18beb63d"></a>

### ValuationRing.isAdic_valuationTopology_span_singleton

```lean
theorem ValuationRing.isAdic_valuationTopology_span_singleton {V : Type u} {K : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] : IsAdic (Ideal.span {a})
```

For a nonzero `a` in a valuation ring, if the powers of `(a)` are separated, then the
topology induced by the fraction-field valuation is the `(a)`-adic topology.

[Source](../AdicModules/ValuationTopology.lean#L121-L157) (native source range).
