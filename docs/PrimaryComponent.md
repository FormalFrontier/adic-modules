# Primary-component exactness

Import `AdicModules` or the narrower `AdicModules.PrimaryComponent`. This is a
manual supplement to the [historical generated API snapshot](API.md), not an
update to its 13-leaf/28-module/103-site inventory.

## Dedekind-domain modules

For a commutative Dedekind domain `R`, a height-one prime `P`, linear maps
`f : M →ₗ[R] N` and `g : N →ₗ[R] Q`, the public theorem
`Ideal.primaryComponent.exact` takes
`Module.IsTorsion R M` and `Function.Exact f g` and yields

```lean
Function.Exact (Ideal.primaryComponent.map P.asIdeal f)
  (Ideal.primaryComponent.map P.asIdeal g)
```

The primary-component and its maps are mathlib's native ideal-power-annihilator
submodule and restricted linear maps. The proof corestricts `f` onto `g.ker`,
uses exactness to make it surjective, and applies mathlib's
`Ideal.primaryComponent.map_surjective`; annihilation by the same ideal power
lifts from `N` to the kernel subtype. Only the **source** is assumed torsion.
No finite generation, finite group, uniform ideal exponent or torsion of `N`
or `Q` is required. For example, deleting source torsion fails for a
surjection `ℤ → ZMod p` followed by zero.

## Ordinary abelian groups

For a natural prime `p` with `[Fact p.Prime]`, the helpers in `AddCommGroup` are:

- `integerPrime p`: the height-one prime ideal `(p)` of `ℤ`;
- `mem_integerPrime_iff p x` and `integerPrime_subgroup p`: elementwise
  membership and equality with `AddCommGroup.primaryComponent G p`;
- `primaryComponent.map p f`: restriction of `f : G →+ H` to the two ordinary
  `p`-primary subgroups, with `primaryComponent.map_apply p f x` for its
  underlying action;
- `integerPrime_map_agrees p f x`: pointwise agreement of this actual restricted
  homomorphism with mathlib's ideal-primary restricted linear map;
- `primaryComponent.exact hG p f g hfg`: exactness of the **ordinary restricted
  homomorphisms** for `hG : IsAddTorsion G` and `hfg : Function.Exact f g`.

The last theorem transports ideal-primary exactness using membership and map
agreement, rather than concluding map exactness merely from subgroup equality.
Here `G`, `H` and `K` are arbitrary abelian groups apart from the stated
source-torsion premise. The [ordinary-import client](../AdicModulesTest/PrimaryComponent.lean)
checks membership, actual maps and both exactness statements. Unlike the
uniform condition in [BoundedIdealPowerTorsion](../AdicModules/BoundedIdealPowerTorsion.lean),
primary membership allows a different exponent for each element;
`Module.Finite` remains necessary for the library's uniform-exponent bridge.

Run `lake exe cache get` in the pinned project before `lake --wfail build`.
Passing the build and selected `#print axioms` checks does not replace complete
transitive standard-axiom audit or independent review of the exact candidate.
