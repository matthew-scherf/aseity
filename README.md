# Aseity

This is a concise, axiom-free formalization of a result in Lean 4.

> No self-contained epistemic system can prove its own aseity, meaning it cannot show that it is not grounded in something external. In theological terms, even an all-knowing God cannot prove that he is ungrounded or not a meta-god.

The theorem does not depend on whether the system is actually grounded. It is about what can be known from inside the system, making it a result about unknowability rather than grounding.

## Argument

Let `S` be an epistemic system and `g : Sys` the maximal ("global") one. Write `U S` for the proposition of `S`'s aseity, in its negative form:

```
U S  :=  ¬ ∃ x, (Ext x ∧ Grounds x S)        -- "nothing external grounds S"
```

`C1: ¬ K S (U S). S` cannot know `U S` because the system is internally sealed. Nothing it can access is outside itself, and its deductive closure never goes beyond its own limits. The boundary between the system and anything external is not something it can examine. Since aseity is about this boundary, the system cannot certify it. For the maximal system, this means `g` cannot even believe `U g`.

The closest structural comparison is Gödel's second incompleteness theorem.

## Aboutness

`AboutExt` is understood as realized reference: a formula is about the external only when some object actually instantiates Ext. This makes the result's dependence clear, rather than hiding it in a vacuous truth. The main lemma is:

```lean
theorem aboutU_iff (S) : AboutExt (U S) ↔ Nonempty Obj
```

Aseity is outward-reaching only when the exterior is a live, non-empty domain. If the exterior is provably empty, `U g` becomes the trivial statement `¬∃x∈∅`, which is not about the external, and the unknowability result does not apply. In this case, a triviality is knowable, even for an internalist God. The result focuses on the live case: as long as something exists, the ground of everything cannot be certified from within.

## Positive form

`U` is the negative form of aseity. The file also defines a variant that drops the externality marker:

```
Upos S  :=  ¬ ∃ x, Grounds x S        -- "nothing grounds S"
```

`Upos` makes the same groundlessness claim but contains no realized reference to the exterior. `notAbout_Upos` shows it is never outward-reaching, and in the model below it is knowable. The unknowability result is therefore specific to the formulation that invokes a live exterior. The obstruction comes from the `Ext` atom.

## Contents

`Aseity.lean` is self-contained Lean 4 that does not use Mathlib.

The object language is concrete. `Form` is an inductive syntax with an `Ext` atom and an existential binder indexed by objects. `AboutExt : Form → Prop` is defined by recursion, as described above. `U S` is defined as the literal `¬∃x (Ext x ∧ Grounds x S)` and `Upos S` as `¬∃x (Grounds x S)`.

```lean
theorem hAboutU [Nonempty Obj] (S) : AboutExt (U S)
```

The key claim is that the negative form of aseity reaches beyond the system's boundary. This is proved using `aboutU_iff` and the assumption of a live exterior.

There are five structural axioms that encode maximal internality. The epistemic predicates `K`, `BSet`, `Cl`, `AccF`, and `WithinF` are left undefined.

| Axiom | Statement | Reading |
|-------|-----------|---------|
| `G1`  | `AccF S φ → WithinF S φ` | nothing accessible lies outside `S` |
| `G3`  | `BSet S φ → AccF S φ` | beliefs are accessible |
| `W2E` | `WithinF S φ → ¬ AboutExt φ` | what is within does not reach outward |
| `ClW` | `(∀ψ, BSet S ψ → WithinF S ψ) → Cl S φ → WithinF S φ` | deduction does not escape the system |
| `J`   | `K S φ → Cl S φ` | knowledge lies in the closure of belief |

From these, `G2` (no belief is outward-reaching) and `L` (nothing outward-reaching is in the closure) are derived, and then `C1` and `Cor_God` follow under `[Nonempty Obj]`. `C1_within_omniscient` adds the hypothesis that `g` knows every formula within it and reaches the same conclusion, so the result is not explained by ignorance.

## Consistency

The axioms are jointly satisfiable, and not only by empty knowers. `M S φ := ¬ AboutExt φ` is a model in which every epistemic predicate is `M`. All five axioms hold, witnessed by the identity functions supplied in `model_blind`. In this model the system knows exactly the formulas that are not outward-reaching (`model_knows_iff`), including `Upos` (`model_knows_Upos`), so it is within-omniscient. `C1` applies and gives `¬ M g (U g)`. The conclusion holds for a coherent system that knows as much as the axioms permit, not because nothing satisfies the axioms.

## Creation

A staged ontology `Obj : Nat → Type`, with the same architecture `M` at every stage. `before_creation`: at a stage whose exterior is empty, the system knows `U g`. `after_creation`: at any stage whose exterior is inhabited, it cannot. Knowledge of aseity does not survive the first external object.

## Independence

Each axiom is needed. For each of the five there is a model over `Sys = Obj = Unit` in which the other four hold and `K () (U ())` is true (`without_G1` through `without_J`). No four of the axioms yield `C1`.

## Layers

The predicates `BSet`, `AccF`, and `WithinF` are distinct levels, not notational variants. `layers_strict` gives a model satisfying all five axioms in which some formula is accessible but not believed, and some formula is within but not accessible.

## Theorems

| Name | Statement |
|------|-----------|
| `aboutU_iff` | `AboutExt (U S) ↔ Nonempty Obj` aboutness = a live exterior |
| `hAboutU` | `AboutExt (U S)` under `[Nonempty Obj]` (the derived hinge) |
| `notAbout_Upos` | `¬ AboutExt (Upos S)` the positive form stays within |
| `G2`, `L` | the firewall, now lemmas |
| `C1` | `¬ K S (U S)` no system can know its own ungroundedness |
| `Cor_God` | `¬ K g (U g)` even God cannot certify his aseity |
| `C1_within_omniscient` | `¬ K g (U g)` even if `g` knows every within-formula |
| `God_cannot_believe_aseity` | `¬ BSet g (U g)` he cannot even hold it as a belief |
| `model_knows_iff`, `model_knows_Upos` | what the model `M` knows |
| `model_blind` | the axioms are jointly satisfied by `M`, which cannot know `U g` |
| `before_creation`, `after_creation` | the switch across the first inhabited stage |
| `without_G1` ... `without_J` | independence, one countermodel per axiom |
| `layers_strict` | belief, access, and within come apart |

`C1`, `Cor_God`, `C1_within_omniscient`, `God_cannot_believe_aseity`, `model_blind`, and `after_creation` carry `[Nonempty Obj]`; `G2`, `L`, and `before_creation` do not.

## Building / verifying

Requires a Lean 4 toolchain (tested on 4.31.0), e.g. via [elan](https://github.com/leanprover/elan). No dependencies.

```bash
lean Aseity.lean
```

The file ends with `#print axioms` checks covering every theorem above. Each reports no axioms. The development is fully constructive, using neither `sorry`, classical choice, nor `propext`. The only premises are the five named structural axioms and `[Nonempty Obj]` where listed, all visible in the source.

## License

MIT
