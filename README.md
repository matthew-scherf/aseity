# Aseity

*A small, axiom-free Lean 4 formalisation of one result:*

> No sufficiently self-enclosed epistemic system can certify its own **aseity** — its being grounded in nothing external. Read theologically, with the system taken to be the maximal one: **even an omniscient God cannot certify that he is ungrounded.**

The theorem is *modally insensitive* to whether the system is in fact grounded. It concerns what can be **known from within**, not what is true — an unknowability result, not a grounding result.

## The argument

Let `S` be an epistemic system and `g : Sys` the maximal ("global") one. Write `U S` for the proposition of `S`'s aseity, in its negative form:

```
U S  :=  ¬ ∃ x, (Ext x ∧ Grounds x S)        -- "nothing external grounds S"
```

`C1 : ¬ K S (U S)` — `S` cannot know `U S` — follows from the system being internally sealed: nothing it can reach lies outside it, its deductive closure never escapes it, and the boundary between it and any exterior is therefore not an object it can survey. Aseity is precisely a claim *about that boundary*, so it falls outside what the system can certify. For the maximal system this sharpens further: `g` cannot even *hold* `U g` as a belief.

The closest structural rhyme is Gödel's second incompleteness theorem: a system strong enough to describe itself cannot certify its own foundational soundness — consistency there, aseity here.

## What's in the file

`Aseity.lean` is self-contained — plain Lean 4, no Mathlib. It has three layers.

**Object language (concrete).** `Form` is an inductive syntax with an `Ext` atom and an object-indexed existential binder. `AboutExt : Form → Prop` is defined by recursion: a formula is *about the external* exactly when `Ext` occurs in it. `U S` is built as the literal `¬∃x (Ext x ∧ Grounds x S)`.

**The hinge — derived, not assumed.**

```lean
theorem hAboutU : AboutExt (U S)
```

That aseity reaches past the system's boundary is the single claim the whole result turns on. Here it is *proved* from the structure of the formula rather than postulated.

**Structural axioms — the only assumptions.** Five hypotheses encode maximal internality; the epistemic predicates `K`, `BSet`, `Cl`, `AccF`, `WithinF` are left opaque.

| Axiom | Statement | Reading |
|-------|-----------|---------|
| `G1`  | `AccF S φ → WithinF S φ` | nothing accessible lies outside `S` |
| `G3`  | `BSet S φ → AccF S φ` | beliefs are accessible |
| `W2E` | `WithinF S φ → ¬ AboutExt φ` | what is within does not reach outward |
| `ClW` | `(∀ψ, BSet S ψ → WithinF S ψ) → Cl S φ → WithinF S φ` | deduction does not escape the system |
| `J`   | `K S φ → Cl S φ` | knowledge lies in the closure of belief |

From these, `G2` (no belief is outward-reaching) and `L` (nothing outward-reaching is in the closure) are **derived**, and then `C1` follows. An earlier draft took `G2` and `L` as primitives; promoting the internality structure and deriving them instead is what keeps the argument from quietly assuming its own conclusion.

## Theorems

| Name | Statement |
|------|-----------|
| `hAboutU` | `AboutExt (U S)` — aseity is about-the-external (the derived hinge) |
| `G2`, `L` | the firewall, now lemmas |
| `C1` | `¬ K S (U S)` — no system can know its own ungroundedness |
| `Cor_God` | `¬ K g (U g)` — even God cannot certify his aseity |
| `God_cannot_believe_aseity` | `¬ BSet g (U g)` — he cannot even hold it as a belief |

## Building / verifying

Requires a Lean 4 toolchain (tested on **4.31.0**), e.g. via [elan](https://github.com/leanprover/elan). No dependencies.

```bash
lean Aseity.lean
```

The file ends with `#print axioms` checks. Each prints **"does not depend on any axioms"**: the development is fully constructive, using neither `sorry`, classical choice, nor `propext`. The only premises are the five named structural axioms, all visible in the source.

## The one assumption worth arguing about

The verdict is honest only because the assumptions are explicit. Four of the five axioms are close to definitional bookkeeping; the weight is carried by **`ClW` — that deductive closure never reaches outside the system.** This is exactly where realism pushes back: if inference *can* deliver a true outward-reaching proposition from inward-facing premises, the firewall breaks and the system may certify its aseity after all.

The formalisation does not settle this — it isolates it. Read the result as conditional and diagnostic: *to the precise extent that `ClW` holds, the question of a system's own ground becomes unposable from within.* Not a settled fact about minds, or about God.

## License

MIT (or your choice) — edit as appropriate.
