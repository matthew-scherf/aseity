# Aseity

[![DOI](https://zenodo.org/badge/1276846438.svg)](https://doi.org/10.5281/zenodo.20796492)

*A small, axiom-free Lean 4 formalisation of one result:*

> No sufficiently self-enclosed epistemic system can certify its own **aseity** - its being grounded in nothing external. Read theologically, with the system taken to be the maximal one: **even an omniscient God cannot certify that he is ungrounded**.

The theorem is *modally insensitive* to whether the system is in fact grounded. It concerns what can be **known from within**, not what is true, and is, therefore, an unknowability result, not a grounding result.

## The Paradox of Absolute Independence
Imagine a system, or an entity like God, that is completely self-sufficient. It has no external creator, no external causes, and nothing outside of it dictates its existence. In philosophy, this absolute independence is called Aseity.

This project presents a formal proof of a striking paradox: An absolutely independent entity can never actually know, or even believe, that it is independent.

## The Logic
The argument relies on a few simple, intuitive rules about boundaries, knowledge, and the world:

The Outer World: To claim "I am completely independent," you have to check the entire outside universe to ensure there is nothing out there causing or grounding you. This makes "independence" an outward-reaching fact.

The Inner Boundary: Your thoughts, beliefs, and knowledge live entirely inside you.

The Blind Spot: Because an entity’s internal thoughts cannot span or verify what lies strictly outside its own boundaries, it has a permanent blind spot. It can look at its internal state, but it cannot structurally verify the absence of external anchors.

## The Conclusion
It cannot know it is independent: Knowledge requires absolute structural certainty. Because the entity cannot verify the outer world from the inside, knowing its own total independence is a logical impossibility.

It cannot even believe it is independent: A rational entity's beliefs must stay within the bounds of what its internal systems can process. Claiming a truth about the infinite "outside" from a strictly closed "inside" breaks the rules of consistent belief.

In short, if you are a completely self-contained system, the one thing you are structurally blocked from proving is that nothing exists outside to contain you.

## The argument

Let `S` be an epistemic system and `g : Sys` the maximal ("global") one. Write `U S` for the proposition of `S`'s aseity, in its negative form:

```
U S  :=  ¬ ∃ x, (Ext x ∧ Grounds x S)        -- "nothing external grounds S"
```

`C1 : ¬ K S (U S)` - `S` cannot know `U S` - follows from the system being internally sealed: nothing it can reach lies outside it, its deductive closure never escapes it, and the boundary between it and any exterior is therefore not an object it can survey. Aseity is precisely a claim *about that boundary*, so it falls outside what the system can certify. For the maximal system this sharpens: `g` cannot even *hold* `U g` as a belief.

The closest structural rhyme is Gödel's second incompleteness theorem: a system strong enough to describe itself cannot certify its own foundational soundness.

## Aboutness

`AboutExt` is read as **realized reference**: a formula is about-the-external exactly when some object instantiates an occurrence of `Ext`. 

```lean
theorem aboutU_iff (S) : AboutExt (U S) ↔ Nonempty Obj
```

So aseity is outward-reaching exactly when the exterior is a live (non-empty) domain. Over a *provably empty* exterior, `U g` collapses to the triviality `¬∃x∈∅`, is no longer about-the-external, and the unknowability result correctly lapses: a triviality is knowable, even for an internalist God. The case the result targets is the live one: as long as anything exists, the ground of the totality cannot be certified from within it.


`Aseity.lean` is self-contained.

**Object language (concrete).** `Form` is an inductive syntax with an `Ext` atom and an object-indexed existential binder. `AboutExt : Form → Prop` is defined by recursion (the realized-reference reading above). `U S` is built as the literal `¬∃x (Ext x ∧ Grounds x S)`.


```lean
theorem hAboutU [Nonempty Obj] (S) : AboutExt (U S)
```

That aseity reaches past the boundary is the single claim the whole result turns on. It is *proved* from `aboutU_iff` together with a live exterior.

**Structural axioms** Five hypotheses encode maximal internality; the epistemic predicates `K`, `BSet`, `Cl`, `AccF`, `WithinF` are left opaque.

| Axiom | Statement | Reading |
|-------|-----------|---------|
| `G1`  | `AccF S φ → WithinF S φ` | nothing accessible lies outside `S` |
| `G3`  | `BSet S φ → AccF S φ` | beliefs are accessible |
| `W2E` | `WithinF S φ → ¬ AboutExt φ` | what is within does not reach outward |
| `ClW` | `(∀ψ, BSet S ψ → WithinF S ψ) → Cl S φ → WithinF S φ` | deduction does not escape the system |
| `J`   | `K S φ → Cl S φ` | knowledge lies in the closure of belief |

From these, `G2` (no belief is outward-reaching) and `L` (nothing outward-reaching is in the closure) are **derived**, and then `C1` and `Cor_God` follow under `[Nonempty Obj]`. 

## Theorems

| Name | Statement |
|------|-----------|
| `aboutU_iff` | `AboutExt (U S) ↔ Nonempty Obj` — aboutness = a live exterior |
| `hAboutU` | `AboutExt (U S)` under `[Nonempty Obj]` (the derived hinge) |
| `G2`, `L` | the firewall, now lemmas |
| `C1` | `¬ K S (U S)` — no system can know its own ungroundedness |
| `Cor_God` | `¬ K g (U g)` — even God cannot certify his aseity |
| `God_cannot_believe_aseity` | `¬ BSet g (U g)` — he cannot even hold it as a belief |

`C1`, `Cor_God`, and `God_cannot_believe_aseity` carry `[Nonempty Obj]`; `G2` and `L` do not.

## Building / verifying

Requires a Lean 4 toolchain (tested on **4.31.0**), e.g. via [elan](https://github.com/leanprover/elan). No dependencies.

```bash
lean Aseity.lean
```

The file ends with `#print axioms` checks. Each prints **"does not depend on any axioms"**: the development is fully constructive, using neither `sorry`, classical choice, nor `propext`. The only premises are the five named structural axioms and `[Nonempty Obj]`, all visible in the source.

## The assumptions

Two explicit assumptions carry the weight:

- **`ClW`  - deductive closure never reaches outside the system.** If inference *can* deliver a true outward-reaching proposition from inward-facing premises, the firewall breaks and the system may certify its aseity after all.
- **`[Nonempty Obj]` - the exterior is a live domain.** Mild ("some object exists"), but load-bearing and deliberately visible: drop it and `aboutU_iff` shows aseity ceases to be about-the-external, so the result lapses.

The formalisation does not settle these but it does isolate them. Read the result as conditional and diagnostic: *to the precise extent that closure stays within and an exterior is live, the question of a system's own ground is unposable from within.* 

## License

MIT 
