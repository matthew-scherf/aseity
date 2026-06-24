# Aseity

[![DOI](https://zenodo.org/badge/1276846438.svg)](https://doi.org/10.5281/zenodo.20796492) 

---

A formalization in [Lean 4](https://lean-lang.org/) of an epistemic limit on self-knowledge of one's own maximality. The central result is constructive and depends on no axioms: the impossibility is a structural consequence of how knowledge relates to a knower's interior.

---

## Abstract

We model a knower `S` whose epistemic access is confined to its *interior*, meaning the facts it can survey. A *world* additionally fixes two *territory facts* that lie beyond any possible survey: whether an exterior to `S` exists, and whether some exterior object grounds `S`. Knowledge is defined in the standard possible-worlds manner as truth across all worlds indistinguishable to `S`, where indistinguishability is agreement on interior data alone.

From this we derive:

- **Factivity and deductive closure** of knowledge come for free (`knows_true`, `knows_mono`); they need not be posited.
- **Maximality is unknowable** (`cannot_know_maximal`): for every world, `S` cannot know that it has no exterior, *even in the world where it in fact has none* (`maximal_unknowable_even_when_true`).
- **The grounding question is undecidable for `S`** (`grounding_undeterminable`): `S` can affirm neither that an exterior grounds it nor that none does.
- **The relativized/absolute split** (`relativized_known_absolute_unknown`): `S` *can* know the relativized universal "nothing I survey grounds me," yet *cannot* know the absolute "nothing grounds me at all."

The governing intuition is that *even knowledge identical to one's own being can supply no distinction that has no internal correlate.* A genuinely maximal interior and a boundedly-blind interior are interior-identical; knowledge supervenes on the interior; therefore knowledge cannot discriminate them.

---

## Plain-language interpretation

Imagine you are mapping the world from the inside, and the only things you can ever check are the things on your map. Now ask: *is my map complete — is there nothing at all beyond its edges?*

The argument says you can never **know** the answer is yes. Consider two situations. In the first, your map really is complete: there is nothing outside it. In the second, there *is* something outside, but, being outside, it is exactly the kind of thing you cannot reach to check. From the inside, these two situations look **identical**. Every observation you could make comes out the same in both. So no amount of looking, however thorough, tells you which one you are in.

This is why the limit doesn't disappear for a perfect or all-powerful knower. The missing fact isn't hidden in some hard-to-reach corner that a stronger mind could finally inspect. There is simply **no internal sign** that distinguishes "there is nothing outside" from "there is something outside that I can't detect." A distinction with no inner correlate can't be known by any inner act of knowing, not even by a being whose knowledge is identical with its own existence.

Two clarifications:

- It is **not** that you can't map the world. You can, and the map can even happen to be perfectly complete. What you can't do is *certify* that completeness from within.
- The catch is in a quiet shift of quantifier. "There are no unicorns in my experience" is a claim about what you've surveyed, and you can know it. "Unicorns don't exist" drops the qualifier and claims something about *everything*, surveyed or not,  and that step is exactly the one no survey can license. You may be entirely right, but you cannot know that you are.

Applied to theology, *aseity* is the classical attribute of existing from oneself, depending on nothing external. The argument is that even a maximal being cannot **know** its own maximality by surveying, because being the whole and merely failing to find an edge are, from the inside, the same.

---

## The formal model

The development lives in `Aseity.lean`. The whole apparatus is four definitions.

A **world** records what `S` can survey and what it cannot:

```lean
structure World (Sys Obj : Type) where
  Grounds    : Obj → Sys → Prop   -- interior: surveyed object x grounds S
  HasExt     : Sys → Prop         -- territory-fact: an exterior to S exists
  ExtGrounds : Sys → Prop         -- territory-fact: some exterior object grounds S
```

**Indistinguishability** is agreement on interior data only — the territory facts are deliberately excluded:

```lean
def Indist (S : Sys) (w₁ w₂ : World Sys Obj) : Prop :=
  ∀ x, w₁.Grounds x S ↔ w₂.Grounds x S
```

**Knowledge** is truth across every indistinguishable world (an S5-style necessity):

```lean
def Knows (S : Sys) (w : World Sys Obj) (P : World Sys Obj → Prop) : Prop :=
  ∀ w', Indist S w w' → P w'
```

The target propositions, all fully `S`-relative:

```lean
def Maximal    (w : World Sys Obj) (S : Sys) : Prop := ¬ w.HasExt S          -- map = territory
def Grounding  (w : World Sys Obj) (S : Sys) : Prop := w.ExtGrounds S         -- grounded by an exterior
def U          (w : World Sys Obj) (S : Sys) : Prop := ¬ w.ExtGrounds S       -- no exterior grounder
def Ungrounded (w : World Sys Obj) (S : Sys) : Prop :=                        -- absolute: nothing grounds S
  (∀ x, ¬ w.Grounds x S) ∧ ¬ w.ExtGrounds S
```

---

## Results

| Lean name | Statement | Reading |
|---|---|---|
| `knows_true` | `Knows S w P → P w` | Knowledge is factive (derived, not assumed). |
| `knows_mono` | `(∀ w', P w' → Q w') → Knows S w P → Knows S w Q` | Deductive closure is free. |
| `knows_no_interior_grounder` | clean interior `→ Knows S w (∀ x, ¬ Grounds x S)` | The *relativized* universal is knowable. |
| `cannot_know_maximal` | `¬ Knows S w (Maximal · S)` | The map is never known to be the territory. |
| `maximal_unknowable_even_when_true` | `Maximal w S → (Maximal w S ∧ ¬ Knows …)` | Unknowable even where true. |
| `cannot_know_grounding` / `cannot_know_ungrounded` | `¬ Knows …` | Neither horn of the grounding question is knowable. |
| `grounding_undeterminable` | `¬ (Knows … Grounding ∨ Knows … U)` | The aseity question is closed to `S`. |
| `relativized_known_absolute_unknown` | `Knows (relativized) ∧ ¬ Knows (absolute)` | The unicorn split, made literal. |

The mechanism in every impossibility result is the same: a world's *interior twin* (`indist_setHasExt`, `indist_setExtGrounds`) toggles a territory fact while leaving the surveyed data, and, hence, `Indist` untouched. Knowledge, being quantified over indistinguishable worlds, cannot see the toggle.

---

## The assumption

**`S`'s epistemic state supervenes on its interior.** Formally, this is the exclusion of `HasExt` and `ExtGrounds` from `Indist`. Everything else (factivity, closure, the impossibilities) follows.

This is also the only place the thesis can be resisted. A classical theist may claim a non-survey species of self-knowledge: God knows its maximality not by *looking for* an exterior but by *being* the ground in which any exterior would have to subsist. Granting such constitutive, non-discriminative knowledge would exempt the totality from the result. The formalization denies this by construction.

---

## A deliberate modeling choice

The exterior is represented as an opaque, `S`-relative *bit* (`HasExt`, `ExtGrounds`), **not** as a predicate `ExtTo : Obj → Sys → Prop` over named objects. Naming exterior objects within `S`'s own domain would hand `S` a survey of the exterior which is the census the thesis denies it can perform. Modeling the exterior as an unquantifiable surplus is therefore not a convenience but a faithfulness condition.

---

## Verifying

The proof is checked by the Lean kernel.

```bash
# install the Lean toolchain manager (once)
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y

# check the development (pinned to Lean 4.31.0; no Mathlib required)
lean Aseity.lean        # silent exit 0 == verified
```

To confirm the results rest on nothing but the definitions, append `#print axioms Aseity.cannot_know_maximal` (and siblings) inside the namespace; each reports *"does not depend on any axioms."*

---

## Status and scope

This is a compact philosophical model, not a theory of knowledge in full. It isolates one phenomenon, namely the in-principle unknowability of one's own boundary, and shows it follows from interior-supervenience alone. It does not model graded confidence, testimony, time, or the internal structure of representation; those are natural extensions. Counterarguments should target the supervenience commitment.

### Aseity: A Formal Epistemic Argument

We work within a general framework involving two types:
- `Sys`: systems (e.g., minds, agents, epistemic subjects, or ontological systems).
- `Obj`: external objects or entities in the "exterior" world.

#### 1. The Language of Forms
A **form** (formula) is built from the following constructors:

- `Ext x` — "Object `x` exists in the exterior."
- `Grounds x S` — "Object `x` is grounded in (dependent on, explained by, sustained by) system `S`."
- `¬φ` — negation of φ.
- `φ ∧ ψ` — conjunction of φ and ψ.
- `∃x. φ(x)` — existential quantification over objects.

#### 2. "About the Exterior" (Outward-Reaching Formulas)
We define a predicate `AboutExt φ`, which is true when the formula φ makes a claim that reaches out to the external world:

- `Ext x` is about the exterior.
- `Grounds x S` is *not* about the exterior (it is internal to the system).
- `¬φ` is about the exterior exactly when φ is.
- `φ ∧ ψ` is about the exterior if *either* φ or ψ is.
- `∃x. φ(x)` is about the exterior if there exists some `x` such that `φ(x)` is.

#### 3. Key Formulas
- **Grounding of S**: `Grounding S` means  
  "There exists an external object `x` such that `x` is grounded in S."  
  (i.e., S depends on something outside itself.)

- **Ungrondedness / Aseity of S**: `U S` means  
  "It is not the case that S has external grounding"  
  (i.e., S is self-existent, independent, has *aseity*).

#### 4. Basic Logical Facts
- `Grounding S` is about the exterior if and only if there exists at least one possible external object (`Nonempty Obj`).
- Similarly, `U S` is about the exterior under the same condition.

(If the exterior is empty, the entire question becomes trivial.)

---

### Epistemic and Doxastic Structure

We assume the following notions for each system `S`:

- `BSet S φ` — φ belongs to the **belief set** of S.
- `Cl S φ` — φ belongs to the **deductive closure** of S’s belief set.
- `K S φ` — S **knows** φ.
- `AccF S φ` — φ is **accessible** to S.
- `WithinF S φ` — φ is **internal** / "within" S.

#### Structural Assumptions (Plausible Constraints)
- **G1**: If a form is accessible to S, then it is within S.  
  (Accessibility implies interiority.)
- **G3**: If φ is in S’s belief set, then it is accessible to S.  
  (Beliefs are accessible.)
- **W2E** ("Within implies not About Exterior"): If φ is within S, then φ is *not* about the exterior.  
  (Nothing fully internal to S can make claims that genuinely reach outside S.)
- **ClW**: The deductive closure of beliefs that are all within S remains within S.  
  (Closure respects the interior boundary.)
- **J**: If S knows φ, then φ is in the deductive closure of S’s beliefs.  
  (Knowledge implies closure.)

---

### Main Theorems

**G2**: If φ is in S’s belief set, then φ is *not* about the exterior.  
(You cannot believe outward-reaching claims.)

**L**: If φ is about the exterior, then φ is *not* in the deductive closure of S’s beliefs.  
(The closure of your beliefs cannot contain any outward-reaching content.)

**Closure is Interior**: For any φ in the deductive closure of S’s beliefs, φ is not about the exterior.

---

### The Central Results

Assuming there is a nonempty exterior world (`Nonempty Obj`):

- **S cannot know its own aseity**:  
  `¬ K S (U S)`  
  (S cannot know that it is ungrounded / self-existent.)

- **S cannot know that it is grounded**:  
  `¬ K S (Grounding S)`  
  (S cannot know that it depends on something external.)

- **Grounding is undeterminable**:  
  `¬ (K S (U S) ∨ K S (Grounding S))`  
  (S cannot know *either* whether it has external grounding or whether it possesses aseity.)

- **S cannot even believe either proposition**:  
  Neither `U S` nor `Grounding S` can belong to S’s belief set.

---

### Summary in Plain English

Any system S is structurally incapable of knowing (or even believing) whether it is self-existent (has aseity) or whether it is grounded in something external.  

This limitation arises because:
1. All of S’s beliefs and knowledge must remain *within* S.
2. Any statement that asserts or denies external grounding is *about the exterior*.
3. Nothing that is fully "within" S can be genuinely about the exterior (the boundary condition `W2E`).

Therefore, the question of its own ontological grounding lies beyond the epistemic reach of any system from the inside. The very nature of interiority prevents the system from settling this foundational metaphysical issue about itself.

All the theorems follow purely from the structural assumptions about belief, accessibility, interiority, and closure and no additional domain-specific axioms are required.

---

## License

MIT 
