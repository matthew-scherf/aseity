# Aseity

[![DOI](https://zenodo.org/badge/1276846438.svg)](https://doi.org/10.5281/zenodo.20796492) 

---

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

All the theorems follow purely from the structural assumptions about belief, accessibility, interiority, and closure — no additional domain-specific axioms are required.

---

This translation preserves the full logical content while making it readable for philosophers, theologians, or epistemologists without a Lean background. The result is a clean, self-contained epistemic limit theorem concerning self-grounding and aseity.


## License

MIT 
