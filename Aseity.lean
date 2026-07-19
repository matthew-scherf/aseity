namespace Aseity


inductive Form (Sys Obj : Type) where
  | ext     : Obj → Form Sys Obj                    -- Ext x
  | grounds : Obj → Sys → Form Sys Obj              -- Grounds x S
  | neg     : Form Sys Obj → Form Sys Obj
  | and     : Form Sys Obj → Form Sys Obj → Form Sys Obj
  | exObj   : (Obj → Form Sys Obj) → Form Sys Obj   -- ∃ x, …

/- About-the-external = *realized* occurrence of `Ext` (reference, not bare sense):
   the existential clause asks for a witnessing object. -/
def AboutExt {Sys Obj : Type} : Form Sys Obj → Prop
  | .ext _       => True
  | .grounds _ _ => False
  | .neg φ       => AboutExt φ
  | .and φ ψ     => AboutExt φ ∨ AboutExt ψ
  | .exObj f     => ∃ x, AboutExt (f x)

/- Aseity of S, negative form:  ¬ ∃ x, (Ext x ∧ Grounds x S). -/
def U {Sys Obj : Type} (S : Sys) : Form Sys Obj :=
  .neg (.exObj (fun x => .and (.ext x) (.grounds x S)))

/- Aseity of S without the externality marker:  ¬ ∃ x, Grounds x S.
   Same groundlessness claim, but no realized reference to the exterior. -/
def Upos {Sys Obj : Type} (S : Sys) : Form Sys Obj :=
  .neg (.exObj (fun x => .grounds x S))

/- Term proof; no simp, no propext. -/
theorem aboutU_iff {Sys Obj : Type} (S : Sys) :
    AboutExt (U S : Form Sys Obj) ↔ Nonempty Obj :=
  ⟨fun h => match h with | ⟨x, _⟩ => ⟨x⟩,
   fun h => match h with | ⟨x⟩ => ⟨x, Or.inl trivial⟩⟩

theorem hAboutU {Sys Obj : Type} [Nonempty Obj] (S : Sys) :
    AboutExt (U S : Form Sys Obj) :=
  (aboutU_iff S).mpr inferInstance

/- The positive form never reaches outward, whatever the ontology. -/
theorem notAbout_Upos {Sys Obj : Type} (S : Sys) :
    ¬ AboutExt (Upos S : Form Sys Obj) :=
  fun h => match h with | ⟨_, hx⟩ => hx

section
variable {Sys Obj : Type}

variable (K       : Sys → Form Sys Obj → Prop)   -- S knows φ
variable (BSet    : Sys → Form Sys Obj → Prop)   -- φ ∈ 𝔅_S
variable (Cl      : Sys → Form Sys Obj → Prop)   -- φ ∈ Cl(𝔅_S)
variable (AccF    : Sys → Form Sys Obj → Prop)   -- φ accessible to S
variable (WithinF : Sys → Form Sys Obj → Prop)   -- φ within S

variable (G1  : ∀ S φ, AccF S φ → WithinF S φ)        -- accessible ⟹ within
variable (G3  : ∀ S φ, BSet S φ → AccF S φ)           -- beliefs are accessible
variable (W2E : ∀ S φ, WithinF S φ → ¬ AboutExt φ)    -- within ⟹ not outward-reaching
variable (ClW : ∀ S φ, (∀ ψ, BSet S ψ → WithinF S ψ) → Cl S φ → WithinF S φ)  -- closure stays within
variable (J   : ∀ S φ, K S φ → Cl S φ)                -- knowledge ⟹ in the closure

include G1 G3 W2E in
theorem G2 (S : Sys) {φ : Form Sys Obj} (h : BSet S φ) : ¬ AboutExt φ :=
  W2E S φ (G1 S φ (G3 S φ h))

include G1 G3 W2E ClW in
theorem L (S : Sys) {φ : Form Sys Obj} (hφ : AboutExt φ) : ¬ Cl S φ :=
  fun hcl => W2E S φ (ClW S φ (fun ψ hψ => G1 S ψ (G3 S ψ hψ)) hcl) hφ


variable [Nonempty Obj]

include G1 G3 W2E ClW J in
theorem C1 (S : Sys) : ¬ K S (U S) :=
  fun hK =>
    W2E S (U S)
      (ClW S (U S) (fun ψ hψ => G1 S ψ (G3 S ψ hψ)) (J S (U S) hK))
      (hAboutU S)

include G1 G3 W2E ClW J in
theorem Cor_God (g : Sys) : ¬ K g (U g) :=
  C1 K BSet Cl AccF WithinF G1 G3 W2E ClW J g

/- The blindness survives within-omniscience: even a system that knows
   every formula within it cannot know its own aseity. -/
include G1 G3 W2E ClW J in
theorem C1_within_omniscient (g : Sys)
    (_KAll : ∀ φ, WithinF g φ → K g φ) : ¬ K g (U g) :=
  C1 K BSet Cl AccF WithinF G1 G3 W2E ClW J g

include G1 G3 W2E in
theorem God_cannot_believe_aseity (g : Sys) : ¬ BSet g (U g) :=
  fun h => W2E g (U g) (G1 g (U g) (G3 g (U g) h)) (hAboutU g)

end

/- ## Consistency

`M` is the uniform internalist model: every epistemic predicate holds of
exactly the formulas that are not outward-reaching.  With all five
predicates set to `M`, every axiom holds, the system knows every
within-formula (it is within-omniscient), and `C1` applies.  So the
axioms are jointly satisfiable by a system that knows a great deal,
and the conclusion is not vacuous. -/

def M {Sys Obj : Type} : Sys → Form Sys Obj → Prop :=
  fun _ φ => ¬ AboutExt φ

section Model
variable {Sys Obj : Type}

/- What the model knows: exactly the non-outward-reaching formulas. -/
theorem model_knows_iff (S : Sys) (φ : Form Sys Obj) :
    M S φ ↔ ¬ AboutExt φ :=
  Iff.rfl

/- In particular it knows the positive form of its own aseity. -/
theorem model_knows_Upos (S : Sys) : M S (Upos S : Form Sys Obj) :=
  notAbout_Upos S

/- All five axioms hold with every predicate equal to `M`; the proofs are
   the lambdas below.  `C1` then yields blindness to the negative form. -/
theorem model_blind [Nonempty Obj] (g : Sys) :
    ¬ M g (U g : Form Sys Obj) :=
  C1 (K := M) (BSet := M) (Cl := M) (AccF := M) (WithinF := M)
    (fun _ _ h => h)        -- G1
    (fun _ _ h => h)        -- G3
    (fun _ _ h => h)        -- W2E
    (fun _ _ _ h => h)      -- ClW
    (fun _ _ h => h)        -- J
    g

end Model

/- ## Creation

A staged ontology `Obj : Nat → Type`.  The epistemic architecture `M` is
fixed across stages.  At a stage with an empty exterior the system knows
`U g`; at any stage with an inhabited exterior it cannot.  Knowledge of
aseity does not persist across the first creation. -/

section Creation
variable {Sys : Type} (Obj : Nat → Type) (g : Sys)

theorem before_creation (t : Nat) (empty : Obj t → False) :
    M g (U g : Form Sys (Obj t)) :=
  fun h => match (aboutU_iff g).mp h with | ⟨x⟩ => empty x

theorem after_creation (t : Nat) [Nonempty (Obj t)] :
    ¬ M g (U g : Form Sys (Obj t)) :=
  model_blind g

end Creation

/- ## Independence

Each axiom is needed for `C1`.  For each of the five, a model over
`Sys = Obj = Unit` in which the other four hold and `K () (U ())` is
true.  So no four of the axioms suffice. -/

section Independence

theorem without_G1 :
    ∃ (K BSet Cl AccF WithinF : Unit → Form Unit Unit → Prop),
      (∀ S φ, BSet S φ → AccF S φ) ∧
      (∀ S φ, WithinF S φ → ¬ AboutExt φ) ∧
      (∀ S φ, (∀ ψ, BSet S ψ → WithinF S ψ) → Cl S φ → WithinF S φ) ∧
      (∀ S φ, K S φ → Cl S φ) ∧
      K () (U ()) :=
  ⟨fun _ _ => True, fun _ _ => True, fun _ _ => True, fun _ _ => True,
   fun _ φ => ¬ AboutExt φ,
   fun _ _ _ => trivial,
   fun _ _ h => h,
   fun _ _ hb _ => (hb (.ext ()) trivial trivial).elim,
   fun _ _ _ => trivial,
   trivial⟩

theorem without_G3 :
    ∃ (K BSet Cl AccF WithinF : Unit → Form Unit Unit → Prop),
      (∀ S φ, AccF S φ → WithinF S φ) ∧
      (∀ S φ, WithinF S φ → ¬ AboutExt φ) ∧
      (∀ S φ, (∀ ψ, BSet S ψ → WithinF S ψ) → Cl S φ → WithinF S φ) ∧
      (∀ S φ, K S φ → Cl S φ) ∧
      K () (U ()) :=
  ⟨fun _ _ => True, fun _ _ => True, fun _ _ => True, fun _ _ => False,
   fun _ φ => ¬ AboutExt φ,
   fun _ _ h => h.elim,
   fun _ _ h => h,
   fun _ _ hb _ => (hb (.ext ()) trivial trivial).elim,
   fun _ _ _ => trivial,
   trivial⟩

theorem without_W2E :
    ∃ (K BSet Cl AccF WithinF : Unit → Form Unit Unit → Prop),
      (∀ S φ, AccF S φ → WithinF S φ) ∧
      (∀ S φ, BSet S φ → AccF S φ) ∧
      (∀ S φ, (∀ ψ, BSet S ψ → WithinF S ψ) → Cl S φ → WithinF S φ) ∧
      (∀ S φ, K S φ → Cl S φ) ∧
      K () (U ()) :=
  ⟨fun _ _ => True, fun _ _ => True, fun _ _ => True, fun _ _ => True,
   fun _ _ => True,
   fun _ _ _ => trivial,
   fun _ _ _ => trivial,
   fun _ _ _ _ => trivial,
   fun _ _ _ => trivial,
   trivial⟩

theorem without_ClW :
    ∃ (K BSet Cl AccF WithinF : Unit → Form Unit Unit → Prop),
      (∀ S φ, AccF S φ → WithinF S φ) ∧
      (∀ S φ, BSet S φ → AccF S φ) ∧
      (∀ S φ, WithinF S φ → ¬ AboutExt φ) ∧
      (∀ S φ, K S φ → Cl S φ) ∧
      K () (U ()) :=
  ⟨fun _ _ => True, fun _ φ => ¬ AboutExt φ, fun _ _ => True,
   fun _ φ => ¬ AboutExt φ, fun _ φ => ¬ AboutExt φ,
   fun _ _ h => h,
   fun _ _ h => h,
   fun _ _ h => h,
   fun _ _ _ => trivial,
   trivial⟩

theorem without_J :
    ∃ (K BSet Cl AccF WithinF : Unit → Form Unit Unit → Prop),
      (∀ S φ, AccF S φ → WithinF S φ) ∧
      (∀ S φ, BSet S φ → AccF S φ) ∧
      (∀ S φ, WithinF S φ → ¬ AboutExt φ) ∧
      (∀ S φ, (∀ ψ, BSet S ψ → WithinF S ψ) → Cl S φ → WithinF S φ) ∧
      K () (U ()) :=
  ⟨fun _ _ => True, fun _ φ => ¬ AboutExt φ, fun _ _ => False,
   fun _ φ => ¬ AboutExt φ, fun _ φ => ¬ AboutExt φ,
   fun _ _ h => h,
   fun _ _ h => h,
   fun _ _ h => h,
   fun _ _ _ h => h.elim,
   trivial⟩

end Independence

/- ## Layers

The three levels `BSet`, `AccF`, `WithinF` are not interchangeable.
A model over `Sys = Obj = Unit` in which all five axioms hold, some
formula is accessible but not believed, and some formula is within but
not accessible. -/

section Layers

abbrev f0 : Form Unit Unit := .grounds () ()
abbrev f1 : Form Unit Unit := .neg f0
abbrev f2 : Form Unit Unit := .neg f1

theorem notAbout_f0 : ¬ AboutExt f0 := fun h => h
theorem notAbout_f1 : ¬ AboutExt f1 := fun h => h
theorem notAbout_f2 : ¬ AboutExt f2 := fun h => h

theorem layers_strict :
    ∃ (K BSet Cl AccF WithinF : Unit → Form Unit Unit → Prop),
      (∀ S φ, AccF S φ → WithinF S φ) ∧
      (∀ S φ, BSet S φ → AccF S φ) ∧
      (∀ S φ, WithinF S φ → ¬ AboutExt φ) ∧
      (∀ S φ, (∀ ψ, BSet S ψ → WithinF S ψ) → Cl S φ → WithinF S φ) ∧
      (∀ S φ, K S φ → Cl S φ) ∧
      (AccF () f1 ∧ ¬ BSet () f1) ∧
      (WithinF () f2 ∧ ¬ AccF () f2) :=
  ⟨fun _ φ => φ = f0, fun _ φ => φ = f0,
   fun _ φ => φ = f0 ∨ φ = f1, fun _ φ => φ = f0 ∨ φ = f1,
   fun _ φ => ¬ AboutExt φ,
   fun _ _ h => h.elim (fun e => e ▸ notAbout_f0) (fun e => e ▸ notAbout_f1),
   fun _ _ h => Or.inl h,
   fun _ _ h => h,
   fun _ _ _ hc => hc.elim (fun e => e ▸ notAbout_f0) (fun e => e ▸ notAbout_f1),
   fun _ _ h => Or.inl h,
   ⟨Or.inr rfl, fun h => nomatch h⟩,
   ⟨notAbout_f2,
    fun h => h.elim (fun e => nomatch e) (fun e => nomatch e)⟩⟩

end Layers

end Aseity

#print axioms Aseity.aboutU_iff
#print axioms Aseity.hAboutU
#print axioms Aseity.notAbout_Upos
#print axioms Aseity.C1
#print axioms Aseity.Cor_God
#print axioms Aseity.C1_within_omniscient
#print axioms Aseity.God_cannot_believe_aseity
#print axioms Aseity.model_knows_Upos
#print axioms Aseity.model_blind
#print axioms Aseity.before_creation
#print axioms Aseity.after_creation
#print axioms Aseity.without_G1
#print axioms Aseity.without_G3
#print axioms Aseity.without_W2E
#print axioms Aseity.without_ClW
#print axioms Aseity.without_J
#print axioms Aseity.layers_strict
