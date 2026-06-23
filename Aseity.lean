namespace Aseity

inductive Form (Sys Obj : Type) where
  | ext     : Obj → Form Sys Obj                    -- Ext x
  | grounds : Obj → Sys → Form Sys Obj              -- Grounds x S
  | neg     : Form Sys Obj → Form Sys Obj
  | and     : Form Sys Obj → Form Sys Obj → Form Sys Obj
  | exObj   : (Obj → Form Sys Obj) → Form Sys Obj   -- ∃ x, …

def AboutExt {Sys Obj : Type} : Form Sys Obj → Prop
  | .ext _       => True
  | .grounds _ _ => False
  | .neg φ       => AboutExt φ
  | .and φ ψ     => AboutExt φ ∨ AboutExt ψ
  | .exObj f     => ∃ x, AboutExt (f x)

def Grounding {Sys Obj : Type} (S : Sys) : Form Sys Obj :=
  .exObj (fun x => .and (.ext x) (.grounds x S))

def U {Sys Obj : Type} (S : Sys) : Form Sys Obj := .neg (Grounding S)

theorem about_grounding_iff {Sys Obj : Type} (S : Sys) :
    AboutExt (Grounding S : Form Sys Obj) ↔ Nonempty Obj := by
  simp only [Grounding, AboutExt]
  constructor
  · rintro ⟨x, _⟩; exact ⟨x⟩
  · rintro ⟨x⟩; exact ⟨x, Or.inl trivial⟩

theorem aboutU_iff {Sys Obj : Type} (S : Sys) :
    AboutExt (U S : Form Sys Obj) ↔ Nonempty Obj := by
  simp only [U, AboutExt]
  exact about_grounding_iff S

theorem hAboutGrounding {Sys Obj : Type} [Nonempty Obj] (S : Sys) :
    AboutExt (Grounding S : Form Sys Obj) :=
  (about_grounding_iff S).mpr inferInstance

theorem hAboutU {Sys Obj : Type} [Nonempty Obj] (S : Sys) :
    AboutExt (U S : Form Sys Obj) :=
  (aboutU_iff S).mpr inferInstance

/-- A bundle of the epistemic predicates and the structural axioms relating them,
for one fixed `Sys`/`Obj` pair. Replaces the earlier pattern of five separate
`variable`-bound predicates plus five separate `variable`-bound axioms, which had
to be threaded through every helper lemma by hand (and was easy to get wrong —
see the bug this superseded). Now every theorem just takes one `Ax : Frame Sys Obj`
and Lean includes it automatically, since it appears in the stated type. -/
structure Frame (Sys Obj : Type) where
  K       : Sys → Form Sys Obj → Prop   -- S knows φ
  BSet    : Sys → Form Sys Obj → Prop   -- φ ∈ 𝔅_S (belief set)
  Cl      : Sys → Form Sys Obj → Prop   -- φ ∈ Cl(𝔅_S) (closure)
  AccF    : Sys → Form Sys Obj → Prop   -- φ accessible to S
  WithinF : Sys → Form Sys Obj → Prop   -- φ within S
  G1  : ∀ S φ, AccF S φ → WithinF S φ                                  -- accessible ⟹ within
  G3  : ∀ S φ, BSet S φ → AccF S φ                                     -- beliefs are accessible
  W2E : ∀ S φ, WithinF S φ → ¬ AboutExt φ                               -- within ⟹ not outward-reaching
  ClW : ∀ S φ, (∀ ψ, BSet S ψ → WithinF S ψ) → Cl S φ → WithinF S φ    -- closure stays within
  J   : ∀ S φ, K S φ → Cl S φ                                          -- knowledge ⟹ in the closure

section
variable {Sys Obj : Type} (Ax : Frame Sys Obj)

theorem G2 (S : Sys) {φ : Form Sys Obj} (h : Ax.BSet S φ) : ¬ AboutExt φ :=
  Ax.W2E S φ (Ax.G1 S φ (Ax.G3 S φ h))

theorem L (S : Sys) {φ : Form Sys Obj} (hφ : AboutExt φ) : ¬ Ax.Cl S φ :=
  fun hcl => Ax.W2E S φ (Ax.ClW S φ (fun ψ hψ => Ax.G1 S ψ (Ax.G3 S ψ hψ)) hcl) hφ

variable [Nonempty Obj]   -- a live exterior; if empty, the question is trivial.

omit [Nonempty Obj] in
theorem closure_is_interior (S : Sys) {φ : Form Sys Obj} (h : Ax.Cl S φ) : ¬ AboutExt φ :=
  fun hφ => L Ax S hφ h

theorem cannot_know_ungrounded (S : Sys) : ¬ Ax.K S (U S) :=
  fun hK => L Ax S (hAboutU S) (Ax.J S (U S) hK)

theorem cannot_know_grounded (S : Sys) : ¬ Ax.K S (Grounding S) :=
  fun hK => L Ax S (hAboutGrounding S) (Ax.J S (Grounding S) hK)

theorem grounding_undeterminable (S : Sys) : ¬ (Ax.K S (U S) ∨ Ax.K S (Grounding S)) := by
  rintro (hK | hK)
  · exact L Ax S (hAboutU S) (Ax.J S (U S) hK)
  · exact L Ax S (hAboutGrounding S) (Ax.J S (Grounding S) hK)

theorem cannot_believe_either (S : Sys) : ¬ Ax.BSet S (U S) ∧ ¬ Ax.BSet S (Grounding S) :=
  ⟨fun h => G2 Ax S h (hAboutU S), fun h => G2 Ax S h (hAboutGrounding S)⟩

end
end Aseity

/- Sanity check: all theorems are axiom-free (depend only on the structural assumptions). -/
#print axioms Aseity.about_grounding_iff
#print axioms Aseity.aboutU_iff
#print axioms Aseity.G2
#print axioms Aseity.L
#print axioms Aseity.closure_is_interior
#print axioms Aseity.cannot_know_ungrounded
#print axioms Aseity.cannot_know_grounded
#print axioms Aseity.grounding_undeterminable
#print axioms Aseity.cannot_believe_either
