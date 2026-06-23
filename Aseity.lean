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

section
variable {Sys Obj : Type}

variable (K       : Sys → Form Sys Obj → Prop)   -- S knows φ
variable (BSet    : Sys → Form Sys Obj → Prop)   -- φ ∈ 𝔅_S (belief set)
variable (Cl      : Sys → Form Sys Obj → Prop)   -- φ ∈ Cl(𝔅_S) (closure)
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

variable [Nonempty Obj]   -- a live exterior; if empty, the question is trivial.

omit [Nonempty Obj] in
include G1 G3 W2E ClW in
theorem closure_is_interior (S : Sys) {φ : Form Sys Obj} (h : Cl S φ) : ¬ AboutExt φ :=
  fun hφ => L _ _ _ _ G1 G3 W2E ClW S hφ h

include G1 G3 W2E ClW J in
theorem cannot_know_ungrounded (S : Sys) : ¬ K S (U S) :=
  fun hK => L _ _ _ _ G1 G3 W2E ClW S (hAboutU S) (J S (U S) hK)

include G1 G3 W2E ClW J in
theorem cannot_know_grounded (S : Sys) : ¬ K S (Grounding S) :=
  fun hK => L _ _ _ _ G1 G3 W2E ClW S (hAboutGrounding S) (J S (Grounding S) hK)

include G1 G3 W2E ClW J in
theorem grounding_undeterminable (S : Sys) : ¬ (K S (U S) ∨ K S (Grounding S)) := by
  rintro (hK | hK)
  · exact L _ _ _ _ G1 G3 W2E ClW S (hAboutU S) (J S (U S) hK)
  · exact L _ _ _ _ G1 G3 W2E ClW S (hAboutGrounding S) (J S (Grounding S) hK)

include G1 G3 W2E in
theorem cannot_believe_either (S : Sys) : ¬ BSet S (U S) ∧ ¬ BSet S (Grounding S) :=
  ⟨fun h => G2 _ _ _ G1 G3 W2E S h (hAboutU S), fun h => G2 _ _ _ G1 G3 W2E S h (hAboutGrounding S)⟩

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
