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

/- Aseity of S:  ¬ ∃ x, (Ext x ∧ Grounds x S). -/
def U {Sys Obj : Type} (S : Sys) : Form Sys Obj :=
  .neg (.exObj (fun x => .and (.ext x) (.grounds x S)))

theorem aboutU_iff {Sys Obj : Type} (S : Sys) :
    AboutExt (U S : Form Sys Obj) ↔ Nonempty Obj := by
  simp only [U, AboutExt]
  constructor
  · rintro ⟨x, _⟩; exact ⟨x⟩
  · rintro ⟨x⟩; exact ⟨x, Or.inl trivial⟩

theorem hAboutU {Sys Obj : Type} [Nonempty Obj] (S : Sys) :
    AboutExt (U S : Form Sys Obj) :=
  (aboutU_iff S).mpr inferInstance

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
  fun hK =>
    W2E g (U g)
      (ClW g (U g) (fun ψ hψ => G1 g ψ (G3 g ψ hψ)) (J g (U g) hK))
      (hAboutU g)

include G1 G3 W2E in
theorem God_cannot_believe_aseity (g : Sys) : ¬ BSet g (U g) :=
  fun h => W2E g (U g) (G1 g (U g) (G3 g (U g) h)) (hAboutU g)

end
end Aseity

#print axioms Aseity.aboutU_iff
#print axioms Aseity.hAboutU
#print axioms Aseity.C1
#print axioms Aseity.Cor_God
#print axioms Aseity.God_cannot_believe_aseity
