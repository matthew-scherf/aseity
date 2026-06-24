namespace Aseity

structure World (Sys Obj : Type) where
  Grounds    : Obj → Sys → Prop   -- interior: surveyed object x grounds S
  HasExt     : Sys → Prop         -- territory-fact: an exterior to S exists
  ExtGrounds : Sys → Prop         -- territory-fact: some exterior object grounds S

variable {Sys Obj : Type}

def Maximal (w : World Sys Obj) (S : Sys) : Prop := ¬ w.HasExt S

def Grounding (w : World Sys Obj) (S : Sys) : Prop := w.ExtGrounds S


def U (w : World Sys Obj) (S : Sys) : Prop := ¬ w.ExtGrounds S

def Ungrounded (w : World Sys Obj) (S : Sys) : Prop :=
  (∀ x, ¬ w.Grounds x S) ∧ ¬ w.ExtGrounds S

 def Indist (S : Sys) (w₁ w₂ : World Sys Obj) : Prop :=
  ∀ x, w₁.Grounds x S ↔ w₂.Grounds x S

def Knows (S : Sys) (w : World Sys Obj) (P : World Sys Obj → Prop) : Prop :=
  ∀ w', Indist S w w' → P w'


theorem indist_refl (S : Sys) (w : World Sys Obj) : Indist S w w := fun _ => Iff.rfl

theorem knows_true (S : Sys) (w : World Sys Obj) {P : World Sys Obj → Prop}
    (h : Knows S w P) : P w :=
  h w (indist_refl S w)

theorem knows_mono (S : Sys) (w : World Sys Obj) {P Q : World Sys Obj → Prop}
    (hPQ : ∀ w', P w' → Q w') (hP : Knows S w P) : Knows S w Q :=
  fun w' hInd => hPQ w' (hP w' hInd)

def setHasExt (w : World Sys Obj) (b : Prop) : World Sys Obj := { w with HasExt := fun _ => b }
def setExtGrounds (w : World Sys Obj) (b : Prop) : World Sys Obj := { w with ExtGrounds := fun _ => b }

theorem indist_setHasExt (S : Sys) (w : World Sys Obj) (b : Prop) :
    Indist S w (setHasExt w b) := fun _ => Iff.rfl

theorem indist_setExtGrounds (S : Sys) (w : World Sys Obj) (b : Prop) :
    Indist S w (setExtGrounds w b) := fun _ => Iff.rfl


theorem knows_no_interior_grounder (S : Sys) (w : World Sys Obj)
    (h : ∀ x, ¬ w.Grounds x S) :
    Knows S w (fun w' => ∀ x, ¬ w'.Grounds x S) := by
  intro w' hInd x hx
  exact h x ((hInd x).mpr hx)


theorem cannot_know_maximal (S : Sys) (w : World Sys Obj) :
    ¬ Knows S w (fun w' => Maximal w' S) := by
  intro hK
  have hMax : Maximal (setHasExt w True) S := hK _ (indist_setHasExt S w True)
  exact hMax trivial

theorem maximal_unknowable_even_when_true (S : Sys) (w : World Sys Obj)
    (hTrue : Maximal w S) :
    Maximal w S ∧ ¬ Knows S w (fun w' => Maximal w' S) :=
  ⟨hTrue, cannot_know_maximal S w⟩


example (S : Sys) (g : Obj → Sys → Prop) :
    Maximal (⟨g, fun _ => False, fun _ => False⟩ : World Sys Obj) S :=
  fun h => h


theorem cannot_know_grounding (S : Sys) (w : World Sys Obj) :
    ¬ Knows S w (fun w' => Grounding w' S) := by
  intro hK
  have h : Grounding (setExtGrounds w False) S := hK _ (indist_setExtGrounds S w False)
  exact h

theorem cannot_know_ungrounded (S : Sys) (w : World Sys Obj) :
    ¬ Knows S w (fun w' => U w' S) := by
  intro hK
  have h : U (setExtGrounds w True) S := hK _ (indist_setExtGrounds S w True)
  exact h trivial

theorem grounding_undeterminable (S : Sys) (w : World Sys Obj) :
    ¬ (Knows S w (fun w' => Grounding w' S) ∨ Knows S w (fun w' => U w' S)) := by
  rintro (h | h)
  · exact cannot_know_grounding S w h
  · exact cannot_know_ungrounded S w h

theorem relativized_known_absolute_unknown (S : Sys) (w : World Sys Obj)
    (clean : ∀ x, ¬ w.Grounds x S) :
    Knows S w (fun w' => ∀ x, ¬ w'.Grounds x S)
    ∧ ¬ Knows S w (fun w' => Ungrounded w' S) := by
  refine ⟨knows_no_interior_grounder S w clean, ?_⟩
  intro hK
  have h : Ungrounded (setExtGrounds w True) S := hK _ (indist_setExtGrounds S w True)
  exact h.2 trivial

end Aseity
