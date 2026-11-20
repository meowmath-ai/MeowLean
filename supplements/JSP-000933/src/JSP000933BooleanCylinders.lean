import JSP000933CompleteValueMap
import JSP000933CCCCodes

namespace JSP000933
namespace CantorCodes

open BooleanCompletion OpenGraphForcing

abbrev Word := List Bool

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

def truthBit (b : Bool) : B := if b = true then ⊤ else ⊥

def literal (x : B) : Bool → B
  | false => xᶜ
  | true => x

def Agrees (x : RealCode) (w : Word) : Prop := ∀ i : Fin w.length, x i.val = w[i.val]

noncomputable def cylinderValue (x : ℕ → B) (w : Word) : B :=
  ⨅ i : Fin w.length, literal (x i.val) (w[i.val])

noncomputable def openValue (code : Word → B) (x : ℕ → B) : B :=
  ⨆ w : Word, code w ⊓ cylinderValue x w

noncomputable def colorValue (code : Word × Word → B) (x y : ℕ → B) : B :=
  ⨆ w : Word × Word, code w ⊓ (cylinderValue x w.1 ⊓ cylinderValue y w.2)

theorem literal_truthBit_r105 (a b : Bool) :
    (literal (truthBit a : B) b) = if a = b then ⊤ else ⊥ := by
  cases a <;> cases b <;> simp [truthBit,literal]

open scoped Classical in
theorem cylinderValue_truthBit_r105 (x : RealCode) (w : Word) :
    (cylinderValue (fun n => truthBit (x n)) w : B) =
      if Agrees x w then ⊤ else ⊥ := by
  classical
  unfold cylinderValue
  simp only [literal_truthBit_r105]
  by_cases h : Agrees x w
  · rw [ite_eq_left h]
    apply top_unique
    exact le_iInf (fun i => by rw [ite_eq_left (h i)] <;> exact le_rfl)
  · rw [ite_eq_right h]
    apply le_bot_iff.mp
    have hm : ∃ i : Fin w.length, x i.val ≠ w[i.val] := by
      by_contra hh
      exact h (fun i => by by_contra hne; exact hh ⟨i,hne⟩)
    obtain ⟨i,hi⟩ := hm
    exact (iInf_le (fun j : Fin w.length => if x j.val = w[j.val] then (⊤ : B) else ⊥) i).trans_eq
      (ite_eq_right hi)

theorem map_literal_r105 (F : CompleteValueMap B C) (x : B) (b : Bool) :
    F.toFun (literal x b) = literal (F.toFun x) b := by
  cases b
  · exact F.map_compl x
  · rfl

theorem map_cylinder_r105 (F : CompleteValueMap B C) (x : ℕ → B) (w : Word) :
    F.toFun (cylinderValue x w) = cylinderValue (fun n => F.toFun (x n)) w := by
  simp only [cylinderValue,F.map_iInf,map_literal_r105]

theorem map_openValue_r105 (F : CompleteValueMap B C) (code : Word → B) (x : ℕ → B) :
    F.toFun (openValue code x) =
      openValue (fun w => F.toFun (code w)) (fun n => F.toFun (x n)) := by
  simp only [openValue,F.map_iSup,F.map_inf,map_cylinder_r105]

theorem map_colorValue_r105 (F : CompleteValueMap B C) (code : Word × Word → B) (x y : ℕ → B) :
    F.toFun (colorValue code x y) =
      colorValue (fun w => F.toFun (code w)) (fun n => F.toFun (x n)) (fun n => F.toFun (y n)) := by
  simp only [colorValue,F.map_iSup,F.map_inf,map_cylinder_r105]

end CantorCodes
end JSP000933
