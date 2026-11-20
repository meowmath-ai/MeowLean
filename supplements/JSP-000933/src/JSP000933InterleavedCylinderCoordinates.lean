import JSP000933ActualClosedSampleTreeCode
import Mathlib.Tactic.FinCases

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def quadWordProjection (u : Word) (i : Fin 4) : Word :=
  List.ofFn (n := (u.length+3-i.val)/4) (fun m =>
    u[4*m.val+i.val]'(by have hm := m.isLt; have hi := i.isLt; omega))

@[simp] theorem quadWordProjection_length_r275 (u : Word) (i : Fin 4) :
    (quadWordProjection u i).length=(u.length+3-i.val)/4 := List.length_ofFn

theorem quadProjection_valid_r275 (u : Word) (i : Fin 4) (m : ℕ)
    (hm : m<(quadWordProjection u i).length) : 4*m+i.val<u.length := by
  rw [quadWordProjection_length_r275] at hm
  have hi := i.isLt
  omega

theorem quadWordProjection_bit_r275 (u : Word) (i : Fin 4) (m : ℕ)
    (hm : m<(quadWordProjection u i).length) :
    (quadWordProjection u i)[m]'hm = u[4*m+i.val]'(quadProjection_valid_r275 u i m hm) := by
  simp only [quadWordProjection,List.getElem_ofFn]

theorem interleave4_bit_r275 (x : Fin 4 → ℕ → B) (i : Fin 4) (m : ℕ) :
    interleave4 x (4*m+i.val)=x i m :=
  congrFun (extract4_interleave4_r240 x i) m

theorem cylinderValue_interleave4_r275 (x : Fin 4 → ℕ → B) (u : Word) :
    cylinderValue (interleave4 x) u=⨅ i : Fin 4, cylinderValue (x i) (quadWordProjection u i) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    unfold cylinderValue
    apply le_iInf
    intro m
    let n : Fin u.length := ⟨4*m.val+i.val,quadProjection_valid_r275 u i m.val m.isLt⟩
    have h₁ : interleave4 x n.val=x i m.val := interleave4_bit_r275 x i m.val
    have h₂ : u[n.val]'n.isLt = (quadWordProjection u i)[m.val]'m.isLt :=
      (quadWordProjection_bit_r275 u i m.val m.isLt).symm
    exact (iInf_le _ n).trans_eq (congrArg₂ literal h₁ h₂)
  · unfold cylinderValue
    apply le_iInf
    intro n
    let i : Fin 4 := ⟨n.val%4,Nat.mod_lt _ (by decide)⟩
    have hm : n.val/4<(quadWordProjection u i).length := by
      rw [quadWordProjection_length_r275]
      have h := n.isLt
      dsimp only [i]
      omega
    let m : Fin (quadWordProjection u i).length := ⟨n.val/4,hm⟩
    let n' : Fin u.length := ⟨4*m.val+i.val,quadProjection_valid_r275 u i m.val m.isLt⟩
    have he : n'=n := by
      apply Fin.ext
      change 4 * (n.val / 4) + n.val % 4 = n.val
      omega
    have h₁ : x i m.val=interleave4 x n.val :=
      (interleave4_bit_r275 x i m.val).symm.trans (congrArg (fun j : Fin u.length => interleave4 x j.val) he)
    have h₂ : (quadWordProjection u i)[m.val]'m.isLt = u[n.val]'n.isLt :=
      (quadWordProjection_bit_r275 u i m.val m.isLt).trans
        (congrArg (fun j : Fin u.length => u[j.val]'j.isLt) he)
    exact (((iInf_le _ i).trans (iInf_le _ m))).trans_eq (congrArg₂ literal h₁ h₂)

theorem cylinderValue_crossQuad_r275 (a b c d : ℕ → B) (u : Word) :
    cylinderValue (interleaveCrossQuad a b c d) u =
      (cylinderValue a (quadWordProjection u 0)⊓cylinderValue c (quadWordProjection u 2))⊓
        (cylinderValue b (quadWordProjection u 1)⊓cylinderValue d (quadWordProjection u 3)) := by
  let f : Fin 4 → ℕ → B := fun i => if i=0 then a else if i=1 then b else if i=2 then c else d
  change cylinderValue (interleave4 f) u=_
  rw [cylinderValue_interleave4_r275]
  have h₀ : f 0=a := rfl
  have h₁ : f 1=b := rfl
  have h₂ : f 2=c := rfl
  have h₃ : f 3=d := rfl
  apply le_antisymm
  · exact le_inf (le_inf ((iInf_le _ 0).trans_eq (congrArg (fun x => cylinderValue x (quadWordProjection u 0)) h₀))
      ((iInf_le _ 2).trans_eq (congrArg (fun x => cylinderValue x (quadWordProjection u 2)) h₂)))
      (le_inf ((iInf_le _ 1).trans_eq (congrArg (fun x => cylinderValue x (quadWordProjection u 1)) h₁))
        ((iInf_le _ 3).trans_eq (congrArg (fun x => cylinderValue x (quadWordProjection u 3)) h₃)))
  · apply le_iInf
    intro i
    fin_cases i
    · change _ ≤ cylinderValue (f 0) (quadWordProjection u 0)
      rw [h₀]
      exact inf_le_left.trans inf_le_left
    · change _ ≤ cylinderValue (f 1) (quadWordProjection u 1)
      rw [h₁]
      exact inf_le_right.trans inf_le_left
    · change _ ≤ cylinderValue (f 2) (quadWordProjection u 2)
      rw [h₂]
      exact inf_le_left.trans inf_le_right
    · change _ ≤ cylinderValue (f 3) (quadWordProjection u 3)
      rw [h₃]
      exact inf_le_right.trans inf_le_right

end SetLanguage
end JSP000933
