import JSP000933ActualRegularLexPrefixes

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem meetCylinder_bounded_r287 (a : ℕ → B) (u : Word) :
    BoundedBitLocal u.length (fun x => cylinderValue (bitsMeet a x) u) := by
  intro p x y h
  apply mask_cylinder_bounded_r278 u
  intro m hm
  exact mask_inf_congr_r126 rfl (h m hm)

noncomputable def meetInputCylinderCode (a : ℕ → B) (u : Word) : Word → B :=
  boundedTestOpenCode u.length (fun x => cylinderValue (bitsMeet a x) u)

theorem meetInputCylinderCode_value_r287 (a x : ℕ → B) (u : Word) :
    openValue (meetInputCylinderCode a u) x=cylinderValue (bitsMeet a x) u :=
  boundedTestOpenCode_value_r278 u.length _ (meetCylinder_bounded_r287 a u) x

noncomputable def meetInputBinaryCode (K : Word × Word → B) (a : ℕ → B) (uv : Word × Word) : B :=
  ⨆ u : Word, K (u,uv.2)⊓meetInputCylinderCode a u uv.1

theorem meetInputBinaryCode_value_r287 (K : Word × Word → B) (a x z : ℕ → B) :
    colorValue (meetInputBinaryCode K a) x z=colorValue K (bitsMeet a x) z := by
  unfold colorValue meetInputBinaryCode
  simp only [iSup_inf_eq]
  apply le_antisymm
  · apply iSup_le
    intro rv
    apply iSup_le
    intro u
    apply le_iSup_of_le (u,rv.2)
    have hC : meetInputCylinderCode a u rv.1⊓cylinderValue x rv.1≤cylinderValue (bitsMeet a x) u :=
      (le_iSup (fun r => meetInputCylinderCode a u r⊓cylinderValue x r) rv.1).trans_eq
        (meetInputCylinderCode_value_r287 a x u)
    exact le_inf (inf_le_left.trans inf_le_left)
      (le_inf ((le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_left)).trans hC)
        (inf_le_right.trans inf_le_right))
  · apply iSup_le
    rintro ⟨u,v⟩
    rw [← meetInputCylinderCode_value_r287 a x u]
    unfold openValue
    rw [iSup_inf_eq,inf_iSup_eq]
    apply iSup_le
    intro r
    exact le_iSup_of_le (r,v) (le_iSup_of_le u
      (le_inf (le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_left)))
        (le_inf (inf_le_right.trans (inf_le_left.trans inf_le_right)) (inf_le_right.trans inf_le_right))))

end SetLanguage
end JSP000933
