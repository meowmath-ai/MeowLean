import JSP000933CantorTopology

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def groundOpenCode (U : Set RealCode) (w : Word) : Bool := by
  classical
  exact decide (cylinder w ⊆ U)

theorem groundOpenCode_iff_r107 [TopologicalSpace Bool] [DiscreteTopology Bool]
    (U : Set RealCode) (hU : IsOpen U) (x : RealCode) :
    GroundOpen (groundOpenCode U) x ↔ x ∈ U := by
  classical
  constructor
  · rintro ⟨w,hw,hx⟩
    exact (show cylinder w ⊆ U from of_decide_eq_true hw) hx
  · intro h
    obtain ⟨w,hx,hw⟩ := isOpen_exists_cylinder_r106 U hU x h
    exact ⟨w,decide_eq_true hw,hx⟩

open scoped Classical in
theorem groundOpen_truth_r107 (code : Word → Bool) (x : RealCode) :
    (openValue (fun w => truthBit (code w)) (fun n => truthBit (x n)) : B) =
      if GroundOpen code x then ⊤ else ⊥ := by
  classical
  by_cases hx : GroundOpen code x
  · rw [ite_eq_left hx,openValue]
    apply top_unique
    obtain ⟨w,hw,ha⟩ := hx
    apply le_iSup_of_le w
    rw [cylinderValue_truthBit_r105]
    simp [truthBit,hw,ha]
  · rw [ite_eq_right hx,openValue]
    apply le_bot_iff.mp
    apply iSup_le
    intro w
    by_cases hw : code w = true
    · have hNo : ¬ Agrees x w := fun h => hx ⟨w,hw,h⟩
      rw [cylinderValue_truthBit_r105]
      simp [truthBit,hw,hNo]
    · simp [truthBit,hw]

open scoped Classical in
theorem groundColor_truth_r107 (code : Word × Word → Bool) (x y : RealCode) :
    (colorValue (fun w => truthBit (code w)) (fun n => truthBit (x n))
      (fun n => truthBit (y n)) : B) = if GroundColor code x y then ⊤ else ⊥ := by
  classical
  by_cases hxy : GroundColor code x y
  · rw [ite_eq_left hxy,colorValue]
    apply top_unique
    obtain ⟨w,hw,hx,hy⟩ := hxy
    apply le_iSup_of_le w
    simp only [cylinderValue_truthBit_r105]
    simp [truthBit,hw,hx,hy]
  · rw [ite_eq_right hxy,colorValue]
    apply le_bot_iff.mp
    apply iSup_le
    intro w
    by_cases hw : code w = true
    · by_cases hx : Agrees x w.1
      · have hy : ¬ Agrees y w.2 := fun hy => hxy ⟨w,hw,hx,hy⟩
        simp only [cylinderValue_truthBit_r105]
        simp [truthBit,hw,hx,hy]
      · simp only [cylinderValue_truthBit_r105]
        simp [truthBit,hw,hx]
    · simp [truthBit,hw]

theorem groundOpenCode_complement_iff_r107 [TopologicalSpace Bool] [DiscreteTopology Bool]
    (F : Set RealCode) (hF : IsClosed F) (x : RealCode) :
    ¬ GroundOpen (groundOpenCode Fᶜ) x ↔ x ∈ F := by
  rw [groundOpenCode_iff_r107 Fᶜ hF.isOpen_compl]
  exact not_not

end CantorCodes
end JSP000933
