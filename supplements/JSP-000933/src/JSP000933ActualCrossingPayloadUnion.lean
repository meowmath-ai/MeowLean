import JSP000933CoherentSelectedNegativeIso

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def activePayloadUnion (w : I → B) (pay : I → ℕ → B) : ℕ → B :=
  fun i => ⨆ j : I, w j ⊓ pay j i

theorem activePayloadUnion_meet_cap_r247
    (w : I → B) (cap pay : I → ℕ → B)
    (hBelow : ∀ x i, w x ⊓ pay x i ≤ cap x i)
    (hCross : ∀ x y, w x ⊓ w y ≤ realEqValue (bitsMeet (cap x) (pay y)) (bitsMeet (cap y) (pay x)))
    (x : I) :
    w x ≤ realEqValue (bitsMeet (activePayloadUnion w pay) (cap x)) (pay x) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro i
  change w x ⊓ (activePayloadUnion w pay i ⊓ cap x i) = w x ⊓ pay x i
  apply le_antisymm
  · apply le_inf (inf_le_left : w x ⊓ _ ≤ w x)
    calc
      w x ⊓ (activePayloadUnion w pay i ⊓ cap x i) =
        (w x ⊓ cap x i) ⊓ activePayloadUnion w pay i := by ac_rfl
      _ ≤ pay x i := by
        unfold activePayloadUnion
        rw [inf_iSup_eq]
        apply iSup_le
        intro y
        let r := (w x ⊓ cap x i) ⊓ (w y ⊓ pay y i)
        have hW : r ≤ w x ⊓ w y := le_inf
          (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
        have hA : r ≤ cap x i ⊓ pay y i := le_inf
          (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
        have he := (le_realEqValue_iff_r126 (w x ⊓ w y) _ _).mp (hCross x y) i
        exact ((le_inf hW hA).trans_eq he).trans (inf_le_right.trans inf_le_right)
  · apply le_inf inf_le_left
    exact le_inf (le_iSup (fun y : I => w y ⊓ pay y i) x) (hBelow x i)

theorem activePayloadUnion_meet_cap_localEq_r247
    (w : I → B) (cap pay : I → ℕ → B)
    (hBelow : ∀ x i, w x ⊓ pay x i ≤ cap x i)
    (hCross : ∀ x y, w x ⊓ w y ≤ realEqValue (bitsMeet (cap x) (pay y)) (bitsMeet (cap y) (pay x)))
    (x : I) :
    LocalEq false (w x) (bitsMeet (activePayloadUnion w pay) (cap x)) (pay x) :=
  LocalEq.of_realEq_r246 false (activePayloadUnion_meet_cap_r247 w cap pay hBelow hCross x)

end SetLanguage
end JSP000933
