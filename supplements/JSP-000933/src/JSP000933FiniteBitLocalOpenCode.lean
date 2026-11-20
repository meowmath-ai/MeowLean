import JSP000933ActualCompactClosedProjection

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def BoundedBitLocal (N : ℕ) (f : (ℕ → B) → B) : Prop :=
  ∀ (p : B) (x y : ℕ → B), (∀ m<N, p⊓x m=p⊓y m) → p⊓f x=p⊓f y

theorem mask_cylinder_bounded_r278 {p : B} {x y : ℕ → B} (u : Word)
    (h : ∀ m<u.length, p⊓x m=p⊓y m) : p⊓cylinderValue x u=p⊓cylinderValue y u := by
  unfold cylinderValue
  apply mask_iInf_congr_r126
  intro m
  have hm := h m.val m.isLt
  cases hw : u[m.val]'m.isLt
  · simpa only [hw,literal] using (mask_compl_congr_r126 hm)
  · simpa only [hw,literal] using hm

noncomputable def boundedTestOpenCode (N : ℕ) (f : (ℕ → B) → B) (u : Word) : B :=
  if u.length=N then f (paddedWordBits u) else ⊥

theorem boundedTestOpenCode_value_r278 (N : ℕ) (f : (ℕ → B) → B)
    (h : BoundedBitLocal N f) (x : ℕ → B) :
    openValue (boundedTestOpenCode N f) x=f x := by
  apply le_antisymm
  · unfold openValue
    apply iSup_le
    intro u
    by_cases hu : u.length=N
    · rw [boundedTestOpenCode,ite_eq_left hu]
      let t := f (paddedWordBits u)⊓cylinderValue x u
      have hC : t≤cylinderValue x u := inf_le_right
      have he := h t x (paddedWordBits u)
        (fun m hm => cylinder_fixes_paddedBits_r258 hC m (hu.symm ▸ hm))
      exact ((le_inf le_rfl (show t≤f (paddedWordBits u) from inf_le_left)).trans_eq he.symm).trans inf_le_right
    · rw [boundedTestOpenCode,ite_eq_right hu,bot_inf_eq]
      exact bot_le
  · apply le_of_dense_named_refinements_r219
    intro p hp hF
    obtain ⟨u,hu,q,hq,hqp,hU⟩ := exists_decided_initialWord_r136 x N p hp
    have he := h q x (paddedWordBits u)
      (fun m hm => cylinder_fixes_paddedBits_r258 hU m (hu.symm ▸ hm))
    have hb : q≤boundedTestOpenCode N f u := by
      rw [boundedTestOpenCode,ite_eq_left hu]
      exact ((le_inf le_rfl (hqp.trans hF)).trans_eq he).trans inf_le_right
    exact ⟨q,hq,hqp,le_iSup_of_le u (le_inf hb hU)⟩

theorem BoundedBitLocal.compl_r278 {N : ℕ} {f : (ℕ → B) → B}
    (h : BoundedBitLocal N f) : BoundedBitLocal N (fun x => (f x)ᶜ) :=
  fun p x y he => mask_compl_congr_r126 (h p x y he)

end SetLanguage
end JSP000933
