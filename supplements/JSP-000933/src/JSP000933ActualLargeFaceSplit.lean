import JSP000933ActualReservedBadSection

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_actualLarge_split_r308 (a : ℕ → B) {p : B} (hA : p≤actualLongBlockLarge a) :
    ∃ P : ℕ → B, ∀ b : Bool, p≤actualLongBlockLarge (actualCoordinateFace a P b) := by
  let K (i : ℕ) := keepNamedBlockCode a (decide (i%2=1)) (i/2)
  have hD (i : ℕ) : DenseOpenNaming p (K i) :=
    keepNamedBlockCode_dense_r306 a _ _ hA
  obtain ⟨P,_,hP⟩ := exists_namedReal_meeting_denseOpen_r219 p [] K hD
  refine ⟨P,fun b => ?_⟩
  unfold actualLongBlockLarge actualCoordinateFace
  apply le_iInf
  intro N
  let i := 2*N+(if b then 1 else 0)
  have hi : i/2=N := by cases b <;> dsimp [i] <;> omega
  have hb : decide (i%2=1)=b := by
    cases b
    · apply decide_eq_false
      dsimp [i]
      omega
    · apply decide_eq_true
      dsimp [i]
      omega
  exact keepNamedBlockCode_sound_r306 a P b N (by simpa only [K,hi,hb] using hP i)

theorem actualCoordinateFace_le_r308 (a P : ℕ → B) (b : Bool) (m : ℕ) :
    actualCoordinateFace a P b m≤a m := inf_le_left

theorem actualCoordinateFace_join_r308 (a P : ℕ → B) (m : ℕ) :
    actualCoordinateFace a P false m⊔actualCoordinateFace a P true m=a m := by
  change (a m⊓(P (4*m))ᶜ)⊔(a m⊓P (4*m))=a m
  rw [← inf_sup_left,compl_sup_eq_top,inf_top_eq]

theorem actualCoordinateFace_disjoint_r308 (a P : ℕ → B) (m : ℕ) :
    actualCoordinateFace a P false m⊓actualCoordinateFace a P true m=⊥ := by
  change (a m⊓(P (4*m))ᶜ)⊓(a m⊓P (4*m))=⊥
  exact le_bot_iff.mp ((le_inf (inf_le_right.trans inf_le_right)
    (inf_le_left.trans inf_le_right)).trans_eq inf_compl_eq_bot')

theorem namedFacePoint_prefixMap_fixed_r308 (free y : ℕ → B) :
    NamedPrefixMap (fun x => namedFacePoint free x y) := by
  intro p n x z he m hm
  exact mask_sup_congr_r211 rfl (mask_inf_congr_r126 rfl (he m hm))

theorem NamedPrefixMap.comp_r308 {f g : (ℕ → B) → ℕ → B}
    (hf : NamedPrefixMap f) (hg : NamedPrefixMap g) : NamedPrefixMap (fun x => f (g x)) :=
  fun p n x y h => hf p n (g x) (g y) (hg p n x y h)

end SetLanguage
end JSP000933
