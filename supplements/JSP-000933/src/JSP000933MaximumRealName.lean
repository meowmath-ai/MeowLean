import JSP000933MixingDisjointRefinement

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def mixRealNames (M : Set B) (x : ↥M → ℕ → B) : ℕ → B :=
  fun n => ⨆ a : ↥M, a.1 ⊓ x a n

theorem mask_mixRealNames_r138 (M : Set B)
    (hM : ∀ a ∈ M, ∀ b ∈ M, a ≠ b → Disjoint a b)
    (x : ↥M → ℕ → B) (a : ↥M) (n : ℕ) :
    a.1 ⊓ mixRealNames M x n = a.1 ⊓ x a n := by
  classical
  apply le_antisymm
  · unfold mixRealNames
    rw [inf_iSup_eq]
    apply iSup_le
    intro b
    by_cases he : a = b
    · subst b
      exact inf_le_right
    · have he' : a.1 ≠ b.1 := fun h => he (Subtype.ext h)
      have hd := disjoint_iff_inf_le.mp (hM a.1 a.2 b.1 b.2 he')
      exact ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans hd).trans bot_le
  · exact le_inf inf_le_left
      (le_iSup (fun b : ↥M => b.1 ⊓ x b n) a)

def RealTestExt (test : (ℕ → B) → B) : Prop :=
  ∀ p x y, p ≤ realEqValue x y → p ⊓ test x = p ⊓ test y

theorem exists_realName_maximum_r138 (test : (ℕ → B) → B) (hExt : RealTestExt test)
    (p : B) (hp : p ≤ ⨆ x : ℕ → B, test x) :
    ∃ x : ℕ → B, p ≤ test x := by
  classical
  obtain ⟨M,hM,hDis,hSup⟩ := exists_disjoint_witnessRefinement_r137 p test hp
  have hEach (a : ↥M) : ∃ x : ℕ → B, a.1 ≤ test x := (hM a.1 a.2).2.2
  choose x hx using hEach
  refine ⟨mixRealNames M x,?_⟩
  rw [← hSup]
  apply sSup_le
  intro a ha
  let b : ↥M := ⟨a,ha⟩
  have heq : a ≤ realEqValue (mixRealNames M x) (x b) :=
    (le_realEqValue_iff_r126 _ _ _).mpr (mask_mixRealNames_r138 M hDis x b)
  exact (le_inf le_rfl (hx b)).trans ((hExt a _ _ heq).ge.trans inf_le_right)

theorem RealTestExt.inf_r138 {f g : (ℕ → B) → B} (hf : RealTestExt f) (hg : RealTestExt g) :
    RealTestExt (fun x => f x ⊓ g x) :=
  fun p x y he => mask_inf_congr_r126 (hf p x y he) (hg p x y he)

theorem RealTestExt.compl_r138 {f : (ℕ → B) → B} (hf : RealTestExt f) :
    RealTestExt (fun x => (f x)ᶜ) := fun p x y he => mask_compl_congr_r126 (hf p x y he)

theorem RealTestExt.iInf_r138 {I : Type} {f : I → (ℕ → B) → B} (hf : ∀ i, RealTestExt (f i)) :
    RealTestExt (fun x => ⨅ i, f i x) :=
  fun p x y he => mask_iInf_congr_r126 (fun i => hf i p x y he)

end CantorCodes
end JSP000933
