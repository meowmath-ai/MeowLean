import JSP000933ActualDenseOpenExtensions

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem _root_.JSP000933.CantorCodes.DenseOpenNaming.restrict_r293 {p q : B} {K : Word → B}
    (h : DenseOpenNaming p K) (hq : q≤p) : DenseOpenNaming q K :=
  fun u => hq.trans (h u)

theorem denseOpen_common_finite_patch_r293 (K : Word → B) :
    ∀ (S : Finset Word) (p : B), p≠⊥ → DenseOpenNaming p K →
      ∃ (q : B) (w : Word), q≠⊥ ∧ q≤p ∧ ∀ s∈S, q ≤ saturateOpenCode K (s++w) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro p hp _
    exact ⟨p,[],hp,le_rfl,by simp⟩
  | @insert s S hs ih =>
    intro p hp hD
    obtain ⟨q,u,hq,hqp,hOld⟩ := ih p hp hD
    obtain ⟨t,v,ht,htq,hT⟩ := denseOpen_has_finite_extension_r292 K hq (hD.restrict_r293 hqp) (s++u)
    refine ⟨t,u++v,ht,htq.trans hqp,?_⟩
    intro w hw
    rw [← List.append_assoc]
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hT
    · exact (htq.trans (hOld w hw)).trans
        (saturatedOpenCode_monoWord_r292 K (extendsWord_append_r292 (w++u) v))

end SetLanguage
end JSP000933
