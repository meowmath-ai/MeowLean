import JSP000933ReifyCoverClique
import JSP000933BooleanNamedCliqueStage

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open CantorCodes FiniteSupport

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def namedCantorOCAValue (B : Type) [NontrivialCompleteBooleanAlgebra B] : B :=
  ⨅ X : bSet B, ⨅ W : bSet B,
    imp (namedAllRealsValue X)
      ((⨆ C : bSet B, namedCliqueValue X W C) ⊔ (⨆ H : bSet B, namedCoverValue X W H))

theorem nativeOCA_le_namedCantorOCA_r180 :
    nativeOCAValue B ≤ namedCantorOCAValue B := by
  apply le_iInf
  intro X
  apply le_iInf
  intro W
  rw [← _root_.deduction]
  let D (x : ℕ → B) := realBitsName x ∈ᴮ X
  let K := namedOpenColorCode W
  let e : {D : (ℕ → B) → B // RealTestExt D} := ⟨D,nativeDomain_ext_r179 X⟩
  let p := namedAllRealsValue X
  have h0 : nativeOCAValue B ≤ (irreflexiveGraphValue D K ⊓ symmetricGraphValue D K)ᶜ ⊔
      (closedCoverExistsValue D K ⊔ weightedCliqueExistsValue D K) :=
    (iInf_le _ e).trans (iInf_le _ K)
  have hValid : irreflexiveGraphValue D K ⊓ symmetricGraphValue D K = ⊤ :=
    namedOpenColor_valid_r177 D W
  rw [hValid,compl_top,bot_sup_eq] at h0
  apply (inf_le_inf_right p h0).trans
  rw [inf_sup_right]
  apply sup_le
  · unfold closedCoverExistsValue
    apply Lattice.bv_cases_left
    intro c
    exact (le_iSup_of_le (closedCoverName c)
      (named_cover_of_goodCode_r179 X W c _ inf_le_right inf_le_left)).trans le_sup_right
  · unfold weightedCliqueExistsValue
    apply Lattice.bv_cases_left
    intro x
    apply Lattice.bv_cases_left
    intro g
    obtain ⟨C,hC⟩ := named_clique_of_weighted_r179 X W x g _ inf_le_right inf_le_left
    exact (le_iSup_of_le C hC).trans le_sup_left

instance ocaCondition_nonempty_r180 (P : OCAParameters) : Nonempty (ocaCondition P) := by
  refine ⟨⟨fun _ => none,?_,?_⟩⟩
  · have h : {i : OmegaTwoIndex | present (show Trace (fun _ : OmegaTwoIndex => OCALabel) from fun _ => none) i} = ∅ := by
      ext i
      simp [present]
    rw [h]
    exact Set.finite_empty
  · intro a s hs
    cases hs

theorem ocaIteration_namedCantorOCA_top_r180 (P : OCAParameters)
    (hDia : DiamondAtOmegaOne P.guess) :
    namedCantorOCAValue (ocaB P) = ⊤ := by
  apply top_unique
  exact (ocaIteration_nativeOCA_top_r170 P hDia).ge.trans nativeOCA_le_namedCantorOCA_r180

end BooleanNames
end JSP000933
