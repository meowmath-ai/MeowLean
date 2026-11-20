import JSP000933MixedNonIsoSyntax
import JSP000933MaximumRealName

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def graphPairBits (G : bSet B) (s : Bool) (x y : ℕ → B) : B :=
  orderedPairSide s (realBitsName x) (realBitsName y) ∈ᴮ G

theorem orderedPairSide_congr_second_r214 (s : Bool) {a b b' : bSet B}
    {p : B} (h : p ≤ b =ᴮ b') :
    p ≤ orderedPairSide s a b =ᴮ orderedPairSide s a b' := by
  cases s
  · exact bSet.pair_congr bSet.bv_refl h
  · exact bSet.pair_congr h bSet.bv_refl

theorem graphPairBits_ext_right_r214 (G : bSet B) (s : Bool) (x : ℕ → B) :
    RealTestExt (graphPairBits G s x) := by
  intro p y z h
  apply maskedMem_left_r175
  exact orderedPairSide_congr_second_r214 s (h.trans_eq (realBitsName_eq_r128 y z).symm)

theorem graphPairBits_ext_left_r214 (G : bSet B) (s : Bool) (y : ℕ → B) :
    RealTestExt (fun x => graphPairBits G s x y) := by
  intro p x z h
  apply maskedMem_left_r175
  exact orderedPairSide_congr_first_r187 s (h.trans_eq (realBitsName_eq_r128 x z).symm)

theorem graphTotal_le_bitsExist_r214 (G : bSet B) (s : Bool) (x : ℕ → B) :
    graphTotalSideValue G s ≤ ⨆ y : ℕ → B, graphPairBits G s x y := by
  let a := realBitsName x
  have h : graphTotalSideValue G s ≤ imp (a ⊆ᴮ bSet.omega)
      (⨆ b : bSet B, (b ⊆ᴮ bSet.omega) ⊓ (orderedPairSide s a b ∈ᴮ G)) := iInf_le _ a
  apply (_root_.context_imp_elim h (le_top.trans (realBitsName_subset_r103 x))).trans
  apply iSup_le
  intro b
  let q := (b ⊆ᴮ bSet.omega) ⊓ (orderedPairSide s a b ∈ᴮ G)
  have hb : q ≤ b =ᴮ realBitsName (membershipBits b) := realBitsName_represents_r103 b inf_le_left
  have hp : q ≤ orderedPairSide s a b =ᴮ orderedPairSide s a (realBitsName (membershipBits b)) :=
    orderedPairSide_congr_second_r214 s hb
  apply le_iSup_of_le (membershipBits b)
  exact bSet.subst_congr_mem_left' hp inf_le_right

theorem graph_namedSelection_r214 (G : bSet B) (s : Bool) (p : B)
    (h : p ≤ graphTotalSideValue G s) :
    ∃ F : (ℕ → B) → ℕ → B, ∀ x, p ≤ graphPairBits G s x (F x) := by
  classical
  have he (x : ℕ → B) : ∃ y, p ≤ graphPairBits G s x y :=
    exists_realName_maximum_r138 (graphPairBits G s x) (graphPairBits_ext_right_r214 G s x) p
      (h.trans (graphTotal_le_bitsExist_r214 G s x))
  choose F hF using he
  exact ⟨F,hF⟩

theorem graph_orderOnSelectedNames_r214 (G : bSet B) (p : B)
    (hG : p ≤ actualPreserveReflectValue G) (x x' y y' : ℕ → B)
    (h₁ : p ≤ graphPairBits G false x y) (h₂ : p ≤ graphPairBits G false x' y') :
    p ≤ bitEq (actualOrdLEValue (realBitsName x) (realBitsName x'))
      (actualHarLEValue (realBitsName y) (realBitsName y')) := by
  have h := hG.trans ((iInf_le _ (realBitsName x)).trans
    ((iInf_le _ (realBitsName x')).trans ((iInf_le _ (realBitsName y)).trans (iInf_le _ (realBitsName y')))))
  have h0 := _root_.context_imp_elim h (le_top.trans (realBitsName_subset_r103 x))
  have h1 := _root_.context_imp_elim h0 (le_top.trans (realBitsName_subset_r103 x'))
  have h2 := _root_.context_imp_elim h1 (le_top.trans (realBitsName_subset_r103 y))
  have h3 := _root_.context_imp_elim h2 (le_top.trans (realBitsName_subset_r103 y'))
  exact _root_.context_imp_elim h3 (le_inf h₁ h₂)

theorem isoValue_has_two_namedSelections_r214 (p : B) (G : bSet B)
    (hG : p ≤ graphPairsOnlyValue G ⊓ (graphTotalSideValue G false ⊓
      (graphTotalSideValue G true ⊓ actualPreserveReflectValue G))) :
    ∃ F R : (ℕ → B) → ℕ → B,
      (∀ x, p ≤ graphPairBits G false x (F x)) ∧
      (∀ y, p ≤ graphPairBits G true y (R y)) ∧
      (∀ x x', p ≤ bitEq (actualOrdLEValue (realBitsName x) (realBitsName x'))
        (actualHarLEValue (realBitsName (F x)) (realBitsName (F x')))) := by
  obtain ⟨F,hF⟩ := graph_namedSelection_r214 G false p (hG.trans (inf_le_right.trans inf_le_left))
  obtain ⟨R,hR⟩ := graph_namedSelection_r214 G true p
    (hG.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
  refine ⟨F,R,hF,hR,fun x x' => ?_⟩
  exact graph_orderOnSelectedNames_r214 G p (hG.trans (inf_le_right.trans
    (inf_le_right.trans inf_le_right))) x x' (F x) (F x') (hF x) (hF x')

end SetLanguage
end JSP000933
