import JSP000930PositiveTypedComplexFunctionSemantics

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000930.AnalyticSyntax JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem graphTypedShape_pair_in_domain {G A : bSet B} {p : B}
    (hShape : p ≤ graphTypedShape G A) (x y : bSet B)
    (hPair : p ≤ pair x y ∈ᴮ G) : p ≤ x ∈ᴮ A := by
  have h := (le_inf (hShape.trans (iInf_le _ (pair x y))) hPair).trans Lattice.bv_imp_elim
  apply h.trans
  apply iSup_le
  intro i
  rw [inf_iSup_eq]
  apply iSup_le
  intro z
  have he : (i ∈ᴮ A) ⊓ (weakComplexName z ⊓ (pair x y =ᴮ pair i z)) ≤ x =ᴮ i :=
    inf_le_right.trans (inf_le_right.trans eq_of_eq_pair_left)
  exact subst_congr_mem_left' (bv_symm he) inf_le_left

theorem typedGraph_func {G A : bSet B} {p : B}
    (hShape : p ≤ graphTypedShape G A) (hTotal : p ≤ graphTypedTotalUnique G A) :
    p ≤ is_func G := by
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply le_iInf
  intro c
  apply le_iInf
  intro d
  rw [← _root_.deduction,← _root_.deduction]
  let m := (p ⊓ ((pair a c ∈ᴮ G) ⊓ (pair b d ∈ᴮ G))) ⊓ (a =ᴮ b)
  have hmp : m ≤ p := inf_le_left.trans inf_le_left
  have ha : m ≤ pair a c ∈ᴮ G := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hb : m ≤ pair b d ∈ᴮ G := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hbd : m ≤ pair a d ∈ᴮ G :=
    subst_congr_mem_left' (pair_congr (bv_symm inf_le_right) bv_refl) hb
  have hDom := graphTypedShape_pair_in_domain (hmp.trans hShape) a c ha
  have hU := (le_inf ((hmp.trans hTotal).trans (iInf_le _ a)) hDom).trans
    Lattice.bv_imp_elim
  apply (le_inf le_rfl hU).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro z
  let e := m ⊓ (weakComplexName z ⊓ ((pair a z ∈ᴮ G) ⊓
    (⨅ w : bSet B,imp (pair a w ∈ᴮ G) (z =ᴮ w))))
  have hOne : e ≤ ⨅ w : bSet B,imp (pair a w ∈ᴮ G) (z =ᴮ w) :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  have hc : e ≤ z =ᴮ c :=
    (le_inf (hOne.trans (iInf_le _ c)) (inf_le_left.trans ha)).trans Lattice.bv_imp_elim
  have hd : e ≤ z =ᴮ d :=
    (le_inf (hOne.trans (iInf_le _ d)) (inf_le_left.trans hbd)).trans Lattice.bv_imp_elim
  exact bv_trans (bv_symm hc) hd

theorem typedGraph_good_total_omega {G : bSet B} {p : B}
    (hTotal : p ≤ graphTypedTotalUnique G bSet.omega) (n : ℕ) :
    p ≤ ⨆ x : bSet B,⨆ y : bSet B,
      (pair (bSet.of_nat n) (pair x y) ∈ᴮ G) ⊓ ((x ⊆ᴮ ratUniverse) ⊓ (y ⊆ᴮ ratUniverse)) := by
  have hn : (⊤ : B) ≤ (bSet.of_nat n : bSet B) ∈ᴮ bSet.omega :=
    bSet.of_nat_mem_omega
  have hU := (le_inf (hTotal.trans (iInf_le _ (bSet.of_nat n))) (le_top.trans hn)).trans
    Lattice.bv_imp_elim
  apply hU.trans
  apply iSup_le
  intro z
  simp only [weakComplexName,iSup_inf_eq]
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  apply le_iSup_of_le x
  apply le_iSup_of_le y
  have hE : (((x ⊆ᴮ ratUniverse) ⊓ (y ⊆ᴮ ratUniverse)) ⊓ (z =ᴮ pair x y)) ⊓
      ((pair (bSet.of_nat n) z ∈ᴮ G) ⊓ (⨅ w : bSet B,imp
        (pair (bSet.of_nat n) w ∈ᴮ G) (z =ᴮ w))) ≤ z =ᴮ pair x y :=
    inf_le_left.trans inf_le_right
  exact le_inf (subst_congr_mem_left' (pair_congr bv_refl hE)
      (inf_le_right.trans inf_le_left)) (inf_le_left.trans inf_le_left)

theorem typedGraph_pairs_omega {G : bSet B} {p : B}
    (hShape : p ≤ graphTypedShape G bSet.omega) (q : bSet B) :
    p ⊓ (q ∈ᴮ G) ≤ ⨆ n : ℕ,⨆ y : bSet B,q =ᴮ pair (bSet.of_nat n) y := by
  have h₀ : p ⊓ (q ∈ᴮ G) ≤ ⨆ i : bSet B,(i ∈ᴮ bSet.omega) ⊓
      (⨆ z : bSet B,weakComplexName z ⊓ (q =ᴮ pair i z)) :=
    (le_inf (inf_le_left.trans (hShape.trans (iInf_le _ q))) inf_le_right).trans
      Lattice.bv_imp_elim
  apply h₀.trans
  apply iSup_le
  intro i
  apply (inf_le_inf (omega_entries_cover i) le_rfl).trans
  rw [iSup_inf_eq]
  apply iSup_le
  intro n
  rw [inf_iSup_eq]
  apply iSup_le
  intro z
  apply le_iSup_of_le n
  apply le_iSup_of_le z
  exact bv_trans (inf_le_right.trans inf_le_right) (pair_congr inf_le_left bv_refl)

end JSP000930.Positive
