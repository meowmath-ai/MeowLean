import JSP000930PositiveTaylorBitCode

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.BooleanNames JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def graphTaylorBits (G : bSet B) (s : TaylorSlot) : B :=
  ⨆ x : bSet B,⨆ y : bSet B,
    (pair (bSet.of_nat s.1) (pair x y) ∈ᴮ G) ⊓
      (ratName s.2.2 ∈ᴮ if s.2.1 then y else x)

theorem graphTaylorBits_on_pair (G : bSet B) (n : ℕ) (x y : bSet B)
    (p : B) (hF : p ≤ is_func G) (hPair : p ≤ pair (bSet.of_nat n) (pair x y) ∈ᴮ G)
    (b : Bool) (q : RatPresentation) :
    p ⊓ graphTaylorBits G (n,b,q) = p ⊓ (ratName q ∈ᴮ if b then y else x) := by
  apply le_antisymm
  · unfold graphTaylorBits
    rw [inf_iSup_eq]
    apply iSup_le
    intro x'
    rw [inf_iSup_eq]
    apply iSup_le
    intro y'
    let r := p ⊓ ((pair (bSet.of_nat n) (pair x' y') ∈ᴮ G) ⊓
      (ratName q ∈ᴮ if b then y' else x'))
    have hEq : r ≤ pair x' y' =ᴮ pair x y :=
      eq_of_is_func_of_eq (inf_le_left.trans hF) bv_refl
        (inf_le_right.trans inf_le_left) (inf_le_left.trans hPair)
    have hv : r ≤ (if b then y' else x') =ᴮ (if b then y else x) := by
      cases b
      · exact hEq.trans eq_of_eq_pair_left
      · exact hEq.trans eq_of_eq_pair_right
    exact le_inf inf_le_left
      (subst_congr_mem_right' hv (inf_le_right.trans inf_le_right))
  · apply le_inf inf_le_left
    unfold graphTaylorBits
    apply le_iSup_of_le x
    apply le_iSup_of_le y
    exact le_inf (inf_le_left.trans hPair) inf_le_right

theorem graphTaylorBits_on_pair_bounded (G : bSet B) (n : ℕ) (x y : bSet B)
    (p : B) (hF : p ≤ is_func G) (hPair : p ≤ pair (bSet.of_nat n) (pair x y) ∈ᴮ G)
    (hx : p ≤ x ⊆ᴮ ratUniverse) (hy : p ≤ y ⊆ᴮ ratUniverse) :
    p ≤ coefficientName (graphTaylorBits G) n =ᴮ pair x y := by
  apply pair_congr
  · have hr := familyName_represents_subset_r70 (ratName (B := B)) x p hx
    have h' : p ≤ weightedRationalSet (fun r => graphTaylorBits G (n,false,r)) =ᴮ
         weightedRationalSet (fun r => ratName r ∈ᴮ x) :=
      weightedCut_eq_of_mask (fun r => graphTaylorBits_on_pair G n x y p hF hPair false r)
    exact bv_trans h' (bv_symm hr)
  · have hr := familyName_represents_subset_r70 (ratName (B := B)) y p hy
    have h' : p ≤ weightedRationalSet (fun r => graphTaylorBits G (n,true,r)) =ᴮ
         weightedRationalSet (fun r => ratName r ∈ᴮ y) :=
      weightedCut_eq_of_mask (fun r => graphTaylorBits_on_pair G n x y p hF hPair true r)
    exact bv_trans h' (bv_symm hr)

theorem graphTaylorBits_named_coeff_mem (G : bSet B) (p : B)
    (hF : p ≤ is_func G)
    (hTotal : ∀ n : ℕ,p ≤ ⨆ x : bSet B,⨆ y : bSet B,
      (pair (bSet.of_nat n) (pair x y) ∈ᴮ G) ⊓ ((x ⊆ᴮ ratUniverse) ⊓ (y ⊆ᴮ ratUniverse)))
    (n : ℕ) :
    p ≤ pair (bSet.of_nat n) (coefficientName (graphTaylorBits G) n) ∈ᴮ G := by
  apply (le_inf le_rfl (hTotal n)).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro x
  rw [inf_iSup_eq]
  apply iSup_le
  intro y
  let d := p ⊓ ((pair (bSet.of_nat n) (pair x y) ∈ᴮ G) ⊓
    ((x ⊆ᴮ ratUniverse) ⊓ (y ⊆ᴮ ratUniverse)))
  have hP : d ≤ pair (bSet.of_nat n) (pair x y) ∈ᴮ G :=
    inf_le_right.trans inf_le_left
  have hE := graphTaylorBits_on_pair_bounded G n x y d (inf_le_left.trans hF) hP
    (inf_le_right.trans (inf_le_right.trans inf_le_left))
    (inf_le_right.trans (inf_le_right.trans inf_le_right))
  exact subst_congr_mem_left' (pair_congr bv_refl (bv_symm hE)) hP

theorem graphTaylorBits_reconstruct (G : bSet B) (p : B)
    (hF : p ≤ is_func G)
    (hTotal : ∀ n : ℕ,p ≤ ⨆ x : bSet B,⨆ y : bSet B,
      (pair (bSet.of_nat n) (pair x y) ∈ᴮ G) ⊓ ((x ⊆ᴮ ratUniverse) ⊓ (y ⊆ᴮ ratUniverse)))
    (hPairs : ∀ z : bSet B,p ⊓ (z ∈ᴮ G) ≤ ⨆ n : ℕ,⨆ y : bSet B,z =ᴮ pair (bSet.of_nat n) y) :
    p ≤ G =ᴮ taylorCodeName (graphTaylorBits G) := by
  have hC := graphTaylorBits_named_coeff_mem G p hF hTotal
  apply (le_inf ?_ ?_).trans (eq_of_subset_subset _ _)
  · rw [subset_unfold]
    apply le_iInf
    intro i
    rw [← _root_.deduction]
    let z := G.func i
    let d := p ⊓ G.bval i
    have hMem : d ≤ z ∈ᴮ G := inf_le_right.trans (bSet.mem_mk' G i)
    have hDes := (le_inf inf_le_left hMem).trans (hPairs z)
    apply (le_inf le_rfl hDes).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    rw [inf_iSup_eq]
    apply iSup_le
    intro y
    let m := d ⊓ (z =ᴮ pair (bSet.of_nat n) y)
    have hY : m ≤ pair (bSet.of_nat n) y ∈ᴮ G :=
      subst_congr_mem_left' inf_le_right (inf_le_left.trans hMem)
    have hEq : m ≤ y =ᴮ coefficientName (graphTaylorBits G) n :=
      eq_of_is_func_of_eq (inf_le_left.trans (inf_le_left.trans hF)) bv_refl hY
        (inf_le_left.trans (inf_le_left.trans (hC n)))
    have hPair : m ≤ z =ᴮ pair (bSet.of_nat n) (coefficientName (graphTaylorBits G) n) :=
      bv_trans inf_le_right (pair_congr bv_refl hEq)
    exact subst_congr_mem_left' (bv_symm hPair)
      (le_top.trans (pair_mem_functionalGraph_self_r102 bSet.of_nat
        (coefficientName (graphTaylorBits G)) n))
  · rw [subset_unfold]
    change p ≤ ⨅ n : ℕ,imp (⊤ : B) (pair (bSet.of_nat n)
      (coefficientName (graphTaylorBits G) n) ∈ᴮ G)
    apply le_iInf
    intro n
    rw [← _root_.deduction,inf_top_eq]
    exact hC n

end JSP000930.Positive
