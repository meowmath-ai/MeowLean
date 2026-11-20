import JSP000933ActualDyadicHybridQuotient
import Mathlib.Data.Finset.Lattice.Fold

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem namedContinuous_finite_sameCylinder_r345 {p : B} (f : ℕ → (ℕ → B) → ℕ → B)
    (hF : ∀ j, NamedContinuousOn p (f j)) (x : ℕ → B) (N : ℕ) :
    ∀ (L : ℕ) (q : B), q≠⊥ → q≤p →
      ∃ (r : B) (u : Word), r≠⊥ ∧ r≤q ∧ r≤cylinderValue x u ∧
        ∀ j<L, ∀ y s, s≤r → s≤cylinderValue y u →
          ∀ m<N, s⊓f j x m=s⊓f j y m := by
  intro L
  induction L with
  | zero =>
    intro q hq hqp
    obtain ⟨u,_,r,hr,hrq,hU⟩ := exists_decided_initialWord_r136 x 0 q hq
    exact ⟨r,u,hr,hrq,hU,fun j hj => (Nat.not_lt_zero j hj).elim⟩
  | succ L ih =>
    intro q hq hqp
    obtain ⟨r,u,hr,hrq,hU,hOld⟩ := ih q hq hqp
    obtain ⟨t,v,ht,htr,hV,hNew⟩ := hF L x N r hr (hrq.trans hqp)
    have hU' : t≤cylinderValue x u := htr.trans hU
    rcases le_total u.length v.length with hLen | hLen
    · have he := extendsWord_of_compatible_r173 x ht hLen hU' hV
      refine ⟨t,v,ht,htr.trans hrq,hV,?_⟩
      intro j hj y s hs hy
      by_cases hj' : j<L
      · exact hOld j hj' y s (hs.trans htr) (hy.trans (cylinderWord_mono_r173 y he))
      · have heq : j=L := by omega
        subst j
        exact hNew y s hs hy
    · have he := extendsWord_of_compatible_r173 x ht hLen hV hU'
      refine ⟨t,u,ht,htr.trans hrq,hU',?_⟩
      intro j hj y s hs hy
      by_cases hj' : j<L
      · exact hOld j hj' y s (hs.trans htr) hy
      · have heq : j=L := by omega
        subst j
        exact hNew y s hs (hy.trans (cylinderWord_mono_r173 y he))

theorem actualHybrid_prefix_congr_r345 {p : B} (f : ℕ → (ℕ → B) → ℕ → B)
    (x y : ℕ → B) (N : ℕ)
    (hT : ∀ j<N, ∀ m<N, p⊓actualDyadicGapTail f x j m=p⊓actualDyadicGapTail f y j m)
    (hF : ∀ j<N, ∀ m<N, p⊓f j x m=p⊓f j y m) :
    ∀ m<N, p⊓actualHybridBit f x m=p⊓actualHybridBit f y m := by
  have hC : ∀ j≤N, ∀ m<N, p⊓actualRecursiveCutLE (actualDyadicGapTail f x) j m=
      p⊓actualRecursiveCutLE (actualDyadicGapTail f y) j m := by
    intro j
    induction j with
    | zero => intro _ _ _; rfl
    | succ j ih =>
      intro hj m hm
      cases m with
      | zero => rfl
      | succ m =>
        change p⊓(actualRecursiveCutLE (actualDyadicGapTail f x) j m⊓actualDyadicGapTail f x j (m+1))=
          p⊓(actualRecursiveCutLE (actualDyadicGapTail f y) j m⊓actualDyadicGapTail f y j (m+1))
        exact mask_inf_congr_r126 (ih ((Nat.le_succ j).trans hj) m (by omega))
          (hT j (by omega) (m+1) hm)
  intro m hm
  unfold actualHybridBit
  apply mask_iSup_congr_r126
  intro j
  by_cases hj : j≤ m
  · have hj' : j<N := hj.trans_lt hm
    exact mask_inf_congr_r126
      (mask_inf_congr_r126 (hC j hj'.le m hm)
        (mask_compl_congr_r126 (hC (j+1) (Nat.succ_le_of_lt hj') m hm))) (hF j hj' m hm)
  · simp only [actualRecursiveCutLE_bot_r335 _ j m (Nat.lt_of_not_ge hj),bot_inf_eq,inf_bot_eq]

def gapCodeProfilePair (i : ℕ) : ℕ × ℕ := (Encodable.decode (α := ℕ × ℕ) i).getD (0,0)

theorem finite_gap_code_bound_r345 (N : ℕ) :
    ∃ M : ℕ, ∀ j<N, ∀ m<N, Encodable.encode (j,m)<M := by
  let f (j m : ℕ) : ℕ := Encodable.encode (j,m)
  let s := Finset.range N
  refine ⟨s.sup (fun j => s.sup (f j))+1,?_⟩
  intro j hj m hm
  have hM : f j m ≤ s.sup (f j) := Finset.le_sup (f := f j) (Finset.mem_range.mpr hm)
  have hJ : s.sup (f j) ≤ s.sup (fun j => s.sup (f j)) :=
    Finset.le_sup (f := fun i => s.sup (f i)) (Finset.mem_range.mpr hj)
  exact Nat.lt_succ_of_le (hM.trans hJ)

theorem actualHybrid_regular_r345 {p : B} (f : ℕ → (ℕ → B) → ℕ → B)
    (hF : ∀ j, NamedContinuousOn p (f j)) : Nonempty (NamedRegularOn p (actualHybridBit f)) := by
  let K (i : ℕ) : Word → B := actualErrorTailBadCode (f (gapCodeProfilePair i).1)
    (f ((gapCodeProfilePair i).1+1)) true (dyadicGapDen (gapCodeProfilePair i).1) (gapCodeProfilePair i).2
  let C (i : ℕ) := closedBoundaryRegularCode (K i)
  refine ⟨⟨C,fun i => (closedBoundaryRegular_dense_r280 (K i)).restrict_r293 le_top,?_⟩⟩
  intro x N q hq hqp hReg
  obtain ⟨M,hM⟩ := finite_gap_code_bound_r345 N
  obtain ⟨r,u,hr,hrq,hU,hDec⟩ := finiteClosedBoundary_sameCylinder_r318 K x M q hq
    (fun i _ => hReg.trans (iInf_le _ i))
  obtain ⟨t,v,ht,htr,hV,hF'⟩ := namedContinuous_finite_sameCylinder_r345 f hF x N N r hr (hrq.trans hqp)
  have hFinish (y : ℕ → B) (s : B) (hst : s≤t)
      (hyU : s≤cylinderValue y u) (hyV : s≤cylinderValue y v) :
      ∀ m<N, s⊓actualHybridBit f x m=s⊓actualHybridBit f y m := by
    have hsr := hst.trans htr
    have hsp := hsr.trans (hrq.trans hqp)
    apply actualHybrid_prefix_congr_r345 f x y N _ (fun j hj => hF' j hj y s hst hyV)
    intro j hj m hm
    let i := Encodable.encode (j,m)
    have hi : gapCodeProfilePair i=(j,m) := by simp [i,gapCodeProfilePair,Encodable.encodek]
    let T := fun x => actualDyadicGapTail f x j m
    have hK (z : ℕ → B) : p⊓openValue (K i) z=p⊓(T z)ᶜ := by
      unfold K
      rw [hi]
      exact actualErrorTailBadCode_mask_r302 (hF j) (hF (j+1)) true (dyadicGapDen j) m z
    exact (closedCode_closedMask_r318 hsp (K i) T x (hK x)).symm.trans
      (((hDec i (hM j hj m hm)).mask_eq_r286 hsr (hsr.trans hU) hyU).trans
        (closedCode_closedMask_r318 hsp (K i) T y (hK y)))
  have hTU : t≤cylinderValue x u := htr.trans hU
  rcases le_total u.length v.length with hLen | hLen
  · have he := extendsWord_of_compatible_r173 x ht hLen hTU hV
    exact ⟨t,v,ht,htr.trans hrq,hV,
      fun y s hs hy => hFinish y s hs (hy.trans (cylinderWord_mono_r173 y he)) hy⟩
  · have he := extendsWord_of_compatible_r173 x ht hLen hV hTU
    exact ⟨t,u,ht,htr.trans hrq,hTU,
      fun y s hs hy => hFinish y s hs hy (hy.trans (cylinderWord_mono_r173 y he))⟩

end SetLanguage
end JSP000933
