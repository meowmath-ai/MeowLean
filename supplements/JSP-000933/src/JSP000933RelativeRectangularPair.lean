import JSP000933RelativeClusterTransversality
import JSP000933RelativeOffDiagonal
import JSP000933CliqueAdmissionMerge

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def sortedLabel (n : ℕ) (x : LabelCandidate) : Fin n→OmegaOneIndex :=
  if h : x.2.card=n then fun j => (x.2.orderIsoOfFin h j).val
  else fun _ => Classical.choice (Ordinal.nonempty_toType_iff.mpr
    (ne_of_gt Cardinal.isRegular_aleph_one.ord_pos))

theorem sortedLabel_strictMono_r460 {n : ℕ} (x : LabelCandidate) (h : x.2.card=n) :
    StrictMono (sortedLabel n x) := by
  rw [sortedLabel,dite_eq_left h]
  exact fun i j hij => (x.2.orderIsoOfFin h).strictMono hij

theorem sortedLabel_mem_r460 {n : ℕ} (x : LabelCandidate) (h : x.2.card=n) (j : Fin n) :
    sortedLabel n x j∈x.2 := by
  rw [sortedLabel,dite_eq_left h]
  exact (x.2.orderIsoOfFin h j).property

theorem sortedLabel_reaches_r460 {n : ℕ} (x : LabelCandidate) (h : x.2.card=n)
    {i : OmegaOneIndex} (hi : i∈x.2) : ∃ j,sortedLabel n x j=i := by
  rw [sortedLabel,dite_eq_left h]
  obtain ⟨j,hj⟩ := (x.2.orderIsoOfFin h).surjective ⟨i,hi⟩
  exact ⟨j,congrArg Subtype.val hj⟩

theorem relativeRectangularPair_r460 (hB : BoundsCountableOmegaOneNames B)
    (D : (ℕ→B)→B) (K : Word×Word→B) (m : B)
    (hIrr : ∀ x,m⊓D x≤(colorValue K x x)ᶜ)
    (hSym : ∀ x y,(m⊓(D x⊓D y))⊓colorValue K x y≤colorValue K y x)
    (Y : OmegaOneIndex→ℕ→B) (hY : ∀ i,m≤D (Y i))
    (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e)
    (hAvoid : ∀ j,RelativeAvoidsOn D K m (relativeScheduleFromEnum e) j (fun i => Y i.val) (Y j))
    {n : ℕ} (lower : CardRelativeCCC m (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j)) n)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (hW : unboundedValue (rowLabelWeight W)≠⊥)
    (hOwn : ∀ i s,W i s≤cliqueAdmitted m (fun i => D (Y i))
      (fun i j => colorValue K (Y i) (Y j)) s)
    (hSize : ∀ i s,s.card≠n+1 → W i s=⊥)
    (hDis : ∀ i j,i<j→∀ s t,¬Disjoint s t → Disjoint (W i s) (W j t))
    (hRow : ∀ x y : LabelCandidate,x≠y → x.1=y.1 → Disjoint (W x.1 x.2) (W y.1 y.2))
    (hCross : ∀ x y : LabelCandidate,∀ a b : Fin (n+1),a≠b →
      W x.1 x.2⊓W y.1 y.2≤colorValue K (Y (sortedLabel (n+1) x a))
        (Y (sortedLabel (n+1) y b))) :
    ∃ i j,i<j ∧ ∃ s t,(W i s⊓W j t)⊓cliqueAdmitted m (fun i => D (Y i))
      (fun i j => colorValue K (Y i) (Y j)) (s∪t)≠⊥ := by
  classical
  let DX (i : OmegaOneIndex) := D (Y i)
  let KX (i j : OmegaOneIndex) := colorValue K (Y i) (Y j)
  let a := sortedLabel (n+1)
  have hCard (i : OmegaOneIndex) (s : Finset OmegaOneIndex) (hN : W i s≠⊥) : s.card=n+1 :=
    by
      by_contra hn
      exact hN (hSize i s hn)
  have hMem (i : OmegaOneIndex) (s : Finset OmegaOneIndex) (hN : W i s≠⊥) (j : Fin (n+1)) :
      a (i,s) j∈s := sortedLabel_mem_r460 (i,s) (hCard i s hN) j
  obtain ⟨u,v,hUV,q,hq,hU,hV,hDiagonal⟩ :=
    relativeCluster_diagonalPair_r459 hB D K m hIrr hSym Y hY e hE hAvoid lower a W hW hOwn
      (fun i s h => sortedLabel_strictMono_r460 (i,s) (hCard i s h)) hMem hDis
  have hRowNe : u.1≠v.1 := fun he => hq ((hRow u v hUV he).out _ hU hV)
  have hu : W u.1 u.2≠⊥ := fun he => hq (le_bot_iff.mp (hU.trans_eq he))
  have hv : W v.1 v.2≠⊥ := fun he => hq (le_bot_iff.mp (hV.trans_eq he))
  have hMark : q≤ m := hU.trans ((hOwn u.1 u.2).trans
    ((cliqueAdmitted_le_vertex_r121 _ _ _ (hMem u.1 u.2 hu (Fin.last n))).trans inf_le_left))
  have hQ : q≤cliqueAdmitted m DX KX (u.2∪v.2) := by
    apply cliqueAdmitted_union_r155 m DX KX (hU.trans (hOwn u.1 u.2)) (hV.trans (hOwn v.1 v.2))
    intro x hx y hy _
    obtain ⟨i,hi⟩ := sortedLabel_reaches_r460 u (hCard u.1 u.2 hu) hx
    obtain ⟨j,hj⟩ := sortedLabel_reaches_r460 v (hCard v.1 v.2 hv) hy
    have hF : q≤KX x y := by
      by_cases hEq : i=j
      · subst j
        simpa only [a,DX,KX,hi,hj] using hDiagonal i
      · have hP := (le_inf hU hV).trans (hCross u v i j hEq)
        simpa only [KX,hi,hj] using hP
    exact ⟨hF,(le_inf (le_inf hMark (le_inf (hMark.trans (hY x))
      (hMark.trans (hY y)))) hF).trans (hSym _ _)⟩
  rcases lt_or_gt_of_ne hRowNe with h | h
  · exact ⟨u.1,v.1,h,u.2,v.2,fun he => hq (le_bot_iff.mp
      ((le_inf (le_inf hU hV) hQ).trans_eq he))⟩
  · rw [Finset.union_comm] at hQ
    exact ⟨v.1,u.1,h,v.2,u.2,fun he => hq (le_bot_iff.mp
      ((le_inf (le_inf hV hU) hQ).trans_eq he))⟩

end RelativeOCA
end JSP000933
