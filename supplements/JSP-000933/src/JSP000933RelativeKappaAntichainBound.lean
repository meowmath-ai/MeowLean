import JSP000933RelativeKappaChoice

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel MarkedForcing OpenGraphForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

structure IncreasingKappaOccurrences (W : GroundContinuumSuccIndex→N→B) (m : B) where
  pick : OmegaOneIndex→DiscreteChoiceOn (KappaOccurrence N) m
  valid : ∀ i x,(pick i).value x≤W x.1 x.2
  increasing : ∀ i j,i<j→∀ y,(pick j).value y≤
    guardByChoice (pick i) (fun x => kappaRowBefore x y)

theorem exists_increasingKappaOccurrences_r475 (hB : BoundsSmallKappaNames B)
    (W : GroundContinuumSuccIndex→N→B) (m : B)
    (hU : m≤unboundedKappaValue (fun i => ⨆ n,W i n)) :
    Nonempty (IncreasingKappaOccurrences W m) := by
  classical
  let Good := {C : DiscreteChoiceOn (KappaOccurrence N) m // ∀ x,C.value x≤W x.1 x.2}
  have hStep (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i<j→Good) :
      ∃ C : DiscreteChoiceOn (KappaOccurrence N) m,(∀ x,C.value x≤W x.1 x.2) ∧
        ∀ (i : ↥(Set.Iio j)) y,C.value y≤guardByChoice (prev i.val i.property).val
          (fun x => kappaRowBefore x y) := by
    have hI : Cardinal.mk (↥(Set.Iio j))<GroundContinuumSucc :=
      (Cardinal.mk_le_aleph0_iff.mpr (OmegaOneIndex_initial_countable_r61 j)).trans_lt
        (Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _))
    exact exists_nextKappaOccurrence_r474 hB hI W m hU (fun i => (prev i.val i.property).val)
  let next (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i<j→Good) : Good :=
    ⟨Classical.choose (hStep j prev),(Classical.choose_spec (hStep j prev)).1⟩
  let s : OmegaOneIndex→Good := WellFounded.fix wellFounded_lt next
  have hs (j : OmegaOneIndex) : s j=next j (fun i _ => s i) :=
    WellFounded.fix_eq wellFounded_lt next j
  refine ⟨⟨fun i => (s i).val,fun i => (s i).property,fun i j hij y => ?_⟩⟩
  change (s j).val.value y≤guardByChoice (s i).val (fun x => kappaRowBefore x y)
  conv_lhs => rw [hs j]
  exact (Classical.choose_spec (hStep j (fun i _ => s i))).2 ⟨i,hij⟩ y

theorem IncreasingKappaOccurrences.overlap_r475 {W : GroundContinuumSuccIndex→N→B}
    {m : B} (S : IncreasingKappaOccurrences W m)
    {i j : OmegaOneIndex} (hij : i<j) (x y : KappaOccurrence N) :
    (S.pick i).value x⊓(S.pick j).value y≤kappaRowBefore x y := by
  rw [inf_comm]
  exact (inf_le_inf (S.increasing i j hij y) le_rfl).trans
    (guardByChoice_elim_r445 (S.pick i) (fun x => kappaRowBefore x y) x)

theorem unboundedValue_const_r475 (m : B) : unboundedValue (fun _ => m)=m := by
  have h (b : OmegaOneIndex) : aboveValue (fun _ => m) b=m := by
    apply le_antisymm (iSup_le (fun _ => le_rfl))
    obtain ⟨j,hj⟩ := OmegaOneIndex_countable_bounded_r61 {b} (Set.countable_singleton b)
    exact le_iSup (fun _ : {k : OmegaOneIndex // b < k} => m) ⟨j,hj b (Set.mem_singleton _)⟩
  apply le_antisymm
  · have hI : Nonempty OmegaOneIndex :=
      Ordinal.nonempty_toType_iff.mpr (ne_of_gt Cardinal.isRegular_aleph_one.ord_pos)
    obtain ⟨i⟩ := hI
    exact (iInf_le _ i).trans_eq (h i)
  · exact le_iInf (fun i => (h i).ge)

theorem relativeCCC_kappaAntichain_bounded_r475 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsSmallKappaNames B)
    (W : GroundContinuumSuccIndex→N→B)
    (hVal : ∀ i n,W i n≤Q.valid n)
    (hApart : ∀ i j,i<j→∀ n k,(W i n⊓W j k)⊓commonRefinementValue Q n k=⊥) :
    unboundedKappaValue (fun i => ⨆ n,W i n)=⊥ := by
  classical
  let m := unboundedKappaValue (fun i => ⨆ n,W i n)
  obtain ⟨S⟩ := exists_increasingKappaOccurrences_r475 hB W m le_rfl
  let V (i : OmegaOneIndex) (n : N) := ⨆ a : GroundContinuumSuccIndex,(S.pick i).value (a,n)
  have hV (i : OmegaOneIndex) (n : N) : V i n≤Q.valid n :=
    iSup_le (fun a => (S.valid i (a,n)).trans (hVal a n))
  have hA (i j : OmegaOneIndex) (hij : i<j) (n k : N) :
      (V i n⊓V j k)⊓commonRefinementValue Q n k=⊥ := by
    apply le_bot_iff.mp
    simp only [V,iSup_inf_eq,inf_iSup_eq]
    apply iSup_le
    intro b
    apply iSup_le
    intro a
    by_cases hab : a<b
    · exact (inf_le_inf (inf_le_inf (S.valid i (a,n)) (S.valid j (b,k))) le_rfl).trans
        (hApart a b hab n k).le
    · have h0 : (S.pick i).value (a,n)⊓(S.pick j).value (b,k)≤(⊥ : B) := by
        simpa only [kappaRowBefore,ite_eq_right hab] using S.overlap_r475 hij (a,n) (b,k)
      exact inf_le_left.trans h0
  have hR : (fun i => ⨆ n,V i n)=(fun _ => m : OmegaOneIndex→B) := by
    funext i
    apply le_antisymm
    · exact iSup_le (fun n => iSup_le (fun a => (S.pick i).each_le (a,n)))
    · apply (S.pick i).covers.ge.trans
      apply iSup_le
      intro x
      exact le_iSup_of_le x.2 (le_iSup (fun a => (S.pick i).value (a,x.2)) x.1)
  have hN := hQ V hV hA
  change unboundedValue (fun i => ⨆ n,V i n)=⊥ at hN
  rw [hR,unboundedValue_const_r475] at hN
  exact hN

end RelativeOCA
end JSP000933
