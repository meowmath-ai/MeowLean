import JSP000933RelativeSharedVertexFibers

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing MarkedForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem actual_cardRelativeCliqueCCC_r462 (hB : BoundsCountableOmegaOneNames B)
    (D : (ℕ→B)→B) (K : Word×Word→B) (m : B)
    (hIrr : ∀ x,m⊓D x≤(colorValue K x x)ᶜ)
    (hSym : ∀ x y,(m⊓(D x⊓D y))⊓colorValue K x y≤colorValue K y x)
    (Y : OmegaOneIndex→ℕ→B) (hY : ∀ i,m≤D (Y i))
    (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e)
    (hAvoid : ∀ j,RelativeAvoidsOn D K m (relativeScheduleFromEnum e) j (fun i => Y i.val) (Y j)) :
    ∀ n,CardRelativeCCC m (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j)) n := by
  classical
  let DX (i : OmegaOneIndex) := D (Y i)
  let KX (i j : OmegaOneIndex) := colorValue K (Y i) (Y j)
  intro n
  induction n with
  | zero => exact CardRelativeCCC.zero_r455 m DX KX
  | succ n lower =>
    intro W hW hSize hPairs
    let u := unboundedValue (rowLabelWeight W)
    change u=⊥
    by_contra hu
    have hF (v : OmegaOneIndex) : u≤(unboundedValue (vertexFiber W v))ᶜ := by
      rw [sharedVertexFiber_bounded_r461 m DX KX lower W hW hSize hPairs v,compl_bot]
      exact le_top
    obtain ⟨S⟩ := exists_relativeDisjointLabels_r448 hB W u le_rfl hF
    let V := joinedLabelWeight S
    have hVu : u≤unboundedValue (rowLabelWeight V) := joinedLabelWeight_unbounded_r449 S
    have hV (i : OmegaOneIndex) (s : Finset OmegaOneIndex) : V i s≤W i s :=
      joinedLabelWeight_le_r449 S i s
    let X (x : LabelCandidate) (j : Fin (n+1)) := Y (sortedLabel (n+1) x j)
    have hOff (i : OmegaOneIndex) (s : Finset OmegaOneIndex) (a b : Fin (n+1)) (hab : a≠b) :
        V i s≤colorValue K (X (i,s) a) (X (i,s) b) := by
      by_cases hs : s.card=n+1
      · have ha := sortedLabel_mem_r460 (i,s) hs a
        have hb := sortedLabel_mem_r460 (i,s) hs b
        have hne := fun he => hab ((sortedLabel_strictMono_r460 (i,s) hs).injective he)
        exact (hV i s).trans ((hW i s).trans (cliqueAdmitted_le_edge_r121 _ _ _ ha hb hne))
      · exact (((hV i s).trans_eq (hSize i s hs))).trans bot_le
    have hThin := rectangularWeight_unbounded_r453 hB K X V hOff
    have hCode : ∃ c : OffDiagonalCode (n+1),
        unboundedValue (rowLabelWeight (rectangularWeight K X V c))≠⊥ := by
      by_contra hn
      have h0 (c : OffDiagonalCode (n+1)) :
          unboundedValue (rowLabelWeight (rectangularWeight K X V c))=⊥ := by
        by_contra hc
        exact hn ⟨c,hc⟩
      rw [hThin] at hVu
      exact hu (le_bot_iff.mp (hVu.trans (iSup_le (fun c => (h0 c).le))))
    obtain ⟨c,hc⟩ := hCode
    let T := rectangularWeight K X V c
    have hTV (i : OmegaOneIndex) (s : Finset OmegaOneIndex) : T i s≤V i s := inf_le_left
    have hTW (i : OmegaOneIndex) (s : Finset OmegaOneIndex) : T i s≤W i s := (hTV i s).trans (hV i s)
    have hOwn (i : OmegaOneIndex) (s : Finset OmegaOneIndex) : T i s≤cliqueAdmitted m DX KX s :=
      (hTW i s).trans (hW i s)
    have hDim (i : OmegaOneIndex) (s : Finset OmegaOneIndex) (hs : s.card≠n+1) : T i s=⊥ :=
      le_bot_iff.mp ((hTW i s).trans_eq (hSize i s hs))
    have hDis (i j : OmegaOneIndex) (hij : i<j) (s t : Finset OmegaOneIndex) (h : ¬Disjoint s t) :
        Disjoint (T i s) (T j t) := by
      have hNe : ((i,s) : LabelCandidate)≠(j,t) := fun he => (ne_of_lt hij) (congrArg Prod.fst he)
      have hBase := joinedLabelWeight_disjoint_invalidPair_r449 S (i,s) (j,t) hNe (Or.inr h)
      exact (hBase.mono_left (hTV i s)).mono_right (hTV j t)
    have hRow (x y : LabelCandidate) (hne : x≠y) (he : x.1=y.1) :
        Disjoint (T x.1 x.2) (T y.1 y.2) := by
      have hBase := joinedLabelWeight_disjoint_invalidPair_r449 S x y hne (Or.inl he)
      exact (hBase.mono_left (hTV x.1 x.2)).mono_right (hTV y.1 y.2)
    obtain ⟨i,j,hij,s,t,hT⟩ := relativeRectangularPair_r460 hB D K m hIrr hSym Y hY e hE hAvoid lower
      T hc hOwn hDim hDis hRow (fun x y _ _ h => rectangularWeight_cross_r453 K X V c x y h)
    have hLe : (T i s⊓T j t)⊓cliqueAdmitted m DX KX (s∪t)≤
        (W i s⊓W j t)⊓cliqueAdmitted m DX KX (s∪t) :=
      inf_le_inf (inf_le_inf (hTW i s) (hTW j t)) le_rfl
    exact hT (le_bot_iff.mp (hLe.trans_eq (hPairs i j hij s t)))

theorem actual_relativeCliqueCCC_r462 (hB : BoundsCountableOmegaOneNames B)
    (D : (ℕ→B)→B) (K : Word×Word→B) (m : B)
    (hIrr : ∀ x,m⊓D x≤(colorValue K x x)ᶜ)
    (hSym : ∀ x y,(m⊓(D x⊓D y))⊓colorValue K x y≤colorValue K y x)
    (Y : OmegaOneIndex→ℕ→B) (hY : ∀ i,m≤D (Y i))
    (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e)
    (hAvoid : ∀ j,RelativeAvoidsOn D K m (relativeScheduleFromEnum e) j (fun i => Y i.val) (Y j)) :
    ForcesRelativeCCC (relativeCliquePoset m (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j))) :=
  relativeCCC_of_cardRelativeCCC_r455 hB m _ _
    (actual_cardRelativeCliqueCCC_r462 hB D K m hIrr hSym Y hY e hE hAvoid)

end RelativeOCA
end JSP000933
