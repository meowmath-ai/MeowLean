import JSP000933CliqueAdmissionMerge

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

def BooleanPairForCard (mark : B) (d : OmegaOneIndex → B)
    (K : OmegaOneIndex → OmegaOneIndex → B) (n : ℕ) : Prop :=
  ∀ {I : Type} (s : I → Finset OmegaOneIndex) (w : I → B), ¬ Countable I →
    (∀ i, (s i).card = n) →
    (∀ i, w i ≠ ⊥ ∧ w i ≤ cliqueAdmitted mark d K (s i)) →
    ∃ i j : I, i ≠ j ∧ ∃ q : B, q ≠ ⊥ ∧ q ≤ w i ∧ q ≤ w j ∧
      q ≤ cliqueAdmitted mark d K (s i ∪ s j)

theorem booleanPair_disjoint_succ_r156 (hCCC : BooleanCCC B)
    (D : (ℕ → B) → B) (K : Word × Word → B) (mark : B)
    (hIrr : ∀ x, mark ⊓ D x ≤ (colorValue K x x)ᶜ)
    (hSym : ∀ x y, (mark ⊓ (D x ⊓ D y)) ⊓ colorValue K x y ≤ colorValue K y x)
    (S : BooleanAvoidanceSchedule B) (Y : OmegaOneIndex → ℕ → B)
    (hY : ∀ i, mark ≤ D (Y i))
    (hAvoid : ∀ j, AvoidsOn D K mark S j (fun i => Y i.1) (Y j))
    {n : ℕ} (lower : BooleanPairForCard mark (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j)) n)
    {I : Type} (s : I → Finset OmegaOneIndex) (w : I → B) (hI : ¬ Countable I)
    (hCard : ∀ i, (s i).card = n+1)
    (hW : ∀ i, w i ≠ ⊥ ∧ w i ≤ cliqueAdmitted mark (fun i => D (Y i))
      (fun i j => colorValue K (Y i) (Y j)) (s i))
    (hDis : ∀ i j, i ≠ j → Disjoint (s i) (s j)) :
    ∃ i j : I, i ≠ j ∧ ∃ q : B, q ≠ ⊥ ∧ q ≤ w i ∧ q ≤ w j ∧
      q ≤ cliqueAdmitted mark (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j)) (s i ∪ s j) := by
  classical
  let D' (i : OmegaOneIndex) := D (Y i)
  let K' (i j : OmegaOneIndex) := colorValue K (Y i) (Y j)
  let O (i : I) : Fin (n+1) ≃o ↥(s i) := Finset.orderIsoOfFin (s i) (hCard i)
  let a (i : I) (j : Fin (n+1)) : OmegaOneIndex := (O i j).1
  have hA (i : I) : StrictMono (a i) := (O i).strictMono
  have hMem (i : I) (j : Fin (n+1)) : a i j ∈ s i := (O i j).2
  have hBase (i : I) : w i ≤ mark :=
    (hW i).2.trans ((cliqueAdmitted_le_vertex_r121 mark D' K' (hMem i (Fin.last n))).trans inf_le_left)
  have hEdge (i : I) (j k : Fin (n+1)) (hne : j ≠ k) : w i ≤ K' (a i j) (a i k) :=
    (hW i).2.trans (cliqueAdmitted_le_edge_r121 mark D' K' (hMem i j) (hMem i k)
      (fun he => hne ((hA i).injective he)))
  obtain ⟨T,hT,v,hV,hRect⟩ := exists_uniformOffDiagonal_r153 K (fun i j => Y (a i j)) w
    hI (fun i => (hW i).1) hEdge
  have hLast : Function.Injective (fun i : ↥T => a i.1 (Fin.last n)) := by
    intro i j he
    by_contra hn
    have hne : i.1 ≠ j.1 := fun he => hn (Subtype.ext he)
    change a i.val (Fin.last n) = a j.val (Fin.last n) at he
    exact (Finset.disjoint_left.mp (hDis i.1 j.1 hne) (hMem i.1 (Fin.last n)))
      (he.symm ▸ hMem j.1 (Fin.last n))
  have hStem : LowerStemPairs K (fun i : ↥T => sampleFromTuple Y (a i.1) (v i)) := by
    intro J f hf hJ u hu
    let stem (j : J) := prefixFinset_r64 (a (f j).1)
    have hSub (j : J) : stem j ⊆ s (f j).1 := by
      intro k hk
      obtain ⟨l,hl⟩ := (mem_prefixFinset_r64.mp hk)
      exact hl ▸ hMem (f j).1 l.castSucc
    have hAdm (j : J) : u j ≤ cliqueAdmitted mark D' K' (stem j) :=
      ((hu j).2.trans ((hV (f j)).2.trans (hW (f j).1).2)).trans
        (cliqueAdmitted_anti_r121 mark D' K' (hSub j))
    obtain ⟨j,k,hjk,q,hq,hqj,hqk,hAd⟩ := lower stem u hJ
      (fun j => card_prefixFinset_r64 (p := a (f j).1) (hA (f j).1))
      (fun j => ⟨(hu j).1,hAdm j⟩)
    have hne : (f j).1 ≠ (f k).1 := fun he => hjk (hf (Subtype.ext he))
    have hPair : q ≤ matchedValue K (sampleFromTuple Y (a (f j).1) (v (f j))).stem
        (sampleFromTuple Y (a (f k).1) (v (f k))).stem := by
      apply le_iInf
      intro i
      have hlj : a (f j).1 i.castSucc ∈ stem j := mem_prefixFinset_r64.mpr ⟨i,rfl⟩
      have hlk : a (f k).1 i.castSucc ∈ stem k := mem_prefixFinset_r64.mpr ⟨i,rfl⟩
      have hd : a (f j).1 i.castSucc ≠ a (f k).1 i.castSucc := by
        intro he
        exact (Finset.disjoint_left.mp (hDis (f j).1 (f k).1 hne) ((hSub j) hlj))
          (he.symm ▸ (hSub k) hlk)
      exact hAd.trans (cliqueAdmitted_le_edge_r121 mark D' K'
        (Finset.mem_union.mpr (Or.inl hlj)) (Finset.mem_union.mpr (Or.inr hlk)) hd)
    exact ⟨j,k,hjk,fun he => hq (le_bot_iff.mp ((le_inf (le_inf hqj hqk) hPair).trans_eq he))⟩
  obtain ⟨i,j,hne,q,hq,hqi,hqj,hAll⟩ := booleanRectangularPair_r152 hCCC D K mark hIrr hSym
    S Y hY hAvoid (fun i : ↥T => a i.1) v hT
    (fun i => ⟨(hV i).1,(hV i).2.trans (hBase i.1)⟩)
    (fun i => hA i.1) hLast hRect hStem
  have hi : q ≤ w i.1 := hqi.trans (hV i).2
  have hj : q ≤ w j.1 := hqj.trans (hV j).2
  refine ⟨i.1,j.1,fun he => hne (Subtype.ext he),q,hq,hi,hj,?_⟩
  apply cliqueAdmitted_union_r155 mark D' K' (hi.trans (hW i.1).2) (hj.trans (hW j.1).2)
  intro x hx y hy _
  obtain ⟨r,hr⟩ := (O i.1).surjective ⟨x,hx⟩
  obtain ⟨t,ht⟩ := (O j.1).surjective ⟨y,hy⟩
  have he₁ : a i.1 r = x := congrArg Subtype.val hr
  have he₂ : a j.1 t = y := congrArg Subtype.val ht
  have hForward : q ≤ K' x y := by
    rw [← he₁,← he₂]
    exact hAll r t
  have hMark := hi.trans (hBase i.1)
  exact ⟨hForward,(le_inf (le_inf hMark (le_inf (hMark.trans (hY x)) (hMark.trans (hY y)))) hForward).trans
    (hSym (Y x) (Y y))⟩

end CantorCodes
end JSP000933
