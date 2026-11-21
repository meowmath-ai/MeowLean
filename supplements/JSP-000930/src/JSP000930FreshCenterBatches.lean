import JSP000930FreshPinRows
import JSP000930OldRawRefinementTransport

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Positive.Dyadic
open JSP000933.MarkedForcing JSP000933.BooleanCompletion JSP000933.ForcingTransport

variable {B I J X : Type} [NontrivialCompleteBooleanAlgebra B]

structure FreshCenterBatch (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (p : I → SymbolicTrace J) (A : J → Prop) (z : J)
    (t : CohenTotal B (X × ℕ)) (route : FreshRows p z × Bool → X)
    (interval : FreshRows p z × Bool → Interval) (m : B) where
  fresh : ∀ k : FreshRows p z,FreshCenterPlan site (H k.1) (p k.1)
    (newPinNumber (p k.1) z k.2) A t (fun j => route (k,j)) (fun j => interval (k,j)) m
  old_support : ∀ i,¬ HasNewPin (p i) z → SymbolicAt A (p i)
  old_valid : ∀ i,¬ HasNewPin (p i) z → m ≤ polyValid site (H i)
    (decodeSymbolicTrace site (H i) (p i))

namespace FreshCenterBatch

variable {site : J → ComplexBits B} {H : I → J → ℕ → ComplexBits B}
variable {p : I → SymbolicTrace J} {A : J → Prop} {z : J}
variable {t : CohenTotal B (X × ℕ)}
variable {route : FreshRows p z × Bool → X} {interval : FreshRows p z × Bool → Interval}
variable {m : B}

open scoped Classical in
noncomputable def center (S : FreshCenterBatch site H p A z t route interval m) (i : I) :
    PolyTrace B J :=
  if h : HasNewPin (p i) z then
    let G := S.fresh ⟨i,h⟩
    oldCenteredTrace site (H i) (p i) (newPinNumber (p i) z h) G.c G.R G.e G.pos_budget
  else decodeSymbolicTrace site (H i) (p i)

theorem center_of_fresh (S : FreshCenterBatch site H p A z t route interval m) (k : FreshRows p z) :
    S.center k.1 = oldCenteredTrace site (H k.1) (p k.1) (newPinNumber (p k.1) z k.2)
      (S.fresh k).c (S.fresh k).R (S.fresh k).e (S.fresh k).pos_budget := by
  classical
  simp only [center,dite_eq_left k.2]

theorem center_of_old (S : FreshCenterBatch site H p A z t route interval m)
    (i : I) (h : ¬ HasNewPin (p i) z) :
    S.center i = decodeSymbolicTrace site (H i) (p i) := by
  classical
  simp only [center,dite_eq_right h]

theorem center_valid (S : FreshCenterBatch site H p A z t route interval m) (i : I) :
    m ≤ polyValid site (H i) (S.center i) := by
  classical
  by_cases h : HasNewPin (p i) z
  · rw [S.center_of_fresh ⟨i,h⟩]
    exact (S.fresh ⟨i,h⟩).center_valid
  · rw [S.center_of_old i h]
    exact S.old_valid i h

theorem center_support (S : FreshCenterBatch site H p A z t route interval m) (i : I) :
    ∀ j ∈ (S.center i).pins,A j := by
  classical
  by_cases h : HasNewPin (p i) z
  · rw [S.center_of_fresh ⟨i,h⟩]
    exact (S.fresh ⟨i,h⟩).center_support
  · rw [S.center_of_old i h]
    exact (decodeSymbolicTrace_support_iff site (H i) (p i)).mpr (S.old_support i h)

end FreshCenterBatch

set_option maxHeartbeats 700000 in
theorem exists_fresh_center_batch [Fintype I]
    (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (site' : J → ComplexBits (CohenBA B (X × ℕ)))
    (H' : I → J → ℕ → ComplexBits (CohenBA B (X × ℕ)))
    (A : J → Prop) (z : J)
    (hSite : ∀ j,A j ∨ j=z → (site j).CutOn (⊤ : B))
    (hH : ∀ i j,A j → ∀ n,(H i j n).CutOn (⊤ : B))
    (hApart : ∀ j,A j ∨ j=z → ∀ k,A k ∨ k=z → j ≠ k →
      (⊤ : B) ≤ ((site j).name =ᴮ (site k).name)ᶜ)
    (hSmap : ∀ j,A j → (site j).map (markedCompleteValueMap (valuedCohen B (X × ℕ))) = site' j)
    (hHmap : ∀ i j,A j → ∀ n,
      (H i j n).map (markedCompleteValueMap (valuedCohen B (X × ℕ))) = H' i j n)
    (q : AnalyticRowTotal site' H' (fun j => A j ∨ j=z))
    (p : I → SymbolicTrace J) (hp : ∀ i,(q.trace i).val = some (p i))
    (t : CohenTotal B (X × ℕ)) (ht : imageCondition t ≤ q.mask)
    (route : FreshRows p z × Bool → X) (interval : FreshRows p z × Bool → Interval) :
    ∃ m : B,m ≠ ⊥ ∧ m ≤ t.mask ∧ Nonempty (FreshCenterBatch site H p A z t route interval m) := by
  classical
  have hSup (i) : SymbolicAt (fun j => A j ∨ j=z) (p i) := by
    have h := (q.trace i).2
    rw [hp i] at h
    exact h
  let F := markedCompleteValueMap (valuedCohen B (X × ℕ))
  let T (k : FreshRows p z) (m : B) :=
    Nonempty (FreshCenterPlan site (H k.1) (p k.1) (newPinNumber (p k.1) z k.2) A
      t (fun j => route (k,j)) (fun j => interval (k,j)) m)
  obtain ⟨m,hm,hmT,hM⟩ := exists_finitely_refined_marks T
    (by
      intro k a b hab hB
      obtain ⟨G⟩ := hB
      exact ⟨G.mono hab⟩) t.mask t.nonzero (by
      intro k b hb hbT
      let i := newPinNumber (p k.1) z k.2
      have hi : (pinAt (p k.1) i).1 = z := newPinNumber_site (p k.1) z k.2
      have hOld (j : J) (hj : j ∈ (p k.1).pins.map Prod.fst)
          (hn : j ≠ (pinAt (p k.1) i).1) : A j :=
        (hSup k.1 j hj).elim id (fun h => (hn (h.trans hi.symm)).elim)
      exact exists_fresh_center_plan site (H k.1) (p k.1) i A t
        (fun j => route (k,j)) (fun j => interval (k,j)) b hb
        (fun j hj => cutOn_mono930 (hSite j (hSup k.1 j hj)) le_top)
        (fun j hj hn n => cutOn_mono930 (hH k.1 j (hOld j hj hn) n) le_top) hOld
        (fun j hj v hv h => le_top.trans (hApart j (hSup k.1 j hj) v (hSup k.1 v hv) h)))
  let oldSupp (i : I) (h : ¬ HasNewPin (p i) z) : SymbolicAt A (p i) :=
    old_support_if_no_new (p i) z (hSup i) h
  refine ⟨m,hm,hmT,⟨⟨fun k => Classical.choice (hM k),oldSupp,?_⟩⟩⟩
  intro i hi
  have hC : imageCondition t ≤ polyValid site' (H' i)
      (decodeSymbolicTrace site' (H' i) (p i)) := by
    have h := ht.trans (q.valid.trans (iInf_le _ i))
    change imageCondition t ≤ (symbolicPolynomialQ site' (H' i)).valid (q.trace i).val at h
    rw [hp i] at h
    exact h
  have hV : imageCondition t ≤ F.toFun (polyValid site (H i)
      (decodeSymbolicTrace site (H i) (p i))) := by
    rw [symbolicPolyValid_partial_map F site (H i) site' (H' i) hSmap (hHmap i) (p i) (oldSupp i hi)]
    exact hC
  change imageCondition t ≤ baseEmbed (valuedCohen B (X × ℕ))
    (polyValid site (H i) (decodeSymbolicTrace site (H i) (p i))) at hV
  exact hmT.trans ((baseEmbed_reflects_mask_r427 _ _).mp hV)

end JSP000930.Negative
