import JSP000930ActualMarkedCohenSuccessor

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.MarkedForcing

inductive CertifiedStageLabel (N : Type) where
  | weak
  | list (head : N) (tail : List N) (ancestry : List (N × N))

namespace CertifiedStageLabel

variable {B N : Type} [CompleteBooleanAlgebra B]

def stored : CertifiedStageLabel N → List N
  | .weak => []
  | .list x t _ => x::t

def edges : CertifiedStageLabel N → List (N × N)
  | .weak => []
  | .list x t a => ((x::t).map (fun n => (x,n))) ++ a

instance : Preorder (CertifiedStageLabel N) where
  le p q := (∀ n ∈ q.stored,n ∈ p.stored) ∧ (∀ a ∈ q.edges,a ∈ p.edges)
  le_refl _ := ⟨fun _ h => h,fun _ h => h⟩
  le_trans _ _ _ hp hq := ⟨fun n hn => hp.1 n (hq.1 n hn),fun a ha => hp.2 a (hq.2 a ha)⟩

instance : OrderTop (CertifiedStageLabel N) where
  top := .weak
  le_top := by
    intro p
    exact ⟨fun n hn => (List.not_mem_nil hn).elim,fun a ha => (List.not_mem_nil ha).elim⟩

noncomputable instance : DecidableRel ((· ≤ ·) : CertifiedStageLabel N → CertifiedStageLabel N → Prop) :=
  Classical.decRel _

def head (Q : ValuedPoset B N) : CertifiedStageLabel N → N
  | .weak => Q.weakest
  | .list n _ _ => n

noncomputable def admits (Q : ValuedPoset B N) (p : CertifiedStageLabel N) : B :=
  ⨅ a : {a : N × N // a ∈ p.edges},Q.refines a.val.1 a.val.2

theorem admits_le_edge (Q : ValuedPoset B N) (p : CertifiedStageLabel N)
    (a : N × N) (h : a ∈ p.edges) : admits Q p ≤ Q.refines a.1 a.2 :=
  iInf_le (fun v : {v : N × N // v ∈ p.edges} => Q.refines v.val.1 v.val.2) ⟨a,h⟩

theorem admits_top (Q : ValuedPoset B N) : admits Q (⊤ : CertifiedStageLabel N) = ⊤ := by
  apply top_unique
  apply le_iInf
  intro a
  exact (List.not_mem_nil a.2).elim

theorem admits_mono (Q : ValuedPoset B N) : Monotone (admits Q) := by
  intro p q hp
  apply le_iInf
  intro a
  exact admits_le_edge Q p a.val (hp.2 a.val a.2)

theorem admits_le_stored (Q : ValuedPoset B N) (p : CertifiedStageLabel N)
    (n : N) (h : n ∈ p.stored) : admits Q p ≤ Q.refines (p.head Q) n := by
  cases p with
  | weak => exact (List.not_mem_nil h).elim
  | list k l a =>
    exact admits_le_edge Q (.list k l a) (k,n)
      (List.mem_append_left _ (List.mem_map.mpr ⟨n,h,rfl⟩))

theorem admits_le_head (Q : ValuedPoset B N) (p : CertifiedStageLabel N) :
    admits Q p ≤ Q.valid (p.head Q) := by
  cases p with
  | weak =>
    change admits Q (⊤ : CertifiedStageLabel N) ≤ Q.valid Q.weakest
    rw [admits_top,Q.weakest_valid]
  | list n l a =>
    exact (admits_le_stored Q (.list n l a) n List.mem_cons_self).trans
      ((Q.refine_valid n n).trans inf_le_left)

theorem admits_singleton (Q : ValuedPoset B N) (n : N) :
    admits Q (.list n [] []) = Q.valid n := by
  apply le_antisymm (admits_le_head Q (.list n [] []))
  apply le_iInf
  intro a
  have he : a.val = (n,n) := List.mem_singleton.mp a.2
  rw [he]
  exact Q.refl n

def mergeWithHead (n : N) (u v : CertifiedStageLabel N) : CertifiedStageLabel N :=
  .list n (u.stored ++ v.stored) (u.edges ++ v.edges)

theorem mergeWithHead_left (n : N) (u v : CertifiedStageLabel N) : mergeWithHead n u v ≤ u :=
  ⟨fun x hx => List.mem_cons_of_mem _ (List.mem_append_left _ hx),
   fun a ha => List.mem_append_right _ (List.mem_append_left _ ha)⟩

theorem mergeWithHead_right (n : N) (u v : CertifiedStageLabel N) : mergeWithHead n u v ≤ v :=
  ⟨fun x hx => List.mem_cons_of_mem _ (List.mem_append_right _ hx),
   fun a ha => List.mem_append_right _ (List.mem_append_right _ ha)⟩

theorem admits_fresh_head (Q : ValuedPoset B N) (n : N) (u v : CertifiedStageLabel N)
    (b : B) (hNU : b ≤ Q.refines n (u.head Q)) (hNV : b ≤ Q.refines n (v.head Q))
    (hu : b ≤ admits Q u) (hv : b ≤ admits Q v) :
    b ≤ admits Q (mergeWithHead n u v) := by
  have hN : b ≤ Q.valid n := hNU.trans ((Q.refine_valid _ _).trans inf_le_left)
  apply le_iInf
  intro a
  have ha : a.val ∈ ((n::(u.stored++v.stored)).map (fun k => (n,k))) ++
      (u.edges++v.edges) := a.2
  rcases List.mem_append.mp ha with ha|ha
  · obtain ⟨k,hk,hak⟩ := List.mem_map.mp ha
    rw [← hak]
    rcases List.mem_cons.mp hk with h|h
    · simpa only [h] using hN.trans (Q.refl n)
    rcases List.mem_append.mp h with h|h
    · exact (le_inf hNU (hu.trans (admits_le_stored Q u k h))).trans (Q.trans _ _ _)
    · exact (le_inf hNV (hv.trans (admits_le_stored Q v k h))).trans (Q.trans _ _ _)
  · rcases List.mem_append.mp ha with ha|ha
    · exact hu.trans (admits_le_edge Q u a.val ha)
    · exact hv.trans (admits_le_edge Q v a.val ha)

end CertifiedStageLabel

end JSP000930.Negative
