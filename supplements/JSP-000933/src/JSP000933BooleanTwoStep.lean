import JSP000933BooleanUncountability

open scoped Cardinal

namespace JSP000933
namespace BooleanTwoStep

open BooleanCompletion OpenGraphForcing

universe u v w
variable {B : Type u} [CompleteBooleanAlgebra B] {Q : Type v}

structure Stage (B : Type u) (Q : Type v) [CompleteBooleanAlgebra B] where
  admitted : Q → B
  leVal : Q → Q → B
  reflVal : ∀ q, admitted q ≤ leVal q q
  transVal : ∀ q r s, leVal q r ⊓ leVal r s ≤ leVal q s

noncomputable def Stage.compVal (S : Stage B Q) (q r : Q) : B :=
  ⨆ t, S.admitted t ⊓ (S.leVal t q ⊓ S.leVal t r)

structure Condition (S : Stage B Q) where
  base : B
  name : Q
  nonzero : base ≠ ⊥
  admitted : base ≤ S.admitted name

instance (S : Stage B Q) : Preorder (Condition S) where
  le p q := p.base ≤ q.base ∧ p.base ≤ S.leVal p.name q.name
  le_refl p := ⟨le_rfl,p.admitted.trans (S.reflVal _)⟩
  le_trans p q r hpq hqr := ⟨hpq.1.trans hqr.1,
    (le_inf hpq.2 (hpq.1.trans hqr.2)).trans (S.transVal _ _ _)⟩

theorem compatible_iff_nonzero_r78 {S : Stage B Q} (p q : Condition S) :
    Compatible p q ↔ (p.base ⊓ q.base) ⊓ S.compVal p.name q.name ≠ ⊥ := by
  constructor
  · rintro ⟨t,htp,htq⟩ h
    have h₁ : t.base ≤ p.base ⊓ q.base := le_inf htp.1 htq.1
    have h₂ : t.base ≤ S.compVal p.name q.name :=
      le_iSup_of_le t.name (le_inf t.admitted (le_inf htp.2 htq.2))
    exact t.nonzero (le_bot_iff.mp ((le_inf h₁ h₂).trans_eq h))
  · intro h
    have hex : ∃ t : Q,
        ((p.base ⊓ q.base) ⊓ (S.admitted t ⊓ (S.leVal t p.name ⊓ S.leVal t q.name))) ≠ ⊥ := by
      by_contra hNone
      apply h
      apply le_bot_iff.mp
      rw [Stage.compVal,inf_iSup_eq]
      apply iSup_le
      intro t
      by_contra hn
      exact hNone ⟨t,fun he => hn he.le⟩
    obtain ⟨t,ht⟩ := hex
    let b := (p.base ⊓ q.base) ⊓ (S.admitted t ⊓ (S.leVal t p.name ⊓ S.leVal t q.name))
    exact ⟨⟨b,t,ht,inf_le_right.trans inf_le_left⟩,
      ⟨inf_le_left.trans inf_le_left,inf_le_right.trans (inf_le_right.trans inf_le_left)⟩,
      ⟨inf_le_left.trans inf_le_right,inf_le_right.trans (inf_le_right.trans inf_le_right)⟩⟩

def Stage.BooleanAntichainCCC (S : Stage B Q) : Prop :=
  ∀ (f : OmegaOneIndex → Q) (g : OmegaOneIndex → B),
    (∀ i, g i ≤ S.admitted (f i)) →
    (∀ i j, i ≠ j → Disjoint (g i ⊓ g j) (S.compVal (f i) (f j))) →
    countableCoverageValue g = ⊤

private theorem exists_index_uncountable_r78 {T : Type w} (h : ¬ Countable T) :
    Nonempty (OmegaOneIndex ↪ T) := by
  have hle : Cardinal.mk (ULift.{w} OmegaOneIndex) ≤ Cardinal.mk T := by
    rw [Cardinal.mk_uLift,mk_OmegaOneIndex_r61,Cardinal.lift_aleph,Ordinal.lift_one,
      ← Cardinal.succ_aleph0]
    apply Order.succ_le_of_lt
    exact lt_of_not_ge fun ht => h (Cardinal.mk_le_aleph0_iff.mp ht)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hle
  exact ⟨⟨fun i => e (ULift.up i),fun _ _ hi => congrArg ULift.down (e.injective hi)⟩⟩

theorem countableAntichains_twoStep_r78 {S : Stage B Q}
    (hB : BooleanCCC B) (hS : S.BooleanAntichainCCC) :
    HasCountableAntichains (Condition S) := by
  classical
  intro F hAnt
  by_contra hF
  obtain ⟨e⟩ := exists_index_uncountable_r78 (fun h => hF (Set.countable_coe_iff.mp h))
  let f (i : OmegaOneIndex) := (e i).1.name
  let g (i : OmegaOneIndex) := (e i).1.base
  have hN (i : OmegaOneIndex) : g i ≠ ⊥ := (e i).1.nonzero
  have hA (i : OmegaOneIndex) : g i ≤ S.admitted (f i) := (e i).1.admitted
  have hAnti (i j : OmegaOneIndex) (hij : i ≠ j) :
      Disjoint (g i ⊓ g j) (S.compVal (f i) (f j)) := by
    apply disjoint_iff_inf_le.mpr
    apply le_of_eq
    by_contra hn
    have hne : (e i).1 ≠ (e j).1 := fun he => hij (e.injective (Subtype.ext he))
    exact hAnt (e i).1 (e i).2 (e j).1 (e j).2 hne
      ((compatible_iff_nonzero_r78 (e i).1 (e j).1).mpr hn)
  exact countableCoverageValue_ne_top_r68 hB OmegaOneIndex_not_countable_r61 g hN
    (hS f g hA hAnti)

end BooleanTwoStep
end JSP000933
