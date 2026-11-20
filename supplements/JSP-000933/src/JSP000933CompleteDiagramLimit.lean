import JSP000933CompleteDiagramPreorder
import JSP000933BooleanDecisions
import JSP000933BooleanNamedCliqueStage
import JSP000933CompleteValueMap

open Lattice

namespace JSP000933
namespace CompleteDiagram

open BooleanCompletion BooleanNames ForcingTransport

variable {I : Type} [LinearOrder I] (S : System I) [hS : IsComplete S]

abbrev LimitBA := RO (Condition S)

instance limitConditions_nonempty [Nonempty I] : Nonempty (Condition S) :=
  Nonempty.map (fun i => Condition.atStage i (⊤ : S.algebra i) top_ne_bot) ‹Nonempty I›

noncomputable def limitEmbed (i : I) (a : S.algebra i) : LimitBA S :=
  ⨆ t : {t : S.algebra i // t ≠ ⊥ ∧ t ≤ a},
    imageCondition (Condition.atStage i t.val t.property.1)

theorem image_le_limitEmbed (i : I) (a : S.algebra i) (p : Condition S) {k : I}
    (hp : p.stage ≤ k) (hi : i ≤ k)
    (hle : S.transition hp p.value ≤ S.transition hi a) :
    imageCondition p ≤ limitEmbed S i a := by
  have ha : a ≠ ⊥ := by
    intro he
    have hle' := hle
    rw [he, hS.bot hi] at hle'
    exact transition_ne_bot hS hp p.positive (le_bot_iff.mp hle')
  let q := Condition.atStage i a ha
  have hpq : p ≤ q := ⟨k, hp, hi, hle⟩
  exact (imageCondition_mono_r50 hpq).trans (le_iSup (fun t : {t : S.algebra i // t ≠ ⊥ ∧ t ≤ a} =>
        imageCondition (Condition.atStage i t.val t.property.1)) ⟨a,ha,le_rfl⟩)

theorem limitEmbed_mono (i : I) : Monotone (limitEmbed S i) := by
  intro a b hab
  apply iSup_le
  intro t
  exact le_iSup_of_le ⟨t.val,t.property.1,t.property.2.trans hab⟩ le_rfl

theorem limitEmbed_disjoint (i : I) {a b : S.algebra i} (hab : Disjoint a b) :
    Disjoint (limitEmbed S i a) (limitEmbed S i b) := by
  apply disjoint_iff_inf_le.mpr
  simp only [limitEmbed,iSup_inf_iSup]
  refine iSup_le fun ⟨p,q⟩ => disjoint_iff_inf_le.mp ?_
  by_contra hn
  have hc := (compatible_iff_not_disjoint_r50 _ _).mpr hn
  have hn' := (Condition.compatibleValue_iff hS
    (Condition.atStage i p.val p.property.1)
    (Condition.atStage i q.val q.property.1) (k := i) le_rfl le_rfl).mp hc
  apply hn'
  change S.transition (show i ≤ i from le_rfl) p.val ⊓
    S.transition (show i ≤ i from le_rfl) q.val = ⊥
  rw [S.identity,S.identity]
  exact hab.out _ (inf_le_left.trans p.property.2) (inf_le_right.trans q.property.2)

theorem image_le_limitEmbed_iff (i : I) (a : S.algebra i) (p : Condition S) {k : I}
    (hp : p.stage ≤ k) (hi : i ≤ k) :
    imageCondition p ≤ limitEmbed S i a ↔ S.transition hp p.value ≤ S.transition hi a := by
  constructor
  · intro h
    by_contra hn
    have hm : S.transition hp p.value ⊓ S.transition hi aᶜ ≠ ⊥ := by
      rw [hS.compl hi]
      intro hz
      exact hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr hz.le))
    let r := Condition.atStage k (S.transition hp p.value ⊓ S.transition hi aᶜ) hm
    have hr : r ≤ p := by
      refine ⟨k,le_rfl,hp,?_⟩
      change S.transition (show k ≤ k from le_rfl) (S.transition hp p.value ⊓ S.transition hi aᶜ) ≤ _
      rw [S.identity]
      exact inf_le_left
    have h1 : imageCondition r ≤ limitEmbed S i a := (imageCondition_mono_r50 hr).trans h
    have h2 : imageCondition r ≤ limitEmbed S i aᶜ := by
      apply image_le_limitEmbed S i aᶜ r (k := k) le_rfl hi
      change S.transition (show k ≤ k from le_rfl) (S.transition hp p.value ⊓ S.transition hi aᶜ) ≤ _
      rw [S.identity]
      exact inf_le_right
    exact imageCondition_ne_bot_r50 r
      ((limitEmbed_disjoint S i (disjoint_compl_right : Disjoint a aᶜ)).out _ h1 h2)
  · exact image_le_limitEmbed S i a p hp hi

theorem limitEmbed_reflects (i : I) {a b : S.algebra i} :
    limitEmbed S i a ≤ limitEmbed S i b ↔ a ≤ b := by
  constructor
  · intro h
    by_cases ha : a = ⊥
    · rw [ha]; exact bot_le
    · let p := Condition.atStage i a ha
      have h1 : imageCondition p ≤ limitEmbed S i a := le_iSup (fun t : {t : S.algebra i // t ≠ ⊥ ∧ t ≤ a} =>
        imageCondition (Condition.atStage i t.val t.property.1)) ⟨a,ha,le_rfl⟩
      have h2 := (image_le_limitEmbed_iff S i b p (k := i) le_rfl le_rfl).mp (h1.trans h)
      simpa only [p,Condition.atStage,S.identity] using h2
  · intro h
    exact limitEmbed_mono S i h

theorem limitEmbed_top (i : I) : limitEmbed S i ⊤ = ⊤ := by
  apply top_unique
  by_contra hn
  have hNZ : (limitEmbed S i ⊤)ᶜ ≠ ⊥ := fun he => hn (compl_eq_bot.mp he).ge
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hNZ
  let k := max p.stage i
  have h : imageCondition p ≤ limitEmbed S i ⊤ := by
    apply image_le_limitEmbed S i ⊤ p (k := k) (le_max_left _ _) (le_max_right _ _)
    rw [hS.top]; exact le_top
  exact imageCondition_ne_bot_r50 p (disjoint_compl_right.out _ h hp)

theorem limitEmbed_bot (i : I) : limitEmbed S i ⊥ = ⊥ := by
  apply le_bot_iff.mp
  apply iSup_le
  rintro ⟨v,hv,hle⟩
  exact False.elim (hv (le_bot_iff.mp hle))

theorem image_le_of_dense {P : Type} [Preorder P] (p : P) (x : RO P)
    (h : ∀ r ≤ p, ∃ s ≤ r, imageCondition s ≤ x) : imageCondition p ≤ x := by
  by_contra hn
  have hN : imageCondition p ⊓ xᶜ ≠ ⊥ := fun he =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨r,hr,hrx⟩ := exists_stronger_below_of_meet_r51 p xᶜ hN
  obtain ⟨s,hs,hsx⟩ := h r hr
  exact imageCondition_ne_bot_r50 s (disjoint_compl_right.out _ hsx
    ((imageCondition_mono_r50 hs).trans hrx))

theorem limitEmbed_joins (i : I) {D : Type} (v : D → S.algebra i) :
    limitEmbed S i (⨆ d,v d) = ⨆ d,limitEmbed S i (v d) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    let p := Condition.atStage i t.val t.property.1
    apply image_le_of_dense p
    intro r hr
    let k := max r.stage i
    have hrk : r.stage ≤ k := le_max_left _ _
    have hik : i ≤ k := le_max_right _ _
    have hle := (Condition.stronger_at hS r p hrk hik).mp hr
    let a := S.transition hrk r.value
    have ha : a ≠ ⊥ := transition_ne_bot hS hrk r.positive
    have hAS : a ≤ ⨆ d,S.transition hik (v d) := by
      rw [← hS.joins hik]
      exact hle.trans (transition_mono hS hik t.property.2)
    have hSome : ∃ d, a ⊓ S.transition hik (v d) ≠ ⊥ := by
      by_contra hn
      have hZ (d : D) : a ⊓ S.transition hik (v d) = ⊥ := by
        by_contra hz
        exact hn ⟨d,hz⟩
      apply ha
      calc
        a = a ⊓ (⨆ d,S.transition hik (v d)) := (inf_eq_left.mpr hAS).symm
        _ = ⨆ d,a ⊓ S.transition hik (v d) := inf_iSup_eq _ _
        _ = ⊥ := by simp only [hZ,iSup_bot]
    obtain ⟨d,hd⟩ := hSome
    let s := Condition.atStage k (a ⊓ S.transition hik (v d)) hd
    have hsr : s ≤ r := by
      refine ⟨k,le_rfl,hrk,?_⟩
      change S.transition (show k ≤ k from le_rfl) (a ⊓ S.transition hik (v d)) ≤ a
      rw [S.identity]
      exact inf_le_left
    have hst : imageCondition s ≤ limitEmbed S i (v d) := by
      apply image_le_limitEmbed S i (v d) s (k := k) le_rfl hik
      change S.transition (show k ≤ k from le_rfl) (a ⊓ S.transition hik (v d)) ≤ _
      rw [S.identity]
      exact inf_le_right
    exact ⟨s,hsr,le_iSup_of_le d hst⟩
  · exact iSup_le fun d => limitEmbed_mono S i (le_iSup v d)

theorem limitEmbed_compl (i : I) (a : S.algebra i) :
    limitEmbed S i aᶜ = (limitEmbed S i a)ᶜ := by
  classical
  symm
  apply IsCompl.compl_eq
  refine ⟨limitEmbed_disjoint S i disjoint_compl_right,codisjoint_iff_le_sup.mpr ?_⟩
  let v (d : Bool) : S.algebra i := if d then aᶜ else a
  have ha : (⨆ d,v d) = ⊤ := by
    apply top_unique
    have h1 : a ≤ ⨆ d,v d := le_iSup_of_le false (by simp [v])
    have h2 : aᶜ ≤ ⨆ d,v d := le_iSup_of_le true (by simp [v])
    exact (sup_compl_eq_top (x := a)).symm.trans_le (sup_le h1 h2)
  calc
    (⊤ : LimitBA S) = limitEmbed S i ⊤ := (limitEmbed_top S i).symm
    _ = limitEmbed S i (⨆ d,v d) := congrArg (limitEmbed S i) ha.symm
    _ = ⨆ d,limitEmbed S i (v d) := limitEmbed_joins S i v
    _ ≤ _ := by
      apply iSup_le
      intro d
      cases d
      · simpa [v] using (le_sup_left : limitEmbed S i a ≤ limitEmbed S i a ⊔ limitEmbed S i aᶜ)
      · simpa [v] using (le_sup_right : limitEmbed S i aᶜ ≤ limitEmbed S i a ⊔ limitEmbed S i aᶜ)

theorem limitEmbed_inf (i : I) (a b : S.algebra i) :
    limitEmbed S i (a ⊓ b) = limitEmbed S i a ⊓ limitEmbed S i b := by
  apply le_antisymm
  · exact le_inf (limitEmbed_mono S i inf_le_left) (limitEmbed_mono S i inf_le_right)
  · by_contra hn
    have hd : (limitEmbed S i a ⊓ limitEmbed S i b) ⊓ (limitEmbed S i (a⊓b))ᶜ ≠ ⊥ := fun he =>
      hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hd
    let k := max p.stage i
    have hpK : p.stage ≤ k := le_max_left _ _
    have hiK : i ≤ k := le_max_right _ _
    have ha := (image_le_limitEmbed_iff S i a p hpK hiK).mp (hp.trans (inf_le_left.trans inf_le_left))
    have hb := (image_le_limitEmbed_iff S i b p hpK hiK).mp (hp.trans (inf_le_left.trans inf_le_right))
    have hAB : imageCondition p ≤ limitEmbed S i (a⊓b) := by
      apply image_le_limitEmbed S i (a⊓b) p hpK hiK
      rw [hS.inf]
      exact le_inf ha hb
    exact imageCondition_ne_bot_r50 p (disjoint_compl_right.out _ hAB (hp.trans inf_le_right))

theorem limitEmbed_comp {i j : I} (hij : i ≤ j) (a : S.algebra i) :
    limitEmbed S j (S.transition hij a) = limitEmbed S i a := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply image_le_limitEmbed S i a (Condition.atStage j t.val t.property.1) (k := j) le_rfl hij
    change S.transition (show j ≤ j from le_rfl) t.val ≤ _
    rw [S.identity]
    exact t.property.2
  · apply iSup_le
    intro t
    apply image_le_limitEmbed S j (S.transition hij a) (Condition.atStage i t.val t.property.1)
      (k := j) hij le_rfl
    change S.transition hij t.val ≤ S.transition (show j ≤ j from le_rfl) _
    rw [S.identity]
    exact transition_mono hS hij t.property.2

noncomputable def limitNameCoefficients [Nonempty I] (i : I) :
    NameCoefficients (S.algebra i) (LimitBA S) where
  map := limitEmbed S i
  map_top := limitEmbed_top S i
  map_inf := limitEmbed_inf S i
  map_compl := limitEmbed_compl S i
  map_iSup := limitEmbed_joins S i

noncomputable def limitCompleteValueMap [Nonempty I] (i : I) :
    CompleteValueMap (S.algebra i) (LimitBA S) where
  toFun := limitEmbed S i
  injective := fun _ _ h => le_antisymm
    ((limitEmbed_reflects S i).mp h.le) ((limitEmbed_reflects S i).mp h.ge)
  monotone := limitEmbed_mono S i
  map_bot := limitEmbed_bot S i
  map_top := limitEmbed_top S i
  map_compl := limitEmbed_compl S i
  map_inf := limitEmbed_inf S i
  map_iSup := limitEmbed_joins S i
  map_iInf := (limitNameCoefficients S i).map_iInf

end CompleteDiagram
end JSP000933
