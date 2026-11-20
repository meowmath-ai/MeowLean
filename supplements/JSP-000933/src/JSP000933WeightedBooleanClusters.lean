import JSP000933SaturatedDomainBridge

namespace JSP000933
namespace CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B]

structure BooleanSample (B : Type) (n : ℕ) where
  stem : Fin n → ℕ → B
  tip : ℕ → B
  weight : B

noncomputable def matchedValue (K : Word × Word → B) {n : ℕ}
    (p q : Fin n → ℕ → B) : B :=
  ⨅ i, colorValue K (p i) (q i)

noncomputable def stemCylinder {n : ℕ} (p : Fin n → ℕ → B) (U : Fin n → Word) : B :=
  ⨅ i, cylinderValue (p i) (U i)

noncomputable def weightedClusterHit (K : Word × Word → B) {n : ℕ}
    (S : I → BooleanSample B n) (p : Fin n → ℕ → B) (U : Fin n → Word) (V : Word) : B :=
  ⨆ i, ((S i).weight ⊓ matchedValue K p (S i).stem) ⊓
    (stemCylinder (S i).stem U ⊓ cylinderValue (S i).tip V)

noncomputable def weightedCluster (K : Word × Word → B) {n : ℕ}
    (S : I → BooleanSample B n) (p : Fin n → ℕ → B) (x : ℕ → B) : B :=
  ⨅ U : Fin n → Word, ⨅ V : Word,
    (stemCylinder p U ⊓ cylinderValue x V)ᶜ ⊔ weightedClusterHit K S p U V

theorem weightedCluster_given_boxes_r143 (K : Word × Word → B) {n : ℕ}
    (S : I → BooleanSample B n) (p : Fin n → ℕ → B) (x : ℕ → B)
    (U : Fin n → Word) (V : Word) {q : B}
    (hC : q ≤ weightedCluster K S p x)
    (hStem : q ≤ stemCylinder p U) (hTip : q ≤ cylinderValue x V) :
    q ≤ weightedClusterHit K S p U V := by
  have h := hC.trans ((iInf_le _ U).trans (iInf_le _ V))
  exact (le_inf le_rfl (le_inf hStem hTip)).trans ((le_materialImp_iff_r126 _ _ _).mp h)

theorem cylinder_empty_r143 (x : ℕ → B) : cylinderValue x [] = ⊤ := by
  apply top_unique
  apply le_iInf
  exact fun i : Fin 0 => Fin.elim0 i

theorem stemCylinder_empty_r143 {n : ℕ} (p : Fin n → ℕ → B) :
    stemCylinder p (fun _ => []) = ⊤ := by
  apply top_unique
  apply le_iInf
  intro i
  rw [cylinder_empty_r143] <;> exact le_rfl

theorem weightedCluster_compl_r143 (K : Word × Word → B) {n : ℕ}
    (S : I → BooleanSample B n) (p : Fin n → ℕ → B) (x : ℕ → B) :
    (weightedCluster K S p x)ᶜ =
      ⨆ U : Fin n → Word, ⨆ V : Word,
        (stemCylinder p U ⊓ cylinderValue x V) ⊓ (weightedClusterHit K S p U V)ᶜ := by
  simp only [weightedCluster,compl_iInf,compl_sup,compl_compl]

theorem hitsWord_saturatedDomain_r143 (x : I → ℕ → B) (d : I → B) (w : Word) :
    hitsWord (saturatedDomain x d) w = ⨆ i, d i ⊓ cylinderValue (x i) w := by
  apply le_antisymm
  · apply iSup_le
    intro y
    unfold saturatedDomain
    rw [iSup_inf_eq]
    apply iSup_le
    intro i
    let p := (d i ⊓ realEqValue y (x i)) ⊓ cylinderValue y w
    have he : p ≤ realEqValue y (x i) := inf_le_left.trans inf_le_right
    have hh := mask_cylinder_congr_r127 he w
    have hp : p ≤ cylinderValue (x i) w :=
      (le_inf le_rfl inf_le_right).trans (hh.le.trans inf_le_right)
    exact le_iSup_of_le i (le_inf (inf_le_left.trans inf_le_left) hp)
  · apply iSup_le
    intro i
    exact le_iSup_of_le (x i) (inf_le_inf_right _ (le_saturatedDomain_at_index_r142 x d i))

end CantorCodes
end JSP000933
