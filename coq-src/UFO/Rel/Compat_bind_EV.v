Require Import Rel.Definitions.
Require Import Lang.BindingsFacts.
Require Import Lang.Sig.
Require Import Lang.SigFacts.
Require Import Wf_natnat.
Require Import Compat_sub.
Require Import Compat_map_EV.
Require Import Compat_map_LV.
Set Implicit Arguments.

Implicit Types EV LV V L : Set.

Section section_EV_bind_aux.

Hint Extern 0 => match goal with
| [ |- ?n ⊨ ?X ⇔ ?X ] => apply auto_contr_id
| [ |- ?n ⊨ ?X ≈ᵢ ?X ] => repeat iintro ; apply auto_contr_id
| [ |- Acc lt' (_, _) ] => try lt'_solve
| [ H : _ ⊨ (False)ᵢ |- _ ] => icontradict H
end.

Fixpoint
  EV_bind_𝓥_aux
  n EV EV' LV
  (Ξ : XEnv EV LV)
  (f : EV → eff ∅ EV' LV ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (Hδ₁ : ∀ α, δ₁ α = subst_eff δ₁' ρ₁ (f α))
  (Hδ₂ : ∀ α, δ₂ α = subst_eff δ₂' ρ₂ (f α))
  (Hδ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂,
        𝓾⟦ Ξ ⊢ ef_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
        𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
  )
  (ξ₁ ξ₂ : list var)
  (v₁ v₂ : val0) (T : ty ∅ EV LV ∅)
  (W : Acc lt' (n, size_ty T))
  {struct W} :
  (n ⊨
    𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (EV_bind_XEnv f Ξ) ⊢ EV_bind_ty f T ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂)
with
  EV_bind_𝓜_aux
  n EV EV' LV
  (Ξ : XEnv EV LV)
  (f : EV → eff ∅ EV' LV ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (Hδ₁ : ∀ α, δ₁ α = subst_eff δ₁' ρ₁ (f α))
  (Hδ₂ : ∀ α, δ₂ α = subst_eff δ₂' ρ₂ (f α))
  (Hδ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂,
        𝓾⟦ Ξ ⊢ ef_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
        𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
  )
  (ξ₁ ξ₂ : list var)
  (m₁ m₂ : md0) (σ : ms ∅ EV LV ∅) (ℓ : lbl LV ∅)
  (W : Acc lt' (n, size_ms σ))
  {struct W} :
  (n ⊨
    𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ ⇔
    𝓜⟦ (EV_bind_XEnv f Ξ) ⊢ (EV_bind_ms f σ) ^ ℓ ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂)
with
  EV_bind_𝓾_aux
  n EV EV' LV
  (Ξ : XEnv EV LV)
  (f : EV → eff ∅ EV' LV ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (Hδ₁ : ∀ α, δ₁ α = subst_eff δ₁' ρ₁ (f α))
  (Hδ₂ : ∀ α, δ₂ α = subst_eff δ₂' ρ₂ (f α))
  (Hδ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂,
        𝓾⟦ Ξ ⊢ ef_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
        𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
  )
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (ε : ef ∅ EV LV ∅)
  (W : Acc lt' (n, 0))
  {struct W} :
  (n ⊨
    𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ EV_bind_ef f ε ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)
with
  EV_bind_𝓤_aux
  n EV EV' LV
  (Ξ : XEnv EV LV)
  (f : EV → eff ∅ EV' LV ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (Hδ₁ : ∀ α, δ₁ α = subst_eff δ₁' ρ₁ (f α))
  (Hδ₂ : ∀ α, δ₂ α = subst_eff δ₂' ρ₂ (f α))
  (Hδ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂,
        𝓾⟦ Ξ ⊢ ef_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
        𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
  )
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (E : eff ∅ EV LV ∅)
  (W : Acc lt' (n, size_eff E))
  {struct W} :
  (n ⊨
    𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ EV_bind_eff f E ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)
with
  EV_bind_𝓣𝓵_aux
  n EV EV' LV
  (Ξ : XEnv EV LV)
  (f : EV → eff ∅ EV' LV ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (Hδ₁ : ∀ α, δ₁ α = subst_eff δ₁' ρ₁ (f α))
  (Hδ₂ : ∀ α, δ₂ α = subst_eff δ₂' ρ₂ (f α))
  (Hδ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂,
        𝓾⟦ Ξ ⊢ ef_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
        𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
  )
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ℓ : lbl LV ∅)
  (W : Acc lt' (n, size_lbl Ξ ℓ))
  {struct W} :
  (n ⊨
    𝓣𝓵⟦ Ξ ⊢ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
    𝓣𝓵⟦ (EV_bind_XEnv f Ξ) ⊢ ℓ ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂)
.

Proof.
{
destruct T as [ | Ta Ea Tb Eb | N ℓ | σ ℓ ] eqn:HT ; simpl 𝓥_Fun.
+ auto.
+ auto_contr.
  apply 𝓚_Fun_nonexpansive ; repeat iintro ;
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
+ auto_contr.
  apply 𝓥_roll_unroll_iff.
  match goal with
  | [ |- ?n ⊨ 𝓥⟦ _ ⊢ ?T ⟧ _ _ _ _ _ _ _ _ _ _ ⇔
              𝓥⟦ _ ⊢ ?T' ⟧ _ _ _ _ _ _ _ _ _ _ ] =>
    replace T' with (EV_bind_ty f T)
    by (simpl ; erewrite EV_bind_it_msig ; crush)
  end.
  apply EV_bind_𝓥_aux ; auto.
+ auto_contr.
  apply EV_bind_𝓜_aux ; auto.
}

{
destruct σ as [ τ | τ | τ | Ta Ea ] eqn:Hσ ; simpl 𝓜_Fun.
+ auto_contr.
  erewrite <- EV_bind_map_XEnv ; [ | ].
  apply EV_bind_𝓜_aux ; [ | | | auto ].
  - intro α ; destruct α ; simpl ; [ rewrite app_nil_r ; reflexivity | ].
    rewrite Hδ₁.
    erewrite LV_bind_EV_map_eff, EV_bind_map_eff, EV_map_eff_id ; try reflexivity.
    intro ; erewrite EV_map_eff_id ; reflexivity.
  - intro α ; destruct α ; simpl ; [ rewrite app_nil_r ; reflexivity | ].
    rewrite Hδ₂.
    erewrite LV_bind_EV_map_eff, EV_bind_map_eff, EV_map_eff_id ; try reflexivity.
    intro ; erewrite EV_map_eff_id ; reflexivity.
  - iintro α ; repeat iintro ; destruct α ; simpl.
    * isplit ; iintro' H ; [ ileft | idestruct H as H H ] ; auto.
    * iespecialize Hδ.
      eapply I_iff_transitive ; [ apply Hδ | ].
      replace (EV_bind_XEnv (EV_lift_inc f) (EV_shift_XEnv Ξ))
      with (EV_shift_XEnv (EV_bind_XEnv f Ξ))
      by (erewrite EV_bind_map_XEnv ; reflexivity).
      apply EV_map_𝓤 ; auto.
      repeat iintro ; simpl ; apply auto_contr_id.
  - reflexivity.
+ auto_contr.
  erewrite <- EV_bind_LV_map_XEnv ; [ | ].
  apply EV_bind_𝓜_aux ; [ | | | auto ].
  - intro ; rewrite Hδ₁.
    unfold compose.
    erewrite LV_bind_map_eff, EV_bind_LV_map_eff, LV_map_eff_id ; try reflexivity.
    * intro ; erewrite LV_map_eff_id ; reflexivity.
    * intro ; erewrite LV_map_lbl_id ; reflexivity.
  - intro ; rewrite Hδ₂.
    unfold compose.
    erewrite LV_bind_map_eff, EV_bind_LV_map_eff, LV_map_eff_id ; try reflexivity.
    * intro ; erewrite LV_map_eff_id ; reflexivity.
    * intro ; erewrite LV_map_lbl_id ; reflexivity.
  - iintro α ; repeat iintro.
    iespecialize Hδ ; unfold compose.
    eapply I_iff_transitive ; [ apply Hδ | ].
    clear.
    erewrite EV_bind_LV_map_XEnv ; [ | reflexivity ].
    apply LV_map_𝓤 ;
    try (simpl ; reflexivity) ;
    try (repeat iintro ; simpl ; apply auto_contr_id).
  - auto.
+ auto_contr.
  - apply EV_bind_𝓥_aux ; auto.
  - apply EV_bind_𝓜_aux ; auto.
+ rewrite EV_bind_XEnv_dom.
  auto_contr.
  apply 𝓗_Fun_nonexpansive ; repeat iintro.
  - apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ auto | ].
    auto_contr.
    * apply 𝓗_Fun_nonexpansive ; repeat iintro ; [ auto_contr | ].
      apply EV_bind_𝓣𝓵_aux ; auto.
    * apply EV_bind_𝓤_aux ; auto.
  - apply EV_bind_𝓣𝓵_aux ; auto. 
}

{
destruct ε as [ | α | [ α | [ α | X ] ] ] ; simpl.
+ auto.
+ iespecialize Hδ ; apply Hδ.
+ isplit ; iintro' H ; [ ileft ; apply H | ].
  idestruct H as H H ; [ apply H | auto ].
+ destruct α.
+ match goal with
  | [ |- n ⊨ ?P ⇔ ?Q ∨ᵢ (False)ᵢ ] =>
    cut (n ⊨ P ⇔ Q)
  end.
  { clear ; intro H.
    isplit ; iintro' H' ; [ ileft | idestruct H' as H' H' ; [ | auto ] ].
    + erewrite <- I_iff_elim_M ; eassumption.
    + erewrite I_iff_elim_M ; eassumption.
  }
  rewrite EV_bind_XEnv_dom.
  auto_contr.
  apply 𝓗_Fun_nonexpansive ; repeat iintro.
  - auto_contr.
  - destruct (get X Ξ) as [ [T E] | ] eqn:HX.
    * eapply binds_EV_bind in HX ; rewrite HX.
      apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
      { apply 𝓥_roll_unroll_iff ; auto. }
      { apply 𝓤_roll_unroll_iff ; auto. }
    * apply get_none_inv in HX.
      erewrite <- EV_bind_XEnv_dom in HX.
      apply get_none in HX.
      rewrite HX ; auto_contr.
}

{
destruct E as [ | ε E ] ; simpl ; [ auto | ].
isplit ; iintro' H.
+ idestruct H as H H.
  - eapply ccompat_se with (E := EV_bind_ef f ε).
    * crush.
    * erewrite <- I_iff_elim_M ; [ apply H | ].
      apply EV_bind_𝓾_aux ; auto.
  - apply ccompat_se with (E := EV_bind_eff f E).
    * crush.
    * erewrite <- I_iff_elim_M ; [ apply H | ].
      apply EV_bind_𝓤_aux ; auto.
+ apply ccompat_eff_In_inverse in H.
  destruct H as [ε' [Hε' H]].
  apply in_app_or in Hε'.
  destruct Hε' as [Hε' | Hε'] ; [ ileft | iright ].
  - eapply ccompat_eff_In in Hε' ; [ clear H | apply H ].
    erewrite I_iff_elim_M ; [ apply Hε' | ].
    apply EV_bind_𝓾_aux ; auto.
  - eapply ccompat_eff_In in Hε' ; [ clear H | apply H ].
    erewrite I_iff_elim_M ; [ apply Hε' | ].
    apply EV_bind_𝓤_aux ; auto.
}

{
destruct ℓ as [ α | [ | X ] ] ; simpl ; [ auto_contr | auto_contr | ].
destruct (get X Ξ) as [ [T E] | ] eqn:HX.
* simpl in W ; rewrite HX in W.
  eapply binds_EV_bind in HX as HX'; rewrite HX'.
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
  { apply 𝓥_roll_unroll_iff ; auto. }
  { apply 𝓤_roll_unroll_iff ; auto. }
* apply get_none_inv in HX.
  erewrite <- EV_bind_XEnv_dom in HX.
  apply get_none in HX.
  rewrite HX ; auto_contr.
}

Qed.

End section_EV_bind_aux.


Section section_EV_bind.
Context (n : nat).
Context (EV EV' LV : Set).
Context (Ξ : XEnv EV LV).
Context (f : EV → eff ∅ EV' LV ∅).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (Hδ₁ : ∀ α, δ₁ α = subst_eff δ₁' ρ₁ (f α)).
Context (Hδ₂ : ∀ α, δ₂ α = subst_eff δ₂' ρ₂ (f α)).
Context (Hδ :
  n ⊨ ∀ᵢ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂,
      𝓾⟦ Ξ ⊢ ef_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
      𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
).

Hint Resolve lt'_wf.

Lemma EV_bind_𝓥 T ξ₁ ξ₂ v₁ v₂ :
n ⊨
  𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
  𝓥⟦ (EV_bind_XEnv f Ξ) ⊢ EV_bind_ty f T ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂.
Proof.
apply EV_bind_𝓥_aux ; auto.
Qed.

Lemma EV_bind_𝓜 σ ℓ ξ₁ ξ₂ m₁ m₂ :
n ⊨
  𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ ⇔
  𝓜⟦ (EV_bind_XEnv f Ξ) ⊢ (EV_bind_ms f σ) ^ ℓ ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂.
Proof.
apply EV_bind_𝓜_aux ; auto.
Qed.

Lemma EV_bind_𝓤 E ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ :
n ⊨
  𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
  𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ EV_bind_eff f E ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂.
Proof.
apply EV_bind_𝓤_aux ; auto.
Qed.

Hint Resolve EV_bind_𝓥 EV_bind_𝓤.

Lemma EV_bind_𝓣 T E ξ₁ ξ₂ t₁ t₂ :
n ⊨
  𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
  𝓣⟦ (EV_bind_XEnv f Ξ) ⊢ (EV_bind_ty f T) # (EV_bind_eff f E) ⟧
  δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
Qed.

End section_EV_bind.
