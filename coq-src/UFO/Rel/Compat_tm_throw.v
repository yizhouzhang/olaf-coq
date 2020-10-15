Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.BasicFacts.
Require Import UFO.Rel.Monotone.
Require Import UFO.Util.Postfix.
Set Implicit Arguments.

Section section_ccompat_tm_throw.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (Ta Tb : ty ∅ EV LV ∅) (Ea Eb : eff ∅ EV LV ∅).
Context (ξ₁ ξ₂ : list var).
Context (t₁ t₂ s₁ s₂ : tm0).

Lemma ccompat_tm_throw n :
  n ⊨ 𝓣⟦ Ξ ⊢ (ty_cont Ta Ea Tb Eb) # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ →
  n ⊨ ( ∀ᵢ ξ₁' ξ₂' (_ : postfix ξ₁ ξ₁') (_ : postfix ξ₂ ξ₂'),
        𝓣⟦ Ξ ⊢ Ta # Ea ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' s₁ s₂
      ) →
  n ⊨ 𝓣⟦ Ξ ⊢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ (tm_throw t₁ s₁) (tm_throw t₂ s₂).
Proof.
intros Ht Hs.
change (tm_throw t₁ s₁) with (ktx_plug (ktx_throw ktx_hole s₁) t₁).
change (tm_throw t₂ s₂) with (ktx_plug (ktx_throw ktx_hole s₂) t₂).
eapply plug0 ; try apply Ht ; clear Ht ; try apply postfix_refl.
+ crush.
+ crush.
+ iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
  iintro v₁ ; iintro v₂ ; iintro Hv ;
  destruct v₁ as [ | | K₁ | | ], v₂ as [ | | K₂ | | ] ; simpl in Hv ;
  idestruct Hv as m₁' Hv ; idestruct Hv as m₂' Hv ;
  idestruct Hv as Hv Hr ; ielim_prop Hv ; destruct Hv as [Hv₁ Hv₂] ;
  inversion Hv₁ ; inversion Hv₂ ; clear Hv₁ Hv₂ ; subst m₁' m₂'.

  simpl.
  eapply 𝓣_step_r ; [ apply step_throw | ].
  eapply 𝓣_step_l ; [ apply step_throw | ].
  iintro_later.
  ielim_vars Hr ; [ | apply postfix_refl | apply postfix_refl ].
  iespecialize Hr ; iapply Hr ; clear Hr.
  ielim_vars Hs ; [ | eassumption | eassumption ].
  apply Hs.
Qed.

End section_ccompat_tm_throw.


Section section_compat_tm_throw.
Context (n : nat).
Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (Ta Tb : ty ∅ EV LV ∅) (Ea Eb : eff ∅ EV LV ∅).

Hint Resolve postfix_trans.

Lemma compat_tm_throw t₁ t₂ s₁ s₂ :
  n ⊨ ⟦ Ξ Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : (ty_cont Ta Ea Tb Eb) # Eb ⟧ →
  n ⊨ ⟦ Ξ Γ ⊢ s₁ ≼ˡᵒᵍ s₂ : Ta # Ea ⟧ →
  n ⊨ ⟦ Ξ Γ ⊢ (tm_throw t₁ s₁) ≼ˡᵒᵍ (tm_throw t₂ s₂) : Tb # Eb ⟧.
Proof.
intros Ht Hs.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
simpl subst_tm.
eapply ccompat_tm_throw.
+ iespecialize Ht.
  ispecialize Ht ; [ eassumption | ].
  ispecialize Ht ; [ eassumption | ].
  ispecialize Ht ; [ eassumption | ].
  ispecialize Ht ; [ eassumption | ].
  apply Ht.
+ iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
  ispecialize Hs ξ₁' ; ispecialize Hs ξ₂' ; iespecialize Hs.
  ispecialize Hs.
  { ielim_prop Hξ ; iintro_prop ; eapply 𝜩_monotone ; eauto. }
  ispecialize Hs.
  { eapply δ_is_closed_monotone ; eassumption. }
  ispecialize Hs.
  { ielim_prop Hρ ; iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto. }
  ispecialize Hs.
  { eapply 𝜞_monotone ; eauto. }
  apply Hs.
Qed.

Lemma compat_ktx_throw T' E' K₁ K₂ s₁ s₂ :
  n ⊨ ⟦ Ξ Γ ⊢ K₁ ≼ˡᵒᵍ K₂ : T' # E' ⇢ (ty_cont Ta Ea Tb Eb) # Eb ⟧ →
  n ⊨ ⟦ Ξ Γ ⊢ s₁ ≼ˡᵒᵍ s₂ : Ta # Ea ⟧ →
  n ⊨ ⟦ Ξ Γ ⊢ (ktx_throw K₁ s₁) ≼ˡᵒᵍ (ktx_throw K₂ s₂) : T' # E' ⇢ Tb # Eb ⟧.
Proof.
intros HK Hs.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro t₁ ; iintro t₂ ; iintro Ht.
iespecialize HK.
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ielim_vars HK ; [ | eassumption | eassumption ].
iespecialize HK ; ispecialize HK ; [ apply Ht | ].

simpl ktx_plug.
eapply ccompat_tm_throw ; [ apply HK | ].
iintro ξ₁'' ; iintro ξ₂'' ; iintro Hξ₁'' ; iintro Hξ₂''.
ispecialize Hs ξ₁''; ispecialize Hs ξ₂'' ; iespecialize Hs.
ispecialize Hs.
{ ielim_prop Hξ ; iintro_prop ; eapply 𝜩_monotone ; eauto. }
ispecialize Hs.
{ eapply δ_is_closed_monotone ; eauto. }
ispecialize Hs.
{ ielim_prop Hρ ; iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto. }
ispecialize Hs.
{ eapply 𝜞_monotone ; eauto. }
apply Hs.
Qed.

End section_compat_tm_throw.
