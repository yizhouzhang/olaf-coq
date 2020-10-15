Require Import Rel.Definitions.
Require Import Rel.BasicFacts.
Require Import Rel.Monotone.
Require Import Util.Postfix.
Require Import Lang.BindingsFacts.
Set Implicit Arguments.

Ltac bind_let :=
  match goal with
  | [ |- ?n ⊨ 𝓣⟦ ?Ξ ⊢ ?T # ?E ⟧ _ _ _ _ _ _ _ _
              (tm_let ?t₁ ?s₁) (tm_let ?t₂ ?s₂) ] =>
    replace (tm_let t₁ s₁)
    with (ktx_plug (ktx_let ktx_hole s₁) t₁) by reflexivity ;
    replace (tm_let t₂ s₂)
    with (ktx_plug (ktx_let ktx_hole s₂) t₂) by reflexivity
  end.

Section section_ccompat_tm_app_let.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (S T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅).

Lemma ccompat_tm_let n ξ₁ ξ₂ s₁ s₂ t₁ t₂ :
  n ⊨ 𝓣⟦ Ξ ⊢ S # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ → (
  n ⊨ ∀ᵢ ξ₁' ξ₂' (_ : postfix ξ₁ ξ₁') (_ : postfix ξ₂ ξ₂'),
      ∀ᵢ v₁ v₂,
      𝓥⟦ Ξ ⊢ S ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' v₁ v₂ ⇒
      𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' (V_subst_tm v₁ t₁) (V_subst_tm v₂ t₂)
  ) →
  n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ (tm_let s₁ t₁) (tm_let s₂ t₂).
Proof.
intros Hs Ht.
bind_let.
eapply plug0 with (ξ₁ := ξ₁) (ξ₂ := ξ₂) ;
  [crush|crush| |apply postfix_refl|apply postfix_refl|exact Hs].
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro v₁ ; iintro v₂ ; iintro Hv.
simpl ktx_plug.
eapply 𝓣_step_r ; [ apply step_let | ].
eapply 𝓣_step_l ; [ apply step_let | ].
iintro_later.

ielim_vars Ht ; [ | eassumption | eassumption ].
iespecialize Ht ; ispecialize Ht ; [ eassumption | ].
apply Ht.
Qed.

End section_ccompat_tm_app_let.

Section section_compat_tm_let.

Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (S T : ty ∅ EV LV ∅).
Context (E : eff ∅ EV LV ∅).

Hint Resolve postfix_trans postfix_refl.

Lemma compat_ktx_let n T' E' K₁ K₂ t₁ t₂ :
  n ⊨ ⟦ Ξ Γ ⊢ K₁ ≼ˡᵒᵍ K₂ : T' # E' ⇢ S # E ⟧ →
  n ⊨ ⟦ Ξ (env_ext Γ S) ⊢ t₁ ≼ˡᵒᵍ t₂ : T # E ⟧ →
  n ⊨ ⟦ Ξ Γ ⊢ (ktx_let K₁ t₁) ≼ˡᵒᵍ (ktx_let K₂ t₂) : T' # E' ⇢ T # E ⟧.
Proof.
intros HK Ht.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
iintro r₁ ; iintro r₂ ; iintro Hr.

iespecialize HK.
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ielim_vars HK ; [ | eassumption | eassumption ].
iespecialize HK ; ispecialize HK ; [ apply Hr | ].

simpl ktx_plug.
eapply ccompat_tm_let ; [ apply HK | ].
iintro ξ₁'' ; iintro ξ₂'' ; iintro Hξ₁'' ; iintro Hξ₂'' ;
iintro v₁ ; iintro v₂ ; iintro Hv.
ispecialize Ht ξ₁'' ; ispecialize Ht ξ₂'' ;
ispecialize Ht δ₁ ; ispecialize Ht δ₂ ; ispecialize Ht δ ;
ispecialize Ht ρ₁ ; ispecialize Ht ρ₂ ; ispecialize Ht ρ.
ispecialize Ht (env_ext γ₁ v₁) ; ispecialize Ht (env_ext γ₂ v₂).
iespecialize Ht.
ispecialize Ht.
{ iintro_prop ; eapply 𝜩_monotone ; eauto. }
ispecialize Ht.
{ eapply δ_is_closed_monotone ; eauto. }
ispecialize Ht.
{ iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto. }
ispecialize Ht.
{ iintro x ; destruct x ; simpl ; [ assumption | ].
  iespecialize Hγ ; eapply 𝓥_monotone ; [ | | apply Hγ ] ; eauto.
}
repeat erewrite V_bind_bind_tm ; try apply Ht.
{ intro x ; destruct x ; simpl ; [ reflexivity | ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
}
{ intro x ; destruct x ; simpl ; [ reflexivity | ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
}
Qed.

Lemma compat_tm_let n t₁ t₂ s₁ s₂ :
n ⊨ ⟦ Ξ (env_ext Γ S) ⊢ t₁ ≼ˡᵒᵍ t₂ : T # E ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ s₁ ≼ˡᵒᵍ s₂ : S # E ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (tm_let s₁ t₁) ≼ˡᵒᵍ (tm_let s₂ t₂) : T # E ⟧.
Proof.
intros Ht Hs.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.

iespecialize Hs.
ispecialize Hs ; [ eassumption | ].
ispecialize Hs ; [ eassumption | ].
ispecialize Hs ; [ eassumption | ].
ispecialize Hs ; [ eassumption | ].
simpl subst_tm.
eapply ccompat_tm_let ; [ apply Hs | ].

iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro v₁ ; iintro v₂ ; iintro Hv.
ispecialize Ht ξ₁' ; ispecialize Ht ξ₂' ;
ispecialize Ht δ₁ ; ispecialize Ht δ₂ ; ispecialize Ht δ ;
ispecialize Ht ρ₁ ; ispecialize Ht ρ₂ ; ispecialize Ht ρ.
ispecialize Ht (env_ext γ₁ v₁) ; ispecialize Ht (env_ext γ₂ v₂).
iespecialize Ht.
ispecialize Ht.
{ iintro_prop ; eapply 𝜩_monotone ; eauto. }
ispecialize Ht.
{ eapply δ_is_closed_monotone ; eauto. }
ispecialize Ht.
{ iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto. }
ispecialize Ht.
{ iintro x ; destruct x ; simpl ; [ assumption | ].
  iespecialize Hγ ; eapply 𝓥_monotone ; [ | | apply Hγ ] ; eauto.
}
repeat erewrite V_bind_bind_tm ; try apply Ht.
{ intro x ; destruct x ; simpl ; [ reflexivity | ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
}
{ intro x ; destruct x ; simpl ; [ reflexivity | ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
}

Qed.

End section_compat_tm_let.
