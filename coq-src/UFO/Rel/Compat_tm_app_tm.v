Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.BasicFacts.
Require Import UFO.Rel.Monotone.
Require Import UFO.Util.Subset.
Require Import UFO.Util.Postfix.
Set Implicit Arguments.

Section section_ccompat_tm_app_tm.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (S : ty ∅ EV LV ∅) (σ : ms ∅ EV LV ∅) (ℓ : lbl LV ∅) (E : eff ∅ EV LV ∅).

Lemma ccompat_tm_app_tm2 n ξ₁ ξ₂ (v₁ v₂ : val0) (s₁ s₂ : tm0) :
  n ⊨ 𝓥⟦ Ξ ⊢ (ty_ms (ms_tm S σ) ℓ) ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ S # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ (ty_ms σ ℓ) # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ (tm_app_tm v₁ s₁) (tm_app_tm v₂ s₂).
Proof.
intros Hv Hs.
change (tm_app_tm (tm_val v₁) s₁)
with (ktx_plug (ktx_app_tm2 ktx_hole v₁) s₁).
change (tm_app_tm (tm_val v₂) s₂)
with (ktx_plug (ktx_app_tm2 ktx_hole v₂) s₂).
eapply plug0 ; try apply Hs ;
  [ crush | crush | | apply postfix_refl | apply postfix_refl ].

iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
iintro u₁ ; iintro u₂ ; iintro Hu.
simpl ktx_plug.

destruct v₁ as [ | | | m₁ [ | X₁ ] | m₁ [ | X₁ ] ], v₂ as [ | | | m₂ [ | X₂ ] | m₂ [ | X₂ ] ] ; simpl 𝓥_Fun in Hv ;
idestruct Hv as m₁' Hv ; idestruct Hv as m₂' Hv ;
idestruct Hv as X₁' Hv ; idestruct Hv as X₂' Hv ;
idestruct Hv as Hv Hr ; ielim_prop Hv ; destruct Hv as [Hv₁ Hv₂] ;
inversion Hv₁ ; inversion Hv₂ ; clear Hv₁ Hv₂ ; subst m₁' m₂' X₁' X₂'.

idestruct Hr as HX₁X₂ Hr ; idestruct Hr as m₁' Hr ; idestruct Hr as m₂' Hr ;
idestruct Hr as Hm Hr ; ielim_prop Hm ; destruct Hm ; subst m₁ m₂.
eapply 𝓣_step_r ; [ apply step_app_tm | ].
eapply 𝓣_step_l ; [ apply step_app_tm | ].
iintro_later.
apply 𝓥_in_𝓣.
simpl 𝓥_Fun.
repeat ieexists ; repeat isplit ; [ crush | assumption | ].

ielim_vars Hr ; [ | eassumption | eassumption ].
iespecialize Hr ; ispecialize Hr ; [ eassumption | ].
apply Hr.
Qed.

Lemma ccompat_tm_app_tm n ξ₁ ξ₂ (t₁ t₂ s₁ s₂ : tm0) :
  n ⊨ 𝓣⟦ Ξ ⊢ (ty_ms (ms_tm S σ) ℓ) # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ →
  n ⊨ ( ∀ᵢ ξ₁' ξ₂' (_ : postfix ξ₁ ξ₁') (_ : postfix ξ₂ ξ₂'),
        𝓣⟦ Ξ ⊢ S # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' s₁ s₂
      ) →
  n ⊨ 𝓣⟦ Ξ ⊢ (ty_ms σ ℓ) # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ (tm_app_tm t₁ s₁) (tm_app_tm t₂ s₂).
Proof.
intros Ht Hs.
change (tm_app_tm t₁ s₁)
with (ktx_plug (ktx_app_tm1 ktx_hole s₁) t₁).
change (tm_app_tm t₂ s₂)
with (ktx_plug (ktx_app_tm1 ktx_hole s₂) t₂).
eapply plug0 ; try apply Ht ;
  [ crush | crush | | apply postfix_refl | apply postfix_refl ].

iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
iintro v₁ ; iintro v₂ ; iintro Hv.
simpl ktx_plug.

ielim_vars Hs ; [ | eassumption | eassumption ].
apply ccompat_tm_app_tm2 ; eauto.
Qed.

End section_ccompat_tm_app_tm.


Section section_compat_tm_app_tm.

Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (S : ty ∅ EV LV ∅) (σ : ms ∅ EV LV ∅) (ℓ : lbl LV ∅) (E : eff ∅ EV LV ∅).

Lemma compat_tm_app_tm n t₁ t₂ s₁ s₂ :
n ⊨ ⟦ Ξ Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : (ty_ms (ms_tm S σ) ℓ) # E ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ s₁ ≼ˡᵒᵍ s₂ : S # E ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (tm_app_tm t₁ s₁) ≼ˡᵒᵍ (tm_app_tm t₂ s₂) : (ty_ms σ ℓ) # E ⟧.
Proof.
intros Ht Hs.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
simpl subst_tm.
eapply ccompat_tm_app_tm.
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

Lemma compat_ktx_app_tm1 n T' E' K₁ K₂ s₁ s₂ :
  n ⊨ ⟦ Ξ Γ ⊢ K₁ ≼ˡᵒᵍ K₂ : T' # E' ⇢ (ty_ms (ms_tm S σ) ℓ) # E ⟧ →
  n ⊨ ⟦ Ξ Γ ⊢ s₁ ≼ˡᵒᵍ s₂ : S # E ⟧ →
  n ⊨ ⟦ Ξ Γ ⊢ (ktx_app_tm1 K₁ s₁) ≼ˡᵒᵍ (ktx_app_tm1 K₂ s₂) : T' # E' ⇢ (ty_ms σ ℓ) # E ⟧.
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
eapply ccompat_tm_app_tm ; [ apply HK | ].
iintro ξ₁'' ; iintro ξ₂'' ; iintro Hξ₁'' ; iintro Hξ₂''.
ispecialize Hs ξ₁''; ispecialize Hs ξ₂'' ; iespecialize Hs.
ispecialize Hs.
{ ielim_prop Hξ ; iintro_prop ; eapply 𝜩_monotone ; eauto using postfix_trans. }
ispecialize Hs.
{ eapply δ_is_closed_monotone ; eauto using postfix_trans. }
ispecialize Hs.
{ ielim_prop Hρ ; iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto using postfix_trans. }
ispecialize Hs.
{ eapply 𝜞_monotone ; eauto using postfix_trans. }
apply Hs.
Qed.

Lemma compat_ktx_app_tm2 n T' E' K₁ K₂ v₁ v₂ :
  n ⊨ ⟦ Ξ Γ ⊢ K₁ ≼ˡᵒᵍ K₂ : T' # E' ⇢ S # E ⟧ →
  n ⊨ ⟦ Ξ Γ ⊢ v₁ ≼ˡᵒᵍᵥ v₂ : ty_ms (ms_tm S σ) ℓ ⟧ →
  n ⊨ ⟦ Ξ Γ ⊢ (ktx_app_tm2 K₁ v₁) ≼ˡᵒᵍ (ktx_app_tm2 K₂ v₂) : T' # E' ⇢ (ty_ms σ ℓ) # E ⟧.
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
eapply ccompat_tm_app_tm2 ; [ | apply HK ].
ispecialize Hs ξ₁'; ispecialize Hs ξ₂' ; iespecialize Hs.
ispecialize Hs.
{ ielim_prop Hξ ; iintro_prop ; eapply 𝜩_monotone ; eauto using subset_trans. }
ispecialize Hs.
{ eapply δ_is_closed_monotone ; eauto using subset_trans. }
ispecialize Hs.
{ ielim_prop Hρ ; iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto using subset_trans. }
ispecialize Hs.
{ eapply 𝜞_monotone ; eauto using subset_trans. }
apply Hs.
Qed.

End section_compat_tm_app_tm.
