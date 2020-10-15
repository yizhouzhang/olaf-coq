Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.Adequacy.
Require Import UFO.Rel.Compatability.
Require Import UFO.Rel.Parametricity.
Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Lang.Static.
Require Import UFO.Lang.StaticFacts.
Require Import UFO.Lang.Xs.
Require Import UFO.Lang.SigFacts.
Require Import UFO.Lang.Context.
Require Import FunctionalExtensionality.

Implicit Types EV LV V L : Set.

Section section_congruence.

Hint Resolve ok_wf_lbl ok_wf_ty ok_wf_eff ok_wf_tm.
Hint Resolve XLEnv_inv_wf_XEnv.
Hint Resolve EV_map_XLEnv LV_map_XLEnv.
Hint Unfold compose.

Fixpoint
congruence_tm n EV LV V L (t₁ t₂ : tm EV LV V L)
(Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
(T : ty ∅ EV LV L) (E : eff ∅ EV LV L) (T0 : ty0)
C (OK_C : ok_ctx C Γ Π T E T0) {struct OK_C} :
n ⊨ 【 Π Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # E 】 →
n ⊨ 【 LEnv_empty ∅→ ⊢ (ctx_plug C t₁) ≼ˡᵒᵍ (ctx_plug C t₂) : T0 # [] 】
with
congruence_md n EV LV V L (m₁ m₂ : md EV LV V L)
(Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
(β : L) (σ : ms ∅ EV LV L) (T0 : ty0)
D (OK_D : ok_dtx D Γ Π β σ T0) {struct OK_D} :
n ⊨ 【 Π Γ ⊢ m₁ ≼ˡᵒᵍₘ m₂ : σ ^ (lbl_id (lid_b β)) 】 →
n ⊨ 【 LEnv_empty ∅→ ⊢ (dtx_plug D m₁) ≼ˡᵒᵍ (dtx_plug D m₂) : T0 # [] 】
.
Proof.
{
intro H.
destruct OK_C as [ | ???? D ???????? OK_D | ???? C | ???? C ?? T E | ???? C |
  ???? C t ??????? OK_t | ???? C s ??????? OK_s | ???? C s ???????? OK_s |
  ???? C t ???????? OK_t | ???? C E₁ | ???? C ℓ₁ |
  ???? C s ???????? OK_s | ???? C t ???????? OK_t | ???? C
] ; (simpl ctx_plug || simpl dtx_plug).
+ apply H ; rewrite empty_def ; try rewrite keys_def ;
    try rewrite map_nil ; simpl ; shelve.
+ eapply congruence_md ; [exact OK_D|].
  iintro Ξ ; iintro f ; iintro HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl ; destruct (f β) as [|X] eqn:EQ_fβ ; [auto|].
  eapply compat_md_res ; [ eauto using LEnv_lookup_inv_binds | ].
  match goal with
  | [ H : ?n ⊨ ⟦ _ ?Γ ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ |- ?n ⊨ ⟦ _ ?Γ' ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  extensionality x ; crush.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ.
  iespecialize H ; ispecialize H ; [exact HΞΠ|].
  simpl L_bind_ty ; simpl L_bind_tm.
  rewrite L_bind_it_msig.
  apply compat_tm_op.
  apply H.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ.
  iespecialize H ; ispecialize H ; [exact HΞΠ|].
  simpl ; rewrite <- L_bind_eff_app.
  apply compat_tm_up ; exact H.
+ eapply congruence_tm ; try exact OK_C.
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ ; simpl.
  eapply compat_tm_down ; [intro;eauto|eauto|eauto|eauto|].
  intros X FrX.
  ispecialize H (Ξ & X ~ (L_bind_ty f T, L_bind_eff f E)).
  ispecialize H (env_ext f (lid_f X)).
  ispecialize H.
  { iintro_prop ; constructor ; eauto. }
  simpl in H.
  unshelve erewrite L_bind_map_ty, L_map_ty_id in H ; [eauto|eauto| |eauto|].
  unshelve erewrite L_bind_map_eff, L_map_eff_id in H ; [eauto|eauto| |eauto|].
  repeat erewrite L_bind_bind_tm with (g := env_ext f (lid_f X)).
  match goal with
  | [ H : ?n ⊨ ⟦ _ ?Γ ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ |- ?n ⊨ ⟦ _ ?Γ' ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  { extensionality x ; unfold compose.
    unshelve erewrite L_bind_map_ty, L_map_ty_id ; eauto.
    intro ; erewrite L_map_lid_id ; eauto.
  }
  { intro α ; destruct α ; simpl ; [auto|].
    unshelve erewrite L_bind_map_lid, L_map_lid_id, L_bind_lid_id ; auto.
  }
  { intro α ; destruct α ; simpl ; [auto|].
    unshelve erewrite L_bind_map_lid, L_map_lid_id, L_bind_lid_id ; auto.
  }
  { intro ; erewrite L_map_lid_id ; auto. }
  { intro ; erewrite L_map_lid_id ; auto. }
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl ; eapply compat_tm_let ; [|exact H].
  apply SI_LN_parametricity_tm ; [ eauto | intro ; eauto | ].
  eapply ok_wf_tm in OK_t ; [|eauto].
  match goal with
  | [ H : wf_tm ?Ξ ?Γ ?t ?T ?E |- wf_tm ?Ξ ?Γ' ?t ?T ?E ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  extensionality x ; crush.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl ; apply compat_tm_let with (S := L_bind_ty f S).
  { match goal with
    | [ H : ?n ⊨ ⟦ _ ?Γ ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ |- ?n ⊨ ⟦ _ ?Γ' ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ ] =>
      replace Γ' with Γ ; [ exact H | ]
    end.
    extensionality x ; crush.
  }
  apply SI_LN_parametricity_tm ; [ eauto | intro ; eauto | eauto ].
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-* ; eapply compat_tm_throw ; [exact H|].
  apply SI_LN_parametricity_tm ; [ eauto | intro ; eauto | eauto ].
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-* ; eapply compat_tm_throw ; [|exact H].
  apply SI_LN_parametricity_tm ; [ eauto | intro ; eauto | ].
  eapply ok_wf_tm in OK_t ; eauto.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-*.
  erewrite <- EV_L_bind_ms ; [ eapply compat_tm_app_eff ; exact H | auto ].
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-*.
  erewrite <- LV_L_bind_ms ; [ eapply compat_tm_app_lbl ; eauto | auto ].
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-*.
  eapply compat_tm_app_tm ; [exact H|].
  eapply SI_LN_parametricity_tm ; [eauto|intro ; eauto|eauto].
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-*.
  eapply compat_tm_app_tm ; [|exact H].
  eapply SI_LN_parametricity_tm ; [eauto|intro ; eauto|].
  eapply ok_wf_tm in OK_t ; eauto.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  eapply compat_sub with (E := L_bind_eff f E1) ; eauto using subty_st, L_bind_se.
}
{
intro H.
destruct OK_D as [ ???? C ????? OK_C | ???? D ????? OK_D |
  ???? D ????? OK_D | ???? D ?????? OK_D ] ; (simpl ctx_plug || simpl dtx_plug).
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-*.
  apply compat_tm_val.
  destruct (f β) as [α|X] eqn:EQ_fβ ; simpl in H|-* ; [destruct α|].
  apply compat_val_md ; apply H.
+ eapply congruence_md ; [exact OK_D|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-*.
  apply compat_md_ev.
  match goal with
  | [ H : ?n ⊨ ⟦ _ ?Γ ⊢ _ ≼ˡᵒᵍₘ _ : _ ^ _ ⟧ |- ?n ⊨ ⟦ _ ?Γ' ⊢ _ ≼ˡᵒᵍₘ _ : _ ^ _ ⟧ ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  extensionality x ; auto using L_bind_EV_map_ty.
+ eapply congruence_md ; [exact OK_D|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-*.
  apply compat_md_lv.
  match goal with
  | [ H : ?n ⊨ ⟦ _ ?Γ ⊢ _ ≼ˡᵒᵍₘ _ : _ ^ _ ⟧ |- ?n ⊨ ⟦ _ ?Γ' ⊢ _ ≼ˡᵒᵍₘ _ : _ ^ _ ⟧ ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  extensionality x ; auto using L_bind_LV_map_ty.
+ eapply congruence_md ; [exact OK_D|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-*.
  apply compat_md_tm.
  match goal with
  | [ H : ?n ⊨ ⟦ _ ?Γ ⊢ _ ≼ˡᵒᵍₘ _ : _ ^ _ ⟧ |- ?n ⊨ ⟦ _ ?Γ' ⊢ _ ≼ˡᵒᵍₘ _ : _ ^ _ ⟧ ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  extensionality x ; auto.
}
Qed.

End section_congruence.

Section section_soundness.

Hint Rewrite dom_empty union_empty_l Xs_ctx_plug.

Theorem soundness EV LV V L (t₁ t₂ : tm EV LV V L) (Closed_t₁ : Xs_tm t₁ = \{})
(Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
(T : ty ∅ EV LV L) (E : eff ∅ EV LV L) :
⊨ 【 Π Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # E 】 →
【 Π Γ ⊢ t₁ ≼ᶜᵗˣ t₂ : T # E 】.
Proof.
intro Ht.
intros C T0 OK_C Closed_C.
eapply adequacy ; [ | crush ].
intro n.
eapply congruence_tm with (n := n) in Ht as HCt ; [|exact OK_C].
iespecialize HCt.
ispecialize HCt ; [ iintro_prop ; constructor | ].
erewrite L_bind_tm_id, L_bind_tm_id, L_bind_ty_id, L_bind_eff_id in HCt ;
  [|auto|auto|auto|auto].
replace (L_bind_ty ∅→ ∘ ∅→) with (∅→ : ∅ → ty0) in HCt ; [|extensionality x ; auto].
exact HCt.
Qed.

Fact unfold_log_eq_I_valid EV LV V L (t₁ t₂ : tm EV LV V L)
(Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
(T : ty ∅ EV LV L) (E : eff ∅ EV LV L) :
(⊨ 【 Π Γ ⊢ t₁ ≈ˡᵒᵍ t₂ : T # E 】) →
(⊨ 【 Π Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # E 】) ∧ (⊨ 【 Π Γ ⊢ t₂ ≼ˡᵒᵍ t₁ : T # E 】).
Proof.
intro H ; split ; intro n ; specialize (H n) ; idestruct H as H1 H2 ; assumption.
Qed.

Theorem soundness_eq EV LV V L (t₁ t₂ : tm EV LV V L)
(Closed_t₁ : Xs_tm t₁ = \{}) (Closed_t₂ : Xs_tm t₂ = \{})
(Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
(T : ty ∅ EV LV L) (E : eff ∅ EV LV L) :
⊨ 【 Π Γ ⊢ t₁ ≈ˡᵒᵍ t₂ : T # E 】 →
【 Π Γ ⊢ t₁ ≈ᶜᵗˣ t₂ : T # E 】.
Proof.
intro H.
apply unfold_log_eq_I_valid in H ; destruct H as [H1 H2].
split ; apply soundness ; assumption.
Qed.

End section_soundness.
