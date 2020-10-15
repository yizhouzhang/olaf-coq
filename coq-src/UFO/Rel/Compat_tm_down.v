Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.BasicFacts.
Require Import UFO.Rel.Monotone.
Require Import UFO.Rel.Compat_weaken_X.
Require Import UFO.Util.Subset.
Require Import UFO.Util.Postfix.
Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Lang.Static.
Set Implicit Arguments.

Local Hint Rewrite in_singleton in_union in_inter dom_single.
Local Hint Resolve subset_union_r subset_empty_l.
Local Hint Resolve 𝓥_monotone 𝓗_monotone.
Local Hint Constructors wf_XEnv.
Local Hint Constructors postfix.

Local Fact fsetfact3 (A : Type) (E : fset A) a :
a ∉ E → disjoint E \{a}.
Proof.
intro H ; apply fset_extens ; [ intros_all ; crush | auto ].
Qed.

Local Hint Resolve fsetfact3.

Section section_ccompat_tm_down.
Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (X : var).
Context (T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅).

Lemma ccompat_tm_down_aux n
(FrX :
  n ⊨ ∀ᵢ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂,
      𝓤⟦ Ξ & (X ~ (T,E)) ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇒ (X ∉ L₁ ∧ X ∉ L₂)ᵢ
) :
n ⊨ ∀ᵢ ζ₁ ζ₂ ξ₁ ξ₂ t₁ t₂,
    𝓣⟦ Ξ & (X ~ (T,E)) ⊢ T # (ef_lbl (lbl_id (lid_f X))) :: E ⟧
      δ₁ δ₂ δ ρ₁ ρ₂ ρ
      (ζ₁ ++ X :: ξ₁) (ζ₂ ++ X :: ξ₂) t₁ t₂ ⇒
    𝓣⟦ Ξ & (X ~ (T,E)) ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      (ζ₁ ++ X :: ξ₁) (ζ₂ ++ X :: ξ₂)
      (ktx_plug (ktx_down ktx_hole X) t₁)
      (ktx_plug (ktx_down ktx_hole X) t₂).
Proof.
loeb_induction LöbIH.
iintro ζ₁ ; iintro ζ₂ ; iintro ξ₁ ; iintro ξ₂ ; iintro t₁ ; iintro t₂ ; iintro Ht.
apply plug1 with
  (ε := ef_lbl (lbl_id (lid_f X))) (Ta := T) (ξ₁ := ζ₁ ++ X :: ξ₁) (ξ₂ := ζ₂ ++ X :: ξ₂).
+ exact FrX.
+ iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
  iintro v₁ ; iintro v₂ ; iintro Hv.
  eapply 𝓣_step_r.
  { simpl ; apply step_down_val ; eauto. }
  eapply 𝓣_step_l.
  { simpl ; apply step_down_val ; eauto. }
  iintro_later.
  apply 𝓥_in_𝓣 ; apply Hv.
+ clear - LöbIH.
  iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
  iintro K₁ ; iintro K₂ ;
  iintro s₁ ; iintro s₂ ; iintro ψ ; iintro Xs₁ ; iintro Xs₂.
  iintro H.
  iintro Xs_K₁K₂.
  iintro Hw.
  ielim_prop Xs_K₁K₂.

  simpl in H.
  idestruct H as X₁ H ; idestruct H as X₂ H ;
  idestruct H as r₁ H ; idestruct H as r₂ H ;
  idestruct H as HX₁X₂ H ; idestruct H as HXs₁Xs₂ H ;
  idestruct H as Hs₁s₂ H ; idestruct H as HX Hr.

  ielim_prop HX₁X₂ ; destruct HX₁X₂ as [HX₁ HX₂].
  ielim_prop Hs₁s₂ ; destruct Hs₁s₂ as [Hs₁ Hs₂].
  ielim_prop HXs₁Xs₂ ; destruct HXs₁Xs₂ as [HXs₁ HXs₂].
  simpl in HX₁, HX₂ ; inversion HX₁ ; inversion HX₂ ; clear HX₁ HX₂.
  subst s₁ s₂ Xs₁ Xs₂ X₁ X₂.

  rewrite get_concat in Hr.
  rewrite binds_single_eq in Hr.

  simpl.
  specialize (Xs_K₁K₂ X).
  assert (tunnels X K₁) ; [ crush | ].
  assert (tunnels X K₂) ; [ crush | ].
  eapply 𝓣_step_r.
  { apply step_down_up ; eauto. }
  eapply 𝓣_step_l.
  { apply step_down_up ; eauto. }

  unfold 𝓗_Fun in Hr.
  apply I_later_forall_down in Hr ; iespecialize Hr.
  apply I_later_forall_down in Hr ; iespecialize Hr.
  apply I_later_forall_down in Hr ; eapply I_forall_elim in Hr ; [ | apply postfix_refl ].
  apply I_later_forall_down in Hr ; eapply I_forall_elim in Hr ; [ | apply postfix_refl ].
  repeat (apply I_later_forall_down in Hr ; iespecialize Hr).
  apply I_later_arrow_down in Hr.
  erewrite I_iff_elim_M ; [ |
      eapply I_later_iff_down ; iintro_later ; apply fold_𝓥𝓤_in_𝓣
  ].
  iapply Hr.

  clear - LöbIH Hw Hξ₁' Hξ₂'.
  apply I_later_forall_up ; iintro ξ₁''.
  apply I_later_forall_up ; iintro ξ₂''.
  apply I_later_forall_up ; iintro Hξ₁''.
  apply I_later_forall_up ; iintro Hξ₂''.
  apply I_later_forall_up ; iintro t₁.
  apply I_later_forall_up ; iintro t₂.
  apply I_later_arrow_up ; iintro Ht.
  ielim_vars Hw ; [ | apply Hξ₂'' | apply Hξ₁'' ].
  iespecialize Hw.
  ispecialize Hw ; [ apply Ht | ].

  later_shift.
  erewrite <- I_iff_elim_M ; [ | apply fold_𝓥𝓤_in_𝓣 ].

  simpl ktx_plug in LöbIH.
  apply postfix_inv_app in Hξ₁'' ; destruct Hξ₁'' as [ ζ₁'' Hξ₁'' ].
  apply postfix_inv_app in Hξ₂'' ; destruct Hξ₂'' as [ ζ₂'' Hξ₂'' ].
  apply postfix_inv_app in Hξ₁' ; destruct Hξ₁' as [ ζ₁' Hξ₁' ].
  apply postfix_inv_app in Hξ₂' ; destruct Hξ₂' as [ ζ₂' Hξ₂' ].
  ispecialize LöbIH (ζ₁'' ++ ζ₁' ++ ζ₁) ;
  ispecialize LöbIH (ζ₂'' ++ ζ₂' ++ ζ₂) ;
  ispecialize LöbIH ξ₁ ;
  ispecialize LöbIH ξ₂.
  repeat rewrite <- app_assoc in LöbIH.
  rewrite <- Hξ₁', <- Hξ₂', <- Hξ₁'', <- Hξ₂'' in LöbIH.
  iespecialize LöbIH.
  ispecialize LöbIH ; [ apply Hw | ].
  apply LöbIH.
+ apply postfix_refl.
+ apply postfix_refl.
+ assumption.
Qed.

Context (FrX_Ξ : X # Ξ).
Context (Wf_Ξ : wf_XEnv Ξ).
Context (Wf_T : wf_ty Ξ T).
Context (Wf_E : wf_eff Ξ E).

Lemma ccompat_tm_down n ξ₁ ξ₂ t₁ t₂ :
n ⊨ ( ∀ᵢ ξ₁' ξ₂' t₁' t₂' ψ Xs₁ Xs₂,
      𝓤⟦ (Ξ & X ~ (T, E)) ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁' t₂' ψ Xs₁ Xs₂ ⇒
      (X ∉ Xs₁ ∧ X ∉ Xs₂)ᵢ
    ) →
X ∉ from_list ξ₁ → X ∉ from_list ξ₂ →
n ⊨ 𝓣⟦ (Ξ & (X ~ (T, E))) ⊢ T # (ef_lbl (lbl_id (lid_f X))) :: E ⟧
    δ₁ δ₂ δ ρ₁ ρ₂ ρ
    (X :: ξ₁) (X :: ξ₂)
    (L_subst_tm (lid_f X) t₁) (L_subst_tm (lid_f X) t₂) →
n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ (⬇ t₁) (⬇ t₂).
Proof.
intros FrX_E FrX_ξ₁ FrX_ξ₂ Ht.
specialize (ccompat_tm_down_aux FrX_E) as H.
ispecialize H ([] : list var).
ispecialize H ([] : list var).
iespecialize H.
repeat rewrite app_nil_l in H.
simpl ktx_plug in H.

eapply 𝓣_step_r.
{ apply step_Down with (X := X) ; assumption. }
eapply 𝓣_step_l.
{ apply step_Down with (X := X) ; assumption. }

iintro_later.
iespecialize H ; ispecialize H ; [ apply Ht | ].
erewrite I_iff_elim_M ; [ apply H | apply X_weaken_𝓣 ] ; crush.
Qed.

End section_ccompat_tm_down.


Section section_compat_tm_down.
Context (n : nat).
Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (Wf_Γ : wf_Γ Ξ Γ).
Context (t₁ t₂ : tm EV LV V (inc ∅)).
Context (T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅).
Context (Wf_Ξ : wf_XEnv Ξ).
Context (Wf_T : wf_ty Ξ T).
Context (Wf_E : wf_eff Ξ E).

Lemma compat_tm_down (B : vars) :
( ∀ X, X \notin B →
  n ⊨ ⟦ (Ξ & (X ~ (T, E))) Γ ⊢
        (L_subst_tm (lid_f X) t₁) ≼ˡᵒᵍ (L_subst_tm (lid_f X) t₂) :
        T # (ef_lbl (lbl_id (lid_f X))) :: E ⟧
) →
n ⊨ ⟦ Ξ Γ ⊢ (⬇ t₁) ≼ˡᵒᵍ (⬇ t₂) : T # E ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
pick_fresh_gen (from_list ξ₁ \u from_list ξ₂ \u B) X.
assert (X ∉ B) as FrB ; [ crush | ].
specialize (Ht X FrB).
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hγ.
ielim_prop Hξ ; specialize Hξ as Hξ_copy ; destruct Hξ_copy as [Hξ₁ Hξ₂].
ielim_prop cl_ρ₁ρ₂.

assert (X ∉ from_list ξ₁) as Frξ₁ ; [ crush | ].
assert (X ∉ from_list ξ₂) as Frξ₂ ; [ crush | ].
assert (X ∉ dom Ξ) as FrΞ ; [ intro ; crush | ].

ispecialize Ht (X :: ξ₁) ; ispecialize Ht (X :: ξ₂).
ispecialize Ht δ₁ ; ispecialize Ht δ₂ ; ispecialize Ht δ.
ispecialize Ht ρ₁ ; ispecialize Ht ρ₂ ; ispecialize Ht ρ.
ispecialize Ht γ₁ ; ispecialize Ht γ₂.
ispecialize Ht.
{ iintro_prop ; split ; [ clear - Hξ₁ | clear - Hξ₂ ] ;
  rewrite dom_concat, from_list_cons, dom_single, union_comm ;
  apply subset_union_2 ; crush.
}
ispecialize Ht.
{ repeat iintro ; iespecialize cl_δ ; ispecialize cl_δ ; [ eassumption | ].
  repeat rewrite from_list_cons ; ielim_prop cl_δ ; crush.
}
ispecialize Ht.
{ iintro_prop ; intros α Y ; specialize (cl_ρ₁ρ₂ α Y) ;
  clear - cl_ρ₁ρ₂ ; repeat rewrite from_list_cons ; crush.
}
ispecialize Ht.
{ iintro x ; ispecialize Hγ x ; clear - Wf_Ξ Wf_Γ Wf_T Wf_E FrΞ Hγ.
  erewrite <- I_iff_elim_M ; [ | apply X_weaken_𝓥 ; crush ].
  eauto.
}

simpl.
apply ccompat_tm_down with (X := X) ; try assumption.
+ iintro ξ₁' ; iintro ξ₂' ;
  iintro s₁ ; iintro s₂ ; iintro ψ ; iintro Xs₁ ; iintro Xs₂ ; iintro Hs.
  erewrite <- I_iff_elim_M in Hs ; [ | apply X_weaken_𝓤 ; crush ].
  iintro_prop.
  assert (Xs₁ \c from_list ξ₁ ∧ Xs₂ \c from_list ξ₂) as HXs₁Xs₂.
  { eapply 𝓤_is_closed ; eassumption. }
  clear - HXs₁Xs₂ Frξ₁ Frξ₂.
  destruct HXs₁Xs₂.
  split ; intro ; auto.
+ clear - Ht.
  repeat erewrite <- V_L_bind_tm, <- EV_L_bind_tm, <- LV_L_bind_tm.
  { apply Ht. }
  { intro ; unfold compose.
    erewrite L_bind_map_lbl, L_bind_lbl_id, L_map_lbl_id ; crush. }
  { intro ; unfold compose.
    erewrite L_bind_map_eff, L_bind_eff_id, L_map_eff_id ; crush. }
  { intro ; unfold compose.
    erewrite L_bind_map_val, L_bind_val_id, L_map_val_id ; crush. }
  { intro ; unfold compose.
    erewrite L_bind_map_lbl, L_bind_lbl_id, L_map_lbl_id ; crush. }
  { intro ; unfold compose.
    erewrite L_bind_map_eff, L_bind_eff_id, L_map_eff_id ; crush. }
  { intro ; unfold compose.
    erewrite L_bind_map_val, L_bind_val_id, L_map_val_id ; crush. }
Qed.

End section_compat_tm_down.
