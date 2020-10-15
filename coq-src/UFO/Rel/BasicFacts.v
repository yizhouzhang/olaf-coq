Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Lang.OperationalFacts.
Require Import UFO.Rel.Monotone.
Require Import UFO.Rel.Definitions.
Require Import UFO.Util.Subset.
Require Import UFO.Util.Postfix.
Set Implicit Arguments.

(** * The small-step transition relation reflects [𝓞] (and [𝓣]) on both sides *)

Lemma 𝓞_step_l n ξ₁ t₁ ξ₁' t₁' ξ₂ t₂ :
  step ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩ → n ⊨ ▷ 𝓞 ξ₁' ξ₂ t₁' t₂ → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros.
  apply 𝓞_roll.
  iright.
  iexists ξ₁' ; iexists t₁' ; isplit.
  { iintro_prop ; assumption. }
  { assumption. }
Qed.

Local Lemma 𝓞_step_tran_l_aux c₁ c₁' :
  step_tran c₁ c₁' →
  ∀ ξ₁ t₁ ξ₁' t₁', c₁ = ⟨ξ₁, t₁⟩ → c₁' = ⟨ξ₁', t₁'⟩ →
  ∀ n ξ₂ t₂, n ⊨ ▷ 𝓞 ξ₁' ξ₂ t₁' t₂ → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  induction 1 as [ | ? [ξ₁'' t₁''] ? ? ? IH ] ; intros ; subst.
  + eapply 𝓞_step_l ; eauto.
  + eapply 𝓞_step_l ; eauto.
    iintro_later.
    eapply IH ; eauto.
Qed.

Lemma 𝓞_step_tran_l ξ₁ t₁ ξ₁' t₁' :
  step_tran ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩ → ∀ n ξ₂ t₂, n ⊨ ▷ 𝓞 ξ₁' ξ₂ t₁' t₂ → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros ; eapply 𝓞_step_tran_l_aux ; eauto.
Qed.

Local Lemma 𝓞_step_r_aux ξ₂ t₂ ξ₂' t₂' :
  step ⟨ξ₂, t₂⟩ ⟨ξ₂', t₂'⟩ → ∀ n, n ⊨ ∀ᵢ ξ₁ t₁, 𝓞 ξ₁ ξ₂' t₁ t₂' ⇒ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step n.
  loeb_induction LöbIH.
  iintro ξ₁ ; iintro t₁ ; iintro H.
  apply 𝓞_roll ; apply 𝓞_unroll in H.
  idestruct H as H H.
  - apply I_Prop_elim in H.
    destruct H as [ [v₁ ?] [ξ₂'' [v₂ ?]] ] ; subst.
    ileft.
    iintro_prop ; split.
    { eexists ; trivial. }
    { eexists ; eexists ; econstructor ; eauto. }
  - idestruct H as ξ₁' H ; idestruct H as t₁' H.
    idestruct H as H1 H2.
    iright.
    iexists ξ₁' ; iexists t₁'.
    isplit ; [ trivial | ].
    later_shift.
    iespecialize LöbIH ; iapply LöbIH.
    trivial.
Qed.

Lemma 𝓞_step_r n ξ₁ t₁ ξ₂ t₂ ξ₂' t₂' :
  step ⟨ξ₂, t₂⟩ ⟨ξ₂', t₂'⟩ → n ⊨ 𝓞 ξ₁ ξ₂' t₁ t₂' → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step H1.
  specialize (𝓞_step_r_aux H_step n) as H.
  iespecialize H.
  iapply H ; trivial.
Qed.

Local Lemma 𝓞_step_refl_tran_r_aux c₂ c₂' :
  step_refl_tran c₂ c₂' →
  ∀ ξ₂ t₂ ξ₂' t₂', c₂ = ⟨ξ₂, t₂⟩ → c₂' = ⟨ξ₂', t₂'⟩ →
  ∀ n ξ₁ t₁, n ⊨ 𝓞 ξ₁ ξ₂' t₁ t₂' → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  induction 1 as [ | ? [ξ₂'' t₂''] ? ? ? IH ] ; intros ; subst.
  + match goal with [ H : _ = _ |- _ ] => inversion H end.
    assumption.
  + eapply 𝓞_step_r ; eauto.
Qed.

Lemma 𝓞_step_refl_tran_r ξ₂ t₂ ξ₂' t₂' :
  step_refl_tran ⟨ξ₂, t₂⟩ ⟨ξ₂', t₂'⟩ →
  ∀ n ξ₁ t₁, n ⊨ 𝓞 ξ₁ ξ₂' t₁ t₂' → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros ; eapply 𝓞_step_refl_tran_r_aux ; eauto.
Qed.

Section section_𝓣_step.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅).

Hint Resolve 𝓡_monotone_l 𝓡_monotone_r.
Hint Resolve step_monotone_config step_tran_monotone_config
  step_refl_tran_monotone_config.

Lemma 𝓣_step_l ξ₁ ξ₁' ξ₂ (t₁ t₁' t₂ : tm0) n :
  step ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩ →
  n ⊨ ▷ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂ t₁' t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  eapply 𝓞_step_l.
  + apply ktx_congruence ; apply H_step.
  + later_shift.
    iespecialize H ; iapply H.
    eauto.
Qed.

Lemma 𝓣_step_tran_l ξ₁ ξ₁' ξ₂ (t₁ t₁' t₂ : tm0) n :
  step_tran ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩ →
  n ⊨ ▷ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂ t₁' t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  eapply 𝓞_step_tran_l.
  + apply ktx_tran_congruence ; apply H_step.
  + later_shift.
    iespecialize H ; iapply H.
    eauto.
Qed.

Lemma 𝓣_step_r ξ₁ ξ₂ ξ₂' (t₁ t₂ t₂' : tm0) n :
  step ⟨ξ₂, t₂⟩ ⟨ξ₂', t₂'⟩ →
  n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂' t₁ t₂' →
  n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  eapply 𝓞_step_r.
  + apply ktx_congruence ; apply H_step.
  + iespecialize H ; iapply H.
    eauto.
Qed.

Lemma 𝓣_step_refl_tran_r ξ₁ ξ₂ ξ₂' (t₁ t₂ t₂' : tm0) n :
  step_refl_tran ⟨ξ₂, t₂⟩ ⟨ξ₂', t₂'⟩ →
  n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂' t₁ t₂' →
  n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  eapply 𝓞_step_refl_tran_r.
  + apply ktx_refl_tran_congruence ; apply H_step.
  + iespecialize H ; iapply H.
    eauto.
Qed.

End section_𝓣_step.


(** * The [𝓥] and [𝓦] relations are smaller than [𝓣]. *)

Section section_𝓥_and_𝓦_are_in_𝓣.

Context (𝓥 : IRel 𝓥_Sig) (𝓤 : IRel 𝓤_Sig).
Context (n : nat).

Hint Resolve postfix_refl.

Lemma 𝓥_in_𝓣
ξ₁ ξ₂ v₁ v₂ :
n ⊨ 𝓥 ξ₁ ξ₂ v₁ v₂ →
n ⊨ 𝓣_Fun_Fix' 𝓥 𝓤 ξ₁ ξ₂ v₁ v₂.
Proof.
  intro H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  idestruct HK as HKV HKW.
  ielim_vars HKV ; [ | auto | auto ].
  iespecialize HKV.
  iapply HKV.
  apply H.
Qed.

Lemma 𝓦_in_𝓣
    ξ₁ ξ₂ J₁ J₂ t₁ t₂ :
    n ⊨ 𝓦_Fun_Fix' 𝓥 𝓤 ξ₁ ξ₂ J₁ J₂ t₁ t₂ →
    n ⊨ 𝓣_Fun_Fix' 𝓥 𝓤 ξ₁ ξ₂ (ktx_plug J₁ t₁) (ktx_plug J₂ t₂).
Proof.
  intro H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  idestruct HK as HKV HKW.
  ielim_vars HKW ; [ | auto | auto ].
  iespecialize HKW.
  iapply HKW.
  apply H.
Qed.

End section_𝓥_and_𝓦_are_in_𝓣.

Section section_plug'.

Context (𝓥a : IRel 𝓥_Sig).
Context (𝓤a : IRel 𝓤_Sig).
Context (𝓥b : IRel 𝓥_Sig).
Context (𝓤b : IRel 𝓤_Sig).

Hint Resolve postfix_trans.
Hint Resolve 𝓡_monotone.

Lemma plug'' (ξ₁ ξ₂ : list var) (K₁ K₂ : ktx0) n :
  n ⊨ 𝓚𝓥_Fun 𝓥a (𝓣_Fun_Fix' 𝓥b 𝓤b) ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓚𝓦_Fun 𝓥a 𝓤a (𝓣_Fun_Fix' 𝓥b 𝓤b) ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓚_Fun (𝓣_Fun_Fix' 𝓥a 𝓤a) (𝓣_Fun_Fix' 𝓥b 𝓤b) ξ₁ ξ₂ K₁ K₂.
Proof.
  intros HKv HKw.
  iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
  iintro t₁ ; iintro t₂ ; iintro Ht.
  iintro J₁ ; iintro J₂ ; iintro HJ.
  repeat rewrite ktx_plug_comp.
  iespecialize Ht ; iapply Ht ; clear Ht.
  isplit.
  * iintro ξ₁'' ; iintro ξ₂'' ; iintro Hξ₁'' ; iintro Hξ₂''.
    iintro v₁ ; iintro v₂ ; iintro Hv.
    repeat rewrite <- ktx_plug_comp.
    ielim_vars' HKv ξ₁'' ξ₂'' ; [ | eauto | eauto ].
    iespecialize HKv.
    ispecialize HKv ; [apply Hv|clear Hv].
    iespecialize HKv ; iapply HKv.
    eauto.
  * iintro ξ₁'' ; iintro ξ₂'' ; iintro Hξ₁'' ; iintro Hξ₂''.
    iintro L₁ ; iintro L₂ ; iintro s₁ ; iintro s₂ ; iintro Hw.
    repeat rewrite <- ktx_plug_comp.
    ielim_vars' HKw ξ₁'' ξ₂'' ; [ | eauto | eauto ].
    iespecialize HKw.
    ispecialize HKw ; [apply Hw|].
    iespecialize HKw ; iapply HKw.
    eauto.
Qed.

Lemma plug' ξ₁ ξ₂ K₁ K₂ n :
  n ⊨ 𝓚𝓥_Fun 𝓥a (𝓣_Fun_Fix' 𝓥b 𝓤b) ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓚𝓦_Fun 𝓥a 𝓤a (𝓣_Fun_Fix' 𝓥b 𝓤b) ξ₁ ξ₂ K₁ K₂ →
  ∀ ξ₁' ξ₂', postfix ξ₁ ξ₁' → postfix ξ₂ ξ₂' →
  ∀ t₁ t₂,
  n ⊨ 𝓣_Fun_Fix' 𝓥a 𝓤a ξ₁' ξ₂' t₁ t₂ →
  n ⊨ 𝓣_Fun_Fix' 𝓥b 𝓤b ξ₁' ξ₂' (ktx_plug K₁ t₁) (ktx_plug K₂ t₂).
Proof.
intros H𝓥 H𝓦 ; intros.
specialize (plug'' H𝓥 H𝓦) as HK.
ielim_vars HK ; [ | eauto | eauto ].
iespecialize HK ; iapply HK ; assumption.
Qed.

End section_plug'.

Section section_plug.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (Ta : ty ∅ EV LV ∅) (Ea : eff ∅ EV LV ∅).
Context (Tb : ty ∅ EV LV ∅) (Eb : eff ∅ EV LV ∅).
Context (ξ₁ ξ₂ : list var).
Context (K₁ K₂ : ktx0).
Context (n : nat).

Lemma plug t₁ t₂ :
  n ⊨ 𝓚𝓥⟦ Ξ ⊢ Ta ⇢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓚𝓦⟦ Ξ ⊢ Ta # Ea ⇢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  ∀ ξ₁' ξ₂', postfix ξ₁ ξ₁' → postfix ξ₂ ξ₂' →
  n ⊨ 𝓣⟦ Ξ ⊢ Ta # Ea ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' (ktx_plug K₁ t₁) (ktx_plug K₂ t₂).
Proof.
  intros.
  eapply unfold_𝓚 with (Ta := Ta) (Ea := Ea) ; eauto.
  apply plug'' ; auto.
Qed.

End section_plug.


Section section_plug0.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (Ta : ty ∅ EV LV ∅).
Context (Tb : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅).
Context (ξ₁ ξ₂ : list var).
Context (K₁ K₂ : ktx0).
Context (K₁_tun : ∀ ℓ, tunnels ℓ K₁).
Context (K₂_tun : ∀ ℓ, tunnels ℓ K₂).

Hint Resolve postfix_trans.

Lemma plug0' n :
  n ⊨ 𝓚𝓥⟦ Ξ ⊢ Ta ⇢ Tb # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓚⟦ Ξ ⊢ Ta # E ⇢ Tb # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂.
Proof.
intro HKv.
loeb_induction LöbIH.
eapply plug''.
+ apply HKv.
+ iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
  iintro L₁ ; iintro L₂ ; iintro s₁ ; iintro s₂ ; iintro Hw.
  apply unfold_𝓦 in Hw.
  destruct Hw as [ψ [Xs₁ [Xs₂ [Hs [HXs₁Xs₂ Hw]]]]].
  repeat rewrite ktx_plug_comp.
  apply 𝓦_in_𝓣.
  eapply fold_𝓦.
  - apply Hs.
  - intro X.
    specialize (HXs₁Xs₂ X) ; destruct HXs₁Xs₂.
    split ; intro HX ; apply tunnels_ktx_comp ; crush.
  - iintro ξ₁'' ; iintro ξ₂'' ; iintro Hξ₁'' ; iintro Hξ₂'' ;
    iintro t₁' ; iintro t₂' ; iintro Ht'.
    repeat rewrite <- ktx_plug_comp.
    ielim_vars Hw ; [ | eauto | eauto ].
    iespecialize Hw.
    ispecialize Hw ; [eauto|].
    later_shift.
    ielim_vars' LöbIH ξ₁'' ξ₂'' ; [ | eauto | eauto ].
    iespecialize LöbIH.
    iapply LöbIH.
    exact Hw.
Qed.

Lemma plug0 n t₁ t₂ :
  n ⊨ 𝓚𝓥⟦ Ξ ⊢ Ta ⇢ Tb # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  ∀ ξ₁' ξ₂', postfix ξ₁ ξ₁' → postfix ξ₂ ξ₂' →
  n ⊨ 𝓣⟦ Ξ ⊢ Ta # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ Tb # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' (ktx_plug K₁ t₁) (ktx_plug K₂ t₂).
Proof.
  intros.
  eapply unfold_𝓚 ; eauto.
  apply plug0' ; auto.
Qed.

End section_plug0.

Section section_plug1.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (Ta : ty ∅ EV LV ∅) (ε : ef ∅ EV LV ∅) (E : eff ∅ EV LV ∅).
Context (Tb : ty ∅ EV LV ∅).
Context (ξ₁ ξ₂ : list var).
Context (X : var).

Definition 𝓚𝓦' : IProp :=
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁'),
  ∀ᵢ (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ J₁ J₂ s₁ s₂ ψ Xs₁ Xs₂,
  𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' s₁ s₂ ψ Xs₁ Xs₂ ⇒
  (∀ X, (X ∈ Xs₁ → tunnels X J₁) ∧ (X ∈ Xs₂ → tunnels X J₂))ᵢ ⇒
  ( ∀ᵢ ξ₁'' ξ₂'',
    ∀ᵢ (_ : postfix ξ₁' ξ₁'') (_ : postfix ξ₂' ξ₂''),
    ∀ᵢ t₁' t₂',
      ▷ ψ ξ₁'' ξ₂'' t₁' t₂' ⇒
      ▷ 𝓣⟦ Ξ ⊢ Ta # ε :: E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
        ξ₁'' ξ₂'' (ktx_plug J₁ t₁') (ktx_plug J₂ t₂')
  ) ⇒
  𝓣⟦ Ξ ⊢ Tb # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁' ξ₂'
    (ktx_plug (ktx_down ktx_hole X) (ktx_plug J₁ s₁))
    (ktx_plug (ktx_down ktx_hole X) (ktx_plug J₂ s₂)).

Hint Resolve postfix_trans.

Lemma plug1' n :
  n ⊨ (∀ᵢ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂,
      𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇒
      (X \notin L₁ ∧ X \notin L₂)ᵢ) →
  n ⊨ 𝓚𝓥⟦ Ξ ⊢ Ta ⇢ Tb # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      ξ₁ ξ₂ (ktx_down ktx_hole X) (ktx_down ktx_hole X) →
  n ⊨ 𝓚𝓦' →
  n ⊨ 𝓚⟦ Ξ ⊢ Ta # (ε :: E) ⇢ Tb # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      ξ₁ ξ₂ (ktx_down ktx_hole X) (ktx_down ktx_hole X).
Proof.
intros FrX HKv HKw.
loeb_induction LöbIH.
eapply plug'' ; [apply HKv|].

iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro J₁ ; iintro J₂ ; iintro s₁ ; iintro s₂ ; iintro Hw.

apply unfold_𝓦 in Hw.
destruct Hw as [ψ [Xs₁ [Xs₂ [Hs [H_Xs Hw]]]]].

simpl in Hs ; idestruct Hs as Hs Hs.
+ ielim_vars' HKw ξ₁' ξ₂' ; [|eauto|eauto].
  iespecialize HKw.
  ispecialize HKw ; [apply Hs|].
  ispecialize HKw ; [iintro_prop ; apply H_Xs|].
  iapply HKw ; clear HKw.
  apply Hw.
+ repeat rewrite ktx_plug_comp.
  apply 𝓦_in_𝓣.
  eapply fold_𝓦.
  - apply Hs.
  - intro Y.
    iespecialize FrX.
    ispecialize FrX ; [apply Hs|ielim_prop FrX ; destruct FrX].
    specialize (H_Xs Y).
    crush.
  - iintro ξ₁'' ; iintro ξ₂'' ; iintro Hξ₁'' ; iintro Hξ₂'' ;
    iintro s₁' ; iintro s₂' ; iintro Hs'.
    ielim_vars Hw ; [ | eauto | eauto ].
    iespecialize Hw.
    ispecialize Hw ; [ apply Hs' | ].
    later_shift.
    repeat rewrite <- ktx_plug_comp.
    ielim_vars' LöbIH ξ₁'' ξ₂'' ; [ | eauto | eauto].
    iespecialize LöbIH.
    ispecialize LöbIH ; [ apply Hw |].
    exact LöbIH.
Qed.

Corollary plug1 n t₁ t₂ :
  n ⊨ (∀ᵢ ξ₁ ξ₂ t₁ t₂ ψ Xs₁ Xs₂,
      𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ Xs₁ Xs₂ ⇒
      (X \notin Xs₁ ∧ X \notin Xs₂)ᵢ) →
  n ⊨ 𝓚𝓥⟦ Ξ ⊢ Ta ⇢ Tb # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      ξ₁ ξ₂ (ktx_down ktx_hole X) (ktx_down ktx_hole X) →
  n ⊨ 𝓚𝓦' →
  ∀ ξ₁' ξ₂', postfix ξ₁ ξ₁' → postfix ξ₂ ξ₂' →
  n ⊨ 𝓣⟦ Ξ ⊢ Ta # (ε :: E) ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ Tb # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      ξ₁' ξ₂'
      (ktx_plug (ktx_down ktx_hole X) t₁)
      (ktx_plug (ktx_down ktx_hole X) t₂).
Proof.
  intros.
  eapply unfold_𝓚 ; [ eassumption | eassumption | | eassumption ].
  apply plug1' ; assumption.
Qed.

End section_plug1.


Section section_𝓤_is_closed.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (E : eff ∅ EV LV ∅).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (ξ₁ ξ₂ : list var).

Hint Rewrite in_singleton.
Hint Resolve In_from_list.

Lemma 𝓤_is_closed n :
𝜩 Ξ ξ₁ ξ₂ →
n ⊨ δ_is_closed ξ₁ ξ₂ δ →
ρ₁ρ₂_are_closed ξ₁ ξ₂ ρ₁ ρ₂ →
∀ ξ₁' ξ₂' t₁ t₂ ψ Xs₁ Xs₂, n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ ψ Xs₁ Xs₂ →
Xs₁ \c from_list ξ₁ ∧ Xs₂ \c from_list ξ₂.
Proof.
intros Hξ₁ξ₂ cl_δ cl_ρ₁ρ₂ ξ₁' ξ₂' t₁ t₂ ψ Xs₁ Xs₂ Ht.
induction E as [ | ε E' IHE' ] ; [ cbn in Ht ; icontradict Ht | ].
simpl in Ht ; idestruct Ht as Ht Ht ; [ clear E IHE' | auto ].
destruct ε as [ α | α | [ p | [ ι | Y ] ] ] ; simpl in Ht.
+ auto. 
+ iespecialize cl_δ.
  ispecialize cl_δ ; [ apply Ht | ].
  auto.
+ specialize (cl_ρ₁ρ₂ p).
  idestruct Ht as X₁ Ht ; idestruct Ht as X₂ Ht ;
  idestruct Ht as r₁ Ht ; idestruct Ht as r₂ Ht ;
  idestruct Ht as Hρ₁ρ₂ Ht ;
  idestruct Ht as HXs₁Xs₂ Ht ; idestruct Ht as Ht₁t₂ Hr.

  ielim_prop HXs₁Xs₂ ; destruct HXs₁Xs₂ ; subst.
  ielim_prop Ht₁t₂ ; destruct Ht₁t₂ ; subst.
  ielim_prop Hρ₁ρ₂ ; destruct Hρ₁ρ₂ as [Hρ₁ Hρ₂].

  clear - cl_ρ₁ρ₂ Hρ₁ Hρ₂.
  specialize (cl_ρ₁ρ₂ X₁) as HX₁ ; destruct HX₁ as [HX₁ _].
  specialize (cl_ρ₁ρ₂ X₂) as HX₂ ; destruct HX₂ as [_ HX₂].
  split ; intro ; crush.
+ contradict ι.
+ idestruct Ht as X₁ Ht ; idestruct Ht as X₂ Ht ;
  idestruct Ht as r₁ Ht ; idestruct Ht as r₂ Ht ;
  idestruct Ht as HX₁X₂ Ht ; idestruct Ht as HXs₁Xs₂ Ht ;
  idestruct Ht as Ht₁t₂ Ht ; idestruct Ht as HY Hr.

  ielim_prop HXs₁Xs₂ ; destruct HXs₁Xs₂ ; subst.
  ielim_prop HX₁X₂ ; destruct HX₁X₂ as [HX₁ HX₂].
  ielim_prop HY.
  inversion HX₁ ; inversion HX₂ ; subst X₁ X₂.

  clear - HY Hξ₁ξ₂.
  destruct Hξ₁ξ₂.
  split ; intro ; crush.
Qed.

End section_𝓤_is_closed.

Ltac bind_hole :=
  match goal with
  | [ |- ?n ⊨ 𝓣⟦ ?Ξ ⊢ ?T # ?E ⟧ _ _ _ _ _ _ _ _ ?t₁ ?t₂ ] =>
  replace t₁ with (ktx_plug ktx_hole t₁) by reflexivity ;
  replace t₂ with (ktx_plug ktx_hole t₂) by reflexivity
  end.
