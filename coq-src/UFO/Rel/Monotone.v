Require Import UFO.Util.Postfix.
Require Import UFO.Util.Subset.
Require Import UFO.Rel.Definitions.
Set Implicit Arguments.

(** Monotinicity with respect to label allocation *)

Section section_monotone.

Hint Resolve postfix_trans.
Hint Resolve subset_trans.

Lemma 𝓡_monotone_l n 𝓥 𝓤 ξ₁ ξ₁' ξ₂ K₁ K₂ :
postfix ξ₁ ξ₁' →
n ⊨ 𝓡_Fun_Fix' 𝓥 𝓤 ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓡_Fun_Fix' 𝓥 𝓤 ξ₁' ξ₂ K₁ K₂.
Proof.
intros Hξ₁' HK ; idestruct HK as HKv HKw ; isplit.
+ iintro ξ₁'' ; iintro ξ₂' ; iintro Hξ₁'' ; iintro Hξ₂'.
  ielim_vars HKv ; [ apply HKv | eauto | eauto ].
+ iintro ξ₁'' ; iintro ξ₂' ; iintro Hξ₁'' ; iintro Hξ₂'.
  ielim_vars HKw ; [ apply HKw | eauto | eauto ].
Qed.

Lemma 𝓡_monotone_r n 𝓥 𝓤 ξ₁ ξ₂ ξ₂' K₁ K₂ :
postfix ξ₂ ξ₂' →
n ⊨ 𝓡_Fun_Fix' 𝓥 𝓤 ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓡_Fun_Fix' 𝓥 𝓤 ξ₁ ξ₂' K₁ K₂.
Proof.
intros Hξ₂' HK ; idestruct HK as HKv HKw ; isplit.
+ iintro ξ₁' ; iintro ξ₂'' ; iintro Hξ₁' ; iintro Hξ₂''.
  ielim_vars HKv ; [ apply HKv | eauto | eauto ].
+ iintro ξ₁' ; iintro ξ₂'' ; iintro Hξ₁' ; iintro Hξ₂''.
  ielim_vars HKw ; [ apply HKw | eauto | eauto ].
Qed.

Hint Resolve 𝓡_monotone_l 𝓡_monotone_r.

Corollary 𝓡_monotone n 𝓥 𝓤 ξ₁ ξ₁' ξ₂ ξ₂' K₁ K₂ :
n ⊨ 𝓡_Fun_Fix' 𝓥 𝓤 ξ₁ ξ₂ K₁ K₂ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝓡_Fun_Fix' 𝓥 𝓤 ξ₁' ξ₂' K₁ K₂.
Proof.
eauto.
Qed.

Lemma 𝓚_monotone_l n 𝓣a 𝓣b ξ₁ ξ₁' ξ₂ K₁ K₂ :
postfix ξ₁ ξ₁' →
n ⊨ 𝓚_Fun 𝓣a 𝓣b ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓚_Fun 𝓣a 𝓣b ξ₁' ξ₂ K₁ K₂.
Proof.
intros ? HK ; do 4 iintro.
ielim_vars HK ; eauto.
Qed.

Lemma 𝓚_monotone_r n 𝓣a 𝓣b ξ₁ ξ₂ ξ₂' K₁ K₂ :
postfix ξ₂ ξ₂' →
n ⊨ 𝓚_Fun 𝓣a 𝓣b ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓚_Fun 𝓣a 𝓣b ξ₁ ξ₂' K₁ K₂.
Proof.
intros ? HK ; do 4 iintro.
ielim_vars HK ; eauto.
Qed.

Hint Resolve 𝓚_monotone_l 𝓚_monotone_r.

Lemma 𝓚_monotone n 𝓣a 𝓣b ξ₁ ξ₁' ξ₂ ξ₂' K₁ K₂ :
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝓚_Fun 𝓣a 𝓣b ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓚_Fun 𝓣a 𝓣b ξ₁' ξ₂' K₁ K₂.
Proof.
eauto.
Qed.

Lemma 𝓗_monotone_l n 𝓣a 𝓣b ξ₁ ξ₁' ξ₂ r₁ r₂ :
postfix ξ₁ ξ₁' →
n ⊨ 𝓗_Fun 𝓣a 𝓣b ξ₁ ξ₂ r₁ r₂ →
n ⊨ 𝓗_Fun 𝓣a 𝓣b ξ₁' ξ₂ r₁ r₂.
Proof.
intros ? H ; do 4 iintro.
ielim_vars H ; eauto.
Qed.

Lemma 𝓗_monotone_r n 𝓣a 𝓣b ξ₁ ξ₂ ξ₂' r₁ r₂ :
postfix ξ₂ ξ₂' →
n ⊨ 𝓗_Fun 𝓣a 𝓣b ξ₁ ξ₂ r₁ r₂ →
n ⊨ 𝓗_Fun 𝓣a 𝓣b ξ₁ ξ₂' r₁ r₂.
Proof.
intros ? H ; do 4 iintro.
ielim_vars H ; eauto.
Qed.

Hint Resolve 𝓗_monotone_l 𝓗_monotone_r.

Corollary 𝓗_monotone n 𝓣a 𝓣b ξ₁ ξ₁' ξ₂ ξ₂' r₁ r₂ :
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝓗_Fun 𝓣a 𝓣b ξ₁ ξ₂ r₁ r₂ →
n ⊨ 𝓗_Fun 𝓣a 𝓣b ξ₁' ξ₂' r₁ r₂.
Proof.
eauto.
Qed.

Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (γ₁ γ₂ : V → val0).

Lemma 𝓜_monotone_l n σ ℓ ξ₁ ξ₁' ξ₂ m₁ m₂ :
postfix ξ₁ ξ₁' →
n ⊨ 𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ →
n ⊨ 𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂ m₁ m₂.
Proof.
+ destruct σ as [ σ' | σ' | σ' | T E ] ; intros Hξ₁' Hm ; simpl in Hm |- *.
  - idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
    idestruct Hm as Hm Hm'.
    repeat ieexists ; isplit ; [ eassumption | ].
    do 4 iintro.
    ielim_vars Hm' ; eauto.
  - idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
    idestruct Hm as Hm Hm'.
    repeat ieexists ; isplit ; [ eassumption | ].
    do 4 iintro.
    ielim_vars Hm' ; eauto.
  - idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
    idestruct Hm as Hm Hm'.
    repeat ieexists ; isplit ; [ eassumption | ].
    do 4 iintro.
    ielim_vars Hm' ; eauto.
  - idestruct Hm as r₁ Hm ; idestruct Hm as r₂ Hm ;
    idestruct Hm as Hm Hr ; idestruct Hr as HX Hr.
    repeat ieexists ; repeat isplit ; [ eassumption | eassumption | ].
    later_shift.
    eapply 𝓗_monotone_l ; eauto.
Qed.

Lemma 𝓜_monotone_r n σ ℓ ξ₁ ξ₂ ξ₂' m₁ m₂ :
postfix ξ₂ ξ₂' →
n ⊨ 𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ →
n ⊨ 𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂' m₁ m₂.
Proof.
+ destruct σ as [ σ' | σ' | σ' | T E ] ; intros Hξ₂' Hm ; simpl in Hm |- *.
  - idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
    idestruct Hm as Hm Hm'.
    repeat ieexists ; isplit ; [ eassumption | ].
    do 4 iintro.
    ielim_vars Hm' ; eauto.
  - idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
    idestruct Hm as Hm Hm'.
    repeat ieexists ; isplit ; [ eassumption | ].
    do 4 iintro.
    ielim_vars Hm' ; eauto.
  - idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
    idestruct Hm as Hm Hm'.
    repeat ieexists ; isplit ; [ eassumption | ].
    do 4 iintro.
    ielim_vars Hm' ; eauto.
  - idestruct Hm as r₁ Hm ; idestruct Hm as r₂ Hm ;
    idestruct Hm as Hm Hr ; idestruct Hr as HX Hr.
    repeat ieexists ; repeat isplit ; [ eassumption | eassumption | ].
    later_shift.
    eapply 𝓗_monotone_r ; eauto.
Qed.

Hint Resolve 𝓜_monotone_l 𝓜_monotone_r.

Corollary 𝓜_monotone n σ ℓ ξ₁ ξ₁' ξ₂ ξ₂' m₁ m₂ :
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ →
n ⊨ 𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' m₁ m₂.
Proof.
eauto.
Qed.

Lemma 𝓥_monotone_l n T ξ₁ ξ₁' ξ₂ v₁ v₂ :
postfix ξ₁ ξ₁' →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂ v₁ v₂.
Proof.
+ destruct T as [ | Ta Ea Tb Eb | 𝔽 ℓ | σ ℓ ] ; intros Hξ₁' Hv ;
  simpl in Hv|-*.
  - crush.
  - idestruct Hv as K₁ Hv ; idestruct Hv as K₂ Hv ;
    idestruct Hv as Hv HK.
    repeat ieexists ; isplit ; eauto.
  - idestruct Hv as m₁ Hv ; idestruct Hv as m₂ Hv ;
    idestruct Hv as X₁ Hv ; idestruct Hv as X₂ Hv ;
    idestruct Hv as Hv HX ; idestruct HX as HX Hm.
    repeat ieexists ; repeat isplit ; try eassumption.
    later_shift.
    apply 𝓥_roll ; apply 𝓥_unroll in Hm.
    simpl in Hm |- *.
    idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
    idestruct Hm as X₁' Hm ; idestruct Hm as X₂' Hm ;
    idestruct Hm as Hm HX' ; idestruct HX' as HX' Hm'.
    repeat ieexists ; repeat isplit ; eauto.
  - idestruct Hv as m₁ Hv ; idestruct Hv as m₂ Hv ;
    idestruct Hv as X₁ Hv ; idestruct Hv as X₂ Hv ;
    idestruct Hv as Hv HX ; idestruct HX as HX Hm.
    repeat ieexists ; repeat isplit ; eauto.
Qed.

Lemma 𝓥_monotone_r n T ξ₁ ξ₂ ξ₂' v₁ v₂ :
postfix ξ₂ ξ₂' →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂' v₁ v₂.
Proof.
+ destruct T as [ | Ta Ea Tb Eb | 𝔽 ℓ | σ ℓ ] ; intros Hξ₂' Hv ; simpl in Hv |- *.
  - crush.
  - idestruct Hv as K₁ Hv ; idestruct Hv as K₂ Hv ;
    idestruct Hv as Hv HK.
    repeat ieexists ; isplit ; eauto.
  - idestruct Hv as m₁ Hv ; idestruct Hv as m₂ Hv ;
    idestruct Hv as X₁ Hv ; idestruct Hv as X₂ Hv ;
    idestruct Hv as Hv HX ; idestruct HX as HX Hm.
    repeat ieexists ; repeat isplit ; try eassumption.
    later_shift.
    apply 𝓥_roll ; apply 𝓥_unroll in Hm.
    simpl in Hm |- *.
    idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
    idestruct Hm as X₁' Hm ; idestruct Hm as X₂' Hm ;
    idestruct Hm as Hm HX' ; idestruct HX' as HX' Hm'.
    repeat ieexists ; repeat isplit ; eauto.
 - idestruct Hv as m₁ Hv ; idestruct Hv as m₂ Hv ;
    idestruct Hv as X₁ Hv ; idestruct Hv as X₂ Hv ;
    idestruct Hv as Hv HX ; idestruct HX as HX Hm.
    repeat ieexists ; repeat isplit ; eauto.
Qed.

Hint Resolve 𝓥_monotone_l 𝓥_monotone_r.

Corollary 𝓥_monotone n T ξ₁ ξ₁' ξ₂ ξ₂' v₁ v₂ :
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' v₁ v₂.
Proof.
eauto.
Qed.

Lemma 𝜞_monotone n Γ ξ₁ ξ₁' ξ₂ ξ₂' :
n ⊨ 𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' γ₁ γ₂.
Proof.
intros Hγ ? ? ; iintro x ; ispecialize Hγ x.
eauto.
Qed.

Hint Resolve postfix_is_subset.

Lemma 𝜩_monotone ξ₁ ξ₂ ξ₁' ξ₂' :
𝜩 Ξ ξ₁ ξ₂ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
𝜩 Ξ ξ₁' ξ₂'.
Proof.
intros H ? ?.
destruct H ; split ; eauto.
Qed.

Lemma δ_is_closed_monotone n ξ₁ ξ₂ ξ₁' ξ₂' :
n ⊨ δ_is_closed ξ₁ ξ₂ δ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ δ_is_closed ξ₁' ξ₂' δ.
Proof.
intros H ? ? ; repeat iintro.
iespecialize H ; ispecialize H ; [ eassumption | ].
ielim_prop H ; destruct H ; split ; eauto.
Qed.

Hint Resolve postfix_In.

Lemma ρ₁ρ₂_are_closed_monotone ξ₁ ξ₂ ξ₁' ξ₂' :
ρ₁ρ₂_are_closed ξ₁ ξ₂ ρ₁ ρ₂ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
ρ₁ρ₂_are_closed ξ₁' ξ₂' ρ₁ ρ₂.
Proof.
intros H H₁ H₂ ; repeat iintro.
intros α X ; specialize (H α X).
apply postfix_is_subset in H₁.
apply postfix_is_subset in H₂.
destruct H ; split ; intro ; auto.
Qed.

End section_monotone.
