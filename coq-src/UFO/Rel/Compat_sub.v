Require Import Lang.Static.
Require Import Rel.Definitions.
Require Import Rel.Monotone.
Require Import Rel.BasicFacts.
Require Import Util.Postfix.

Implicit Types EV LV V : Set.

Section section_ccompat_se.

Lemma ccompat_eff_In
EV LV (Ξ : XEnv EV LV) δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂
ε E (Hε : In ε E) t₁ t₂ ψ l₁ l₂ n :
n ⊨ 𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ →
n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂.
Proof.
intro.
induction E ; [ crush | ].
apply in_inv in Hε ; destruct Hε ; [ ileft | iright ] ; crush.
Qed.

Lemma ccompat_eff_In_inverse
EV LV (Ξ : XEnv EV LV) δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂
E t₁ t₂ ψ l₁ l₂ n :
n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ →
∃ ε, In ε E ∧ (n ⊨ 𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂).
Proof.
intro Ht.
induction E as [ | ε E IH ] ; [ crush | ].
idestruct Ht as Ht Ht.
+ exists ε ; crush.
+ destruct (IH Ht) as [ ε' ? ].
  exists ε' ; crush.
Qed.

Lemma ccompat_se
EV LV (Ξ : XEnv EV LV) δ₁ δ₂ δ ρ₁ ρ₂ ρ
E E' (Q : se E E')
ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ n :
n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ →
n ⊨ 𝓤⟦ Ξ ⊢ E' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂.
Proof.
intro H.
induction E as [ | ε E IHE ] ; simpl in * ; [ crush | ].
idestruct H as Hε HE.
- destruct E' as [ | ε' E' ] ; simpl in *.
  * destruct (Q ε) ; auto.
  * destruct (Q ε) ; [ auto | subst | ].
    { ileft ; assumption. }
    { iright ; eapply ccompat_eff_In ; eauto. }
- crush.
Qed.

End section_ccompat_se.

Lemma ccompat_sub𝓥_hole
𝓥1 𝓥2 𝓤2
(H : ∀ ξ₁ ξ₂ v₁ v₂ n, n ⊨ 𝓥1 ξ₁ ξ₂ v₁ v₂ → n ⊨ 𝓥2 ξ₁ ξ₂ v₁ v₂)
n ξ₁ ξ₂ :
n ⊨ 𝓚𝓥_Fun 𝓥1 (𝓣_Fun_Fix' 𝓥2 𝓤2) ξ₁ ξ₂ ktx_hole ktx_hole.
Proof.
iintro ξ₁' ; iintro ξ₂' ; iintro v₁ ; iintro v₂ ; iintro Hξ₁' ; iintro Hξ₂'.
simpl.
iintro Hv.
apply 𝓥_in_𝓣 ; auto.
Qed.

Lemma ccompat_sub𝓦_hole
𝓥1 𝓥2 𝓤1 𝓤2
(Hsub𝓥 : ∀ ξ₁ ξ₂ v₁ v₂ n, n ⊨ 𝓥1 ξ₁ ξ₂ v₁ v₂ → n ⊨ 𝓥2 ξ₁ ξ₂ v₁ v₂)
(Hsub𝓤 : ∀ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ n, n ⊨ 𝓤1 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ → n ⊨ 𝓤2 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂)
n ξ₁ ξ₂ :
n ⊨ 𝓚𝓦_Fun 𝓥1 𝓤1 (𝓣_Fun_Fix' 𝓥2 𝓤2) ξ₁ ξ₂ ktx_hole ktx_hole.
Proof.
loeb_induction LöbIH.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
iintro K₁ ; iintro K₂ ; iintro t₁ ; iintro t₂.
simpl.
iintro HKt.
apply 𝓦_in_𝓣.
idestruct HKt as ψ HKt ; idestruct HKt as l₁ HKt ; idestruct HKt as l₂ HKt.
idestruct HKt as Ht HKt.
idestruct HKt as Xs_K₁K₂ Hψ.
ielim_prop Xs_K₁K₂.
repeat ieexists ; repeat isplit.
+ eauto.
+ auto.
+ iintro ξ₁'' ; iintro ξ₂'' ; iintro Hξ₁'' ; iintro Hξ₂'' ;
  iintro t₁' ; iintro t₂'.
  ielim_vars Hψ ; [|eauto|eauto].
  iespecialize Hψ.
  later_shift.
  iintro Ht'.
  ispecialize Hψ ; [ apply Ht' | ].
  apply 𝓣_unroll in Hψ ; apply 𝓣_roll.
  change (ktx_plug K₁ t₁') with (ktx_plug ktx_hole (ktx_plug K₁ t₁')).
  change (ktx_plug K₂ t₂') with (ktx_plug ktx_hole (ktx_plug K₂ t₂')).
  eapply plug'.
  - apply ccompat_sub𝓥_hole ; eauto.
  - apply LöbIH.
  - clear - Hξ₁' Hξ₁'' ; eauto using postfix_trans.
  - clear - Hξ₂' Hξ₂'' ; eauto using postfix_trans.
  - apply Hψ.
Qed.

Lemma ccompat_sub𝓥a𝓤a_sub𝓣b_ktx
𝓥a1 𝓤a1 𝓥a2 𝓤a2 𝓣b1 𝓣b2 :
(∀ ξ₁ ξ₂ v₁ v₂ n, n ⊨ 𝓥a2 ξ₁ ξ₂ v₁ v₂ → n ⊨ 𝓥a1 ξ₁ ξ₂ v₁ v₂) →
(∀ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ n, n ⊨ 𝓤a2 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ → n ⊨ 𝓤a1 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂) →
(∀ ξ₁ ξ₂ t₁ t₂ n , n ⊨ 𝓣b1 ξ₁ ξ₂ t₁ t₂ → n ⊨ 𝓣b2 ξ₁ ξ₂ t₁ t₂) →
∀ ξ₁ ξ₂ K₁ K₂ n,
n ⊨ 𝓚_Fun (𝓣_Fun_Fix' 𝓥a1 𝓤a1) 𝓣b1 ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓚_Fun (𝓣_Fun_Fix' 𝓥a2 𝓤a2) 𝓣b2 ξ₁ ξ₂ K₁ K₂.
Proof.
intros ? ? ? ξ₁ ξ₂ K₁ K₂ n HK.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
iintro t₁ ; iintro t₂ ; iintro Ht.
ielim_vars HK ; [|eauto|eauto].
ispecialize HK t₁.
ispecialize HK t₂.
ispecialize HK ; [ | auto ].
change t₁ with (ktx_plug ktx_hole t₁).
change t₂ with (ktx_plug ktx_hole t₂).
eapply plug'.
* eapply ccompat_sub𝓥_hole ; eassumption.
* eapply ccompat_sub𝓦_hole ; eassumption.
* eassumption.
* eassumption.
* eassumption.
Qed.

Lemma ccompat_sub𝓣a_sub𝓥b𝓤b_ktx
𝓣a1 𝓣a2 𝓥b1 𝓤b1 𝓥b2 𝓤b2 :
(∀ ξ₁ ξ₂ t₁ t₂ n , n ⊨ 𝓣a2 ξ₁ ξ₂ t₁ t₂ → n ⊨ 𝓣a1 ξ₁ ξ₂ t₁ t₂) →
(∀ ξ₁ ξ₂ v₁ v₂ n, n ⊨ 𝓥b1 ξ₁ ξ₂ v₁ v₂ → n ⊨ 𝓥b2 ξ₁ ξ₂ v₁ v₂) →
(∀ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ n, n ⊨ 𝓤b1 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ → n ⊨ 𝓤b2 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂) →
∀ ξ₁ ξ₂ K₁ K₂ n,
n ⊨ 𝓚_Fun 𝓣a1 (𝓣_Fun_Fix' 𝓥b1 𝓤b1) ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓚_Fun 𝓣a2 (𝓣_Fun_Fix' 𝓥b2 𝓤b2) ξ₁ ξ₂ K₁ K₂.
Proof.
intros ? ? ? ξ₁ ξ₂ K₁ K₂ n HK.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
iintro t₁ ; iintro t₂ ; iintro Ht.
ielim_vars HK ; [|eauto|eauto].
ispecialize HK t₁.
ispecialize HK t₂.
ispecialize HK ; [ auto | ].
change (ktx_plug K₁ t₁) with (ktx_plug ktx_hole (ktx_plug K₁ t₁)).
change (ktx_plug K₂ t₂) with (ktx_plug ktx_hole (ktx_plug K₂ t₂)).
eapply plug'.
* eapply ccompat_sub𝓥_hole ; eassumption.
* eapply ccompat_sub𝓦_hole ; eassumption.
* eassumption.
* eassumption.
* eassumption.
Qed.

Lemma ccompat_sub𝓥a𝓤a_sub𝓥b𝓤b_ktx
𝓥a1 𝓤a1 𝓥b1 𝓤b1 𝓥a2 𝓤a2 𝓥b2 𝓤b2 :
(∀ ξ₁ ξ₂ v₁ v₂ n, n ⊨ 𝓥a2 ξ₁ ξ₂ v₁ v₂ → n ⊨ 𝓥a1 ξ₁ ξ₂ v₁ v₂) →
(∀ ξ₁ ξ₂ v₁ v₂ n, n ⊨ 𝓥b1 ξ₁ ξ₂ v₁ v₂ → n ⊨ 𝓥b2 ξ₁ ξ₂ v₁ v₂) →
(∀ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ n, n ⊨ 𝓤a2 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ → n ⊨ 𝓤a1 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂) →
(∀ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ n, n ⊨ 𝓤b1 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ → n ⊨ 𝓤b2 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂) →
∀ ξ₁ ξ₂ K₁ K₂ n,
n ⊨ 𝓚_Fun (𝓣_Fun_Fix' 𝓥a1 𝓤a1) (𝓣_Fun_Fix' 𝓥b1 𝓤b1) ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓚_Fun (𝓣_Fun_Fix' 𝓥a2 𝓤a2) (𝓣_Fun_Fix' 𝓥b2 𝓤b2) ξ₁ ξ₂ K₁ K₂.
Proof.
intros.
eapply ccompat_sub𝓥a𝓤a_sub𝓣b_ktx ; [eauto|eauto|eauto| ].
eapply ccompat_sub𝓣a_sub𝓥b𝓤b_ktx ; [eauto|eauto|eauto| ].
assumption.
Qed.

Fixpoint
ccompat_st
EV LV (Ξ : XEnv EV LV) δ₁ δ₂ δ ρ₁ ρ₂ ρ
T T' (H : st T T') {struct H} :
∀ ξ₁ ξ₂ v₁ v₂ n,
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
n ⊨ 𝓥⟦ Ξ ⊢ T' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂
with
ccompat_ss
EV LV (Ξ : XEnv EV LV) δ₁ δ₂ δ ρ₁ ρ₂ ρ
σ σ' ℓ (H : ss σ σ') {struct H} :
∀ ξ₁ ξ₂ m₁ m₂ n,
n ⊨ 𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ →
n ⊨ 𝓜⟦ Ξ ⊢ σ' ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂
.
Proof.
{
intros ξ₁ ξ₂ v₁ v₂ n.
destruct H ; simpl ; intro Hv.
+ auto.
+ idestruct Hv as K₁ Hv ; idestruct Hv as K₂ Hv ; idestruct Hv as Hv HK.
  repeat ieexists ; isplit ; [ eassumption | ].
  eapply ccompat_sub𝓥a𝓤a_sub𝓥b𝓤b_ktx ; try eassumption.
  - apply ccompat_st ; assumption.
  - apply ccompat_st ; assumption.
  - apply ccompat_se ; assumption.
  - apply ccompat_se ; assumption.
+ apply Hv.
+ idestruct Hv as m₁ Hv ; idestruct Hv as m₂ Hv ;
  idestruct Hv as X₁ Hv ; idestruct Hv as X₂ Hv ;
  idestruct Hv as Hv Hm ; idestruct Hm as Hℓ Hm.
  repeat ieexists ; repeat isplit ; try eassumption.
  eauto.
+ eapply ccompat_st ; [ eassumption | ].
  eapply ccompat_st ; [ eassumption | ].
  apply Hv.
}

{
intros ξ₁ ξ₂ m₁ m₂ n.
destruct H ; simpl 𝓜_Fun ; intro Hm.
+ idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
  idestruct Hm as Hm Hm'.
  ielim_prop Hm ; destruct Hm ; subst.
  repeat ieexists ; isplit ; [ eauto | ].
  repeat iintro.
  ielim_vars Hm' ; [|eauto|eauto].
  iespecialize Hm'.
  ispecialize Hm' ; [ eassumption | ].
  eapply ccompat_ss ; [ apply H | ].
  apply Hm'.
+ idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
  idestruct Hm as Hm Hm'.
  ielim_prop Hm ; destruct Hm ; subst.
  repeat ieexists ; isplit ; [ eauto | ].
  repeat iintro.
  ielim_vars Hm' ; [|eauto|eauto].
  iespecialize Hm'.
  ispecialize Hm' ; [ eassumption | ].
  eapply ccompat_ss ; [ apply H | ].
  apply Hm'.
+ idestruct Hm as m₁' Hm ; idestruct Hm as m₂' Hm ;
  idestruct Hm as Hm Hm'.
  ielim_prop Hm ; destruct Hm ; subst.
  repeat ieexists ; isplit ; [ eauto | ].
  repeat iintro.
  ielim_vars Hm' ; [|eauto|eauto].
  iespecialize Hm'.
  ispecialize Hm'.
  - eapply ccompat_st ; eassumption.
  - eapply ccompat_ss ; [ eassumption | ].
    apply Hm'.
+ idestruct Hm as r₁ Hm ; idestruct Hm as r₂ Hm ;
  idestruct Hm as Hm Hr ; idestruct Hr as HX Hr.
  ielim_prop Hm ; destruct Hm ; subst.
  repeat ieexists ; repeat isplit ; [ auto | auto | ].
  later_shift.
  iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
  ielim_vars Hr ; [|eauto|eauto].
  iintro K₁ ; iintro K₂ ; iintro HKY.
  iespecialize Hr ; iapply Hr.
  eapply ccompat_sub𝓥a𝓤a_sub𝓣b_ktx
  with (𝓤a1 :=
    λ _ξ₁ _ξ₂ _t₁ _t₂ _Φ _L₁ _L₂,
    𝓾⟦ Ξ ⊢ ef_lbl ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ _ξ₁ _ξ₂ _t₁ _t₂ _Φ _L₁ _L₂ ∨ᵢ
    𝓤⟦ Ξ ⊢ E2 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ _ξ₁ _ξ₂ _t₁ _t₂ _Φ _L₁ _L₂
  ).
  - apply ccompat_st ; eassumption.
  - intros _ξ₁ _ξ₂ _t₁ _t₂ _Φ _L₁ _L₂ _n _H.
    idestruct _H as _H _H ; [ ileft | iright ].
    * apply _H.
    * eapply ccompat_se ; eassumption.
  - clear ; intros ; eassumption.
  - eassumption.
+ eapply ccompat_ss ; [ eassumption | ].
  eapply ccompat_ss ; [ eassumption | ].
  apply Hm.
}
Qed.

Lemma ccompat_sub
EV LV (Ξ : XEnv EV LV) δ₁ δ₂ δ ρ₁ ρ₂ ρ
T T' E E' :
st T T' →
se E E' →
∀ ξ₁ ξ₂ t₁ t₂ n,
n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ →
n ⊨ 𝓣⟦ Ξ ⊢ T' # E' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
intros HT HE ξ₁ ξ₂ t₁ t₂ n Ht.
bind_hole.
apply plug with (Ta := T) (Ea := E) (ξ₁ := ξ₁) (ξ₂ := ξ₂).
+ apply ccompat_sub𝓥_hole.
  apply ccompat_st.
  assumption.
+ apply ccompat_sub𝓦_hole.
  - apply ccompat_st ; assumption.
  - apply ccompat_se ; assumption.
+ apply postfix_refl.
+ apply postfix_refl.
+ assumption.
Qed.

Lemma compat_sub
EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅)
T T' E E' :
st T T' →
se E E' →
∀ t₁ t₂ n,
n ⊨ ⟦ Ξ Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # E ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T' # E' ⟧.
Proof.
intros HT HE t₁ t₂ n Ht.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro HΞ ; iintro cl_δ ; iintro cl_ρ ; iintro HΓ.
eapply ccompat_sub.
+ apply HT.
+ apply HE.
+ iespecialize Ht.
  repeat (ispecialize Ht ; [ eassumption | ]).
  exact Ht.
Qed.
