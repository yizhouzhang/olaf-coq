Require Import LibReflect LibList.
Require Import UFO.Util.Wf_natnat.
Require Import UFO.Rel.Definitions.
Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Lang.Static.
Require Import UFO.Lang.StaticFacts.
Set Implicit Arguments.

Implicit Types EV LV : Set.

Section section_X_weaken_aux.

Local Hint Extern 1 => match goal with
| [ |- ?n ⊨ ?X ≈ᵢ ?X ] => repeat iintro ; apply auto_contr_id
| [ |- ?n ⊨ ?X ⇔ ?X ] => apply auto_contr_id
| [ |- Acc lt' (_, _) ] => try lt'_solve
end.

Fixpoint
  X_weaken_𝓾_aux
  (n : nat)
  (EV LV : Set)
  (Ξ Ξ' : XEnv EV LV)
  (Wf_ΞΞ' : wf_XEnv (Ξ & Ξ'))
  (Disj : disjoint (dom Ξ) (dom Ξ'))
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (ε : ef ∅ EV LV ∅)
  (Wf_ε : wf_ef Ξ ε)
  (W : Acc lt' (n, 0))
  {struct W} :
  (n ⊨
    𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓾⟦ (Ξ & Ξ') ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)

with
  X_weaken_𝓤_aux
  (n : nat)
  (EV LV : Set)
  (Ξ Ξ' : XEnv EV LV)
  (Wf_ΞΞ' : wf_XEnv (Ξ & Ξ'))
  (Disj : disjoint (dom Ξ) (dom Ξ'))
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (E : eff ∅ EV LV ∅)
  (Wf_E : wf_eff Ξ E)
  (W : Acc lt' (n, size_eff E))
  {struct W} :
  (n ⊨
    𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (Ξ & Ξ') ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)

with
  X_weaken_𝓥_aux
  (n : nat)
  (EV LV : Set)
  (Ξ Ξ' : XEnv EV LV)
  (Wf_ΞΞ' : wf_XEnv (Ξ & Ξ'))
  (Disj : disjoint (dom Ξ) (dom Ξ'))
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (v₁ v₂ : val0) (T : ty ∅ EV LV ∅)
  (Wf_T : wf_ty Ξ T)
  (W : Acc lt' (n, size_ty T))
  {struct W} :
  (n ⊨
    𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (Ξ & Ξ') ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂)

with
  X_weaken_𝓜_aux
  (n : nat)
  (EV LV : Set)
  (Ξ Ξ' : XEnv EV LV)
  (Wf_ΞΞ' : wf_XEnv (Ξ & Ξ'))
  (Disj : disjoint (dom Ξ) (dom Ξ'))
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (m₁ m₂ : md0) (σ : ms ∅ EV LV ∅) (ℓ : lbl LV ∅)
  (Wf_σ : wf_ms Ξ σ) (Wf_ℓ : wf_lbl Ξ ℓ)
  (W : Acc lt' (n, size_ms σ))
  {struct W} :
  (n ⊨
    𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ ⇔
    𝓜⟦ (Ξ & Ξ') ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂)
.

Proof.

{
destruct ε as [ | α | [ p | [ | X ] ] ] ; simpl.
+ auto.
+ auto_contr.
+ auto_contr.
+ auto_contr.
+ inversion Wf_ε as [ | | ? [ ? HX | ] ] ; subst.
  auto_contr.
  - rewrite dom_concat, in_union.
    split ; crush.
  - apply 𝓗_Fun_nonexpansive ; repeat iintro ; [ auto_contr | ].
    apply get_some in HX as BindsX ; destruct BindsX as [ [T E] BindsX ].
    rewrite get_concat.
    eapply disjoint_in_notin in Disj as BindsNotX ; [ | eassumption ].
    apply get_none in BindsNotX.
    rewrite BindsX, BindsNotX.
    apply wf_XEnv_concat_inv_l in Wf_ΞΞ' as Wf_Ξ.
    specialize (binds_wf Wf_Ξ BindsX) as Wf_TE.
    apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
    { apply 𝓥_roll_unroll_iff ; crush. }
    { apply 𝓤_roll_unroll_iff ; crush. }
}

{
destruct E ; simpl ; [auto|].
inversion Wf_E ; auto_contr ; auto.
}

{
destruct T as [ | Ta Ea Tb Eb | N ℓ | σ ℓ ] eqn:HT ; simpl 𝓥_Fun ; inversion Wf_T ; subst.
+ crush.
+ auto_contr.
  apply 𝓚_Fun_nonexpansive ; repeat iintro ;
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
+ auto_contr.
  apply 𝓥_roll_unroll_iff.
  apply X_weaken_𝓥_aux ; [ auto | auto | | auto ].
  constructor ; [ | auto ].
  inversion Wf_T.
  apply wf_it_msig ; assumption.
+ auto_contr ; auto.
}

Hint Resolve EV_map_wf_XEnv EV_map_wf_lbl.
Hint Resolve LV_map_wf_XEnv LV_map_wf_lbl.
Hint Rewrite EV_map_XEnv_dom.
Hint Rewrite LV_map_XEnv_dom.
Hint Rewrite <- EV_map_XEnv_concat.
Hint Rewrite <- LV_map_XEnv_concat.

{
destruct σ as [ τ | τ | τ | Ta Ea ] eqn:Hσ ; simpl 𝓜_Fun ; inversion Wf_σ ; subst.
+ auto_contr.
  rewrite EV_map_XEnv_concat.
  apply X_weaken_𝓜_aux ; crush.
+ auto_contr.
  rewrite LV_map_XEnv_concat.
  apply X_weaken_𝓜_aux ; crush.
+ auto_contr ; auto.
+ destruct ℓ as [ α | [ | Χ ] ] ; simpl ; [ | crush | ].
  - auto_contr.
    apply 𝓗_Fun_nonexpansive ; repeat iintro.
    * apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ auto | ].
      auto_contr ; auto.
    * auto_contr.
  - inversion Wf_ℓ as [ ? HX | ] ; subst.
    apply get_some in HX as BindsX ; destruct BindsX as [ [T E] BindsX ].
    rewrite get_concat, dom_concat, in_union.
    eapply disjoint_in_notin in Disj as BindsNotX ; [ | eassumption ].
    apply get_none in BindsNotX.
    rewrite BindsX, BindsNotX.
    apply wf_XEnv_concat_inv_l in Wf_ΞΞ' as Wf_Ξ.
    specialize (binds_wf Wf_Ξ BindsX) as Wf_TE.
    auto_contr ; [ crush | ].
    apply 𝓗_Fun_nonexpansive ; repeat iintro.
    * apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ auto | ].
      auto_contr.
      ++ split ; crush.
      ++ apply 𝓗_Fun_nonexpansive ; repeat iintro.
         -- auto_contr.
         -- apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
            { apply 𝓥_roll_unroll_iff ; crush. }
            { apply 𝓤_roll_unroll_iff ; crush. }
      ++ apply X_weaken_𝓤_aux ; auto. 
    * apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
      { apply 𝓥_roll_unroll_iff ; crush. }
      { apply 𝓤_roll_unroll_iff ; crush. }
}
Qed.

End section_X_weaken_aux.

Section section_X_weaken.

Context (n : nat).
Context (EV LV : Set).
Context (Ξ Ξ' : XEnv EV LV).
Context (Wf_ΞΞ' : wf_XEnv (Ξ & Ξ')).
Context (Disj : disjoint (dom Ξ) (dom Ξ')).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).

Hint Resolve lt'_wf.

Lemma X_weaken_𝓥 T (Wf_T : wf_ty Ξ T) ξ₁ ξ₂ v₁ v₂ :
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (Ξ & Ξ') ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂.
Proof.
apply X_weaken_𝓥_aux ; auto.
Qed.

Lemma X_weaken_𝓜 σ ℓ (Wf_σ : wf_ms Ξ σ) (Wf_ℓ : wf_lbl Ξ ℓ) ξ₁ ξ₂ m₁ m₂ :
n ⊨ 𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ ⇔
    𝓜⟦ (Ξ & Ξ') ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂.
Proof.
apply X_weaken_𝓜_aux ; auto.
Qed.

Lemma X_weaken_𝓤 E (Wf_E : wf_eff Ξ E) ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ :
n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (Ξ & Ξ') ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂.
Proof.
apply X_weaken_𝓤_aux ; auto.
Qed.

Hint Resolve X_weaken_𝓥 X_weaken_𝓤.

Lemma X_weaken_𝓣 T (Wf_T : wf_ty Ξ T) E (Wf_E : wf_eff Ξ E) ξ₁ ξ₂ t₁ t₂ :
n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
    𝓣⟦ (Ξ & Ξ') ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
Qed.

End section_X_weaken.
