Require Import Syntax.
Require Import Bindings.
Require Import BindingsFacts.
Require Import Sig.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Fixpoint EV_map_it_sig
EP EV EV' LV L (f : EV → EV')
κ (N : it EP EV LV L κ)
Σ P Σ' P'
(H : it_sig N = exist _ Σ P)
(H' : it_sig (EV_map_it f N) = exist _ Σ' P')
{struct N} :
EV_map_is f Σ = Σ'.
Proof.
destruct N as [ F | κ N E ].
+ inversion H ; inversion H'.
  rewrite <- EP_EV_map_is.
  erewrite EV_map_map_is ; crush.
+ simpl EV_map_it in H'.
  destruct (it_sig N) as [ Σ₀ P₀ ] eqn:H₀.
  destruct (it_sig (EV_map_it f N)) as [ Σ₀' P₀' ] eqn:H₀'.
  assert (EV_map_is f Σ₀ = Σ₀') as HΣ₀Σ₀'.
  { eapply EV_map_it_sig with (N := N) ; eassumption. }

  destruct Σ₀ as [ | Σ₀ ] ; simpl in P₀ ; inversion P₀.
  assert (HΣ : Σ = EP_subst_is E Σ₀).
  {
    clear - H H₀.
    simpl in H ; rewrite H₀ in H.
    injection H ; auto.
  }
  destruct Σ₀' as [ | Σ₀'] ; simpl in P₀' ; inversion P₀'.
  assert (HΣ' : Σ' = EP_subst_is (EV_map_eff f E) Σ₀').
  {
    clear - H' H₀'.
    simpl in H' ; rewrite H₀' in H'.
    injection H' ; auto.
  }

  clear - HΣ HΣ' HΣ₀Σ₀'.
  simpl in HΣ₀Σ₀'.
  inversion HΣ₀Σ₀' ; subst Σ₀'.
  rewrite HΣ, HΣ' ; simpl.
  erewrite EP_bind_EV_map_is ; crush.
Qed.

Lemma EV_map_it_msig
EP EV EV' LV L (f : EV → EV')
(N : it EP EV LV L 𝕄) :
EV_map_ms f (it_msig N) = it_msig (EV_map_it f N).
Proof.
destruct (it_sig N) as [ Σ P ] eqn:H.
destruct (it_sig (EV_map_it f N)) as [ Σ' P' ] eqn:H'.
assert (Q : EV_map_is f Σ = Σ').
{ eapply EV_map_it_sig ; eassumption. }
simpl in Q.

destruct Σ as [ σ | ] ; [ | discriminate ].
destruct Σ' as [ σ' | ] ; [ | discriminate ].

unfold it_msig.
rewrite H, H'.
injection Q ; auto.
Qed.

Fixpoint LV_map_it_sig
EP EV LV LV' L (f : LV → LV')
κ (N : it EP EV LV L κ)
Σ P Σ' P'
(H : it_sig N = exist _ Σ P)
(H' : it_sig (LV_map_it f N) = exist _ Σ' P')
{struct N} :
LV_map_is f Σ = Σ'.
Proof.
destruct N as [ F | κ N E ].
+ inversion H ; inversion H'.
  rewrite <- EP_LV_map_is.
  rewrite <- EV_LV_map_is.
  erewrite LV_map_map_is ; crush.
+ simpl LV_map_it in H'.
  destruct (it_sig N) as [ Σ₀ P₀ ] eqn:H₀.
  destruct (it_sig (LV_map_it f N)) as [ Σ₀' P₀' ] eqn:H₀'.
  assert (LV_map_is f Σ₀ = Σ₀') as HΣ₀Σ₀'.
  {
    eapply LV_map_it_sig with (N := N).
    + apply H₀.
    + apply H₀'. 
  }

  destruct Σ₀ as [ | Σ₀ ] ; simpl in P₀ ; inversion P₀.
  assert (HΣ : Σ = EP_subst_is E Σ₀).
  {
    clear - H H₀.
    simpl in H ; rewrite H₀ in H.
    injection H ; auto.
  }
  destruct Σ₀' as [ | Σ₀'] ; simpl in P₀' ; inversion P₀'.
  assert (HΣ' : Σ' = EP_subst_is (LV_map_eff f E) Σ₀').
  {
    clear - H' H₀'.
    simpl in H' ; rewrite H₀' in H'.
    injection H' ; auto.
  }

  clear - HΣ HΣ' HΣ₀Σ₀'.
  simpl in HΣ₀Σ₀'.
  inversion HΣ₀Σ₀' ; subst Σ₀'.
  rewrite HΣ, HΣ' ; simpl.
  erewrite EP_bind_LV_map_is ; crush.
Qed.

Lemma LV_map_it_msig
EP EV LV LV' L (f : LV → LV')
(N : it EP EV LV L 𝕄) :
LV_map_ms f (it_msig N) = it_msig (LV_map_it f N).
Proof.
destruct (it_sig N) as [ Σ P ] eqn:H.
destruct (it_sig (LV_map_it f N)) as [ Σ' P' ] eqn:H'.
assert (Q : LV_map_is f Σ = Σ').
{ eapply LV_map_it_sig ; eassumption. }
simpl in Q.

destruct Σ as [ σ | ] ; [ | discriminate ].
destruct Σ' as [ σ' | ] ; [ | discriminate ].

unfold it_msig.
rewrite H, H'.
injection Q ; auto.
Qed.

Fixpoint EV_bind_it_sig
EP EV EV' LV L (f : EV → eff EP EV' LV L)
κ (N : it EP EV LV L κ)
Σ P Σ' P'
(H : it_sig N = exist _ Σ P)
(H' : it_sig (EV_bind_it f N) = exist _ Σ' P')
{struct N} :
EV_bind_is f Σ = Σ'.
Proof.
destruct N as [ F | κ N E ].
+ inversion H ; inversion H'.
  generalize (LV_open_is (L_open_is (Signature F)) : is ∅ ∅ LV L).
  intro Σ₀.
  repeat rewrite EP_EV_map_is.
  erewrite EV_bind_map_is, EV_bind_is_id ; crush.
+ simpl EV_bind_it in H'.
  destruct (it_sig N) as [ Σ₀ P₀ ] eqn:H₀.
  destruct (it_sig (EV_bind_it f N)) as [ Σ₀' P₀' ] eqn:H₀'.
  assert (EV_bind_is f Σ₀ = Σ₀') as HΣ₀Σ₀'.
  { eapply EV_bind_it_sig with (N := N) ; eassumption. }

  destruct Σ₀ as [ | Σ₀ ] ; simpl in P₀ ; inversion P₀.
  assert (HΣ : Σ = EP_subst_is E Σ₀).
  {
    clear - H H₀.
    simpl in H ; rewrite H₀ in H.
    injection H ; auto.
  }
  destruct Σ₀' as [ | Σ₀'] ; simpl in P₀' ; inversion P₀'.
  assert (HΣ' : Σ' = EP_subst_is (EV_bind_eff f E) Σ₀').
  {
    clear - H' H₀'.
    simpl in H' ; rewrite H₀' in H'.
    injection H' ; auto.
  }

  clear - HΣ HΣ' HΣ₀Σ₀'.
  simpl in HΣ₀Σ₀'.
  inversion HΣ₀Σ₀' ; subst Σ₀'.
  rewrite HΣ, HΣ' ; simpl.
  erewrite EP_EV_bind_is ; try reflexivity.
  - intro ; unfold compose.
    erewrite EP_bind_map_eff, EP_map_eff_id, EP_bind_eff_id ; reflexivity.
  - destruct x ; simpl ; reflexivity.
Qed.

Lemma EV_bind_it_msig
EP EV EV' LV L (f : EV → eff EP EV' LV L)
(N : it EP EV LV L 𝕄) :
EV_bind_ms f (it_msig N) = it_msig (EV_bind_it f N).
Proof.
destruct (it_sig N) as [ Σ P ] eqn:H.
destruct (it_sig (EV_bind_it f N)) as [ Σ' P' ] eqn:H'.
assert (Q : EV_bind_is f Σ = Σ').
{ eapply EV_bind_it_sig ; eassumption. }
simpl in Q.

destruct Σ as [ σ | ] ; [ | discriminate ].
destruct Σ' as [ σ' | ] ; [ | discriminate ].

unfold it_msig.
rewrite H, H'.
injection Q ; auto.
Qed.

Fixpoint LV_bind_it_sig
EP EV LV LV' L (f : LV → lbl LV' L)
κ (N : it EP EV LV L κ)
Σ P Σ' P'
(H : it_sig N = exist _ Σ P)
(H' : it_sig (LV_bind_it f N) = exist _ Σ' P')
{struct N} :
LV_bind_is f Σ = Σ'.
Proof.
destruct N as [ F | κ N E ].
+ inversion H ; inversion H'.
  repeat rewrite EV_LV_map_is.
  repeat rewrite EP_LV_map_is.
  erewrite LV_bind_map_is, LV_bind_is_id ; crush.
+ simpl LV_bind_it in H'.
  destruct (it_sig N) as [ Σ₀ P₀ ] eqn:H₀.
  destruct (it_sig (LV_bind_it f N)) as [ Σ₀' P₀' ] eqn:H₀'.
  assert (LV_bind_is f Σ₀ = Σ₀') as HΣ₀Σ₀'.
  { eapply LV_bind_it_sig with (N := N) ; eassumption. }

  destruct Σ₀ as [ | Σ₀ ] ; simpl in P₀ ; inversion P₀.
  assert (HΣ : Σ = EP_subst_is E Σ₀).
  {
    clear - H H₀.
    simpl in H ; rewrite H₀ in H.
    injection H ; auto.
  }
  destruct Σ₀' as [ | Σ₀'] ; simpl in P₀' ; inversion P₀'.
  assert (HΣ' : Σ' = EP_subst_is (LV_bind_eff f E) Σ₀').
  {
    clear - H' H₀'.
    simpl in H' ; rewrite H₀' in H'.
    injection H' ; auto.
  }

  clear - HΣ HΣ' HΣ₀Σ₀'.
  simpl in HΣ₀Σ₀'.
  inversion HΣ₀Σ₀' ; subst Σ₀'.
  rewrite HΣ, HΣ' ; simpl.
  erewrite EP_LV_bind_is ; try reflexivity.
  destruct x ; simpl ; reflexivity.
Qed.

Lemma LV_bind_it_msig
EP EV LV LV' L (f : LV → lbl LV' L)
(N : it EP EV LV L 𝕄) :
LV_bind_ms f (it_msig N) = it_msig (LV_bind_it f N).
Proof.
destruct (it_sig N) as [ Σ P ] eqn:H.
destruct (it_sig (LV_bind_it f N)) as [ Σ' P' ] eqn:H'.
assert (Q : LV_bind_is f Σ = Σ').
{ eapply LV_bind_it_sig ; eassumption. }
simpl in Q.

destruct Σ as [ σ | ] ; [ | discriminate ].
destruct Σ' as [ σ' | ] ; [ | discriminate ].

unfold it_msig.
rewrite H, H'.
injection Q ; auto.
Qed.

Fixpoint L_bind_it_sig
EP EV LV L L' (f : L → lid L')
κ (N : it EP EV LV L κ)
Σ P Σ' P'
(H : it_sig N = exist _ Σ P)
(H' : it_sig (L_bind_it f N) = exist _ Σ' P')
{struct N} :
L_bind_is f Σ = Σ'.
Proof.
destruct N as [ F | κ N E ].
+ inversion H ; inversion H'.
  repeat rewrite LV_L_map_is.
  repeat rewrite EV_L_map_is.
  repeat rewrite EP_L_map_is.
  erewrite L_bind_map_is, L_bind_is_id ; crush.
+ simpl L_bind_it in H'.
  destruct (it_sig N) as [ Σ₀ P₀ ] eqn:H₀.
  destruct (it_sig (L_bind_it f N)) as [ Σ₀' P₀' ] eqn:H₀'.
  assert (L_bind_is f Σ₀ = Σ₀') as HΣ₀Σ₀'.
  { eapply L_bind_it_sig with (N := N) ; eassumption. }

  destruct Σ₀ as [ | Σ₀ ] ; simpl in P₀ ; inversion P₀.
  assert (HΣ : Σ = EP_subst_is E Σ₀).
  {
    clear - H H₀.
    simpl in H ; rewrite H₀ in H.
    injection H ; auto.
  }
  destruct Σ₀' as [ | Σ₀'] ; simpl in P₀' ; inversion P₀'.
  assert (HΣ' : Σ' = EP_subst_is (L_bind_eff f E) Σ₀').
  {
    clear - H' H₀'.
    simpl in H' ; rewrite H₀' in H'.
    injection H' ; auto.
  }

  clear - HΣ HΣ' HΣ₀Σ₀'.
  simpl in HΣ₀Σ₀'.
  inversion HΣ₀Σ₀' ; subst Σ₀'.
  rewrite HΣ, HΣ' ; simpl.
  erewrite EP_L_bind_is ; try reflexivity.
  destruct x ; simpl ; reflexivity.
Qed.

Lemma L_bind_it_msig
EP EV LV L L' (f : L → lid L')
(N : it EP EV LV L 𝕄) :
L_bind_ms f (it_msig N) = it_msig (L_bind_it f N).
Proof.
destruct (it_sig N) as [ Σ P ] eqn:H.
destruct (it_sig (L_bind_it f N)) as [ Σ' P' ] eqn:H'.
assert (Q : L_bind_is f Σ = Σ').
{ eapply L_bind_it_sig ; eassumption. }
simpl in Q.

destruct Σ as [ σ | ] ; [ | discriminate ].
destruct Σ' as [ σ' | ] ; [ | discriminate ].

unfold it_msig.
rewrite H, H'.
injection Q ; auto.
Qed.