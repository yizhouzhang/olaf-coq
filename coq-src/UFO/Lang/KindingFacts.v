Require Import Lang.Syntax.
Require Import Lang.Bindings.
Require Import Lang.BindingsFacts.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Section section_sk_is_map.

Fixpoint sk_is_EP_map
EP EP' EV LV L (f : EP → EP')
(Σ : is EP EV LV L) :
sk_is Σ = sk_is (EP_map_is f Σ).
Proof.
destruct Σ ; simpl.
+ auto.
+ erewrite sk_is_EP_map ; reflexivity.
Qed.

Fixpoint sk_is_L_map
EP EV LV L L' (f : L → L')
(Σ : is EP EV LV L) :
sk_is Σ = sk_is (L_map_is f Σ).
Proof.
destruct Σ ; simpl.
+ auto.
+ erewrite sk_is_L_map ; reflexivity.
Qed.

Fixpoint sk_is_LV_map
EP EV LV LV' L (f : LV → LV')
(Σ : is EP EV LV L) :
sk_is Σ = sk_is (LV_map_is f Σ).
Proof.
destruct Σ ; simpl.
+ auto.
+ erewrite sk_is_LV_map ; reflexivity.
Qed.

Fixpoint sk_is_EV_map
EP EV EV' LV L (f : EV → EV')
(Σ : is EP EV LV L) :
sk_is Σ = sk_is (EV_map_is f Σ).
Proof.
destruct Σ ; simpl.
+ auto.
+ erewrite sk_is_EV_map ; reflexivity.
Qed.

End section_sk_is_map.


Fixpoint sk_is_EP_bind
EP EP' EV LV L (f : EP → eff EP' EV LV L)
(Σ : is EP EV LV L) :
sk_is Σ = sk_is (EP_bind_is f Σ).
Proof.
destruct Σ ; simpl.
+ auto.
+ erewrite sk_is_EP_bind ; reflexivity.
Qed.
