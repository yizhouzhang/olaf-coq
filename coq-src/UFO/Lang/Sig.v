Require Import Syntax.
Require Import Bindings.
Require Import KindingFacts.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

(** Computes the signature of a parameterized interface N *)
Fixpoint it_sig EP EV LV L
κ (N : it EP EV LV L κ) : { Σ : is EP EV LV L | sk_is Σ = κ }.
Proof.
destruct N as [ F | κ N E].
+ apply exist with (x :=
    EP_open_is (EV_open_is (LV_open_is (L_open_is (Signature F))))
  ).
  rewrite SignatureKind.
  rewrite <- sk_is_EP_map, <- sk_is_EV_map, <- sk_is_LV_map, <- sk_is_L_map.
  reflexivity.
+ destruct (it_sig _ _ _ _ _ N) as [ Σ P ].
  destruct Σ as [ | Σ₀ ] ; simpl in P ; [ discriminate | ]. 
  apply exist with (x := EP_subst_is E Σ₀).
  rewrite <- sk_is_EP_bind.
  injection P.
  intro H ; exact H.
Defined.

(** Computes the operation signature of a non-parameterized interface N *)
Definition it_msig EP EV LV L (N : it EP EV LV L 𝕄) : ms EP EV LV L.
Proof.
destruct (it_sig N) as [ Σ P ].
destruct Σ as [ σ |].
+ refine σ.
+ discriminate.
Defined.
