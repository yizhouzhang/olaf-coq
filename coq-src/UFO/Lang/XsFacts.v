Require Import UFO.Lang.Syntax.
Require Import UFO.Lang.Bindings.
Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Lang.Operational.
Require Import UFO.Lang.Xs.
Require Import UFO.Util.Subset.

Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Lemma Xs_eff_app EP EV LV L (E E' : eff EP EV LV L) :
Xs_eff (E ++ E') = Xs_eff E \u Xs_eff E'.
Proof.
induction E ; simpl.
+ rewrite union_empty_l ; auto.
+ rewrite IHE, union_assoc ; auto.
Qed.

Section section_Xs_map_and_bind.

Lemma
L_map_lid_Xs
L L' (f : L → L')
(ι : lid L) :
Xs_lid (L_map_lid f ι) = Xs_lid ι.
Proof.
destruct ι ; crush.
Qed.

Hint Rewrite L_map_lid_Xs.

Lemma
L_map_lbl_Xs
LV L L' (f : L → L')
(ℓ : lbl LV L) :
Xs_lbl (L_map_lbl f ℓ) = Xs_lbl ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite L_map_lbl_Xs.

Lemma
L_map_ef_Xs
EP EV LV L L' (f : L → L')
(e : ef EP EV LV L) :
Xs_ef (L_map_ef f e) = Xs_ef e.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite L_map_ef_Xs.

Lemma
L_map_eff_Xs
EP EV LV L L' (f : L → L')
(E : eff EP EV LV L) :
Xs_eff (L_map_eff f E) = Xs_eff E.
Proof.
induction E ; crush.
Qed.

Hint Rewrite L_map_eff_Xs.

Lemma
L_map_it_Xs
EP EV LV L L' (f : L → L')
κ (N : it EP EV LV L κ) :
Xs_it (L_map_it f N) = Xs_it N.
Proof.
induction N ; crush.
Qed.

Hint Rewrite L_map_it_Xs.

Fixpoint
L_map_ms_Xs
EP EV LV L L' (f : L → L')
(σ : ms EP EV LV L) :
Xs_ms (L_map_ms f σ) = Xs_ms σ
with
L_map_ty_Xs
EP EV LV L L' (f : L → L')
(T : ty EP EV LV L) :
Xs_ty (L_map_ty f T) = Xs_ty T
.
Proof.
+ destruct σ ; crush.
+ destruct T ; crush.
Qed.

Hint Rewrite L_map_ms_Xs.
Hint Rewrite L_map_ty_Xs.

Fixpoint
L_map_md_Xs
EV LV V L L' (f : L → L')
(m : md EV LV V L) :
Xs_md (L_map_md f m) = Xs_md m
with
L_map_ktx_Xs
EV LV V L L' (f : L → L')
(K : ktx EV LV V L) :
Xs_ktx (L_map_ktx f K) = Xs_ktx K
with
L_map_tm_Xs
EV LV V L L' (f : L → L')
(t : tm EV LV V L) :
Xs_tm (L_map_tm f t) = Xs_tm t
with
L_map_val_Xs
EV LV V L L' (f : L → L')
(v : val EV LV V L) :
Xs_val (L_map_val f v) = Xs_val v
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Hint Rewrite L_map_md_Xs.
Hint Rewrite L_map_ktx_Xs.
Hint Rewrite L_map_tm_Xs.
Hint Rewrite L_map_val_Xs.

Lemma
LV_map_lbl_Xs
LV L LV' (f : LV → LV')
(ℓ : lbl LV L) :
Xs_lbl (LV_map_lbl f ℓ) = Xs_lbl ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite LV_map_lbl_Xs.

Lemma
LV_map_ef_Xs
EP EV LV L LV' (f : LV → LV')
(e : ef EP EV LV L) :
Xs_ef (LV_map_ef f e) = Xs_ef e.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite LV_map_ef_Xs.

Lemma
LV_map_eff_Xs
EP EV LV L LV' (f : LV → LV')
(E : eff EP EV LV L) :
Xs_eff (LV_map_eff f E) = Xs_eff E.
Proof.
induction E ; crush.
Qed.

Hint Rewrite LV_map_eff_Xs.

Lemma
LV_map_it_Xs
EP EV LV L LV' (f : LV → LV')
κ (N : it EP EV LV L κ) :
Xs_it (LV_map_it f N) = Xs_it N.
Proof.
induction N ; crush.
Qed.

Hint Rewrite LV_map_it_Xs.

Fixpoint
LV_map_ms_Xs
EP EV LV L LV' (f : LV → LV')
(σ : ms EP EV LV L) :
Xs_ms (LV_map_ms f σ) = Xs_ms σ
with
LV_map_ty_Xs
EP EV LV L LV' (f : LV → LV')
(T : ty EP EV LV L) :
Xs_ty (LV_map_ty f T) = Xs_ty T
.
Proof.
+ destruct σ ; crush.
+ destruct T ; crush.
Qed.

Hint Rewrite LV_map_ms_Xs.
Hint Rewrite LV_map_ty_Xs.

Fixpoint
LV_map_md_Xs
EV LV V L LV' (f : LV → LV')
(m : md EV LV V L) :
Xs_md (LV_map_md f m) = Xs_md m
with
LV_map_ktx_Xs
EV LV V L LV' (f : LV → LV')
(K : ktx EV LV V L) :
Xs_ktx (LV_map_ktx f K) = Xs_ktx K
with
LV_map_tm_Xs
EV LV V L LV' (f : LV → LV')
(t : tm EV LV V L) :
Xs_tm (LV_map_tm f t) = Xs_tm t
with
LV_map_val_Xs
EV LV V L LV' (f : LV → LV')
(v : val EV LV V L) :
Xs_val (LV_map_val f v) = Xs_val v
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Hint Rewrite LV_map_md_Xs.
Hint Rewrite LV_map_ktx_Xs.
Hint Rewrite LV_map_tm_Xs.
Hint Rewrite LV_map_val_Xs.

Lemma
EV_map_ef_Xs
EP EV LV L EV' (f : EV → EV')
(e : ef EP EV LV L) :
Xs_ef (EV_map_ef f e) = Xs_ef e.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EV_map_ef_Xs.

Lemma
EV_map_eff_Xs
EP EV LV L EV' (f : EV → EV')
(E : eff EP EV LV L) :
Xs_eff (EV_map_eff f E) = Xs_eff E.
Proof.
induction E ; crush.
Qed.

Hint Rewrite EV_map_eff_Xs.

Lemma
EV_map_it_Xs
EP EV LV L EV' (f : EV → EV')
κ (N : it EP EV LV L κ) :
Xs_it (EV_map_it f N) = Xs_it N.
Proof.
induction N ; crush.
Qed.

Hint Rewrite EV_map_it_Xs.

Fixpoint
EV_map_ms_Xs
EP EV LV L EV' (f : EV → EV')
(σ : ms EP EV LV L) :
Xs_ms (EV_map_ms f σ) = Xs_ms σ
with
EV_map_ty_Xs
EP EV LV L EV' (f : EV → EV')
(T : ty EP EV LV L) :
Xs_ty (EV_map_ty f T) = Xs_ty T
.
Proof.
+ destruct σ ; crush.
+ destruct T ; crush.
Qed.

Hint Rewrite EV_map_ms_Xs.
Hint Rewrite EV_map_ty_Xs.

Fixpoint
EV_map_md_Xs
EV LV V L EV' (f : EV → EV')
(m : md EV LV V L) :
Xs_md (EV_map_md f m) = Xs_md m
with
EV_map_ktx_Xs
EV LV V L EV' (f : EV → EV')
(K : ktx EV LV V L) :
Xs_ktx (EV_map_ktx f K) = Xs_ktx K
with
EV_map_tm_Xs
EV LV V L EV' (f : EV → EV')
(t : tm EV LV V L) :
Xs_tm (EV_map_tm f t) = Xs_tm t
with
EV_map_val_Xs
EV LV V L EV' (f : EV → EV')
(v : val EV LV V L) :
Xs_val (EV_map_val f v) = Xs_val v
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Hint Rewrite EV_map_md_Xs.
Hint Rewrite EV_map_ktx_Xs.
Hint Rewrite EV_map_tm_Xs.
Hint Rewrite EV_map_val_Xs.

Fixpoint
V_map_md_Xs
EV LV V L V' (f : V → V')
(m : md EV LV V L) :
Xs_md (V_map_md f m) = Xs_md m
with
V_map_ktx_Xs
EV LV V L V' (f : V → V')
(K : ktx EV LV V L) :
Xs_ktx (V_map_ktx f K) = Xs_ktx K
with
V_map_tm_Xs
EV LV V L V' (f : V → V')
(t : tm EV LV V L) :
Xs_tm (V_map_tm f t) = Xs_tm t
with
V_map_val_Xs
EV LV V L V' (f : V → V')
(v : val EV LV V L) :
Xs_val (V_map_val f v) = Xs_val v
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Hint Rewrite V_map_md_Xs.
Hint Rewrite V_map_ktx_Xs.
Hint Rewrite V_map_tm_Xs.
Hint Rewrite V_map_val_Xs.

Hint Resolve subset_empty_l.
Hint Resolve subset_union_l subset_union_r.
Hint Resolve subset_refl.

Lemma
L_bind_lid_Xs
L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(ι : lid L) :
Xs_lid (L_bind_lid f ι) \c Xs_lid ι \u B.
Proof.
destruct ι ; simpl ; auto.
Qed.

Lemma
L_bind_lbl_Xs
LV L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(ℓ : lbl LV L) :
Xs_lbl (L_bind_lbl f ℓ) \c Xs_lbl ℓ \u B.
Proof.
destruct ℓ ; simpl.
+ auto.
+ eapply subset_trans ; [ apply L_bind_lid_Xs ; auto | auto ].
Qed.

Lemma
L_bind_ef_Xs
EV LV L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(e : ef ∅ EV LV L) :
Xs_ef (L_bind_ef f e) \c Xs_ef e \u B.
Proof.
destruct e ; simpl.
+ auto.
+ auto.
+ eapply subset_trans ; [ apply L_bind_lbl_Xs ; auto | auto ].
Qed.

Lemma
L_bind_eff_Xs
EV LV L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(E : eff ∅ EV LV L) :
Xs_eff (L_bind_eff f E) \c Xs_eff E \u B.
Proof.
induction E ; simpl.
+ auto.
+ apply union_subset.
  - eapply subset_trans ; [ apply L_bind_ef_Xs ; auto | ].
    auto using union_subset.
  - rewrite <- union_assoc ; auto.
Qed.

Fixpoint
L_bind_it_Xs
EV LV L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
κ (N : it ∅ EV LV L κ) :
Xs_it (L_bind_it f N) \c Xs_it N \u B.
Proof.
destruct N as [ | N E ] ; simpl.
+ auto.
+ apply union_subset.
  - eapply subset_trans ; [ apply L_bind_it_Xs ; auto | ].
    auto using union_subset.
  - eapply subset_trans ; [ apply L_bind_eff_Xs ; auto | ].
    auto using union_subset.
Qed.

Fixpoint
L_bind_ms_Xs
EV LV L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(σ : ms ∅ EV LV L) :
Xs_ms (L_bind_ms f σ) \c Xs_ms σ \u B
with
L_bind_ty_Xs
EV LV L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(T : ty ∅ EV LV L) :
Xs_ty (L_bind_ty f T) \c Xs_ty T \u B
.
Proof.
+ destruct σ ; simpl.
  - eapply subset_trans ; [ apply L_bind_ms_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_ms_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
    * eapply subset_trans ; [ apply L_bind_ms_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
    * eapply subset_trans ; [ apply L_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
+ destruct T ; simpl.
  - auto.
  - repeat apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_it_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_lbl_Xs with (B := B) ; auto | auto ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ms_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_lbl_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
Qed.

Fixpoint
L_bind_md_Xs
EV LV V L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(m : md EV LV V L) :
Xs_md (L_bind_md f m) \c Xs_md m \u B
with
L_bind_ktx_Xs
EV LV V L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(K : ktx EV LV V L) :
Xs_ktx (L_bind_ktx f K) \c Xs_ktx K \u B
with
L_bind_val_Xs
EV LV V L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(v : val EV LV V L) :
Xs_val (L_bind_val f v) \c Xs_val v \u B
with
L_bind_tm_Xs
EV LV V L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(t : tm EV LV V L) :
Xs_tm (L_bind_tm f t) \c Xs_tm t \u B
.
Proof.
+ destruct m ; simpl.
  - eapply subset_trans ; [ apply L_bind_md_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_md_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_md_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
+ destruct K ; simpl.
  - auto.
  - auto.
  - auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_lbl_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_val_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
+ destruct v ; simpl.
  - auto.
  - auto.
  - eapply subset_trans ; [ apply L_bind_ktx_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_md_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_lid_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - eapply union_subset. 
    * eapply subset_trans ; [ apply L_bind_md_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_lid_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
+ destruct t ; simpl.
  - eapply subset_trans ; [ apply L_bind_val_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_lbl_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
Qed.

Lemma
LV_bind_lbl_Xs
LV L LV'
B (f : LV → lbl LV' L) (Q : ∀ x, Xs_lbl (f x) \c B)
(ℓ : lbl LV L) :
Xs_lbl (LV_bind_lbl f ℓ) \c Xs_lbl ℓ \u B.
Proof.
destruct ℓ ; simpl ; auto.
Qed.

Lemma
LV_bind_ef_Xs
EV LV L LV'
B (f : LV → lbl LV' L) (Q : ∀ x, Xs_lbl (f x) \c B)
(e : ef ∅ EV LV L) :
Xs_ef (LV_bind_ef f e) \c Xs_ef e \u B.
Proof.
destruct e ; simpl.
+ auto.
+ auto.
+ eapply subset_trans ; [ apply LV_bind_lbl_Xs ; auto | auto ].
Qed.

Lemma
LV_bind_eff_Xs
EV LV L LV'
B (f : LV → lbl LV' L) (Q : ∀ x, Xs_lbl (f x) \c B)
(E : eff ∅ EV LV L) :
Xs_eff (LV_bind_eff f E) \c Xs_eff E \u B.
Proof.
induction E ; simpl.
+ auto.
+ apply union_subset.
  - eapply subset_trans ; [ apply LV_bind_ef_Xs ; auto | ].
    auto using union_subset.
  - rewrite <- union_assoc ; auto.
Qed.

Fixpoint
LV_bind_it_Xs
EV LV L LV'
B (f : LV → lbl LV' L) (Q : ∀ x, Xs_lbl (f x) \c B)
κ (N : it ∅ EV LV L κ) :
Xs_it (LV_bind_it f N) \c Xs_it N \u B.
Proof.
destruct N as [ | N E ]; simpl.
+ auto.
+ apply union_subset.
  - eapply subset_trans ; [ apply LV_bind_it_Xs ; auto | ].
    auto using union_subset.
  - eapply subset_trans ; [ apply LV_bind_eff_Xs ; auto | ].
    auto using union_subset.
Qed.

Fixpoint
LV_bind_ms_Xs
EV LV L LV'
B (f : LV → lbl LV' L) (Q : ∀ x, Xs_lbl (f x) \c B)
(σ : ms ∅ EV LV L) :
Xs_ms (LV_bind_ms f σ) \c Xs_ms σ \u B
with
LV_bind_ty_Xs
EV LV L LV'
B (f : LV → lbl LV' L) (Q : ∀ x, Xs_lbl (f x) \c B)
(T : ty ∅ EV LV L) :
Xs_ty (LV_bind_ty f T) \c Xs_ty T \u B
.
Proof.
+ destruct σ ; simpl.
  - eapply subset_trans ; [ apply LV_bind_ms_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply LV_bind_ms_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
    * eapply subset_trans ; [ apply LV_bind_ms_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
    * eapply subset_trans ; [ apply LV_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
+ destruct T ; simpl.
  - auto.
  - repeat apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_it_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_lbl_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ms_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_lbl_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
Qed.

Fixpoint
LV_bind_md_Xs
EV LV V L LV'
B (f : LV → lbl LV' L) (Q : ∀ x, Xs_lbl (f x) \c B)
(m : md EV LV V L) :
Xs_md (LV_bind_md f m) \c Xs_md m \u B
with
LV_bind_ktx_Xs
EV LV V L LV'
B (f : LV → lbl LV' L) (Q : ∀ x, Xs_lbl (f x) \c B)
(K : ktx EV LV V L) :
Xs_ktx (LV_bind_ktx f K) \c Xs_ktx K \u B
with
LV_bind_val_Xs
EV LV V L LV'
B (f : LV → lbl LV' L) (Q : ∀ x, Xs_lbl (f x) \c B)
(v : val EV LV V L) :
Xs_val (LV_bind_val f v) \c Xs_val v \u B
with
LV_bind_tm_Xs
EV LV V L LV'
B (f : LV → lbl LV' L) (Q : ∀ x, Xs_lbl (f x) \c B)
(t : tm EV LV V L) :
Xs_tm (LV_bind_tm f t) \c Xs_tm t \u B
.
Proof.
+ destruct m ; simpl.
  - eapply subset_trans ; [ apply LV_bind_md_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply LV_bind_md_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply LV_bind_md_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | auto ].
+ destruct K ; simpl.
  - auto.
  - auto.
  - auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_lbl_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_val_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
+ destruct v ; simpl.
  - auto.
  - auto.
  - eapply subset_trans ; [ apply LV_bind_ktx_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_md_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_md_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
+ destruct t ; simpl.
  - eapply subset_trans ; [ apply LV_bind_val_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_lbl_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply LV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
Qed.

Lemma
EV_bind_ef_Xs
EV LV L EV'
B (f : EV → eff ∅ EV' LV L) (Q : ∀ x, Xs_eff (f x) \c B)
e :
Xs_eff (EV_bind_ef f e) \c Xs_ef e \u B.
Proof.
destruct e ; simpl.
+ auto.
+ auto.
+ apply union_subset ; auto.
Qed.

Lemma
EV_bind_eff_Xs
EV LV L EV'
B (f : EV → eff ∅ EV' LV L) (Q : ∀ x, Xs_eff (f x) \c B)
E :
Xs_eff (EV_bind_eff f E) \c Xs_eff E \u B.
Proof.
induction E ; simpl.
+ auto.
+ rewrite Xs_eff_app.
  apply union_subset.
  - eapply subset_trans ; [ apply EV_bind_ef_Xs ; auto | ].
    auto using union_subset.
  - rewrite <- union_assoc ; auto.
Qed.

Fixpoint
EV_bind_it_Xs
EV LV L EV'
B (f : EV → eff ∅ EV' LV L) (Q : ∀ x, Xs_eff (f x) \c B)
κ (N : it ∅ EV LV L κ) :
Xs_it (EV_bind_it f N) \c Xs_it N \u B.
Proof.
destruct N as [ | N E ] ; simpl.
+ auto.
+ apply union_subset.
  - eapply subset_trans ; [ apply EV_bind_it_Xs ; auto | ].
    auto using union_subset.
  - eapply subset_trans ; [ apply EV_bind_eff_Xs ; auto | ].
    auto using union_subset.
Qed.

Fixpoint
EV_bind_ms_Xs
EV LV L EV'
B (f : EV → eff ∅ EV' LV L) (Q : ∀ x, Xs_eff (f x) \c B)
σ :
Xs_ms (EV_bind_ms f σ) \c Xs_ms σ \u B
with
EV_bind_ty_Xs
EV LV L EV'
B (f : EV → eff ∅ EV' LV L) (Q : ∀ x, Xs_eff (f x) \c B)
T :
Xs_ty (EV_bind_ty f T) \c Xs_ty T \u B
.
Proof.
+ destruct σ ; simpl.
  - eapply subset_trans ; [ apply EV_bind_ms_Xs with (B := B) | auto ].
    intro α ; destruct α ; simpl.
    * rewrite union_empty_l ; auto.
    * rewrite EV_map_eff_Xs ; auto.
  - eapply subset_trans ; [ apply EV_bind_ms_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
    * eapply subset_trans ; [ apply EV_bind_ms_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
    * eapply subset_trans ; [ apply EV_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto using union_assoc.
+ destruct T ; simpl.
  - auto.
  - repeat apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_ty_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_it_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ms_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
Qed.

Fixpoint
EV_bind_md_Xs
EV LV V L EV'
B (f : EV → eff ∅ EV' LV L) (Q : ∀ x, Xs_eff (f x) \c B)
(m : md EV LV V L) :
Xs_md (EV_bind_md f m) \c Xs_md m \u B
with
EV_bind_ktx_Xs
EV LV V L EV'
B (f : EV → eff ∅ EV' LV L) (Q : ∀ x, Xs_eff (f x) \c B)
(K : ktx EV LV V L) :
Xs_ktx (EV_bind_ktx f K) \c Xs_ktx K \u B
with
EV_bind_val_Xs
EV LV V L EV'
B (f : EV → eff ∅ EV' LV L) (Q : ∀ x, Xs_eff (f x) \c B)
(v : val EV LV V L) :
Xs_val (EV_bind_val f v) \c Xs_val v \u B
with
EV_bind_tm_Xs
EV LV V L EV'
B (f : EV → eff ∅ EV' LV L) (Q : ∀ x, Xs_eff (f x) \c B)
(t : tm EV LV V L) :
Xs_tm (EV_bind_tm f t) \c Xs_tm t \u B
.
Proof.
+ destruct m ; simpl.
  - eapply subset_trans ; [ apply EV_bind_md_Xs with (B := B) | auto ].
    intro α ; destruct α ; simpl.
    * rewrite union_empty_l ; auto.
    * rewrite EV_map_eff_Xs ; auto.
  - eapply subset_trans ; [ apply EV_bind_md_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_md_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
+ destruct K ; simpl.
  - auto.
  - auto.
  - auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ktx_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_val_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
+ destruct v ; simpl.
  - auto.
  - auto.
  - eapply subset_trans ; [ apply EV_bind_ktx_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_md_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_md_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
+ destruct t ; simpl.
  - eapply subset_trans ; [ apply EV_bind_val_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_eff_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | ].
      apply union_subset ; auto.
Qed.

Fixpoint
V_bind_md_Xs
EV LV V L V'
B (f : V → val EV LV V' L) (Q : ∀ x, Xs_val (f x) \c B)
m :
Xs_md (V_bind_md f m) \c Xs_md m \u B
with
V_bind_ktx_Xs
EV LV V L V'
B (f : V → val EV LV V' L) (Q : ∀ x, Xs_val (f x) \c B)
K :
Xs_ktx (V_bind_ktx f K) \c Xs_ktx K \u B
with
V_bind_val_Xs
EV LV V L V'
B (f : V → val EV LV V' L) (Q : ∀ x, Xs_val (f x) \c B)
v :
Xs_val (V_bind_val f v) \c Xs_val v \u B
with
V_bind_tm_Xs
EV LV V L V'
B (f : V → val EV LV V' L) (Q : ∀ x, Xs_val (f x) \c B)
t :
Xs_tm (V_bind_tm f t) \c Xs_tm t \u B
.
Proof.
+ destruct m ; simpl ; auto.
+ destruct K ; simpl.
  - auto.
  - auto.
  - auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_ktx K)), <- union_assoc ; auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_ktx K)), <- union_assoc ; auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_ktx K)), <- union_assoc ; auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_ktx K)), <- union_assoc ; auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_ktx K)), <- union_assoc ; auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_ktx K)), <- union_assoc ; auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_ktx K)), <- union_assoc ; auto.
+ destruct v ; simpl.
  - auto.
  - auto.
  - auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_md m)), <- union_assoc ; auto.
  - apply union_subset.
    * eapply subset_trans.
      { apply V_bind_md_Xs with (B := B) ; crush. }
      { auto using union_subset, union_assoc. }
    * rewrite (union_comm (Xs_md m)), <- union_assoc ; auto.
+ destruct t ; simpl.
  - auto.
  - auto.
  - auto.
  - auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_tm t)), <- union_assoc ; auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * eapply subset_trans.
      { apply V_bind_tm_Xs with (B := B) ; crush. }
      { rewrite <- union_assoc ; auto. }
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * eapply subset_trans ; auto using union_subset, union_assoc.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_tm t)), <- union_assoc ; auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * rewrite (union_comm (Xs_tm t)), <- union_assoc ; auto.
  - apply union_subset.
    * eapply subset_trans ; auto using union_subset, union_assoc.
    * eapply subset_trans ; auto using union_subset, union_assoc.
Qed.

End section_Xs_map_and_bind.

Section section_Xs_ktx_plug.

Hint Rewrite union_empty_l.

Lemma Xs_ktx_plug EV LV V L (K : ktx EV LV V L) t :
Xs_tm (ktx_plug K t) = Xs_ktx K \u Xs_tm t.
Proof.
induction K ; simpl.
+ crush.
+ crush.
+ crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite union_assoc, (union_comm _ (Xs_tm K)).
  crush.
Qed.

End section_Xs_ktx_plug.
