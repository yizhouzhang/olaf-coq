Require Import UFO.Lang.Syntax.
Require Import UFO.Lang.Bindings.
Require Import UFO.Lang.Operational.
Require Import UFO.Lang.Sim.
Require Import UFO.Lang.Xs.
Require Import UFO.Util.Postfix.
Require Import UFO.Util.FromList.
Require Import UFO.Util.Subset.
Require TLC.LibList.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Local Hint Constructors lid_sim lbl_sim ef_sim eff_sim it_sim ty_sim ms_sim.
Local Hint Constructors md_sim ktx_sim val_sim tm_sim.

(** [xx_sym] is reflexivie *)
Section section_sim_refl.

Import TLC.LibList.

Hint Rewrite in_singleton.
Hint Extern 1 => match goal with
| [ H : _ \u _ \c _ |- _ ] => apply union_subset_inv in H ; destruct H
| [ H : \{ ?a } \c ?A |- _ ] => assert (a ∈ A) ; [ specialize (H a) ; crush | ]
end.

Lemma var_sim_refl ξ X (H : X ∈ from_list ξ) :
var_sim ξ ξ X X.
Proof.
rewrite from_list_spec in H.
apply mem_Nth in H.
destruct H as [n ?].
exists n ; crush.
Qed.

Hint Resolve var_sim_refl.

Lemma lid_sim_refl L ξ (ι : lid L) (H : Xs_lid ι \c from_list ξ) :
lid_sim ξ ξ ι ι.
Proof.
destruct ι ; crush.
Qed.

Hint Resolve lid_sim_refl.

Lemma
lbl_sim_refl LV L ξ (ℓ : lbl LV L) (H : Xs_lbl ℓ \c from_list ξ) :
lbl_sim ξ ξ ℓ ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Hint Resolve lbl_sim_refl.

Lemma
ef_sim_refl EP EV LV L ξ (e : ef EP EV LV L) (H : Xs_ef e \c from_list ξ) :
ef_sim ξ ξ e e.
Proof.
destruct e ; crush.
Qed.

Hint Resolve ef_sim_refl.
Hint Extern 1 => match goal with
| [ H : _ \u _ \c _ |- _ ] => apply union_subset_inv in H ; destruct H
end.

Lemma
eff_sim_refl
EP EV LV L ξ (E : eff EP EV LV L) (H : Xs_eff E \c from_list ξ) :
eff_sim ξ ξ E E.
Proof.
induction E ; crush.
Qed.

Hint Resolve eff_sim_refl.

Lemma
it_sim_refl
EP EV LV L ξ κ (N : it EP EV LV L κ) (H : Xs_it N \c from_list ξ) :
it_sim ξ ξ N N.
Proof.
induction N ; crush.
Qed.

Hint Resolve it_sim_refl.

Fixpoint
ms_sim_refl
EP EV LV L ξ (σ : ms EP EV LV L) (H : Xs_ms σ \c from_list ξ) {struct σ} :
ms_sim ξ ξ σ σ
with
ty_sim_refl
EP EV LV L ξ (T : ty EP EV LV L) (H : Xs_ty T \c from_list ξ) {struct T} :
ty_sim ξ ξ T T
.
Proof.
+ destruct σ ; constructor ; crush.
+ destruct T ; constructor ; crush.
Qed.

Hint Resolve ms_sim_refl.
Hint Resolve ty_sim_refl.

Fixpoint
md_sim_refl
EV LV V L ξ (m : md EV LV V L) (H : Xs_md m \c from_list ξ) {struct m} :
md_sim ξ ξ m m
with
ktx_sim_refl
EV LV V L ξ (K : ktx EV LV V L) (H : Xs_ktx K \c from_list ξ) {struct K} :
ktx_sim ξ ξ K K
with
val_sim_refl
EV LV V L ξ (v : val EV LV V L) (H : Xs_val v \c from_list ξ) {struct v} :
val_sim ξ ξ v v
with
tm_sim_refl
EV LV V L ξ (t : tm EV LV V L) (H : Xs_tm t \c from_list ξ) {struct t} :
tm_sim ξ ξ t t
.
Proof.
+ destruct m ; constructor ; crush.
+ destruct K ; constructor ; crush.
+ destruct v ; constructor ; crush.
+ destruct t ; constructor ; crush.
Qed.

End section_sim_refl.


(** [xx_sym] is symmetric *)
Section section_sim_sym.

Lemma var_sim_sym ξ ξ' (X X' : var) (H : var_sim ξ ξ' X X') :
var_sim ξ' ξ X' X.
Proof.
destruct H as [n ?].
exists n ; crush.
Qed.

Hint Resolve var_sim_sym.

Lemma lid_sim_sym L ξ ξ' (ι ι' : lid L) (H : lid_sim ξ ξ' ι ι') :
lid_sim ξ' ξ ι' ι.
Proof.
destruct H ; crush.
Qed.

Hint Resolve lid_sim_sym.

Lemma
lbl_sim_sym LV L ξ ξ' (ℓ ℓ' : lbl LV L) (H : lbl_sim ξ ξ' ℓ ℓ') :
lbl_sim ξ' ξ ℓ' ℓ.
Proof.
destruct H ; crush.
Qed.

Hint Resolve lbl_sim_sym.

Lemma
ef_sim_sym EP EV LV L ξ ξ' (e e' : ef EP EV LV L) (H : ef_sim ξ ξ' e e') :
ef_sim ξ' ξ e' e.
Proof.
destruct H ; crush.
Qed.

Hint Resolve ef_sim_sym.

Lemma
eff_sim_sym
EP EV LV L ξ ξ' (E E' : eff EP EV LV L) (H : eff_sim ξ ξ' E E') :
eff_sim ξ' ξ E' E.
Proof.
induction H ; crush.
Qed.

Hint Resolve eff_sim_sym.

Lemma
it_sim_sym
EP EV LV L ξ ξ' κ (N N' : it EP EV LV L κ) (H : it_sim ξ ξ' N N') :
it_sim ξ' ξ N' N.
Proof.
induction H ; crush.
Qed.

Hint Resolve it_sim_sym.

Fixpoint
ms_sim_sym
EP EV LV L ξ ξ' (σ σ' : ms EP EV LV L) (H : ms_sim ξ ξ' σ σ') :
ms_sim ξ' ξ σ' σ
with
ty_sim_sym
EP EV LV L ξ ξ' (T T' : ty EP EV LV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ' ξ T' T
.
Proof.
+ destruct H ; constructor ; crush.
+ destruct H ; constructor ; crush.
Qed.

Hint Resolve ms_sim_sym.
Hint Resolve ty_sim_sym.

Fixpoint
md_sim_sym
EV LV V L ξ ξ' (m m' : md EV LV V L) (H : md_sim ξ ξ' m m') :
md_sim ξ' ξ m' m
with
ktx_sim_sym
EV LV V L ξ ξ' (K K' : ktx EV LV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ' ξ K' K
with
val_sim_sym
EV LV V L ξ ξ' (v v' : val EV LV V L) (H : val_sim ξ ξ' v v') :
val_sim ξ' ξ v' v
with
tm_sim_sym
EV LV V L ξ ξ' (t t' : tm EV LV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ' ξ t' t
.
Proof.
+ destruct H ; constructor ; crush.
+ destruct H ; constructor ; crush.
+ destruct H ; constructor ; crush.
+ destruct H ; constructor ; crush.
Qed.

End section_sim_sym.

Section section_sim_and_bindings.

Lemma
L_map_lid_sim
L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(ι ι' : lid L) (H : lid_sim ξ ξ' ι ι') :
lid_sim ξ ξ' (L_map_lid f ι) (L_map_lid f' ι')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_map_lid_sim.

Lemma
L_map_lbl_sim
LV L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(ℓ ℓ' : lbl LV L) (H : lbl_sim ξ ξ' ℓ ℓ') :
lbl_sim ξ ξ' (L_map_lbl f ℓ) (L_map_lbl f' ℓ')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_map_lbl_sim.

Lemma
L_map_ef_sim
EP EV LV L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(e e' : ef EP EV LV L) (H : ef_sim ξ ξ' e e') :
ef_sim ξ ξ' (L_map_ef f e) (L_map_ef f' e')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_map_ef_sim.

Fixpoint
L_map_eff_sim
EP EV LV L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(E E' : eff EP EV LV L) (H : eff_sim ξ ξ' E E') :
eff_sim ξ ξ' (L_map_eff f E) (L_map_eff f' E')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve L_map_eff_sim.

Fixpoint
L_map_it_sim
EP EV LV L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
κ (N N' : it EP EV LV L κ) (H : it_sim ξ ξ' N N') :
it_sim ξ ξ' (L_map_it f N) (L_map_it f' N')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve L_map_it_sim.

Fixpoint
L_map_ms_sim
EP EV LV L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(σ σ' : ms EP EV LV L) (H : ms_sim ξ ξ' σ σ') :
ms_sim ξ ξ' (L_map_ms f σ) (L_map_ms f' σ')
with
L_map_ty_sim
EP EV LV L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(T T' : ty EP EV LV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (L_map_ty f T) (L_map_ty f' T')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve L_map_ms_sim.
Hint Resolve L_map_ty_sim.

Fixpoint
L_map_md_sim
EV LV V L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(m m' : md EV LV V L) (H : md_sim ξ ξ' m m') :
md_sim ξ ξ' (L_map_md f m) (L_map_md f' m')
with
L_map_ktx_sim
EV LV V L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(K K' : ktx EV LV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (L_map_ktx f K) (L_map_ktx f' K')
with
L_map_val_sim
EV LV V L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(v v' : val EV LV V L) (H : val_sim ξ ξ' v v') :
val_sim ξ ξ' (L_map_val f v) (L_map_val f' v')
with
L_map_tm_sim
EV LV V L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(t t' : tm EV LV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (L_map_tm f t) (L_map_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve L_map_md_sim L_map_val_sim L_map_ktx_sim L_map_tm_sim.

Lemma
LV_map_lbl_sim
LV L LV'
ξ ξ' (f f' : LV → LV') (Q : ∀ α, f α = f' α)
(ℓ ℓ' : lbl LV L) (H : lbl_sim ξ ξ' ℓ ℓ') :
lbl_sim ξ ξ' (LV_map_lbl f ℓ) (LV_map_lbl f' ℓ')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve LV_map_lbl_sim.

Lemma
LV_map_ef_sim
EP EV LV L LV'
ξ ξ' (f f' : LV → LV') (Q : ∀ α, f α = f' α)
(e e' : ef EP EV LV L) (H : ef_sim ξ ξ' e e') :
ef_sim ξ ξ' (LV_map_ef f e) (LV_map_ef f' e')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve LV_map_ef_sim.

Fixpoint
LV_map_eff_sim
EP EV LV L LV'
ξ ξ' (f f' : LV → LV') (Q : ∀ α, f α = f' α)
(E E' : eff EP EV LV L) (H : eff_sim ξ ξ' E E') :
eff_sim ξ ξ' (LV_map_eff f E) (LV_map_eff f' E')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve LV_map_eff_sim.

Fixpoint
LV_map_it_sim
EP EV LV L LV'
ξ ξ' (f f' : LV → LV') (Q : ∀ α, f α = f' α)
κ (N N' : it EP EV LV L κ) (H : it_sim ξ ξ' N N') :
it_sim ξ ξ' (LV_map_it f N) (LV_map_it f' N')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve LV_map_it_sim.

Fixpoint
LV_map_ms_sim
EP EV LV L LV'
ξ ξ' (f f' : LV → LV') (Q : ∀ α, f α = f' α)
(σ σ' : ms EP EV LV L) (H : ms_sim ξ ξ' σ σ') :
ms_sim ξ ξ' (LV_map_ms f σ) (LV_map_ms f' σ')
with
LV_map_ty_sim
EP EV LV L LV'
ξ ξ' (f f' : LV → LV') (Q : ∀ α, f α = f' α)
(T T' : ty EP EV LV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (LV_map_ty f T) (LV_map_ty f' T')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve LV_map_ms_sim.
Hint Resolve LV_map_ty_sim.

Fixpoint
LV_map_md_sim
EV LV V L LV'
ξ ξ' (f f' : LV → LV') (Q : ∀ α, f α = f' α)
(m m' : md EV LV V L) (H : md_sim ξ ξ' m m') :
md_sim ξ ξ' (LV_map_md f m) (LV_map_md f' m')
with
LV_map_ktx_sim
EV LV V L LV'
ξ ξ' (f f' : LV → LV') (Q : ∀ α, f α = f' α)
(K K' : ktx EV LV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (LV_map_ktx f K) (LV_map_ktx f' K')
with
LV_map_val_sim
EV LV V L LV'
ξ ξ' (f f' : LV → LV') (Q : ∀ α, f α = f' α)
(v v' : val EV LV V L) (H : val_sim ξ ξ' v v') :
val_sim ξ ξ' (LV_map_val f v) (LV_map_val f' v')
with
LV_map_tm_sim
EV LV V L LV'
ξ ξ' (f f' : LV → LV') (Q : ∀ α, f α = f' α)
(t t' : tm EV LV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (LV_map_tm f t) (LV_map_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve LV_map_md_sim LV_map_val_sim LV_map_ktx_sim LV_map_tm_sim.

Lemma
EV_map_ef_sim
EP EV LV L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(e e' : ef EP EV LV L) (H : ef_sim ξ ξ' e e') :
ef_sim ξ ξ' (EV_map_ef f e) (EV_map_ef f' e')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve EV_map_ef_sim.

Fixpoint
EV_map_eff_sim
EP EV LV L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(E E' : eff EP EV LV L) (H : eff_sim ξ ξ' E E') :
eff_sim ξ ξ' (EV_map_eff f E) (EV_map_eff f' E')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve EV_map_eff_sim.

Fixpoint
EV_map_it_sim
EP EV LV L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
κ (N N' : it EP EV LV L κ) (H : it_sim ξ ξ' N N') :
it_sim ξ ξ' (EV_map_it f N) (EV_map_it f' N')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve EV_map_it_sim.

Fixpoint
EV_map_ms_sim
EP EV LV L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(σ σ' : ms EP EV LV L) (H : ms_sim ξ ξ' σ σ') :
ms_sim ξ ξ' (EV_map_ms f σ) (EV_map_ms f' σ')
with
EV_map_ty_sim
EP EV LV L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(T T' : ty EP EV LV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (EV_map_ty f T) (EV_map_ty f' T')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve EV_map_ms_sim.
Hint Resolve EV_map_ty_sim.

Fixpoint
EV_map_md_sim
EV LV V L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(m m' : md EV LV V L) (H : md_sim ξ ξ' m m') :
md_sim ξ ξ' (EV_map_md f m) (EV_map_md f' m')
with
EV_map_ktx_sim
EV LV V L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(K K' : ktx EV LV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (EV_map_ktx f K) (EV_map_ktx f' K')
with
EV_map_val_sim
EV LV V L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(v v' : val EV LV V L) (H : val_sim ξ ξ' v v') :
val_sim ξ ξ' (EV_map_val f v) (EV_map_val f' v')
with
EV_map_tm_sim
EV LV V L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(t t' : tm EV LV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (EV_map_tm f t) (EV_map_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve EV_map_md_sim EV_map_val_sim EV_map_ktx_sim EV_map_tm_sim.

Fixpoint
V_map_md_sim
EV LV V L V'
ξ ξ' (f f' : V → V') (Q : ∀ α, f α = f' α)
(m m' : md EV LV V L) (H : md_sim ξ ξ' m m') :
md_sim ξ ξ' (V_map_md f m) (V_map_md f' m')
with
V_map_ktx_sim
EV LV V L V'
ξ ξ' (f f' : V → V') (Q : ∀ α, f α = f' α)
(K K' : ktx EV LV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (V_map_ktx f K) (V_map_ktx f' K')
with
V_map_val_sim
EV LV V L V'
ξ ξ' (f f' : V → V') (Q : ∀ α, f α = f' α)
(v v' : val EV LV V L) (H : val_sim ξ ξ' v v') :
val_sim ξ ξ' (V_map_val f v) (V_map_val f' v')
with
V_map_tm_sim
EV LV V L V'
ξ ξ' (f f' : V → V') (Q : ∀ α, f α = f' α)
(t t' : tm EV LV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (V_map_tm f t) (V_map_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve V_map_md_sim V_map_val_sim V_map_ktx_sim V_map_tm_sim.

Lemma
L_bind_lid_sim
L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(ι ι' : lid L) (H : lid_sim ξ ξ' ι ι') :
lid_sim ξ ξ' (L_bind_lid f ι) (L_bind_lid f' ι')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_bind_lid_sim.

Lemma
L_bind_lbl_sim
LV L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(ℓ ℓ' : lbl LV L) (H : lbl_sim ξ ξ' ℓ ℓ') :
lbl_sim ξ ξ' (L_bind_lbl f ℓ) (L_bind_lbl f' ℓ')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_bind_lbl_sim.

Lemma
L_bind_ef_sim
EP EV LV L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(e e' : ef EP EV LV L) (H : ef_sim ξ ξ' e e') :
ef_sim ξ ξ' (L_bind_ef f e) (L_bind_ef f' e')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_bind_ef_sim.

Lemma
L_bind_eff_sim
EP EV LV L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(E E' : eff EP EV LV L) (H : eff_sim ξ ξ' E E') :
eff_sim ξ ξ' (L_bind_eff f E) (L_bind_eff f' E')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve L_bind_eff_sim.

Lemma
L_bind_it_sim
EP EV LV L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
κ (N N' : it EP EV LV L κ) (H : it_sim ξ ξ' N N') :
it_sim ξ ξ' (L_bind_it f N) (L_bind_it f' N')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve L_bind_it_sim.

Fixpoint
L_bind_ms_sim
EP EV LV L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(σ σ' : ms EP EV LV L) (H : ms_sim ξ ξ' σ σ') :
ms_sim ξ ξ' (L_bind_ms f σ) (L_bind_ms f' σ')
with
L_bind_ty_sim
EP EV LV L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(T T' : ty EP EV LV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (L_bind_ty f T) (L_bind_ty f' T')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve L_bind_ms_sim L_bind_ty_sim.

Fixpoint
L_bind_md_sim
EV LV V L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(m m' : md EV LV V L) (H : md_sim ξ ξ' m m') :
md_sim ξ ξ' (L_bind_md f m) (L_bind_md f' m')
with
L_bind_ktx_sim
EV LV V L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(K K' : ktx EV LV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (L_bind_ktx f K) (L_bind_ktx f' K')
with
L_bind_val_sim
EV LV V L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(u u' : val EV LV V L) (H : val_sim ξ ξ' u u') :
val_sim ξ ξ' (L_bind_val f u) (L_bind_val f' u')
with
L_bind_tm_sim
EV LV V L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(t t' : tm EV LV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (L_bind_tm f t) (L_bind_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Lemma
LV_bind_lbl_sim
LV L LV'
ξ ξ' (f f' : LV → lbl LV' L) (Q : ∀ x, lbl_sim ξ ξ' (f x) (f' x))
ℓ ℓ' (H : lbl_sim ξ ξ' ℓ ℓ') :
lbl_sim ξ ξ' (LV_bind_lbl f ℓ) (LV_bind_lbl f' ℓ')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve LV_bind_lbl_sim.

Lemma
LV_bind_ef_sim
EP EV LV L LV'
ξ ξ' (f f' : LV → lbl LV' L) (Q : ∀ x, lbl_sim ξ ξ' (f x) (f' x))
(e e' : ef EP EV LV L) (H : ef_sim ξ ξ' e e') :
ef_sim ξ ξ' (LV_bind_ef f e) (LV_bind_ef f' e')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve LV_bind_ef_sim.

Lemma
LV_bind_eff_sim
EP EV LV L LV'
ξ ξ' (f f' : LV → lbl LV' L) (Q : ∀ x, lbl_sim ξ ξ' (f x) (f' x))
(E E' : eff EP EV LV L) (H : eff_sim ξ ξ' E E') :
eff_sim ξ ξ' (LV_bind_eff f E) (LV_bind_eff f' E')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve LV_bind_eff_sim.

Lemma
LV_bind_it_sim
EP EV LV L LV'
ξ ξ' (f f' : LV → lbl LV' L) (Q : ∀ x, lbl_sim ξ ξ' (f x) (f' x))
κ (N N' : it EP EV LV L κ) (H : it_sim ξ ξ' N N') :
it_sim ξ ξ' (LV_bind_it f N) (LV_bind_it f' N')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve LV_bind_it_sim.

Fixpoint
LV_bind_ms_sim
EP EV LV L LV'
ξ ξ' (f f' : LV → lbl LV' L) (Q : ∀ x, lbl_sim ξ ξ' (f x) (f' x))
(σ σ' : ms EP EV LV L) (H : ms_sim ξ ξ' σ σ') :
ms_sim ξ ξ' (LV_bind_ms f σ) (LV_bind_ms f' σ')
with
LV_bind_ty_sim
EP EV LV L LV'
ξ ξ' (f f' : LV → lbl LV' L) (Q : ∀ x, lbl_sim ξ ξ' (f x) (f' x))
(T T' : ty EP EV LV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (LV_bind_ty f T) (LV_bind_ty f' T')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve LV_bind_ms_sim LV_bind_ty_sim.

Fixpoint
LV_bind_md_sim
EV LV V L LV'
ξ ξ' (f f' : LV → lbl LV' L) (Q : ∀ x, lbl_sim ξ ξ' (f x) (f' x))
(m m' : md EV LV V L) (H : md_sim ξ ξ' m m') :
md_sim ξ ξ' (LV_bind_md f m) (LV_bind_md f' m')
with
LV_bind_ktx_sim
EV LV V L LV'
ξ ξ' (f f' : LV → lbl LV' L) (Q : ∀ x, lbl_sim ξ ξ' (f x) (f' x))
(K K' : ktx EV LV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (LV_bind_ktx f K) (LV_bind_ktx f' K')
with
LV_bind_val_sim
EV LV V L LV'
ξ ξ' (f f' : LV → lbl LV' L) (Q : ∀ x, lbl_sim ξ ξ' (f x) (f' x))
(u u' : val EV LV V L) (H : val_sim ξ ξ' u u') :
val_sim ξ ξ' (LV_bind_val f u) (LV_bind_val f' u')
with
LV_bind_tm_sim
EV LV V L LV'
ξ ξ' (f f' : LV → lbl LV' L) (Q : ∀ x, lbl_sim ξ ξ' (f x) (f' x))
(t t' : tm EV LV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (LV_bind_tm f t) (LV_bind_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Lemma
EV_bind_ef_sim
EV LV L EV'
ξ ξ' (f f' : EV → eff ∅ EV' LV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
e e' (H : ef_sim ξ ξ' e e') :
eff_sim ξ ξ' (EV_bind_ef f e) (EV_bind_ef f' e')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve EV_bind_ef_sim.

Lemma eff_app_sim
EP EV LV L ξ ξ' :
∀ (E₁ E₁' : eff EP EV LV L), eff_sim ξ ξ' E₁ E₁' →
∀ E₂ E₂', eff_sim ξ ξ' E₂ E₂' →
eff_sim ξ ξ' (E₁ ++ E₂) (E₁' ++ E₂').
Proof.
induction 1 ; intros ? ? H₂.
+ crush.
+ rewrite <- Coq.Lists.List.app_comm_cons.
  crush.
Qed.

Hint Resolve eff_app_sim.

Lemma
EV_bind_eff_sim
EV LV L EV'
ξ ξ' (f f' : EV → eff ∅ EV' LV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
E E' (H : eff_sim ξ ξ' E E') :
eff_sim ξ ξ' (EV_bind_eff f E) (EV_bind_eff f' E')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve EV_bind_eff_sim.

Lemma
EV_bind_it_sim
EV LV L EV'
ξ ξ' (f f' : EV → eff ∅ EV' LV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
κ (N N' : it ∅ EV LV L κ) (H : it_sim ξ ξ' N N') :
it_sim ξ ξ' (EV_bind_it f N) (EV_bind_it f' N')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve EV_bind_it_sim.

Fixpoint
EV_bind_ms_sim
EV LV L EV'
ξ ξ' (f f' : EV → eff ∅ EV' LV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
σ σ' (H : ms_sim ξ ξ' σ σ') :
ms_sim ξ ξ' (EV_bind_ms f σ) (EV_bind_ms f' σ')
with
EV_bind_ty_sim
EV LV L EV'
ξ ξ' (f f' : EV → eff ∅ EV' LV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
T T' (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (EV_bind_ty f T) (EV_bind_ty f' T')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve EV_bind_ms_sim EV_bind_ty_sim.

Fixpoint
EV_bind_md_sim
EV LV V L EV'
ξ ξ' (f f' : EV → eff ∅ EV' LV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
(m m' : md EV LV V L) (H : md_sim ξ ξ' m m') :
md_sim ξ ξ' (EV_bind_md f m) (EV_bind_md f' m')
with
EV_bind_ktx_sim
EV LV V L EV'
ξ ξ' (f f' : EV → eff ∅ EV' LV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
(K K' : ktx EV LV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (EV_bind_ktx f K) (EV_bind_ktx f' K')
with
EV_bind_val_sim
EV LV V L EV'
ξ ξ' (f f' : EV → eff ∅ EV' LV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
(u u' : val EV LV V L) (H : val_sim ξ ξ' u u') :
val_sim ξ ξ' (EV_bind_val f u) (EV_bind_val f' u')
with
EV_bind_tm_sim
EV LV V L EV'
ξ ξ' (f f' : EV → eff ∅ EV' LV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
(t t' : tm EV LV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (EV_bind_tm f t) (EV_bind_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Fixpoint
V_bind_md_sim
EV LV V L V'
ξ ξ' (f f' : V → val EV LV V' L) (Q : ∀ x, val_sim ξ ξ' (f x) (f' x))
m m' (H : md_sim ξ ξ' m m') :
md_sim ξ ξ' (V_bind_md f m) (V_bind_md f' m')
with
V_bind_ktx_sim
EV LV V L V'
ξ ξ' (f f' : V → val EV LV V' L) (Q : ∀ x, val_sim ξ ξ' (f x) (f' x))
K K' (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (V_bind_ktx f K) (V_bind_ktx f' K')
with
V_bind_val_sim
EV LV V L V'
ξ ξ' (f f' : V → val EV LV V' L) (Q : ∀ x, val_sim ξ ξ' (f x) (f' x))
u u' (H : val_sim ξ ξ' u u') :
val_sim ξ ξ' (V_bind_val f u) (V_bind_val f' u')
with
V_bind_tm_sim
EV LV V L V'
ξ ξ' (f f' : V → val EV LV V' L) (Q : ∀ x, val_sim ξ ξ' (f x) (f' x))
t t' (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (V_bind_tm f t) (V_bind_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

End section_sim_and_bindings.


(** [xx_sim] is closed under world extension *)
Section section_sim_future.

Context (ξ₁ ξ₁' ξ₂ ξ₂' : list var).
Context (P : (ξ₂ = ξ₁ ∧ ξ₂' = ξ₁') ∨ (∃ X X', ξ₂ = X :: ξ₁ ∧ ξ₂' = X' :: ξ₁')).

Lemma var_sim_future
X X' (H : var_sim ξ₁ ξ₁' X X') : var_sim ξ₂ ξ₂' X X'.
Proof.
destruct P as [ [P₂ P₂'] | [? [? [P₂ P₂']]] ] ; rewrite P₂, P₂' in *.
+ auto.
+ destruct H as [ n [H H'] ].
  exists (S n) ; split ; constructor ; assumption.
Qed.

Hint Resolve var_sim_future.

Lemma lid_sim_future
L (ι ι' : lid L) (H : lid_sim ξ₁ ξ₁' ι ι') : lid_sim ξ₂ ξ₂' ι ι'.
Proof.
destruct H ;  auto.
Qed.

Hint Resolve lid_sim_future.

Lemma lbl_sim_future
LV L (ℓ ℓ' : lbl LV L) (H : lbl_sim ξ₁ ξ₁' ℓ ℓ') : lbl_sim ξ₂ ξ₂' ℓ ℓ'.
Proof.
destruct H ; auto.
Qed.

Hint Resolve lbl_sim_future.

Lemma ef_sim_future
EP EV LV L (e e' : ef EP EV LV L) (H : ef_sim ξ₁ ξ₁' e e') : ef_sim ξ₂ ξ₂' e e'.
Proof.
destruct H ; auto.
Qed.

Hint Resolve ef_sim_future.

Lemma eff_sim_future
EP EV LV L (E E' : eff EP EV LV L) (H : eff_sim ξ₁ ξ₁' E E') : eff_sim ξ₂ ξ₂' E E'.
Proof.
induction H ; auto.
Qed.

Hint Resolve eff_sim_future.

Lemma it_sim_future
EP EV LV L
κ (N N' : it EP EV LV L κ) (H : it_sim ξ₁ ξ₁' N N') : it_sim ξ₂ ξ₂' N N'.
Proof.
induction H ; auto.
Qed.

Hint Resolve it_sim_future.

Fixpoint
ms_sim_future
EP EV LV L (σ σ' : ms EP EV LV L) (H : ms_sim ξ₁ ξ₁' σ σ') {struct H} : ms_sim ξ₂ ξ₂' σ σ'
with
ty_sim_future
EP EV LV L (T T' : ty EP EV LV L) (H : ty_sim ξ₁ ξ₁' T T') {struct H} : ty_sim ξ₂ ξ₂' T T'.
Proof.
+ destruct H ; constructor ; auto.
+ destruct H ; constructor ; auto.
Qed.

Hint Resolve ms_sim_future ty_sim_future.

Fixpoint
md_sim_future
EV LV V L (m m' : md EV LV V L) (H : md_sim ξ₁ ξ₁' m m') {struct H} : md_sim ξ₂ ξ₂' m m'
with
ktx_sim_future
EV LV V L (K K' : ktx EV LV V L) (H : ktx_sim ξ₁ ξ₁' K K') {struct H} : ktx_sim ξ₂ ξ₂' K K'
with
val_sim_future
EV LV V L (v v' : val EV LV V L) (H : val_sim ξ₁ ξ₁' v v') {struct H} : val_sim ξ₂ ξ₂' v v'
with
tm_sim_future
EV LV V L (t t' : tm EV LV V L) (H : tm_sim ξ₁ ξ₁' t t') {struct H} : tm_sim ξ₂ ξ₂' t t'
.
Proof.
+ destruct H ; constructor ; auto.
+ destruct H ; constructor ; auto.
+ destruct H ; constructor ; auto.
+ destruct H ; constructor ; auto.
Qed.

End section_sim_future.


Lemma eff_app_sim_inv_l ξ ξ' EP EV LV L : ∀ (E1 E2 E' : eff EP EV LV L),
eff_sim ξ ξ' (E1 ++ E2) E' →
∃ E1' E2', E' = E1' ++ E2' ∧ (eff_sim ξ ξ' E1 E1' ∧ eff_sim ξ ξ' E2 E2').
Proof.
induction E1 ; simpl ; intros ? ? H.
+ repeat eexists ; [ | constructor | exact H ].
  auto.
+ inversion H ; subst ; clear H.
  match goal with
  | [ H : eff_sim _ _ (E1 ++ _) _ |- _ ] =>
    apply IHE1 in H ; destruct H as [?[?[?[??]]]] ; subst
  end.
  repeat eexists ; auto using app_comm_cons.
Qed.
