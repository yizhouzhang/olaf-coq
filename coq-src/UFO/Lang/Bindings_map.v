Require Import FinFun.
Require Import Lang.Syntax.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Section section_map_inc.
Context (A B : Set).

(** If we can change the representation of a variable from [A] to [B],
then we can change the representation of a variable from [inc A] to
[inc B]. *)
Definition map_inc (f : A → B) : inc A → inc B :=
  λ v, match v with
  | VZ    => VZ
  | VS v' => VS (f v')
  end.

Fixpoint map_incn (f : A → B) n {struct n} : incn A n → incn B n.
Proof.
destruct n as [ | n ] ; simpl ; intro x.
+ refine (f x).
+ destruct x as [ | x].
  - refine VZ.
  - refine (VS (map_incn f n x)).
Defined.

Hint Extern 0 => match goal with
| [ Inj : Injective ?f, H : ?f _ = ?f _ |- _ ] =>
  apply Inj in H ; subst
end.

Lemma map_inc_is_injective (f : A → B) :
Injective f → Injective (map_inc f).
Proof.
intros_all ; crush.
Qed.

End section_map_inc.


(** Change the variable representation type [L] to [L']. *)

Definition
  L_map_lid
    L L' (f : L → L') (ι : lid L) : lid L' :=
  match ι with
  | lid_f X => lid_f X
  | lid_b N => lid_b (f N)
  end
.

Definition
  L_map_lbl
    LV L L' (f : L → L') (ℓ : lbl LV L) : lbl LV L' :=
  match ℓ with
  | lbl_var α => lbl_var α
  | lbl_id ι => lbl_id (L_map_lid f ι)
  end
.

Definition
  L_map_ef
    EP EV LV L L' (f : L → L') (e : ef EP EV LV L) : ef EP EV LV L' :=
  match e with
  | ef_par α => ef_par α
  | ef_var α => ef_var α
  | ef_lbl ℓ => ef_lbl (L_map_lbl f ℓ)
  end
.

Fixpoint
  L_map_eff
    EP EV LV L L' (f : L → L') (E : eff EP EV LV L) {struct E} : eff EP EV LV L' :=
  match E with
  | [] => []
  | e :: E' => (L_map_ef f e) :: (L_map_eff f E')
  end
.

Fixpoint
  L_map_it
    EP EV LV L L' (f : L → L') κ (N : it EP EV LV L κ) {struct N} : it EP EV LV L' κ :=
  match N with
  | it_name F => it_name F
  | it_inst N E => it_inst (L_map_it f N) (L_map_eff f E)
  end
.

Fixpoint
  L_map_ty
    EP EV LV L L' (f : L → L') (T : ty EP EV LV L) {struct T} : ty EP EV LV L' :=
  match T with
  | 𝟙 => ty_unit
  | ty_it N ℓ => ty_it (L_map_it f N) (L_map_lbl f ℓ)
  | ty_cont T₁ E₁ T₂ E₂ =>
      ty_cont
      (L_map_ty f T₁) (L_map_eff f E₁)
      (L_map_ty f T₂) (L_map_eff f E₂)
  | ty_ms σ ℓ => ty_ms (L_map_ms f σ) (L_map_lbl f ℓ)
  end
with
  L_map_ms
    EP EV LV L L' (f : L → L') (σ : ms EP EV LV L) {struct σ} : ms EP EV LV L' :=
  match σ with
  | ms_ev σ => ms_ev (L_map_ms f σ)
  | ms_lv σ => ms_lv (L_map_ms f σ)
  | ms_tm T σ => ms_tm (L_map_ty f T) (L_map_ms f σ)
  | ms_res T E => ms_res (L_map_ty f T) (L_map_eff f E)
  end
.

Fixpoint L_map_is
EP EV LV L L' (f : L → L') (Σ : is EP EV LV L) {struct Σ} : is EP EV LV L' :=
match Σ with
| is_ms σ => is_ms (L_map_ms f σ)
| is_ep Σ => is_ep (L_map_is f Σ)
end.

Fixpoint
  L_map_md
    EV LV V L L' (f : L → L')
    (m : md EV LV V L) {struct m} : md EV LV V L' :=
  match m with
  | md_ev m => md_ev (L_map_md f m)
  | md_lv m => md_lv (L_map_md f m)
  | md_tm m => md_tm (L_map_md f m)
  | md_res t => md_res (L_map_tm f t)
  end
with
  L_map_ktx
    EV LV V L L' (f : L → L')
    (K : ktx EV LV V L) {struct K} : ktx EV LV V L' :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (L_map_ktx f K) X
  | ktx_up K =>
      ktx_up (L_map_ktx f K)
  | ktx_op K =>
      ktx_op (L_map_ktx f K)
  | ktx_let K t =>
      ktx_let (L_map_ktx f K) (L_map_tm f t)
  | ktx_throw K t =>
      ktx_throw (L_map_ktx f K) (L_map_tm f t)
  | ktx_app_eff K E =>
      ktx_app_eff (L_map_ktx f K) (L_map_eff f E)
  | ktx_app_lbl K ℓ =>
      ktx_app_lbl (L_map_ktx f K) (L_map_lbl f ℓ)
  | ktx_app_tm1 K t =>
      ktx_app_tm1 (L_map_ktx f K) (L_map_tm f t)
  | ktx_app_tm2 K v =>
      ktx_app_tm2 (L_map_ktx f K) (L_map_val f v)
  end
with
  L_map_val
    EV LV V L L' (f : L → L')
    (v : val EV LV V L) {struct v} : val EV LV V L' :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_cont K => L_map_ktx f K
  | val_md m ι => val_md (L_map_md f m) (L_map_lid f ι)
  | val_fix m ι => val_fix (L_map_md f m) (L_map_lid f ι)
  end
with
  L_map_tm
    EV LV V L L' (f : L → L')
    (t : tm EV LV V L) {struct t} : tm EV LV V L' :=
  match t with
  | tm_val v => L_map_val f v
  | tm_op t => tm_op (L_map_tm f t)
  | ⇧ t => ⇧ (L_map_tm f t)
  | ⬇ t => ⬇ (L_map_tm (map_inc f) t)
  | ⇩ X t => ⇩ X (L_map_tm f t)
  | tm_let s t => tm_let (L_map_tm f s) (L_map_tm f t)
  | tm_throw t s => tm_throw (L_map_tm f t) (L_map_tm f s)
  | tm_app_eff t E => tm_app_eff (L_map_tm f t) (L_map_eff f E)
  | tm_app_lbl t ℓ => tm_app_lbl (L_map_tm f t) (L_map_lbl f ℓ)
  | tm_app_tm t s => tm_app_tm (L_map_tm f t) (L_map_tm f s)
  end
.

(** Change the variable representation type [LV] to [LV']. *)

Definition
  LV_map_lbl
    LV LV' L (f : LV → LV') (ℓ : lbl LV L) : lbl LV' L :=
  match ℓ with
  | lbl_var z => lbl_var (f z)
  | lbl_id lid => lbl_id lid
  end
.

Definition
  LV_map_ef
    EP EV LV LV' L (f : LV → LV') (e : ef EP EV LV L) : ef EP EV LV' L :=
  match e with
  | ef_par α => ef_par α 
  | ef_var α => ef_var α 
  | ef_lbl ℓ => ef_lbl (LV_map_lbl f ℓ)
  end
.

Fixpoint
  LV_map_eff
    EP EV LV LV' L (f : LV → LV') (E : eff EP EV LV L) {struct E} : eff EP EV LV' L :=
  match E with
  | [] => []
  | e :: E' => (LV_map_ef f e) :: (LV_map_eff f E')
  end
.

Fixpoint
  LV_map_it
    EP EV LV LV' L (f : LV → LV') κ (N : it EP EV LV L κ) {struct N} : it EP EV LV' L κ :=
  match N with
  | it_name 𝔽 => it_name 𝔽
  | it_inst N E => it_inst (LV_map_it f N) (LV_map_eff f E)
  end
.

Fixpoint
  LV_map_ty
    EP EV LV LV' L (f : LV → LV') (T : ty EP EV LV L) {struct T} : ty EP EV LV' L :=
  match T with
  | 𝟙 => ty_unit
  | ty_it N ℓ => ty_it (LV_map_it f N) (LV_map_lbl f ℓ)
  | ty_cont T₁ E₁ T₂ E₂ =>
      ty_cont
      (LV_map_ty f T₁) (LV_map_eff f E₁)
      (LV_map_ty f T₂) (LV_map_eff f E₂)
  | ty_ms σ ℓ => ty_ms (LV_map_ms f σ) (LV_map_lbl f ℓ)
  end
with
  LV_map_ms
    EP EV LV LV' L (f : LV → LV') (σ : ms EP EV LV L) {struct σ} : ms EP EV LV' L :=
  match σ with
  | ms_ev σ => ms_ev (LV_map_ms f σ)
  | ms_lv σ => ms_lv (LV_map_ms (map_inc f) σ)
  | ms_tm T σ => ms_tm (LV_map_ty f T) (LV_map_ms f σ)
  | ms_res T E => ms_res (LV_map_ty f T) (LV_map_eff f E)
  end
.

Fixpoint LV_map_is
EP EV LV LV' L (f : LV → LV') (Σ : is EP EV LV L) {struct Σ} : is EP EV LV' L :=
match Σ with
| is_ms σ => is_ms (LV_map_ms f σ)
| is_ep Σ => is_ep (LV_map_is f Σ)
end.

Fixpoint
  LV_map_md
    EV LV LV' V L (f : LV → LV')
    (m : md EV LV V L) {struct m} : md EV LV' V L :=
  match m with
  | md_ev m => md_ev (LV_map_md f m)
  | md_lv m => md_lv (LV_map_md (map_inc f) m)
  | md_tm m => md_tm (LV_map_md f m)
  | md_res t => md_res (LV_map_tm f t)
  end
with
  LV_map_val
    EV LV LV' V L (f : LV → LV')
    (v : val EV LV V L) {struct v} : val EV LV' V L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_cont K => val_cont (LV_map_ktx f K)
  | val_md m ι => val_md (LV_map_md f m) ι
  | val_fix m ι => val_fix (LV_map_md f m) ι
  end
with
  LV_map_tm
    EV LV LV' V L (f : LV → LV')
    (t : tm EV LV V L) {struct t} : tm EV LV' V L :=
  match t with
  | tm_val v => LV_map_val f v
  | tm_op t => tm_op (LV_map_tm f t)
  | ⇧ t => ⇧ (LV_map_tm f t)
  | ⬇ t => ⬇ (LV_map_tm f t)
  | ⇩ X t => ⇩ X (LV_map_tm f t)
  | tm_let s t => tm_let (LV_map_tm f s) (LV_map_tm f t)
  | tm_throw t s => tm_throw (LV_map_tm f t) (LV_map_tm f s)
  | tm_app_eff t E => tm_app_eff (LV_map_tm f t) (LV_map_eff f E)
  | tm_app_lbl t ℓ => tm_app_lbl (LV_map_tm f t) (LV_map_lbl f ℓ)
  | tm_app_tm t s => tm_app_tm (LV_map_tm f t) (LV_map_tm f s)
  end
with
  LV_map_ktx
    EV LV LV' V L (f : LV → LV')
    (K : ktx EV LV V L) {struct K} : ktx EV LV' V L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (LV_map_ktx f K) X
  | ktx_up K =>
      ktx_up (LV_map_ktx f K)
  | ktx_op K =>
      ktx_op (LV_map_ktx f K)
  | ktx_let K t =>
      ktx_let (LV_map_ktx f K) (LV_map_tm f t)
  | ktx_throw K t =>
      ktx_throw (LV_map_ktx f K) (LV_map_tm f t)
  | ktx_app_eff K E =>
      ktx_app_eff (LV_map_ktx f K) (LV_map_eff f E)
  | ktx_app_lbl K ℓ =>
      ktx_app_lbl (LV_map_ktx f K) (LV_map_lbl f ℓ)
  | ktx_app_tm1 K t =>
      ktx_app_tm1 (LV_map_ktx f K) (LV_map_tm f t)
  | ktx_app_tm2 K v =>
      ktx_app_tm2 (LV_map_ktx f K) (LV_map_val f v)
  end
.

Definition LV_map_XEnv EV LV LV'
(f : LV → LV') (Ξ : XEnv EV LV) : XEnv EV LV' :=
  map (λ x,
    match x with
      (T, E) => (LV_map_ty f T, LV_map_eff f E)
    end
  ) Ξ.

Fixpoint LV_map_LEnv EV LV L LV'
(f : LV → LV') (Π : LEnv EV LV L) : LEnv EV LV' L :=
match Π with
| LEnv_empty => LEnv_empty
| LEnv_push Π T E => LEnv_push (LV_map_LEnv f Π) (LV_map_ty f T) (LV_map_eff f E)
end.

(** Change the variable representation type [EV] to [EV']. *)

Fixpoint
  EV_map_ef
    EP EV EV' LV L (f : EV → EV') (e : ef EP EV LV L) : ef EP EV' LV L :=
  match e with
  | ef_par α => ef_par α
  | ef_var α => ef_var (f α)
  | ef_lbl ℓ => ef_lbl ℓ
  end
.

Fixpoint
  EV_map_eff
    EP EV EV' LV L (f : EV → EV') (E : eff EP EV LV L) {struct E} : eff EP EV' LV L :=
  match E with
  | [] => []
  | e :: E' => (EV_map_ef f e) :: (EV_map_eff f E')
  end
.

Fixpoint
  EV_map_it
    EP EV EV' LV L (f : EV → EV') κ (N : it EP EV LV L κ) {struct N} : it EP EV' LV L κ :=
  match N with
  | it_name 𝔽 => it_name 𝔽
  | it_inst N E => it_inst (EV_map_it f N) (EV_map_eff f E)
  end
.

Fixpoint
  EV_map_ty
    EP EV EV' LV L (f : EV → EV') (T : ty EP EV LV L) {struct T} : ty EP EV' LV L :=
  match T with
  | 𝟙 => ty_unit
  | ty_it N ℓ => ty_it (EV_map_it f N) ℓ
  | ty_cont T₁ E₁ T₂ E₂ =>
      ty_cont
      (EV_map_ty f T₁) (EV_map_eff f E₁)
      (EV_map_ty f T₂) (EV_map_eff f E₂)
  | ty_ms σ ℓ => ty_ms (EV_map_ms f σ) ℓ
  end
with
  EV_map_ms
    EP EV EV' LV L (f : EV → EV') (σ : ms EP EV LV L) {struct σ} : ms EP EV' LV L :=
  match σ with
  | ms_ev σ => ms_ev (EV_map_ms (map_inc f) σ)
  | ms_lv σ => ms_lv (EV_map_ms f σ)
  | ms_tm T σ => ms_tm (EV_map_ty f T) (EV_map_ms f σ)
  | ms_res T E => ms_res (EV_map_ty f T) (EV_map_eff f E)
  end
.

Fixpoint EV_map_is
EP EV EV' LV L (f : EV → EV') (Σ : is EP EV LV L) {struct Σ} : is EP EV' LV L :=
match Σ with
| is_ms σ => is_ms (EV_map_ms f σ)
| is_ep Σ => is_ep (EV_map_is f Σ)
end.

Fixpoint
  EV_map_md
    EV EV' LV V L (f : EV → EV')
    (m : md EV LV V L) {struct m} : md EV' LV V L :=
  match m with
  | md_ev m => md_ev (EV_map_md (map_inc f) m)
  | md_lv m => md_lv (EV_map_md f m)
  | md_tm m => md_tm (EV_map_md f m)
  | md_res t => md_res (EV_map_tm f t)
  end
with
  EV_map_ktx
    EV EV' LV V L (f : EV → EV')
    (K : ktx EV LV V L) {struct K} : ktx EV' LV V L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (EV_map_ktx f K) X
  | ktx_up K =>
      ktx_up (EV_map_ktx f K)
  | ktx_op K =>
      ktx_op (EV_map_ktx f K)
  | ktx_let K t =>
      ktx_let (EV_map_ktx f K) (EV_map_tm f t)
  | ktx_throw K t =>
      ktx_throw (EV_map_ktx f K) (EV_map_tm f t)
  | ktx_app_eff K E =>
      ktx_app_eff (EV_map_ktx f K) (EV_map_eff f E)
  | ktx_app_lbl K ℓ =>
      ktx_app_lbl (EV_map_ktx f K) ℓ
  | ktx_app_tm1 K t =>
      ktx_app_tm1 (EV_map_ktx f K) (EV_map_tm f t)
  | ktx_app_tm2 K v =>
      ktx_app_tm2 (EV_map_ktx f K) (EV_map_val f v)
  end
with
  EV_map_val
    EV EV' LV V L (f : EV → EV')
    (v : val EV LV V L) {struct v} : val EV' LV V L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_cont K => EV_map_ktx f K
  | val_md m ι => val_md (EV_map_md f m) ι
  | val_fix m ι => val_fix (EV_map_md f m) ι
  end
with
  EV_map_tm
    EV EV' LV V L (f : EV → EV')
    (t : tm EV LV V L) {struct t} : tm EV' LV V L :=
  match t with
  | tm_val v => EV_map_val f v
  | tm_op t => tm_op (EV_map_tm f t)
  | ⇧ t => ⇧ (EV_map_tm f t)
  | ⬇ t => ⬇ (EV_map_tm f t)
  | ⇩ X t => ⇩ X (EV_map_tm f t)
  | tm_let s t => tm_let (EV_map_tm f s) (EV_map_tm f t)
  | tm_throw t s => tm_throw (EV_map_tm f t) (EV_map_tm f s)
  | tm_app_eff t E => tm_app_eff (EV_map_tm f t) (EV_map_eff f E)
  | tm_app_lbl t ℓ => tm_app_lbl (EV_map_tm f t) ℓ
  | tm_app_tm t s => tm_app_tm (EV_map_tm f t) (EV_map_tm f s)
  end
.

Definition EV_map_XEnv EV EV' LV
(f : EV → EV') (Ξ : XEnv EV LV) : XEnv EV' LV :=
  map (λ x,
    match x with
      (T, E) => (EV_map_ty f T, EV_map_eff f E)
    end
  ) Ξ.

Fixpoint EV_map_LEnv EV LV L EV'
(f : EV → EV') (Π : LEnv EV LV L) : LEnv EV' LV L :=
match Π with
| LEnv_empty => LEnv_empty
| LEnv_push Π T E => LEnv_push (EV_map_LEnv f Π) (EV_map_ty f T) (EV_map_eff f E)
end.

(** Change the variable representation type [EP] to [EP']. *)

Fixpoint
  EP_map_ef
    EP EP' EV LV L (f : EP → EP') (e : ef EP EV LV L) : ef EP' EV LV L :=
  match e with
  | ef_par α => ef_par (f α)
  | ef_var α => ef_var α
  | ef_lbl ℓ => ef_lbl ℓ
  end
.

Fixpoint
  EP_map_eff
    EP EP' EV LV L (f : EP → EP') (E : eff EP EV LV L) {struct E} : eff EP' EV LV L :=
  match E with
  | [] => []
  | e :: E' => (EP_map_ef f e) :: (EP_map_eff f E')
  end
.

Fixpoint
  EP_map_it
    EP EP' EV LV L (f : EP → EP') κ (N : it EP EV LV L κ) {struct N} : it EP' EV LV L κ :=
  match N with
  | it_name 𝔽 => it_name 𝔽
  | it_inst N E => it_inst (EP_map_it f N) (EP_map_eff f E)
  end
.

Fixpoint
  EP_map_ty
    EP EP' EV LV L (f : EP → EP') (T : ty EP EV LV L) {struct T} : ty EP' EV LV L :=
  match T with
  | 𝟙 => ty_unit
  | ty_it N ℓ => ty_it (EP_map_it f N) ℓ
  | ty_cont T₁ E₁ T₂ E₂ =>
      ty_cont
      (EP_map_ty f T₁) (EP_map_eff f E₁)
      (EP_map_ty f T₂) (EP_map_eff f E₂)
  | ty_ms σ ℓ => ty_ms (EP_map_ms f σ) ℓ
  end
with
  EP_map_ms
    EP EP' EV LV L (f : EP → EP') (σ : ms EP EV LV L) {struct σ} : ms EP' EV LV L :=
  match σ with
  | ms_ev σ => ms_ev (EP_map_ms f σ)
  | ms_lv σ => ms_lv (EP_map_ms f σ)
  | ms_tm T σ => ms_tm (EP_map_ty f T) (EP_map_ms f σ)
  | ms_res T E => ms_res (EP_map_ty f T) (EP_map_eff f E)
  end
.

Fixpoint EP_map_is
EP EP' EV LV L (f : EP → EP') (Σ : is EP EV LV L) {struct Σ} : is EP'  EV LV L:=
match Σ with
| is_ms σ => is_ms (EP_map_ms f σ)
| is_ep Σ => is_ep (EP_map_is (map_inc f) Σ)
end.

(** Change the variable representation type [V] to [V']. *)

Fixpoint
  V_map_md
    EV LV V V' L (f : V → V')
    (m : md EV LV V L) {struct m} : md EV LV V' L :=
  match m with
  | md_ev m => md_ev (V_map_md f m)
  | md_lv m => md_lv (V_map_md f m)
  | md_tm m => md_tm (V_map_md (map_inc f) m)
  | md_res t => md_res (V_map_tm (map_inc f) t)
  end
with
  V_map_ktx
    EV LV V V' L (f : V → V')
    (K : ktx EV LV V L) {struct K} : ktx EV LV V' L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
     ktx_down (V_map_ktx f K) X
  | ktx_up K =>
      ktx_up (V_map_ktx f K)
  | ktx_op K =>
      ktx_op (V_map_ktx f K)
  | ktx_let K t =>
      ktx_let (V_map_ktx f K) (V_map_tm (map_inc f) t)
  | ktx_throw K t =>
      ktx_throw (V_map_ktx f K) (V_map_tm f t)
  | ktx_app_eff K E =>
      ktx_app_eff (V_map_ktx f K) E
  | ktx_app_lbl K ℓ =>
      ktx_app_lbl (V_map_ktx f K) ℓ
  | ktx_app_tm1 K t =>
      ktx_app_tm1 (V_map_ktx f K) (V_map_tm f t)
  | ktx_app_tm2 K v =>
      ktx_app_tm2 (V_map_ktx f K) (V_map_val f v)
  end
with
  V_map_val
    EV LV V V' L (f : V → V')
    (v : val EV LV V L) {struct v} : val EV LV V' L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var (f x)
  | val_cont K => V_map_ktx f K
  | val_md m ι => val_md (V_map_md f m) ι
  | val_fix m ι => val_fix (V_map_md (map_inc f) m) ι
  end
with
  V_map_tm
    EV LV V V' L (f : V → V')
    (t : tm EV LV V L) {struct t} : tm EV LV V' L :=
  match t with
  | tm_val v => V_map_val f v
  | tm_op t => tm_op (V_map_tm f t)
  | ⇧ t => ⇧ (V_map_tm f t)
  | ⬇ t => ⬇ (V_map_tm f t)
  | ⇩ X t => ⇩ X (V_map_tm f t)
  | tm_let s t => tm_let (V_map_tm f s) (V_map_tm (map_inc f) t)
  | tm_throw t s => tm_throw (V_map_tm f t) (V_map_tm f s)
  | tm_app_eff t E => tm_app_eff (V_map_tm f t) E
  | tm_app_lbl t ℓ => tm_app_lbl (V_map_tm f t) ℓ
  | tm_app_tm t s => tm_app_tm (V_map_tm f t) (V_map_tm f s)
  end
.

(** A syntactic object can be used in a context that binds one more variable. *)

Notation L_shift_lid := (L_map_lid (@VS _)).
Notation L_shift_lbl := (L_map_lbl (@VS _)).
Notation L_shift_ef := (L_map_ef (@VS _)).
Notation L_shift_eff := (L_map_eff (@VS _)).
Notation L_shift_it := (L_map_it (@VS _)).
Notation L_shift_ty := (L_map_ty (@VS _)).
Notation L_shift_ms := (L_map_ms (@VS _)).
Notation L_shift_is := (L_map_is (@VS _)).
Notation L_shift_md := (L_map_md (@VS _)).
Notation L_shift_val := (L_map_val (@VS _)).
Notation L_shift_tm := (L_map_tm (@VS _)).
Notation L_shift_ktx := (L_map_ktx (@VS _)).

Notation LV_shift_lbl := (LV_map_lbl (@VS _)).
Notation LV_shift_ef := (LV_map_ef (@VS _)).
Notation LV_shift_eff := (LV_map_eff (@VS _)).
Notation LV_shift_it := (LV_map_it (@VS _)).
Notation LV_shift_ty := (LV_map_ty (@VS _)).
Notation LV_shift_ms := (LV_map_ms (@VS _)).
Notation LV_shift_is := (LV_map_is (@VS _)).
Notation LV_shift_md := (LV_map_md (@VS _)).
Notation LV_shift_val := (LV_map_val (@VS _)).
Notation LV_shift_tm := (LV_map_tm (@VS _)).
Notation LV_shift_ktx := (LV_map_ktx (@VS _)).
Notation LV_shift_XEnv := (LV_map_XEnv (@VS _)).
Notation LV_shift_LEnv := (LV_map_LEnv (@VS _)).

Notation EV_shift_ef := (EV_map_ef (@VS _)).
Notation EV_shift_eff := (EV_map_eff (@VS _)).
Notation EV_shift_it := (EV_map_it (@VS _)).
Notation EV_shift_ty := (EV_map_ty (@VS _)).
Notation EV_shift_ms := (EV_map_ms (@VS _)).
Notation EV_shift_is := (EV_map_is (@VS _)).
Notation EV_shift_md := (EV_map_md (@VS _)).
Notation EV_shift_val := (EV_map_val (@VS _)).
Notation EV_shift_tm := (EV_map_tm (@VS _)).
Notation EV_shift_ktx := (EV_map_ktx (@VS _)).
Notation EV_shift_XEnv := (EV_map_XEnv (@VS _)).
Notation EV_shift_LEnv := (EV_map_LEnv (@VS _)).

Notation EP_shift_ef := (EP_map_ef (@VS _)).
Notation EP_shift_eff := (EP_map_eff (@VS _)).
Notation EP_shift_it := (EP_map_it (@VS _)).
Notation EP_shift_ty := (EP_map_ty (@VS _)).
Notation EP_shift_ms := (EP_map_ms (@VS _)).
Notation EP_shift_is := (EP_map_is (@VS _)).

Notation V_shift_md := (V_map_md (@VS _)).
Notation V_shift_val := (V_map_val (@VS _)).
Notation V_shift_tm := (V_map_tm (@VS _)).
Notation V_shift_ktx := (V_map_ktx (@VS _)).

(** Syntactic objects that do not contain free variables can be used
in any context that binds free variables. *)

Notation L_open_lid := (L_map_lid ∅→).
Notation L_open_lbl := (L_map_lbl ∅→).
Notation L_open_ef := (L_map_ef ∅→).
Notation L_open_eff := (L_map_eff ∅→).
Notation L_open_it := (L_map_it ∅→).
Notation L_open_ty := (L_map_ty ∅→).
Notation L_open_ms := (L_map_ms ∅→).
Notation L_open_is := (L_map_is ∅→).
Notation L_open_md := (L_map_md ∅→).
Notation L_open_val := (L_map_val ∅→).
Notation L_open_tm := (L_map_tm ∅→).
Notation L_open_ktx := (L_map_ktx ∅→).

Notation LV_open_lbl := (LV_map_lbl ∅→).
Notation LV_open_ef := (LV_map_ef ∅→).
Notation LV_open_eff := (LV_map_eff ∅→).
Notation LV_open_it := (LV_map_it ∅→).
Notation LV_open_ty := (LV_map_ty ∅→).
Notation LV_open_ms := (LV_map_ms ∅→).
Notation LV_open_is := (LV_map_is ∅→).
Notation LV_open_md := (LV_map_md ∅→).
Notation LV_open_val := (LV_map_val ∅→).
Notation LV_open_tm := (LV_map_tm ∅→).
Notation LV_open_ktx := (LV_map_ktx ∅→).
Notation LV_open_XEnv := (LV_map_XEnv ∅→).

Notation EV_open_ef := (EV_map_ef ∅→).
Notation EV_open_eff := (EV_map_eff ∅→).
Notation EV_open_it := (EV_map_it ∅→).
Notation EV_open_ty := (EV_map_ty ∅→).
Notation EV_open_ms := (EV_map_ms ∅→).
Notation EV_open_is := (EV_map_is ∅→).
Notation EV_open_md := (EV_map_md ∅→).
Notation EV_open_val := (EV_map_val ∅→).
Notation EV_open_tm := (EV_map_tm ∅→).
Notation EV_open_ktx := (EV_map_ktx ∅→).
Notation EV_open_XEnv := (EV_map_XEnv ∅→).

Notation EP_open_ef := (EP_map_ef ∅→).
Notation EP_open_eff := (EP_map_eff ∅→).
Notation EP_open_it := (EP_map_it ∅→).
Notation EP_open_ty := (EP_map_ty ∅→).
Notation EP_open_ms := (EP_map_ms ∅→).
Notation EP_open_is := (EP_map_is ∅→).

Notation V_open_md := (V_map_md ∅→).
Notation V_open_val := (V_map_val ∅→).
Notation V_open_tm := (V_map_tm ∅→).
Notation V_open_ktx := (V_map_ktx ∅→).