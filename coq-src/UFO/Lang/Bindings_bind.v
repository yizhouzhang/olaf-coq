Require Import Lang.Syntax Lang.Bindings_map.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Section section_lift_inc.
Context (EP EP' EV EV' LV LV' V V' L L' : Set).

(** If we have a substitution function of form [EV → eff EV' LV L],
then we can turn it into one of form [inc EV → eff (inc EV') LV L]. *)

Definition L_lift_inc (f : L → lid L') :
    inc L → lid (inc L') :=
  λ α, match α with
  | VZ   => lid_b VZ
  | VS β => L_shift_lid (f β)
  end.

Definition LV_lift_inc (f : LV → lbl LV' L) :
    inc LV → lbl (inc LV') L :=
  λ α, match α with
  | VZ   => lbl_var VZ
  | VS β => LV_shift_lbl (f β)
  end.

Definition EV_lift_inc (f : EV → eff EP EV' LV L) :
    inc EV → eff EP (inc EV') LV L :=
  λ α, match α with
  | VZ   => [ ef_var VZ ]
  | VS β => EV_shift_eff (f β)
  end.

Definition EP_lift_inc (f : EP → eff EP' EV LV L) :
    inc EP → eff (inc EP') EV LV L :=
  λ α, match α with
  | VZ   => [ ef_par VZ ]
  | VS β => EP_shift_eff (f β)
  end.

Definition V_lift_inc (f : V → val EV LV V' L) :
    inc V → val EV LV (inc V') L :=
  λ x, match x with
  | VZ   => val_var VZ
  | VS β => V_shift_val (f β)
  end.

End section_lift_inc.


(** Apply the substitution function [f : L → lid L'] *)

Definition
L_bind_lid
L L' (f : L → lid L') (ID : lid L) : lid L' :=
  match ID with
  | lid_b x => f x
  | lid_f X => lid_f X
  end
.

Definition
L_bind_lbl
LV L L' (f : L → lid L') (ℓ : lbl LV L) : lbl LV L' :=
  match ℓ with
  | lbl_var α => lbl_var α
  | lbl_id id => lbl_id (L_bind_lid f id)
  end
.

Definition
L_bind_ef
EP EV LV L L' (f : L → lid L') (e : ef EP EV LV L) : ef EP EV LV L' :=
  match e with
  | ef_par α => ef_par α
  | ef_var α => ef_var α
  | ef_lbl ℓ => ef_lbl (L_bind_lbl f ℓ)
  end
.

Fixpoint
L_bind_eff
EP EV LV L L' (f : L → lid L') (E : eff EP EV LV L) {struct E} : eff EP EV LV L' :=
  match E with
  | [] => []
  | e :: E' => (L_bind_ef f e) :: (L_bind_eff f E')
  end
.

Fixpoint
L_bind_it
EP EV LV L L' (f : L → lid L') κ (N : it EP EV LV L κ) {struct N} : it EP EV LV L' κ :=
  match N with
  | it_name 𝔽 => it_name 𝔽
  | it_inst N E => it_inst (L_bind_it f N) (L_bind_eff f E)
  end
.

Fixpoint
L_bind_ty
EP EV LV L L' (f : L → lid L') (T : ty EP EV LV L) {struct T} : ty EP EV LV L' :=
  match T with
  | 𝟙 => ty_unit
  | ty_it N ℓ => ty_it (L_bind_it f N) (L_bind_lbl f ℓ)
  | ty_cont T₁ E₁ T₂ E₂ =>
      ty_cont
      (L_bind_ty f T₁) (L_bind_eff f E₁)
      (L_bind_ty f T₂) (L_bind_eff f E₂)
  | ty_ms σ ℓ => ty_ms (L_bind_ms f σ) (L_bind_lbl f ℓ)
  end
with
L_bind_ms
EP EV LV L L' (f : L → lid L') (σ : ms EP EV LV L) {struct σ} : ms EP EV LV L' :=
  match σ with
  | ms_ev σ => ms_ev (L_bind_ms f σ)
  | ms_lv σ => ms_lv (L_bind_ms f σ)
  | ms_tm T σ => ms_tm (L_bind_ty f T) (L_bind_ms f σ)
  | ms_res T E => ms_res (L_bind_ty f T) (L_bind_eff f E)
  end
.

Fixpoint
L_bind_is
EP EV LV L L' (f : L → lid L') (Σ : is EP EV LV L) {struct Σ} : is EP EV LV L' :=
  match Σ with
  | is_ms σ => is_ms (L_bind_ms f σ)
  | is_ep Σ => is_ep (L_bind_is f Σ)
  end
.

Fixpoint
L_bind_md
EV LV V L L' (f : L → lid L')
(m : md EV LV V L) {struct m} : md EV LV V L' :=
  match m with
  | md_ev m => md_ev (L_bind_md f m)
  | md_lv m => md_lv (L_bind_md f m)
  | md_tm m => md_tm (L_bind_md f m)
  | md_res t => md_res (L_bind_tm f t)
  end
with
L_bind_ktx
EV LV V L L' (f : L → lid L')
(K : ktx EV LV V L) {struct K} : ktx EV LV V L' :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (L_bind_ktx f K) X
  | ktx_up K =>
      ktx_up (L_bind_ktx f K)
  | ktx_op K =>
      ktx_op (L_bind_ktx f K)
  | ktx_let K t =>
      ktx_let (L_bind_ktx f K) (L_bind_tm f t)
  | ktx_throw K t =>
      ktx_throw (L_bind_ktx f K) (L_bind_tm f t)
  | ktx_app_eff K E =>
      ktx_app_eff (L_bind_ktx f K) (L_bind_eff f E)
  | ktx_app_lbl K ℓ =>
      ktx_app_lbl (L_bind_ktx f K) (L_bind_lbl f ℓ)
  | ktx_app_tm1 K t =>
      ktx_app_tm1 (L_bind_ktx f K) (L_bind_tm f t)
  | ktx_app_tm2 K v =>
      ktx_app_tm2 (L_bind_ktx f K) (L_bind_val f v)
  end
with
L_bind_val
EV LV V L L' (f : L → lid L')
(v : val EV LV V L) {struct v} : val EV LV V L' :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_cont K => L_bind_ktx f K
  | val_md m ι => val_md (L_bind_md f m) (L_bind_lid f ι)
  | val_fix m ι => val_fix (L_bind_md f m) (L_bind_lid f ι)
  end
with
L_bind_tm
EV LV V L L' (f : L → lid L')
(t : tm EV LV V L) {struct t} : tm EV LV V L' :=
  match t with
  | tm_val v => L_bind_val f v
  | tm_op t => tm_op (L_bind_tm f t)
  | ⇧ t => ⇧ (L_bind_tm f t)
  | ⬇ t => ⬇ (L_bind_tm (L_lift_inc f) t)
  | ⇩ X t => ⇩ X (L_bind_tm f t)
  | tm_let s t => tm_let (L_bind_tm f s) (L_bind_tm f t)
  | tm_throw t s => tm_throw (L_bind_tm f t) (L_bind_tm f s)
  | tm_app_eff t E => tm_app_eff (L_bind_tm f t) (L_bind_eff f E)
  | tm_app_lbl t ℓ => tm_app_lbl (L_bind_tm f t) (L_bind_lbl f ℓ)
  | tm_app_tm t s => tm_app_tm (L_bind_tm f t) (L_bind_tm f s)
  end
.

(** Apply the substitution function [f : LV → lbl LV' L] *)

Definition
LV_bind_lbl
LV LV' L (f : LV → lbl LV' L) (ℓ : lbl LV L) : lbl LV' L :=
  match ℓ with
  | lbl_var α => f α
  | lbl_id id => lbl_id id
  end
.

Definition
LV_bind_ef
EP EV LV LV' L (f : LV → lbl LV' L) (e : ef EP EV LV L) : ef EP EV LV' L :=
  match e with
  | ef_par α => ef_par α
  | ef_var α => ef_var α
  | ef_lbl ℓ => ef_lbl (LV_bind_lbl f ℓ)
  end
.

Fixpoint
LV_bind_eff
EP EV LV LV' L (f : LV → lbl LV' L) (E : eff EP EV LV L) {struct E} : eff EP EV LV' L :=
  match E with
  | [] => []
  | e :: E' => (LV_bind_ef f e) :: (LV_bind_eff f E')
  end
.

Fixpoint
LV_bind_it
EP EV LV LV' L (f : LV → lbl LV' L) κ (N : it EP EV LV L κ) {struct N} : it EP EV LV' L κ :=
  match N with
  | it_name 𝔽 => it_name 𝔽
  | it_inst N E => it_inst (LV_bind_it f N) (LV_bind_eff f E)
  end
.

Fixpoint
LV_bind_ty
EP EV LV LV' L (f : LV → lbl LV' L) (T : ty EP EV LV L) {struct T} : ty EP EV LV' L :=
  match T with
  | 𝟙 => ty_unit
  | ty_it N ℓ => ty_it (LV_bind_it f N) (LV_bind_lbl f ℓ)
  | ty_cont T₁ E₁ T₂ E₂ =>
      ty_cont
      (LV_bind_ty f T₁) (LV_bind_eff f E₁)
      (LV_bind_ty f T₂) (LV_bind_eff f E₂)
  | ty_ms σ ℓ => ty_ms (LV_bind_ms f σ) (LV_bind_lbl f ℓ)
  end
with
LV_bind_ms
EP EV LV LV' L (f : LV → lbl LV' L) (σ : ms EP EV LV L) {struct σ} : ms EP EV LV' L :=
  match σ with
  | ms_ev σ => ms_ev (LV_bind_ms f σ)
  | ms_lv σ => ms_lv (LV_bind_ms (LV_lift_inc f) σ)
  | ms_tm T σ => ms_tm (LV_bind_ty f T) (LV_bind_ms f σ)
  | ms_res T E => ms_res (LV_bind_ty f T) (LV_bind_eff f E)
  end
.

Fixpoint
LV_bind_is
EP EV LV LV' L (f : LV → lbl LV' L) (Σ : is EP EV LV L) {struct Σ} : is EP EV LV' L :=
  match Σ with
  | is_ms σ => is_ms (LV_bind_ms f σ)
  | is_ep Σ => is_ep (LV_bind_is f Σ)
  end
.

Fixpoint
LV_bind_md
EV LV LV' V L (f : LV → lbl LV' L)
(m : md EV LV V L) {struct m} : md EV LV' V L :=
  match m with
  | md_ev m => md_ev (LV_bind_md f m)
  | md_lv m => md_lv (LV_bind_md (LV_lift_inc f) m)
  | md_tm m => md_tm (LV_bind_md f m)
  | md_res t => md_res (LV_bind_tm f t)
  end
with
LV_bind_ktx
EV LV LV' V L (f : LV → lbl LV' L)
(K : ktx EV LV V L) {struct K} : ktx EV LV' V L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (LV_bind_ktx f K) X
  | ktx_up K =>
      ktx_up (LV_bind_ktx f K)
  | ktx_op K =>
      ktx_op (LV_bind_ktx f K)
  | ktx_let K t =>
      ktx_let (LV_bind_ktx f K) (LV_bind_tm f t)
  | ktx_throw K t =>
      ktx_throw (LV_bind_ktx f K) (LV_bind_tm f t)
  | ktx_app_eff K E =>
      ktx_app_eff (LV_bind_ktx f K) (LV_bind_eff f E)
  | ktx_app_lbl K ℓ =>
      ktx_app_lbl (LV_bind_ktx f K) (LV_bind_lbl f ℓ)
  | ktx_app_tm1 K t =>
      ktx_app_tm1 (LV_bind_ktx f K) (LV_bind_tm f t)
  | ktx_app_tm2 K v =>
      ktx_app_tm2 (LV_bind_ktx f K) (LV_bind_val f v)
  end
with
LV_bind_val
EV LV LV' V L (f : LV → lbl LV' L)
(v : val EV LV V L) {struct v} : val EV LV' V L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_cont K => LV_bind_ktx f K
  | val_md m ι => val_md (LV_bind_md f m) ι
  | val_fix m ι => val_fix (LV_bind_md f m) ι
  end
with
LV_bind_tm
EV LV LV' V L (f : LV → lbl LV' L)
(t : tm EV LV V L) {struct t} : tm EV LV' V L :=
  match t with
  | tm_val v => LV_bind_val f v
  | tm_op t => tm_op (LV_bind_tm f t)
  | ⇧ t => ⇧ (LV_bind_tm f t)
  | ⬇ t => ⬇ (LV_bind_tm (L_shift_lbl ∘ f) t)
  | ⇩ X t => ⇩ X (LV_bind_tm f t)
  | tm_let s t => tm_let (LV_bind_tm f s) (LV_bind_tm f t)
  | tm_throw t s => tm_throw (LV_bind_tm f t) (LV_bind_tm f s)
  | tm_app_eff t E => tm_app_eff (LV_bind_tm f t) (LV_bind_eff f E)
  | tm_app_lbl t ℓ => tm_app_lbl (LV_bind_tm f t) (LV_bind_lbl f ℓ)
  | tm_app_tm t s => tm_app_tm (LV_bind_tm f t) (LV_bind_tm f s)
  end
.

(** Apply the substitution function [f : EV → eff EV' LV L] *)

Definition
EV_bind_ef
EP EV EV' LV L (f : EV → eff EP EV' LV L) (e : ef EP EV LV L) :
eff EP EV' LV L :=
  match e with
  | ef_par α => [ ef_par α ]
  | ef_var α => f α
  | ef_lbl ℓ => [ ef_lbl ℓ ]
  end
.

Fixpoint
EV_bind_eff
EP EV EV' LV L (f : EV → eff EP EV' LV L) (E : eff EP EV LV L) {struct E} : eff EP EV' LV L :=
  match E with
  | [] => []
  | e :: E' => (EV_bind_ef f e) ++ (EV_bind_eff f E')
  end
.

Fixpoint
EV_bind_it
EP EV EV' LV L (f : EV → eff EP EV' LV L) κ (N : it EP EV LV L κ) {struct N} : it EP EV' LV L κ :=
  match N with
  | it_name 𝔽 => it_name 𝔽
  | it_inst N E => it_inst (EV_bind_it f N) (EV_bind_eff f E)
  end
.

Fixpoint
EV_bind_ty
EP EV EV' LV L (f : EV → eff EP EV' LV L) (T : ty EP EV LV L) {struct T} : ty EP EV' LV L :=
  match T with
  | 𝟙 => ty_unit
  | ty_it N ℓ => ty_it (EV_bind_it f N) ℓ
  | ty_cont T₁ E₁ T₂ E₂ =>
      ty_cont
      (EV_bind_ty f T₁) (EV_bind_eff f E₁)
      (EV_bind_ty f T₂) (EV_bind_eff f E₂)
  | ty_ms σ ℓ => ty_ms (EV_bind_ms f σ) ℓ
  end
with
EV_bind_ms
EP EV EV' LV L (f : EV → eff EP EV' LV L) (σ : ms EP EV LV L) {struct σ} : ms EP EV' LV L :=
  match σ with
  | ms_ev σ => ms_ev (EV_bind_ms (EV_lift_inc f) σ)
  | ms_lv σ => ms_lv (EV_bind_ms (LV_shift_eff ∘ f) σ)
  | ms_tm T σ => ms_tm (EV_bind_ty f T) (EV_bind_ms f σ)
  | ms_res T E => ms_res (EV_bind_ty f T) (EV_bind_eff f E)
  end
.

Fixpoint
EV_bind_is
EP EV EV' LV L (f : EV → eff EP EV' LV L) (Σ : is EP EV LV L) {struct Σ} : is EP EV' LV L :=
  match Σ with
  | is_ms σ => is_ms (EV_bind_ms f σ)
  | is_ep Σ => is_ep (EV_bind_is (EP_shift_eff ∘ f) Σ)
  end
.

Fixpoint
EV_bind_md
EV EV' LV V L (f : EV → eff ∅ EV' LV L)
(m : md EV LV V L) {struct m} : md EV' LV V L :=
  match m with
  | md_ev m => md_ev (EV_bind_md (EV_lift_inc f) m)
  | md_lv m => md_lv (EV_bind_md (LV_shift_eff ∘ f) m)
  | md_tm m => md_tm (EV_bind_md f m)
  | md_res t => md_res (EV_bind_tm f t)
  end
with
EV_bind_ktx
EV EV' LV V L (f : EV → eff ∅ EV' LV L)
(K : ktx EV LV V L) {struct K} : ktx EV' LV V L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (EV_bind_ktx f K) X
  | ktx_up K =>
      ktx_up (EV_bind_ktx f K)
  | ktx_op K =>
      ktx_op (EV_bind_ktx f K)
  | ktx_let K t =>
      ktx_let (EV_bind_ktx f K) (EV_bind_tm f t)
  | ktx_throw K t =>
      ktx_throw (EV_bind_ktx f K) (EV_bind_tm f t)
  | ktx_app_eff K E =>
      ktx_app_eff (EV_bind_ktx f K) (EV_bind_eff f E)
  | ktx_app_lbl K ℓ =>
      ktx_app_lbl (EV_bind_ktx f K) ℓ
  | ktx_app_tm1 K t =>
      ktx_app_tm1 (EV_bind_ktx f K) (EV_bind_tm f t)
  | ktx_app_tm2 K v =>
      ktx_app_tm2 (EV_bind_ktx f K) (EV_bind_val f v)
  end
with
EV_bind_val
EV EV' LV V L (f : EV → eff ∅ EV' LV L)
(v : val EV LV V L) {struct v} : val EV' LV V L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_cont K => EV_bind_ktx f K
  | val_md m ι => val_md (EV_bind_md f m) ι
  | val_fix m ι => val_fix (EV_bind_md f m) ι
  end
with
EV_bind_tm
EV EV' LV V L (f : EV → eff ∅ EV' LV L)
(t : tm EV LV V L) {struct t} : tm EV' LV V L :=
  match t with
  | tm_val v => EV_bind_val f v
  | tm_op t => tm_op (EV_bind_tm f t)
  | ⇧ t => ⇧ (EV_bind_tm f t)
  | ⬇ t => ⬇ (EV_bind_tm (L_shift_eff ∘ f) t)
  | ⇩ X t => ⇩ X (EV_bind_tm f t)
  | tm_let s t =>
      tm_let (EV_bind_tm f s) (EV_bind_tm f t)
  | tm_throw t s => tm_throw (EV_bind_tm f t) (EV_bind_tm f s)
  | tm_app_eff t E => tm_app_eff (EV_bind_tm f t) (EV_bind_eff f E)
  | tm_app_lbl t ℓ => tm_app_lbl (EV_bind_tm f t) ℓ
  | tm_app_tm t s => tm_app_tm (EV_bind_tm f t) (EV_bind_tm f s)
  end
.

(** Apply the substitution function [f : EP → eff EP' EV LV L] *)

Definition
EP_bind_ef
EP EP' EV LV L (f : EP → eff EP' EV LV L) (e : ef EP EV LV L) :
eff EP' EV LV L :=
  match e with
  | ef_par α => f α
  | ef_var α => [ ef_var α ]
  | ef_lbl ℓ => [ ef_lbl ℓ ]
  end
.

Fixpoint
EP_bind_eff
EP EP' EV LV L (f : EP → eff EP' EV LV L) (E : eff EP EV LV L) {struct E} : eff EP' EV LV L :=
  match E with
  | [] => []
  | e :: E' => (EP_bind_ef f e) ++ (EP_bind_eff f E')
  end
.

Fixpoint
EP_bind_it
EP EP' EV LV L (f : EP → eff EP' EV LV L) κ (N : it EP EV LV L κ) {struct N} : it EP' EV LV L κ :=
  match N with
  | it_name 𝔽 => it_name 𝔽
  | it_inst N E => it_inst (EP_bind_it f N) (EP_bind_eff f E)
  end
.

Fixpoint
EP_bind_ty
EP EP' EV LV L (f : EP → eff EP' EV LV L) (T : ty EP EV LV L) {struct T} : ty EP' EV LV L :=
  match T with
  | 𝟙 => ty_unit
  | ty_it N ℓ => ty_it (EP_bind_it f N) ℓ
  | ty_cont T₁ E₁ T₂ E₂ =>
      ty_cont
      (EP_bind_ty f T₁) (EP_bind_eff f E₁)
      (EP_bind_ty f T₂) (EP_bind_eff f E₂)
  | ty_ms σ ℓ => ty_ms (EP_bind_ms f σ) ℓ
  end
with
EP_bind_ms
EP EP' EV LV L (f : EP → eff EP' EV LV L) (σ : ms EP EV LV L) {struct σ} : ms EP' EV LV L :=
  match σ with
  | ms_ev σ => ms_ev (EP_bind_ms (EV_shift_eff ∘ f) σ)
  | ms_lv σ => ms_lv (EP_bind_ms (LV_shift_eff ∘ f) σ)
  | ms_tm T σ => ms_tm (EP_bind_ty f T) (EP_bind_ms f σ)
  | ms_res T E => ms_res (EP_bind_ty f T) (EP_bind_eff f E)
  end
.

Fixpoint
EP_bind_is
EP EP' EV LV L (f : EP → eff EP' EV LV L) (Σ : is EP EV LV L) {struct Σ} : is EP' EV LV L :=
match Σ with
| is_ms σ => is_ms (EP_bind_ms f σ)
| is_ep Σ => is_ep (EP_bind_is (EP_lift_inc f) Σ)
end
.

(** Apply the substitution function [f : V → val EV LV V'] *)

Fixpoint
V_bind_md
EV LV V V' L (f : V → val EV LV V' L)
(m : md EV LV V L) {struct m} : md EV LV V' L :=
  match m with
  | md_ev m => md_ev (V_bind_md (EV_shift_val ∘ f) m)
  | md_lv m => md_lv (V_bind_md (LV_shift_val ∘ f) m)
  | md_tm m => md_tm (V_bind_md (V_lift_inc f) m)
  | md_res t => md_res (V_bind_tm (V_lift_inc f) t)
  end
with
V_bind_ktx
EV LV V V' L (f : V → val EV LV V' L)
(K : ktx EV LV V L) {struct K} : ktx EV LV V' L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (V_bind_ktx f K) X
  | ktx_up K =>
      ktx_up (V_bind_ktx f K)
  | ktx_op K =>
      ktx_op (V_bind_ktx f K)
  | ktx_let K t =>
      ktx_let (V_bind_ktx f K) (V_bind_tm (V_lift_inc f) t)
  | ktx_throw K t =>
      ktx_throw (V_bind_ktx f K) (V_bind_tm f t)
  | ktx_app_eff K E =>
      ktx_app_eff (V_bind_ktx f K) E
  | ktx_app_lbl K ℓ =>
      ktx_app_lbl (V_bind_ktx f K) ℓ
  | ktx_app_tm1 K t =>
      ktx_app_tm1 (V_bind_ktx f K) (V_bind_tm f t)
  | ktx_app_tm2 K v =>
      ktx_app_tm2 (V_bind_ktx f K) (V_bind_val f v)
  end
with
V_bind_val
EV LV V V' L (f : V → val EV LV V' L)
(v : val EV LV V L) {struct v} : val EV LV V' L :=
  match v with
  | val_unit => val_unit
  | val_var x => f x
  | val_cont K => V_bind_ktx f K
  | val_md m ι => val_md (V_bind_md f m) ι
  | val_fix m ι => val_fix (V_bind_md (V_lift_inc f) m) ι
  end
with
V_bind_tm
EV LV V V' L (f : V → val EV LV V' L)
(t : tm EV LV V L) {struct t} : tm EV LV V' L :=
  match t with
  | tm_val v => V_bind_val f v
  | tm_op t => tm_op (V_bind_tm f t)
  | ⇧ t => ⇧ (V_bind_tm f t)
  | ⬇ t => ⬇ (V_bind_tm (L_shift_val ∘ f) t)
  | ⇩ X t => ⇩ X (V_bind_tm f t)
  | tm_let s t => tm_let (V_bind_tm f s) (V_bind_tm (V_lift_inc f) t)
  | tm_throw t s => tm_throw (V_bind_tm f t) (V_bind_tm f s)
  | tm_app_eff t E => tm_app_eff (V_bind_tm f t) E
  | tm_app_lbl t ℓ => tm_app_lbl (V_bind_tm f t) ℓ
  | tm_app_tm t s => tm_app_tm (V_bind_tm f t) (V_bind_tm f s)
  end
.

Definition EV_bind_XEnv EV EV' LV
(f : EV → eff ∅ EV' LV ∅) (Ξ : XEnv EV LV) : XEnv EV' LV :=
  map (λ x,
    match x with
      (T, E) => (EV_bind_ty f T, EV_bind_eff f E)
    end
  ) Ξ.

Definition LV_bind_XEnv EV LV LV'
(f : LV → lbl LV' ∅) (Ξ : XEnv EV LV) : XEnv EV LV' :=
  map (λ x,
    match x with
      (T, E) => (LV_bind_ty f T, LV_bind_eff f E)
    end
  ) Ξ.

(** Construct substitution functions for one (or two) free variable(s). *)

Section section_substfun.
Context {EP EV LV V L : Set}.

Definition L_substfun (ID : lid L) : inc L → lid L :=
  λ α, match α with
  | VZ   => ID
  | VS β => lid_b β
  end.

Definition LV_substfun (ℓ : lbl LV L) : inc LV → lbl LV L :=
  λ α, match α with
  | VZ   => ℓ
  | VS β => lbl_var β
  end.

Definition EV_substfun (E : eff ∅ EV LV L) : inc EV → eff ∅ EV LV L :=
  λ α, match α with
  | VZ   => E
  | VS β => [ ef_var β ]
  end.

Definition EP_substfun (E : eff EP EV LV L) : inc EP → eff EP EV LV L :=
  λ α, match α with
  | VZ   => E
  | VS β => [ ef_par β ]
  end.

Definition V_substfun (v : val EV LV V L) : inc V → val EV LV V L :=
  λ x, match x with
  | VZ   => v
  | VS y => val_var y
  end.

(** Innermost bound variable is substituted by [t2]. *)
Definition V2_substfun (t1 t2 : val EV LV V L) :
    inc (inc V) → val EV LV V L :=
  λ x, match x with
  | VZ        => t2
  | VS VZ     => t1
  | VS (VS y) => val_var y
  end.

End section_substfun.

Notation L_subst_lid ι := (L_bind_lid (L_substfun ι)).
Notation L_subst_lbl ι := (L_bind_lbl (L_substfun ι)).
Notation L_subst_ef ι := (L_bind_ef (L_substfun ι)).
Notation L_subst_eff ι := (L_bind_eff (L_substfun ι)).
Notation L_subst_it ι := (L_bind_it (L_substfun ι)).
Notation L_subst_ty ι := (L_bind_ty (L_substfun ι)).
Notation L_subst_ms ι := (L_bind_ms (L_substfun ι)).
Notation L_subst_is ι := (L_bind_is (L_substfun ι)).
Notation L_subst_md ι := (L_bind_md (L_substfun ι)).
Notation L_subst_ktx ι := (L_bind_ktx (L_substfun ι)).
Notation L_subst_val ι := (L_bind_val (L_substfun ι)).
Notation L_subst_tm ι := (L_bind_tm (L_substfun ι)).

Notation LV_subst_lbl ℓ := (LV_bind_lbl (LV_substfun ℓ)).
Notation LV_subst_ef ℓ := (LV_bind_ef (LV_substfun ℓ)).
Notation LV_subst_eff ℓ := (LV_bind_eff (LV_substfun ℓ)).
Notation LV_subst_it ℓ := (LV_bind_it (LV_substfun ℓ)).
Notation LV_subst_ty ℓ := (LV_bind_ty (LV_substfun ℓ)).
Notation LV_subst_ms ℓ := (LV_bind_ms (LV_substfun ℓ)).
Notation LV_subst_is ℓ := (LV_bind_is (LV_substfun ℓ)).
Notation LV_subst_md ℓ := (LV_bind_md (LV_substfun ℓ)).
Notation LV_subst_ktx ℓ := (LV_bind_ktx (LV_substfun ℓ)).
Notation LV_subst_val ℓ := (LV_bind_val (LV_substfun ℓ)).
Notation LV_subst_tm ℓ := (LV_bind_tm (LV_substfun ℓ)).
Notation LV_subst_XEnv ℓ := (LV_bind_XEnv (LV_substfun ℓ)).

Notation EV_subst_ef E := (EV_bind_ef (EV_substfun E)).
Notation EV_subst_eff E := (EV_bind_eff (EV_substfun E)).
Notation EV_subst_it E := (EV_bind_it (EV_substfun E)).
Notation EV_subst_ty E := (EV_bind_ty (EV_substfun E)).
Notation EV_subst_ms E := (EV_bind_ms (EV_substfun E)).
Notation EV_subst_is E := (EV_bind_is (EV_substfun E)).
Notation EV_subst_md E := (EV_bind_md (EV_substfun E)).
Notation EV_subst_ktx E := (EV_bind_ktx (EV_substfun E)).
Notation EV_subst_val E := (EV_bind_val (EV_substfun E)).
Notation EV_subst_tm E := (EV_bind_tm (EV_substfun E)).
Notation EV_subst_XEnv E := (EV_bind_XEnv (EV_substfun E)).

Notation EP_subst_ef E := (EP_bind_ef (EP_substfun E)).
Notation EP_subst_eff E := (EP_bind_eff (EP_substfun E)).
Notation EP_subst_it E := (EP_bind_it (EP_substfun E)).
Notation EP_subst_ty E := (EP_bind_ty (EP_substfun E)).
Notation EP_subst_ms E := (EP_bind_ms (EP_substfun E)).
Notation EP_subst_is E := (EP_bind_is (EP_substfun E)).

Notation V_subst_md v := (V_bind_md (V_substfun v)).
Notation V_subst_ktx v := (V_bind_ktx (V_substfun v)).
Notation V_subst_val v := (V_bind_val (V_substfun v)).
Notation V_subst_tm v := (V_bind_tm (V_substfun v)).
