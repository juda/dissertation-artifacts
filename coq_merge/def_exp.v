Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export def_typ.


Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> typ -> exp
  | exp_app : exp -> exp -> exp
  | exp_nat : exp
  | exp_top : exp
  | exp_fix : typ -> exp -> exp
  | exp_unfold : typ -> exp -> exp
  | exp_fold : typ -> exp -> exp
  | exp_anno : exp -> typ -> exp
  | exp_merge : exp -> exp -> exp
  | exp_rcd : var -> exp -> exp
  | exp_proj : exp -> var -> exp
.


Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.


Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs A e1 B => exp_abs A (open_ee_rec (S k) f e1) B
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_nat => exp_nat
  | exp_top => exp_top
  | exp_fix T e1 => exp_fix T (open_ee_rec (S k) f e1)               
  | exp_unfold T e1 => exp_unfold T (open_ee_rec k f e1)
  | exp_fold T e1 => exp_fold T (open_ee_rec k f e1)
  | exp_anno e1 T => exp_anno (open_ee_rec k f e1) T
  | exp_merge e1 e2 => exp_merge (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_rcd l e => exp_rcd l (open_ee_rec k f e)
  | exp_proj e l => exp_proj (open_ee_rec k f e) l                             
  end.

Notation open_ee e1 e2     := (open_ee_rec 0 e2 e1).

Fixpoint subst_ee (y:atom) (u:exp) (e:exp) {struct e} : exp :=
  match e with
  | (exp_bvar n)   => exp_bvar n
  | (exp_fvar x)   => (if x == y then u else (exp_fvar x))
  | (exp_abs A e1 B)    => exp_abs A (subst_ee y u e1) B
  | (exp_app e1 e2) => exp_app (subst_ee y u e1) (subst_ee y u e2)
  | exp_nat => exp_nat
  | exp_top => exp_top
  | exp_fix T e1 => exp_fix T (subst_ee y u e1)               
  | exp_unfold T e => exp_unfold T (subst_ee y u e)
  | exp_fold T e => exp_fold T (subst_ee y u e)
  | exp_anno e1 T => exp_anno (subst_ee y u e1) T
  | exp_merge e1 e2 => exp_merge (subst_ee y u e1) (subst_ee y u e2)
  | exp_rcd l e => exp_rcd l (subst_ee y u e)
  | exp_proj e l => exp_proj (subst_ee y u e)  l                    
  end.


Fixpoint fv_ee (e_5:exp) : vars :=
  match e_5 with
  | (exp_bvar nat)   => {}
  | (exp_fvar x)   => {{x}}
  | (exp_abs A e B)     => fv_ee e
  | (exp_app e1 e2) => fv_ee e1 \u fv_ee e2
  | exp_nat => {}
  | exp_top => {}
  | exp_fix T e1 => fv_ee e1
  | exp_unfold T e => fv_ee e
  | exp_fold T e => fv_ee e
  | exp_anno e T => fv_ee e
  | exp_merge e1 e2 => fv_ee e1 \u fv_ee e2
  | exp_rcd l e => fv_ee e
  | exp_proj e l => fv_ee e                       
  end.


Inductive expr : exp -> Prop :=
 | lc_fvar : forall (x:var),
     expr (exp_fvar x)
 | lc_abs : forall (e:exp) L A B,
     (forall x, x \notin L -> expr (open_ee e (exp_fvar x)))  ->
     type A ->
     type B ->
     expr (exp_abs A e B)
 | lc_app : forall (e1 e2:exp),
     expr e1 ->
     expr e2 ->
     expr (exp_app e1 e2)
 | lc_nat :
     expr exp_nat
 | lc_top:
     expr exp_top
 | lc_fix: forall e L T,
     (forall x, x \notin L -> expr (open_ee e (exp_fvar x)))  ->
     type T ->
     expr (exp_fix T e)
 | lc_unfold: forall T e,
     type T ->
     expr e ->
     expr (exp_unfold T e)
 | lc_fold: forall T e,
     expr e ->
     type T ->
     expr (exp_fold T e)
 | lc_anno : forall T e,
     type T ->
     expr e ->
     expr (exp_anno e T)
 | lc_merge : forall e1 e2,
     expr e1 ->
     expr e2 ->
     expr (exp_merge e1 e2)
 | lc_rcd: forall e l,
     expr e ->
     expr (exp_rcd l e)
 | lc_proj: forall e l,
     expr e ->
     expr (exp_proj e l)
.


Inductive ord : typ -> Prop :=    (* defn ord *)
 | ord_nat : 
     ord typ_nat
 | ord_top : 
     ord typ_top
 | ord_bot : 
     ord typ_bot        
 | ord_arr : forall (A B:typ) ,
     ord (typ_arrow A B)
 | ord_rec : forall (T:typ) ,
     ord (typ_mu T)
 | ord_rcd : forall l A,
     ord (typ_rcd l A)
 | ord_var : forall (X:atom),
     ord (typ_fvar X)
.

Inductive value : exp -> Prop :=
  | value_abs : forall t1 A B , 
      expr (exp_abs A t1 B) ->
      value (exp_abs A t1 B)
  | value_nat:
      value exp_nat
  | value_top:
      value exp_top
  | value_fold: forall T e,
      value e ->
      type T ->
      value (exp_fold T e)
  | value_merge : forall e1 e2,
      value e1 ->
      value e2 ->
      value (exp_merge e1 e2)
  | value_rcd: forall l e,
      value e ->
      value (exp_rcd l e)
.


Inductive typ_reduce : exp -> typ -> exp -> Prop :=    (* defn typ_reduce *)
 | tred_nat : 
     typ_reduce exp_nat typ_nat exp_nat
 | tred_top : forall (e:exp) A,
     expr e ->
     ord A ->
     toplike empty A ->
     typ_reduce e A exp_top
 | tred_rec : forall (A:typ) (e:exp) (B:typ),
     expr e ->
     ~ toplike empty (typ_mu B)   ->
     Sub empty  (typ_mu A)   (typ_mu B)  ->
     typ_reduce (exp_fold (typ_mu A) e) (typ_mu B) (exp_fold (typ_mu B) e)               
 | tred_arrow : forall (e:exp) (A1 A2 B2 B1:typ),
     expr (exp_abs A1 e A2) ->
      ~ toplike empty B2  ->
      Sub empty  A2   B2  ->
      Sub empty B1 A1 ->
     typ_reduce (exp_abs A1 e A2) (typ_arrow B1 B2) (exp_abs A1 e B2)
 | tred_and : forall (e:exp) (A B:typ) (e1 e2:exp),
     typ_reduce e A e1 ->
     typ_reduce e B e2 ->
     typ_reduce e (typ_and A B) (exp_merge e1 e2)
 | tred_mergeL : forall (e1 e2:exp) (T:typ) (e:exp),
     expr e2 ->
     typ_reduce e1 T e ->
     ord T ->
     typ_reduce (exp_merge e1 e2) T e
 | tred_mergeR : forall (e1 e2:exp) (T:typ) (e:exp),
     expr e1 ->
     typ_reduce e2 T e ->
     ord T ->
     typ_reduce (exp_merge e1 e2) T e
 | tred_rcd: forall e1 e2 T l,
     typ_reduce e1 T e2 ->
     ~ toplike empty (typ_rcd l T) ->
     typ_reduce (exp_rcd l e1) (typ_rcd l T) (exp_rcd l e2)
.


Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

Inductive appTyp : typ -> typ -> Prop :=   
 | AT_arr : forall (A B:typ),
     appTyp (typ_arrow A B) (typ_arrow A B)
 | AT_toparr : 
     appTyp typ_top (typ_arrow typ_top typ_top)
 | AT_rcd: forall A l,
     appTyp (typ_rcd l A) (typ_rcd l A)
 | AT_toprcd: forall l,
     appTyp typ_top (typ_rcd l typ_top)
.


Inductive RSub : env -> typ -> typ -> Prop :=
| RS_self: forall E A,
    WFS E A ->
    wf_env E ->
    RSub E A A
| RS_arrow: forall E A1 A2 B1 B2,
    Sub E B1 A1 ->
    RSub E A2 B2 ->
    RSub E (typ_arrow A1 A2) (typ_arrow B1 B2)
| RS_and : forall E A1 A2 B1 B2,
    RSub E A1 B1 ->
    RSub E A2 B2 ->
    RSub E (typ_and A1 A2) (typ_and B1 B2)
| RS_rcd: forall E A B l,
    RSub E A B ->
    RSub E (typ_rcd l A) (typ_rcd l B)
| RS_top: forall A E,
    toplike E A ->
    RSub E typ_top A
.


Inductive typing : env -> exp -> dirflag -> typ -> Prop :=
| typing_nat : forall G,
    wf_env G ->
    typing G exp_nat Inf typ_nat
| typing_top : forall G,
    wf_env G ->
    typing G exp_top Inf typ_top
| typing_var : forall (G:env) (x:var) (T:typ),
    wf_env G ->
    binds x (bind_typ T) G  ->
    typing G (exp_fvar x) Inf T
| typing_anno: forall G e A ,
    typing G e Chk A ->
    typing G (exp_anno e A) Inf A
 | typing_abs : forall (L:vars) (G:env) e A B ,
     (forall x , x \notin L -> typing ((x ~ bind_typ A) ++ G) (open_ee e x) Chk B)  ->
     typing G (exp_abs A e B) Inf (typ_arrow A B)
 | typing_app : forall (G:env) (e1 e2:exp) (C T2 T1:typ),
     typing G e1 Inf C ->
     appTyp C (typ_arrow T1 T2) ->
     typing G e2 Chk T1 ->
     typing G (exp_app e1 e2) Inf T2
 | typing_fix: forall (L:vars) (G:env) e A ,
     (forall x , x \notin L -> typing ((x ~ bind_typ A) ++ G) (open_ee e x) Chk A)  ->
     typing G (exp_fix A e ) Inf A
 | typing_fold : forall G A e,
     typing G e Chk (open_tt A  (typ_mu A))    ->
     WFS G (typ_mu A) ->
     typing G (exp_fold (typ_mu A) e) Inf (typ_mu A)
 | typing_merge : forall G e1 e2 A B ,
     typing G e1 Inf A ->
     typing G e2 Inf B ->
     dis G A B ->
     typing G (exp_merge e1 e2) Inf (typ_and A B)
 | typing_mergev : forall G A e1 e2 B,
     value e1 ->
     value e2 ->
     wf_env G ->
     typing nil e1 Inf A ->
     typing nil e2 Inf B ->
     (forall T e3 e4, typ_reduce e1 T e3 -> typ_reduce e2 T e4 -> e3 = e4 ) ->
     typing G (exp_merge e1 e2) Inf (typ_and A B)
 | typing_unfold : forall G T e ,
     typing G e Chk (typ_mu T) ->
     typing G (exp_unfold (typ_mu T) e) Inf (open_tt T  (typ_mu T))
 | typing_rcd : forall e A G l,
     typing G e Inf A ->
     typing G (exp_rcd l e) Inf (typ_rcd l A)
 | typing_proj : forall e A G l C,
     typing G e Inf A ->
     appTyp A (typ_rcd l C) ->
     typing G (exp_proj e l) Inf C
 | typing_sub: forall G e A B,
     typing G e Inf A ->
     Sub G A B ->
     typing G e Chk B
.




Inductive step : exp -> exp -> Prop :=
| step_top : forall e,
    value e ->
    step (exp_app exp_top e) exp_top
 | step_beta : forall (e e1 e2:exp) A B,
     expr (exp_abs A e B) ->
     value e2 ->
     value e1 ->
     typ_reduce e1 A e2 ->
     step (exp_app  (exp_abs A e B) e1)  (exp_anno (open_ee e e2) B)
 | step_app1 : forall (e1 e2 e1':exp),
     expr e2 ->
     step e1 e1' ->
     step (exp_app e1 e2) (exp_app e1' e2)
 | step_app2 : forall v1 e2 e2',
     value v1 ->
     step e2 e2' ->
     step (exp_app v1 e2) (exp_app v1 e2')
 | step_mergel: forall e1 e2 e1',
     expr e2 ->
     step e1 e1' ->
     step (exp_merge e1 e2) (exp_merge e1' e2)
 | step_merger: forall e1 e2 e2',
     value e1 ->
     step e2 e2' ->
     step (exp_merge e1 e2) (exp_merge e1 e2')
 | step_anno: forall e A e',
     step e e' ->
     type A ->
     step (exp_anno e A) (exp_anno e' A)
 | step_annov: forall e A e',
     value e ->
     typ_reduce e A e' ->
     step (exp_anno e A) e'
 | step_fix: forall e A,
     expr (exp_fix A e) ->
     step (exp_fix A e) (exp_anno (open_ee e (exp_fix A e)) A)
 | step_fld: forall A B e1 e2 ,
     value e1 ->
     typ_reduce e1 (open_tt A (typ_mu A)) e2 ->
     type (typ_mu B) ->
     ~ toplike empty (typ_mu A) ->
     step (exp_unfold (typ_mu A) (exp_fold (typ_mu B) e1)) e2
 | step_fldm: forall A  e1 e2 e,
     value e1 -> value e2 ->
     typ_reduce (exp_merge e1 e2)  (typ_mu A) e ->
     ~ toplike empty (typ_mu A) ->
     step (exp_unfold (typ_mu A) (exp_merge e1 e2)) (exp_unfold (typ_mu A) e)
 | step_fldt: forall A  e1 ,
     value e1 ->
     typ_reduce e1 (typ_mu A) exp_top ->
     toplike empty (typ_mu A) ->
     step (exp_unfold (typ_mu A) e1) exp_top        
 | step_fold: forall e e' T,
     step e e' ->
     type T ->
     step (exp_fold T e) (exp_fold T e')
 | step_unfold: forall e e' T,
     step e e' ->
     type T ->
     step (exp_unfold T e) (exp_unfold T e')
 | step_rcd: forall e e' l,
     step e  e' ->
     step (exp_rcd l e) (exp_rcd l e')
 | step_proj: forall e e' l,
     step e e' ->
     step (exp_proj e l) (exp_proj e' l)
 | step_projtop : forall l,
     step (exp_proj exp_top l) exp_top
 | step_projrcd: forall e l,
     value e ->
     step (exp_proj (exp_rcd l e) l) e         
.

                    


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let D := gather_atoms_with (fun x : exp => fv_ee x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : typ => fl_tt x) in
  constr:(A `union` B `union`  E  \u D \u F \u G).


Hint Constructors expr ord value typ_reduce typing step appTyp RSub: core.


(* ********************************************************************** *)
(** ** Properties of expression substitution in expressions *)

(** This section follows the structure of the previous two sections. *)

Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof with congruence || eauto.
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...
  Case "exp_bvar".
    destruct (j===n)... destruct (i===n)...
Qed.


Lemma open_ee_rec_expr : forall u e k,
  expr e ->
  e = open_ee_rec k u e.
Proof with auto.
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := exp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_fvar X);
    auto
      ].
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_ee e ->
  e = subst_ee x u e.
Proof with auto.
  intros x u e; induction e; simpl; intro H; f_equal...
  Case "exp_fvar".
    destruct (a==x)...
    contradict H; fsetdec.
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  expr u ->
  subst_ee x u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x u e2) (subst_ee x u e1).
Proof with auto.
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n); subst...
  Case "exp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x u e) y = subst_ee x u (open_ee e y).
Proof with congruence || auto.
  intros x y u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
Qed.



Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_ee e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (exp_fvar x) e).
Proof with congruence || auto.
  induction e; intros u k Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (k === n)... simpl. destruct (x == x)...
  Case "exp_fvar".
    destruct (a == x)... contradict Fr; fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u,
  x `notin` fv_ee e ->
  open_ee e u = subst_ee x u (open_ee e x).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.


Lemma subst_ee_expr : forall z e1 e2,
  expr e1 ->
  expr e2 ->
  expr (subst_ee z e2 e1).
Proof with auto.
  intros z e1 e2 He1 He2.
  induction He1; simpl; auto;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton z);
    intros;
    try rewrite subst_ee_open_ee_var;
    try rewrite subst_ee_open_te_var;
    instantiate;
    auto
  ].
  Case "expr_var".
    destruct (x == z)...
Qed.


Hint Resolve  subst_ee_expr : core.
