Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export String.

Inductive typ : Set :=
| typ_top   : typ
| typ_bot   : typ                
| typ_nat   : typ
| typ_bvar  : nat -> typ
| typ_fvar  : var -> typ
| typ_and   : typ -> typ -> typ
| typ_mu :    typ -> typ
| typ_arrow : typ -> typ -> typ
| typ_rcd : var -> typ -> typ.


Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat      
  | typ_top         => typ_top
  | typ_bot         => typ_bot                      
  | typ_bvar J      => if K === J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X 
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_and T1 T2 => typ_and (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_mu T        => typ_mu (open_tt_rec (S K) U T)
  | typ_rcd l T => typ_rcd l (open_tt_rec K U T)
  end.

(* T type U name *)
Definition open_tt T U := open_tt_rec 0 U T.

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_nat :
      type typ_nat
  | type_bot :
      type typ_bot         
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_arrow T1 T2)
  | type_and : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_and T1 T2)
  | type_rcd : forall l T,
      type T ->
      type (typ_rcd l T)
  | type_mu : forall L T,
      (forall X, X \notin L -> type (open_tt T (typ_fvar X))) ->
      type (typ_mu T).

Hint Constructors type : core.


Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bot => typ_bot               
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_and T1 T2 => typ_and (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_mu T => typ_mu (subst_tt Z U T)
  | typ_rcd l T => typ_rcd l (subst_tt Z U T)
  end.

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bot => {}               
  | typ_bvar J => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_and T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_mu T => (fv_tt T)
  | typ_rcd l T => fv_tt T
  end.

Fixpoint fl_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bot => {}               
  | typ_bvar J => {}
  | typ_fvar X => {}
  | typ_arrow T1 T2 => (fl_tt T1) `union` (fl_tt T2)
  | typ_mu T => (fl_tt T)
  | typ_rcd X T => {{ X }} `union` fl_tt T
  | typ_and T1 T2 => (fl_tt T1) `union` (fl_tt T2)
  end.

Inductive binding : Set :=
  | bind_sub : binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).
Notation empty := (@nil (atom * binding)).


Inductive WFS : env -> typ -> Prop :=
| WFS_top : forall E, WFS E typ_top
| WFS_bot : forall E, WFS E typ_bot                          
| WFS_nat : forall E, WFS E typ_nat
| WFS_fvar : forall X E,
    binds X bind_sub E ->
    WFS E (typ_fvar X)
| WFS_arrow : forall E A B,
    WFS E A ->
    WFS E B ->
    WFS E (typ_arrow A B)
| WFS_and : forall E A B,
    WFS E A ->
    WFS E B ->
    WFS E (typ_and A B)
| WFS_rcd : forall E l T,
    WFS E T ->
    WFS E (typ_rcd l T)
| WFS_rec : forall L E A,
    (forall  X, X \notin L -> 
        WFS (X ~ bind_sub ++ E) (open_tt A (typ_rcd X (open_tt A X)))) ->
      (forall  X, X \notin L -> 
        WFS (X ~ bind_sub ++ E) (open_tt A X)) ->
      WFS E (typ_mu A).


Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) ,
      wf_env E ->
      X \notin dom E ->
      wf_env (X ~ bind_sub ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      WFS E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).

Inductive toplike : env -> typ -> Prop :=  
| toplike_base : forall E,
     wf_env E ->
     toplike E typ_top
 | toplike_and : forall (T1 T2:typ) E,
     toplike E T1 ->
     toplike E T2 ->
     toplike E (typ_and T1 T2)
 | toplike_arrow : forall (A B:typ) E,
     toplike E B ->
     WFS E A ->
     toplike E (typ_arrow A B)
 | toplike_rcd : forall A E l,
     toplike E A ->
     toplike E (typ_rcd l A)
 | toplike_rec : forall (L:vars) (B:typ) E,
       ( forall X, X \notin  L  -> toplike (X ~ bind_sub ++ E) ( open_tt B X )  )  ->
       toplike E (typ_mu B).


Inductive Sub : env -> typ -> typ -> Prop :=
| S_nat: forall E,
    wf_env E ->
    Sub E typ_nat typ_nat
| S_fvar: forall E X,
    wf_env E ->
    WFS E (typ_fvar X) ->
    Sub E (typ_fvar X) (typ_fvar X)
| S_bot : forall E A,
    wf_env E ->
    WFS E A -> 
    Sub E typ_bot A        
| S_arrow: forall E A1 A2 B1 B2,
    Sub E B1 A1 ->
    Sub E A2 B2 ->
    Sub E (typ_arrow A1 A2) (typ_arrow B1 B2)
| S_and : forall E A B1 B2,
    Sub E A B1 ->
    Sub E A B2 ->
    Sub E A (typ_and B1 B2)
| S_andL : forall E A1 A2 B,
    Sub E A1 B ->
    WFS E A2 ->
    Sub E (typ_and A1 A2) B
| S_andR : forall E A1 A2 B,
    Sub E A2 B ->
    WFS E A1 ->
    Sub E (typ_and A1 A2) B
| S_rec: forall L A1 A2 E,
    (forall X,
        X \notin L -> WFS (X ~ bind_sub ++ E) (open_tt A1 X)) ->
    (forall X,
        X \notin L -> WFS (X ~ bind_sub ++ E) (open_tt A2 X)) ->
    (forall X,
        X \notin L ->
        Sub (X ~ bind_sub ++ E) (open_tt A1 (typ_rcd X (open_tt A1 X))) (open_tt A2 (typ_rcd X (open_tt A2 X)))) ->
    Sub E (typ_mu A1) (typ_mu A2)
| S_rcd : forall A B l E,
    Sub E A B ->
    Sub E (typ_rcd l A) (typ_rcd l B)             
| S_top: forall A B E,
    WFS E A ->
    toplike E B ->
    Sub E A B.

Inductive Mode := Neg | Pos.

Definition flip (m : Mode) : Mode :=
  match m with
  | Neg => Pos
  | Pos => Neg
  end.

Definition equiv E A B := Sub E A B /\ Sub E B A.

  
Inductive dis : env -> typ -> typ -> Prop :=    (* defn dis *)
 | dis_IntArr : forall (E:env) (A1 A2:typ),
     wf_env E ->
     WFS E (typ_arrow A1 A2) ->
     dis E typ_nat (typ_arrow A1 A2)
  | dis_ArrInt : forall (E:env) (A1 A2:typ),
     wf_env E ->
     WFS E (typ_arrow A1 A2) ->
     dis E (typ_arrow A1 A2) typ_nat        
  | dis_IntRec : forall (E:env) (T:typ),
     wf_env E ->
     WFS E (typ_mu T) ->
     dis E typ_nat (typ_mu T)
  | dis_RecInt : forall (E:env) (T:typ),
     wf_env E ->
     WFS E (typ_mu T) ->
     dis E (typ_mu T) typ_nat      
  | dis_ArrRec : forall (E:env) (A1 A2 T:typ),
     wf_env E ->
     WFS E (typ_arrow A1 A2) ->
     WFS E (typ_mu T) ->
     dis E (typ_arrow A1 A2) (typ_mu T)
  | dis_RecArr : forall (E:env) (A1 A2 T:typ),
     wf_env E ->
     WFS E (typ_arrow A1 A2) ->
     WFS E (typ_mu T) ->
     dis E  (typ_mu T) (typ_arrow A1 A2)        
  | dis_IntVar : forall (E:env) (X:atom),
     WFS E (typ_fvar X) ->
     wf_env E ->
     dis E typ_nat (typ_fvar X)
  | dis_VarInt : forall (E:env) (X:atom),
     WFS E (typ_fvar X) ->
     wf_env E ->
     dis E (typ_fvar X) typ_nat         
 | dis_ArrVar : forall (E:env) (A1 A2:typ) (X:atom),
     wf_env E ->
     WFS E (typ_fvar X) ->
     WFS E (typ_arrow A1 A2) ->
     dis E (typ_arrow A1 A2) (typ_fvar X)
  | dis_VarArr : forall (E:env) (A1 A2:typ) (X:atom),
     wf_env E ->
     WFS E (typ_fvar X) ->
     WFS E (typ_arrow A1 A2) ->
     dis E (typ_fvar X) (typ_arrow A1 A2)        
 | dis_RecVar : forall (E:env) (T:typ) (X:atom),
     wf_env E ->
     WFS E (typ_fvar X) ->
     WFS E (typ_mu T) ->
     dis E (typ_mu T) (typ_fvar X)
 | dis_VarRec : forall (E:env) (T:typ) (X:atom),
     wf_env E ->
     WFS E (typ_fvar X) ->
     WFS E (typ_mu T) ->
     dis E (typ_fvar X) (typ_mu T)         
 | dis_IntRcd: forall E A X,
     wf_env E ->
     WFS E (typ_rcd X A) ->
     dis E typ_nat (typ_rcd X A)
 | dis_RcdInt: forall E A X,
     wf_env E ->
     WFS E (typ_rcd X A) ->
     dis E (typ_rcd X A) typ_nat            
 | dis_ArrRcd: forall E A X B1 B2,
     wf_env E ->
     WFS E (typ_rcd X A) ->
     WFS E (typ_arrow B1 B2) ->
     dis E (typ_arrow B1 B2) (typ_rcd X A)
 | dis_RcdArr: forall E A X B1 B2,
     wf_env E ->
     WFS E (typ_rcd X A) ->
     WFS E (typ_arrow B1 B2) ->
     dis E (typ_rcd X A) (typ_arrow B1 B2)         
 | dis_RecRcd: forall E A X B,
     wf_env E ->
     WFS E (typ_rcd X A) ->
     WFS E (typ_mu B) ->
     dis E (typ_mu B) (typ_rcd X A)
 | dis_RcdRec: forall E A X B,
     wf_env E ->
     WFS E (typ_rcd X A) ->
     WFS E (typ_mu B) ->
     dis E (typ_rcd X A) (typ_mu B)           
 | dis_RcdVar: forall E A X Y,
     wf_env E ->
     WFS E (typ_rcd X A) ->
     WFS E (typ_fvar Y) ->
     dis E (typ_rcd X A) (typ_fvar Y)
 | dis_VarRcd: forall E A X Y,
     wf_env E ->
     WFS E (typ_rcd X A) ->
     WFS E (typ_fvar Y) ->
     dis E (typ_fvar Y) (typ_rcd X A)        
 | dis_topL : forall (E:env) (A B:typ) ,
     wf_env E ->
     WFS E A ->
     toplike E B ->
     dis E A B
 | dis_topR : forall (E:env) (A B:typ) ,
     wf_env E ->
     WFS E B ->
     toplike E A ->
     dis E A B         
 | dis_andL : forall (E:env) (A1 A2 B:typ),
     dis E A1 B ->
     dis E A2 B ->
     dis E (typ_and A1 A2) B
 | dis_andR : forall (E:env) (A B1 B2:typ),
     dis E A B1 ->
     dis E A B2 ->
     dis E A (typ_and B1 B2)
 | dis_VarVar : forall (E:env) (X1 X2:atom),
     wf_env E ->
     WFS E (typ_fvar X1) ->
     WFS E (typ_fvar X2) ->
     X1 <> X2 ->
     dis E (typ_fvar X1) (typ_fvar X2)
 | dis_ArrArr : forall (E:env) (A1 A2 B1 B2:typ),
     WFS E A1 ->
     WFS E B1 ->
     dis E A2 B2 ->
     dis E (typ_arrow A1 A2) (typ_arrow B1 B2)
 | dis_RcdRcd: forall E A X B Y,
     X <> Y ->
     WFS E A ->
     WFS E B ->
     wf_env E ->
     dis E (typ_rcd X A) (typ_rcd Y B)
 | dis_RcdRcdEq: forall E A X B,
     dis E A B ->
     dis E (typ_rcd X A) (typ_rcd X B)  
 | dis_RecRec : forall L E A1 A2,
     ( forall X , X \notin L -> WFS ([(X, bind_sub)] ++ E) (open_tt A1 X)) ->
     ( forall X , X \notin L -> WFS ([(X, bind_sub)] ++ E) (open_tt A2 X)) -> 
     ( forall  X , X \notin  L  ->  dis ((X ~ bind_sub) ++ E) (open_tt A1 X) (open_tt A2 X)) ->
     dis E (typ_mu A1) (typ_mu A2).



Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : typ => fl_tt x) in
  constr:(A `union` B `union`  E  \u F \u G).


Hint Constructors Sub WFS   wf_env toplike   dis: core.





(* ********************************************************************** *)
(** ** Properties of type substitution in types *)

(** The next lemma is the strengthened induction hypothesis for the
    lemma that follows, which states that opening a locally closed
    term is the identity.  This lemma is not otherwise independently
    useful. *)

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with congruence || eauto.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
    destruct (j === n)... destruct (i === n)...
Qed.

(** Opening a locally closed term is the identity.  This lemma depends
    on the immediately preceding lemma. *)

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  unfold open_tt in *.
  pick fresh X.
  apply open_tt_rec_type_aux with (j:=0) (V:=(typ_fvar X))...
Qed.

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt T ->
   T = subst_tt Z U T.
Proof with auto.
  induction T; simpl; intro H; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
    contradict H; fsetdec.
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "typ_bvar".
    destruct (k === n); subst...
  Case "typ_fvar".
    destruct (a == X); subst... apply open_tt_rec_type...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with congruence || auto.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (Y == X)...
Qed.

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (typ_fvar X) T2).
Proof with congruence || auto.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "typ_bvar".
    destruct (k === n)... simpl. destruct (X == X)...
  Case "typ_fvar".
    destruct (a == X)... contradict Fr; fsetdec.
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.

Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T).
Proof with auto.
  intros Z P T HT HP.
  induction HT; simpl...
  destruct (X == Z)...
  pick fresh Y.
  apply type_mu with (L:=L \u {{Z}})...
  intros.
  rewrite subst_tt_open_tt_var...
Qed.



(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy for automatically
    discharging local-closure proof obligations. *)

Hint Resolve subst_tt_type  : core.

(** We also add as hints the lemmas concerning [body_e]. *)


(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the MetatheoryEnv library. *)





Definition relation (X:Type) := X -> X -> Prop.

Section Star.

  Variable A : Type.
  Variable R : relation A.

  Inductive star: relation A:=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

  Lemma star_one:
    forall a b, R a b -> star a b.
  Proof.
    eauto using star.
  Qed.

  Lemma star_trans:
    forall a b, star a b -> forall c, star b c -> star a c.
  Proof.
    induction 1; eauto using star.
  Qed.


  Hypothesis R_functional:
    forall a b c, R a b -> R a c -> b = c.

  Lemma star_star_inv:
    forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
  Proof.
    induction 1; intros.
    - auto.
    - inversion H1; subst.
      + right. eauto using star.
      + assert (b = b0) by (eapply R_functional; eauto). subst b0.
        apply IHstar; auto.
  Qed.

  Definition irred a : Prop := forall b, ~(R a b).

  Lemma finseq_unique:
    forall a b,
      star a b -> irred b -> forall b',
      star a b' -> irred b' ->
      b = b'.
  Proof.
    intros a b s.
    induction s; intros; eauto.
    unfold irred in H.
    destruct H0; eauto.
    assert (not (R a b)) by eauto.
    contradiction.
    destruct H1.
    unfold irred in H2.
    assert (not (R a b)) by eauto.
    contradiction.
    eapply IHs; eauto.
    assert (b = b0).
    apply R_functional with (a:=a).
    apply H.
    apply H1.
    subst.
    auto.
  Qed.

End Star.

