Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Export disjoint.
Require Export def_exp.


Definition consistencySpec v1 v2 :=
  forall T v1' v2', typ_reduce v1 T v1' -> typ_reduce v2 T v2' -> v1' = v2'.

Lemma value_lc_expr: forall v,
    value v -> expr v.
Proof with auto.
  intros.
  induction H...
Qed.  

Lemma tred_regular_type: forall v A t,
    typ_reduce v A t -> WFS empty A.
Proof with auto.
  intros.
  induction H;try solve [get_well_form;auto]...
Qed.    

Lemma typing_chk2inf: forall G v A,
    typing G v Chk A -> exists B, typing G v Inf B /\ Sub G B A.
Proof with auto.
  intros G v A Typ.
  dependent induction Typ...
  exists A...
Qed.

Lemma typing_chk_sub: forall G e A B,
    typing G e Chk A -> Sub G A B -> typing G e Chk B.
Proof with auto.
  intros...
  dependent induction H...
  apply typing_sub with (A:=A)...
  apply Transitivity with (B:=B0)...
Qed.

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  WFS E U.
Proof with auto.
  induction 1; intros J; analyze_binds J...
  apply IHwf_env in BindsTac.
  rewrite_alist (nil ++ [(X, bind_sub)] ++ E).
  apply WFS_weakening...
  injection BindsTacVal; intros; subst...
  rewrite_alist (nil ++ [(x0, bind_typ T)] ++ E).
  apply WFS_weakening...
  rewrite_alist (nil ++ [(x0, bind_typ T)] ++ E).
  apply WFS_weakening...
Qed.



Lemma typing_regular : forall E e dir T,
  typing E e dir T ->
  wf_env E /\ expr e /\ WFS E T.
Proof with auto.
  intros.
  induction H;destruct_hypos...
  - (* var *)
    repeat split...
    apply wf_typ_from_binds_typ with (x:=x)...
  - (* anno *)
    repeat split...
    constructor...
    get_type...
  - (* arrow *)
    repeat split...
    +
      pick fresh X.
      specialize_x_and_L X L.
      destruct_hypos.    
      inversion H0...
    +
      apply lc_abs with (L:=L)...
      intros.
      eapply H0...
      pick fresh X.
      specialize_x_and_L X L.
      destruct_hypos.
      dependent destruction H0...
      get_type...
      pick fresh X.
      specialize_x_and_L X L.
      destruct_hypos.
      get_type...
    +
      pick fresh X.
      specialize_x_and_L X L.
      destruct_hypos.
      constructor...
      dependent destruction H0...
      add_nil.
      apply WFS_strengthening with (X:=X) (m:=bind_typ A)...
  - (* app *)
    dependent destruction H0.
    dependent destruction H7...
    repeat split...
  - (* fix *)
    repeat split...
    +
      pick fresh X.
      specialize_x_and_L X L.
      destruct_hypos.
      dependent destruction H0...
    +
      apply lc_fix with (L:=L)...
      intros.
      eapply H0...
      pick fresh X.
      specialize_x_and_L X L.
      destruct_hypos.
      get_type...
    +
      pick fresh X.
      specialize_x_and_L X L.
      destruct_hypos.
      dependent destruction H0...
  - (* fold *)
    repeat split...
    constructor...
    get_type...
  - (* merge *)
    repeat split...
    rewrite_alist (nil ++ G ++ nil).
    apply WFS_weakening...
  - (* unfold *)
    repeat split...
    constructor...
    get_type...
    dependent destruction H2.
    pick fresh X.
    rewrite subst_tt_intro with (X:=X)...
    add_nil.
    apply subst_tt_wfs3...
    apply H3...
    apply WFS_rec with (L:=L)...
  - (* proj *)
    repeat split...
    dependent destruction H0...
    dependent destruction H3...    
  - (* sub *)
    repeat split...
    get_well_form...
Qed.


Lemma tred_regular : forall v1 T v2,
    typ_reduce v1 T v2 -> expr v1 /\ expr v2 /\ WFS empty T.
Proof with auto.
  intros.
  dependent induction H;destruct_hypos...
  -
    get_well_form...
  -
    repeat split;try constructor...
    get_type...
    get_type...
    get_well_form...
  -
    repeat split...
    dependent destruction H.
    apply lc_abs with (L:=L)...
    get_type...
    constructor;get_well_form...
Qed.

Lemma bind_type_notin: forall G,
    wf_env G ->
    forall x m,
      x `notin` dom G ->
      binds x m G -> False.
Proof with auto.
  intros G H.
  induction H;intros...
  -
    analyze_binds H2.
    apply IHwf_env with (x:=x) (m:=m)...
  -
    analyze_binds H3.
    apply IHwf_env with (x:=x0) (m:=m)...
Qed.  

  
Lemma bind_type_uniq: forall G ,
    wf_env G ->
    forall x T S ,
    binds x (bind_typ T) G ->
    binds x (bind_typ S) G ->
    T = S.
Proof with auto.
  intros G H...
  induction H;intros...
  -
    analyze_binds H...
  -
    analyze_binds H1...
    analyze_binds H2...
    apply IHwf_env with (x:=x)...
  -
    analyze_binds H2...
    +
      analyze_binds H3...
      inversion BindsTacVal0...
      inversion BindsTacVal...
      apply bind_type_notin with (x:=x) (m:=bind_typ S) in H...
      destruct H.
    +
      analyze_binds H3...
      apply bind_type_notin with (x:=x) (m:=bind_typ T0) in H...
      destruct H.
      apply IHwf_env with (x:=x0)...
Qed.


Lemma RSub_regular: forall E A B,
    RSub E A B -> WFS E A /\ WFS E B /\ wf_env E.
Proof with auto.
  intros.
  induction H;get_well_form;destruct_hypos...
Qed.


Ltac get_well_form :=
    repeat match goal with
           | [ H : Sub _ _ _ |- _ ] => apply sub_regular in H;destruct_hypos
           | [ H : RSub _ _ _ |- _ ] => apply RSub_regular in H;destruct_hypos
           | [ H : toplike _ _ |- _ ] => apply toplike_regular in H;destruct_hypos                            | [ H : dis _ _ _ |- _ ] => apply dis_regular in H;destruct_hypos
           | [ H : typing _ _ _ _ |- _ ] => apply typing_regular in H;destruct_hypos                          | [ H : typ_reduce _ _ _ |- _ ] => apply tred_regular in H;destruct_hypos
           end.



Lemma typing_weakening: forall G1 G2 G3 e dir A,
    typing (G1 ++ G3) e dir A ->
    wf_env (G1 ++ G2 ++ G3) ->
    WFS (G1 ++ G2 ++ G3) A ->
    typing (G1 ++ G2 ++ G3) e dir A.
Proof with auto.
  intros.
  generalize dependent G2.
  dependent induction H;intros...
  - (* abs *)
    dependent destruction H2.
    apply typing_abs with (L:=L \u dom (G1 ++ G2 ++ G3))...
    intros.
    rewrite_alist (([(x, bind_typ A)] ++ G1) ++ G2 ++ G3).
    apply H0...
    rewrite_alist ([(x, bind_typ A)] ++ G1 ++ G2 ++ G3)...
    rewrite_alist (nil ++ [(x, bind_typ A)] ++ (G1 ++ G2 ++ G3))...
    apply WFS_weakening...
  - (* app *)
    apply typing_app with (C:=C) (T1:=T1)...
    apply IHtyping1...
    dependent destruction H0...
    constructor...
    get_well_form.
    apply WFS_weakening...
    apply IHtyping2...
    get_well_form.
    apply WFS_weakening...
  - (* fix *)
    apply typing_fix with (L:=L \u dom (G1 ++ G2 ++ G3))...
    intros.
    rewrite_alist (([(x, bind_typ A)] ++ G1) ++ G2 ++ G3).
    apply H0...
    rewrite_alist ([(x, bind_typ A)] ++ G1 ++ G2 ++ G3)...
    rewrite_alist (nil ++ [(x, bind_typ A)] ++ (G1 ++ G2 ++ G3))...
    apply WFS_weakening...
  - (* fold *)
    dependent destruction H.
    apply typing_fold with (A:=A)...
    apply IHtyping...
    get_well_form.
    apply WFS_weakening...
  - (* merge *)
    dependent destruction H3.
    apply typing_merge...
    apply dis_weakening...
  - (* unfold *)
    apply typing_unfold...
    apply IHtyping...
    get_well_form...
    apply WFS_weakening...
  - (* rcd *)
    apply typing_rcd...
    apply IHtyping...
    get_well_form...
    apply WFS_weakening...
  - (* proj *)
    apply typing_proj with (A:=A)...
    apply IHtyping...
    get_well_form...
    apply WFS_weakening...
  - (* sub *)
    apply typing_sub with (A:=A)...
    apply IHtyping...
    get_well_form.
    apply WFS_weakening...
    apply Sub_weakening...
Qed.    

Lemma appTyp_arrow_unique: forall A B1 B2 C1 C2,
    appTyp A (typ_arrow B1 B2) -> appTyp A (typ_arrow C1 C2) -> B1 = C1 /\ B2 = C2.
Proof with auto.
  intros.
  dependent induction H;dependent induction H0...  
Qed.

Lemma appTyp_rcd_unique: forall A l B2 C2,
    appTyp A (typ_rcd l B2) -> appTyp A (typ_rcd l C2) -> B2 = C2.
Proof with auto.
  intros.
  dependent induction H;dependent induction H0...  
Qed.

Lemma inference_unique_aux : forall G e A1 A2,
    typing empty e Inf A1 ->
    typing G e Inf A2 ->
    A1 = A2.
Proof with auto.
  intros.
  generalize dependent A2.
  dependent induction H;intros;try solve [dependent destruction H0;auto|dependent destruction H1;auto]...
  - (* var *)
    analyze_binds H0...
  - (* app *)
    dependent destruction H2...
    assert (C = C0).
    apply IHtyping1...
    subst.
    apply appTyp_arrow_unique with (C1:=T3) (C2:=T0) in H0...
    inversion H0...
  - (* merge *)
    dependent destruction H2...
    +
      f_equal...
    +
      f_equal...
      apply IHtyping1...
      rewrite_alist (nil ++ G ++ nil).
      apply typing_weakening...
      rewrite_alist (nil ++ G++empty) in H4...    
      get_well_form...
      apply WFS_weakening...
      apply IHtyping2...
      rewrite_alist (nil ++ G ++ nil).
      apply typing_weakening...
      rewrite_alist (nil ++ G++empty) in H4...    
      get_well_form...
      apply WFS_weakening...
  - (* mergev *)
    dependent destruction H5...
    +
      f_equal...
    +
      f_equal...
      apply IHtyping1...
      rewrite_alist (nil ++ G ++ nil).
      apply typing_weakening...
      rewrite_alist (nil ++ G++empty) in H7...    
      get_well_form...
      apply WFS_weakening...
      apply IHtyping2...
      rewrite_alist (nil ++ G ++ nil).
      apply typing_weakening...
      rewrite_alist (nil ++ G++empty) in H7...    
      get_well_form...
      apply WFS_weakening...
  - (* rcd *)
    dependent destruction H0...
    f_equal.
    apply IHtyping...
  - (* proj *)
    dependent destruction H1...
    assert (A=A0).
    apply IHtyping...
    subst.
    apply appTyp_rcd_unique with (C2:=C0) in H0...
Qed.
    



    
Lemma inference_unique : forall G e A1 A2,
    typing G e Inf A1 ->
    typing G e Inf A2 ->
    A1 = A2.
Proof with auto.
  intros.
  generalize dependent A2.
  dependent induction H;intros;try solve [dependent destruction H0;auto|dependent destruction H1;auto]...
  - (* var *)
    dependent destruction H1...
    apply bind_type_uniq with (G:=G) (x:=x)...
  - (* app *)
    dependent destruction H2...
    assert (C = C0).
    apply IHtyping1...
    subst.
    apply appTyp_arrow_unique with (C1:= T3) (C2:=T0) in H0...
    inversion H0...
  - (* merge *)
    dependent destruction H2...
    +
      f_equal...
    +
      f_equal...
      apply IHtyping1...
      rewrite_alist (nil ++ G ++ nil).
      apply typing_weakening...
      rewrite_alist (nil ++ G++empty) in H4...    
      get_well_form...
      apply WFS_weakening...
      apply IHtyping2...
      rewrite_alist (nil ++ G ++ nil).
      apply typing_weakening...
      rewrite_alist (nil ++ G++empty) in H4...    
      get_well_form...
      apply WFS_weakening...
  - (* mergev *)
    dependent destruction H5...
    +
      f_equal...
      apply inference_unique_aux with (G:=G) (e:=e1)...
      apply inference_unique_aux with (G:=G) (e:=e2)...
    +
      f_equal...
  - (* rcd *)
    dependent destruction H0...
    f_equal.
    apply IHtyping...
  - (* proj *)
    dependent destruction H1...
    assert (A=A0).
    apply IHtyping...
    subst.
    apply appTyp_rcd_unique with (C2:=C0) in H0...    
Qed.
    
Lemma typing_inf_chk_sub: forall G e A B,
    typing G e Inf A -> typing G e Chk B -> Sub G A B.
Proof with auto.
  intros G e A B H H0.
  apply typing_chk2inf in H0.
  destruct H0.
  destruct H0.
  apply inference_unique with (A2:=x) in H...
  subst...
Qed.
