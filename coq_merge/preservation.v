Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Export typereduce.


Lemma wf_env_to_uniq: forall E,
    wf_env E ->
    uniq E.
Proof with auto.
  intros.
  induction H...
Qed.  


Lemma wf_typ_strengthening : forall E F x U T,
 WFS (F ++ x ~ bind_typ U ++ E) T ->
 WFS (F ++ E) T.
Proof with simpl_env; eauto.
  intros.
  dependent induction H...
  -
    analyze_binds H...
  -
    apply WFS_rec with (L:=L).
    intros.
    rewrite_alist (([(X, bind_sub)] ++ F) ++ E).
    eapply H0...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ F) ++ E).
    eapply H2...
Qed.


Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ x ~ bind_typ T ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma WFS_typ_strengthening: forall E1 E2 T X U,
    WFS (E1 ++ X ~ bind_typ U ++ E2) T->
    WFS (E1 ++ E2) T.
Proof with auto.
  intros.
  dependent induction H;try solve [simpl in *;constructor;eauto]...
  -
    analyze_binds H...
  -
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A);intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0 with (X0:=X0) (U0:=U) (X1:=X)...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H2 with (X0:=X0) (U0:=U) (X1:=X)...
Qed.

Lemma toplike_typ_strengthening: forall E1 E2 T X U,
    toplike (E1 ++ X ~ bind_typ U ++ E2) T->
    wf_env  (E1 ++ E2 ) ->
    toplike (E1 ++ E2) T.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor...
    eapply IHtoplike1...
    eapply IHtoplike2...
  -
    constructor...
    eapply IHtoplike...
    apply WFS_typ_strengthening in H0...
  -
    constructor...
    eapply IHtoplike...
  -
    apply toplike_rec with (L:=L \u fv_tt B \u dom (E1++E2));intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (U0:=U)...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ E2)...
Qed.  

Lemma Sub_strengthening: forall E1 E2 A B X U,
    Sub (E1 ++ X ~ (bind_typ U) ++ E2) A B ->
    wf_env  (E1 ++ E2 ) ->
    Sub (E1 ++ E2) A B.
Proof with eauto using WFS_typ_strengthening.
  intros.
  dependent induction H...
  -
    apply S_rec with (L:=L \u {{X}} \u fv_tt A1 \u fv_tt A2 \u dom (E1++E2));intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply WFS_typ_strengthening with (X:=X) (U:=U)...
    apply H...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply WFS_typ_strengthening with (X:=X) (U:=U)...
    apply H0...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H2 with (X0:=X0) (U0:=U) (X1:=X)...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ E2)...
  -
    apply S_top...
    eapply toplike_typ_strengthening...
Qed.


Lemma dis_strengthening: forall E1 E2 A B X U,
    dis (E1 ++ X ~ (bind_typ U) ++ E2) A B ->
    wf_env  (E1 ++ E2 ) ->
    dis (E1 ++ E2) A B.
Proof with eauto using WFS_typ_strengthening.
  intros.
  dependent induction H;try solve [constructor;auto;apply toplike_typ_strengthening in H;auto]...
  -
    constructor...
    eapply toplike_typ_strengthening...
  -
    apply dis_topR...
    eapply toplike_typ_strengthening...
  -
    apply dis_RecRec with (L:=L \u {{X}} \u fv_tt A1 \u fv_tt A2 \u dom (E1++E2));intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply WFS_typ_strengthening with (X:=X) (U:=U)...
    apply H...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply WFS_typ_strengthening with (X:=X) (U:=U)...
    apply H0...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H2 with (X0:=X0) (U0:=U) (X1:=X)...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ E2)...
Qed.

Lemma value_subst: forall e z u,
    value e ->
    expr u ->
    value (subst_ee z u e).
Proof with auto.
  intros.
  induction H;simpl...
  constructor...
  dependent destruction H.
  apply lc_abs with (L:=L \u {{z}})...
  intros.
  rewrite  subst_ee_open_ee_var...
Qed.


Lemma fv_ee_open_rec: forall k e1 e2,
    fv_ee (open_ee_rec k e2 e1) [<=]  (fv_ee e1) \u fv_ee e2.
Proof with auto.
  intros.
  generalize dependent k.
  induction e1;intros;simpl;try fsetdec...
  -
    destruct (k==n);simpl;fsetdec...
  -
    specialize (IHe1_1 k).
    specialize (IHe1_2 k).
    fsetdec...    
  -
    specialize (IHe1_1 k).
    specialize (IHe1_2 k).
    fsetdec...
Qed.


Lemma fv_ee_open_var: forall e1 x,
    fv_ee (open_ee e1 (exp_fvar x)) [<=]  add x (fv_ee e1).
Proof with auto.
  intros.
  assert (fv_ee (open_ee e1 (exp_fvar x)) [<=]  (fv_ee e1) \u {{x}}).
  apply fv_ee_open_rec...
  fsetdec...
Qed.  

Lemma fv_ee_open2: forall e1 e2  k,
    fv_ee e1 [<=] fv_ee (open_ee_rec k e2 e1) .
Proof with auto.
  intros.
  generalize dependent k.
  induction e1;intros;simpl;try fsetdec...
  -
    specialize (IHe1_1 k).
    specialize (IHe1_2 k).
    fsetdec...    
  -
    specialize (IHe1_1 k).
    specialize (IHe1_2 k).
    fsetdec...
Qed.

Lemma add_notin_G: forall x G1 G2,
    G1 [<=] add x G2 ->
    x \notin G1 ->
    G1 [<=]  G2.
Proof with auto.
  intros.
  fsetdec...
Qed.           

Lemma fv_in_dom: forall G e dir T,
    typing G e dir T -> fv_ee e [<=] dom G.
Proof with auto.
  intros.
  dependent induction H; simpl; try fsetdec...
  - 
    apply binds_In in H0.
    fsetdec.
  -
    pick fresh x.
    specialize_x_and_L x L.
    simpl in H0.
    assert (fv_ee e [<=] fv_ee (open_ee e x)).
    apply fv_ee_open2...
    assert (fv_ee e [<=] add x (dom G)).
    fsetdec...
    apply add_notin_G with (x:=x)...
  - 
    pick fresh x.
    specialize_x_and_L x L.
    simpl in H0.
    assert (fv_ee e [<=] fv_ee (open_ee e x)).
    apply fv_ee_open2...
    assert (fv_ee e [<=] add x (dom G)).
    fsetdec...
    apply add_notin_G with (x:=x)...
Qed.

Lemma subst_value : forall v T dir z u,
    typing nil v dir T -> subst_ee u z v = v.
Proof with auto.
  intros.
  apply fv_in_dom in H...
  simpl in H...
  rewrite <- subst_ee_fresh...
  fsetdec...
Qed.



    

Lemma RSub_to_Sub: forall E A B,
    RSub E A B ->
    Sub E A B.
Proof with auto.
  intros.
  induction H...
  -
    apply Reflexivity...
  -
    apply RSub_regular in H.
    apply RSub_regular in H0.
    destruct_hypos...
Qed.


Lemma Rsub_sub_top: forall E B A,
    toplike E B ->
    RSub E B A ->
    toplike E A.
Proof with auto.
  intros.
  generalize dependent A.
  induction H;intros;try solve [dependent destruction H0;auto|dependent destruction H1;auto]...
  -
    dependent destruction H1...
    constructor...
    get_well_form...
  -
    dependent destruction H1...
    apply toplike_rec with (L:=L)...
Qed.
    
Lemma RSub_trans: forall E B,
    WFS E B ->
    forall A C,
    RSub E A B -> RSub E B C -> RSub E A C.
Proof with auto.
  intros E B HB.
  induction HB;intros;try solve [dependent destruction H;dependent destruction H0;auto]...
  -
    dependent destruction H0...
    inversion H0...
  -
    dependent destruction H...
    dependent destruction H1...
    constructor...
    apply Transitivity with (B:=A)...
    constructor...
    apply Rsub_sub_top with (B:=typ_arrow A B)...
  -
    dependent destruction H...
    dependent destruction H1...
    constructor...
    apply Rsub_sub_top with (B:=typ_and A B)...
  -
    dependent destruction H0...
    dependent destruction H...
    constructor...
    apply Rsub_sub_top with (B:=typ_rcd l T)...
  -
    dependent destruction H3...
    constructor...
    apply Rsub_sub_top with (B:=typ_mu A)...
Qed.


Lemma tred_preser_Rsub: forall v A v' ,
    value v ->
    typ_reduce v A v'->
    typing nil v Chk A ->
    exists B, typing nil v' Inf B /\ RSub empty B A.
Proof with auto.
  intros.
  dependent induction H0...
  - (* nat *)
    exists typ_nat...
  - (* top *)
    exists typ_top...
  - (* fold *)
    dependent destruction H3.
    dependent destruction H3.
    exists (typ_mu B).
    split...
    apply typing_fold...
    apply typing_chk_sub with (A:=(open_tt A (typ_mu A)))...
    apply unfolding_lemma...
    get_well_form...
    constructor...
    get_well_form...
  - (* abs *)
    dependent destruction H4.
    dependent destruction H4.
    exists (typ_arrow A1 B2)...
    split...
    apply typing_abs with (L:=L).
    intros.
    apply typing_chk_sub with (A:=A2)...
    rewrite_alist (nil ++ ([(x, bind_typ A1)] ++ empty)).
    apply Sub_weakening...
    constructor...
    get_well_form...
    constructor...
    constructor...
    get_well_form...
  - (* merge *)
    dependent destruction H1.
    assert (Hq:=H).
    apply consistent_afterTR with (A:=A) (B:=B) (v1:=e1) (v2:=e2) (C:=A0) in Hq...
    apply and_inv in H0.
    destruct H0.
    assert (typing empty e Chk A).
    apply typing_sub with (A:=A0)...
    assert (typing empty e Chk B).
    apply typing_sub with (A:=A0)...
    specialize (IHtyp_reduce1 H H3).
    specialize (IHtyp_reduce2 H H4).
    destruct IHtyp_reduce1.
    destruct IHtyp_reduce2.
    destruct_hypos.
    exists (typ_and x x0).
    split...
    apply typing_mergev...
    apply TypedReduce_prv_value with (v:=e) (A:=A)...
    apply TypedReduce_prv_value with (v:=e) (A:=B)...
  - (* mergeL *)
    dependent destruction H.
    assert (Hq:=H).
    apply reduce_to_typing with (e2:=e) (T:=T) in H...
    dependent destruction H4...
    dependent destruction H4...
    exists A...
    exists A...
  - (* mergeR *)
    dependent destruction H.
    assert (Hq:=H0).
    apply reduce_to_typing with (e2:=e) (T:=T) in Hq...
    dependent destruction H4...
    dependent destruction H4...
    exists B0...
    exists B0...
  - (* rcd *)
    dependent destruction H.
    dependent destruction H2.
    dependent destruction H2.
    assert (Hq:=H0).
    apply reduce_to_typing with (e2:=e2) (T:=T) in Hq...
    apply IHtyp_reduce in Hq...
    destruct_hypos.
    exists (typ_rcd l x)...
    exists A...
Qed.   


Lemma disjoint_bot_toplike_L: forall A E,
    dis E typ_bot A ->
    toplike E A.
Proof with auto.
  intros.
  dependent induction H...
  inversion H1.  
Qed.

Lemma disjoint_bot_toplike_R: forall A E,
    dis E A typ_bot ->
    toplike E A.
Proof with auto.
  intros.
  dependent induction H...
  inversion H1.  
Qed.

Lemma disjoint_and_inv: forall E A B C,
    dis E A (typ_and B C) ->
    dis E A B /\ dis E A C.
Proof with auto.
  intros.
  dependent induction H...
  -
    dependent destruction H1...
  -
    dependent destruction H0...
  -
    split.
    apply dis_andL...
    eapply IHdis1 with (B0:=B) (C0:=C)...
    eapply IHdis2 with (B0:=B) (C0:=C)...
    apply dis_andL...
    eapply IHdis1 with (B0:=B) (C0:=C)...
    eapply IHdis2 with (B0:=B) (C0:=C)...
Qed.


          

Lemma disjoint_RSub: forall A1 A2 B E,
    RSub E A1 A2 -> dis E A2 B -> dis E A1 B.
Proof with auto.
  intros.
  generalize dependent B.
  dependent induction H;intros...
  -
    dependent induction B;try solve [inversion H1|get_well_form;constructor;auto]...
    +
      dependent destruction H1...
      inversion H3.
      assert (dis E A2 typ_bot).
      apply IHRSub...
      apply dis_topR...
      dependent destruction H3...
      apply disjoint_bot_toplike_R in H4...
      apply dis_topR...
      constructor...
      get_well_form...
    +
      dependent destruction H1...
      inversion H3.
      inversion H2.
    +
      dependent destruction H1...
      *
        dependent destruction H3...
      *
        dependent destruction H2...
    +
      dependent destruction H1...
      *
        dependent destruction H3...
        dependent destruction H2...
        apply dis_topL...
        get_well_form...        
      *
        dependent destruction H2...
        dependent destruction H3...
        apply dis_ArrArr...
        get_well_form...
      *
        apply dis_ArrArr...
        get_well_form...
  -
    dependent induction H1...
    +
      apply dis_topL...
      get_well_form...
    +
      dependent destruction H1.
      apply dis_andL...
    +
      apply dis_andR...
      apply IHdis1 with (B3:=B1) (B4:=B2)...
      apply IHdis2 with (B4:=B1) (B5:=B2)...
  -
    dependent induction B0;try solve [get_well_form;constructor;auto]...
    +
      dependent destruction H0...
      inversion H2.
      dependent destruction H2.
      assert (dis E A typ_bot).
      apply IHRSub...
      apply disjoint_bot_toplike_R in H3...
    +
      dependent destruction H0...
      inversion H2.
      inversion H1.
    +
      dependent destruction H0...
      *
        apply dis_topL...
        get_well_form...
      *
        dependent destruction H2.
        dependent destruction H1.
        apply dis_andR...
    +
      dependent destruction H0...
      *
        apply dis_topL...
        get_well_form...
      *
        dependent destruction H1.
        dependent destruction H2.
        destruct (l==a);subst...
        apply dis_RcdRcd...
        get_well_form...
      *
        apply dis_RcdRcd...
        get_well_form...
  -
     get_well_form...
Qed.


Lemma Rsub_weakening: forall E1 E2 E3 A B,
    RSub (E1 ++ E3) A B ->
    wf_env (E1 ++ E2 ++ E3) ->
    RSub (E1 ++ E2 ++ E3) A B.
Proof with auto.
  intros.
  generalize dependent E2.
  dependent induction H;intros...
  -
    constructor...
    apply WFS_weakening...
  -
    constructor...
    apply Sub_weakening...
  -
    constructor...
    apply toplike_weakening...
Qed.    

Lemma Typing_subst_2 : forall E F S' e u S  dir T (z : atom),
    typing (F ++ [(z, bind_typ S)] ++ E) e dir T ->
    typing E u Inf S' ->
    RSub E S' S ->
    exists T', typing (F ++ E) (subst_ee z u e) dir T' /\ RSub (F++E) T' T.
Proof with eauto using wf_env_strengthening, RSub_to_Sub.
  intros.
  generalize dependent u.
  generalize dependent S'.
  assert (wf_env (F++E)) as Q1.
  get_well_form...
  assert (Q2:=H).
  dependent induction H;intros;simpl...
  - (* var *)
    destruct (x==z)...
    +
      subst.
      apply binds_mid_eq in H0...
      inversion H0...
      subst...
      exists S'...
      split...
      rewrite_alist (nil ++ F ++ E).
      apply typing_weakening...
      get_well_form...
      apply WFS_weakening...
      rewrite_alist (nil ++ F ++ E).
      apply Rsub_weakening...
      apply wf_env_to_uniq...
    +
      exists T...
      split...
      constructor...
      get_well_form...
      apply WFS_typ_strengthening in H9...
  - (* anno *)
    destruct IHtyping with (E0:=E) (F0:=F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    destruct H2.
    exists A...
    split...
    constructor...
    apply typing_chk_sub with (A:=x)...
    constructor...
    get_well_form...
  - (* abs *)
    exists (typ_arrow A B)...
    split...
    apply typing_abs with (L:={{z}} \u L \u dom (F++E)).
    intros.
    destruct H0 with (x:=x) (E0:=E) (F0:=[(x, bind_typ A)] ++ F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    rewrite_alist ([(x, bind_typ A)] ++ F ++ E).
    constructor...
    get_well_form...
    dependent destruction H10...
    apply WFS_typ_strengthening in H10_...
    rewrite_alist ([(x, bind_typ A)] ++ F ++ [(z, bind_typ S)] ++ E)...
    destruct_hypos.
    rewrite  subst_ee_open_ee_var ...
    apply typing_chk_sub with (A:=x0)...
    get_well_form...
    constructor...
    get_well_form...
    apply WFS_typ_strengthening in H9...
  - (* app *)
    destruct IHtyping1 with (E0:=E) (F0:=F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    destruct IHtyping2 with (E0:=E) (F0:=F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    destruct_hypos.
    dependent destruction H0...
    +
      dependent destruction H7...
      *
        exists T2...
        split...
        apply typing_app with (C:=typ_arrow T1 T2) (T1:=T1)...
        apply typing_chk_sub with (A:=x0)...
        constructor...
        get_well_form...
        dependent destruction H0...
      *
        exists A2...
        split...
        apply typing_app with (C:=typ_arrow A1 A2) (T1:=A1)...
        apply typing_chk_sub with (A:=x0)...
        apply Transitivity with (B:=T1)...
      *
        exists typ_top...
        split...
        apply typing_app with (C:=typ_top) (T1:=typ_top)...
        apply typing_chk_sub with (A:=x0)...
        constructor...
        get_well_form...
        constructor...
        dependent destruction H0...        
    +
      dependent destruction H7...
      *
        exists typ_top...
        split...
        apply typing_app with (C:=typ_top) (T1:=typ_top)...
        apply typing_chk_sub with (A:=x0)...
      *
        exists typ_top...
        split...
        apply typing_app with (C:=typ_top) (T1:=typ_top)...
        apply typing_chk_sub with (A:=x0)...        
  - (* fix *)
    exists A...
    split...
    apply typing_fix with (L:=L \u {{z}} \u dom (F++E))...
    intros.
    destruct H0 with (x:=x) (E0:=E) (F0:=[(x, bind_typ A)] ++ F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    rewrite_alist ([(x, bind_typ A)] ++ F ++ E).
    constructor...
    get_well_form...
    apply WFS_typ_strengthening in H10...
    rewrite_alist ([(x, bind_typ A)] ++ F ++ [(z, bind_typ S)] ++ E)...
    destruct_hypos.
    rewrite  subst_ee_open_ee_var ...
    apply typing_chk_sub with (A:=x0)...
    get_well_form...
    constructor...
    get_well_form...
    apply WFS_typ_strengthening in H9...
  - (* fold *)
    exists (typ_mu A).
    split...
    destruct IHtyping with  (E0:=E) (F0:= F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    destruct_hypos.
    apply typing_fold...
    apply typing_chk_sub with (A:=x)...
    apply WFS_typ_strengthening in H0...
    constructor...
    apply WFS_typ_strengthening in H0...
  - (* merge *)
    destruct IHtyping1 with  (E0:=E) (F0:= F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    destruct IHtyping2 with  (E0:=E) (F0:= F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    destruct_hypos.
    exists (typ_and x x0).
    split...
    apply typing_merge...
    apply dis_strengthening in H1...
    apply disjoint_RSub with (B:=B) in H7...
    apply disjoint_RSub with (B:=x) in H6...
    apply dis_comm...
    apply dis_comm...
  - (* mergev *)
    exists (typ_and A B).
    split...
    apply typing_mergev...
    +
      apply value_subst...
      get_well_form...
    +
      apply value_subst...
      get_well_form...
    +
      rewrite subst_value with (T:=A) (dir:=Inf)...
    +
      rewrite subst_value with (T:=B) (dir:=Inf)...
    +
      intros.
      rewrite subst_value with (T:=A) (dir:=Inf) in H7...
      rewrite subst_value with (T:=B) (dir:=Inf) in H8...
    +
      constructor...
      get_well_form...
      apply WFS_typ_strengthening in H13...
  - (* unfold *)
    destruct IHtyping with  (E0:=E) (F0:= F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    destruct_hypos.
    dependent destruction H3.
    +
      exists (open_tt T (typ_mu T)).
      split...
      constructor...
      assert (Hq:=H3).
      dependent destruction Hq.
      pick fresh X.
      rewrite subst_tt_intro with (X:=X)...
      rewrite_alist (nil ++ (F ++ E)).
      apply subst_tt_wfs3...
    +
      exists (open_tt T (typ_mu T)).
      split...
      constructor...
      apply typing_chk_sub with (A:=typ_top)...
      constructor...
      get_well_form.
      assert (Hq:=H6).
      dependent destruction Hq.
      pick fresh X.
      rewrite subst_tt_intro with (X:=X)...
      rewrite_alist (nil ++ (F ++ E)).
      apply subst_tt_wfs3...
  - (* rcd *)
    destruct IHtyping with  (E0:=E) (F0:= F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    destruct_hypos.
    exists (typ_rcd l x)...    
  - (* proj *)
    destruct IHtyping with  (E0:=E) (F0:= F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    destruct_hypos.
    dependent destruction Q2.
    apply inference_unique with (A2:=A0) in H...
    subst.
    dependent destruction H0...
    +
      dependent destruction H5...
      *
        dependent destruction H.
        exists C...
      *
        dependent destruction H.
        exists typ_top...
    +
      dependent destruction H5...
  - (* sub *)    
    destruct IHtyping with  (E0:=E) (F0:= F) (S0:=S) (z0:=z) (S':=S') (u:=u)...
    destruct_hypos.
    exists B...
    split...
    apply typing_sub with (A:=x)...
    apply Transitivity with (B:=A)...
    apply Sub_strengthening in H0...
    constructor...
    get_well_form...
    apply WFS_typ_strengthening in H6...
Qed.    


Lemma arrowLike_Rsub: forall A B C C',
    appTyp C (typ_arrow A B) -> RSub empty C' C
    -> exists A' B', appTyp C' (typ_arrow A' B') /\ Sub empty A A' /\ RSub empty B' B.
Proof with auto.
  intros.
  dependent induction H...
  -
    dependent destruction H0...
    +
      exists A.
      exists B.
      dependent destruction H.
      repeat split...
      apply Reflexivity...
    +
      exists A1.
      exists A2...
    +
      dependent destruction H.
      exists typ_top.
      exists typ_top...
  -
    dependent destruction H0...
    +
      exists typ_top.
      exists typ_top...
    +
      exists typ_top.
      exists typ_top...
Qed.

Lemma step_not_value: forall (v:exp),
    value v -> irred exp step v.
Proof with auto.
  intros.
  unfold irred.
  induction H; intros;try solve [intros v;dependent destruction v;auto]...
  -
    intros v.
    dependent destruction v...
    apply IHvalue with (b:=e')...
  -
    intros v.
    dependent destruction v...
    apply IHvalue1 with (b:=e1')...
    apply IHvalue2 with (b:=e2')...
  -
    intros v.
    dependent destruction v...
    apply IHvalue with (b:=e')...
Qed.

Lemma WFS_open: forall G A,
    WFS G (typ_mu A) ->
    WFS G (open_tt A (typ_mu A)).
Proof with auto.
  intros.
  assert (Hq:=H).
  dependent destruction H.
  pick fresh X.
  rewrite subst_tt_intro with (X:=X)...
  add_nil.
  apply subst_tt_wfs3...
  apply H0...
Qed.

Lemma subst_tt_toplike3: forall B E1 E2 A X,
    WFS (E1 ++ E2) A ->
    toplike (E1 ++ (X~bind_sub) ++ E2) B ->
    X `notin` fv_tt A -> wf_env (E1 ++ E2) ->
    toplike (E1 ++ E2) (subst_tt X A B).
Proof with auto.
  intros.
  generalize dependent A.
  dependent induction H0;intros;simpl;try solve [constructor;auto]...

  -
    constructor...
    apply subst_tt_wfs3...
  -
    apply toplike_rec with (L:=L \u {{X}} \u dom (E1++E2)).
    intros.
    rewrite  subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ E2)...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ (E1++E2)).    
    apply WFS_weakening...
    apply WFS_type in H1...
Qed.

Lemma toplike_open: forall G A,
    toplike G (typ_mu A) ->
    toplike G (open_tt A (typ_mu A)).
Proof with auto.
  intros.
  assert (Hq:=H).
  dependent destruction H.
  pick fresh X.
  rewrite subst_tt_intro with (X:=X)...
  add_nil.
  apply subst_tt_toplike3...
  get_well_form...
  apply H...
  get_well_form...
Qed.

  
Theorem preservation_aux : forall e e' dir A,
    typing nil e dir A ->
    step e e' ->
    exists C, typing nil e' dir C /\ RSub empty C A.
Proof with eauto using RSub_to_Sub.
  intros.
  generalize dependent e'.
  dependent induction H;intros;try solve [dependent destruction H0;auto|dependent destruction H1;auto]...
  - (* anno *)
    dependent destruction H0...
    +
      exists A...
      split...
      constructor...
      destruct IHtyping with (e':=e')...
      destruct_hypos.
      apply typing_chk_sub with (A:=x)...
      constructor...
      get_well_form...
    +
      apply tred_preser_Rsub with (v':=e') in H...
  - (* app *)
    dependent destruction H2...
    +
      exists typ_top...
      split...
      dependent destruction H.
      dependent destruction H0...      
    +
      dependent destruction H.
      dependent destruction H0.
      exists T2.
      apply tred_preser_Rsub with (v':=e3) in H5...
      destruct_hypos.
      pick fresh z.
      specialize_x_and_L z L.
      rewrite subst_ee_intro with (x:=z)...
      rewrite_alist (nil ++ [(z, bind_typ T1)] ++ empty) in H.
      apply Typing_subst_2 with (S:=T1) (S':=x) (u:=e3) in H...
      destruct_hypos.
      split.
      constructor.
      apply typing_chk_sub with (A:=x0)...
      constructor...
      get_well_form...      
    +
      destruct IHtyping1 with (e':=e1')...
      destruct H4.
      apply arrowLike_Rsub with (C':=x) in H0...
      destruct H0.
      destruct H0.
      destruct_hypos.
      exists x1...
      split...
      apply typing_app with (C:=x) (T1:=x0)...
      apply typing_chk_sub with (A:=T1)...
    +
      destruct IHtyping2 with (e':=e2')...
      destruct H4.
      exists T2...
      split...
      apply typing_app with (C:=C) (T1:=T1)...
      apply typing_chk_sub with (A:=x)...
      constructor...
      get_well_form.
      dependent destruction H0...
      dependent destruction H13...      
  - (* fix *)
    dependent destruction H1...
    exists A...
    split...
    assert (Hq:=H).
    apply typing_anno.
    pick fresh x.
    rewrite subst_ee_intro with (x:=x)...
    assert (x \notin L) by auto.
    apply H in H2.
    rewrite_alist (nil ++ [(x, bind_typ A)] ++ empty) in H2.
    apply Typing_subst_2 with (S:=A) (S':=A) (u:=exp_fix A e) in H2...
    destruct H2.
    destruct H2.
    apply typing_chk_sub with (A:=x0)...
    constructor...
    get_well_form...
    apply WFS_typ_strengthening in H4...
    pick fresh x.
    specialize_x_and_L x L.
    get_well_form...
    constructor...
    dependent destruction H...
  - (* fold *)
    dependent destruction H1...
    destruct IHtyping with (e':=e')...
    destruct_hypos.
    exists (typ_mu A)...
    split...
    apply typing_fold...
    apply typing_chk_sub with (A:= x)...
  - (* merge *)
    dependent destruction H2...
    +
      destruct IHtyping1 with (e':=e1')...
      destruct H4.
      exists (typ_and x B)...
      split...
      constructor...
      apply disjoint_RSub with (A2:=A)...
      constructor...
      constructor...
      get_well_form...
    +
      destruct IHtyping2 with (e':=e2')...
      destruct H4.
      exists (typ_and A x)...
      split...
      constructor...
      apply dis_comm...
      apply disjoint_RSub with (A2:=B)...
      apply dis_comm...
      constructor...
      constructor...
      get_well_form...
  - (* mergev *)
    dependent destruction H5...
    +
      apply step_not_value in H...
      assert (False).
      unfold irred in H.
      apply H with (b:=e1')...
      destruct H7.
    +
      apply step_not_value in H0...
      assert (False).
      unfold irred in H0.
      apply H0 with (b:=e2')...
      destruct H7.
  - (* unfold *)
    dependent induction H0...
    + (* step_fld *)
      clear IHtyping.

      apply tred_preser_Rsub in H0...    
      dependent destruction H...
      dependent destruction H...
      apply typing_chk_sub with (A:=open_tt B (typ_mu B))...
      apply unfolding_lemma...
    +
      clear IHtyping.
      exists (open_tt T (typ_mu T)).
      split.
      constructor...
      apply tred_preser_Rsub in H1...    
      destruct_hypos.
      apply typing_chk_sub with (A:=x)...
      apply typing_sub with (A:=x)...
      apply Reflexivity...
      get_well_form...
      constructor...
      apply WFS_open...
      get_well_form...
    +
      exists typ_top...
      split...
      constructor...
      apply toplike_open...
    +
      destruct IHtyping with (e':=e')...
      destruct H2.
      dependent destruction H3...
      *
        exists (open_tt T (typ_mu T))...
        split.
        dependent destruction H2.
        constructor...
        constructor...
        apply WFS_open...        
      *
        exists (open_tt T  (typ_mu T)).
        split.
        dependent destruction H2.
        constructor...
        apply typing_chk_sub with (A:=typ_top)...
        constructor...
        get_well_form...
        apply WFS_open...
  - (* rcd *)
    dependent induction H0...
    destruct IHtyping with (e':=e')...
    destruct_hypos.
    exists (typ_rcd l x)...
  - (* proj *)
    dependent destruction H1...
    destruct IHtyping with (e':=e')...
    destruct_hypos.
    dependent destruction H0...
    +
      dependent destruction H3...
      *
        dependent destruction H0.
        exists C...
      *
        dependent destruction H0...
    +
      dependent destruction H3...
    +
      dependent destruction H...
      dependent destruction H0...
    +
      dependent destruction H...
      dependent destruction H0...
      exists C...
      split...
      constructor...
      get_well_form...
  - (* sub *)
    destruct IHtyping with (e':=e')...
    destruct_hypos.
    exists B.
    split.
    apply typing_sub with (A:=x)...
    apply Transitivity with (B:=A)...
    constructor...
    get_well_form...
Qed.


Theorem preservation : forall e e' dir A,
    typing nil e dir A ->
    step e e' ->
    typing nil e' Chk A.
Proof with auto.
  intros...
  apply preservation_aux with (e':=e') in H...
  destruct_hypos...
  destruct dir...
  apply typing_sub with (A:=x)...
  apply RSub_to_Sub...
  apply typing_chk_sub with (A:=x)...
  apply RSub_to_Sub...
Qed.
