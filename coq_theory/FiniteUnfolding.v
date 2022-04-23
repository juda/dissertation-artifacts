Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Infra.

Lemma sub_regular : forall E A B,
    Sub E A B -> wf_env E /\ WFS E A /\ WFS E B.
Proof with auto.
  intros.
  induction H...
  destruct IHSub1.
  destruct IHSub2.
  destruct H2.
  destruct H4.
  split...
  split.
  pick fresh X.
  specialize (H0 0 X).
  assert (X \notin L) by auto.
  apply H0 in H1.
  destruct H1.
  dependent destruction H1...
  split;apply WFS_rec with (L:=L);intros;
  apply H0...
Qed.

Lemma refl : forall E A,
    wf_env E -> WFS E A -> Sub E  A A.
Proof with auto.
  intros.
  induction H0...
  apply SA_rec with (L:=L \u dom E)...
Defined.

Lemma trans_aux: forall B E,
    WFS E B -> forall A C,
    Sub E A B -> Sub E B C -> Sub E A C.
Proof with auto.
  intros B E H.
  dependent induction H;intros...
  -
    dependent destruction H0.
    dependent destruction H...
  -
    dependent destruction H.
    dependent destruction H0...
  -
    dependent destruction H0.
    dependent destruction H2...
  -
    dependent destruction H1.
    dependent destruction H2...
    constructor...    
    constructor...
    apply sub_regular in H1_...
    apply H1_.
    apply sub_regular in H1_0...
    apply H1_0.
  -
    dependent destruction H1.
    dependent destruction H2...
    constructor...
    apply WFS_rec with (L:=L0)...
    intros...
    specialize (H1 n X H4).
    apply sub_regular in H1...
    destruct H1...
    destruct H5...
    apply SA_rec with (L:=L \u L0 \u L1).
    intros.
    apply H0 with (n:=n)...
Qed.

Lemma Transitivity: forall B E A C,
    Sub E A B -> Sub E B C -> Sub E A C.
Proof with auto.
  intros.
  apply trans_aux with (B:=B)...
  apply sub_regular in H0.
  destruct H0.
  destruct H1...
Qed.

Lemma Sub_weakening: forall E E1 E2 A B,
    Sub (E1++E2) A B ->
    wf_env (E1 ++ E ++ E2) ->
    Sub (E1++E++E2) A B.
Proof with auto.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    constructor...
    apply wfs_weakening...
  -
    apply SA_rec with (L:=L \u dom (E1 ++ E ++ E2))...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply H0...
    rewrite_alist ([(X, bind_sub)] ++ E1 ++ E ++ E2)...
Qed.

Lemma wfs_replacing: forall E1 E2 T X Y,
    WFS (E1++ X ~ bind_sub ++E2) T ->
    X <> Y ->
    WFS (E1++ Y ~ bind_sub ++E2) (subst_tt X Y T).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros...
  -
    simpl.
    destruct (X0==X)...
    constructor.
    analyze_binds H.
  -
    simpl.
    rewrite_alist (E1 ++ Y ~ bind_sub ++ E2).
    constructor...
  -
    simpl.
    apply WFS_rec with (L:=L \u {{X}}).
    intros.
    rewrite <- subst_open_unfoldn...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H0...
Qed.


Lemma Sub_replacing: forall E1 E2 A B X Y,
    Sub (E1++ X ~ bind_sub ++E2) A B ->
    X <> Y ->
    wf_env (E1 ++ Y ~ bind_sub ++ E2) ->
    Sub (E1++ Y ~ bind_sub ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros...
  -
    simpl.
    destruct (X0==X)...
    analyze_binds H0.
  -
    simpl.
    constructor...
    rewrite_alist (E1 ++ [(Y, bind_sub)] ++ E2).
    apply wfs_replacing...
  -
    simpl.
    rewrite_alist (E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
  -
    simpl.
    apply SA_rec with (L:=L  \u {{X}} \u dom (E1 ++ [(Y, bind_sub)] ++ E2) )...
    intros.
    rewrite <- subst_open_unfoldn...
    rewrite <- subst_open_unfoldn...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H0...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
Qed.

Lemma subst_wfs_unfoldn: forall n T X E1 E2,
    WFS (E1 ++ X ~ bind_sub ++ E2) (unfoldT T X n) ->
    forall Y, Y \notin fv_tt T \u {{X}} -> X \notin fv_tt T ->
    WFS (E1 ++ Y ~ bind_sub ++ E2) (unfoldT T Y n).
Proof with auto.
  intros.
  rewrite <- unfoldT_subst with (X:=X)...
  apply wfs_replacing...
Qed.
  

Lemma subst_sub_unfoldn: forall n C D X E1 E2,
    Sub (E1 ++ X ~ bind_sub ++ E2) (unfoldT C X n) (unfoldT D X n) ->
    forall Y, Y \notin fv_tt C \u fv_tt D \u {{X}} ->
              X \notin fv_tt C \u fv_tt D ->
              wf_env (E1 ++ Y ~ bind_sub  ++ E2) ->
              Sub (E1 ++ Y ~ bind_sub  ++ E2) (unfoldT C Y n) (unfoldT D Y n).
Proof with auto.
  intros.
  rewrite <- unfoldT_subst with (X:=X)...
  remember (subst_tt X Y (unfoldT C X n)).
  rewrite <- unfoldT_subst with (X:=X)...
  subst.
  apply Sub_replacing...
Qed.

Lemma wfs_permutation: forall E E1 E2 E3 A,
    WFS (E ++ E1 ++ E2 ++ E3) A ->
    WFS (E ++ E2 ++ E1 ++ E3) A.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor.
    apply in_app_iff in H.
    destruct H.
    apply In_lemmaL...
    apply in_app_iff in H.
    destruct H.
    apply In_lemmaR.
    apply In_lemmaR...
    apply In_lemmaL...
    apply in_app_iff in H.
    destruct H.
    apply In_lemmaR...
    apply In_lemmaL...
    apply In_lemmaR...
    apply In_lemmaR...
    apply In_lemmaR...
  -
    apply WFS_rec with (L:=L)...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E) ++ E2 ++ E1 ++ E3).
    apply H0...
Qed.    
    
Lemma Sub_permutation: forall E E1 E2 E3 A B,
    Sub (E ++ E1 ++ E2 ++ E3) A B ->
    wf_env (E ++ E2 ++ E1 ++ E3) ->
    Sub (E ++ E2 ++ E1 ++ E3) A B.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor...
    analyze_binds H0...
  -
    constructor...
    apply wfs_permutation...
  -
    apply SA_rec with (L:=L \u dom (E ++ E2 ++ E1 ++ E3 ))...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E) ++ E2 ++ E1 ++ E3).
    apply H0...
    rewrite_alist ([(X, bind_sub)] ++ E ++ E2 ++ E1 ++ E3)...    
Qed.

Lemma strengthening_wfs: forall E1 E2 T X m,
    WFS (E1 ++ X ~ m ++ E2) T->
    X \notin fv_tt T ->
    WFS (E1 ++ E2) T.
Proof with auto.
  intros.
  dependent induction H...
  -
    analyze_binds H...
    simpl.
    apply D.F.singleton_iff...
  -
    simpl in H1.
    constructor...
    apply IHWFS1 with (X0:=X) (m0:=m)...
    apply IHWFS2 with (X0:=X) (m0:=m)...
  -
    simpl in H1.
    apply WFS_rec with (L:=L \u {{X}}).
    intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (m0:=m)...
    apply notin_fv_tt_open...
Qed.    

Lemma strengthening_sub: forall E1 E2 A B X m,
    Sub (E1 ++ X ~ m ++ E2) A B ->
    X \notin (fv_tt A \u fv_tt B) ->
    wf_env  (E1 ++ E2 ) ->
    Sub (E1 ++ E2) A B.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor...
    analyze_binds H0...
    apply AtomSetImpl.union_2.
    apply D.F.singleton_iff...
  -
    constructor...
    apply strengthening_wfs with (X:=X) (m:=m)...
  -
    simpl in H1.
    constructor...
    apply IHSub1 with (X0:=X) (m0:=m)...
    apply IHSub2 with (X0:=X) (m0:=m)...
  -
    simpl in H1.
    apply SA_rec with (L:=L \u {{X}} \u dom (E1 ++ E2)).
    intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (m0:=m)...
    apply notin_union.
    split.
    apply notin_fv_tt_open...
    apply notin_fv_tt_open...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ E2).
    constructor...
Qed.

Lemma wf_env_strengthening: forall E1 E2 X,
    wf_env (E1++E2) ->
    X \notin dom (E1++E2) ->
    wf_env (E1 ++ X ~ bind_sub ++ E2).
Proof with auto.
  induction E1;intros...
  constructor...
  rewrite_alist (a :: (E1 ++ [(X, bind_sub)] ++ E2)).
  destruct a.
  simpl in *.
  destruct b...
  constructor...
  eapply IHE1...
  dependent destruction H...
  dependent destruction H...
  constructor...
  eapply IHE1...
  dependent destruction H...
  dependent destruction H...
  rewrite_alist (E1 ++ (X~ bind_sub) ++ E2).
  apply wfs_weakening...
  dependent destruction H...
Qed.
  
Lemma subst_rec: forall E1 E2 X A B,
    Sub (E1 ++ X ~ bind_sub ++ E2) A B ->
    wf_env (E1 ++ E2) ->
    forall  C D ,
      WFS (E1 ++ E2) (typ_mu C) -> WFS (E1 ++ E2) (typ_mu D) ->
      X \notin fv_tt C \u fv_tt D \u dom (E1 ++ E2)  ->
    (forall n, Sub (E1 ++ X ~ bind_sub ++ E2) (subst_tt X (unfoldT C X n) A) (subst_tt X (unfoldT D X n) B)) ->
    Sub (E1 ++ E2) (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B).
Proof with auto.
  intros E1 E2 X A B H.
  dependent induction H;intros...
  -
    simpl in *...
    destruct (X0==X)...
    apply SA_rec with (L:={{X}} \u fv_tt C \u fv_tt D \u dom (E1 ++ E2)).
    intros...
    rewrite_alist (nil ++ [(X1, bind_sub)] ++ (E1 ++ E2)).
    apply subst_sub_unfoldn with (X:=X)...
    apply Sub_permutation...
    simpl...
    constructor...
    constructor...
    analyze_binds H0.
  -
    constructor...
    rewrite_alist (nil ++ E1 ++ E2).
    apply subst_tt_wfs2...
    simpl.
    rewrite_alist (nil ++ (X ~ bind_sub) ++ E1 ++ E2).
    apply wfs_permutation...
  -
    simpl in *.
    constructor...
    apply IHSub1...
    intros.
    specialize (H5 n).
    dependent destruction H5...
    apply IHSub2...
    intros.
    specialize (H5 n).
    dependent destruction H5...
  -
    assert (type (typ_mu C)). apply wfs_type with (E:=E1 ++ E2)...
    assert (type (typ_mu D)). apply wfs_type with (E:=E1 ++ E2)...
    simpl in *...
    apply SA_rec with (L:=L \u {{X}} \u fv_tt C \u fv_tt D \u fv_tt A1 \u fv_tt A2 \u dom (E1 ++ E2)).
    intros.
    rewrite <- subst_open_unfoldn...
    rewrite <- subst_open_unfoldn...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0...
    +
      constructor...
    +
      rewrite_alist  (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
      apply wfs_weakening...
    +
      rewrite_alist  (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
      apply wfs_weakening...
    +
      intros.
      specialize (H5 n0).
      dependent destruction H5.
      remember (unfoldT C X n0).
      remember (unfoldT D X n0).
      assert (type t).
      {
        dependent destruction H6.
        subst.
        pick fresh Y.
        rewrite <- unfoldT_subst with (X:=Y)...
        apply subst_tt_type...
        apply type_unfoldT...
      }
      assert (type t0).
      {
        dependent destruction H7.
        subst.
        pick fresh Y.
        rewrite <- unfoldT_subst with (X:=Y)...
        apply subst_tt_type...
        apply type_unfoldT...
      }
      rewrite subst_open_unfoldn...
      rewrite subst_open_unfoldn...
      pick fresh X1.
      remember (subst_tt X t A1).
      remember (subst_tt X t0 A2).
      rewrite_alist  (nil ++ [(X0, bind_sub)] ++ (E1 ++ (X, bind_sub) :: E2)) ...
      apply subst_sub_unfoldn with (X:=X1)...
      rewrite_alist ([(X1, bind_sub)] ++ E1 ++ (X, bind_sub) :: E2)...
      assert (X0 \notin fv_tt t1).
      {
        subst.
        apply notin_fv_subst...
        apply notin_fv_tt_open...
      }
      assert (X0 \notin fv_tt t2).
      {
        subst.
        apply notin_fv_subst...
        apply notin_fv_tt_open...
      }
      auto.
      assert (X1 \notin fv_tt t1).
      {
        subst.
        apply notin_fv_subst...
      }
      assert (X1 \notin fv_tt t2).
      {
        subst.
        apply notin_fv_subst...
      }
      auto.
      constructor...
      apply wf_env_strengthening...
Qed.
  
Lemma unfolding_lemma :
  forall E A B,
    Sub E (typ_mu A) (typ_mu B) ->
    Sub E (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof with auto.
  intros.
  assert (Hq:=H).
  dependent destruction H.
  pick fresh X.
  assert (X \notin L) by auto.
  apply H with (n:=0) in H0...
  simpl in H0.
  rewrite_alist (nil ++ E).
  rewrite subst_tt_intro with (X:=X)...
  remember (subst_tt X (typ_mu A) (open_tt A X)).
  rewrite subst_tt_intro with (X:=X)...
  subst.
  apply sub_regular in Hq.
  destruct_hypos.
  apply subst_rec...
  intros.
  rewrite unfoldSn...
  rewrite unfoldSn...
  apply H...
Qed.


Lemma completeness_wfa : forall E A, WFS E A -> WFA E A.
  intros.
  induction H; eauto.
  apply WFA_rec with (L := L); intros; eauto.
  specialize (H0 0 X H1); simpl in *. eauto.
Defined.

Lemma completeness_wf : forall E A, WFS E A -> WF E A.
Proof with auto.
  intros.
  induction H...
  apply WF_rec with (L := L); intros...
  specialize (H0 0 X H1)...
  specialize (H0 1 X H1)...
Defined.

Lemma completeness : forall E A B,
    Sub E A B -> sub E A B.
Proof with auto.
  intros.
  induction H; eauto.
  - constructor...
    apply completeness_wf; eauto.
  - apply sa_rec with (L := L); intros.
    specialize (H0 0 X H1); eauto.
    specialize (H0 1 X H1); eauto.
Defined.

Lemma wfs_generalize : forall n E X A,
    X \notin fv_tt A ->
    WFS E (open_tt A (typ_fvar X)) ->
    WFS E (unfoldT A X n).
Proof with auto.  
  induction n;intros...
  simpl.
  rewrite subst_tt_intro with (X:=X)...
  apply subst_tt_wfs...
Qed.


Lemma soundness_wfa : forall E A,
    WFA E A -> WFS E A.
Proof with auto.  
  intros.
  induction H...  
  apply WFS_rec with (L := L \u fv_tt A).
  intros...
  assert (X \notin L) by auto.
  specialize (H0 X H2).
  apply wfs_generalize...
Defined.

Lemma soundness_wf : forall E A,
    WF E A -> WFS E A.
Proof with auto.  
  intros.
  induction H...  
  apply WFS_rec with (L := L \u fv_tt A);intros...
  assert (X \notin L) by auto.
  specialize (H0 X H4).
  apply wfs_generalize...
Defined.

Lemma refl_algo : forall E A,
    wf_env E -> WFS E A -> sub E  A A.
Proof with auto.
  intros.
  induction H0...
  apply sa_rec with (L:=L \u dom E)...
  intros.
  assert (X \notin L) by auto.
  assert (wf_env ([(X, bind_sub)] ++ E)).
  constructor...
  specialize (H1 0 X H3 H4).
  simpl in H1...
  intros.
  assert (X \notin L) by auto.
  assert (wf_env ([(X, bind_sub)] ++ E)).
  constructor...
  specialize (H1 1 X H3 H4).
  simpl in H1...
Defined.

Lemma suba_regular : forall E A B,
    sub E A B -> wf_env E /\ WF E A /\ WF E B.
Proof with auto.
  intros.
  induction H...
  -
    destruct IHsub1.
    destruct IHsub2.
    destruct H2.
    destruct H4.
    split...
  -
    split.
    pick fresh X.
    specialize (H2 X).
    assert (X \notin L) by auto.
    apply H2 in H3.
    destruct H3.
    dependent destruction H3...
    split;apply WF_rec with (L:=L);intros...
    apply H0...
    apply H2...
    apply H0...
    apply H2...
Qed.

Lemma trans_aux_algo: forall B E,
    WF E B -> forall A C,
    sub E A B -> sub E B C -> sub E A C.
Proof with auto.
  intros B E H.
  dependent induction H;intros...
  -
    dependent destruction H0.
    dependent destruction H...
  -
    dependent destruction H.
    dependent destruction H0...
  -
    dependent destruction H0.
    dependent destruction H2...
  -
    dependent destruction H1.
    dependent destruction H2...
    constructor...    
    constructor...
    apply suba_regular in H1_...
    apply H1_.
    apply suba_regular in H1_0...
    apply H1_0.
  -
    dependent destruction H3.
    dependent destruction H5...
    constructor...
    apply WF_rec with (L:=L0);intros...
    specialize (H3 X H7).
    apply suba_regular in H3...
    destruct H3...
    destruct H8...
    specialize (H4 X H7).
    apply suba_regular in H4...
    destruct H4...
    destruct H8...
    apply sa_rec with (L:=L \u L0 \u L1);intros...
Qed.

Lemma trans_algo: forall B E A C,
    sub E A B -> sub E B C -> sub E A C.
Proof with auto.
  intros.
  apply trans_aux_algo with (B:=B)...
  apply suba_regular in H0.
  destruct H0.
  destruct H1...
Qed.

Lemma sub_replacing: forall E1 E2 A B X Y,
    sub (E1++ X ~ bind_sub ++E2) A B ->
    X <> Y ->
    wf_env (E1 ++ Y ~ bind_sub ++ E2) ->
    sub (E1++ Y ~ bind_sub ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros...
  -
    simpl.
    destruct (X0==X)...
    analyze_binds H0.
  -
    simpl.
    constructor...
    rewrite_alist (E1 ++ [(Y, bind_sub)] ++ E2).
    apply completeness_wf.
    apply wfs_replacing...
    apply soundness_wf...
  -
    simpl.
    rewrite_alist (E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
  -
    simpl.
    apply sa_rec with (L:=L  \u {{X}} \u dom (E1 ++ [(Y, bind_sub)] ++ E2) )...
    intros.
    rewrite  subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H0...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite <- subst_tt_open_tt...
    rewrite <- subst_tt_open_tt...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H2...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
Qed.

Lemma open_subst_twice : forall A (X Y:atom),
    X \notin fv_tt A ->
    subst_tt X Y (open_tt A (open_tt A X)) = (open_tt A (open_tt A Y)).
Proof with auto.
  intros.
  remember (open_tt A X).
  rewrite subst_tt_open_tt...
  rewrite <- subst_tt_fresh...
  f_equal...
  subst.
  rewrite <- subst_tt_intro...
Qed.  

