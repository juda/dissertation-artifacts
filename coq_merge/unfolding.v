Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export decidability.


Definition chooseS (m : Mode) X (C : typ) (D : typ) :=
  match m with
  | Pos => subst_tt X C
  | Neg => subst_tt X D
  end.

Definition choose (m : Mode)  (C : typ) (D : typ) :=
  match m with
  | Pos => C
  | Neg => D
  end.

Lemma chooseS_arrow : forall m X C D A1 A2, 
    chooseS m X C D (typ_arrow A1 A2) = typ_arrow (chooseS m X C D A1) (chooseS m X C D A2).
  intros. destruct m; simpl in *; eauto.
Defined.

Lemma chooseS_and : forall m X C D A1 A2, 
    chooseS m X C D (typ_and A1 A2) = typ_and (chooseS m X C D A1) (chooseS m X C D A2).
  intros. destruct m; simpl in *; eauto.
Defined.

Lemma choose_flip: forall m A B ,
    choose m A B = choose (flip m) B A .
Proof with auto.
  intros.
  destruct m...
Qed.




Lemma mu_transform_1: forall C D (Y X:atom) A m,
    type (typ_mu (choose m C D)) ->
    X <> Y ->
    (subst_tt X (typ_mu (choose m C D)) (open_tt A (typ_rcd Y (open_tt A Y)))) =
 (open_tt (subst_tt X (typ_mu (choose m C D)) A)
       (typ_rcd Y (open_tt (subst_tt X (typ_mu (choose m C D)) A) Y))).
Proof with auto.
  intros.
  rewrite subst_tt_open_tt...
  f_equal.
  simpl...
  f_equal.
  rewrite subst_tt_open_tt_var...
Qed.


Lemma mu_transform_2: forall (X Y:atom) C D A m,
    type (typ_rcd X (choose m (open_tt C X) (open_tt D X))) ->
     X <> Y ->
    open_tt (subst_tt X (typ_rcd X (choose m (open_tt C X) (open_tt D X))) A)
    (typ_rcd Y (open_tt (subst_tt X (typ_rcd X (choose m (open_tt C X) (open_tt D X))) A) Y)) =
  subst_tt X (typ_rcd X (choose m (open_tt C X) (open_tt D X)))
    (open_tt A (typ_rcd Y (open_tt A Y))).
Proof with auto.
  intros.
  rewrite subst_tt_open_tt...
  f_equal...
  simpl...
  f_equal...
  rewrite subst_tt_open_tt_var...
Qed.


Lemma mu_transform3: forall X0 A1 X C ,
    X <> X0 -> type (typ_rcd X C) ->
    (subst_tt X (typ_rcd X C) (open_tt A1 (typ_rcd X0 (open_tt A1 X0)))) =
(open_tt (subst_tt X (typ_rcd X C) A1)
       (typ_rcd X0 (open_tt (subst_tt X (typ_rcd X C) A1) X0))).
Proof with auto.
  intros.
  rewrite subst_tt_open_tt...
  f_equal...
  simpl...
  f_equal...
  rewrite subst_tt_open_tt_var...
Qed.  


Lemma subst_tt_equiv: forall E A B,
    Sub E A B -> forall C D X,
    equiv E C D ->
    Sub E (subst_tt X (typ_rcd X C) A) (subst_tt X (typ_rcd X D) B).
Proof with auto.
  intros E A B H.
  induction H;intros;unfold equiv in *;destruct_hypos;simpl in *;try solve [constructor]...
  -
    destruct (X==X0)...
  -
    constructor...
    get_well_form.
    apply subst_tt_wfs...
  -
    constructor...
    get_well_form.
    apply subst_tt_wfs...
  -
    apply S_andR...
    get_well_form.
    apply subst_tt_wfs...
  -
    apply S_rec with (L:=L \u {{X}} \u dom E);intros.
    +
      rewrite subst_tt_open_tt_var...
      apply subst_tt_wfs...
      get_well_form.
      constructor...
      add_nil.
      apply WFS_weakening...
      apply H...
      get_type...
    +
      rewrite subst_tt_open_tt_var...
      apply subst_tt_wfs...
      get_well_form.
      constructor...
      add_nil.
      apply WFS_weakening...
      apply H0...
      get_type...
    +
      rewrite <- mu_transform3...
      rewrite <- mu_transform3...
      apply H2...
      split.
      rewrite_alist (nil ++ (X0 ~ bind_sub) ++ E).
      apply Sub_weakening...
      simpl.
      constructor...
      get_well_form...
      rewrite_alist (nil ++ (X0 ~ bind_sub) ++ E).
      apply Sub_weakening...
      simpl.
      constructor...
      get_well_form...
      get_type...
      get_type...
  -
    apply S_top...
    get_well_form.
    apply subst_tt_wfs...
    apply subst_tt_toplike...
    get_well_form...
Qed.



Lemma open_var_distinct : forall C i j A B ,
    i <> j ->
    type A -> type B ->
  open_tt_rec i A (open_tt_rec j B C) = open_tt_rec j B (open_tt_rec i A C).
Proof with congruence || eauto.
  intros C.
  induction C;intros;simpl;try solve [f_equal;eauto]...
  -
    destruct (j==n)...
    destruct (i==n)...
    subst...
    simpl...
    destruct (n==n)...
    rewrite <- open_tt_rec_type...
    destruct (i==n)...
    simpl...
    destruct (i==n)...
    rewrite <- open_tt_rec_type...
    simpl...
    destruct (i==n)...
    destruct (j==n)...
Qed.

Lemma rcd_transform1: forall C  k (X Y:atom),
     (typ_rcd Y (open_tt_rec 0 Y (open_tt_rec (S k) X C)) = open_tt_rec (S k) X (typ_rcd Y (open_tt_rec 0 Y C))).
Proof with auto.
  intros.
  simpl.
  f_equal...
  rewrite <- open_var_distinct...
Qed.


Lemma wf_env_weakening: forall E1 E2 X,
    wf_env (E1++E2) ->
    X \notin dom (E1++E2) ->
    wf_env (E1 ++ (X~bind_sub) ++ E2).
Proof with auto.
  intros E1.
  induction E1;intros...
  constructor...
  destruct a.
  rewrite_alist ((a, b) :: E1 ++ E2) in H.
  rewrite_alist ((a, b) :: E1 ++ [(X, bind_sub)] ++ E2).
  dependent destruction H.
  constructor...
  constructor...
  apply WFS_weakening...
Qed.  
          



Lemma Sub_subst_rcd_dismiss: forall E E1 A B X C D,
    X `notin` fl_tt A \u fl_tt B ->
    Sub (E1++[(X, bind_sub)] ++ E) (subst_tt X (typ_rcd X C) A)
        (subst_tt X (typ_rcd X D) B) ->
    type C -> type D ->
    ~ toplike (E1++[(X, bind_sub)] ++ E) D ->
    ~ toplike (E1++[(X, bind_sub)] ++ E) C ->
    WFS (E1 ++ [(X, bind_sub)] ++ E) A ->
    WFS (E1 ++ [(X, bind_sub)] ++ E) B ->
    Sub (E1++[(X, bind_sub)] ++ E) A B.
Proof with auto.
  intros.
  dependent induction H0;try solve [simpl in *;auto]...
  -
    induction A;try solve [simpl in *;inversion x0|simpl in *;destruct (a==X);inversion x0]...
    induction B;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
  -
    induction A;try solve [simpl in *;inversion x0|simpl in *;destruct (a==X);inversion x0]...
    induction B;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    simpl in *.
    destruct (a==X);destruct (a0==X);try solve [inversion x0|inversion x]...
    rewrite <-x0.
    rewrite <-x.
    apply Reflexivity...    
  -
    induction A;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
  -
    induction A;try solve [simpl in *;inversion x0|simpl in *;destruct (a==X);inversion x0]...
    induction B;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    clear IHB1 IHB2 IHA1 IHA2.
    simpl in *.
    inversion x0.
    inversion x.
    dependent destruction H5.
    dependent destruction H6.
    constructor...
    apply IHSub1 with (C:=D) (D:=C)...
    apply IHSub2 with (C:=C) (D:=D)...
  -
    induction B;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    simpl in *.
    inversion x.
    dependent destruction H6.
    constructor...
    apply IHSub1 with (C0:=C) (D:=D)...
    apply IHSub2 with (C0:=C) (D:=D)...
  -
    induction A;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    simpl in *.
    inversion x.
    dependent destruction H6.
    apply S_andL...
    apply IHSub with (C:=C) (D0:=D)...
  -
    induction A;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    simpl in *.
    inversion x.
    dependent destruction H6.
    apply S_andR...
    apply IHSub with (C:=C) (D0:=D)...
  -
    induction A;try solve [simpl in *;inversion x0|simpl in *;destruct (a==X);inversion x0]...
    induction B;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    clear IHA IHB.
    simpl in *.
    inversion x0.
    inversion x.
    dependent destruction H8.
    dependent destruction H10.
    apply S_rec with (L:=L \u L0 \u L1 \u fv_tt A \u fv_tt B \u {{X}} \u fv_tt C
                     \u fv_tt D \u dom (E1 ++(X~ bind_sub)++ E));intros...
    rewrite_alist  (([(X0, bind_sub)] ++ E1) ++ (X, bind_sub) :: E).
    apply H2 with (X0:=X0) (C:=C) (D:=D)...
    *
      apply notin_union...
      split;apply notin_fl_tt_open;simpl.
      auto.
      apply notin_union.
      split...
      apply notin_fl_tt_open...
      auto.
      apply notin_union.
      split...
      apply notin_fl_tt_open... 
    *
      subst.
      rewrite  subst_tt_open_tt...
      f_equal...
      simpl...
      f_equal...
      rewrite  subst_tt_open_tt_var...
    *
      subst.
      rewrite  subst_tt_open_tt...
      f_equal...
      simpl...
      f_equal...
      rewrite  subst_tt_open_tt_var...
    *
      intros v.
      assert (False).
      apply H6.
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E1 ++ (X, bind_sub) :: E) in v.
      apply toplike_strengthening in v...
      get_well_form...
      dependent destruction H15...
      destruct H15.
    *
      intros v.
      assert (False).
      apply H7.
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E1 ++ (X, bind_sub) :: E) in v.
      apply toplike_strengthening in v...
      get_well_form...
      dependent destruction H15...
      destruct H15.
    *
      apply H8...
    *
      apply H10...
  -
    induction A;try solve [simpl in *;inversion x0|simpl in *;destruct (a==X);inversion x0];
    induction B;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    +
      simpl in *.
      destruct (a==X);destruct (a0==X);try solve [inversion x|inversion x0]...
      inversion x.
      inversion x0;subst.
      apply Reflexivity...
      get_well_form...
    +
      clear IHB.
      simpl in *.
      destruct (a==X);subst;try solve [inversion x0]...
      inversion x0.
      inversion x;subst...
      apply notin_union in H.
      destruct H.
      apply notin_union in H7.
      destruct H7.
      apply test_solve_notin_7 in H7...
      destruct H7.
    +
      clear IHA.
      simpl in *.
      destruct (a0==X);subst;try solve [inversion x]...
      inversion x0.
      inversion x;subst...
      apply notin_union in H.
      destruct H.
      apply notin_union in H.
      destruct H.
      apply test_solve_notin_7 in H...
      destruct H.
    +
      clear IHA IHB.
      simpl in *.
      inversion x0.
      inversion x;subst...
      constructor...
      apply IHSub with (C0:=C) (D0:=D)...
      dependent destruction H5...
      dependent destruction H6...
  -
    apply S_top...
    apply toplike_subst_rev in H0...
    destruct H0...
    dependent destruction H0...
    assert (False).
    apply H4...
    destruct H8...
Qed.        


Lemma Sub_non_toplike: forall E A B,
    Sub E A B ->
    ~ toplike E B ->
    ~ toplike E A.
Proof with auto.
  intros.
  intros v.
  apply H0...
  apply toplikeSubToplike with (A:=A)...
Qed.  

Lemma Sub_twice_to_one: forall E E1 A B X,
    X `notin` fl_tt A \u fl_tt B \u fv_tt A \u fv_tt B ->
    Sub (E1++[(X, bind_sub)] ++ E) (open_tt A (typ_rcd X (open_tt A X)))
        (open_tt B (typ_rcd X (open_tt B X))) ->
    WFS (E1 ++ [(X, bind_sub)] ++ E) (open_tt A X) ->
    WFS (E1 ++ [(X, bind_sub)] ++ E) (open_tt B X) ->
    Sub (E1++[(X, bind_sub)] ++ E) (open_tt A X) (open_tt B X).
Proof with auto.
  intros.
  pose toplike_dec as HQ.
  destruct HQ with (A:=open_tt B (typ_rcd X (open_tt B X))) (E:=E1 ++ [(X, bind_sub)] ++ E).
  -
    apply S_top...
    rewrite subst_tt_intro with (X:=X) in t...
    apply toplike_subst_rev in t...
    destruct t...
    dependent destruction H3...
    constructor...
    get_type...
  -
    rewrite subst_tt_intro with (X:=X) in H0...
    remember (subst_tt X (typ_rcd X (open_tt A X)) (open_tt A X)).
    rewrite subst_tt_intro with (X:=X) in H0...
    subst.
    apply Sub_subst_rcd_dismiss in H0...
    +
      apply notin_union.
      split.
      apply notin_fl_tt_open...
      apply notin_fl_tt_open...
    +
      get_type...
    +
      get_type...
    +
      intros v.
      apply n...
      rewrite subst_tt_intro with (X:=X)...
      apply subst_tt_toplike...
    +
      apply Sub_non_toplike in H0...
      intros v.
      apply H0...
      apply subst_tt_toplike...
      rewrite <- subst_tt_intro...
Qed.    

Lemma WFS_permutation : forall A B C D E T ,
    WFS (E ++ A ++ B ++ C ++ D ) T ->
    WFS (E ++ C ++ A ++ B ++ D) T.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor...
    analyze_binds H...
  -
    apply WFS_rec with (L:=L);intros;
      rewrite_alist (([(X, bind_sub)] ++ E) ++ C ++ A ++ B ++ D)...
Qed.

Lemma WFS_permutation2 : forall A B C D  T ,
    WFS ( A ++ B ++ C ++ D ) T ->
    WFS ( A ++ C ++ B ++ D) T.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor...
    analyze_binds H...
  -
    apply WFS_rec with (L:=L);intros;
      rewrite_alist (([(X, bind_sub)]  ++ A) ++ C ++ B ++ D)...
Qed.

Lemma toplike_permutation : forall A B C D  T ,
    toplike ( A ++ B ++ C ++ D ) T ->
    wf_env (A ++ C ++ B ++ D) ->
    toplike ( A ++ C ++ B ++ D) T.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor...
    apply WFS_permutation2...
  -
    apply toplike_rec with (L:=L \u dom (A ++ B++C ++D) );intros.
    rewrite_alist (([(X, bind_sub)]  ++ A) ++ C ++ B ++ D)...
    apply H0...
    rewrite_alist ([(X, bind_sub)]  ++ A ++ C ++ B ++ D)...
Qed.


Lemma Sub_permutation: forall A B C D S T,
    Sub (A ++ B ++ C ++ D) S T ->
    wf_env (A ++ C ++ B ++ D) ->
    Sub (A ++ C ++ B ++ D) S T.
Proof with auto using WFS_permutation2.
   intros.
   dependent induction H...
   -
     apply S_rec with (L:=L \u dom (A ++ B++C ++D) );intros;
     rewrite_alist (([(X, bind_sub)]  ++ A) ++ C ++ B ++ D)...
     apply WFS_permutation2...
     rewrite_alist ([(X, bind_sub)]  ++ A ++ B ++ C ++ D)...
     apply WFS_permutation2...
     rewrite_alist ([(X, bind_sub)]  ++ A ++ B ++ C ++ D)...
     apply H2...
     rewrite_alist ([(X, bind_sub)]  ++ A ++ C ++ B ++ D)...
  -
    apply S_top ...
    apply toplike_permutation...
Qed.


 
Lemma wf_env_notin: forall E1 E2 X,
    wf_env (E1 ++ (X~bind_sub) ++ E2) ->
    X \notin dom (E1 ++ E2).
Proof with auto.
  intros E1.
  dependent induction E1;intros...
  simpl in *...
  dependent destruction H...
  rewrite_alist (a :: (E1 ++ [(X, bind_sub)] ++ E2)) in H.
  rewrite_alist (a :: E1 ++ E2).
  simpl.
  destruct a.
  apply notin_add_3...
  dependent destruction H...
  apply IHE1...
  dependent destruction H...
Qed.


Lemma subst_tt_toplike3: forall B E1 E2 A X,
    WFS (E1 ++ E2) A ->
    wf_env (E1++E2) ->
    toplike (E1 ++ (X~bind_sub) ++ E2) B ->
    X \notin fv_tt A ->
    toplike (E1 ++ E2) (subst_tt X A B).
Proof with auto.
  intros.
  generalize dependent A.
  dependent induction H1;intros;simpl;try solve [constructor;auto]...
  -
    constructor...
    apply subst_tt_wfs3...
  -
    simpl.
    apply toplike_rec with (L:=L \u {{X}} \u dom E1 \u dom E2).
    intros.
    rewrite  subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H1...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ E2).
    constructor...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ E1 ++ E2).
    apply WFS_weakening...
    get_type...
Qed.

  
Lemma sub_generalize_intensive : forall E1 E2 A B C D X m,
    WFS (E1 ++ X ~ bind_sub ++ E2) A -> WFS (E1 ++ X ~ bind_sub ++ E2) B ->
    X \notin fv_tt C \u fv_tt D ->
    X \notin fl_tt A \u fl_tt B ->
    Sub (E1 ++ X ~ bind_sub ++ E2) (subst_tt X (typ_rcd X (choose m (open_tt C X) (open_tt D X))) A)
    (subst_tt X (typ_rcd X (choose m (open_tt D X) (open_tt C X))) B) ->
    Sub (E1 ++ E2) (typ_mu C) (typ_mu D) ->
    ~ toplike (E1 ++ E2) (typ_mu C) ->
    ~ toplike (E1 ++ E2) (typ_mu D) ->
    Sub (E1 ++ E2) (subst_tt X (typ_mu (choose m C D)) A) (subst_tt X (typ_mu (choose m D C)) B).
Proof with auto.
  intros.
  assert (wf_env (E1 ++ E2)).
  get_well_form...
  dependent induction H3...
  - (* nat *)
    dependent induction H;simpl in *;try solve [inversion x0;auto].
    dependent induction H0;simpl in *;try solve [inversion x;auto].
    destruct (X0==X)...
    inversion x...
    inversion x...
    destruct (X0==X)...
    inversion x0...
    inversion x0...
  - (* var *)
    dependent induction H;simpl in *;try solve [inversion x0;auto].
    dependent induction H0;simpl in *;try solve [inversion x;auto].
    destruct (X1==X)...
    inversion x0...
    destruct (X2==X)...
    inversion x...
    rewrite <- x0.
    rewrite <- x...
    constructor...
    rewrite x0...
    analyze_binds H...    
  - (* bot *)
    dependent induction H;simpl in *;try solve [inversion x;auto].
    constructor...
    destruct m;simpl;apply subst_tt_wfs3...
    get_well_form...
    get_well_form...
    destruct (X0==X)...
    inversion x...
    inversion x...
  - (* arrow *)
    dependent induction H;simpl in *;try solve [inversion x0;auto].
    +
      destruct (X0==X)...
      inversion x0...
      inversion x0...
    +
      inversion x0.
      dependent induction H3;simpl in *;try solve [inversion x;auto].
      *
        destruct (X0==X)...
        inversion x...
        inversion x...
      *
        clear IHWFS1 IHWFS2 IHWFS0 IHWFS3.
        inversion x.
        constructor...
        rewrite choose_flip...
        remember (typ_mu (choose (flip m) C D)).
        rewrite choose_flip...
        subst...
        apply IHSub1...
        rewrite choose_flip...
        rewrite choose_flip...
  - (* and *)
    dependent induction H0;simpl in *;try solve [inversion x;auto].
    destruct (X0==X)...
    inversion x...
    inversion x...
  - (* andL *)
    dependent induction H;simpl in *;try solve [inversion x;auto].
    +
      destruct (X0==X)...
      inversion x...
      inversion x...
    +
      inversion x.
      apply S_andL...
      
      destruct m;simpl;apply subst_tt_wfs3;get_well_form...
  - (* andR *)
    dependent induction H;simpl in *;try solve [inversion x;auto].
    +
      destruct (X0==X)...
      inversion x...
      inversion x...
    +
      inversion x.
      apply S_andR...
      destruct m;simpl;apply subst_tt_wfs3;get_well_form...
  - (* rec *)
    dependent induction A;simpl in *;try solve [inversion x0;auto].
    +
      destruct (a==X)...
      inversion x0...
      inversion x0...
    +
      dependent induction B;simpl in *;try solve [inversion x;auto].
      *
        destruct (a==X)...
        inversion x...
        inversion x...
      *
        clear IHA IHB.
        inversion x0.
        inversion x.
        clear x x0.
        assert (Ht:=H7).
        apply sub_regular in Ht.
        destruct_hypos.
        dependent destruction H.
        dependent destruction H7.
        assert (Ht1:=H16).
        assert (Ht2:=H17).
        dependent destruction Ht1.
        dependent destruction Ht2.
        apply S_rec with (L:=L \u L0 \u L1 \u {{X}} \u fv_tt C \u fv_tt D \u L2 \u L3 \u dom E1 \u dom E2);intros...
        --
          rewrite subst_tt_open_tt_var...
          rewrite_alist (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
          apply subst_tt_wfs3...
          apply WFS_permutation...
          apply H0...
          apply WFS_weakening...
          destruct m...
          simpl;destruct m...
          destruct m;get_type...
        --
          rewrite subst_tt_open_tt_var...
          rewrite_alist (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
          apply subst_tt_wfs3...
          apply WFS_permutation...
          apply H8...
          apply WFS_weakening...
          destruct m...
          simpl;destruct m...
          destruct m;get_type...
        --
          rename X0 into Y.
          rewrite_alist (([(Y, bind_sub)] ++ E1) ++ E2).
          rewrite <- mu_transform_1...
          rewrite <- mu_transform_1...
          apply H4 with (X1:=X) (X0:=Y)...
          apply notin_union.
          split;apply notin_fl_tt_open;simpl...
          apply notin_union;split...
          apply notin_fl_tt_open;simpl...
          apply notin_union;split...
          apply notin_fl_tt_open;simpl...
          rewrite_alist (((Y, bind_sub) :: E1 ++ (X, bind_sub) :: E2))...
          apply H...
          rewrite_alist (((Y, bind_sub) :: E1 ++ (X, bind_sub) :: E2))...
          apply H7...
          rewrite H13.
          rewrite mu_transform_2...
          constructor;destruct m;simpl.
          rewrite subst_tt_intro with (X:=Y)...
          apply subst_tt_type...
          specialize_x_and_L Y L3.
          get_type...
          rewrite subst_tt_intro with (X:=Y)...
          apply subst_tt_type...
          specialize_x_and_L Y L2.
          get_type...
          rewrite H14.
          rewrite mu_transform_2...
          constructor;destruct m;simpl.
          rewrite subst_tt_intro with (X:=Y)...
          apply subst_tt_type...
          specialize_x_and_L Y L2.
          get_type...
          rewrite subst_tt_intro with (X:=Y)...
          apply subst_tt_type...
          specialize_x_and_L Y L3.
          get_type...
          rewrite_alist (nil ++ (Y ~ bind_sub) ++ E1 ++ E2).
          apply Sub_weakening...
          simpl.
          constructor...
          intros v.
          apply H10.
          rewrite_alist (nil ++ Y~bind_sub ++ (E1++E2)) in v.
          apply toplike_strengthening in v...
          intros v.
          apply H11.
          rewrite_alist (nil ++ Y~bind_sub ++ (E1++E2)) in v.
          apply toplike_strengthening in v...
          rewrite_alist ([(Y, bind_sub)] ++ E1 ++ E2).
          constructor...
          get_type.
          destruct m;simpl...
          get_type.
          destruct m;simpl...
  - (* rcd *)
    dependent induction H;simpl in *;try solve [inversion x0;auto].
    +
      destruct (X0==X)...
      *
        dependent induction H0;simpl in *;try solve [inversion x;auto].
        --
          destruct (X1==X)...
          ++
            inversion x0.
            inversion x.
            clear x x0.
            rewrite H10 in H3.
            rewrite H12 in H3.
            destruct m;simpl in *...
            dependent destruction H4.
            **
              apply S_rec with (L:=L \u fv_tt C \u fv_tt D \u {{X}} \u fl_tt C \u fl_tt D \u dom E1 \u dom E2);intros...
              rename X2 into Y.
              specialize_x_and_L Y L.
              rewrite_alist (nil ++ [(Y, bind_sub)] ++ E1 ++ E2) in H6.
              apply Sub_twice_to_one in H6...
              assert (equiv ([(Y, bind_sub)] ++ E1 ++ E2) (open_tt D Y) (open_tt C Y)).
              {
                unfold equiv.
              split...
              add_nil.
              rewrite subst_tt_intro with (X:=X)...
              remember ((subst_tt X Y (open_tt D X))).
              rewrite subst_tt_intro with (X:=X)...
              subst.
              apply Sub_replacing...
              apply Sub_permutation...
              get_well_form...
              simpl.
              constructor...
              apply wf_env_notin...
              simpl.
              constructor...
              }
              rewrite subst_tt_intro with (X:=Y)...
              remember (subst_tt Y (typ_rcd Y (open_tt D Y)) (open_tt D Y)).
              rewrite subst_tt_intro with (X:=Y)...
              subst.
              apply subst_tt_equiv...
              unfold equiv in H15.
              destruct H15...
            **
              assert (False).
              apply H7...
              destruct H13.
          ++
            inversion x.
        --
          inversion x0.
          inversion x...
          subst.
          apply notin_union in H2.
          destruct H2.
          apply notin_union in H8.
          destruct H8.
          apply notin_singleton_1 in H8.
          destruct H8...
      *
        inversion x0.
    +
      inversion x0.
      dependent induction H0;simpl in *;try solve [inversion x;auto].
      *
        destruct (X0==X)...
        --
          inversion x.
          subst.
          apply notin_union in H2.
          destruct H2.
          apply notin_union in H2.
          destruct H2.
          apply notin_singleton_1 in H2.
          destruct H2...
        --
          inversion x.
      *
        inversion x.
        clear IHWFS IHWFS0.
        subst.
        constructor...
  - (* top *)
    apply S_top...
    +
      destruct m;simpl in *.
      apply subst_tt_wfs3...
      get_well_form...
      apply subst_tt_wfs3...
      get_well_form...
    +
      apply subst_tt_toplike3...
      destruct m;get_well_form...
      apply toplike_subst_rev in H4...
      destruct H4...
      dependent destruction H4.
      destruct m;simpl in *.
      assert (False).
      apply H6.
      apply toplike_rec with (L:={{X}} \u dom (E1++E2));intros...
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E1 ++ E2).
      apply toplike_permutation...
      rewrite subst_tt_intro with (X:=X)...
      apply toplike_replacing...
      apply wf_env_weakening...
      constructor...
      destruct H9.
      assert (False).
      apply H7.
      apply toplike_rec with (L:={{X}} \u dom (E1++E2));intros...
      rewrite_alist (nil ++ [(X0, bind_sub)] ++ E1 ++ E2).
      apply toplike_permutation...
      rewrite subst_tt_intro with (X:=X)...
      apply toplike_replacing...
      apply wf_env_weakening...
      constructor...
      destruct H9.
      constructor.
      get_type.
      destruct m;simpl.
      dependent destruction H9.
      pick fresh Y.
      rewrite subst_tt_intro with (X:=Y)...
      dependent destruction H10.
      pick fresh Y.
      rewrite subst_tt_intro with (X:=Y)...
      destruct m;simpl...
Qed.


Lemma unfolding_lemma: forall E A B,
    Sub E (typ_mu A) (typ_mu B) ->
    Sub E (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof with auto.
  intros.
  assert (Ht:=H).
  pose toplike_dec.
  destruct s with (E:=E) (A:=typ_mu B).
  -
    apply S_top.
    +
      assert (WFS E (typ_mu A)).
      get_well_form...
      assert (Hq:=H0).
      dependent destruction Hq.
      pick fresh X.
      rewrite subst_tt_intro with (X:=X)...
      add_nil.
      apply subst_tt_wfs3...
      apply H2...
    +
      assert (Hq:=t).
      dependent destruction Hq.
      pick fresh X.
      rewrite subst_tt_intro with (X:=X)...
      add_nil.
      apply subst_tt_toplike3...
      get_well_form...
      get_well_form...
      apply H0...
  -
    dependent destruction H.
    +
      add_nil.
      pick fresh Y.
      rewrite subst_tt_intro with (X:=Y)...
      remember (subst_tt Y (typ_mu A) (open_tt A Y)).
      rewrite subst_tt_intro with (X:=Y)...
      subst.
      assert (A = choose Pos A B) by auto.
      assert (B = choose Pos B A) by auto.
      rewrite H2.
      rewrite H3.
      apply sub_generalize_intensive;simpl...
      *
        apply H...
      *
        apply H0...
      *
        apply notin_union.
        split.
        apply notin_fl_tt_open...
        apply notin_fl_tt_open...
      *
        rewrite <-  subst_tt_intro...
        rewrite <-  subst_tt_intro...
        apply H1...
      *
        apply Sub_non_toplike with (B:=typ_mu B)...
    +
      assert (False).
      apply n...
      destruct H1.
Qed.    
