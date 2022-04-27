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

Lemma mu_transform_0: forall C  (Y X:atom) A ,
    type (typ_mu C) ->
    X <> Y ->
    (subst_tt X (typ_mu C) (open_tt A (typ_rcd Y (open_tt A Y)))) =
 (open_tt (subst_tt X (typ_mu C) A)
       (typ_rcd Y (open_tt (subst_tt X (typ_mu C) A) Y))).
Proof with auto.
  intros.
  rewrite subst_tt_open_tt...
  f_equal.
  simpl...
  f_equal.
  rewrite subst_tt_open_tt_var...
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
    dependent destruction H3.
    dependent destruction H4.
    constructor...
    apply IHSub1 with (C:=D) (D:=C)...
    apply IHSub2 with (C:=C) (D:=D)...
  -
    induction B;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    simpl in *.
    inversion x.
    dependent destruction H4.
    constructor...
    apply IHSub1 with (C0:=C) (D:=D)...
    apply IHSub2 with (C0:=C) (D:=D)...
  -
    induction A;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    simpl in *.
    inversion x.
    dependent destruction H4.
    apply S_andL...
    apply IHSub with (C:=C) (D0:=D)...
  -
    induction A;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    simpl in *.
    inversion x.
    dependent destruction H4.
    apply S_andR...
    apply IHSub with (C:=C) (D0:=D)...
  -
    induction A;try solve [simpl in *;inversion x0|simpl in *;destruct (a==X);inversion x0]...
    induction B;try solve [simpl in *;inversion x|simpl in *;destruct (a==X);inversion x]...
    clear IHA IHB.
    simpl in *.
    inversion x0.
    inversion x.
    dependent destruction H6.
    dependent destruction H8.
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
      apply H6...
    *
      apply H8...
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
      apply notin_union in H5.
      destruct H5.
      apply test_solve_notin_7 in H5...
      destruct H5.
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
      dependent destruction H3...
      dependent destruction H4...
  -
    induction B;try solve [inversion x]...
    simpl in x...
    destruct (a==X);try solve [inversion x]...
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
  rewrite subst_tt_intro with (X:=X) in H0...
  remember (subst_tt X (typ_rcd X (open_tt A X)) (open_tt A X)).
  rewrite subst_tt_intro with (X:=X) in H0...
  subst.
  apply Sub_subst_rcd_dismiss in H0;try solve [get_type;auto]...
  apply notin_union.
  split.
  apply notin_fl_tt_open...
  apply notin_fl_tt_open...
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


  
Lemma sub_generalize_intensive : forall E1 E2 A B C D X m,
    WFS (E1 ++ X ~ bind_sub ++ E2) A -> WFS (E1 ++ X ~ bind_sub ++ E2) B ->
    X \notin fv_tt C \u fv_tt D ->
    X \notin fl_tt A \u fl_tt B ->
    Sub (E1 ++ X ~ bind_sub ++ E2) (subst_tt X (typ_rcd X (open_tt C X)) A)
    (subst_tt X (typ_rcd X  (open_tt D X)) B) ->
    Sub (E1 ++ E2) (typ_mu (choose m C D)) (typ_mu (choose m D C)) ->
    Sub (E1 ++ E2) (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B).
Proof with auto.
  intros.
  assert (wf_env (E1 ++ E2)).
  get_well_form...
  generalize dependent m.
  dependent induction H3;intros...
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
        apply IHSub1 with (m:=flip m)...
        rewrite <- choose_flip...
        rewrite <- choose_flip...
        apply IHSub2 with (m:= m)...
  - (* and *)
    dependent induction H0;simpl in *;try solve [inversion x;auto].
    destruct (X0==X)...
    inversion x...
    inversion x...
    inversion x...
    constructor...
    apply IHSub1 with (m:=m)...
    apply IHSub2 with (m:=m)...
  - (* andL *)
    dependent induction H;simpl in *;try solve [inversion x;auto].
    +
      destruct (X0==X)...
      inversion x...
      inversion x...
    +
      inversion x.
      apply S_andL...
      apply IHSub with (m:=m)...
      apply subst_tt_wfs3;get_well_form...
      destruct m;simpl...
  - (* andR *)
    dependent induction H;simpl in *;try solve [inversion x;auto].
    +
      destruct (X0==X)...
      inversion x...
      inversion x...
    +
      inversion x.
      apply S_andR...
      apply IHSub with (m:=m)...
      apply subst_tt_wfs3;get_well_form...
      destruct m;simpl...
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
        assert (Ht1:=H).
        assert (Ht2:=H0).
        dependent destruction Ht1.
        dependent destruction Ht2.
        assert (type (typ_mu C) /\ type (typ_mu D)) as Hq.
        destruct m;get_type...
        destruct Hq.
        apply S_rec with (L:=L \u L0 \u L1 \u {{X}} \u fv_tt C \u fv_tt D   \u dom E1 \u dom E2);intros...
        --
          rewrite subst_tt_open_tt_var...
          rewrite_alist (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
          apply subst_tt_wfs3...
          apply WFS_permutation...
          apply H12...
          apply WFS_weakening...
          destruct m;simpl;get_well_form...
        --
          rewrite subst_tt_open_tt_var...
          rewrite_alist (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
          apply subst_tt_wfs3...
          apply WFS_permutation...
          apply H14...
          apply WFS_weakening...
          destruct m;simpl;get_well_form...
        --
          rename X0 into Y.
          rewrite_alist (([(Y, bind_sub)] ++ E1) ++ E2).
          rewrite <- mu_transform_0...
          rewrite <- mu_transform_0...
          apply H4 with (X1:=X) (X0:=Y) (m:=m)...
          ++
            apply notin_union.
            split;apply notin_fl_tt_open;simpl...
            apply notin_union;split...
            apply notin_fl_tt_open;simpl...
            apply notin_union;split...
            apply notin_fl_tt_open;simpl...
          ++
            rewrite_alist (((Y, bind_sub) :: E1 ++ (X, bind_sub) :: E2))...
            apply H9...
          ++
            rewrite_alist (((Y, bind_sub) :: E1 ++ (X, bind_sub) :: E2))...
            apply H13...
          ++
            rewrite H10.
            rewrite subst_tt_open_tt...
            f_equal...
            simpl...
            f_equal...
            rewrite subst_tt_open_tt_var...
            dependent destruction H15.
            pick fresh Z.
            constructor...
            rewrite subst_tt_intro with (X:=Z)...
            dependent destruction H15.
            pick fresh Z.
            constructor...
            rewrite subst_tt_intro with (X:=Z)...
          ++
            rewrite H11.
            rewrite subst_tt_open_tt...
            f_equal...
            simpl...
            f_equal...
            rewrite subst_tt_open_tt_var...
            dependent destruction H16.
            pick fresh Z.
            constructor...
            rewrite subst_tt_intro with (X:=Z)...
            dependent destruction H16.
            pick fresh Z.
            constructor...
            rewrite subst_tt_intro with (X:=Z)...
          ++
            rewrite_alist ([(Y, bind_sub)] ++ E1 ++ E2).
            constructor...
          ++
            rewrite_alist (nil ++ Y~bind_sub ++ (E1++E2)).
            apply Sub_weakening...
            constructor...
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
            rewrite H8 in H3.
            rewrite H10 in H3.
            destruct m;simpl in *...
            dependent destruction H4...
            **
              apply S_rec with (L:=L \u fv_tt C \u fv_tt D \u {{X}} \u fl_tt C \u fl_tt D \u dom E1 \u dom E2);intros...
              rename X2 into Y.
              specialize_x_and_L Y L.
              rewrite_alist (nil ++ [(Y, bind_sub)] ++ E1 ++ E2) in H7.
              apply Sub_twice_to_one in H7...
              assert (equiv ([(Y, bind_sub)] ++ E1 ++ E2) (open_tt D Y) (open_tt C Y)).
              {
                unfold equiv.
                split...
                add_nil.
                rewrite subst_tt_intro with (X:=X)...
                remember ((subst_tt X Y (open_tt C X))).
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
              remember (subst_tt Y (typ_rcd Y (open_tt C Y)) (open_tt C Y)).
              rewrite subst_tt_intro with (X:=Y)...
              subst.
              apply subst_tt_equiv...
              unfold equiv in H13.
              destruct H13...
              unfold equiv in *...
              destruct H13...
          ++
            inversion x.
        --
          inversion x0.
          inversion x...
          subst.
          apply notin_union in H2.
          destruct H2.
          apply notin_union in H6.
          destruct H6.
          apply notin_singleton_1 in H6.
          destruct H6...
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
        apply IHSub with (m:=m)...
  - (* top *)
    induction B;try solve [inversion x]...
    +
      simpl...
      constructor...
      apply subst_tt_wfs3...
      destruct m;simpl in *;get_well_form...
    +
      simpl in x...
      destruct (a==X);try solve [inversion x]...
Qed.


Lemma unfolding_lemma: forall E A B,
    Sub E (typ_mu A) (typ_mu B) ->
    Sub E (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof with auto.
  intros.
  assert (Ht:=H).
  dependent destruction H.
  -
    add_nil.
    pick fresh Y.
    rewrite subst_tt_intro with (X:=Y)...
    remember (subst_tt Y (typ_mu A) (open_tt A Y)).
    rewrite subst_tt_intro with (X:=Y)...
    subst.
    apply sub_generalize_intensive with (m:=Pos)...
    apply H...
    apply H0...
    apply notin_union.
    split.
    apply notin_fl_tt_open...
    apply notin_fl_tt_open...
    rewrite <-  subst_tt_intro...
    rewrite <-  subst_tt_intro...
    apply H1...
Qed.    

