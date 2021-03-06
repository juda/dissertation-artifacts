Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Antisymmetry.
            

Lemma choose_flip: forall m A B ,
    choose m A B = choose (flip m) B A .
Proof with auto.
  intros.
  destruct m...
Qed.

Lemma wf_env_map_free2: forall E1 E2 X C B,
    wf_env (E1 ++ X~B++ E2) ->
    WF  E2 C ->
    wf_env ((map (subst_tb X C) E1)++ E2).
Proof with auto.
  induction E1;intros;simpl...
  dependent destruction H...
  destruct a.
  rewrite_env ((a, b) :: E1 ++ X~B++ E2) in H.
  simpl...
  rewrite_env  ((a, subst_tb X C b) :: (map (subst_tb X C) E1 ++ E2)).
  destruct b;simpl...
  -
    dependent destruction H.
    constructor...
    apply IHE1 with (B:=B)...
    apply subst_tb_wf with (Q:=B)...
  -
    dependent destruction H.
    constructor...
    apply IHE1 with (B:=B)...
    apply subst_tb_wf with (Q:=B)...
Qed.

Lemma subst_reverse: forall A B X C D,
    X \notin fl_tt A \u fl_tt B ->
    subst_tt X (typ_label X C) A = subst_tt X (typ_label X D) B ->
    (C = D \/ (X \notin fv_tt A \u fv_tt B)) /\ (A=B).
Proof with auto.
  induction A;induction B;intros;simpl in *; try solve [inversion H0|right;auto|destruct (a==X);inversion H0]...
  -
    destruct (a==X);subst...
    destruct (a0==X);subst...
    inversion H0...
    inversion H0...
    destruct (a0==X);subst...
    inversion H0...
  -
    destruct (a==X);subst...
    +
      inversion H0...
      apply notin_union in H.
      destruct_hypos.
      apply notin_union in H1.
      destruct_hypos.
      apply notin_singleton_1 in H1...
      destruct H1...
    +
      inversion H0...
  -
    inversion H0.
    apply IHA1 in H2...
    apply IHA2 in H3...
    destruct_hypos;subst.
    destruct H2;destruct H1...
  -
    inversion H0.
    apply IHA1 in H2...
    apply IHA2 in H3...
    destruct_hypos;subst.
    destruct H2;destruct H1...
  -
    inversion H0.
    apply IHA in H2...
    destruct_hypos;subst...    
  -
    destruct (a0==X);subst...
    +
      inversion H0.
      apply notin_union in H.
      destruct_hypos.
      apply notin_union in H.
      destruct_hypos.
      apply notin_singleton_1 in H...
      destruct H...
    +
      inversion H0.
  -
    inversion H0.
    apply IHA in H3...
    destruct_hypos;subst...    
Qed.

  
Lemma subst_tt_wf_env_label_rec: forall E1 X E2 U,
    wf_env (map (subst_tb X (typ_label X (open_tt U X))) E1 ++ (X, bind_sub typ_top) :: E2) ->
    X \notin fv_tt U \u fl_env E1 ->
    WF E2 (typ_mu U) ->
    wf_env (map (subst_tb X (typ_mu U)) E1 ++ E2).
Proof with auto.
  intros.
  apply wf_env_drop_label in H.
  rewrite drop_label_reverse_env in H...
  apply wf_env_map_free2 with (B:=bind_sub typ_top)...
Qed.

Lemma drop_wf_env_label_rec: forall E1 X E2 U,
    wf_env (map (subst_tb X (typ_label X (open_tt U X))) E1 ++ (X, bind_sub typ_top) :: E2) ->
    X \notin fv_tt U \u fl_env E1 ->
    WF E2 (typ_mu U) ->
    wf_env ( E1 ++ (X, bind_sub typ_top) :: E2).
Proof with auto.
  intros.
  apply wf_env_drop_label in H.
  rewrite drop_label_reverse_env in H...
Qed.

Lemma maps_subst_tb_free: forall E X U,
    X \notin fv_env E ->
    map (subst_tb X U) E = E.
Proof with auto.
  induction E;intros...
  destruct a.
  destruct b.
  -
    simpl in *.
    f_equal...
    f_equal...
    f_equal...
    rewrite <- subst_tt_fresh...
  -
    simpl in *.
    f_equal...
    f_equal...
    f_equal...
    rewrite <- subst_tt_fresh...
Qed.

Lemma binds_map_free_env: forall E1 E2 X Y U T S,
    Y \notin {{X}}  ->
    wf_env (E1 ++ (Y, bind_sub T) :: E2) ->
    binds X (bind_sub U) (E1 ++ (Y, bind_sub T) :: E2) ->
    binds X (bind_sub (subst_tt Y S U)) (map (subst_tb Y S) E1 ++ (Y, bind_sub T) :: E2).
Proof with auto.
  intros.
  unfold binds in *.
  apply binds_map_free with (Y:=Y) (P:=S) in H1...
  apply notin_from_wf_env in H0.
  rewrite_env (map (subst_tb Y S) E1 ++ map (subst_tb Y S) [(Y, bind_sub T)] ++ map (subst_tb Y S) E2) in H1.
  simpl in H1...
  assert (map (subst_tb Y S) E2 = E2).
  rewrite maps_subst_tb_free ...
  rewrite H2 in H1...
  assert (subst_tt Y S T = T).
  rewrite <- subst_tt_fresh...
  rewrite H3 in H1...
Qed.

Lemma binds_map_free_env2: forall E1 E2 X Y U S,
    Y \notin {{X}}  ->
    wf_env (E1 ++ (Y, bind_sub typ_top) :: E2) ->
    binds X (bind_sub U) (E1 ++ (Y, bind_sub typ_top) :: E2) ->
    binds X (bind_sub (subst_tt Y S U)) (map (subst_tb Y S) E1 ++  E2).
Proof with auto.
  intros.
  analyze_binds H1...
  -
    unfold binds in *.
    apply In_lemmaL.
    apply binds_map_free...
  -
    unfold binds in *.
    apply In_lemmaR.
    rewrite <- maps_subst_tb_free with (X:=Y) (U:=S)...
    apply binds_map_free...
    apply notin_from_wf_env in H0...
Qed.

Lemma binds_subst_extensial: forall E S T X0 X U,
    binds X0 (bind_sub U) (map (subst_tb X S) E) ->
    exists A,
      binds X0 (bind_sub A) (map (subst_tb X T) E).
Proof with auto.
  induction E;intros...
  simpl in *.
  analyze_binds H.
  simpl in *.
  destruct a.
  analyze_binds H.
  -
    destruct b;simpl in *; inversion BindsTacVal.
    exists (subst_tt X T t)...
  -
    apply IHE with (T:=T) in BindsTac...
    destruct_hypos.
    exists x...
Qed.


Lemma WF_narrowing_env: forall E1 E E2 A S T X,
    WF (E1 ++ map (subst_tb X S) E ++ E2) A ->
    WF (E1 ++ map (subst_tb X T) E ++ E2) A.
Proof with auto.
  intros.
  dependent induction H;try solve [analyze_binds H;eauto]...
  -
    analyze_binds H; try solve [apply WF_var with (U:=U);auto].
    apply binds_subst_extensial with (T:=T) in BindsTac0.
    destruct_hypos.
    apply WF_var with (U:=x)...
  -
    apply WF_all with (L:=L )...
    apply IHWF with (S0:=S)...
    intros.
    rewrite_env ((X0 ~ bind_sub T1 ++ E1) ++ map (subst_tb X T) E ++ E2). 
    eapply H1 with (S0:=S)...
  -
    apply WF_rec with (L:=L );intros...
    rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ map (subst_tb X T) E ++ E2). 
    eapply H0 with (S0:=S)...
    rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ map (subst_tb X T) E ++ E2). 
    eapply H2 with (S0:=S)...
Qed.

Lemma notin_fl_env: forall E X Y U,
    binds X (bind_sub U) E ->
    Y \notin fl_env E ->
    Y \notin fl_tt U.
Proof with eauto.
  induction E;intros...
  simpl in *.
  destruct a.
  destruct b...
  -
    analyze_binds H.
    inversion BindsTacVal...
    apply IHE with (X:=X)...
  -
    analyze_binds H.
    apply IHE with (X:=X)...
Qed.

Lemma sub_tvar_trans_var: forall X A E B,
    binds X (bind_sub A) E ->
    sub E X B ->
    (typ_fvar X) <> B ->
    sub E A B.
Proof with auto.
  intros.
  generalize dependent A.
  dependent induction H0;intros...
  -
    destruct H1...
  -
    constructor...
    apply WF_from_binds_typ with (x:=X)...
  -
    apply  binds_uniq with (A:=A) in H...
    subst...
    get_well_form...
Qed.

Lemma EqDec_eq : forall (A B: typ),
    {A = B} + {A <> B}.
Proof with auto.
  intros.
  decide equality.
  decide equality. 
Qed.  

Lemma mu_transform_0: forall C  (Y X:atom) A ,
    type (typ_mu C) ->
    X <> Y ->
    (subst_tt X (typ_mu C) (open_tt A (typ_label Y (open_tt A Y)))) =
 (open_tt (subst_tt X (typ_mu C) A)
       (typ_label Y (open_tt (subst_tt X (typ_mu C) A) Y))).
Proof with auto.
  intros.
  rewrite subst_tt_open_tt...
  f_equal.
  simpl...
  f_equal.
  rewrite subst_tt_open_tt_var...
Qed.

Lemma mu_transform_1: forall (X Y:atom) A C,
    X <> Y ->
    type (open_tt C X) ->
    (open_tt (subst_tt X (typ_label X (open_tt C X)) A)
                 (typ_label Y (open_tt (subst_tt X (typ_label X (open_tt C X)) A) Y))) =
    (subst_tt X (typ_label X (open_tt C X)) (open_tt A (typ_label Y (open_tt A Y)))).
Proof with auto.
  intros.
  rewrite subst_tt_open_tt...
  f_equal...
  simpl...
  f_equal...
  rewrite subst_tt_open_tt...
  f_equal...
  simpl...
  destruct (Y==X)...
  destruct H...
Qed.  

Lemma sub_generalize_intensive : forall E1 E2 A B C D X m S,
    sub (E1 ++ X ~ bind_sub typ_top ++ E2) A B ->
    X \notin fv_tt C \u fv_tt D \u fl_env E1 \u fl_env E2 \u fl_tt A \u fl_tt B \u dom E1 \u dom E2 \u fv_tt S ->
    sub (map (subst_tb X (typ_label X (open_tt S X))) E1 ++ X ~ bind_sub typ_top ++ E2) (subst_tt X (typ_label X (open_tt C X)) A) (subst_tt X (typ_label X  (open_tt D X)) B) ->
    sub E2 (typ_mu (choose m C S))  (typ_mu (choose m S C)) ->
    sub E2 (typ_mu (choose m S D))  (typ_mu (choose m D S)) ->
    sub (map (subst_tb X (typ_mu S)) E1 ++ E2) (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B).
Proof with auto.
  intros.
  generalize dependent m.
  generalize dependent C.
  generalize dependent D.
  generalize dependent S.
  dependent induction H;intros...
  -
    simpl.
    constructor...
    apply subst_tt_wf_env_label_rec...
    get_well_form...
    destruct m;simpl in *;get_well_form...
  -
    simpl in *.
    destruct (X0==X);subst...
    +
      assert (wf_env (empty ++ map (subst_tb X (typ_mu S)) E1 ++ E2)).
      apply subst_tt_wf_env_label_rec...
      get_well_form...
      destruct m;simpl in *;get_well_form...
      rewrite_env (nil ++ map (subst_tb X (typ_mu S)) E1 ++ E2).
      apply Sub_weakening...
      destruct m;simpl in *...
      *
        apply sub_transitivity with (Q:=typ_mu S)...
      *
        assert (sub E2 (typ_mu D) (typ_mu C)).
        apply sub_transitivity with (Q:=typ_mu S)...
        dependent destruction H6.
        dependent destruction H2.
        apply sub_strengthening_env in H2...
        pick fresh Y.
        specialize_x_and_L Y L.
        apply sub_nominal_inversion in H8...
        rewrite_env (nil ++ (X, bind_sub typ_top) :: E) in H2.
        apply Sub_renaming with (Y:=Y) in H2...
        simpl in H2.
        rewrite <- subst_tt_intro in H2...
        rewrite <- subst_tt_intro in H2...
        apply sub_antisymmetry in H2...
        apply open_tt_var_rev in H2...
        subst.
        apply Reflexivity;get_well_form...
        solve_notin.
        simpl...
        constructor...
        get_well_form...
        constructor...
        get_well_form...
        pick fresh Y.
        specialize_x_and_L Y L.
        rewrite_env (nil ++ Y ~ bind_sub typ_top ++ E) in H7.
        apply WF_renaming with (Y:=X) in H7...
        simpl in H7...
        rewrite <- subst_tt_intro in H7...
        solve_notin.
        pick fresh Y.
        specialize_x_and_L Y L.
        rewrite_env (nil ++ Y ~ bind_sub typ_top ++ E) in H6.
        apply WF_renaming with (Y:=X) in H6...
        simpl in H6...
        rewrite <- subst_tt_intro in H6...
        solve_notin.   
    +
      constructor...
      apply subst_tt_wf_env_label_rec...
      get_well_form...
      destruct m;simpl in *;get_well_form...
      assert (typ_fvar X0 = subst_tt X (typ_mu S) (typ_fvar X0)).
      simpl...
      destruct (X0==X);subst...
      destruct n...
      rewrite H5.
      apply subst_tb_wf with (Q:=bind_sub typ_top)...
      destruct m;simpl in *;get_well_form...
  -
    simpl.
    constructor...
    apply subst_tt_wf_env_label_rec...
    get_well_form...
    destruct m;simpl in *;get_well_form...
    rewrite_env (nil ++ map (subst_tb X (typ_mu S)) E1 ++ E2).
    apply  WF_narrowing_env with (S:=typ_mu C).
    apply subst_tb_wf with (Q:=bind_sub typ_top)...
    destruct m;simpl in *;get_well_form...
  -
    simpl in *.
    destruct (X0==X);subst...
    +
      analyze_binds_uniq H.
      apply uniq_from_wf_env...
      get_well_form...
      inversion BindsTacVal;subst.
      dependent destruction H0.
      simpl...
      constructor...
      apply subst_tt_wf_env_label_rec...
      get_well_form...
      destruct m;simpl in *;get_well_form...
      rewrite_env (nil ++ map (subst_tb X (typ_mu S)) E1 ++ E2).
      apply  WF_narrowing_env with (S:=typ_mu C).
      apply WF_weakening...
      destruct m;simpl in *;get_well_form...
    +
      destruct ( EqDec_eq T  (typ_fvar X0)).
      *
        induction T;try solve [inversion e].
        rewrite e in *.
        simpl...
        destruct (X0==X);subst...
        destruct n...
        constructor...
        apply subst_tt_wf_env_label_rec...
        get_well_form...
        destruct m;simpl in *;get_well_form...
        apply WF_var with (U:=subst_tt X (typ_mu S) U)...
        apply binds_map_free_env2...
        get_well_form...
      *
        apply sa_trans_tvar with (U:=subst_tt X (typ_mu S) U)...
        --
          apply binds_map_free_env2...
          get_well_form...
        --
          apply IHsub with (m:=m)...
          ++
            solve_notin.
            apply notin_fl_env with (X:=X0) (E:=E1 ++ (X, bind_sub typ_top) :: E2)...
            solve_notin.
          ++
            apply sub_tvar_trans_var with (A:=subst_tt X (typ_label X (open_tt S X)) U) in H2...
            **
              apply binds_map_free_env...
              get_well_form...
            **
              induction T;simpl;try solve [intros v;inversion v]...
              destruct (a==X);subst...
              intros v;inversion v.
          ++
            destruct m;simpl in *;apply Reflexivity;get_well_form...
  -
    simpl in *.
    dependent destruction H2.
    constructor...
    +
      apply IHsub1 with (m:=flip m)...
      destruct m;simpl in *...
      destruct m;simpl in *...
    +
      apply IHsub2 with (m:=m)...
  -
    simpl in *.
    dependent destruction H3.
    apply subst_reverse in x...
    destruct_hypos;subst.
    destruct H7.
    +
      apply open_tt_var_rev in H7...
      subst.
      apply sa_all with (L:=L \u L0  \u {{X}});intros...
      *
        rewrite_env (nil ++ map (subst_tb X (typ_mu S0)) E1 ++ E2).
        apply WF_narrowing_env with (S:=typ_mu D).
        simpl.
        apply subst_tb_wf with (Q:=bind_sub typ_top)...
        destruct m;simpl in *;get_well_form...
      *
        assert (D = S0).
        {
          destruct m;simpl in *;
            apply sub_antisymmetry in H5...
          inversion H5...
          get_well_form...
          get_well_form...
          inversion H5...
          get_well_form...
          get_well_form...
        }
        subst.
        assert (type (typ_mu S0) ).
        destruct m;simpl in *;get_type...
        rewrite subst_tt_open_tt_var...
        rewrite subst_tt_open_tt_var...
        rewrite_env ( map (subst_tb X (typ_mu S0)) (X0~bind_sub S++ E1) ++ E2).
        apply H1 with (m:=m)...
        --
          solve_notin.
        --
          rewrite <- subst_tt_open_tt_var...
          rewrite <- subst_tt_open_tt_var...
          apply H4...
          dependent destruction H9.
          constructor...
          pick fresh Z.
          rewrite subst_tt_intro with (X:=Z)...
          apply subst_tt_type...
          dependent destruction H9.
          constructor...
          pick fresh Z.
          rewrite subst_tt_intro with (X:=Z)...
          apply subst_tt_type...
    +
      assert (subst_tt X (typ_mu C) S = subst_tt X (typ_mu S0) S).
      rewrite <- subst_tt_fresh...
      rewrite <- subst_tt_fresh...
      assert (subst_tt X (typ_mu D) S = subst_tt X (typ_mu S0) S).
      rewrite <- subst_tt_fresh...
      rewrite <- subst_tt_fresh...
      rewrite H9.
      rewrite H10.
      apply sa_all with (L:=L \u L0  \u {{X}});intros...
      *
        apply subst_tb_wf with (Q:=bind_sub typ_top)...
        destruct m;simpl in *;get_well_form...
      *
        rewrite_env ( map (subst_tb X (typ_mu S0)) (X0~bind_sub S ++ E1) ++ E2).
        rewrite subst_tt_open_tt_var...
        rewrite subst_tt_open_tt_var...
        apply H1 with (m:=m)...
        --
          solve_notin.
        --
          rewrite_env ( X0 ~ bind_sub (subst_tt X (typ_label X (open_tt S0 X)) S) ++ map (subst_tb X (typ_label X (open_tt S0 X))) E1 ++ (X, bind_sub typ_top) :: E2).
          assert (subst_tt X (typ_label X (open_tt S0 X)) S = subst_tt X (typ_label X (open_tt C X)) S).
          rewrite <- subst_tt_fresh...
          rewrite <- subst_tt_fresh...
          rewrite H12.
          rewrite <- subst_tt_open_tt_var...
          rewrite <- subst_tt_open_tt_var...
          ++
            assert (type (typ_mu D)).
            destruct m;simpl in *;get_type...
            dependent destruction H13.
            constructor.
            pick fresh Z.
            rewrite subst_tt_intro with (X:=Z)...
            apply subst_tt_type...
          ++
            assert (type (typ_mu C)).
            destruct m;simpl in *;get_type...
            dependent destruction H13.
            constructor.
            pick fresh Z.
            rewrite subst_tt_intro with (X:=Z)...
            apply subst_tt_type...
        --
          destruct m;simpl in *;get_type...
        --
          destruct m;simpl in *;get_type...
  -
    simpl in *.
    dependent destruction H4.
    apply sa_rec with (L:=L \u L0 \u {{X}} \u fv_tt C \u fv_tt D   \u dom E1 \u dom E2);intros...
    +
      rewrite subst_tt_open_tt_var...
      rewrite_env (nil ++ map (subst_tb X (typ_mu S)) (X0~bind_sub typ_top ++ E1) ++ E2).
      apply WF_narrowing_env with (S:=typ_mu C)...
      apply subst_tb_wf with (Q:=bind_sub typ_top)...
      apply H...
      destruct m;simpl;get_well_form...
      destruct m;simpl;get_type...
    +
      rewrite subst_tt_open_tt_var...
      rewrite_env (nil ++ map (subst_tb X (typ_mu S)) (X0~bind_sub typ_top ++ E1) ++ E2).
      apply WF_narrowing_env with (S:=typ_mu D)...
      apply subst_tb_wf with (Q:=bind_sub typ_top)...
      apply H0...
      destruct m;simpl;get_well_form...
      destruct m;simpl;get_type...
    +
      assert (type (typ_mu C) /\ type (typ_mu D)).
      split;destruct m;simpl in *;get_type...
      destruct_hypos.
      rename X0 into Y.
      rewrite_env (map (subst_tb X (typ_mu S)) (Y~bind_sub typ_top ++ E1) ++ E2).
      rewrite <- mu_transform_0...
      rewrite <- mu_transform_0...
      apply H2 with (X1:=X) (X0:=Y) (m:=m)...
      *
        solve_notin.
      *
        rewrite <- mu_transform_1...
        rewrite <- mu_transform_1...
        apply H6...
        dependent destruction H11.
        pick fresh Z.
        rewrite subst_tt_intro with (X:=Z)...
        apply subst_tt_type...
        dependent destruction H10.
        pick fresh Z.
        rewrite subst_tt_intro with (X:=Z)...
        apply subst_tt_type...
  -
    simpl in *.
    dependent destruction H1.
    constructor...
    apply IHsub with (m:=m)...
Qed.
    
          
 
Lemma unfolding_lemma: forall E A B,
    sub E (typ_mu A) (typ_mu B) ->
    sub E (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof with auto.
  intros.
  assert (Ht:=H).
  dependent destruction H.
  pick fresh X.
  rewrite subst_tt_intro with (X:=X)...
  remember (subst_tt X (typ_mu A) (open_tt A X)) .
  rewrite subst_tt_intro with (X:=X)...
  subst.
  rewrite_env (map (subst_tb X (typ_mu B)) nil ++ E).
  apply sub_generalize_intensive with (m:=Pos)...
  -
    specialize_x_and_L X L.
    apply sub_nominal_inversion in H1...
  -
    solve_notin.
  -
    simpl.
    rewrite <- subst_tt_intro...
    rewrite <- subst_tt_intro...
    apply H1...
  -
    get_well_form.
    apply Reflexivity...
Qed.
