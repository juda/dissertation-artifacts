Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export definition.

Lemma notin_fv_tt_open : forall X U T,
    X `notin` fv_tt T ->
    X \notin fv_tt U ->
    X `notin` fv_tt (open_tt T U).
Proof with auto.
  intros.
  simpl.
  unfold open_tt.
  unfold open_tt_rec.
  generalize 0.
  induction T;simpl in *;intros...
  destruct (n0==n)...
Qed.


Lemma notin_fl_tt_open : forall X U T,
    X `notin` fl_tt T ->
    X \notin fl_tt U ->
    X `notin` fl_tt (open_tt T U).
Proof with auto.
  intros.
  unfold open_tt.
  unfold open_tt_rec.
  generalize 0.
  induction T;simpl in *;intros...
  destruct (n0==n)...
Qed.

Lemma notin_union: forall X A B,
    X `notin` (union A B) <->
    X `notin` A /\ X `notin` B.
Proof with auto.
  split.
  intros;split...
  intros;destruct H...
Qed.

Lemma notin_fv_subst2: forall X A B Y,
    X \notin fv_tt A ->
    X \notin fv_tt B ->
    X <> Y ->
    X \notin fv_tt (subst_tt Y A B).
Proof with auto.
  intros.
  induction B...
  -
    simpl.
    destruct (a == Y)...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
Qed.

Lemma notin_fv_subst: forall X A B,
    X \notin fv_tt A ->
    X \notin fv_tt B ->
    X \notin fv_tt (subst_tt X A B).
Proof with auto.
  intros.
  induction B...
  -
    simpl.
    destruct (a == X)...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
Qed.



Lemma in_dec: forall T X,
    X \notin T \/ X \in T.
Proof.
  intros.
  apply notin_diff_1.
  assert (AtomSetImpl.diff T T [=] {}).
  apply AtomSetProperties.diff_subset_equal.
  apply KeySetProperties.subset_refl.
  rewrite H.
  auto.
Qed.

Ltac destruct_hypos :=
  repeat
    match goal with
    | [H : _ /\ _ |- _ ] => destruct H
    | [H : exists _,_ |- _ ] => destruct H                                  
    end.

Ltac specialize_x_and_L X L :=
  repeat match goal with
         | [H : forall _, _ \notin L -> _, Q : X \notin L |- _ ] => specialize (H _ Q); clear Q
         | [H : forall _, _ \notin L -> _ |- _ ] => assert (X \notin L) by auto
         end.


Ltac add_nil :=
    match goal with
    | [ |- WFS ?E _ ] => rewrite_alist (nil ++ E)                               
    | [ |- Sub ?E _ _ ] => rewrite_alist (nil ++ E)                                  
    end.


Lemma type_subst : forall A, 
    forall X B, type B -> type (subst_tt X B A) -> type A.
Proof with auto.
  intros.
  dependent induction H0;try solve [destruct A; simpl in *; inversion x; eauto]...
    destruct A; simpl in *; inversion x; eauto.
    apply type_mu with (L := union L (singleton X)).
    intros.
    specialize_x_and_L X0 L.
    eapply (H0 B H X); eauto.
    subst.
    apply subst_tt_open_tt_var; eauto.
Defined.

Lemma WFS_type: forall E T,
    WFS E T -> type T.
Proof with auto.
  intros.
  induction H...
  apply type_mu with (L:=L)...
Qed.

Lemma subst_tt_rcd: forall  Y X A B,
    (typ_rcd X (subst_tt Y A B)) = subst_tt Y A (typ_rcd X B).
Proof with auto.
  intros...
Qed.  


Lemma WFS_weakening: forall E1 E2 T E,
    WFS (E1 ++ E2) T ->
    WFS (E1 ++ E ++ E2) T.
Proof with auto.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    apply WFS_rec with (L:=L)...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply H0...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply H2...
Qed.

Lemma subst_tt_wfs: forall A B E X,
    WFS E A ->
    WFS E B ->
    WFS E (subst_tt X A B).
Proof with auto.
  intros.
  generalize dependent A.
  dependent induction H0;intros;simpl in *...
  -
    destruct (X0==X)...
  -
    assert (type A0).
    apply WFS_type in H3...
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A0).
    intros.
    rewrite  subst_tt_open_tt_var...
    rewrite  subst_tt_rcd.
    rewrite  <- subst_tt_open_tt...
    apply H0...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
    apply WFS_weakening...
    intros.
    rewrite  subst_tt_open_tt_var...
    apply H2...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
    apply WFS_weakening...
Qed.

Lemma subst_tt_wfs2: forall Y B E1 E2 X,
    WFS (E1 ++ (X ~ bind_sub) ++ E2) B ->
    WFS (E1 ++ (Y ~ bind_sub) ++ E2) (subst_tt X Y B).
Proof with auto.
  intros.
  dependent induction H;intros;simpl in *...
  -
    destruct (X0==X)...
    analyze_binds H...
  -
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A \u {{Y}});intros.
    rewrite  subst_tt_open_tt_var...
    rewrite  subst_tt_rcd.
    rewrite  <- subst_tt_open_tt...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ (Y, bind_sub) :: E2).
    apply H0...
    rewrite  subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ (Y, bind_sub) :: E2).
    apply H2...
Qed.

Lemma subst_tt_wfs3: forall  B E1 E2 X A,
    WFS (E1 ++ (X ~ bind_sub) ++ E2) B ->
    WFS (E1 ++ E2 ) A ->
    X \notin fv_tt A ->
    WFS (E1 ++ E2) (subst_tt X A B).
Proof with auto.
  intros.
  dependent induction H;intros;simpl in *...
  -
    destruct (X0==X)...
    analyze_binds H...
  -
    assert (type A).
    apply WFS_type in H3...
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A );intros.
    rewrite  subst_tt_open_tt_var...
    rewrite  subst_tt_rcd.
    rewrite  <- subst_tt_open_tt...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
    apply WFS_weakening...
    rewrite  subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H2...
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
    apply WFS_weakening...
Qed.

Lemma sub_regular : forall E A B ,
    Sub E A B -> wf_env E /\ WFS E A /\ WFS E B.
Proof with auto.
  intros.
  dependent induction H;try solve [destruct_hypos;repeat split;auto]...
  -
    split.
    pick fresh X.
    specialize_x_and_L X L.
    destruct_hypos.
    dependent destruction H2...
    split;
      apply WFS_rec with (L:=L \u fv_tt A1 \u fv_tt A2);intros...
    eapply H2...
    eapply H2...
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


Lemma and_inv : forall E A B C, Sub E A (typ_and B C) -> Sub E A B /\ Sub E A C.
Proof with auto.
  intros E A B C s.
  dependent induction s...
  -
    dependent destruction H0...
  -
    destruct (sub_regular s).
    dependent destruction H1.
    destruct IHs with (B0:=B) (C0:=C)...
  -
    destruct IHs with (B0:=B) (C0:=C)...    
Qed.

    
(* =============================== *)
(* =============================== *)
(* =============================== *)
(* =============================== *)
(* =============================== *)
(* =============================== *)


Ltac get_well_form :=
    repeat match goal with
           | [ H : Sub _ _ _ |- _ ] => apply sub_regular in H;destruct_hypos
           end.

Ltac get_type :=
    repeat match goal with
           | [ H : Sub _ _ _ |- _ ] => get_well_form
           | [ H : WFS _ _ |- _ ] => apply WFS_type in H
           end.



Lemma Reflexivity : forall E A,
    wf_env E ->
    WFS E A ->
    Sub E A A.
Proof with auto.
  intros.
  induction H0...
  apply S_rec with (L:=L \u dom E);intros...
Qed.

Lemma WFS_strengthening: forall E1 E2 T X m,
    WFS (E1 ++ X ~ m ++ E2) T->
    X \notin fv_tt T ->
    WFS (E1 ++ E2) T.
Proof with auto.
  intros.
  dependent induction H;try solve [simpl in *;constructor;eauto]...
  -
    analyze_binds H...
    simpl.
    apply D.F.singleton_iff...
  -
    simpl in *.
    apply WFS_rec with (L:=L \u {{X}} \u fv_tt A).
    intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (m0:=m)...
    apply notin_fv_tt_open...
    simpl.
    apply notin_fv_tt_open...
    intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H2 with (X1:=X) (m0:=m)...
    apply notin_fv_tt_open...
Qed.

Lemma trans_aux : forall E B,
    WFS E B ->
    forall A C,
      Sub E A B -> Sub E B C -> Sub E A C.
Proof with auto.
  intros E B H.
  dependent induction H;intros...
  - (* top *)
    dependent induction H...
    +
      constructor...
      get_well_form...
    +
      dependent induction H1...
  - (* bot *)
    dependent induction H...
  - (* nat *)
    dependent induction H...
    +
      constructor...
      get_well_form...
  - (* and *)
    dependent induction H0...
    +
      constructor...
      get_well_form...
    +
      apply S_andL...
      apply IHSub with (X0:=X)...
    +
      apply S_andR...
      apply IHSub with (X0:=X)...
  - (* arrow *)
    assert (WFS E A0).
    get_well_form...
    assert (WFS E C).
    get_well_form...
    dependent induction H3... (* induction A0 *)
    + (* top *)
      dependent destruction H1...
    + (* bot *)
      constructor...
      get_well_form...
    + (* nat *)
      dependent destruction H1.
    + (* var *)
      dependent destruction H1.
    + (* arrow *)
      dependent induction H4;try solve [dependent destruction H2;inversion H3]...
      * (* top *)
        constructor...
        get_well_form...
      * (* arrow *)
        clear IHWFS5 IHWFS3 IHWFS4 IHWFS6.
        dependent destruction H1.
        dependent destruction H2.
        constructor...
      * (* and *)
        destruct (and_inv H2).
        dependent destruction H1.
        --
          constructor.
          ++
            apply IHWFS5...
            intros.
            assert (Sub E A0 (typ_and A1 B1)).
            apply IHWFS3...
            destruct (and_inv H9)...
            intros.
            assert (Sub E B0 (typ_and A1 B1)).
            apply IHWFS4...
            destruct (and_inv H9)...
          ++
            apply IHWFS6...
            intros.
            assert (Sub E A0 (typ_and A1 B1)).
            apply IHWFS3...
            destruct (and_inv H9)...
            intros.
            assert (Sub E B0 (typ_and A1 B1)).
            apply IHWFS4...
            destruct (and_inv H9)...
    + (* and *)
      dependent induction H1...
    + (* rcd *)
      dependent induction H1...
    + (* rec *)
      dependent induction H1...
  - (* and *)
    destruct (and_inv H1).
    dependent induction H2...
    constructor.
    apply IHSub1 with (A1:=A) (B0:=B)...
    apply IHSub2 with (A1:=A) (B0:=B)...
  - (* rcd *)
    assert (WFS E A /\ WFS E C /\ wf_env E).
    get_well_form...
    destruct_hypos.
    dependent induction H2; try solve [inversion H0;dependent destruction H0;auto]...
    + (* rcd *)
      dependent induction H1...
      *
        assert (Sub E (typ_rcd l T) (typ_and B1 B2)) as qt.
        constructor...
        constructor...
        apply IHSub1 with (l1:=l) (T1:=T)...
        intros.
        specialize (IHWFS0 H1 IHWFS1 H5 qt H3 H4).
        apply and_inv in IHWFS0.
        destruct IHWFS0...
        inversion H3...
        apply IHSub2 with (l1:=l) (T1:=T)...
        intros.
        specialize (IHWFS0 H1 IHWFS1 H5 qt H3 H4).
        apply and_inv in IHWFS0.
        destruct IHWFS0...
        inversion H3...
      *
        inversion H0;subst.
        --
          dependent destruction H0...
  - (* rec *)
    dependent induction H3...
    + (* bot *)
      constructor...
      get_well_form...
    + (* andL *)
      apply S_andL...
      apply IHSub with (A0:=A)...
    + (* andR *)
      apply S_andR...
      apply IHSub with (A0:=A)...
    + (* rec *)
      clear H4 H6.
      dependent induction H7...
      * (* and *)
        constructor...
        eapply IHSub1...
        eapply IHSub2...
      * (* rec *)
        apply S_rec with (L:=L \u L0 \u L1)...
      *
        apply S_top...
        apply WFS_rec with (L:= L \u L0);intros.
        specialize_x_and_L X L0.
        get_well_form...
        specialize_x_and_L X L0.
        get_well_form...
Qed.


Lemma Transitivity : forall E B A C,
      Sub E A B -> Sub E B C -> Sub E A C.
Proof with auto.
  intros.
  assert (WFS E B).
  apply sub_regular in H0.
  apply H0.
  apply trans_aux with (B:=B)...
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
    apply WFS_weakening...
  -
    constructor...
    apply WFS_weakening...
  -
    constructor...
    apply WFS_weakening... 
  -
    apply S_andR...
    apply WFS_weakening...
  -
    apply S_rec with (L:=L \u dom (E1 ++ E ++ E2))...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply WFS_weakening...
    rewrite_alist ([(X, bind_sub)] ++ E1 ++ E2)...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply WFS_weakening...
    rewrite_alist ([(X, bind_sub)] ++ E1 ++ E2)...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply H2...
    rewrite_alist ([(X, bind_sub)] ++ E1 ++ E ++ E2)...
  -
    apply S_top...
    apply WFS_weakening...
Qed.


Lemma label_transform3: forall A (X X0 Y : atom),
    X <> X0 ->
    (subst_tt X Y (open_tt A (typ_rcd X0 (open_tt A X0)))) =
(open_tt (subst_tt X Y A) (typ_rcd X0 (open_tt (subst_tt X Y A) X0))).
Proof with auto.
  intros.
  rewrite  subst_tt_open_tt...
  f_equal...
  simpl.
  f_equal...
  rewrite  subst_tt_open_tt_var...
Qed.  


  

Lemma WFS_replacing: forall E1 E2 T X Y,
    WFS (E1++ X ~ bind_sub ++E2) T ->
    X <> Y ->
    WFS (E1++ Y ~ bind_sub ++E2) (subst_tt X Y T).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros;simpl;try solve [rewrite_alist (E1 ++ Y ~ bind_sub ++ E2);constructor;auto]...
  -
    destruct (X0==X)...
    constructor.
    analyze_binds H.
  -
    apply WFS_rec with (L:=L \u {{X}});intros.
    rewrite <- label_transform3...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H0...
    rewrite  subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H2...
Qed.


Lemma Sub_replacing: forall E1 E2 A B X Y,
    Sub (E1++ X ~ bind_sub ++E2) A B ->
    X <> Y ->
    wf_env (E1 ++ Y ~ bind_sub ++ E2) ->
    Sub (E1++ Y ~ bind_sub ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros;simpl;try solve [rewrite_alist (E1 ++ [(Y, bind_sub)] ++ E2);constructor;auto;apply  WFS_replacing;auto]...
  -
    destruct (X0==X)...
    constructor...
    constructor...
    dependent destruction H0.
    analyze_binds H0.
  -
    apply S_rec with (L:=L  \u {{X}} \u dom (E1 ++ [(Y, bind_sub)] ++ E2) );intros...
    rewrite  subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply WFS_replacing...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ [(X, bind_sub)] ++ E2)...
    rewrite  subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply WFS_replacing...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ [(X, bind_sub)] ++ E2)...
    rewrite <- label_transform3...
    rewrite <- label_transform3...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H2...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
Qed.


Fixpoint subst_tl (Z : atom) (U : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bot => typ_bot               
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (subst_tl Z U T1) (subst_tl Z U T2)
  | typ_and T1 T2 => typ_and (subst_tl Z U T1) (subst_tl Z U T2)
  | typ_mu T => typ_mu (subst_tl Z U T)
  | typ_rcd l T => if (l==Z) then typ_rcd U (subst_tl Z U T) else typ_rcd l (subst_tl Z U T)
  end.

Lemma subst_tl_open_tt_rec : forall Z  A (X Y : atom) k,
    subst_tl X Y (open_tt_rec k A Z) = open_tt_rec k (subst_tl X Y A) (subst_tl X Y Z).
Proof with auto.
  intros Z.
  induction Z;intros ; simpl in *; f_equal...
  -
    destruct (k==n)...
  -
    destruct (a==X);subst;simpl...
    f_equal...
    f_equal...
Qed.    

Lemma subst_tl_open_tt : forall A Z (X Y : atom),
    subst_tl X Y (open_tt A Z) = open_tt (subst_tl X Y A) (subst_tl X Y Z).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tl_open_tt_rec...
Qed.

Lemma subst_tl_open_tt_var : forall A (X Y Z: atom),
    subst_tl X Y (open_tt A Z) = open_tt (subst_tl X Y A) Z.
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tl_open_tt_rec...
Qed.  
  
Lemma label_transform2: forall A (X X0 Y : atom),
    X <> X0 ->
    (subst_tl X Y (open_tt A (typ_rcd X0 (open_tt A X0)))) =
(open_tt (subst_tl X Y A) (typ_rcd X0 (open_tt (subst_tl X Y A) X0))).
Proof with auto.
  intros.
  rewrite  subst_tl_open_tt...
  f_equal...
  simpl.
  destruct (X0==X);subst...
  destruct H...
  f_equal...
  rewrite subst_tl_open_tt...
Qed.


Lemma WFS_replacing2: forall E T X Y,
    WFS E T ->
    X <> Y ->
    WFS E (subst_tl X Y T).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros;simpl;try solve [constructor;auto]...
  -
    destruct (l==X);subst...
  -
    apply WFS_rec with (L:=L \u {{X}});intros.
    rewrite <- label_transform2...
    rewrite <- subst_tl_open_tt_var...
Qed.


Lemma Sub_replacing2: forall E A B X Y,
    Sub E A B ->
    X <> Y ->
    Sub E (subst_tl X Y A) (subst_tl X Y B).
Proof with eauto using WFS_replacing2.
  intros.
  generalize dependent Y.
  dependent induction H;intros;simpl;try solve [constructor;auto]...
  -
    apply S_rec with (L:=L  \u {{X}} \u dom E );intros...
    rewrite <- subst_tl_open_tt_var...
    rewrite <- subst_tl_open_tt_var...
    rewrite <- label_transform2...
    rewrite <- label_transform2...
  -
    destruct (l==X);subst...
Qed.

Lemma label_transform1: forall (X Y:atom) A,
    X \notin fv_tt A ->
    (subst_tt X Y (open_tt A (typ_rcd X (open_tt A X)))) =
    (open_tt A (typ_rcd X (open_tt A Y))).
Proof with auto.
  intros.
  rewrite subst_tt_open_tt...
  simpl...
  rewrite <- subst_tt_intro...
  f_equal...
  rewrite <- subst_tt_fresh...
Qed.

Lemma subst_tl_fresh: forall A X Y,
    X `notin` fl_tt A ->
    subst_tl X Y A = A.
Proof with auto.
  induction A;intros;simpl in *;try solve [f_equal;auto]...
  destruct (a==X);subst...
  apply notin_union in H.
  destruct H.
  apply notin_singleton_1 in H...
  destruct H...
  f_equal...
Qed.
    

Lemma label_transform4: forall (X Y Z:atom) A,
    X \notin fl_tt A ->
    (subst_tl X Y (open_tt A (typ_rcd X (open_tt A Z)))) =
    (open_tt A (typ_rcd Y (open_tt A Z))).
Proof with auto.
  intros.
  rewrite subst_tl_open_tt...
  simpl...
  destruct (X==X)...
  f_equal...
  apply subst_tl_fresh...
  f_equal...
  apply subst_tl_fresh...
  apply notin_fl_tt_open...
  destruct n...
Qed.  
  
Lemma Sub_replacing_open: forall E1 E2 A B X Y,
    Sub (E1++ X ~ bind_sub ++E2) (open_tt A (typ_rcd X (open_tt A X))) (open_tt B (typ_rcd X (open_tt B X)))  ->
    Y \notin {{X}} \u fv_tt A \u fv_tt B ->
    X \notin fv_tt A \u fv_tt B \u fl_tt A \u fl_tt B ->
    wf_env (E1 ++ [(Y, bind_sub)] ++ E2) ->
    Sub (E1++ Y ~ bind_sub ++E2) (open_tt A (typ_rcd Y (open_tt A Y))) (open_tt B (typ_rcd Y (open_tt B Y))).
Proof with auto.
  intros.
  apply Sub_replacing with (Y:=Y) in H...
  rewrite label_transform1 in H...
  rewrite label_transform1 in H...
  apply Sub_replacing2 with (X:=X) (Y:=Y) in H...
  rewrite label_transform4 in H...
  rewrite label_transform4 in H...
Qed.  
  

