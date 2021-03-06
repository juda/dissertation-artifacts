Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export infra.

Ltac destructs_hypos :=
  repeat
    match goal with
    | [H : _ /\ _ |- _ ] => destruct H
    end.

Ltac specialize_x_and_L X L :=
  repeat match goal with
         | [H : forall _, _ \notin L -> _, Q : X \notin L |- _ ] => assert(Qt:=Q);specialize (H _ Qt);clear Qt
         | [H : forall _, _ \notin L -> _ |- _ ] => assert (X \notin L) by auto
         end.

Ltac add_nil :=
    match goal with
    | [ |- WF ?E _ ] => rewrite_alist (nil ++ E)
    | [ |- Sub ?E _ _ ] => rewrite_alist (nil ++ E)                                  
    end.


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

Lemma wf_rcd_lookup : forall E i T Ti,
  WF E T ->
  Tlookup i T = Some Ti ->
  WF E Ti.
Proof with eauto.
  intros E i T.
  dependent induction T; intros; try solve [inversion H0]...
  - (* RCons *)
    dependent destruction H.
    simpl in *.
    destruct (a==i)...
    inversion H3; subst...
Qed.

Lemma Sub_regular : forall E A B,
    Sub E A B -> wf_env E /\ WF E A /\ WF E B.
Proof with auto.
  intros.
    induction H;destructs_hypos...
  -
    split.
    pick fresh X.
    specialize_x_and_L X L.
    destructs_hypos.
    dependent destruction H0...
    split;apply WF_rec with (L:=L  \u fv_tt A1 \u fv_tt A2);intros;
      try solve [eapply H0;eauto|eapply H2;eauto]...
    
Qed.

Lemma wf_type: forall E A,
    WF E A -> type A.
Proof with auto.
  intros.
  induction H...
  apply type_mu with (L:=L)...
Qed.  
  
Ltac get_well_form :=
    repeat match goal with
    | [ H : Sub _ _ _ |- _ ] => apply Sub_regular in H;destructs_hypos   
           end.

Ltac get_type :=
    repeat match goal with
           | [ H : Sub _ _ _ |- _ ] => get_well_form
           | [ H : WF _ _ |- _ ] => apply wf_type in H
           end.

Lemma sub_refl : forall E A ,
    wf_env E -> WF E A -> Sub E A A.
Proof with auto.
  intros.
  induction H0...
  -
    apply S_rec with (L:=L \u dom E);intros...
  -
    constructor...
    simpl...
    apply KeySetProperties.FM.Subset_refl...
    intros.
    simpl in *.
    inversion H0.
  -
    dependent induction H0...
    +
      constructor...
      apply KeySetProperties.FM.Subset_refl...
      intros.
      simpl in *...
      destruct (i==i0)...
      inversion H2.
      inversion H0...
      subst...
      inversion H0...
    +
      constructor...
      apply KeySetProperties.FM.Subset_refl...
      apply IHWF2 in H.
      dependent destruction H.
      intros.
      simpl in *.
      destruct (i==i1)...
      inversion H8.
      inversion H7.
      subst...
      apply H5 with (i:=i1)...
Qed.    

Lemma union_empty: forall A i,
    union (singleton i) A [<=] Metatheory.empty -> False.
Proof with eauto.
  intros.
  unfold "[<=]" in H.
  eapply empty_iff...
Qed.

Ltac collect_nil H := simpl in H;apply union_empty in H;destruct H.

Lemma label_belong: forall i A B,
    Tlookup i A = Some B -> i \in collectLabel A.
Proof with auto.
  intros.
  dependent induction A;simpl in *;try solve [inversion H]...
  destruct (a==i)...
  apply IHA2 in H...
Qed.

Lemma label_trans: forall i A B,
    i \in  A -> A [<=] B -> i \in  B .
Proof with auto.
  intros.
  unfold "[<=]" in H0...
Qed.

Lemma lookup_some: forall i T,
    i \in collectLabel T ->
    exists S, Tlookup i T = Some S.
Proof with auto.
  intros.
  induction T;simpl in *;try solve [apply empty_iff in H;destruct H]...
  apply AtomSetImpl.union_1 in H...
  destruct H...
  apply KeySetFacts.singleton_iff in H.
  exists T1...
  destruct (a==i)...
  destruct n...
  apply IHT2 in H...
  destruct H.
  destruct (a==i)...
  exists T1...
  exists x...
Qed.  
  
Lemma rcd_types_match : forall S T E i Ti,
    Sub E S T ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si /\ Sub E Si Ti.
Proof with auto.
  intros.
  dependent induction H;simpl in *;try solve [inversion H1|inversion H0|inversion H3]...
  induction H1...
  simpl in H7;inversion H7.
  induction H0...
  simpl in H2.
  apply union_empty in H2...
  destruct H2.
  assert (Ht:=H7).
  apply label_belong in Ht.
  apply label_trans with (B:=collectLabel (typ_rcd_cons i1 T0 T3)) in Ht...
  apply lookup_some in Ht.
  destruct Ht.
  specialize (H5 i x Ti H0 H7)...
  exists x...
Qed.  

Lemma rcd_inversion: forall A B E,
    Sub E A B ->
    rt_type A ->
    rt_type B ->
    (forall i t1 t2, Tlookup i A = Some t1 ->  Tlookup i B = Some t2 -> Sub E t1 t2).
Proof with auto.
  intros.
  induction H;try solve [inversion H0|inversion H1]...
  apply H9 with (i:=i)...
Qed.

Fixpoint dropLabel (Z : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (dropLabel Z  T1) (dropLabel Z  T2)
  | typ_mu T => typ_mu (dropLabel Z  T)
  | typ_rcd_nil     => typ_rcd_nil
  | typ_rcd_cons i T1 T2  => if (i==Z) then (dropLabel Z T2) else (typ_rcd_cons i T1 (dropLabel Z T2))
  end.

Lemma rt_type_drop: forall E A i,
    WF E A ->
    rt_type A -> rt_type (dropLabel i A).
Proof with auto.
  intros.
  induction H;try solve [inversion H0]...
  simpl.
  destruct (i0==i)...
Qed.

Lemma union_subset_x: forall a b c,
    b [<=] c ->
    union a b [<=] union a c.
Proof with auto.
  intros.
  apply AtomSetProperties.union_subset_3...
  apply AtomSetProperties.union_subset_1...
  apply KeySetProperties.subset_trans with (s2:=c)...
  apply AtomSetProperties.union_subset_2...
Qed.

Lemma drop_collect: forall A i,
    collectLabel A [<=] {{i}} \u collectLabel (dropLabel i A).
Proof with auto.
  intros.
  induction A;simpl;try solve [apply AtomSetProperties.union_subset_2]...
  destruct (a==i)...
  subst.
  apply AtomSetProperties.union_subset_3 with (s:={{i}}) in IHA2...
  apply AtomSetProperties.union_subset_1.
  simpl.
  rewrite <- AtomSetProperties.union_assoc...
  assert (union (singleton i) (singleton a) [=] {{a}} \u {{i}}).
  rewrite  KeySetProperties.union_sym...
  apply KeySetProperties.equal_refl...
  rewrite H.
  rewrite  AtomSetProperties.union_assoc...
  apply union_subset_x...
Qed.

Lemma drop_coolect_less: forall A i,
    collectLabel (dropLabel i A) [<=] collectLabel A.
Proof with auto.
  intros.
  induction A;simpl in *;try solve [apply F.Subset_refl]...
  destruct (a==i)...
  apply KeySetProperties.subset_trans with (s2:=collectLabel A2)...
  apply AtomSetProperties.union_subset_2.
  simpl...
  apply union_subset_x...
Qed.

Lemma drop_collect_flip: forall A i,
    i \in collectLabel A ->
    {{i}} \u collectLabel (dropLabel i A) [<=] collectLabel A.
Proof with auto.
  intros.
  induction A;simpl in *;try solve [apply KeySetFacts.empty_iff in H;destruct H]...
  apply F.union_iff in H.
  destruct H...
  apply AtomSetImpl.singleton_1 in H...
  destruct (a==i)...
  subst.
  apply union_subset_x...
  apply drop_coolect_less...
  destruct n...
  destruct (a==i)...
  subst.
  apply union_subset_x...
  apply drop_coolect_less...
  apply IHA2 in H.
  simpl...
  rewrite <- AtomSetProperties.union_assoc...
  assert (union (singleton i) (singleton a) [=] {{a}} \u {{i}}).
  rewrite  KeySetProperties.union_sym...
  apply KeySetProperties.equal_refl...
  rewrite H0.
  rewrite  AtomSetProperties.union_assoc...
  apply union_subset_x...
Qed.

Lemma union_subset_x2: forall a b c,
    union {{a}} b [<=] union {{a}} c ->
    a \notin b ->
    b [<=] c.
Proof with auto.
  intros.
  unfold "[<=]" in *.
  intros.
  assert (Ht:=H1).
  apply AtomSetImpl.union_3 with (s:={{a}}) in Ht.
  specialize (H _ Ht).
  apply AtomSetImpl.union_1 in H.
  destruct H...
  apply AtomSetImpl.singleton_1 in H...
  subst.
  assert (False).
  apply H0...
  destruct H.
Qed.

Lemma open_tt_drop_var: forall A (X i : atom)  k,
    (open_tt_rec k X (dropLabel i A) ) = dropLabel i (open_tt_rec k X A).
Proof with auto.
  intro.
  induction A;intros;simpl in *;try solve [f_equal;auto]...
  destruct (k==n)...
  destruct (a==i)...
  simpl.
  f_equal...
Qed.

Lemma wf_weakening: forall E1 E2 T E,
    WF (E1 ++ E2) T ->
    WF (E1 ++ E ++ E2) T.
Proof with auto.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    apply WF_rec with (L:=L);intros;rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply H0...
    apply H2...    
Qed.


Lemma  subst_tt_rt_type : forall E A B X,
    WF E A  ->
    rt_type  B ->
    WF E B ->
    rt_type  (subst_tt X A B).
Proof with auto.
  intros.
  induction H0...
  dependent destruction H1...
  simpl...
Qed.

Lemma subst_tt_collect: forall T E i X A,
    i `notin` collectLabel T ->
    rt_type T ->
    WF E T ->
    i `notin` collectLabel (subst_tt X A T).
Proof with auto.
  intros.
  induction H1;try solve [inversion H0]...
  simpl in *.
  apply notin_union in H.
  destruct H.
  apply notin_union.
  split...
Qed.  
  
Lemma subst_tt_wf: forall E1 E2 A B X,
    WF (E1 ++ E2) A  ->
    WF (E1 ++ (X~bind_sub) ++ E2) B ->
    WF (E1 ++ E2) (subst_tt X A B).
Proof with auto.
  
    intros.
    dependent induction H0;simpl in *...
    +
      destruct (X0==X)...
      constructor...
      analyze_binds H0...
    +
      assert (type A).
      get_type...
      apply WF_rec with (L:=L \u {{X}} \u fv_tt A);intros...
      rewrite subst_tt_open_tt_var...
      rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
      apply H0...
      add_nil.
      rewrite_alist (empty ++ [(X0, bind_sub)] ++ E1 ++ E2).
      apply wf_weakening...
      rewrite subst_tt_open_tt_var...
      rewrite <- subst_tt_open_tt...
      rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
      apply H2...
      rewrite_alist (empty ++ [(X0, bind_sub)] ++ E1 ++ E2).
      apply wf_weakening...
    +
      constructor...
      apply subst_tt_rt_type with (E:=(E1 ++ (X ~ bind_sub) ++ E2))...
      apply wf_weakening...
      eapply subst_tt_collect...
      eauto.
Qed.

Lemma notin_drop_fv: forall X A i,
    X \notin fv_tt A ->
    X `notin` fv_tt (dropLabel i A).
Proof with auto.
  intros.
  induction A;simpl in *...
  destruct (a==i)...
Qed.

Lemma notin_drop_collect: forall X A i,
    X \notin collectLabel A ->
    X `notin` collectLabel (dropLabel i A).
Proof with auto.
  intros.
  induction A;simpl in *...
  destruct (a==i)...
Qed.

Lemma notin_drop_collect_self: forall  A i,
    i \notin collectLabel A ->
   collectLabel A [=] collectLabel (dropLabel i A).
Proof with auto.
  intros.
  induction A;simpl in *;try solve [apply KeySetProperties.equal_refl]...
  destruct (a==i)...
  apply notin_union in H.
  destruct H.
  subst.
  apply notin_singleton_1 in H.
  destruct H...
  simpl...
  apply notin_union in H.
  destruct H...
  apply KeySetProperties.union_equal_2...
Qed.

Lemma notin_drop_self: forall j A,
    j `notin` collectLabel (dropLabel j A).
Proof with auto.
  intros.
  induction A...
  simpl.
  destruct (a==j)...
Qed.  
  
Lemma WF_drop: forall A i E,
   
    WF E A -> WF E (dropLabel i A).
Proof with auto.
  intros.
  induction H;simpl;try solve [inversion H]...
  apply WF_rec with (L:=L \u fv_tt A \u {{i}});intros.
  unfold open_tt.
  rewrite open_tt_drop_var...
  apply H0...
  rewrite subst_tt_intro with (X:=X)...
  apply subst_tt_wf...
  unfold open_tt.
  rewrite open_tt_drop_var...
  apply H0...
  apply wf_weakening...
  unfold open_tt.
  rewrite open_tt_drop_var...
  apply H0...
  apply notin_drop_fv...
  destruct (i0==i)...
  constructor...
  apply rt_type_drop with (E:=E)...
  apply notin_drop_collect...
Qed.  


Lemma Tlookup_drop:forall i j T A,
    Tlookup j (dropLabel i A) = Some T ->
    Tlookup j A = Some T.
Proof with auto.
  intros.
  induction A;simpl in *;try solve [inversion H]...
  destruct (a==i)...
  destruct (a==j)...
  subst.
  apply label_belong in H.
  assert (j `notin` collectLabel (dropLabel j A2)).
  apply notin_drop_self...
  assert (False).
  apply H0...
  destruct H1.
  simpl in H.
  destruct (a==j)...
Qed.

Lemma Tlookup_drop_flip: forall i A j t,
    Tlookup i A = Some t ->
    i <> j ->
    Tlookup i (dropLabel j A) = Some t.
Proof with auto.
  intros.
  induction A;simpl in *;try solve [inversion H]...
  destruct (a==i)...
  destruct (a==j)...
  subst.
  destruct H0...
  simpl.
  destruct (a==i)...
  destruct n0...
  destruct (a==j)...
  simpl...
  destruct (a==i)...
  destruct n...
Qed.  
  
Lemma trans_aux: forall B E,
    WF E B -> forall A C,
    Sub E A B -> Sub E B C -> Sub E A C.
Proof with auto.
  intros B E H.
  dependent induction H;intros;try solve [dependent destruction H0;dependent destruction H;auto]...
  -
    dependent destruction H...
    dependent destruction H1...
    inversion H2.
    inversion H1.
  -
    dependent destruction H...
    inversion H1.
  -
    dependent destruction H1.
    dependent destruction H0...
    constructor...
    get_well_form...
    inversion H2.
  -
    dependent destruction H1.
    dependent destruction H2...
    constructor...
    get_well_form...
    inversion H2.
    inversion H3.
  -
    dependent destruction H3.
    dependent destruction H5...
    constructor...
    apply WF_rec with (L:=L0);intros...
    specialize_x_and_L X L0.
    get_well_form...
    specialize_x_and_L X L0.
    get_well_form...
    apply S_rec with (L:=L \u L0 \u L1)...
    inversion H6.
    inversion H5.
  -
    dependent destruction H.
    dependent destruction H6...
    induction H8...
    collect_nil H9.
  -
    dependent destruction H3.
    dependent destruction H10...
    apply S_rcd...
    apply F.Subset_trans with (s':=collectLabel (typ_rcd_cons i T1 T2))...    
    intros.

    destruct (i0==i).
    +
      subst.
      assert (Tlookup i (typ_rcd_cons i T1 T2) = Some T1).
      {
        simpl.
        destruct (i==i)...
        destruct n...
      }
      apply IHWF1...
      apply H9 with (i0:=i)...
      apply H16 with (i0:=i)...
    +
      assert (Sub E (dropLabel i A1) T2).
      {
        apply S_rcd...
        apply rt_type_drop with (E:=E)...
        simpl in H6.
        assert (union (singleton i) (collectLabel T2) [<=] {{i}} \u collectLabel (dropLabel i A1)).
        {
          apply KeySetProperties.subset_trans with (s2:=collectLabel A1)...
          apply drop_collect...
        }
        apply union_subset_x2 in H19...
        apply WF_drop...
        intros.
        apply H9 with (i0:=i1)...
        apply Tlookup_drop in H19...
        simpl.
        destruct (i==i1)...
        apply label_belong in H19.
        subst.
        assert (i1 `notin` collectLabel (dropLabel i1 A1)) by apply notin_drop_self.
        assert (False).
        apply H21...
        destruct H22.
      }
      assert (Sub E T2 (dropLabel i A2)).
      {
        apply S_rcd...
        apply rt_type_drop with (E:=E)...
        simpl in H13.
        assert (i \notin  collectLabel A2 \/ i \in collectLabel A2).
        apply in_dec...
        destruct H20.
        rewrite <- notin_drop_collect_self...
        unfold "[<=]" in *.
        intros.
        specialize (H13 _ H21).
        apply union_iff in H13.
        destruct H13...
        apply AtomSetImpl.singleton_1 in H13.
        subst.
        assert (False).
        apply H20...
        destruct H13.
        assert ( {{i}} \u collectLabel (dropLabel i A2) [<=] {{i}} \u (collectLabel T2) ).
        {
          
          apply KeySetProperties.subset_trans with (s2:=collectLabel A2)...
          apply drop_collect_flip...
        }
        apply union_subset_x2 in H21...
        apply notin_drop_self.
        apply WF_drop...
        intros.
        apply H16 with (i0:=i1)...
        simpl.
        destruct (i==i1)...
        apply label_belong in H21.
        subst.
        assert (i1 `notin` collectLabel (dropLabel i1 A2)) by apply notin_drop_self.
        assert (False).
        apply H22...
        destruct H23.
        apply Tlookup_drop in H21...
      }
      assert (Sub E (dropLabel i A1) (dropLabel i A2)).
      {
        apply IHWF2...
      }
      apply rcd_inversion with (i:=i0) (t1:=t1) (t2:=t2) in H21...
      apply rt_type_drop with (E:=E)...
      apply rt_type_drop with (E:=E)...
      apply Tlookup_drop_flip...
      apply Tlookup_drop_flip...
Qed.

Lemma Transitivity: forall B E A C,
    Sub E A B -> Sub E B C -> Sub E A C.
Proof with auto.
  intros.
  apply trans_aux with (B:=B)...
  get_well_form...
Qed.


