Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Export preservation.


Lemma TypedReduce_progress: forall v A,
    value v -> typing nil v Chk A -> exists v', typ_reduce v A v'.
Proof with auto.
  intros.
  apply typing_chk2inf in H0.
  destruct_hypos.
  generalize dependent x.
  generalize dependent v.
  dependent induction A;intros v val...
  - (* top *)
    exists exp_top...
    constructor...
    apply value_lc_expr...
  - (* bot *)
    dependent induction val;intros;try solve [dependent destruction H0;dependent destruction H1;solve_not_toplike]...
    +
      dependent destruction H0...
      dependent destruction H2...
      inversion H3.
    +
      dependent destruction H0...
      *
        dependent destruction H1...
        destruct IHval1 with (x:=A)...
        exists x...
        apply tred_mergeL...
        get_well_form...
        destruct IHval2 with (x:=B)...
        exists x...
        apply tred_mergeR...
        get_well_form...
        solve_not_toplike.
      *
        dependent destruction H3...
        destruct IHval1 with (x:=A)...
        exists x...
        apply tred_mergeL...
        get_well_form...
        destruct IHval2 with (x:=B)...
        exists x...
        apply tred_mergeR...
        get_well_form...
        solve_not_toplike.
  - (* nat *)
    dependent induction val;intros;try solve [dependent destruction H0;dependent destruction H1;solve_not_toplike]...
    +
      exists exp_nat...
    +
      dependent destruction H0...
      dependent destruction H2...
      solve_not_toplike.
    +
      dependent destruction H0...
      *
        dependent destruction H1...
        destruct IHval1 with (x:=A)...
        exists x...
        apply tred_mergeL...
        get_well_form...
        destruct IHval2 with (x:=B)...
        exists x...
        apply tred_mergeR...
        get_well_form...
        solve_not_toplike.
      *
        dependent destruction H3...
        destruct IHval1 with (x:=A)...
        exists x...
        apply tred_mergeL...
        get_well_form...
        destruct IHval2 with (x:=B)...
        exists x...
        apply tred_mergeR...
        get_well_form...
        solve_not_toplike.
  - (* bvar *)
    intros.
    get_well_form.
    dependent destruction H2...
  - (* fvar *)
    intros.
    dependent induction H0;try solve [dependent destruction val|dependent destruction H1;solve_not_toplike]...
    +
      dependent destruction val.
      dependent destruction H1.
      destruct IHtyping1...
      exists x...
      apply tred_mergeL...
      get_well_form...
      destruct IHtyping2...
      exists x...
      apply tred_mergeR...
      get_well_form...
      solve_not_toplike.
    +
      dependent destruction val.
      dependent destruction H3.
      destruct IHtyping1...
      exists x...
      apply tred_mergeL...
      get_well_form...
      destruct IHtyping2...
      exists x...
      apply tred_mergeR...
      get_well_form...
      solve_not_toplike.
  - (* and *)
    assert (Hv:=val).
    dependent induction val;intros;assert (Hq:=H0)...
    +      
      dependent destruction H0...
      destruct (and_inv H1)...
      destruct IHA1 with (v:=(exp_abs A t1 B)) (x:=(typ_arrow A B))...
      destruct IHA2 with (v:=(exp_abs A t1 B)) (x:=(typ_arrow A B))...
      exists (exp_merge x x0)...
    +
      dependent destruction H0...
      destruct (and_inv H1)...
      destruct IHA1 with (v:=exp_nat) (x:=typ_nat)...
      destruct IHA2 with (v:=exp_nat) (x:=typ_nat)...
      exists (exp_merge x x0)...      
    +
      dependent destruction H0...
      destruct (and_inv H1)...
      destruct IHA1 with (v:=exp_top) (x:=typ_top)...
      destruct IHA2 with (v:=exp_top) (x:=typ_top)...
      exists (exp_merge x x0)...
    +
      dependent destruction H0...
      destruct (and_inv H2)...
      destruct IHA1 with (v:=(exp_fold (typ_mu A) e)) (x:=(typ_mu A) )...
      destruct IHA2 with (v:=(exp_fold (typ_mu A) e)) (x:=(typ_mu A) )...
      exists (exp_merge x x0)...
    +
      dependent destruction H0...
      *
        apply and_inv in H1.
        destruct_hypos.
        destruct IHA1 with (v:=exp_merge e1 e2) (x:=typ_and A B)...
        destruct IHA2 with (v:=exp_merge e1 e2) (x:=typ_and A B)...
        exists (exp_merge x x0)...
      *
        apply and_inv in H3.
        destruct_hypos.
        destruct IHA1 with (v:=exp_merge e1 e2) (x:=typ_and A B)...
        destruct IHA2 with (v:=exp_merge e1 e2) (x:=typ_and A B)...
        exists (exp_merge x x0)...
    +
      dependent destruction H0...
      destruct (and_inv H1)...
      destruct IHA1 with (v:=exp_rcd l e) (x:=typ_rcd l A )...
      destruct IHA2 with (v:=exp_rcd l e) (x:=typ_rcd l A )...
      exists (exp_merge x x0)...
  - (* mu *)
    dependent induction val;intros;try solve [dependent destruction H0;dependent destruction H1;exists exp_top;auto]...
    + (* mu *)
      assert (Hq:=H0).
      dependent destruction H0...
      pose toplike_dec.
      destruct s with (E:=empty) (A:=typ_mu A).
      *
        exists exp_top...
        constructor...
        constructor...
        apply value_lc_expr...
      *
        exists (exp_fold (typ_mu A) e).
        constructor...
        get_well_form...
    + (* merge *)
      dependent destruction H0...
      *
        dependent destruction H1...
        destruct IHval1 with (x:=A0)...
        exists x...
        apply tred_mergeL...
        get_well_form...
        destruct IHval2 with (x:=B)...
        exists x...
        apply tred_mergeR...
        get_well_form...
        exists exp_top...
        constructor...
        constructor;get_well_form...        
      *
        dependent destruction H3...
        destruct IHval1 with (x:=A0)...
        exists x...
        apply tred_mergeL...
        get_well_form...
        destruct IHval2 with (x:=B)...
        exists x...
        apply tred_mergeR...
        get_well_form...
        exists exp_top...
        constructor...
        constructor;get_well_form...
    + (* rcd *)
      dependent destruction H0...
      dependent destruction H1...
      exists exp_top...
      constructor...
      get_well_form...
  - (* arrow *)
    assert (Hv:=val).
    dependent induction val;intros;try solve [dependent destruction H0;dependent destruction H1;exists exp_top;auto]...
    +  (* arrow *) 
      dependent destruction H0...
      pose toplike_dec.
      destruct s with (E:=empty) (A:=A2).
      *
        exists exp_top...
        constructor...
        constructor...
        get_well_form...
        inversion H3...
      *
        exists (exp_abs A t1 A2).
        dependent destruction H1...
        assert (False) as q.
        apply n...
        dependent destruction H2...
        destruct q.
    + (* fold *)
      dependent destruction H0...
      dependent destruction H2...
      exists exp_top...
      constructor...
      constructor...
      get_well_form...
    + (* merge *)
      dependent destruction H0...
      *
        dependent destruction H1...
        destruct IHval1 with (x:=A)...
        exists x...
        apply tred_mergeL...
        get_well_form...
        destruct IHval2 with (x:=B)...
        exists x...
        apply tred_mergeR...
        get_well_form...
        exists exp_top...
        constructor...
        constructor;get_well_form...      
      *
        dependent destruction H3...
        destruct IHval1 with (x:=A)...
        exists x...
        apply tred_mergeL...
        get_well_form...
        destruct IHval2 with (x:=B)...
        exists x...
        apply tred_mergeR...
        get_well_form...
        exists exp_top...
        constructor...
        constructor;get_well_form...
    + (* rcd *)
      dependent destruction H0...
      dependent destruction H1...
      exists exp_top...
      constructor...
      get_well_form...      
  - (* rcd *)
    dependent induction val;intros;try solve [dependent destruction H0;dependent destruction H1;exists exp_top;auto]...
    +
      dependent destruction H0...
      dependent destruction H2...
      exists exp_top...
      constructor...
      constructor...
      get_well_form...
    +
      dependent destruction H0...
      *
        dependent destruction H1...
        destruct IHval1 with (x:=A0)...
        exists x...
        apply tred_mergeL...
        get_well_form...
        destruct IHval2 with (x:=B)...
        exists x...
        apply tred_mergeR...
        get_well_form...
        exists exp_top...
        constructor...
        constructor;get_well_form...      
      *
        dependent destruction H3...
        destruct IHval1 with (x:=A0)...
        exists x...
        apply tred_mergeL...
        get_well_form...
        destruct IHval2 with (x:=B)...
        exists x...
        apply tred_mergeR...
        get_well_form...
        exists exp_top...
        constructor...
        constructor;get_well_form...
    +
      dependent destruction H0...
      pose toplike_dec.
      destruct s with (E:=empty) (A:=typ_rcd a A).
      *
        exists exp_top...
        constructor...
        get_well_form...
      *
        dependent destruction H1...
        --
          destruct IHA with (v:=e) (x:=A0)...
          exists (exp_rcd a x)...
        --
          assert (False) as q.
          apply n...
          destruct q.
Qed.


Lemma canonical_form_fold : forall e U ,
  value e ->
  typing empty e Chk (typ_mu U) ->
  ~ toplike empty (typ_mu U) ->
  (exists V, exists e1, Sub empty (typ_mu V) (typ_mu U) /\
                        value e1 /\ e = (exp_fold (typ_mu V) e1)) \/ (exists e1 e2, e = exp_merge e1 e2) .
Proof with auto.
  intros.
  generalize dependent U.
  dependent induction H;intros...
  - (* abs *)
    dependent destruction H0...
    dependent destruction H0...
    dependent destruction H1...
    assert (False) as Q.
    apply H3...
    destruct Q.
  -
    dependent destruction H0...
    dependent destruction H0...
    dependent destruction H0...
    assert (False) as Q.
    apply H2...
    destruct Q.
  -
    dependent destruction H0...
    dependent destruction H0...
    assert (False) as Q.
    apply H1...
    apply topCorrectR...
    destruct Q.
  -
    dependent destruction H1...
    dependent destruction H1...
    left.
    exists A.
    exists e...
  -
    right.
    exists e1.
    exists e2...
  -
    dependent destruction H0...
    dependent destruction H0...
    dependent destruction H1...
    assert (False) as Q.
    apply H3...
    destruct Q.
Qed.   


Theorem progress : forall e dir A,
    typing nil e dir A ->
    value e \/ exists e', step e e' .
Proof with auto.
  intros.
  assert (Ht:=H).
  dependent induction Ht;try solve [left;get_well_form;constructor;auto]...
  - (* var *)
    analyze_binds H1...
  - (* anno *)
    right.
    dependent destruction H...
    destruct IHHt...
    +
      assert (Hq:=H0).
      apply TypedReduce_progress with (A:=A) in H0...
      destruct H0.
      exists x...
    +
      destruct H0.
      exists (exp_anno x A)...
      constructor...
      get_well_form...
      get_type...
  - (* app *)
    destruct IHHt1;destruct IHHt2...
    +
      dependent destruction Ht1;try solve [inversion H1|inversion H0|inversion H2|inversion H4]...
      *
        dependent destruction H1...
        right.
        exists exp_top...
      *
        right.
        dependent destruction H1...
        apply TypedReduce_progress in Ht2...
        destruct Ht2.
        exists (exp_anno (open_ee e x) T2)...
        constructor...
        apply value_lc_expr...
        apply TypedReduce_prv_value in H1...
    +
      destruct H2.
      right.
      exists (exp_app e1 x)...
    +
      destruct H1.
      right.
      exists (exp_app  x e2)...
      constructor...
      apply value_lc_expr...
    +
      destruct H1.
      right.
      exists (exp_app x e2)...
      constructor...
      get_well_form...      
  - (* fix *)
    right.
    exists (exp_anno (open_ee e (exp_fix A e)) A)...
    constructor...
    get_well_form...
  - (* fold *)
    destruct IHHt...
    +
      left.
      constructor...
      get_type...
    +
      right.
      destruct H1.
      exists (exp_fold (typ_mu A) x)...
      constructor...
      get_type...
  - (* merge *)
    destruct IHHt1;destruct IHHt2...
    +
      right.
      destruct H2.
      exists (exp_merge e1 x)...
    +
      right.
      destruct H1.
      exists (exp_merge x e2)...
      constructor...
      apply value_lc_expr...
    +
      right.
      destruct_hypos.
      exists (exp_merge x0 e2)...
      constructor...
      get_well_form...
  - (* unfold *)
    right.
    destruct IHHt...
    +
      pose toplike_dec.
      destruct s with (E:=empty) (A:=typ_mu T).
      *
        exists exp_top.
        apply step_fldt...
        constructor...
        apply value_lc_expr...
      *
        apply canonical_form_fold in Ht...
        destruct Ht.
        --
          destruct_hypos.
          subst.
          dependent destruction H.
          dependent destruction H.
          dependent destruction H.
          assert (typing empty x0 Chk (open_tt T (typ_mu T))).
          apply typing_chk_sub with (A:=open_tt x (typ_mu x))...
          apply unfolding_lemma...
          apply TypedReduce_progress in H5...
          destruct_hypos.
          exists x1...
          constructor...
          get_type...
        --
          destruct_hypos.
          subst.
          dependent destruction H.
          apply TypedReduce_progress in H...
          destruct_hypos.
          dependent destruction H0.
          exists (exp_unfold (typ_mu T) x1)...
    +
      destruct_hypos.
      exists (exp_unfold (typ_mu T) x)...
      apply step_unfold...
      get_well_form...
      get_type...
  - (* rcd *)
    dependent destruction H...
    destruct IHHt...
    right.
    destruct_hypos.
    exists (exp_rcd l x)...
  - (* proj *)
    right.
    dependent destruction H...
    apply inference_unique with (A2:=A) in Ht...
    subst.
    destruct IHHt...
    +
      dependent destruction H;try solve [inversion H0|inversion H1|inversion H2|inversion H3|inversion H4|inversion H5|inversion H6]...
      *
        dependent destruction H0...
        exists exp_top...
      *
        dependent destruction H1.
        dependent destruction H2...
        exists e...
    +
      destruct_hypos.
      exists (exp_proj x l)...      
Qed.


Theorem step_unique: forall A e e1 e2 dir,
    typing nil e dir A -> step e e1 -> step e e2 -> e1 = e2.
Proof with auto.
  intros.
  generalize dependent A.
  generalize dependent dir.
  generalize dependent e2.
  assert (HG:=H0).
  dependent induction H0;intros...
  - (* top *)
    dependent destruction H1...
    +
      dependent destruction H1...
    +
      apply step_not_value in H1...
      destruct H1.
  - (* abs *)
    dependent destruction H3...
    +
      f_equal...
      f_equal...
      apply TypedReduce_unique with (A:=A) (v:=e1)...
      dependent induction H7...
      *
        dependent destruction H7...
        dependent destruction H7_...
        apply typing_chk2inf in H7_0...
        destruct_hypos.
        exists x...
        apply typing_chk2inf in H7_0...
        destruct_hypos.
        exists x...
      *
        destruct IHtyping with (A0:=A) (B0:=B) (e0:=e) (e3:=e1)...
        exists x...
    +
      dependent destruction H4...
    +
      apply step_not_value in H4...
      destruct H4.
  - (* appl *)
    dependent destruction H1...
    +
      apply step_not_value in H0...
      destruct H0.
    +
      dependent destruction H0.
    +
      f_equal...
      dependent induction H3...
      *
        dependent destruction H3...
        apply IHstep with (A:=typ_arrow T1 T2) (dir:=Inf)...
        apply IHstep with (A:=typ_top) (dir:=Inf)...
      *
        apply IHtyping with (e3:=e2) (e4:=e1)...
    +
      apply step_not_value in H0...
      destruct H0.
  - (* appr *)
    dependent destruction H1...
    +
      apply step_not_value in H0...
      destruct H0.
    +
      apply step_not_value in H0...
      destruct H0.
    +
      apply step_not_value in H2...
      destruct H2.
    +
      f_equal...
      dependent induction H3...
      *
        dependent destruction H3.
        apply IHstep with (A:=T1) (dir:=Chk)...
        apply IHstep with (A:=typ_top) (dir:=Chk)...
      *
        apply IHtyping with (e3:=e2) (v2:=v1)...
  - (* mergel *)
    dependent destruction H1...
    +
      f_equal.
      dependent induction H3...
      *
        apply IHstep with (A:=A) (dir:=Inf)...
      *
        apply IHstep with (A:=A) (dir:=Inf)...
      *
        apply IHtyping with (e3:=e2) (e4:=e1)...
    +
      apply step_not_value in H0...
      destruct H0.
  - (* merger *)
    dependent destruction H1...
    +
      apply step_not_value in H2...
      destruct H2.
    +
      f_equal...
      dependent induction H3.
      *
        apply IHstep with (A:=B) (dir:=Inf)...
      *
        apply IHstep with (A:=B) (dir:=Inf)...
      *
        apply IHtyping with (e3:=e2) (e4:=e1)...        
  - (* anno *)
    dependent destruction H1...
    +
      f_equal...
      dependent induction H3...
      apply IHstep with (A:=A) (dir:=Chk)...
      apply IHtyping with (A0:=A) (e0:=e)...
    +
      apply step_not_value in H0...
      destruct H0.
  - (* annov *)
    dependent destruction H1...
    +
      apply step_not_value in H1...
      destruct H1.
    +
      apply TypedReduce_unique with (A:=A) (v:=e)...
      dependent induction H3.
      *
        apply typing_chk2inf in H3...
        destruct_hypos.
        exists x...
      *
        dependent destruction H3...
        apply typing_chk2inf in H3...
        destruct_hypos.
        exists x...        
  - (* fix *)
    dependent destruction H1...    
  - (* unfold *)
    dependent destruction H3...
    +
      apply TypedReduce_unique with (A:=(open_tt A (typ_mu A))) (v:=e1)...
      dependent induction H7...
      *
        dependent destruction H7.
        dependent destruction H7.
        dependent destruction H7.
        exists A0...
      *
        destruct IHtyping with (e4:=e1) (B0:=B) (A0:=A)...
        exists x...
    +
      assert (False).
      apply H2...
      destruct H7.
    +
      dependent destruction H3...
      apply step_not_value in H3...
      destruct H3.
  - (* unfold merge *)
    dependent destruction H3...
    +
      f_equal.
      apply TypedReduce_unique with (A:=typ_mu A) (v:=exp_merge e1 e2)...
      dependent induction H7.
      *
        dependent destruction H7.
        exists A0...
      *
        destruct IHtyping with (e3:=e2) (e5:=e1) (A0:=A)...
        exists x...
    +
      assert (False).
      apply H2...
      destruct H7.
    +
      apply step_not_value in H3...
      destruct H3.
  - (* unfold top *)
    dependent destruction H2...
    +
      assert (False).
      apply H5...
      destruct H7.
    +
      assert (False).
      apply H5...
      destruct H7.
    +
      apply step_not_value in H2...
      destruct H2.
  - (* fold *)
    dependent destruction H1...
    f_equal...
    dependent induction H3...
    *
      dependent destruction H3...
      apply IHstep with (A:=A0) (dir:=Inf)...
    *
      apply IHtyping with (T0:=T) (e0:=e)...
  - (* unfold *)
    dependent destruction H1...
    +
      apply step_not_value in H0...
      destruct H0.
    +
      apply step_not_value in H0...
      destruct H0.
    +
      apply step_not_value in H0...
      destruct H0.
    +
      f_equal...
      dependent induction H3...
      *
        apply IHstep with (A:=typ_mu T0) (dir:=Chk)...
      *
        apply IHtyping with (T0:=T) (e0:=e)...
  - (* rcd *)
    dependent destruction H1...
    f_equal...
    dependent induction H...
    *
      apply IHstep with (A:=A) (dir:=Inf)...
    *
      apply IHtyping with (e0:=e) (l0:=l)...
  - (* proj *)
    dependent destruction H1...
    +
      f_equal.
      dependent induction H...
      *
        apply IHstep with (A:=A) (dir:=Inf)...
      *
        apply IHtyping with (e0:=e) (l0:=l)...
    +
      dependent destruction HG...
      dependent destruction HG...
    +
      dependent destruction HG...
      dependent destruction HG...
      apply step_not_value in HG...
      destruct HG.
  - (* projtop *)
    dependent destruction H1...
    dependent destruction H1...
  - (* projrcd *)
    dependent destruction H1...
    dependent destruction H1...
    apply step_not_value in H1...
    destruct H1.
Qed.
