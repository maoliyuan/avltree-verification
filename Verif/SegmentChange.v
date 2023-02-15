From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import RBT.Verif.RBtree_Type.
Require Import RBT.Verif.RBtree_Definition.
Require Import RBT.Verif.Half_Tree.
Require Import RBT.Verif.relation_map.
Require Import RBT.Verif.Abstract.

Section Section_SegmentChange.

Class RBtree_with_tag_comm {rbt : RBtree_setting} := {
Optt_comm : forall t1 t2 , Optt t1 t2 = Optt t2 t1
}.

Context {rbt:RBtree_setting}.
Context {rbt_comm : RBtree_with_tag_comm}.
Existing Instance rbt_comm.
Theorem f_twice_comm: forall v t1 t2, f ( f v t1) t2 = f ( f v t2) t1.
Proof.
  intros.
  rewrite f_tag.
  rewrite Optt_comm.
  rewrite f_tag.
  reflexivity.
Qed.
Theorem seg_tag_update : forall  lo hi t t0 m ,
   segment_update lo hi t (tag_update t0 m) =
     tag_update t0 (segment_update lo hi t m).
  Proof.
    intros.
    extensionality x.
    unfold segment_update, tag_update.
    destruct (m x).
    destruct (lo <=? x) ,( x <=? hi).
    simpl. rewrite f_twice_comm. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
    reflexivity.
  Qed.


Fixpoint change_segment' (lo hi : Key) (delta: Tag) (s: RBtree) (slo shi: Key) : RBtree :=
if (hi <? lo) then s else (
if (hi <? slo)  || (shi <? lo) 
  then s else (
  if (  lo <=? slo ) && ( shi <=? hi) then  tag_tree_t delta s
else
match s with
|Empty => Empty
|T co l k v t r =>  T co (change_segment' lo hi delta l slo k ) k 
                     (if (lo <=? k) && (k<=? hi) then f v delta else v) t
                      (change_segment' lo hi delta r k shi)
end
)).


Inductive change_segment lo hi delta s : RBtree -> Prop := 
|seg_intro:  forall low high,  SearchTree' low  s high -> 
  change_segment lo hi delta s (change_segment' lo hi delta s low high).


(*Proof *)
       
   
    Lemma change_Empty : forall lo hi t slo shi, change_segment' lo hi t Empty slo shi = Empty.
    Proof.
      intros.
      simpl.
      destruct (hi <? lo), ( hi <? slo), (shi <? lo), (lo <=? slo), (shi <=? hi);reflexivity. 
    Qed.
    Lemma change_up_defaultmap : forall lo hi t,
        segment_update lo hi t relate_default = relate_default.
    Proof.
      intros. extensionality x.
      unfold segment_update.
      unfold relate_default. reflexivity.
    Qed.
    Lemma change_up_hilo : forall lo hi t m,
      hi < lo ->
        segment_update lo hi t m = m.
    Proof.
      intros. extensionality x.
      unfold segment_update.
      destruct (m x); [| auto].
      
      remember (lo<=? x) as a.
      remember (x <=? hi) as b.
      destruct a,b;try auto.
      symmetry in Heqa, Heqb.
      solve_order.
    Qed.
    Lemma change_up_notin: forall lo hi m pm t,
     restriction m pm ->
     (forall k, (  lo <= k /\  k <= hi) -> ~ pm k ) ->
       segment_update lo hi t m = m.
    Proof.
      intros. extensionality k.
      pose proof H0 k.
      unfold segment_update.
      unfold restriction in H.
      pose proof H k.
      destruct (m k).
      - remember ( lo <=? k) as u. remember ( k <=? hi) as w. symmetry in Hequ, Heqw.
        destruct u, w.
        assert ( lo <= k /\ k <= hi). { split.  eapply lteb_lte; try eassumption. eapply lteb_lte; try eassumption. }
        exfalso. pose proof H1 H3. apply H4. apply H2. discriminate.
        simpl. reflexivity. reflexivity. reflexivity.
      - reflexivity.
    Qed.
    Lemma change_up_allin: forall lo hi m pm t,
     restriction m pm ->
     (forall k, pm k -> (lo <= k /\  k <= hi)  ) ->
       segment_update lo hi t m = tag_update t m.
    Proof.
      intros. extensionality k.
      pose proof H0 k.
      unfold segment_update , tag_update.
      unfold restriction in H.
      pose proof H k.
      destruct (m k).
      - remember ( lo <=? k) as u. remember ( k <=? hi) as w. symmetry in Hequ, Heqw.
        assert ( lo <= k /\ k <= hi). { apply H1.  apply H2. discriminate. } destruct H3.
        destruct u, w. reflexivity.  solve_order. solve_order. solve_order.
      - reflexivity.
    Qed.

  Theorem segment_st_pre: forall s lo hi t  slo shi, SearchTree' slo s shi ->
     SearchTree' slo (change_segment' lo hi t s slo shi) shi.
  Proof.
    intro.
    induction s.
    + intros.  rewrite change_Empty. auto.
    + intros.
    pose proof search_popro _ _ _ H.
    unfold change_segment'. fold change_segment'.
    inversion H. subst.
    destruct (hi <? lo);[auto |].
    remember ( hi <? slo) as m.
    remember (shi <? lo) as n.
    remember (lo <=? slo) as u.
    remember (shi <=? hi) as w.
    symmetry in Heqm, Heqn, Hequ, Heqw.
    destruct m, n;
   [ simpl; auto| simpl; auto | simpl; auto |  ].
    destruct u ,w;
    [ eapply search_tag_tree_t; try eassumption | | |].
    -
      simpl. apply ST_T. apply IHs1; try eassumption.
      apply IHs2; try eassumption.
    - simpl. apply ST_T. apply IHs1; try eassumption.
      apply IHs2; try eassumption.
    - simpl. apply ST_T. apply IHs1; try eassumption.
      apply IHs2; try eassumption.
  Qed.
  Theorem segement_abs : forall s lo hi t slo shi cts,
   SearchTree' slo s shi -> Abs s cts ->
    Abs (change_segment' lo hi t s slo shi) (segment_update lo hi t cts).
  Proof.
    intro.
    induction s.
    - intros. rewrite change_Empty. inversion H0. subst. rewrite change_up_defaultmap. auto.
    - intros. inversion H. subst.
      unfold change_segment'. fold change_segment'.
      remember (hi<? lo) as a;destruct a.
      --  symmetry in Heqa.
          erewrite change_up_hilo;auto. eapply ltb_lt;auto.
      --
      pose proof restriction_rb _ _ _ _ H H0.
      inversion H0. subst.
      remember ( hi <? slo) as m.
      remember (shi <? lo) as n.
      remember (lo <=? slo) as u.
      remember (shi <=? hi) as w.
      symmetry in Heqm, Heqn, Hequ, Heqw.
      destruct m, n.
      simpl. erewrite change_up_notin; try eassumption. res_intros.
      simpl. erewrite change_up_notin; try eassumption. res_intros.
      simpl. erewrite change_up_notin; try eassumption. res_intros.
      pose proof IHs1 lo hi t0 slo k a H9 H11.
      pose proof IHs2 lo hi t0 k shi b H10 H12.
      assert ( SearchTree' slo (change_segment' lo hi t0 s1 slo k) k). {
      eapply segment_st_pre; try eassumption. }
      assert ( SearchTree' k (change_segment' lo hi t0 s2 k shi) shi). { eapply segment_st_pre; try eassumption . }
      destruct u,w.
      + erewrite change_up_allin;try eassumption.
        
        eapply tag_tree_abs. auto. intros. super_destruct H6. split. left. tr. left. tr.
      +
        simpl. rewrite seg_tag_update.
      rewrite seg_v_update ; erewrite segment_combine by (first [res_simpl | res_intros ]); eapply Abs_T; try eassumption .
      + rewrite seg_tag_update ;
      rewrite seg_v_update ; erewrite segment_combine by (first [res_simpl | res_intros ]); eapply Abs_T; try eassumption .
      + rewrite seg_tag_update ;
      rewrite seg_v_update ; erewrite segment_combine by (first [res_simpl | res_intros ]); eapply Abs_T; try eassumption .
  Qed.
  Theorem segement_isrb_co : forall s lo hi t slo shi co,
    is_redblack_color s co ->
    SearchTree' slo s shi ->
    is_redblack_color (change_segment' lo hi t s slo shi) co.
  Proof.
    intros.
    revert lo hi t slo shi H0 .
    induction H.
    - intros. rewrite change_Empty. apply IsRB_co_leaf.
    - intros.
      unfold change_segment'. fold change_segment'.
      remember (hi<? lo) as a;destruct a.
      -- eapply IsRB_co_r; auto.
      --
      remember ( hi <? slo) as m.
      remember (shi <? lo) as n.
      destruct m, n.
      eapply IsRB_co_r; try eassumption.
      eapply IsRB_co_r; try eassumption.
      eapply IsRB_co_r; try eassumption.
      inversion H1.
      subst.
      pose proof IHis_redblack_color1 lo hi t slo k H10.
      pose proof IHis_redblack_color2 lo hi t k shi H11.
      destruct (lo <=? slo), (shi <=? hi).
      eapply isrb_tagupdate. eapply IsRB_co_r; try eassumption.
      eapply IsRB_co_r; try eassumption.
      eapply IsRB_co_r; try eassumption.
      eapply IsRB_co_r; try eassumption.
    - intros.
      unfold change_segment'. fold change_segment'.
      remember (hi<? lo) as a;destruct a.
      -- eapply IsRB_co_b; auto.
      --
      remember ( hi <? slo) as m.
      remember (shi <? lo) as n.
      destruct m, n.
      eapply IsRB_co_b; try eassumption.
      eapply IsRB_co_b; try eassumption.
      eapply IsRB_co_b; try eassumption.
      inversion H1.
      subst.
      pose proof IHis_redblack_color1 lo hi t slo k H10.
      pose proof IHis_redblack_color2 lo hi t k shi H11.
      destruct (lo <=? slo), (shi <=? hi).
      eapply isrb_tagupdate. eapply IsRB_co_b; try eassumption.
      eapply IsRB_co_b; try eassumption.
      eapply IsRB_co_b; try eassumption.
      eapply IsRB_co_b; try eassumption.
  Qed.
  Theorem segement_isrb_dep: forall s lo hi t slo shi n,
    is_redblack_dep s n ->
    SearchTree' slo s shi ->
    is_redblack_dep (change_segment' lo hi t s slo shi) n.
  Proof.
    intros.
    revert lo hi t slo shi H0 .
    induction H.
    - intros. rewrite change_Empty. apply IsRB_dep_em.
    - intros.
      unfold change_segment'. fold change_segment'.
      remember (hi<? lo) as a;destruct a;[eapply IsRB_dep_r;auto |].
      destruct ( hi <? slo), (shi <? lo).
      eapply IsRB_dep_r; try eassumption.
      eapply IsRB_dep_r; try eassumption.
      eapply IsRB_dep_r; try eassumption.
      inversion H1.
      subst.
      pose proof IHis_redblack_dep1 lo hi t slo k H10.
      pose proof IHis_redblack_dep2 lo hi t k shi H11.
      destruct (lo <=? slo), (shi <=? hi).
      eapply isrb_tagupdate_dep. eapply IsRB_dep_r; try eassumption.
      eapply IsRB_dep_r; try eassumption.
      eapply IsRB_dep_r; try eassumption.
      eapply IsRB_dep_r; try eassumption.
    - intros.
      unfold change_segment'. fold change_segment'.
      remember (hi<? lo) as a;destruct a;[eapply IsRB_dep_b;auto | ].
      destruct ( hi <? slo), (shi <? lo).
      eapply IsRB_dep_b; try eassumption.
      eapply IsRB_dep_b; try eassumption.
      eapply IsRB_dep_b; try eassumption.
      inversion H1.
      subst.
      pose proof IHis_redblack_dep1 lo hi t slo k H10.
      pose proof IHis_redblack_dep2 lo hi t k shi H11.
      destruct (lo <=? slo), (shi <=? hi).
      eapply isrb_tagupdate_dep. eapply IsRB_dep_b; try eassumption.
      eapply IsRB_dep_b; try eassumption.
      eapply IsRB_dep_b; try eassumption.
      eapply IsRB_dep_b; try eassumption.
  Qed.

Theorem segement_keep: forall s lo hi t tree, SearchTree s -> is_redblack s ->
 change_segment lo hi t s tree -> 
 SearchTree tree /\  is_redblack tree .
Proof.
  intros.
  inversion H. subst.
  destruct H0.
  destruct H3.
  inversion H1. subst.

  split.
  eapply ST_intro .
  eapply (segment_st_pre s lo hi t); try eassumption.
  split.
  eapply segement_isrb_co; try eassumption.
  exists x.
  eapply segement_isrb_dep; try eassumption.
Qed.

End Section_SegmentChange.