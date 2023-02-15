From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import RBT.Verif.RBtree_Type.
Require Import RBT.Verif.RBtree_Definition.
Require Import RBT.Verif.Half_Tree.
Require Import RBT.Verif.relation_map.
Require Import RBT.Verif.Abstract.

Section Section_general_split.

Context {rbt:RBtree_setting}.
Existing Instance rbt.

Fixpoint general_split(lbool rbool : Key -> bool)  (t : Tag) (s : RBtree)  (b: list Half_tree): 
 list Half_tree * RBtree :=
 match s with
 |Empty => (b, Empty)
 |T co l y v t' r =>
    if (lbool y) then 
        general_split lbool rbool (Optt t t') l
              ((false,co ,y,f(f v t') t ,default, tag_tree_t (Optt t t') r)::b)
      else if (rbool y) then 
        general_split lbool rbool ( Optt t t' ) r
              ((true,co ,y,f(f v t') t ,default, tag_tree_t (Optt t t' ) l)::b)
      else 
        (b, T co (tag_tree_t (Optt t t') l) y (f v (Optt t t')) default (tag_tree_t (Optt t t') r))
end.

Definition general_split_simpl (lbool rbool : Key -> bool) (s: RBtree) := general_split lbool rbool default s nil.

Definition lb_rb_tree lb rb (s : RBtree): Prop :=
match s with
|Empty => True
|T co le y v t ri => lb y = false /\ rb y = false
end.

(*GENERAL SPLIT PROPERTIES---------------------------------------------*)
Theorem general_split_lbrb_tree :
  forall lb rb lo hi  tree h  t l s ,
  (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false))->
    SearchTree' lo tree hi -> SearchTree_half lo h hi
      -> (l , s) = general_split lb rb t tree h -> 
               lb_rb_tree lb rb s.
Proof.
  intros. revert h t l s  H1 H2.
  induction H0.
  - intros.
    inversion H2. subst.
    reflexivity.
  - intros.
    simpl in H2.
    pose proof search_popro lo l k H0_.
    pose proof search_popro k r hi H0_0.
    remember (lb k) as m.
    remember (rb k) as n.
    destruct m.
    + clear IHSearchTree'2.
      eapply IHSearchTree'1; try eassumption.
      eapply ST_cons_false; try eassumption.
      eapply search_tag_tree_t; try eassumption.
      right. auto.
    + destruct n.
      * clear IHSearchTree'1.
        eapply IHSearchTree'2; try eassumption.
        eapply ST_cons_true; try eassumption.
        eapply search_tag_tree_t; try eassumption.
        right. auto.
      * 
        inversion H2. subst.
        simpl.
        split.
        symmetry. auto.
        symmetry. auto.
Qed.
Theorem general_split_ST_pro:
  forall lb rb lo hi  tree h  t l s ,
  (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false))->
    SearchTree' lo tree hi -> SearchTree_half lo h hi ->
     (l , s) = general_split lb rb t tree h ->
     ( exists x  y,  SearchTree_half x l y /\ SearchTree' x s y /\ 
                      ( lo <= x /\ y <= hi) ).
Proof.
  intros. revert lo hi h t l s  H0 H1 H2.
  induction tree.
  - intros.
     simpl in H2.
     inversion H2. subst.
     exists lo. exists hi.
     split.
     * auto.
     * split.
       auto.
       split.
       right. reflexivity.
       right. reflexivity.
  - intros.
    simpl in H2.
    inversion H0.
    subst.
    pose proof search_popro lo tree1 k H11.
    pose proof search_popro k tree2 hi H12.
    remember (lb k) as m.
    remember (rb k) as n.
    destruct m.
    + (* left part *)
       clear IHtree2.
       assert (SearchTree_half lo
       ((false, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) tree2) :: h) k).
     { eapply ST_cons_false; try eassumption.  apply search_tag_tree_t. auto. 
        right. auto. }
      
       pose proof IHtree1 lo k _ _ _ _ H11 H5 H2.
       destruct H6. destruct H6. super_destruct H6.
       exists x. exists x0.
       split. auto.
       split. auto.
       split. auto.
       tr.
    + destruct n.
      * (* right part*)
        assert (SearchTree_half k
       ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) tree1) :: h) hi).
     { eapply ST_cons_true; try eassumption.  apply search_tag_tree_t. auto.
       right. auto.   }
     
       pose proof IHtree2 k hi _ _ _ _ H12 H5 H2.
       destruct H6. destruct H6. super_destruct H6.
       exists x. exists x0.
       split. auto.
       split. auto.
       split. tr.
       auto.
      * (* middle part*)
        clear IHtree1 IHtree2.
        exists lo. exists hi.
        inversion H2. subst.
        split.
        auto.
        split.
        apply ST_T. apply search_tag_tree_t. auto. apply search_tag_tree_t. auto.
        split.
       right. reflexivity.
       right. reflexivity.
Qed.
Theorem general_split_ST:
  forall lb rb lo hi  tree h  t l s ,
  (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false))->
    SearchTree' lo tree hi -> SearchTree_half lo h hi ->
     lb hi = true /\ rb lo = true ->
     (l , s) = general_split lb rb t tree h ->
     ( exists x  y,  SearchTree_half x l y /\ SearchTree' x s y /\ 
                      (lb y = true /\ rb x = true) ).
Proof.
  intros. revert lo hi h t l s  H0 H1 H2 H3.
  induction tree.
  - intros.
     simpl in H3.
     inversion H3. subst.
     exists lo. exists hi.
     split.
     * auto.
     * split.
       auto.
       auto.
  - intros.
    simpl in H3.
    inversion H0.
    subst.
    pose proof search_popro lo tree1 k H12.
    pose proof search_popro k tree2 hi H13.
    remember (lb k) as m.
    remember (rb k) as n.
    destruct m.
    + (* left part *)
       clear IHtree2.
       assert (SearchTree_half lo
       ((false, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) tree2) :: h) k).
     { eapply ST_cons_false; try eassumption.  apply search_tag_tree_t. auto.
       right. auto.  }
       eapply IHtree1. apply H12. apply H6.
       split. symmetry. tauto.
      tauto.
      apply H3.
    + destruct n.
      * (* right part*)
        assert (SearchTree_half k
       ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) tree1) :: h) hi).
     { eapply ST_cons_true; try eassumption.  apply search_tag_tree_t. auto.
       right. auto.   }
    eapply IHtree2. apply H13. apply H6.
       split. apply H2. symmetry. tauto.
      apply H3.
      * (* middle part*)
        clear IHtree1 IHtree2.
        exists lo. exists hi.
        inversion H3. subst.
        split.
        auto.
        split.
        apply ST_T. apply search_tag_tree_t. auto. apply search_tag_tree_t. auto.
        auto.
Qed.
Theorem general_split_ST_prepro:
  forall lb rb lo hi  tree h  t l s ,
  (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false))->
    SearchTree' lo tree hi -> SearchTree_half lo h hi ->
     lb hi = true /\ rb lo = true ->
     (l , s) = general_split lb rb t tree h ->
     ( exists x  y,  SearchTree_half x l y /\ SearchTree' x s y /\ 
                     (lb y = true /\ rb x = true) /\ ( lo <= x /\ y <= hi) ).
Proof.
  intros. revert lo hi h t l s  H0 H1 H2 H3.
  induction tree.
  - intros.
     simpl in H3.
     inversion H3. subst.
     exists lo. exists hi.
     split.
     * auto.
     * split.
       auto.
       split.
       auto.
       split.
       right. reflexivity.
       right. reflexivity.
  - intros.
    simpl in H3.
    inversion H0.
    subst.
    pose proof search_popro lo tree1 k H12.
    pose proof search_popro k tree2 hi H13.
    remember (lb k) as m.
    remember (rb k) as n.
    destruct m.
    + (* left part *)
       clear IHtree2.
       assert (SearchTree_half lo
       ((false, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) tree2) :: h) k).
     { eapply ST_cons_false; try eassumption.  apply search_tag_tree_t. auto. 
        right. auto. }
       assert (lb k = true /\ rb lo = true ).
       { split. symmetry. tauto.
      tauto. }
       pose proof IHtree1 lo k _ _ _ _ H12 H6 H7 H3.
       destruct H8. destruct H8. super_destruct H8.
       exists x. exists x0.
       split. auto.
       split. auto.
       split.
       * split;auto. 
       * split. auto.
       tr.
    + destruct n.
      * (* right part*)
        assert (SearchTree_half k
       ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) tree1) :: h) hi).
     { eapply ST_cons_true; try eassumption.  apply search_tag_tree_t. auto.
       right. auto.   }
       assert (lb hi = true /\ rb k = true ).
       { split.
      tauto. symmetry. tauto. }
       pose proof IHtree2 k hi _ _ _ _ H13 H6 H7 H3.
       destruct H8. destruct H8. super_destruct H8.
       exists x. exists x0.
       split. auto.
       split. auto.
       split.
       tauto.
       split. tr.
       auto.
      * (* middle part*)
        clear IHtree1 IHtree2.
        exists lo. exists hi.
        inversion H3. subst.
        split.
        auto.
        split.
        apply ST_T. apply search_tag_tree_t. auto. apply search_tag_tree_t. auto.
        split.
       auto.
       split.
       right. reflexivity.
       right. reflexivity.
Qed.
(**保证split过后的 list Half_tree 的out ST 性质 *)
Theorem general_split_ST_out :
 forall lb rb lo hi tree h t l s olo ohi ,
    (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false))->
    SearchTree' lo tree hi -> SearchTree_half lo h hi -> SearchTree_half_out olo h ohi ->
       (l , s) = general_split lb rb t tree h ->
         SearchTree_half_out  (min_k lo olo) l (max_k hi ohi).
Proof.
  intros. revert lo hi h t l s olo ohi H0 H1 H2 H3.
  induction tree.
  - intros.
    simpl in H3.
    inversion H3.
    subst.
    pose proof min_right lo olo.
    pose proof search_half_popro3_lte (min_k lo olo) h ohi olo H2 H4.
    eapply search_half_popro2_lte; try eassumption.
    apply max_right.
  - intros.
    simpl in H3.
    inversion H0.
    subst.
    pose proof search_popro lo tree1 k H12.
    pose proof search_popro k tree2 hi H13.
    remember (lb k) as m.
    remember (rb k) as n.
    destruct m.
    + (*left part*)
       clear IHtree2.
       assert (SearchTree_half lo
       ((false, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) tree2) :: h) k).
     { eapply ST_cons_false; try eassumption.  apply search_tag_tree_t. auto.
       right. auto.  }
       assert (SearchTree_half_out (min_k lo olo) ((false, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) tree2) :: h) (max_k hi ohi)).
      { eapply ST_out_cons; try eassumption.
        eapply ST_ht_false; try eassumption.
        eapply search_tag_tree_t; try eassumption. }
      pose proof IHtree1 _ _ _ (Optt t0 t) l s _ _ H12 H6 H7.
      assert ( min_k (min_k lo olo) lo = (min_k lo olo)).
      {
        apply min_lte.
        apply min_left. }
      assert ( (max_k (max_k hi ohi) k) = (max_k hi ohi)).
      { rewrite max_comm.
        apply max_lte.
        left.
        pose proof max_left hi ohi.
        tr. }
      rewrite <- H9. 
      rewrite <- H10.
      rewrite min_comm.
      rewrite max_comm.
      apply H8; try eassumption.
    + destruct n.
      (*right part*)
     *  clear IHtree1.
        assert (SearchTree_half k
       ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) tree1) :: h) hi).
     { eapply ST_cons_true; try eassumption.  apply search_tag_tree_t. auto. 
       right. auto.  }
       assert (SearchTree_half_out (min_k lo olo) ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) tree1) :: h) (max_k hi ohi)).
      { eapply ST_out_cons; try eassumption.
        eapply ST_ht_true; try eassumption.
        eapply search_tag_tree_t; try eassumption. }
      pose proof IHtree2 _ _ _ (Optt t0 t) l s _ _ H13 H6 H7.
      assert ( min_k (min_k lo olo) k = (min_k lo olo)).
      {
        apply min_lte.
        pose proof min_left lo olo.
        tr. }
      assert ( (max_k (max_k hi ohi) hi) = (max_k hi ohi)).
      { rewrite max_comm.
        apply max_lte.
        apply max_left.
      }
      rewrite <- H9. 
      rewrite <- H10.
      rewrite min_comm.
      rewrite max_comm.
      apply H8; try eassumption.
     * 
       clear IHtree1 IHtree2.
       inversion H3. subst.
       pose proof min_right lo olo.
    pose proof search_half_popro3_lte (min_k lo olo) h ohi olo H2 H6.
    eapply search_half_popro2_lte; try eassumption.
    apply max_right.
Qed.


(**保证split过后得到的half tree 和RBtree 满足 Abs性质*)
Theorem general_split_abs:
   forall lb rb lo hi tree h tmap hmap t l s,
  (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false)) ->
   SearchTree' lo tree hi -> Abs tree tmap ->
  Forall (fun x =>  snd ( fst x) = default) h ->
   SearchTree_half lo h hi -> Abs_half h hmap -> 
    (l , s ) = general_split lb rb t tree h -> Abs (complete_tree l s) (combine (tag_update t tmap) hmap).
Proof.
  intros. revert h tmap hmap t l s  H1 H2 H3 H4 H5.
  pose proof (search_popro _ _ _ H0).
  induction H0.
  - intros.
    inversion H2 ; subst.
    simpl in H6.
    inversion H6; subst.
    eapply complete_relate_pre; try eassumption.
    apply ST_E ; try eassumption.
  - intros.
    pose proof (search_popro _ _ _ H0_).
    pose proof (search_popro _ _ _ H0_0).
    inversion H0. subst.
    pose proof (IHSearchTree'1 H6); clear IHSearchTree'1 .
    pose proof (IHSearchTree'2 H7); clear IHSearchTree'2 .
    simpl in H5.
    remember (lb k ) as m.
    remember (rb k ) as n.
    destruct m.
    + (* left part *)
       clear H9.
       pose proof tag_tree_abs r (Optt t0 t) b H16.
       pose proof Abs_cons h hmap false c k (f (f v t) t0) default _ _ default H4 H9 (accumulate_default _  H2); clear H9.
       rewrite Optt_default in H10.
       rewrite tag_update_default in H10.
       assert (Forall P  ((false, c, k, f (f v t) t0, default,
         tag_tree_t (Optt t0 t) r) :: h)).
      { eapply Forall_cons. unfold P. simpl. reflexivity. try eassumption. }

      assert (SearchTree_half lo  ((false, c, k, f (f v t) t0, default,
         tag_tree_t (Optt t0 t) r) :: h) k).
      { eapply ST_cons_false; try eassumption.   eapply search_tag_tree_t; try eassumption.
       right. auto. }

      pose proof H8 _ _ _ _ _ _ H15 H9 H11 H10 H5 ; clear H8 H9 H10 H11 H5.
      rewrite tag_update_twice.
      rewrite f_tag in H12.
      remember (Optt t0 t) as tag.
      rewrite v_up_tagupdate_iff in H12.
       erewrite  <- (v_update_combine k v a b)   by (first [ res_simpl | res_intros | res_intro ]).
       rewrite tagupdate_combine.
       rewrite combine_comm.
       erewrite combine_asso  by (first [ res_simpl | res_intros | res_intro ]).
       auto.
    + destruct n.
      (* right part*)
      * clear H8.
        pose proof tag_tree_abs l (Optt t0 t) a H15.
       pose proof Abs_cons h hmap true c k (f (f v t) t0) default _ _ default H4 H8 (accumulate_default _ H2 );clear H8.
       rewrite Optt_default in H10.
       rewrite tag_update_default in H10.
       assert ( Forall P
        ((true, c, k, f (f v t) t0, default,
         tag_tree_t (Optt t0 t) l) :: h) ).
       { eapply Forall_cons. unfold P. simpl. reflexivity. auto. }
       assert (SearchTree_half k
        ((true, c, k, f (f v t) t0, default,
         tag_tree_t (Optt t0 t) l) :: h) hi ).
       { eapply ST_cons_true; try eassumption.  eapply search_tag_tree_t; try eassumption.
       right. auto.  }
       pose proof H9 _ _ _ _ _ _ H16 H8 H11 H10 H5; clear H10 H9 H8 H11 H5.
       
       rewrite tag_update_twice.
       rewrite f_tag in H12.
       remember (Optt t0 t) as tag.
       rewrite v_up_tagupdate_iff in H12.
       rewrite (combine_comm a b).
       erewrite  <- (v_update_combine k v b a)  by (first [ res_simpl | res_intros | res_intro ]).
       rewrite tagupdate_combine.
       rewrite combine_comm.
       erewrite combine_asso  by (first [ res_simpl | res_intros | res_intro ]).
       auto.
      * (* midlle part *)
        clear H9 H8.
         inversion H5. subst.
         remember (T c (tag_tree_t (Optt t0 t) l) k (f v (Optt t0 t)) default
        (tag_tree_t (Optt t0 t) r)) as tree.
        assert ( SearchTree' lo tree hi).
        { rewrite Heqtree. eapply ST_T. eapply search_tag_tree_t; try eassumption. eapply search_tag_tree_t; try eassumption. }
        assert (Abs tree 
         ( tag_update default (v_update k (f v (Optt t0 t)) (combine ( tag_update (Optt t0 t) a) ( tag_update (Optt t0 t) b)) ))).
        { rewrite Heqtree. eapply Abs_T; try eassumption. eapply tag_tree_abs; try eassumption.  eapply tag_tree_abs; try eassumption. }
        pose proof complete_relate_pre _ _ _ _ _ _ H2 H3 H8 H9 H4.
        rewrite tag_update_default in H10.
        rewrite tag_update_twice.
        rewrite combine_comm in H10.
        rewrite combine_comm.
        remember (Optt t0 t) as tag.
        rewrite tag_v_update.
        remember (f v tag) as v2.
        rewrite tagupdate_combine.
        erewrite v_update_combine by (first [ res_simpl | res_intros |res_intro ]).
        erewrite <- v_update_combine by (first [ res_simpl | res_intros |res_intro ]).
        auto.
Qed.

Lemma general_split_tag_default:
  forall lb rb s t l  lo hi h b,
  (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false)) ->
  SearchTree' lo s hi -> SearchTree_half lo l hi -> Forall P l -> (h , b) = general_split lb rb t  s l -> Forall P h.
Proof.
  intros.
  revert t l lo hi h b H0 H1 H2 H3.
  induction s.
  - intros. inversion H3. subst. auto.
  - intros.
    simpl in H3.
    inversion H0. subst.
    pose proof search_popro _ _ _ H0.
    remember (lb k) as u.
    remember (rb k) as w.
    destruct u.
    + (* left part *)
      assert (SearchTree_half lo
       ((false, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s2) :: l) k ).
      { eapply ST_cons_false; try eassumption.  eapply search_popro; try eassumption.  eapply search_tag_tree_t; try eassumption.
      right. auto.
       eapply search_popro; try eassumption.
      }
      assert (
      Forall P
       ((false, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s2) :: l)
      ).
      { eapply Forall_cons. reflexivity. auto.
       }
      apply ( IHs1 (Optt t0 t) ((false, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t)  s2) :: l) lo k h b H12 H5 H6 H3).
    + destruct w.
      * (* right part *)
       assert (SearchTree_half k
       ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l) hi ).
      { eapply ST_cons_true; try eassumption.  eapply search_popro; try eassumption.  eapply search_tag_tree_t; try eassumption. right. auto.
       eapply search_popro; try eassumption.
      }
      assert (
      Forall P
       ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l)
      ).
      { eapply Forall_cons. reflexivity. auto.
       }
      apply ( IHs2(Optt t0 t) ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l) _ _ h b H13 H5 H6 H3).
     *
      inversion H3.
      subst. auto.
Qed.

Lemma general_split_tag_default_tree:
  forall lb rb s t l  lo hi h b,
  (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false)) ->
  SearchTree' lo s hi -> SearchTree_half lo l hi -> (h , b) = general_split lb rb t  s l -> default_tag_tree b \/ b = Empty.
Proof.
  intros.
  revert lo hi t l h b H0 H1 H2.
  induction s.
  - intros. inversion H2. subst. right. reflexivity.
  - intros. simpl in H2.
    inversion H0. subst.
    pose proof search_popro _ _ _ H0.
    remember (lb k) as u.
    remember (rb k) as w.
    destruct u.
    + 
      assert (SearchTree_half lo
       ((false, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s2) :: l) k ).
      { eapply ST_cons_false; try eassumption.  eapply search_popro; try eassumption.  eapply search_tag_tree_t; try eassumption. right. auto.
       eapply search_popro; try eassumption.
      }
     eapply (IHs1 lo k (Optt t0 t) ((false, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s2) :: l) h b);try eassumption.
    + destruct w.
      * assert (SearchTree_half k
       ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l) hi ).
      { eapply ST_cons_true; try eassumption.  eapply search_popro; try eassumption. eapply search_tag_tree_t; try eassumption. right. auto.
       eapply search_popro; try eassumption.
      }
      eapply (IHs2 k hi (Optt t0 t) ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l) h b);try eassumption.
     * 
      inversion H2.
      subst. left.  reflexivity.
Qed.
(** 保证split过后得到的half tree 和RBtree 满足 RB color性质*)
Theorem general_split_RB_co :
forall lb rb s l t h b ,
 (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false)) ->
 is_redblack_color s Black -> is_redblack_color_half l Black ->
   (Red_tree s /\ fst_black' l \/ Black_tree s \/ (s = Empty /\ ~ l =nil)) ->
   (h , b) = general_split lb rb  t s l ->
   ( is_redblack_color b Black /\ is_redblack_color_half h Black ) /\
      (Red_tree b /\ fst_black' h \/ Black_tree b \/ (b = Empty /\ ~ h =nil)).
Proof.
  intros. revert l t h b H0 H1 H2 H3.
  induction s.
  - intros. inversion H3. subst.
     split.
     split. auto. auto.
     right. right.
     destruct H2 as [ [H2 H4] | [ H2 | [H2 H4]]].
     inversion H2.
     inversion H2.
     firstorder.
  - intros.
    simpl in H3.
    assert ( is_redblack_color s1 Black).
    { eapply isrb_left; try eassumption.
    }
    assert ( is_redblack_color s2 Black).
    { eapply isrb_right;try eassumption.
    }
    remember (lb k) as u.
    remember (rb k) as w.
    destruct u.
    + (* left part*)
    assert (is_redblack_color_half ((false, c, k, v, default,s2)::l) Black).
    {
     destruct H2 as [[H2 [H6 H7]] | [ H2 | [H2 H6]]].
     inversion H2. subst. inversion H0. subst. eapply IsRB_co_r_cons; try eassumption. eapply isb_isr_half; try eassumption.
     inversion H2. subst. eapply IsRB_co_b_cons; try eassumption.
     inversion H2.
    }
    assert (is_redblack_color_half ((false, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l)
  Black).
  { eapply isrb_change_half. apply H6.  eapply isrb_bro; try eassumption.
   eapply isrb_tagupdate; try eassumption. eapply isrb_bro; try eassumption. }
      clear IHs2.
      assert (
      Red_tree s1 /\ fst_black' ((false, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l) \/
Black_tree s1 \/
s1 = Empty /\ (false, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l <> nil
      ).
      {
       destruct s1. right. right. split. reflexivity. discriminate.
       destruct c0.
       left. split. reflexivity. split. 2: discriminate.
        destruct c. inversion H0. subst. inversion H10. reflexivity.
       right. left. reflexivity.
      }
      apply (IHs1 ((false, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l) (Optt t0 t) h b H4 H7 H8 H3 ). 
     + destruct w.
      * (* right part *)
       assert (is_redblack_color_half ((false, c, k, v, default,s1)::l) Black).
    {
     destruct H2 as [[H2 [H6 H7]] | [ H2 | [H2 H6]]].
     inversion H2. subst. inversion H0. subst. eapply IsRB_co_r_cons; try eassumption. eapply isb_isr_half; try eassumption.
     inversion H2. subst. eapply IsRB_co_b_cons; try eassumption.
     inversion H2.
    }
    assert (is_redblack_color_half ((true, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s1) :: l)
  Black). { eapply isrb_change_half. apply H6. eapply isrb_bro; try eassumption.
   eapply isrb_tagupdate; try eassumption. eapply isrb_bro; try eassumption. }
      clear IHs1.
      assert (
      Red_tree s2 /\ fst_black' ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l) \/
Black_tree s2 \/
s2 = Empty /\ ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l) <> nil
      ).
      {
       destruct s2. right. right. split. reflexivity. discriminate.
       destruct c0.
       left. split. reflexivity. split. 2: discriminate.
        destruct c. inversion H0. subst. inversion H14. reflexivity.
       right. left. reflexivity.
      }
      apply (IHs2 ((true, c, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l)  (Optt t0 t) h b);try eassumption.
     *
       inversion H3.
       split.  split. 2:auto.
       destruct H2 as [[H2 [H9 H10]] | [ H2 | [H2 H6]]].
       subst. inversion H2. subst. inversion H0. subst.
       eapply IsRB_co_r. eapply isrb_tagupdate; try eassumption.
       eapply isrb_tagupdate; try eassumption.
       inversion H2. subst. eapply IsRB_co_b.
       eapply isrb_tagupdate; try eassumption.
       eapply isrb_tagupdate; try eassumption.
       inversion H2.

       destruct H2 as [ [H9 H10 ] | [ H2 | [H2 H6]]].
       subst. inversion H9. subst.
        left. split. reflexivity. auto.
       subst. inversion H2. subst.
        right. left. reflexivity.
       subst. inversion H2.
Qed.
Theorem general_split_RB_co_loose :
forall lb rb s l t h b ,
 (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false)) ->
 is_redblack_color s Black -> is_redblack_color_half_loose l Black ->
   (Red_tree s /\ fst_black l \/ Black_tree s \/ (s = Empty /\ ~ l =nil)) ->
   (h , b) = general_split lb rb  t s l ->
   ( is_redblack_color b Black /\ is_redblack_color_half_loose h Black ) /\
      (Red_tree b /\ fst_black h \/ Black_tree b \/ (b = Empty /\ ~ h =nil)).
Proof.
  intros. revert l t h b H0 H1 H2 H3.
  induction s.
  - intros. inversion H3. subst.
     split.
     split. auto. auto.
     right. right.
     destruct H2 as [ [H2 H4] | [ H2 | [H2 H4]]].
     inversion H2.
     inversion H2.
     firstorder.
  - intros.
    simpl in H3.
    assert ( is_redblack_color s1 Black).
    { eapply isrb_left; try eassumption.
    }
    assert ( is_redblack_color s2 Black).
    { eapply isrb_right;try eassumption.
    }
    remember (lb k) as u.
    remember (rb k) as w.
    destruct u.
    + (* left part*)
   
    assert (is_redblack_color_half_loose ((false, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l)
  Black).
  { destruct H2 as [[H2 H7] | [ H2 | [H2 H6]]].
     inversion H2. subst. inversion H0. subst. eapply IsRB_co_r_cons_l; try eassumption.
     eapply isb_isr_half_loose; try eassumption. eapply isrb_tagupdate; try eassumption.
     inversion H2. subst. eapply IsRB_co_b_cons_l; try eassumption.  eapply isrb_tagupdate; try eassumption.
     inversion H2. }
      clear IHs2.
      assert (
      Red_tree s1 /\ fst_black ((false, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l) \/
Black_tree s1 \/
s1 = Empty /\ (false, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l <> nil
      ).
      {
       destruct s1. right. right. split. reflexivity. discriminate.
       destruct c0.
       left. split. reflexivity.
       inversion H0. subst. inversion H9. reflexivity.
       right. left. reflexivity.
      }
      apply (IHs1 ( (false, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l) (Optt t0 t) h b H4 H6 H7 H3 ).
     + destruct w.
      * (* right part *)
      
    assert (is_redblack_color_half_loose ((true, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s1) :: l)
  Black).
    { destruct H2 as [[H2 H7] | [ H2 | [H2 H6]]].
     inversion H2. subst. inversion H0. subst. eapply IsRB_co_r_cons_l; try eassumption. eapply isb_isr_half_loose; try eassumption. eapply isrb_tagupdate; try eassumption.
     inversion H2. subst. eapply IsRB_co_b_cons_l; try eassumption. eapply isrb_tagupdate; try eassumption.
     inversion H2. }
      clear IHs1.
      assert (
      Red_tree s2 /\ fst_black ((true, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s1) :: l) \/
Black_tree s2 \/
s2 = Empty /\ ((true, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s1) :: l) <> nil
      ).
      {
       destruct s2. right. right. split. reflexivity. discriminate.
       destruct c0.
       left. split. reflexivity.
        destruct c. inversion H0. subst. inversion H13. reflexivity.
       right. left. reflexivity.
      }
      apply (IHs2 ((true, c, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s1) :: l)  (Optt t0 t) h b);try eassumption.
     *
       inversion H3.
       split.  split. 2:auto.
       destruct H2 as [[H2 H10] | [ H2 | [H2 H6]]].
       subst. inversion H2. subst. inversion H0. subst.
       eapply IsRB_co_r. eapply isrb_tagupdate; try eassumption.
       eapply isrb_tagupdate; try eassumption.
       inversion H2. subst. eapply IsRB_co_b.
       eapply isrb_tagupdate; try eassumption.
       eapply isrb_tagupdate; try eassumption.
       inversion H2.

       destruct H2 as [ [H9 H10 ] | [ H2 | [H2 H6]]].
       subst. inversion H9. subst.
        left. split. reflexivity. auto.
       subst. inversion H2. subst.
        right. left. reflexivity.
       subst. inversion H2.
Qed.

(** 保证split过后得到的half tree 和RBtree 满足 RB dep性质*)
Theorem general_split_RB_dep :
  forall lb rb s l n depth t h b,
   (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false)) ->
  is_redblack_dep s n -> is_redblack_dep_half l depth n ->
   (h , b) = general_split lb rb t s l -> (exists n' d',  is_redblack_dep b n' /\
   is_redblack_dep_half h d' n' ).
Proof.
  intros. revert l n depth t h b H0 H1 H2.
  induction s.
  - intros. inversion H2. subst. exists O. exists depth. split.
     apply IsRB_dep_em.   inversion H0. subst. auto.
  - intros. simpl in H2.
    destruct (lb k).
    + (* left part *)
      clear IHs2.
      inversion H0.
      subst.
      apply (IHs1 ((false, Red, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l)  n depth (Optt t0 t) h b); try eassumption.
      eapply IsRB_dep_r_cons. auto.
      eapply isrb_tagupdate_dep; try eassumption.
      subst.
      apply (IHs1 ((false, Black, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l) n0  depth (Optt t0 t) h b ); try eassumption.
      eapply IsRB_dep_b_cons; try eassumption.
      eapply isrb_tagupdate_dep; try eassumption.
    + destruct (rb k).
    * (*right part*)
      clear IHs1.
      inversion H0.
      subst.
      apply (IHs2 ((true, Red, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l)n depth (Optt t0 t) h b ); try eassumption.
      eapply IsRB_dep_r_cons. auto.
      eapply isrb_tagupdate_dep; try eassumption.
      subst.
      apply (IHs2 ((true, Black, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l)  n0 depth (Optt t0 t) h b); try eassumption.
      eapply IsRB_dep_b_cons; try eassumption.
      eapply isrb_tagupdate_dep; try eassumption.
    * inversion H2. exists n. exists depth.
      split. 2: auto.
      inversion H0.
      subst. eapply IsRB_dep_r. eapply isrb_tagupdate_dep; try eassumption. eapply isrb_tagupdate_dep; try eassumption.
      subst. eapply IsRB_dep_b. eapply isrb_tagupdate_dep; try eassumption. eapply isrb_tagupdate_dep; try eassumption.
Qed.

Theorem general_split_RB_dep_enhance :
  forall lb rb s l n depth t h b,
   (forall Rb,  lb Rb  = negb (rb Rb ) \/ (lb Rb = false /\ rb Rb = false)) ->
  is_redblack_dep s n -> is_redblack_dep_half l depth n ->
   (h , b) = general_split lb rb t s l -> (exists n' ,  is_redblack_dep b n' /\
   is_redblack_dep_half h depth n' ).
Proof.
  intros. revert l n depth t h b H0 H1 H2.
  induction s.
  - intros. inversion H2. subst. exists O. split.
     apply IsRB_dep_em.   inversion H0. subst. auto.
  - intros. simpl in H2.
    destruct (lb k).
    + (* left part *)
      clear IHs2.
      inversion H0.
      subst.
      apply (IHs1 ((false, Red, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l)  n depth (Optt t0 t) h b); try eassumption.
      eapply IsRB_dep_r_cons. auto.
      eapply isrb_tagupdate_dep; try eassumption.
      subst.
      apply (IHs1 ((false, Black, k, f (f v t) t0, default, tag_tree_t (Optt t0 t) s2) :: l) n0  depth (Optt t0 t) h b ); try eassumption.
      eapply IsRB_dep_b_cons; try eassumption.
      eapply isrb_tagupdate_dep; try eassumption.
    + destruct (rb k).
    * (*right part*)
      clear IHs1.
      inversion H0.
      subst.
      apply (IHs2 ((true, Red, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l)n depth (Optt t0 t) h b ); try eassumption.
      eapply IsRB_dep_r_cons. auto.
      eapply isrb_tagupdate_dep; try eassumption.
      subst.
      apply (IHs2 ((true, Black, k, f (f v t) t0, default,
        tag_tree_t (Optt t0 t) s1) :: l)  n0 depth (Optt t0 t) h b); try eassumption.
      eapply IsRB_dep_b_cons; try eassumption.
      eapply isrb_tagupdate_dep; try eassumption.
    * inversion H2. exists n.
      split. 2: auto.
      inversion H0.
      subst. eapply IsRB_dep_r. eapply isrb_tagupdate_dep; try eassumption. eapply isrb_tagupdate_dep; try eassumption.
      subst. eapply IsRB_dep_b. eapply isrb_tagupdate_dep; try eassumption. eapply isrb_tagupdate_dep; try eassumption.
Qed.


Lemma general_split_leq :
 forall tree t0 h lo hi k0 ,
  SearchTree' lo tree k0 -> k0 < hi ->
  general_split (fun x: Key => x <=? k0) (fun x : Key => x <=? lo ) t0 tree h =
   general_split (fun x: Key => x <=? hi) (fun x : Key => x <=? lo ) t0 tree h .
Proof.
  intro.
  induction tree.
  - intros.
    simpl.
    reflexivity.
  - intros.
    inversion H. subst.
    apply search_popro in H10.
    assert (k <=? k0 = true).
    { eapply lteb_lte. tr. }
    assert (k <=? hi = true).
    { eapply lteb_lte. tr. }
    simpl.
    rewrite H1, H2.
    apply IHtree1.
    eapply search_popro2. try eassumption.
    auto. auto.
Qed.

End Section_general_split.
