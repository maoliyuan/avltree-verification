From Coq Require Import Lists.List.
Require Import RBT.Verif.RBtree_Type.
Require Import RBT.Verif.RBtree_Definition. 

Section Section_Half_Tree.

Context {rbt:RBtree_setting}. 
Existing Instance rbt. 

Definition Half_tree : Type := (bool * color * Key * Value * Tag * RBtree ).

(*Some simple Properties*)
  Definition fst_false (l :  Half_tree) : Prop :=
  match l with
  |(false, co, k, v, t, r) => True
  |(true, co, k, v, t, r) => False
  end.
  Definition fst_black (h : list Half_tree) : Prop :=
  match hd_error h with
  |None => True
  |Some (b, c, k ,v, t, r) => c = Black
  end.
  Definition fst_black' (h : list Half_tree):Prop := fst_black h /\ ~ h =nil.
  Fixpoint last_black (l : list Half_tree) : Prop :=
  match l with
  | nil  => False 
  | a :: nil => match a with 
           | (_, c, _, _ , _ ,_ ) => c = Black
           end
  |_ :: l' => last_black l'
  end.
  (*性质P: 半树tag为default*)
  Definition P : Half_tree -> Prop :=  fun x =>  snd ( fst x) = default.
  
  Fixpoint accumulate_tag_for_ht (l : list Half_tree) : Tag :=
  match l with
  | nil => default
  |( pb, pc, p, pv, pt, brother) :: l' =>
    Optt (accumulate_tag_for_ht l') pt
  end.
  Lemma accumulate_default : forall h ,
   Forall P h ->
      default = accumulate_tag_for_ht h.
  Proof.
    intros.
    induction H.
      - reflexivity.
      - 
         unfold P in H. destruct x. repeat destruct p.
         simpl in H. subst t.
         simpl.
         rewrite <- IHForall.
         rewrite Optt_default. auto.
  Qed.


(**拼接完整的树*)
Definition complete_tree_one  (b : RBtree) (H : Half_tree): RBtree :=
match H with
|(pb, pc, p, pv, pt, brother) =>
  (*当前子树base为左子树(false) 还是右(true) *)
  match pb with
  |false => T pc b p pv pt brother
  |true => T pc brother p pv pt b
  end
end.
Fixpoint complete_tree  (l: list Half_tree) (b : RBtree) : RBtree :=
match l with
|nil => b
|(pb, pc, p, pv, pt, brother) :: l' =>
  (*当前子树base为左子树(false) 还是右(true) *)
  match pb with
  |false => complete_tree l'  (T pc b p pv pt brother)
  |true => complete_tree l' (T pc brother p pv pt b)
  end
end.
Lemma complete_tree_true : forall l b  pc p pv pt brother,
 complete_tree (  (true, pc, p, pv, pt, brother) :: l) b = 
    complete_tree l (T pc brother p pv pt b).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
Lemma complete_tree_false : forall l b  pc p pv pt brother,
 complete_tree (  (false, pc, p, pv, pt, brother) :: l) b = 
    complete_tree l (T pc b p pv pt brother).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
Theorem complete_tree_app :
 forall l h r ,
  complete_tree (l ++ h) r = complete_tree h (complete_tree l r).
Proof.
 intros.
 revert r.
 induction l.
 - intros.
   simpl.
   reflexivity.
 - intros.
   destruct a.
   repeat destruct p.
   destruct b.
   + simpl.
     apply IHl.
   + simpl.
     apply IHl.
Qed.

(*SearchTree AND RedBlack Properties*)
Inductive SearchTree_half : Key -> list Half_tree -> Key ->  Prop :=
|ST_nil : forall lo hi, lo < hi -> SearchTree_half lo nil hi
|ST_cons_true : forall lo hi l co k kv kt tree low,
  SearchTree_half lo l hi  -> k < hi -> SearchTree' lo tree k -> 
   k <= low -> low < hi->
    SearchTree_half low ((true,co,k,kv,kt,tree)::l) hi
|ST_cons_false : forall  lo  hi l co k kv kt tree high,
  SearchTree_half lo l hi  -> k < hi -> SearchTree' k tree hi -> 
   high <= k -> lo < high ->
   SearchTree_half lo ((false,co,k,kv,kt,tree)::l) high.
Inductive SearchTree_half_tree: Key -> Half_tree -> Key -> Prop :=
| ST_ht_true : forall lo hi co k v t tree,
  SearchTree' lo tree k -> k < hi -> 
    SearchTree_half_tree  lo (true, co, k,v,t,tree) hi
| ST_ht_false : forall lo hi co k v t tree,
  SearchTree' k tree hi -> lo < k ->
    SearchTree_half_tree  lo (false, co, k,v,t,tree) hi.
Inductive SearchTree_half_out : Key -> list Half_tree -> Key -> Prop :=
| ST_out_nil : forall lo hi, lo < hi -> SearchTree_half_out lo nil hi 
| ST_out_cons : forall lo hi l b co k v t tree low high,
 SearchTree_half_out lo l hi ->
  SearchTree_half_tree low (b,co,k,v,t,tree) high ->
   SearchTree_half_out (min_k low lo) ((b,co,k,v,t,tree)::l) (max_k high hi).
Inductive is_redblack_color_half : list Half_tree -> color -> Prop :=
|IsRB_co_nil: is_redblack_color_half nil Black
|IsRB_co_r_cons: forall  l b k kv kt tree,
   is_redblack_color_half l Red ->
   is_redblack_color tree Red ->
   is_redblack_color_half ((b,Red,k,kv,kt,tree)::l) Black
|IsRB_co_b_cons: forall l c b k kv kt tree,
   is_redblack_color_half l Black ->
   is_redblack_color tree Black ->
   is_redblack_color_half ((b,Black,k,kv,kt,tree)::l) c.
Inductive is_redblack_dep_half : list Half_tree -> nat -> nat -> Prop :=
|IsRB_dep_nil: forall n , is_redblack_dep_half nil n n
|IsRB_dep_r_cons: forall  l b k kv kt tree nown needn,
   is_redblack_dep_half l nown needn ->
   is_redblack_dep tree needn -> 
   is_redblack_dep_half ((b,Red,k,kv,kt,tree)::l) nown  needn
|IsRB_dep_b_cons: forall l b k kv kt tree nown needn ,
   is_redblack_dep_half l nown (S needn) -> 
   is_redblack_dep tree needn -> 
   is_redblack_dep_half ((b,Black,k,kv,kt,tree)::l) nown  needn.
Inductive is_redblack_color_half_loose : list Half_tree -> color -> Prop :=
|IsRB_co_nil_l: forall c, is_redblack_color_half_loose nil c
|IsRB_co_r_cons_l: forall  l b k kv kt tree,
   is_redblack_color_half_loose l Red ->
   is_redblack_color tree Red ->
   is_redblack_color_half_loose ((b,Red,k,kv,kt,tree)::l) Black
|IsRB_co_b_cons_l: forall l c b k kv kt tree,
   is_redblack_color_half_loose l Black ->
   is_redblack_color tree Black ->
   is_redblack_color_half_loose ((b,Black,k,kv,kt,tree)::l) c.

(*SearchTree Lemmas*)
  Lemma search_h_popro2 : 
   forall lo t hi k ,
     SearchTree_half lo t hi -> k <= hi/\ lo < k -> SearchTree_half lo t k .
  Proof. 
    intros. revert lo hi k H H0.
    induction t.
    -  intros. constructor. inversion H. destruct H0. tr.
    -  intros. inversion H.
       + subst.  destruct H0.
       eapply ST_cons_true. 3: apply H5.
       eapply IHt. apply H3.
       split. auto.
       pose proof search_popro _ _ _ H5.
       TR 5.
       tr.
       auto.
       auto.
       + subst. destruct H0.
         eapply ST_cons_false.
         3: apply H5.
         eapply IHt. apply H3.
         split. right. reflexivity. TR 5.
         auto.
         TR 5.
         auto.
  Qed.
  Lemma search_h_popro3 : 
   forall lo t hi k ,
     SearchTree_half lo t hi -> lo <= k /\ k < hi -> SearchTree_half k t hi .
  Proof.
  intros. revert lo hi k H H0.
    induction t.
    -  intros. constructor. inversion H. destruct H0. tr.
    -  intros. inversion H.
       + subst.  destruct H0.
       eapply ST_cons_true. 3: apply H5.
       eapply IHt. apply H3.
       split. right. auto.
        pose proof search_popro _ _ _ H5.
       TR 5.
       tr.
       TR 5.
       auto.
       + subst. destruct H0.
         eapply ST_cons_false.
         3: apply H5.
         eapply IHt. apply H3.
         split.
         auto.
         TR 5.
         auto.
         TR 5.
         auto.
  Qed.
  Lemma search_half_popro :
   forall lo l hi,
    SearchTree_half_out lo l hi -> lo < hi.
  Proof.
    intros.
    induction H.
    - auto.
    - inversion H0.
      + subst.
      assert (low < high ).
      { pose proof search_popro _ _ _ H9. tr. }
      eapply min_max; try eassumption.
      + subst.
      assert (low < high ).
      { pose proof search_popro _ _ _ H9. tr. }
      eapply min_max; try eassumption.
  Qed.
  Lemma search_half_popro2:
    forall lo l hi k,
     SearchTree_half_out lo l k -> k < hi -> SearchTree_half_out lo l hi .
  Proof.
    intros.
    induction H.
    - constructor. tr.
    - assert (max_k (max_k high hi0) hi = hi).
      { unfold max_k at 1.
        assert (max_k high hi0 <? hi = true).
        { eapply ltb_lt. auto. }
        rewrite H2.
        reflexivity. }
      rewrite <- H2.
      constructor.
      + eapply IHSearchTree_half_out.
        eapply max_lt_right; try eassumption.
      + inversion H1.
       * subst.
         eapply ST_ht_true; try eassumption.
         pose proof max_left high hi0.
         tr.
       * subst.
         eapply ST_ht_false; try eassumption.
         eapply search_popro2_lte; try eassumption.
         apply max_left.
  Qed.
  Lemma search_half_popro2_lte:
    forall lo l hi k,
     SearchTree_half_out lo l k -> k <= hi -> SearchTree_half_out lo l hi .
  Proof.
    intros.
    destruct H0. eapply search_half_popro2; try eassumption.
    subst. auto.
  Qed.
  Lemma search_half_popro3:
    forall lo l hi k,
     SearchTree_half_out k l hi -> lo < k -> SearchTree_half_out lo l hi .
  Proof.
    intros.
    induction H.
    - constructor. tr.
    - assert (min_k (min_k low lo0) lo = lo).
      { unfold min_k at 1.
        assert (min_k low lo0  <? lo = false).
        { eapply ltb_false_lte. left. auto. }
        rewrite H2.
        reflexivity. }
      rewrite <- H2.
      constructor.
      + eapply IHSearchTree_half_out.
        eapply min_lt_right; try eassumption.
      + inversion H1.
       * subst.
         eapply ST_ht_true; try eassumption.
         eapply search_popro3_lte; try eassumption.
         pose proof min_left low lo0.
         auto.
       * subst.
         eapply ST_ht_false; try eassumption.
         pose proof min_left low lo0.
         tr.
  Qed.
  Lemma search_half_popro3_lte:
    forall lo l hi k,
     SearchTree_half_out k l hi -> lo <= k -> SearchTree_half_out lo l hi .
  Proof.
    intros.
    destruct H0. eapply search_half_popro3; try eassumption.
    subst. auto.
  Qed.
  Theorem complete_st_pre:
   forall l lo hi tree,
    SearchTree_half lo l hi -> SearchTree' lo tree hi -> SearchTree (complete_tree l tree).
  Proof.
    intro.
    induction l.
    - intros. simpl. eapply ST_intro. apply H0.
    - intros. inversion H.
      + simpl. subst. apply IHl with lo0 hi. auto. apply ST_T. auto.
        eapply search_popro3_lte; try eassumption.
      + simpl. subst. apply IHl with lo hi0. auto. apply ST_T. 
        eapply search_popro2_lte; try eassumption. auto.
  Qed.
  Theorem complete_lt :
  forall lo hi h tree,
   SearchTree' lo (complete_tree h tree) hi ->
     SearchTree' lo tree hi.
  Proof.
    intros.
    revert lo hi tree H.
    induction h.
    - intros.
      simpl in H.
      auto.
    - intros.
      destruct a. repeat destruct p.
      destruct b.
      + simpl in H.
        pose proof IHh lo hi _ H.
        inversion H0. subst.
        eapply search_popro3; try eassumption.
        eapply search_popro; try eassumption.
      + simpl in H.
        pose proof IHh lo hi _ H.
        inversion H0. subst.
        eapply search_popro2; try eassumption.
        eapply search_popro; try eassumption.
  Qed.
  Theorem search_complete : forall l b lo hi olo ohi,
   SearchTree' lo b hi -> SearchTree_half lo l hi -> SearchTree_half_out olo l ohi ->
     SearchTree' (min_k lo olo) (complete_tree l b) (max_k hi ohi).
  Proof.
    intro.
    induction l.
    - intros.
      simpl.
      pose proof min_left lo olo.
      pose proof max_left hi ohi.
      pose proof search_popro2_lte _ _ _ _ H H3.
      eapply search_popro3_lte; try eassumption.
    - intros.
      destruct a. repeat destruct p.
      destruct b0.
      + inversion H0; subst. inversion H1; subst.
        simpl.
        inversion H17; subst.
        pose proof search_popro _ _ _ H9.
        pose proof search_popro _ _ _ H12.
        assert (low <= lo).
        { tr. }
        rewrite <- min_asso.
        rewrite (min_comm lo low).
        rewrite (min_lte _ _  H4).
        assert (SearchTree' (max_k lo0 low) r k).
        { pose proof lte_complete  lo0 low.
          destruct H5.
          * rewrite (max_lte _ _ H5). auto.
          * rewrite max_comm.
            rewrite (max_lte _ _ H5). auto. }
        assert (SearchTree' (max_k lo0 low) (T c r k v t b) hi ).
        { eapply ST_T; try eassumption.
          eapply search_popro3_lte; try eassumption. }
        assert (SearchTree_half (max_k lo0 low) l hi).
        {
          eapply search_h_popro3; try eassumption.
          split.
          * apply max_left.
          * 
          erewrite <- max_lt.
          split. tr. tr. }
         pose proof IHl _ _ _ _ _ H6 H7 H16; clear IHl.
         assert (min_k low lo1 <= min_k (max_k lo0 low) lo1 ).
         { pose proof lte_complete  lo0 low.
           destruct H18.
           * erewrite (max_lte _ _ H18).
             right. auto.
           * rewrite max_comm.
             erewrite (max_lte _ _ H18).
             eapply min_xz; try eassumption. }
         eapply search_popro3_lte.
         2 : apply H18.
         eapply search_popro2_lte; try eassumption.
         erewrite (max_comm high hi0).
         erewrite <- max_asso.
         eapply max_left.
     + inversion H0; subst. inversion H1; subst.
        simpl.
        inversion H17; subst.
        pose proof search_popro _ _ _ H9.
        pose proof search_popro _ _ _ H12.
        assert (hi <= high).
        { tr. }
        rewrite <- max_asso.
        rewrite (max_lte _ _  H4).
        assert (SearchTree' k r (min_k hi0 high)).
        { pose proof lte_complete hi0 high.
          destruct H5.
          * rewrite (min_lte _ _ H5). auto.
          * rewrite min_comm.
            rewrite (min_lte _ _ H5). auto. }
        assert (SearchTree' lo (T c b k v t r) (min_k hi0 high) ).
        { eapply ST_T; try eassumption.
          eapply search_popro2_lte; try eassumption. }
        assert (SearchTree_half lo l  (min_k hi0 high)).
        {
          eapply search_h_popro2; try eassumption.
          split.
          * apply min_left.
          *
          erewrite <- min_lt.
          split. TR 5. tr. }
         pose proof IHl _ _ _ _ _ H6 H7 H16; clear IHl.
         assert ((max_k (min_k hi0 high) hi1) <= (max_k high hi1) ).
         { pose proof lte_complete hi0 high.
           destruct H18.
           * 
             erewrite (min_lte _ _ H18).
             eapply max_xz; try eassumption.
           * rewrite min_comm.
             erewrite (min_lte _ _ H18).
             right. auto. }
         eapply search_popro2_lte.
         2 : apply H18.
         eapply search_popro3_lte; try eassumption.
         erewrite (min_comm low lo0).
         erewrite <- min_asso.
         eapply min_left.
  Qed.
  Lemma halftree_false_key_st : forall h lo hi k,
   Forall fst_false h ->
     Forall (fun x: Half_tree =>  k < snd ( fst (fst (fst x)))) h ->
      k < hi ->
       SearchTree_half_out lo h hi ->
        SearchTree_half_out k h hi.
  Proof.
    intro.
    induction h.
    - intros.
      eapply ST_out_nil; try eassumption.
    - intros.
      destruct a. repeat destruct p.
      inversion H; subst.
      inversion H0; subst.
      simpl in  H5.
      simpl in H7.
      destruct b.
      + inversion H5.
      + inversion H2. subst.
        inversion H17; subst.
        rewrite <- (min_self k).
        rewrite <- (max_self ( max_k high hi0)).
        eapply ST_out_cons.
        * assert (SearchTree_half_out lo0 h (max_k high hi0)).
          { eapply search_half_popro2_lte; try eassumption.
            apply max_right. }
          clear H16.
          eapply IHh; try eassumption.
        * eapply ST_ht_false; try eassumption.
        eapply search_popro2_lte; try eassumption.
        apply max_left.
  Qed.
  Lemma false_ht_true_app_st : forall l c k v t left h lo hi x x0 lo0,
    Forall fst_false l ->
     SearchTree_half  lo l hi ->
       SearchTree' x left k ->
         SearchTree_half x h x0 -> k < x0  ->  k < hi  ->
         SearchTree_half_out  lo0 l x0 ->
          SearchTree_half k (l ++ (true, c, k, v, t, left) :: h) (min_k hi x0).
  Proof.
    intro.
    induction l.
    - intros.
      simpl.
      pose proof search_popro _ _ _ H1.
      pose proof min_lt hi x0.
      eapply ST_cons_true; try eassumption.
      eapply search_h_popro2; try eassumption.
      split. apply min_right.
      rewrite <- H7. split. tr. tr.
      rewrite <- H7. split. tr. tr.
      right. auto.
      rewrite <- H7. split. tr. tr.
   - intros.
     destruct a. repeat destruct p.
     inversion H; subst.
     simpl in H8.
     destruct b.
     + contradiction.
     + inversion H0. subst.
       inversion H5;subst.
       inversion H23; subst.
       rewrite <- app_comm_cons.
       pose proof search_popro _ _ _ H15.
       assert (min_k hi (max_k high hi1) = hi).
       { rewrite  (min_lte hi (max_k high hi1)).
         reflexivity.
         pose proof max_left high hi1.
         tr. }
       rewrite H7.
       eapply ST_cons_false. 4: tr. 4: tr.
       eapply IHl; try eassumption.
       TR 5.
       eapply search_half_popro2_lte; try eassumption.
       apply max_right.
       pose proof min_lt hi0 (max_k high hi1).
       rewrite <- H10.
       split. tr. pose proof max_left high hi1. tr.
       pose proof lte_complete hi0 (max_k high hi1).
       destruct H10.
       * 
         pose proof min_lte hi0 _ H10.
         rewrite H11.
         auto.
       * 
         pose proof min_lte _ _ H10.
         rewrite min_comm.
         rewrite H11.
         clear H18.
         eapply search_popro2_lte; try eassumption.
         apply max_left.
  Qed.



(*Redblack Lemmas*)
  Lemma isr_isb_half:
   forall t, is_redblack_color_half t Red -> is_redblack_color_half t Black .
  Proof.
    intros.
    induction H.
    - apply IsRB_co_nil.
    - eapply IsRB_co_r_cons; try eassumption.
    - eapply IsRB_co_b_cons; try eassumption.
  Qed.
  Lemma isb_isr_half : forall l , ~ l = nil ->
   is_redblack_color_half l Black ->
  fst_black l -> is_redblack_color_half l Red.
  Proof.
    intros.
    inversion H0.
    subst. exfalso. auto.
    unfold fst_black in H0. subst. inversion H1.
    subst. eapply IsRB_co_b_cons; try eassumption.
  Qed.
  Lemma isrb_bro: forall b c k v t bro co l, is_redblack_color_half ((b, c, k, v, t, bro)::l) co -> is_redblack_color bro c.
  Proof.
    intros.
    inversion H.
    subst. auto.
    subst. auto.
  Qed.
  Lemma isrb_change_half : forall b1 b2 c k1 k2 v1 v2 t1 t2 tree1 tree2 co l,
      is_redblack_color_half ((b1, c, k1, v1, t1, tree1)::l) co ->
     is_redblack_color tree1 c -> is_redblack_color tree2 c
       -> is_redblack_color_half ((b2, c, k2, v2, t2, tree2)::l) co.
  Proof.
    intros.
    inversion H.
    subst. eapply IsRB_co_r_cons; try eassumption.
    subst. eapply IsRB_co_b_cons; try eassumption.
  Qed.
  Lemma rb_co_loose2ori: forall l c,
   is_redblack_color_half_loose l c ->
    last_black l ->  is_redblack_color_half l c.
  Proof.
    intros.
    induction H.
    - subst. inversion H0.
    - subst. destruct l. inversion H0.  eapply IsRB_co_r_cons; try eassumption.
      eapply IHis_redblack_color_half_loose;try eassumption.
    - subst.
      eapply IsRB_co_b_cons; try eassumption.
      destruct l.
      eapply IsRB_co_nil.
      eapply IHis_redblack_color_half_loose;try eassumption.
  Qed.
  Lemma rb_co_ori2loose: forall l c,
   is_redblack_color_half l c -> is_redblack_color_half_loose l c.
  Proof.
    intros.
    induction H.
    - eapply IsRB_co_nil_l.
    - eapply IsRB_co_r_cons_l;try eassumption.
    - eapply IsRB_co_b_cons_l;try eassumption.
  Qed.
  Lemma isr_isb_half_loose:
   forall t, is_redblack_color_half_loose t Red -> is_redblack_color_half_loose t Black .
  Proof.
    intros.
    induction H.
    - apply IsRB_co_nil_l.
    - eapply IsRB_co_r_cons_l; try eassumption.
    - eapply IsRB_co_b_cons_l; try eassumption.
  Qed.
  Lemma isb_isr_half_loose:
   forall t, fst_black t ->
    is_redblack_color_half_loose t Black -> is_redblack_color_half_loose t Red .
  Proof.
    intros.
    inversion H0.
    - apply IsRB_co_nil_l.
    - subst. inversion H.
    - subst. eapply IsRB_co_b_cons_l; try eassumption.
  Qed.
    Lemma isrb_dep_app_Red : forall l0 l b k v t bro d n x,
   is_redblack_dep_half l d n ->
    is_redblack_dep bro n ->
      is_redblack_dep_half l0 n x ->
        is_redblack_dep_half (l0 ++ (b, Red, k, v, t, bro) :: l) d x.
  Proof.
    intro.
    induction l0.
    - intros. simpl.
      inversion H1. subst.
      eapply IsRB_dep_r_cons;try eassumption.
    - intros.
      destruct a.
      repeat destruct p.
      inversion H1.
      + subst.
        eapply IsRB_dep_r_cons;try eassumption.
        eapply IHl0;try eassumption. 
      + subst.
        eapply IsRB_dep_b_cons;try eassumption.
        eapply IHl0;try eassumption.
  Qed.

  Lemma isrb_dep_app_Black : forall l0 l b k v t bro d n x,
   is_redblack_dep_half l d (S n) ->
    is_redblack_dep bro n ->
      is_redblack_dep_half l0 n x ->
        is_redblack_dep_half (l0 ++ (b, Black, k, v, t, bro) :: l) d x.
  Proof.
    intro.
    induction l0.
    - intros. simpl.
      inversion H1. subst.
      eapply IsRB_dep_b_cons;try eassumption.
    - intros.
      destruct a.
      repeat destruct p.
      inversion H1.
      + subst.
        eapply IsRB_dep_r_cons;try eassumption.
        eapply IHl0;try eassumption. 
      + subst.
        eapply IsRB_dep_b_cons;try eassumption.
        eapply IHl0;try eassumption.
  Qed.




Lemma complete_redblack_co :
  forall  h b , is_redblack_color_half h Black -> ~ b = Empty -> is_redblack_color b Black ->
  (  ( Red_tree b /\ fst_black h ) \/ Black_tree b)
   -> is_redblack_color (makeBlack(complete_tree h b)) Red.
Proof.
  intro.
  induction h.
  - intros. destruct b.
    + exfalso . auto.
    + simpl. inversion H1.
      subst. eapply IsRB_co_b; try eassumption. eapply isr_isb ;try eassumption. eapply isr_isb; try eassumption.
      subst. eapply IsRB_co_b; try eassumption.
  - intros.
    destruct a. repeat destruct p.
    inversion H.
    + subst. destruct b0.
      * simpl.
        assert (is_redblack_color b Red).
        {
         destruct b. exfalso. auto.
         simpl in H2. unfold fst_black in H2. unfold hd_error in H2.
         destruct c. exfalso. inversion H2. inversion H3. inversion H6. inversion H3.
         inversion H1 ; subst.
         eapply IsRB_co_b; try eassumption.
        }
        eapply IHh.
        eapply isr_isb_half; try eassumption.
        unfold not; intros. inversion H4.
        eapply IsRB_co_r; try eassumption.
        left. split. reflexivity.
        inversion H5. reflexivity.
      * simpl.
        assert (is_redblack_color b Red).
        {
         destruct b. exfalso. auto.
         simpl in H2. unfold fst_black in H2. unfold hd_error in H2.
         destruct c. exfalso. inversion H2. inversion H3. inversion H6. inversion H3.
         inversion H1 ; subst.
         eapply IsRB_co_b; try eassumption.
        }
        eapply IHh.
        eapply isr_isb_half; try eassumption.
        unfold not; intros. inversion H4.
        eapply IsRB_co_r; try eassumption.
        left. split. reflexivity.
        inversion H5. reflexivity.
    + subst. destruct b0.
      * simpl. apply IHh.
        auto.
        unfold not; intros. inversion H3.
        eapply IsRB_co_b; try eassumption.
        right. reflexivity.
      * simpl. apply IHh.
        auto.
        unfold not; intros. inversion H3.
        eapply IsRB_co_b; try eassumption.
        right. reflexivity.
Qed.
Lemma complete_rb_rev : forall  h b , ~ h = nil ->
 is_redblack_color (complete_tree h b) Red -> (
  is_redblack_color_half h Black /\ is_redblack_color b Black /\
    (  ( Red_tree b /\ fst_black h ) \/ ~ Red_tree b) ).
Proof.
  intro.
  induction h.
  - intros. exfalso. auto.
  - intros. destruct a. repeat destruct p.
    destruct h.
    *
    destruct b0.
    + simpl in H0. inversion H0. subst. split. apply IsRB_co_b_cons. apply IsRB_co_nil.
      auto. split. auto. unfold fst_black, hd_error. destruct b. right. unfold not;intro;contradiction.
      destruct c. left. split. reflexivity. reflexivity. right. unfold not;intro. inversion H1.
    + simpl in H0. inversion H0. subst. split. apply IsRB_co_b_cons. apply IsRB_co_nil.
      auto. split. auto. unfold fst_black, hd_error. destruct b. right. unfold not;intro. inversion H1.
      destruct c. left. split. reflexivity. reflexivity. right. unfold not;intro. inversion H1.
    * assert (h::h0 <> nil). { discriminate. }
      destruct b0.
      + rewrite complete_tree_true in H0.
        pose proof IHh _ H1 H0. destruct H2 as [ H2 [ H3 [ [ H4 H5] | H4 ]]].
        assert (c = Red). { destruct c.  reflexivity.  inversion H4. } subst.
         inversion H3. subst. split.
         inversion H2. subst. inversion H5. subst.
         eapply IsRB_co_r_cons. eapply IsRB_co_b_cons; try eassumption. auto. split.
         eapply isrb_right; try eassumption.
         right. destruct b. unfold not;intro. inversion H6.
         destruct c. inversion H12.  unfold not;intro. inversion H6.
        assert (c = Black). { destruct c. simpl in H4. exfalso. apply H4. auto. reflexivity. } subst.
         inversion H3. subst.
         split.
         eapply IsRB_co_b_cons; try eassumption.
         split. auto. unfold fst_black, hd_error. destruct b. right.  unfold not;intro. inversion H5.
         destruct c. left. split. reflexivity. reflexivity. right.  unfold not;intro. inversion H5.
      + rewrite complete_tree_false in H0.
        pose proof IHh _ H1 H0. destruct H2 as [ H2 [ H3 [ [ H4 H5] | H4 ]]].
        assert (c = Red). { destruct c.  reflexivity.  inversion H4. } subst.
         inversion H3. subst. split.
         inversion H2. subst. inversion H5. subst.
         eapply IsRB_co_r_cons. eapply IsRB_co_b_cons; try eassumption. auto. split.
         eapply isr_isb; try eassumption.
         right. destruct b.  unfold not;intro. inversion H6.
         destruct c. inversion H8.  unfold not;intro. inversion H6.
        assert (c = Black). { destruct c. simpl in H4. exfalso. apply H4. auto. reflexivity. } subst.
         inversion H3. subst.
         split.
         eapply IsRB_co_b_cons; try eassumption.
         split. auto. unfold fst_black, hd_error. destruct b. right. unfold not;intro. inversion H5.
         destruct c. left. split. reflexivity. reflexivity. right.  unfold not;intro. inversion H5.
Qed.
Lemma complete_isrb: forall h b, ~ h = nil ->
  is_redblack_color_half h Black -> (makeBlack (complete_tree h b ) = (complete_tree h b)).
Proof.
  intro.
  induction h.
  - intros. exfalso. auto.
  - intros.
    destruct h.
    + inversion H0. inversion H3. subst. destruct b0.  reflexivity. reflexivity.
    + destruct a. repeat destruct p.
      inversion H0.
      * subst. pose proof isr_isb_half _ H3. assert (h::h0 <> nil). { discriminate. }
        destruct b0. repeat rewrite complete_tree_true. eapply IHh; try eassumption.
        repeat rewrite complete_tree_false. eapply IHh; try eassumption.
      * subst. assert (h::h0 <> nil). { discriminate. }
        destruct b0. repeat rewrite complete_tree_true. eapply IHh; try eassumption.
        repeat rewrite complete_tree_false. eapply IHh; try eassumption.
Qed.
Lemma complete_isb_isr: forall h b, ~ h = nil -> is_redblack_color_half h Black ->
 is_redblack_color (complete_tree h b) Black -> is_redblack_color (complete_tree h b) Red.
Proof.
  intros.
  assert (complete_tree h b = makeBlack (complete_tree h b)).
  { symmetry. apply complete_isrb; try eassumption.
   }
   rewrite H2.
   eapply isb_isr. auto.
Qed.
Lemma complete_tree_empty_co: forall l,
  is_redblack_color_half l Black -> is_redblack_color (makeBlack(complete_tree l Empty)) Red.
Proof.
  intro.
  destruct l.
  - intros. simpl. apply IsRB_co_leaf.
  - intros. inversion H.
    + subst.  pose proof isr_isb_half _ H2. inversion H2;subst. pose proof IsRB_co_leaf Red.
      destruct b.
      rewrite complete_tree_true. eapply complete_redblack_co; try eassumption. discriminate. eapply IsRB_co_r; try eassumption. left. split; [reflexivity | reflexivity].
      rewrite complete_tree_false. eapply complete_redblack_co; try eassumption. discriminate. eapply IsRB_co_r; try eassumption. left. split; [reflexivity | reflexivity].
    + subst. pose proof IsRB_co_leaf Black.
      destruct b.
      rewrite complete_tree_true. eapply complete_redblack_co; try eassumption. discriminate. eapply IsRB_co_b; try eassumption.  right; reflexivity.
      rewrite complete_tree_false. eapply complete_redblack_co; try eassumption. discriminate. eapply IsRB_co_b; try eassumption.  right; reflexivity.
Qed.
Lemma complete_tree_co : forall l s,
 is_redblack_color_half l Black -> is_redblack_color  s Black ->
 ( s = Empty \/ ( Red_tree s /\ fst_black l ) \/ Black_tree s ) 
   -> is_redblack_color (makeBlack(complete_tree l s)) Red.
Proof.
  intros.
  destruct H1.
  - subst. eapply complete_tree_empty_co; try eassumption.
  - eapply complete_redblack_co; try eassumption.
    destruct s;[| discriminate].
    inversion H1. destruct H2. inversion H2. inversion H2.
Qed.
Lemma complete_makeBlack_dep : forall  l r d n,
    is_redblack_dep r n ->
    is_redblack_dep_half l d n ->
     exists n' : nat, is_redblack_dep (makeBlack (complete_tree l r)) n'.
Proof.
  intro.
  induction l.
  - intros.
    simpl.
    inversion H.
    + subst;simpl. exists 0. apply IsRB_dep_em.
    + subst;simpl. exists (S n). eapply IsRB_dep_b;try eassumption.
    + subst;simpl. exists (S n0). auto.
  - intros.
     destruct a. repeat destruct p.
     inversion H0.
     +  subst.
        simpl.
        repeat (match goal with 
        | |- exists n' : nat, is_redblack_dep (makeBlack (if ?x then _ else _ )) _
               => destruct x
        | |- exists n' : nat, is_redblack_dep (makeBlack (complete_tree l _ )) _ 
              => eapply IHl;try eassumption
        | |- is_redblack_dep (T Red _ _ _ _ _) _ => eapply IsRB_dep_r;try eassumption
        end).
     + subst.
       simpl.
       repeat (match goal with 
        | |- exists n' : nat, is_redblack_dep (makeBlack (if ?x then _ else _ )) _
               => destruct x
        | |- exists n' : nat, is_redblack_dep (makeBlack (complete_tree l _ )) _ 
              => eapply IHl;try eassumption
        | |- is_redblack_dep (T Black _ _ _ _ _) _ => eapply IsRB_dep_b;try eassumption
        end).
 Qed.

End Section_Half_Tree.

