Require Import VST.floyd.proofauto.
Require Import RBT.Verif.rbt_bst_3.
Require Import RBT.Verif.RBtree_key.
Require Import Coq.micromega.Psatz.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_rbtree := Tstruct _tree noattr.

(*********************************************************************

Environmental Setting

*********************************************************************)

Definition RED_COLOR : Z := 1.
Definition BLACK_COLOR : Z := 0.

Instance Reb_Z : Reb Z := {
  Equal_bool x y := x =? y
}.

Instance Rlt_Z : Rlt Z := {
  lt_prop x y := x < y
}.

Instance Rltb_Z : Rltb Z := {
  lt_bool x y := x <? y
}.

Instance Transitive_Z : Transitive Z.
  unfold Transitive.
  unfold lt_prop in *. simpl in *. apply Z.lt_trans.
Defined.

Instance Asymmetric_Z : Asymmetric Z.
  unfold Asymmetric.
  unfold lt_prop in *. simpl in *. apply Z.lt_asymm.
Defined.

Instance Complete_Z : Complete Z.
  unfold Complete.
  unfold lt_prop in *. simpl in *. 
  intros. omega.
Defined.

Instance TotalOrder_Z : TotalOrder Z.
  apply Build_TotalOrder.
  - apply Transitive_Z.
  - apply Asymmetric_Z.
  - apply Complete_Z.
Defined.

Lemma Rb_spec_Z: @Rb_spec Z Reb_Z.
Proof. 
  unfold Rb_spec.
  simpl. intros.
  symmetry. apply Z.eqb_eq.
Qed.

Lemma Rltb_spec_Z: @Rltb_spec Z Rlt_Z Rltb_Z.
Proof.
  unfold Rltb_spec.
  simpl. intros. 
  symmetry. apply Z.ltb_lt.
Qed.

Lemma Rlt_R_Z: @Rlt_R Z Rlt_Z.
Proof. 
  unfold Rlt_R.
  intros. 
  simpl. 
  unfold iff; split.
  - intros. destruct H as [H H'].
    omega.
  - intros. split; omega.
Qed.

Lemma lte_complete_Z: forall x y, (@lte_prop Z Rlt_Z x y) \/ (@lte_prop Z Rlt_Z y x).
Proof.
  intros. unfold lte_prop.
  simpl.
  omega.
Qed. 

Program Instance C_RBT : RBtree_setting := {
  Key := Z;
  Value := Z;
  Tag := Z;
  
  KRb := Reb_Z;
  VRb := Reb_Z;
  LKR := Rlt_Z;
  LKRb := Rltb_Z;

  Opv v := v;
  f v t := v + t;
  Opvt v t := v + t;
  Opvv v1 v2 := v1 + v2;
  Optt t1 t2 := t1 + t2;

  default := 0;
  Zero := -2147483647;
  Inf := 2147483647
}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation.
  omega.
Qed.
Next Obligation.
  omega.
Qed.
Next Obligation. 
  omega. 
Qed.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. 
  lia.
Qed.

(* 
    TODO:
    Finish all the obligations.
*)

Inductive another_insert k v t : RBtree -> Prop :=
  | insert_intro : 
    forall l s h b, (l, s) = insert' k v t -> 
      (h, b) = balance' l s ->
      another_insert k v t (makeBlack (complete_tree h b)).
  
(*********************************************************************

Toolbox for Pointers

*********************************************************************)

Lemma sepalg_Tsh: sepalg.nonidentity Tsh.
Proof.
  apply top_share_nonidentity.
Qed.

(*********************************************************************

Fundamental Definitions

*********************************************************************)

(* use Z to represent color *)
Definition Col2Z (c: color) : Z :=  
  match c with
  | Red   => RED_COLOR
  | Black => BLACK_COLOR
  end.

(* turn the result of the functional lookup to the C one *)
Definition Lookup2Z (x: Key) (t: RBtree) : Z :=
  match lookup x t with
  | None    => 0    (* Default value *)
  | Some v  => v
  end.

(* representation of RBtree in memory *)
Fixpoint rbtree_rep (t: RBtree) (p: val) (p_fa: val) : mpred :=
  match t with
  | T col lch key_ value_ tag_ rch => 
    !! (Int.min_signed <= key_ <= Int.max_signed /\ 
      is_pointer_or_null p_fa) &&
    EX p_lch : val, EX p_rch : val, 
    data_at Tsh t_struct_rbtree 
      (Vint (Int.repr (Col2Z col)), 
        (Vint (Int.repr key_), 
          (Vint (Int.repr value_), 
            (Vint (Int.repr tag_), 
              (p_lch, (p_rch, p_fa)))))) p
    * rbtree_rep lch p_lch p * rbtree_rep rch p_rch p
  | E => !! (p = nullval /\ is_pointer_or_null p_fa) && emp 
  end.

(* representation of treebox in memory, assume t is a root *)
Definition treeroot_rep (t: RBtree) (b: val) :=
  EX p: val, data_at Tsh (tptr t_struct_rbtree) p b * rbtree_rep t p nullval.

(* representation of treebox in memory *)
Definition treebox_rep (t: RBtree) (b: val) (p_fa: val) :=
  EX p: val, data_at Tsh (tptr t_struct_rbtree) p b * rbtree_rep t p p_fa.

(* representation of half_tree list in memory *)
(* maybe not useful *)
Fixpoint partial_tree_rep (t: list Half_tree) (root p p_fa: val) : mpred :=
  match t with
  | []      =>  !! (p_fa = nullval) && data_at Tsh (tptr t_struct_rbtree) p root 
    (* 瀵� root 杩藉姞闄愬埗鏈夊繀瑕佸悧锛� *)  
  | (vacancy, col, key_, value_, tag_, oppo) :: l  =>
    EX p_gfa: val, EX p_oppo : val, 
        !! (Int.min_signed <= key_ <= Int.max_signed) &&
          (* 涓嶅緱宸插姞杩欎箞涓€鍙� *)
        rbtree_rep oppo p_oppo p_fa *
        partial_tree_rep l root p_fa p_gfa *
        data_at Tsh t_struct_rbtree
        (Vint (Int.repr (Col2Z col)), 
          (Vint (Int.repr key_), 
            (Vint (Int.repr value_), 
              (Vint (Int.repr tag_), 
                ((match vacancy with false => p | true => p_oppo end), 
                ((match vacancy with true => p | false => p_oppo end), p_gfa)))))) p_fa 
  end.

(* representation of half_tree list in memory, b means "branch" *)
Fixpoint partial_treebox_rep (t: list Half_tree) (root b p: val) : mpred :=
  match t with
  | []      =>  !! (p = nullval /\ root = b /\ is_pointer_or_null root) && emp 
    (* 瀵� root 杩藉姞闄愬埗鏈夊繀瑕佸悧锛� *)
  | (vacancy, col, key_, value_, tag_, ch) :: l  =>
    EX p_fa: val, EX p_oppo : val, EX b_fa : val,
    match vacancy with 
    | false   =>
        !! (Int.min_signed <= key_ <= Int.max_signed) &&
        !! (b = (field_address t_struct_rbtree [StructField _left] p)) &&
        rbtree_rep ch p_oppo p *
        field_at Tsh t_struct_rbtree [StructField _color] (Vint (Int.repr (Col2Z col))) p *
        field_at Tsh t_struct_rbtree [StructField _key] (Vint (Int.repr key_)) p *
        field_at Tsh t_struct_rbtree [StructField _value] (Vint (Int.repr value_)) p *
        field_at Tsh t_struct_rbtree [StructField _tag] (Vint (Int.repr tag_)) p *
        field_at Tsh t_struct_rbtree [StructField _right] p_oppo p *
        field_at Tsh t_struct_rbtree [StructField _fa] p_fa p *
        data_at Tsh (tptr t_struct_rbtree) p b_fa *
        partial_treebox_rep l root b_fa p_fa
        (* represent the pointer of the "branch" only *)
    | true    =>
        !! (Int.min_signed <= key_ <= Int.max_signed) &&
        !! (b = (field_address t_struct_rbtree [StructField _right] p)) &&
        rbtree_rep ch p_oppo p *
        field_at Tsh t_struct_rbtree [StructField _color] (Vint (Int.repr (Col2Z col))) p *
        field_at Tsh t_struct_rbtree [StructField _key] (Vint (Int.repr key_)) p *
        field_at Tsh t_struct_rbtree [StructField _value] (Vint (Int.repr value_)) p *
        field_at Tsh t_struct_rbtree [StructField _tag] (Vint (Int.repr tag_)) p *
        field_at Tsh t_struct_rbtree [StructField _left] p_oppo p *
        field_at Tsh t_struct_rbtree [StructField _fa] p_fa p * 
        data_at Tsh (tptr t_struct_rbtree) p b_fa *
        partial_treebox_rep l root b_fa p_fa
    end
  end.

Definition get_color_tree (t: RBtree) : Z :=
  match t with  
  | T c t1 k v tag t2 => Col2Z c
  | E => -1 
  end.

(*********************************************************************

Delete Function (Simulation)

*********************************************************************)

(*
Definition CaseFour_sol (s :RBtree) (H : Half_tree) : RBtree :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |_  ,(T Red wrl wrk wrv wrt wrr) =>
                 (T pc (T Black s p pv default (tag_tree_t wt wl)) wk (f wv wt) pt (tag_tree_t wt (makeBlack wr)))
              |_ , _ => Empty
              end
           | _ =>Empty
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Red wll wlk wlv wlt wlr),_  =>
                 (T pc (tag_tree_t wt (makeBlack wl)) wk (f wv wt) pt (T Black (tag_tree_t wt wl) p pv default s))
              |_ , _ => Empty
              end
           | _ =>Empty
           end
   end
end.

Definition CaseThree_sol (s :RBtree) (H : Half_tree) : RBtree :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Red wll wlk wlv wlt wlr), _ =>
     CaseFour_sol s
   (false, pc, p, pv, pt, (T Black (tag_tree_t wlt wll) wlk (f wlv wlt) wt 
                                   (T Red (tag_tree_t wlt wlr) wk wv default wr)))
              |_ , _ => Empty
              end
           | _ =>Empty
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |_ ,(T Red wrl wrk wrv wrt wrr) =>
     CaseFour_sol s (true, pc, p, pv, pt, 
      (T Black (T Red wl wk wv default (tag_tree_t wrt wrl)) wrk (f wrv wrt) wt 
                                   (tag_tree_t wrt wrr)))
              |_ , _ => Empty
              end
           | _ =>Empty
           end
   end
end.


Definition CaseTwo_sol (s:RBtree) (H:Half_tree) :RBtree :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=>
          (T pc s p pv pt (T Red wl wk wv wt wr))
              |Empty , Empty => (T pc s p pv pt (T Red Empty wk wv wt Empty))
              |_ ,_ => Empty
              end
           | _ =>Empty
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=>
          (T pc (T Red wl wk wv wt wr) p pv pt s)
              |Empty , Empty => (T pc (T Red Empty wk wv wt Empty) p pv pt s)
              |_ , _ => Empty
              end
           | _ =>Empty
           end
   end
end.

Definition CaseTTF_sol (s:RBtree) (H:Half_tree) : RBtree :=
(* 杩欓噷閲囩敤浜嗗師鏈夌殑璁捐锛屽皢 match s 涓嬫斁浜� *)
match H with
| (pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=> CaseTwo_sol s H
              |Empty, Empty => CaseTwo_sol s H
              |(T Red _ _ _ _ _ ), (T Black _ _ _ _ _ ) => CaseThree_sol s H
              |(T Red _ _ _ _ _ ), Empty => CaseThree_sol s H
              |_  ,(T Red _ _ _ _ _) => CaseFour_sol s H
              |_ , _ => Empty
              end
           | _ =>Empty
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=> CaseTwo_sol s H
              |Empty, Empty => CaseTwo_sol s H
              |(T Black _ _ _ _ _ ), (T Red _ _ _ _ _ ) => CaseThree_sol s H
              |Empty, (T Red _ _ _ _ _ ) => CaseThree_sol s H
              |(T Red _ _ _ _ _ ) , _ => CaseFour_sol s H
              |_ , _ => Empty
              end
           | _ =>Empty
           end
   end
end.


(* 鐢ㄤ竴涓� option Half_tree 鎸囩ず鏄惁闇€瑕佸仠姝� delete_balance *)
Definition CaseOne_sol (s:RBtree) (H:Half_tree) : option Half_tree * RBtree :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Red wl wk wv wt wr => 
              (* 杩欓噷瀵圭涓€娆� Case TTF 鐨勭粨鏋滃仛浜嗚璁� *)
              let ts := (CaseTTF_sol s (false, Red, p, pv, default, tag_tree_t wt wl)) in
              (match ts with
              | T Red _ _ _ _ _ => (Some (false, Black, wk, f wv wt, pt, tag_tree_t wt wr), ts)
              | _ => (None, CaseTTF_sol ts
                  (false, Black, wk, f wv wt, pt, tag_tree_t wt wr))
              end)
           | _ => (None, Empty)
           end
   |true => match brother with
           |T Red wl wk wv wt wr => 
              (* 杩欓噷瀵圭涓€娆� Case TTF 鐨勭粨鏋滃仛浜嗚璁� *)
              let ts := (CaseTTF_sol s (true, Red, p, pv, default, tag_tree_t wt wr)) in
              (match ts with
              | T Red _ _ _ _ _ => (Some (true, Black, wk, f wv wt, pt, tag_tree_t wt wl), ts)
              | _ => (None, CaseTTF_sol ts
                  (true, Black, wk, f wv wt, pt, tag_tree_t wt wl))
              end)
           | _ => (None, Empty)
           end
   end
end.

Fixpoint delete_balance (s: RBtree) (h: list Half_tree) (ori_color: color) :  RBtree * list Half_tree  :=
match ori_color with
(** remove 鐐逛负绾㈣壊 涓嶅奖鍝嶇粨鏋�*)
|Red => (s,h)
|Black => match h with
         |nil => (s, h) (** (makeBlack s, h)*)
         |(pb, pc, p, pv, pt, brother) :: l' =>
           match s with (**s 鏍圭粨鐐规湁涓€涓猠xtra black*)
           |T Red sl sk sv st sr => (T Black sl sk sv st sr, h)
           |_  => (*鍙岄粦*)
              match brother with
              |Empty => (s,h) (*涓嶅彲鑳戒负绌�*)
              |T Red wl wk wv wt wr => 
                (* 杩欓噷鍔犱簡涓€涓 Case one 缁撴灉鐨勮璁� *)
                match (CaseOne_sol s (pb, pc, p, pv, pt, brother)) with
                | (None, res) => delete_balance res l' Black
                | (Some hft, res) => (makeBlack res, hft :: l')
                end
              |T Black wl wk wv wt wr => delete_balance 
              (CaseTTF_sol s (pb, pc, p, pv, pt, brother)) l' Black
              end
           end
        end
end.

(* check function *)
Definition CaseFour_check (s :RBtree) (H : Half_tree) : bool :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |_  ,(T Red wrl wrk wrv wrt wrr) => true
              |_ , _ => false
              end
           | _ => false
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Red wll wlk wlv wlt wlr),_  => true
              |_ , _ => false
              end
           | _ => false
           end
   end
end.

Definition CaseThree_check (s :RBtree) (H : Half_tree) : bool :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Red wll wlk wlv wlt wlr), _ =>
     CaseFour_check s
   (false, pc, p, pv, pt, (T Black (tag_tree_t wlt wll) wlk (f wlv wlt) wt 
                                   (T Red (tag_tree_t wlt wlr) wk wv default wr)))
              |_ , _ => false
              end
           | _ => false
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |_ ,(T Red wrl wrk wrv wrt wrr) =>
     CaseFour_check s (true, pc, p, pv, pt, 
      (T Black (T Red wl wk wv default (tag_tree_t wrt wrl)) wrk (f wrv wrt) wt 
                                   (tag_tree_t wrt wrr)))
              |_ , _ => false
              end
           | _ => false
           end
   end
end.


Definition CaseTwo_check (s:RBtree) (H:Half_tree) : bool :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=> true
              |Empty , Empty => true
              |_ ,_ => false
              end
           | _ => false
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ ) => true
              |_ , _ => false
              end
           | _ => false
           end
   end
end.

Definition CaseTTF_check (s:RBtree) (H:Half_tree) : bool :=
match H with
|  (pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=> CaseTwo_check s H
              |Empty, Empty => CaseTwo_check s H
              |(T Red _ _ _ _ _ ), (T Black _ _ _ _ _ ) => CaseThree_check s H
              |(T Red _ _ _ _ _ ), Empty => CaseThree_check s H
              |_  ,(T Red wrl wrk wrv wrt wrr) => CaseFour_check s H
              |_ , _ => false
              end
           | _ => false
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=> CaseTwo_check s H
              |(T Black _ _ _ _ _ ), (T Red _ _ _ _ _ ) => CaseThree_check s H
              |(T Red _ _ _ _ _ ) ,(T _ _ _ _ _ _) => CaseFour_check s H
              |_ , _ => false
              end
           | _ => false
           end
   end
end.

Definition CaseOne_check (s:RBtree) (H:Half_tree) : bool :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Red wl wk wv wt wr => 
              (* 杩欓噷瀵圭涓€娆� Case TTF 鐨勭粨鏋滃仛浜嗚璁� *)
              (if (CaseTTF_check s (false, Red, p, pv, default, tag_tree_t wt wl))
              then
                (let ts := (CaseTTF_sol s (false, Red, p, pv, default, tag_tree_t wt wl)) in
                match ts with
                | T Red _ _ _ _ _ => true
                | _ => CaseTTF_check ts (false, Black, wk, f wv wt, pt, tag_tree_t wt wr)
                end)
              else false)
           | _ => false
           end
   |true => match brother with
           |T Red wl wk wv wt wr => 
              (* 杩欓噷瀵圭涓€娆� Case TTF 鐨勭粨鏋滃仛浜嗚璁� *)
              (if (CaseTTF_check s (true, Red, p, pv, default, tag_tree_t wt wr))
              then
                (let ts := (CaseTTF_sol s (true, Red, p, pv, default, tag_tree_t wt wr)) in
                match ts with
                | T Red _ _ _ _ _ => true
                | _ => CaseTTF_check ts (true, Black, wk, f wv wt, pt, tag_tree_t wt wl)
                end)
              else false)
           | _ => false
           end
   end
end.

Fixpoint delete_check (s: RBtree) (h: list Half_tree) (ori_color: color) : bool :=
match ori_color with
(** remove 鐐逛负绾㈣壊 涓嶅奖鍝嶇粨鏋�*)
|Red => true 
|Black => match h with
         |nil => true (** (makeBlack s, h)*)
         |(pb, pc, p, pv, pt, brother) :: l' =>
           match s with (**s 鏍圭粨鐐规湁涓€涓猠xtra black*)
           |T Red sl sk sv st sr => true
           |_  => (*鍙岄粦*)
              match brother with
              |Empty => false (*涓嶅彲鑳戒负绌�*)
              |T Red wl wk wv wt wr => 
              if CaseOne_check s (pb, pc, p, pv, pt, brother)
              then 
                (match (CaseOne_sol s (pb, pc, p, pv, pt, brother)) with
                | (None, res) => delete_check res l' Black
                | (Some hft, res) => true
                end)
              else false
              |T Black wl wk wv wt wr => 
              if CaseTTF_check s (pb, pc, p, pv, pt, brother)
              then delete_check
              (CaseTTF_sol s (pb, pc, p, pv, pt, brother)) l' Black
              else false
              end
           end
        end
end.
*)

Definition CaseFour_sol (s : RBtree) (H : Half_tree) : RBtree :=
  match H with
  | (pb, pc, p, pv, pt, brother) =>
    match pb with
    | false => 
      match brother with
      | T Black wl wk wv wt wr => 
        match wr with
        | T Red wrl wrk wrv wrt wrr =>
          (T pc (T Black s p pv default (tag_tree_t wt wl)) 
            wk (f wv wt) pt (tag_tree_t wt (makeBlack wr)))
        | _ => Empty
        end
      | _ => Empty
      end
    | true => 
      match brother with
      | T Black wl wk wv wt wr => 
        match wl with
        | T Red wll wlk wlv wlt wlr =>
          (T pc (tag_tree_t wt (makeBlack wl)) wk (f wv wt) 
            pt (T Black (tag_tree_t wt wl) p pv default s))
        | _ => Empty
        end
      | _ => Empty
      end
    end
  end.

Definition CaseThree_sol (s :RBtree) (H : Half_tree) : RBtree :=
  match H with
  | (pb, pc, p, pv, pt, brother) =>
    match pb with
    | false => 
      match brother with
      | T Black wl wk wv wt wr => 
        match wl with
        | T Red wll wlk wlv wlt wlr =>
          CaseFour_sol s
          (false, pc, p, pv, pt, (T Black (tag_tree_t wlt wll) wlk 
            (f wlv wlt) wt (T Red (tag_tree_t wlt wlr) wk wv default wr)))
        | _ => Empty
        end
      | _ => Empty
      end
    | true => 
      match brother with
      | T Black wl wk wv wt wr => 
        match wr with
        | T Red wrl wrk wrv wrt wrr =>
          CaseFour_sol s 
          (true, pc, p, pv, pt, (T Black (T Red wl wk wv default 
            (tag_tree_t wrt wrl)) wrk (f wrv wrt) wt (tag_tree_t wrt wrr)))
        | _ => Empty
        end
      | _ => Empty
      end
    end
  end.

(* 杩欓噷鍖归厤棰滆壊鐩存帴纭紪鐮佷簡銆傝涓洪鑹插湪 Coq 涓殑琛ㄧず涓嶅彉銆�*)
Definition CaseTwo_sol (s : RBtree) (H : Half_tree) : RBtree :=
  match H with
  | (pb, pc, p, pv, pt, brother) =>
    match pb with
    | false => 
      match brother with
      | T Black wl wk wv wt wr => 
        match (get_color_tree wl), (get_color_tree wr) with
        | 0, 0 | -1, -1 =>
          (T pc s p pv pt (T Red wl wk wv wt wr))
        | _ ,_ => Empty
        end
      | _ => Empty
      end
    | true => 
      match brother with
      | T Black wl wk wv wt wr => 
        match get_color_tree wl, get_color_tree wr with
        | 0, 0 | -1, -1 =>
          (T pc (T Red wl wk wv wt wr) p pv pt s)
        | _ , _ => Empty
        end
      | _ => Empty
      end
    end
  end.

Definition CaseTTF_sol (s: RBtree) (H: Half_tree) : bool * RBtree :=
  (* 鐢ㄤ竴涓� bool 鎸囩ず鏄惁 break *)
  match H with
  | (pb, pc, p, pv, pt, brother) =>
    match pb with
    | false => 
      match brother with
      | T Black wl wk wv wt wr =>
        match (get_color_tree wl), (get_color_tree wr) with
        | 0, 0 | -1, -1 => (false, CaseTwo_sol s H)
        | 1, 0 | 1, -1 => (true, CaseThree_sol s H)
        | _, 1 => (true, CaseFour_sol s H)
        | _ , _ => (false, Empty)
        end
      | _ => (false, Empty)
      end
    | true => 
      match brother with
      | T Black wl wk wv wt wr =>
        match (get_color_tree wl), (get_color_tree wr) with
        | 0, 0 | -1, -1 => (false, CaseTwo_sol s H)
        | 0, 1 | -1, 1 => (true, CaseThree_sol s H)
        | 1, _ => (true, CaseFour_sol s H)
        | _ , _ => (false, Empty)
        end
      | _ => (false, Empty)
      end
    end
  end.

Definition CaseOne_sol (s : RBtree) (H : Half_tree) : 
  bool * RBtree * option Half_tree :=
  match H with
  | (pb, pc, p, pv, pt, brother) =>
    match pb with
    | false => 
      match brother with
      | T Red wl wk wv wt wr => 
      (* 杩欓噷瀵圭涓€娆� Case TTF 鐨勭粨鏋滃仛浜嗚璁� *)
        let (br, ts) := (CaseTTF_sol s (false, Red, p, pv, default, tag_tree_t wt wl)) in
        (match ts with
         | T Red _ _ _ _ _ => (br, ts, Some (false, Black, wk, f wv wt, pt, tag_tree_t wt wr))
         | _ => (CaseTTF_sol ts
             (false, Black, wk, f wv wt, pt, tag_tree_t wt wr), None)
         end)
      | _ => (false, Empty, None)
      end
    | true => match brother with
      | T Red wl wk wv wt wr => 
      (* 杩欓噷瀵圭涓€娆� Case TTF 鐨勭粨鏋滃仛浜嗚璁� *)
        let (br, ts) := (CaseTTF_sol s (true, Red, p, pv, default, tag_tree_t wt wr)) in
        (match ts with
         | T Red _ _ _ _ _ => (br, ts, Some (true, Black, wk, f wv wt, pt, tag_tree_t wt wl))
         | _ => (CaseTTF_sol ts
             (true, Black, wk, f wv wt, pt, tag_tree_t wt wl), None)
         end)
      | _ => (false, Empty, None)
      end
    end
  end.

Fixpoint delete_balance (s: RBtree) (h: list Half_tree) (ori_color: color) : RBtree * list Half_tree :=
  match ori_color with
  | Red => (s, h)
  | Black => 
    match h with
    | nil => (s, h) 
    | (pb, pc, p, pv, pt, brother) :: l' =>
      match s with
      | T Red sl sk sv st sr => (T Black sl sk sv st sr, h)
      | _  => (* 鍙岄粦 *)
        match brother with
        | Empty => (s, h) (* 涓嶅彲鑳戒负绌� *)
        | T Red wl wk wv wt wr => 
        (* 杩欓噷鍔犱簡涓€涓 Case one 缁撴灉鐨勮璁� *)
          match (CaseOne_sol s (pb, pc, p, pv, pt, brother)) with
          | (br, ts, None) => 
            match br with 
            | true => (ts, l')
            | false => delete_balance ts l' Black
            end
          | (br, ts, Some hft) => (makeBlack ts, hft :: l')
          end
        | T Black wl wk wv wt wr => 
          match (CaseTTF_sol s (pb, pc, p, pv, pt, brother)) with
          | (true, ts) => (ts, l')
          | (false, ts) => delete_balance ts l' Black
          end
        end
      end
    end
  end.

(* check function *)
Definition CaseFour_check (s :RBtree) (H : Half_tree) : bool :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |_  ,(T Red wrl wrk wrv wrt wrr) => true
              |_ , _ => false
              end
           | _ => false
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Red wll wlk wlv wlt wlr),_  => true
              |_ , _ => false
              end
           | _ => false
           end
   end
end.

Definition CaseThree_check (s :RBtree) (H : Half_tree) : bool :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Red wll wlk wlv wlt wlr), _ =>
     CaseFour_check s
   (false, pc, p, pv, pt, (T Black (tag_tree_t wlt wll) wlk (f wlv wlt) wt 
                                   (T Red (tag_tree_t wlt wlr) wk wv default wr)))
              |_ , _ => false
              end
           | _ => false
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |_ ,(T Red wrl wrk wrv wrt wrr) =>
     CaseFour_check s (true, pc, p, pv, pt, 
      (T Black (T Red wl wk wv default (tag_tree_t wrt wrl)) wrk (f wrv wrt) wt 
                                   (tag_tree_t wrt wrr)))
              |_ , _ => false
              end
           | _ => false
           end
   end
end.


Definition CaseTwo_check (s:RBtree) (H:Half_tree) : bool :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=> true
              |Empty , Empty => true
              |_ ,_ => false
              end
           | _ => false
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ ) => true
              |_ , _ => false
              end
           | _ => false
           end
   end
end.

Definition CaseTTF_check (s:RBtree) (H:Half_tree) : bool :=
match H with
|  (pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=> CaseTwo_check s H
              |Empty, Empty => CaseTwo_check s H
              |(T Red _ _ _ _ _ ), (T Black _ _ _ _ _ ) => CaseThree_check s H
              |(T Red _ _ _ _ _ ), Empty => CaseThree_check s H
              |_  ,(T Red wrl wrk wrv wrt wrr) => CaseFour_check s H
              |_ , _ => false
              end
           | _ => false
           end
   |true => match brother with
           |T Black wl wk wv wt wr => 
              match wl, wr with
              |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=> CaseTwo_check s H
              |(T Black _ _ _ _ _ ), (T Red _ _ _ _ _ ) => CaseThree_check s H
              |(T Red _ _ _ _ _ ) ,(T _ _ _ _ _ _) => CaseFour_check s H
              |_ , _ => false
              end
           | _ => false
           end
   end
end.

Definition CaseOne_check (s:RBtree) (H:Half_tree) : bool :=
match H with
|(pb, pc, p, pv, pt, brother) =>
   match pb with
   |false => match brother with
           |T Red wl wk wv wt wr => 
              (* 杩欓噷瀵圭涓€娆� Case TTF 鐨勭粨鏋滃仛浜嗚璁� *)
              (if (CaseTTF_check s (false, Red, p, pv, default, tag_tree_t wt wl))
              then
                (let ts := (CaseTTF_sol s (false, Red, p, pv, default, tag_tree_t wt wl)) in
                match ts with
                | T Red _ _ _ _ _ => true
                | _ => CaseTTF_check ts (false, Black, wk, f wv wt, pt, tag_tree_t wt wr)
                end)
              else false)
           | _ => false
           end
   |true => match brother with
           |T Red wl wk wv wt wr => 
              (* 杩欓噷瀵圭涓€娆� Case TTF 鐨勭粨鏋滃仛浜嗚璁� *)
              (if (CaseTTF_check s (true, Red, p, pv, default, tag_tree_t wt wr))
              then
                (let ts := (CaseTTF_sol s (true, Red, p, pv, default, tag_tree_t wt wr)) in
                match ts with
                | T Red _ _ _ _ _ => true
                | _ => CaseTTF_check ts (true, Black, wk, f wv wt, pt, tag_tree_t wt wl)
                end)
              else false)
           | _ => false
           end
   end
end.

Fixpoint delete_check (s: RBtree) (h: list Half_tree) (ori_color: color) : bool :=
match ori_color with
(** remove 鐐逛负绾㈣壊 涓嶅奖鍝嶇粨鏋�*)
|Red => true 
|Black => match h with
         |nil => true (** (makeBlack s, h)*)
         |(pb, pc, p, pv, pt, brother) :: l' =>
           match s with (**s 鏍圭粨鐐规湁涓€涓猠xtra black*)
           |T Red sl sk sv st sr => true
           |_  => (*鍙岄粦*)
              match brother with
              |Empty => false (*涓嶅彲鑳戒负绌�*)
              |T Red wl wk wv wt wr => 
              if CaseOne_check s (pb, pc, p, pv, pt, brother)
              then 
                (match (CaseOne_sol s (pb, pc, p, pv, pt, brother)) with
                | (None, res) => delete_check res l' Black
                | (Some hft, res) => true
                end)
              else false
              |T Black wl wk wv wt wr => 
              if CaseTTF_check s (pb, pc, p, pv, pt, brother)
              then delete_check
              (CaseTTF_sol s (pb, pc, p, pv, pt, brother)) l' Black
              else false
              end
           end
        end
end.

(*********************************************************************

Function Specifications

*********************************************************************)

(* mallocN *)
Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [ 1%positive OF tint ]
     PROP (4 <= n <= Int.max_unsigned)
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: val,
     PROP (malloc_compatible n v)
     LOCAL (temp ret_temp v)
     SEP (memory_block Tsh n v).

(* freeN *)
Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block Tsh n p)
  POST [ tvoid ]
    PROP () LOCAL () SEP ().

(* Optt *)
Definition Optt_spec :=
 DECLARE _Optt
  WITH t1 : Tag, t2 : Tag
  PRE [ _t1 OF tuint , _t2 OF tuint ]
    PROP () 
    LOCAL (temp _t1 (Vint (Int.repr t1)); 
          temp _t2 (Vint (Int.repr t2)))
    SEP ()
  POST [ tuint ]
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.repr (Optt t1 t2)))) 
     SEP ().

(* Opvt *)
Definition Opvt_spec :=
 DECLARE _Opvt
  WITH v_ : Value, t_ : Tag
  PRE [ _v OF tuint , _t OF tuint ]
    PROP () 
    LOCAL (temp _v (Vint (Int.repr v_));
          temp _t (Vint (Int.repr t_)))
    SEP ()
  POST [ tuint ]
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.repr (f v_ t_))))
     SEP ().

(* treebox_new *)
Definition treebox_new_spec :=
 DECLARE _treebox_new
  WITH u : unit
  PRE  [  ]
       PROP() LOCAL() SEP ()
  POST [ tptr (tptr t_struct_rbtree) ]
    EX v:val,
    PROP()
    LOCAL(temp ret_temp v)
    SEP (data_at Tsh (tptr t_struct_rbtree) nullval v).

(* tree_free *)
Definition tree_free_spec :=
 DECLARE _tree_free
  WITH t: RBtree, p: val, p_fa: val
  PRE  [ _p OF (tptr t_struct_rbtree) ]
    PROP() 
    LOCAL(temp _p p) 
    SEP (rbtree_rep t p p_fa)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (emp).

(* treebox_free *)
Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH t: RBtree, b: val
  PRE  [ _b OF (tptr (tptr t_struct_rbtree)) ]
       PROP() LOCAL(temp _b b) SEP (treeroot_rep t b)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (emp).

(* left_rotate *)
Definition left_rotate_spec :=
 DECLARE _left_rotate
  WITH 
    col_l: color, key_l: Key, value_l: Value, tag_l: Tag, fa_l: val, 
    col_r: color, key_r: Key, value_r: Value, tag_r: Tag,  
    ta: RBtree, tb: RBtree, tc: RBtree, 
    l: val, r: val, 
    pa: val
  PRE  [ _l OF (tptr t_struct_rbtree)]
    PROP (Int.min_signed <= key_l <= Int.max_signed; 
          is_pointer_or_null fa_l) 
    LOCAL (temp _l l) 
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (r, fa_l)))))) l;
          rbtree_rep ta pa l;
          rbtree_rep (T col_r tb key_r value_r tag_r tc) r l)
  POST [ tptr t_struct_rbtree ]
    EX pc: val, 
    PROP ()
    LOCAL (temp ret_temp r)
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (l, (pc, fa_l)))))) r;
          rbtree_rep tc pc r;
          rbtree_rep (T col_l ta key_l value_l tag_l tb) l r).

(* left_rotate_wrap *)
Definition left_rotate_wrap_spec :=
 DECLARE _left_rotate_wrap
  WITH 
    col_l: color, key_l: Key, value_l: Value, tag_l: Tag, fa_l: val, 
    col_r: color, key_r: Key, value_r: Value, tag_r: Tag,  
    ta: RBtree, tb: RBtree, tc: RBtree, 
    l: val, r: val, 
    pa: val, root : val, hft_list : list Half_tree
  PRE  [ _l OF (tptr t_struct_rbtree), _root OF tptr (tptr t_struct_rbtree) ]
    PROP (Int.min_signed <= key_l <= Int.max_signed; 
          is_pointer_or_null fa_l) 
    LOCAL (temp _l l; temp _root root) 
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (r, fa_l)))))) l;
          rbtree_rep ta pa l;
          rbtree_rep (T col_r tb key_r value_r tag_r tc) r l;
          partial_tree_rep hft_list root l fa_l)
  POST [ Tvoid ]
    EX pc: val, 
    PROP ()
    LOCAL ()
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (l, (pc, fa_l)))))) r;
          rbtree_rep tc pc r;
          rbtree_rep (T col_l ta key_l value_l tag_l tb) l r; 
          partial_tree_rep hft_list root r fa_l).

(* right_rotate *)
Definition right_rotate_spec :=
 DECLARE _right_rotate
  WITH 
    col_l: color, key_l: Key, value_l: Value, tag_l: Tag, 
    col_r: color, key_r: Key, value_r: Value, tag_r: Tag, fa_r: val, 
    ta: RBtree, tb: RBtree, tc: RBtree, 
    l: val, r: val, 
    pc: val
  PRE  [ _r OF (tptr t_struct_rbtree)]
    PROP (Int.min_signed <= key_r <= Int.max_signed;
          is_pointer_or_null fa_r)
    LOCAL (temp _r r) 
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (l, (pc, fa_r)))))) r;
          rbtree_rep tc pc r;
          rbtree_rep (T col_l ta key_l value_l tag_l tb) l r)
  POST [ tptr t_struct_rbtree ]
    EX pa: val, 
    PROP ()
    LOCAL (temp ret_temp l)
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (r, fa_r)))))) l;
          rbtree_rep ta pa l;
          rbtree_rep (T col_r tb key_r value_r tag_r tc) r l).

(* right_rotate_wrap *)
Definition right_rotate_wrap_spec :=
 DECLARE _right_rotate_wrap
  WITH 
    col_l: color, key_l: Key, value_l: Value, tag_l: Tag, 
    col_r: color, key_r: Key, value_r: Value, tag_r: Tag, fa_r: val, 
    ta: RBtree, tb: RBtree, tc: RBtree, 
    l: val, r: val, 
    pc: val, root : val, hft_list : list Half_tree
  PRE  [ _r OF (tptr t_struct_rbtree), _root OF tptr (tptr t_struct_rbtree)]
    PROP (Int.min_signed <= key_r <= Int.max_signed;
          is_pointer_or_null fa_r)
    LOCAL (temp _r r; temp _root root) 
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (l, (pc, fa_r)))))) r;
          rbtree_rep tc pc r;
          rbtree_rep (T col_l ta key_l value_l tag_l tb) l r; 
          partial_tree_rep hft_list root r fa_r)
  POST [ Tvoid ]
    EX pa: val, 
    PROP ()
    LOCAL ()
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (r, fa_r)))))) l;
          rbtree_rep ta pa l;
          rbtree_rep (T col_r tb key_r value_r tag_r tc) r l; 
          partial_tree_rep hft_list root l fa_r).

(* tag_tree_t *)
Definition tag_tree_t_spec :=
 DECLARE _tag_tree_t
  WITH t: RBtree, tag: Tag, x: val, x_fa: val
  PRE  [ _x OF tptr (Tstruct _tree noattr), _tag OF tuint ]
    PROP () 
    LOCAL (temp _x x; temp _tag (Vint (Int.repr tag))) 
    SEP (rbtree_rep t x x_fa)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (rbtree_rep (tag_tree_t tag t) x x_fa).

(* pushdown *)
Definition pushdown_spec :=
 DECLARE _pushdown
  WITH c : color, k : Key, v : Value, tg : Tag, 
    p_lch : val, p_rch : val, p_fa : val, p : val,
    t'1 : RBtree, t'2 : RBtree
  PRE  [ _p OF tptr t_struct_rbtree ]
    PROP () 
    LOCAL (temp _p p) 
    SEP (data_at Tsh t_struct_rbtree
          (Vint (Int.repr (Col2Z c)),
          (Vint (Int.repr k),
          (Vint (Int.repr v),
          (Vint (Int.repr tg),
          (p_lch, (p_rch, p_fa)))))) p;
        rbtree_rep t'1 p_lch p;
        rbtree_rep t'2 p_rch p)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (data_at Tsh t_struct_rbtree
          (Vint (Int.repr (Col2Z c)),
          (Vint (Int.repr k),
          (Vint (Int.repr (v + tg)),
          (Vint (Int.repr default),
          (p_lch, (p_rch, p_fa)))))) p;
        rbtree_rep (tag_tree_t tg t'1) p_lch p;
        rbtree_rep (tag_tree_t tg t'2) p_rch p).

(* make_black *)
Definition make_black_spec :=
 DECLARE _make_black
  WITH t: RBtree, root: val
  PRE  [ _root OF (tptr (tptr t_struct_rbtree)) ]
    PROP () 
    LOCAL (temp _root root) 
    SEP (treebox_rep t root nullval)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (treebox_rep (makeBlack t) root nullval). 

(* get_color *)
Definition get_color_spec :=
 DECLARE _get_color
  WITH t: RBtree, x: val, t_fa: val
  PRE  [ _p OF tptr t_struct_rbtree ]
    PROP () 
    LOCAL (temp _p x) 
    SEP (rbtree_rep t x t_fa)
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (get_color_tree t))))
    SEP (rbtree_rep t x t_fa). 

(* update *)
Definition update_spec :=
  DECLARE _update
  WITH root: val, t: RBtree, tg: Tag, targ_lo: Key, targ_hi: Key
  PRE  [ _root OF tptr (tptr (Tstruct _tree noattr)), _tg OF tuint, 
          _targ_l OF tint, _targ_r OF tint ]
    PROP (Int.min_signed <= targ_lo <= Int.max_signed;
          Int.min_signed <= targ_hi <= Int.max_signed) 
    LOCAL (temp _root root; temp _tg (Vint (Int.repr tg)); 
            temp _targ_l (Vint (Int.repr targ_lo));
            temp _targ_r (Vint (Int.repr targ_hi))) 
    SEP (treeroot_rep t root)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (treeroot_rep (change_segment targ_lo targ_hi tg t) root). 

(* update_aux *)
Definition update_aux_spec :=
  DECLARE _update_aux
  WITH p: val, p_fa: val, t: RBtree, tg: Tag, targ_lo: Key, targ_hi: Key, 
    lo: Key, hi: Key
  PRE  [ _t OF tptr (Tstruct _tree noattr), _tg OF tuint, 
          _l OF tint, _r OF tint, _targ_l OF tint, _targ_r OF tint ]
    PROP (Int.min_signed <= targ_lo <= Int.max_signed;
          Int.min_signed <= targ_hi <= Int.max_signed; 
          Int.min_signed <= lo <= Int.max_signed;
          Int.min_signed <= hi <= Int.max_signed) 
    LOCAL (temp _t p; temp _tg (Vint (Int.repr tg)); 
            temp _l (Vint (Int.repr lo));
            temp _r (Vint (Int.repr hi));
            temp _targ_l (Vint (Int.repr targ_lo));
            temp _targ_r (Vint (Int.repr targ_hi))) 
    SEP (rbtree_rep t p p_fa)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (rbtree_rep (change_segment' targ_lo targ_hi tg t lo hi) p p_fa).

(* tree_minimum *)
Definition tree_minimum_spec :=
 DECLARE _tree_minimum
  WITH t_tree: RBtree, b: val, p_fa: val, 
    hft_list : list Half_tree, root : val
  PRE  [ _t OF tptr (tptr t_struct_rbtree) ]
    PROP (t_tree <> Empty) 
    LOCAL (temp _t b) 
    SEP (treebox_rep t_tree b p_fa; 
      partial_treebox_rep hft_list root b p_fa)
  POST [ tptr (tptr t_struct_rbtree) ]
    EX min_b : val, EX min_tree : RBtree,
    EX min_p_fa : val, EX min_hft_list : list Half_tree,
    PROP (Up_split (minimum_split default t_tree hft_list) =
       (min_hft_list, min_tree))
    LOCAL (temp ret_temp min_b)
    SEP (treebox_rep min_tree min_b min_p_fa; 
      partial_treebox_rep min_hft_list root min_b min_p_fa). 

(*****************涓嬮潰寮€濮嬫渶閲嶈鐨勫嚑涓姛鑳藉嚱鏁扮殑瀹氫箟****************)

(* solve_double_red *)
Definition solve_double_red_spec :=
  DECLARE _solve_double_red
  WITH t_initial: RBtree, 
      root: val,    (* real root *)
      p_fa_initial: val,    
      b_initial: val, 
      hft_list_initial: list Half_tree
  PRE  [ _t OF tptr (tptr t_struct_rbtree), 
      _root OF tptr (tptr t_struct_rbtree) ]
    PROP (t_initial <> Empty)    (* 鐩存帴鍔犱笂杩欎竴鏉′細涓嶄細鏈変簺鏆村姏锛� *) 
    LOCAL (temp _t b_initial; temp _root root) 
    SEP (treebox_rep t_initial b_initial p_fa_initial; 
      partial_treebox_rep hft_list_initial root b_initial p_fa_initial)
  POST [ Tvoid ]
    EX t_balanced: RBtree, 
    EX hft_list_balanced: list Half_tree, 
    EX b_balanced: val, 
    EX p_balanced: val,
    PROP ((hft_list_balanced, t_balanced) = balance' hft_list_initial t_initial)
    LOCAL ()
    SEP (treebox_rep t_balanced b_balanced p_balanced; 
        partial_treebox_rep hft_list_balanced root b_balanced p_balanced).

(* solve_double_black *)
Definition solve_double_black_spec :=
  DECLARE _solve_double_black
  WITH t_initial: RBtree, 
      root: val,    (* real root *)
      p_initial : val, p_fa_initial : val,
      b_initial: val, 
      hft_list_initial: list Half_tree
  PRE  [ _p OF (tptr t_struct_rbtree), 
      _p_fa OF (tptr t_struct_rbtree),
      _root OF tptr (tptr t_struct_rbtree) ]
    PROP (delete_check t_initial hft_list_initial Black = true)    
    LOCAL (temp _p p_initial; temp _p_fa p_fa_initial; temp _root root) 
    SEP (rbtree_rep t_initial p_initial p_fa_initial;
      data_at Tsh (tptr t_struct_rbtree) p_initial b_initial;
      partial_treebox_rep hft_list_initial root b_initial p_fa_initial)
  POST [ Tvoid ]
    EX t_balanced: RBtree, 
    EX hft_list_balanced: list Half_tree, 
    EX b_balanced: val, 
    EX p_balanced: val,
    PROP ((t_balanced, hft_list_balanced) = 
      delete_balance t_initial hft_list_initial Black)
    LOCAL ()
    SEP (treebox_rep t_balanced b_balanced p_balanced; 
        partial_treebox_rep hft_list_balanced root b_balanced p_balanced).

(* insert *)
Definition insert_spec :=
 DECLARE _insert
  WITH t_tree: RBtree, x: Key, v: Value, b: val
  PRE  [ _t OF tptr (tptr t_struct_rbtree), _x OF tint, 
          _value OF tuint ]
    PROP (Int.min_signed <= x <= Int.max_signed) 
    LOCAL (temp _t b; temp _x (Vint (Int.repr x)); 
          temp _value (Vint (Int.repr v)))
    SEP (treeroot_rep t_tree b)
  POST [ Tvoid ]
    EX t_complete : RBtree, 
    PROP (another_insert x v t_tree t_complete)
    LOCAL ()
    SEP (treeroot_rep t_complete b).

(* delete *)
Definition delete_spec :=
 DECLARE _delete
  WITH t_tree: RBtree, x: Key, v: Value, b: val
  PRE  [ _t OF tptr (tptr t_struct_rbtree), _x OF tint ]
    PROP (Int.min_signed <= x <= Int.max_signed) 
    LOCAL (temp _t b; temp _x (Vint (Int.repr x)))
    SEP (treeroot_rep t_tree b)
  POST [ Tvoid ]
    EX t_complete : RBtree, 
    PROP ()
    LOCAL ()
    SEP (treeroot_rep (delete x t_tree) b).

(* lookup *)
(* TODO: Ill-defined. Fix it. *)
Definition lookup_spec :=
 DECLARE _lookup
  WITH x: Z, b: val, t: RBtree
  PRE  [ _t OF (tptr (tptr t_struct_rbtree)), _x OF tint ]
    PROP (Int.min_signed <= x <= Int.max_signed) 
    LOCAL (temp _t b; temp _x (Vint (Int.repr x))) 
    SEP (treeroot_rep t b)
  POST [ tuint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (Lookup2Z x t))))
    SEP (treeroot_rep t b).

(* all functions of the program *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [
    mallocN_spec;           (* vacuous truth! *)
    freeN_spec;             (* vacuous truth! *)
    Optt_spec;              (* OK! *)
    Opvt_spec;              (* OK! *)
    treebox_new_spec;       (* OK! *)
    tree_free_spec;         (* OK! *)
    treebox_free_spec;      (* OK! *)
    left_rotate_spec;       (* OK! *)
    right_rotate_spec;      (* OK! *)
    left_rotate_wrap_spec;  (* OK! *)
    right_rotate_wrap_spec; (* OK! *)
    tag_tree_t_spec;        (* OK! *)
    insert_spec;            (* OK! *)
    make_black_spec;        (* OK! *)
    get_color_spec;         (* OK! *)
    solve_double_red_spec;  (* OK! *)
    lookup_spec;            (* need extension *)
    update_aux_spec;        (* OK! *)
    update_spec;            (* OK! *)
    pushdown_spec;          (* OK! *)
    tree_minimum_spec;
    solve_double_black_spec;
    delete_spec
  ]).

(*********************************************************************

Proofs for Specifications

*********************************************************************)

(* 琛ㄦ槑瀛樻斁浜嗘爲鐨勪綅缃竴瀹氭槸涓€涓寚閽� *)
Lemma rbtree_rep_saturate_local:
   forall t p p_fa, rbtree_rep t p p_fa |-- !! is_pointer_or_null p.
Proof.
  destruct t; simpl; intros.
  entailer!.
  Intros pa pb. entailer!.
Qed.
Hint Resolve rbtree_rep_saturate_local: saturate_local.

(* TODO: Not sure whether this is necessary *)
Lemma rbtree_rep_saturate_local_father:
   forall t p p_fa, rbtree_rep t p p_fa |-- !! is_pointer_or_null p_fa.
Proof.
  destruct t; simpl; intros.
  entailer!.
  Intros pa pb. entailer!.
Qed.
Hint Resolve rbtree_rep_saturate_local: saturate_local.

Lemma rbtree_rep_valid_pointer:
  forall t p p_fa, rbtree_rep t p p_fa |-- valid_pointer p.
Proof.
  intros.
  destruct t. 
  - simpl. entailer!. (* 杩囦簬涓囪兘 *)
  - simpl; normalize; auto with valid_pointer.
Qed.
Hint Resolve rbtree_rep_valid_pointer: valid_pointer.

(* TODO: seems not helpful *)
Lemma rbtree_rep_nullval : forall (t: RBtree) p, 
  rbtree_rep t nullval p |-- !!(t = empty_tree).
Proof.
  intros. 
  destruct t.
  - simpl. entailer!.
  - simpl rbtree_rep. Intros. Intros p_lch p_rch.
    entailer!. 
Qed.

Lemma treeroot_rep_saturate_local:
  forall t b, treeroot_rep t b |-- 
    !! field_compatible (tptr t_struct_rbtree) [] b.
Proof.
  intros.
  unfold treeroot_rep.
  Intros p.
  entailer!.
Qed.
Hint Resolve treeroot_rep_saturate_local: saturate_local.

Lemma treebox_rep_saturate_local:
  forall t b p_fa, treebox_rep t b p_fa |-- 
    !! field_compatible (tptr t_struct_rbtree) [] b.
Proof.
  intros.
  unfold treebox_rep.
  Intros p.
  entailer!.
Qed.
Hint Resolve treebox_rep_saturate_local: saturate_local.

Lemma treebox_rep_saturate_local':
   forall t b p_fa, treebox_rep t b p_fa |-- !! is_pointer_or_null b.
Proof.
  intros.
  unfold treebox_rep.
  Intros p.
  entailer!.
Qed.
Hint Resolve treebox_rep_saturate_local': saturate_local.

Lemma treebox_rep_valid_pointer:
   forall t b p_fa, treebox_rep t b p_fa |-- valid_pointer b.
Proof.
  intros.
  unfold treebox_rep.
  Intros p.
  entailer!.
Qed.
Hint Resolve treebox_rep_valid_pointer: valid_pointer.

(* saturate DB for partial_tree_rep *)
Lemma partial_tree_rep_saturate_local_father:
  forall hft_list root p p_fa, 
    partial_tree_rep hft_list root p p_fa |-- 
      !! is_pointer_or_null p_fa.
Proof.
  intros.
  destruct hft_list.
  - simpl. entailer!.
  - destruct h as [[[[[vacancy col] key_] value_] tag_] opposite].
    destruct vacancy; simpl; normalize; auto with valid_pointer; entailer!.
Qed.
Hint Resolve partial_tree_rep_saturate_local_father: saturate_local.

Lemma partial_tree_rep_valid_pointer_father:
  forall hft_list root p p_fa, 
    partial_tree_rep hft_list root p p_fa |-- valid_pointer p_fa.
Proof.
  intros.
  destruct hft_list.
  - simpl. entailer!.
  - destruct h as [[[[[vacancy col] key_] value_] tag_] opposite].
    destruct vacancy; simpl; normalize; auto with valid_pointer; entailer!.
Qed.
Hint Resolve partial_tree_rep_valid_pointer_father: valid_pointer.

(* saturate DB for partial_treebox_rep *)
Lemma partial_treebox_rep_saturate_local_father:
  forall hft_list root b p_fa, 
    partial_treebox_rep hft_list root b p_fa |-- 
      !! is_pointer_or_null p_fa.
Proof.
  intros.
  destruct hft_list.
  - simpl. entailer!.
  - destruct hft_list; destruct h as [[[[[vacancy col] key_] value_] tag_] opposite];
    destruct vacancy; simpl; normalize; auto with valid_pointer; entailer!.
Qed.
Hint Resolve partial_treebox_rep_saturate_local_father: saturate_local.

Lemma partial_treebox_rep_valid_pointer_father:
  forall hft_list root b p,
    partial_treebox_rep hft_list root b p |-- valid_pointer p.
Proof.
  intros.
  destruct hft_list.
  - simpl partial_treebox_rep. entailer!.
  - destruct h as [[[[[vacancy col] key_] value_] tag_] ch].
    simpl.
    destruct vacancy; Intros p_fa p_lch b_fa; Intros;
      rewrite field_at_data_at'. entailer!. entailer!.
Qed.
Hint Resolve partial_treebox_rep_valid_pointer_father: valid_pointer.

(* only useful in the definition here. *)
Lemma field_color_valid_pointer:
  forall c p, 
    field_at Tsh t_struct_rbtree [StructField _color] (Vint (Int.repr (Col2Z c))) p
    |-- valid_pointer p.
Proof.
  intros.
  rewrite field_at_data_at'.
  entailer!.
Qed.
Hint Resolve field_color_valid_pointer: valid_pointer.

(* TODO: seems not useful *)
Lemma andp_eliminate:
  forall (A : Type) (NA : NatDed A) (P Q Q' : A),
  Q |-- Q' -> P && Q |-- P && Q'.
Proof.
  intros.
  apply andp_derives.
  - apply derives_refl.
  - apply H.
Qed.

Lemma general_split_tag :  
  forall t lbool rbool t_tree hft_list, 
  general_split lbool rbool t t_tree hft_list =
  general_split lbool rbool default (tag_tree_t t t_tree) hft_list.  
Proof.
  intros. 
  destruct t_tree.
  - simpl. reflexivity.
  - simpl.
    destruct lbool eqn:E.
    + do 5 f_equal.
      lia.
    + destruct rbool eqn:E'.
      * do 5 f_equal. lia.
      * do 5 f_equal.
Qed.

Lemma partial_tree_rep_father_not_null:
  forall hft_list root p0, 
    partial_tree_rep hft_list root p0 nullval |-- !! (hft_list = []).
Proof.
  intros.
  destruct hft_list.
  - entailer!.
  - destruct h as [[[[[vacancy col] key_] value_] tag_] opposite].
    simpl partial_tree_rep.
    destruct vacancy.
    + Intros p_gfa p_opposite.
      entailer!.
    + Intros p_gfa p_opposite.
      entailer!.
Qed.

(* several lemmas about colors *)
Lemma col_not_0: forall col, Int.repr (Col2Z col) <> Int.repr 0 -> col = Red.
Proof.
  intros.
  destruct col.
  - reflexivity. 
  - exfalso. apply H. reflexivity. 
Qed.

Lemma col_not_1: forall col, Int.repr (Col2Z col) <> Int.repr 1 -> col = Black.
Proof.
  intros.
  destruct col.
  - exfalso. apply H. reflexivity. 
  - reflexivity. 
Qed.

Lemma col_is_black: forall col, Int.repr (Col2Z col) = Int.repr 0 -> col = Black.
Proof.
  intros.
  destruct col.
  - discriminate.
  - reflexivity.
Qed.

Lemma col_is_red: forall col, Int.repr (Col2Z col) = Int.repr 1 -> col = Red.
Proof.
  intros.
  destruct col.
  - reflexivity.
  - discriminate.
Qed.

(* used to determine color and to substitution *)
Ltac color_replace :=
  match goal with
  | x : Int.repr (Col2Z ?c) = Int.repr 0 |- _ => 
    try (apply col_is_black in x; subst c)
  | x : Int.repr (Col2Z ?c) = Int.repr 1 |- _ => 
    try (apply col_is_red in x; subst c)
  | x : Int.repr (Col2Z ?c) <> Int.repr 0 |- _ =>
    try (apply col_not_0 in x; subst c)
  | x : Int.repr (Col2Z ?c) <> Int.repr 1 |- _ =>
    try (apply col_not_1 in x; subst c)
  end.

Local Open Scope logic.

(* TODO: it looks bad. *)
Lemma insert_lemma : forall hft_list_balanced t_balanced (p p' b b' : val), 
  data_at Tsh (tptr t_struct_rbtree) p b' * rbtree_rep t_balanced p p' *
    partial_treebox_rep hft_list_balanced b b' p'
  |-- treebox_rep (complete_tree hft_list_balanced t_balanced) b nullval.
Proof.
  intros hft_list_balanced.
  induction hft_list_balanced.
  - intros. 
    simpl.
    Intros.
    unfold treebox_rep.
    Exists p.
    subst p'. subst b.
    entailer!.
  - intros. 
    destruct a as [[[[[vacancy col] key] value] tag] opposite].
    simpl partial_treebox_rep.
    Intros p_fa0 p_oppo b_fa.
    pose proof (IHhft_list_balanced (T col 
      (if vacancy then opposite else t_balanced) 
        key value tag (if vacancy then t_balanced else opposite))
      p' p_fa0 b b_fa).
    clear IHhft_list_balanced.
    apply derives_trans with (Q:=
      (data_at Tsh (tptr t_struct_rbtree) p' b_fa *
      rbtree_rep (T col (if vacancy then opposite else t_balanced) 
        key value tag (if vacancy then t_balanced else opposite)) p' p_fa0 *
      partial_treebox_rep hft_list_balanced b b_fa p_fa0)).
    {
      simpl rbtree_rep.
      Exists (if vacancy then p_oppo else p) (if vacancy then p else p_oppo).
      unfold_data_at (data_at _ _ _ p').
      destruct vacancy; Intros; entailer!.
    }
    {
      sep_apply H.
      destruct vacancy; simpl complete_tree; 
      apply derives_refl.
    }
Qed.

Lemma insert_lemma' : forall hft_list_balanced t_balanced (p' b b' : val), 
  treebox_rep t_balanced b' p' *
    partial_treebox_rep hft_list_balanced b b' p'
  |-- treeroot_rep (complete_tree hft_list_balanced t_balanced) b.
Proof.
  intros.
  unfold treebox_rep.
  Intros p0.
  sep_apply insert_lemma.
  unfold treebox_rep, treeroot_rep.
  Intros p1. Exists p1.
  entailer!.
Qed.

Lemma partialtreebox_partialtree : forall hft_list p b root p_fa,
  data_at Tsh (tptr t_struct_rbtree) p b *
  partial_treebox_rep hft_list root b p_fa
  |-- partial_tree_rep hft_list root p p_fa.
Proof.
  intros hft_list.
  induction hft_list.
  - intros. simpl. entailer.
  - intros. destruct a as [[[[[? ?] ?] ?] ?] ?].
    simpl.
    destruct b0.
    + Intros p_fa0 p_lch b_fa.
      Exists p_fa0 p_lch.
      unfold_data_at (data_at _ _ _ p_fa).
      entailer!. 
      sep_apply IHhft_list.
      apply derives_refl.
    + Intros p_fa0 p_rch b_fa.
      Exists p_fa0 p_rch.
      unfold_data_at (data_at _ _ _ p_fa).
      entailer!.
      sep_apply IHhft_list.
      apply derives_refl.
Qed.

Lemma partialtree_partialtreebox : forall hft_list p root p_fa,
  partial_tree_rep hft_list root p p_fa
  |-- EX b, data_at Tsh (tptr t_struct_rbtree) p b *
    partial_treebox_rep hft_list root b p_fa.
Proof.
  intros hft_list.
  induction hft_list.
  - intros. simpl. 
    Exists root.
    entailer!.
  - intros. destruct a as [[[[[? ?] ?] ?] ?] ?].
    simpl.
    destruct b.
    + Intros p_gfa p_fa_lch.
      Exists (field_address t_struct_rbtree [StructField _right] p_fa).
      Exists p_gfa p_fa_lch.
      sep_apply IHhft_list.
      Intros b_fa. Exists b_fa. 
      unfold_data_at (data_at _ _ _ p_fa).
      entailer!.
    + Intros p_gfa p_fa_rch.
      Exists (field_address t_struct_rbtree [StructField _left] p_fa).
      Exists p_gfa p_fa_rch.
      sep_apply IHhft_list.
      Intros b_fa. Exists b_fa. 
      unfold_data_at (data_at _ _ _ p_fa).
      entailer!.
Qed.

Fact silly_fact: forall (b : bool), (if b then Empty else Empty) = Empty.
Proof. destruct b; simpl; reflexivity. Qed.

Lemma change_empty : forall lo hi delta slo shi,
  change_segment' lo hi delta Empty slo shi = Empty.
Proof.
  intros. simpl.
  destruct (hi <? slo); destruct (shi <? lo); simpl; try reflexivity.
  apply silly_fact.
Qed.

Ltac strip_0 := 
  rewrite Z.add_0_l in *; rewrite Z.add_0_r in *.

Ltac arith_bool :=
  repeat match goal with
  | x: ?a >= ?b |- _  => 
    rewrite Z.ge_le_iff in x; rewrite <- Z.ltb_ge in x
  | x: ?a < ?b  |- _  => rewrite Zlt_is_lt_bool in x
  end.
  
Lemma arith_bool_1 : forall a b, 
  (if a <? b then true else a =? b) = (a <=? b).
Proof.
  intros.
  destruct (a <=? b) eqn:E.
  - rewrite Z.leb_le in E.
    destruct (a <? b) eqn:E'.
    + reflexivity.
    + assert (a = b).
      { rewrite Z.ltb_ge in E'. lia. }
      rewrite H. apply Z.eqb_refl.
  - rewrite Z.leb_gt in E. 
    destruct (a <? b) eqn:E'.
    + rewrite Z.ltb_lt in E'. lia. 
    + destruct (a =? b) eqn:E''.
      * rewrite Z.eqb_eq in E''. 
        rewrite E'' in E. lia.
      * reflexivity.
Qed.

Lemma zlt_bool_1 : forall a b, 
  (a <? b) = (if zlt a b then true else false).
Proof.
  intros.
  destruct (a <? b) eqn:E.
  - rewrite zlt_true.
    + reflexivity.
    + rewrite <- Z.ltb_lt. exact E.
  - rewrite zlt_false.
    + reflexivity.
    + rewrite Z.ge_le_iff. rewrite <- Z.ltb_ge. exact E.
Qed.

(* proof for treebox_new *)
(* copied from verif_bst.v *)
Theorem body_treebox_new: semax_body Vprog Gprog f_treebox_new treebox_new_spec.
Proof.
  start_function.
  forward_call (sizeof (tptr t_struct_rbtree)).
  { simpl sizeof; computable. }
  Intros p.
  rewrite memory_block_data_at_ by auto.
  forward.
  forward.
  Exists p. entailer!.
Qed.

Local Open Scope logic.

Lemma saturate_local_or:
  forall (b : bool) p1 p2, 
  !! (is_pointer_or_null p1) && !! (is_pointer_or_null p2)
  |-- !! (is_pointer_or_null (if b then p1 else p2)).
Proof.
  intros.
  destruct b; entailer.  
Qed.
Hint Resolve saturate_local_or: saturate_local.

Lemma tc_val_or:
  forall (b : bool) p1 p2 ty, 
  !! (tc_val ty p1) && !! (tc_val ty p2)
  |-- !! (tc_val ty (if b then p1 else p2)).
Proof.
  intros.
  destruct b; entailer.  
Qed.
Hint Resolve tc_val_or: saturate_local.

Lemma valid_pointer_or:
  forall (b : bool) p1 p2, 
    valid_pointer p1 * valid_pointer p2 
    |-- valid_pointer (if b then p1 else p2).
Proof.
  intros.
  destruct b; entailer. 
Qed.
Hint Resolve valid_pointer_or: valid_pointer.

(* TODO: may not be useful *)
Lemma data_at_nullval : forall h, 
  data_at Tsh t_struct_rbtree h nullval |-- !! False.
Proof.
  intros.
  entailer!.
Qed.

Lemma delete_balance_red : forall t l, 
  delete_balance t l Red = (t, l).
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma delete_lemma : forall hft_list b b0 p_fa,
  partial_treebox_rep hft_list b b0 p_fa *
  data_at Tsh (tptr t_struct_rbtree) nullval b0
  |-- treeroot_rep (complete_tree hft_list Empty) b.
Proof.
  intros.
  pose proof (insert_lemma hft_list Empty).
  specialize (H nullval p_fa b b0).
  unfold treeroot_rep, treebox_rep in *.
  eapply derives_trans; [ | apply H].
  simpl rbtree_rep.
  entailer!.
Qed.

(* help simplify match expression *)
Lemma delete_balance_t_color : forall t va_f c_f k_f v_f tg_f oppo l,
  get_color_tree t <> Col2Z Red -> 
  delete_balance t ((va_f, c_f, k_f, v_f, tg_f, oppo) :: l) Black =
  match oppo with
  | Empty => (t, ((va_f, c_f, k_f, v_f, tg_f, oppo) :: l))
  | T Red wl wk wv wt wr => 
    match (CaseOne_sol t (va_f, c_f, k_f, v_f, tg_f, oppo)) with
    | (None, res) => delete_balance res l Black
    | (Some hft, res) => (makeBlack res, hft :: l)
    end
  | T Black wl wk wv wt wr => delete_balance 
    (CaseTTF_sol t (va_f, c_f, k_f, v_f, tg_f, oppo)) l Black
  end.
Proof.
  intros.
  destruct t; [ reflexivity | ].
  destruct c; [ simpl in H; contradiction | reflexivity ].
Qed.

Lemma match_color : forall {A : Type} (t : RBtree) (res1 res2 : A), 
  get_color_tree t <> Col2Z Red -> 
  match t with
  | T Red _ _ _ _ _ => res1
  | _ => res2
  end = res2.
Proof.
  intros.
  destruct t; [ reflexivity | ].
  destruct c; [ simpl in H; contradiction | reflexivity ].
Qed.

Lemma case2_solve_not_null : forall t hft,
  CaseTwo_check t hft = true ->
  CaseTwo_sol t hft <> Empty.
Proof.
  intros.
  destruct hft as [[[[[va_f c_f] k_f] v_f] tg_f] oppo].
  simpl in H.
  destruct va_f.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo2; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    simpl CaseTwo_sol.
    intro; discriminate.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1.
    * destruct oppo2; [ | simpl in H; discriminate ].
      simpl CaseTwo_sol.
      intro; discriminate.
    * destruct c; [ simpl in H; discriminate | ].
      destruct oppo2; [ simpl in H; discriminate | ].
      destruct c; [ simpl in H; discriminate | ].
      simpl CaseTwo_sol.
      intro; discriminate.
Qed.

Lemma case3_solve_not_null : forall t hft,
  CaseThree_check t hft = true ->
  CaseThree_sol t hft <> Empty.
Proof.
  intros.
  destruct hft as [[[[[va_f c_f] k_f] v_f] tg_f] oppo].
  simpl in H.
  destruct va_f.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo2; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    simpl CaseThree_sol.
    intro; discriminate.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1; [ simpl in H; discriminate | ].
    destruct c; [ | simpl in H; discriminate ].
    simpl CaseThree_sol.
    intro; discriminate.
Qed.

Lemma case4_solve_not_null : forall t hft,
  CaseFour_check t hft = true ->
  CaseFour_sol t hft <> Empty.
Proof.
  intros.
  destruct hft as [[[[[va_f c_f] k_f] v_f] tg_f] oppo].
  simpl in H.
  destruct va_f.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1; [ simpl in H; discriminate | ].
    destruct c; [ | simpl in H; discriminate ].
    simpl CaseFour_sol.
    intro; discriminate.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo2; [ simpl in H; discriminate | ].
    destruct c; [ | simpl in H; discriminate ].
    simpl CaseFour_sol.
    intro; discriminate.
Qed.

Lemma case_solve_not_null : forall t hft, 
  get_color_tree t <> Col2Z Red ->
  CaseTTF_check t hft = true ->
  CaseTTF_sol t hft <> Empty.
Proof.
  intros.
  destruct hft as [[[[[va_f c_f] k_f] v_f] tg_f] oppo].
  unfold CaseTTF_check in H0.
  unfold CaseTTF_sol.
  destruct va_f.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1; [ simpl in H; discriminate | ].
    destruct c.
    * destruct oppo2; [ simpl in H; discriminate | ].
      apply (case4_solve_not_null _ _ H0).
    * destruct oppo2; [ simpl in H; discriminate | ].
      destruct c.
      - apply (case3_solve_not_null _ _ H0).
      - apply (case2_solve_not_null _ _ H0).
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1.
    * destruct oppo2; [ simpl in H; discriminate | ].
      destruct c; [ | simpl in H; discriminate ].
      apply (case4_solve_not_null _ _ H0).
    * destruct c.
      - destruct oppo2; [ apply (case4_solve_not_null _ _ H0) | ].
        destruct c; [ apply (case4_solve_not_null _ _ H0) | ].
        apply (case3_solve_not_null _ _ H0).
      - destruct oppo2; [ simpl in H; discriminate | ].
        destruct c; [ apply (case4_solve_not_null _ _ H0) | ].
        apply (case2_solve_not_null _ _ H0).
Qed.

(* TODO锛氬姹傛洿楂樼殑鑷姩鍖栨柟娉曟潵瑙ｅ喅杩欎竴闂銆�*)
Lemma if_else_then_true : forall (b res : bool), 
  (if b then res else false) = true <-> b = true /\ res = true.
Proof.
  intros. split; intros. 
  - destruct b.
    + tauto. 
    + discriminate.
  - destruct H.
    rewrite H.
    exact H0.
Qed. 

(* TODO锛氳繖涓緢绠€鍗曪紝浣嗕负鍟ヨ繖涔堥暱 *)
Lemma case_one_true : forall s pb pc p pv pt wc wl wk wv wt wr, 
  get_color_tree s <> Col2Z Red ->
  CaseOne_check s (pb, pc, p, pv, pt, T wc wl wk wv wt wr) = true ->
  (get_color_tree 
    (CaseTTF_sol s (pb, Red, p, pv, default, tag_tree_t wt (if pb then wr else wl))) 
    = Col2Z Red /\
    CaseOne_sol s (pb, pc, p, pv, pt, T wc wl wk wv wt wr) = 
      (Some (pb, Black, wk, f wv wt, pt, tag_tree_t wt (if pb then wl else wr)), 
        (CaseTTF_sol s (pb, Red, p, pv, default, tag_tree_t wt (if pb then wr else wl))))) \/
  (CaseTTF_check 
    (CaseTTF_sol s (pb, Red, p, pv, default, tag_tree_t wt (if pb then wr else wl))) 
    (pb, Black, wk, f wv wt, pt, tag_tree_t wt (if pb then wl else wr)) = true /\
    get_color_tree (tag_tree_t wt (if pb then wl else wr)) = Col2Z Black /\
    get_color_tree 
    (CaseTTF_sol s (pb, Red, p, pv, default, tag_tree_t wt (if pb then wr else wl))) 
    = Col2Z Black /\
      CaseOne_sol s (pb, pc, p, pv, pt, T wc wl wk wv wt wr) = 
        (None, CaseTTF_sol (CaseTTF_sol s (pb, Red, p, pv, default, tag_tree_t wt (if pb then wr else wl)))
          (pb, Black, wk, f wv wt, pt, tag_tree_t wt (if pb then wl else wr)))).
Proof.
  intros. unfold CaseOne_check in H0.
  destruct pb.
  - destruct wc; [ | discriminate ].
    rewrite if_else_then_true in H0.
    destruct H0 as [H0_copy H0].
    remember (CaseTTF_sol s (true, Red, p, pv, default, tag_tree_t wt wr)) as ts.
    destruct ts.
    + apply case_solve_not_null in H0_copy; [ | assumption ].
      rewrite <- Heqts in H0_copy.
      contradiction.
    + destruct c.
      * left. split.
        --  reflexivity.
        --  unfold CaseOne_sol. rewrite <- Heqts.
            reflexivity. 
      * right. split; [ exact H0 | ]. 
        destruct wl; [ simpl in H0; discriminate | ].
        destruct c; [ simpl in H0; discriminate | ].
        do 2 split; [ reflexivity | ].
        unfold CaseOne_sol. rewrite <- Heqts.
        reflexivity. 
  - destruct wc; [ | discriminate ].
    rewrite if_else_then_true in H0.
    destruct H0 as [H0_copy H0].
    remember (CaseTTF_sol s (false, Red, p, pv, default, tag_tree_t wt wl)) as ts.
    destruct ts.
    + apply case_solve_not_null in H0_copy; [ | assumption ].
      rewrite <- Heqts in H0_copy.
      contradiction.
    + destruct c.
      * left. split.
        --  reflexivity.
        --  unfold CaseOne_sol. rewrite <- Heqts.
            reflexivity. 
      * right. split; [ exact H0 | ]. 
        destruct wr; [ simpl in H0; discriminate | ].
        destruct c; [ simpl in H0; discriminate | ].
        do 2 split; [ reflexivity | ].
        unfold CaseOne_sol. rewrite <- Heqts.
        reflexivity. 
Qed.

Theorem body_solve_double_black: 
  semax_body Vprog Gprog f_solve_double_black solve_double_black_spec.
Proof. 
  start_function.
  forward_loop
  (EX t : RBtree, 
  EX hft_list : list Half_tree, 
  EX p : val, 
  EX p_fa : val,
  PROP (delete_check t hft_list Black = true /\
    delete_balance t_initial hft_list_initial Black
   = delete_balance t hft_list Black)
  LOCAL (temp _root root; temp _p p; temp _p_fa p_fa)
  SEP (rbtree_rep t p p_fa;
    partial_tree_rep hft_list root p p_fa)).
  {
    Exists t_initial.
    Exists hft_list_initial.
    Exists p_initial p_fa_initial.
    entailer!.
    apply partialtreebox_partialtree.
  }
  {
    Intros t hft_list p p_fa. 
    forward_if (p_fa <> nullval).
    { (* if p_fa is nullptr, then return directly *)
      subst.
      destruct hft_list eqn:E.
      2: {
        (* show hft_list is empty *)
        destruct h as [[[[[va c] k] v] tg] oppo].
        simpl partial_tree_rep.
        Intros p_gfa p_oppo.
        assert_PROP (False) by entailer!.
        contradiction.
      }
      simpl partial_tree_rep.
      Intros.
      forward.                      (* *root = p; *)
      forward.                      (* return; *)

      simpl in H1.
      rewrite H1.
      Exists t (@nil Half_tree).
      Exists root nullval.
      simpl partial_treebox_rep.
      unfold treebox_rep.
      Exists p.
      entailer!.
    }
    {
      forward.
      entailer!. 
    }
    destruct hft_list.
    { (* assert hft_list <> [] *)
      simpl partial_tree_rep.
      Intros.
      contradiction.
    }
    forward_call (t, p, p_fa).
    Intros vret.
    forward_if (get_color_tree t <> Col2Z Red).
                                    (* if (get_color(p) == RED) *)
    { (* the color of t is red *)
      destruct t.
      { (* assert t <> Empty *)
        simpl in H3.
        rewrite H3 in H4.
        assert_PROP (False) by entailer!.
        contradiction.
      }
      simpl rbtree_rep.
      Intros p_lch p_rch.
      forward.                      (* p->color = BLACK; *)
      forward.                      (* return; *)

      apply int_eq_e in H4.
      color_replace.
      rewrite H1.
      Exists (T Black t1 k v t2 t3) (h :: hft_list).
      destruct h as [[[[[va_f c_f] k_f] v_f] tg_f] oppo].
      simpl delete_balance.
      simpl partial_tree_rep.
      Intros p_gfa p_oppo.
      Exists (if va_f then (offset_val 20 p_fa) else (offset_val 16 p_fa)).
      Exists p_fa.
      simpl partial_treebox_rep.
      Exists p_gfa p_oppo.
      sep_apply partialtree_partialtreebox.
      Intros b_fa.
      Exists b_fa.
      unfold treebox_rep.
      Exists p.
      simpl rbtree_rep.
      Exists p_lch p_rch.
      destruct va_f.
      + assert_PROP (field_compatible t_struct_rbtree [StructField _right] p_fa)
          by entailer!.
        replace (offset_val 20 p_fa)
          with (field_address t_struct_rbtree [StructField _right] p_fa)
          by (unfold field_address; simpl;
          rewrite if_true by auto with field_compatible; auto).
        (* TODO: 杩欓噷鏄笉鏄湁鐐瑰啑闀匡紵 *)
        unfold_data_at (data_at _ _ _ p_fa).
        entailer!.
      + assert_PROP (field_compatible t_struct_rbtree [StructField _left] p_fa)
          by entailer!.
        replace (offset_val 16 p_fa)
          with (field_address t_struct_rbtree [StructField _left] p_fa)
          by (unfold field_address; simpl;
          rewrite if_true by auto with field_compatible; auto).
        (* TODO: 杩欓噷鏄笉鏄湁鐐瑰啑闀匡紵 *)
        unfold_data_at (data_at _ _ _ p_fa).
        entailer!.
    }
    {
      forward.
      entailer!.
      rewrite H3 in H4.
      simpl Col2Z in H4.
      apply int_eq_false_e in H4.
      contradiction.
    }
    destruct h as [[[[[va_f c_f] k_f] v_f] tg_f] oppo].
    simpl partial_tree_rep.
    Intros p_gfa p_oppo.
    rewrite delete_balance_t_color in H1; [| assumption ].
    destruct oppo.
    (* show oppo <> Empty *)
    { simpl in H0. rewrite (match_color _ _ _ H4) in H0. discriminate. }
    simpl rbtree_rep.
    Intros p_sib_lch p_sib_rch.

    forward.
    { destruct va_f; entailer!. }
    forward_if.                     (* if (p == p_fa->left) *)
    { destruct va_f; entailer!. }
    { (* p is the left child of p_fa *)
      forward.                      (* p_sib = p_fa->right; *)
      { destruct va_f; entailer!. }
      destruct va_f.
      { (* eliminate the wrong case *)
        (* TODO: 杩欎釜椤哄簭杩樻槸鏈夌偣绁炲锛屽厛璁ㄨ宸﹀彸鍐嶅仛 *)
        subst p.
        (* TODO: 杩欓噷涓哄暐杩欎箞闀� *)
        destruct t.
        {
          simpl rbtree_rep.
          Intros.
          assert_PROP (False) by entailer!.
          contradiction.
        }
        {
          simpl rbtree_rep.
          Intros p_lch1 p_rch1.
          sep_apply data_at_conflict; [apply sepalg_Tsh| ].
          sep_apply FF_local_facts.
          Intros.
          contradiction.
        }
      }
      forward.
      forward_if          (* if (p_sib->color == RED) *)
      (EX hft_list_changed : list Half_tree, 
        EX p_changed : val, 
        EX p_gfa_changed : val, 
        EX p_oppo_changed : val, 
        EX c_changed : color, 
        EX tg_changed : Tag, 
        EX k_sib : Key, 
        EX v_sib : Value, 
        EX tg_sib : Tag, 
        EX lch_sib : RBtree, 
        EX rch_sib : RBtree, 
        EX p_sib_lch : val, 
        EX p_sib_rch : val, 
        let hft := (false, c_changed, k_f, v_f, tg_changed, 
              (T Black lch_sib k_sib v_sib tg_sib rch_sib)) in
        PROP (delete_check (CaseTTF_sol t hft)
            hft_list_changed Black = true;
          CaseTTF_check t hft = true;
          delete_balance t_initial hft_list_initial Black
          = delete_balance (CaseTTF_sol t hft)
            hft_list_changed Black; 
            Int.min_signed <= k_sib <= Int.max_signed; 
            is_pointer_or_null p_gfa_changed)
        LOCAL (temp _root root; temp _p p; temp _p_fa p_fa; 
          temp _p_sib p_oppo_changed)
        SEP (rbtree_rep t p_changed p_fa;
          rbtree_rep lch_sib p_sib_lch p_oppo_changed;
          rbtree_rep rch_sib p_sib_rch p_oppo_changed;
          data_at Tsh t_struct_rbtree
          (Vint (Int.repr BLACK_COLOR),
          (Vint (Int.repr k_sib),
          (Vint (Int.repr v_sib),
          (Vint (Int.repr tg_sib), (p_sib_lch, (p_sib_rch, p_fa)))))) p_oppo_changed;
          data_at Tsh t_struct_rbtree
          (Vint (Int.repr (Col2Z c_changed)),
          (Vint (Int.repr k_f),
          (Vint (Int.repr v_f), (Vint (Int.repr tg_changed), 
            (p_changed, (p_oppo_changed, p_gfa_changed))))))
          p_fa;
          partial_tree_rep hft_list_changed root p_fa p_gfa_changed))%assert.
      (* TODO锛氳繖閲屾寜鐞嗘潵璇达紝_p 搴旇鏄� p_changed锛屼絾鏄疄闄呬笂涓嶆槸銆�
        铏界劧涓嶅奖鍝嶅悗缁殑璇佹槑銆�*)
      {
        color_replace.
        unfold CaseOne_sol in H1.
        (* show CaseOne_check is true *)
        assert ((CaseOne_check t
             (false, c_f, k_f, v_f, tg_f, T Red oppo1 k v t0 oppo2)) = true).
        {
          remember (CaseOne_check t
             (false, c_f, k_f, v_f, tg_f, T Red oppo1 k v t0 oppo2)) as bb.
          destruct bb.
          - reflexivity.
          - unfold delete_check in H0. rewrite <- Heqbb in H0.
            rewrite (match_color _ _ _ H4) in H0.
            discriminate.
        }
        apply case_one_true in H8; [ | assumption ].
        assert ((CaseTTF_check t
             (false, Red, k_f, v_f, default, tag_tree_t t0 oppo1)) = true).
        {
          simpl in H0. rewrite (match_color _ _ _ H4) in H0.
          rewrite if_else_then_true in H0. destruct H0 as [H0 _].
          rewrite if_else_then_true in H0. destruct H0 as [H0 _].
          exact H0.
        }
        pose proof H9 as H9_copy.
        apply (case_solve_not_null _ _ H4) in H9.
        (* a critical conclusion *)
        assert (
          delete_balance t_initial hft_list_initial Black = 
          delete_balance (CaseTTF_sol t
             (false, Red, k_f, v_f, default, tag_tree_t t0 oppo1)) 
          ((false, Black, k, f v t0, tg_f, tag_tree_t t0 oppo2) :: hft_list)
          Black).
        {
          rewrite H1.
          remember (CaseTTF_sol t (false, Red, k_f, v_f, default, tag_tree_t t0 oppo1))
            as t_t.
          destruct t_t; [ contradiction | ].
          destruct c.
          - simpl delete_balance. reflexivity.
          - destruct H8; destruct H8. 
            + discriminate H8.
            + destruct H10. destruct H11 as [H11 _]. 
              remember (tag_tree_t t0 oppo2) as t_t.
              destruct t_t.
              * discriminate H10.
              * destruct c; [ discriminate H10 | ].
                reflexivity.
        }

        forward_call (Red, k, v, t0, p_sib_lch, p_sib_rch, p_fa, p_oppo, 
          oppo1, oppo2).  (* pushdown(p_sib); *)
        forward.
        forward.          (* p_sib->tag = p_fa->tag; *)
        forward.          (* p_fa->tag = DEFAULT_TAG; *)
        forward.          (* p_sib->color = p_fa->color; *)
        forward.          (* p_fa->color = RED; *)
        assert_PROP (is_pointer_or_null p_gfa) by entailer!.
        forward_call      (* left_rotate_wrap(p_fa, root); *)
        (Red, k_f, v_f, default, p_gfa,
          Black, k, (v + t0), tg_f, 
          t, (tag_tree_t t0 oppo1), (tag_tree_t t0 oppo2), 
          p_fa, p_oppo, 
          p, root, hft_list).
        {
          simpl rbtree_rep.
          Exists p_sib_lch p_sib_rch.
          entailer!.
        }
        Intros vret0.
        simpl rbtree_rep at 2.
        Intros p' p_oppo'.
        forward.          (* p_sib = p_fa->right; *)
        destruct oppo1.
        { (* show oppo1 <> Empty *)
          simpl delete_check in H0.
          rewrite match_color in H0; [| assumption ].
          discriminate.
        }
        destruct c.
        { simpl in H9_copy. discriminate H9_copy. }
        simpl rbtree_rep.
        simpl tag_tree_t in H1.
        clear p_sib_lch. clear p_sib_rch.
        Intros p_sib_lch p_sib_rch.

        Exists ((false, Black, k, f v t0, tg_f, tag_tree_t t0 oppo2)
          :: hft_list).
        Exists p' p_oppo p_oppo'.
        Exists Red default k0 v0 (t0 + t1) oppo1_1 oppo1_2.
        Exists p_sib_lch p_sib_rch.
        simpl tag_tree_t in *.
        entailer!.
        {
          remember (CaseTTF_sol t
            (false, Red, k_f, v_f, default,
             T Black oppo1_1 k0 v0 (t0 + t1) oppo1_2)) as t_t.
          destruct t_t.
          - contradiction.
          - destruct H8; destruct H8.
            + simpl in H8. destruct c; [ | discriminate H8 ].
              simpl. reflexivity.
            + destruct H13. 
              remember (tag_tree_t t0 oppo2) as t_t.
              destruct t_t.
              * discriminate H13.
              * destruct c0; [ discriminate H13 | ].
                destruct H19.
                destruct c; [ discriminate H19 | ].
                unfold delete_check.
                rewrite H8.
                unfold delete_check in H0.
                rewrite (match_color _ _ _ H4) in H0.
                rewrite if_else_then_true in H0.
                destruct H0.
                rewrite H20 in H21.
                exact H21.
        }
        simpl partial_tree_rep.
        Exists p_gfa vret0.
        entailer!.
      }
      {
        forward.
        color_replace.
        Exists hft_list.
        Exists p p_gfa p_oppo.
        Exists c_f tg_f k v t0 oppo1 oppo2.
        Exists p_sib_lch p_sib_rch.
        entailer!.
        unfold delete_check in H0.
        rewrite (match_color _ _ _ H4) in H0.
        rewrite if_else_then_true in H0.
        destruct H0 as [H00 H0].
        split; assumption.
      }

      clear H0 H1 H3 H6 H7.
      clear c_f tg_f c oppo1 k v t0 oppo2 hft_list.
      clear vret p_gfa p_oppo p_sib_lch p_sib_rch.
      Intros hft_list p' p_gfa p_oppo.
      Intros c_f tg_f k v tg oppo1 oppo2.
      Intros p_sib_lch p_sib_rch.

      (* Case 2 *)
      forward.
      forward_call (oppo1, p_sib_lch, p_oppo).
      forward_if (temp _t'4 
        (Val.of_bool 
          ((negb (Int.eq (Int.repr (get_color_tree oppo1)) (Int.repr 1))) &&
          (negb (Int.eq (Int.repr (get_color_tree oppo2)) (Int.repr 1)))))).
      {
        forward.
        forward_call (oppo2, p_sib_rch, p_oppo).
        forward.
        entailer!.
        apply f_equal.
        destruct oppo1.
        - simpl get_color_tree. 
          (* TODO: 杩欓噷鐨勬瘮杈冨ソ鍍忓湪鍒殑鍦版柟涔熷嚭鐜拌繃锛� *)
          unfold Int.eq, zeq. simpl. reflexivity.
        - destruct c; try contradiction.
          simpl get_color_tree.
          unfold Int.eq, zeq. simpl. reflexivity.
      }
      {
        forward.
        entailer!.
        destruct oppo1; simpl get_color_tree in *.
        - discriminate.
        - destruct c; try discriminate.
          unfold Int.eq, zeq. simpl. reflexivity.
      }
      forward_if.
        (* if (get_color(p_sib->left) != RED && get_color(p_sib->right) != RED) *)
      {
        assert (get_color_tree oppo1 <> Col2Z Red).
        {
          intro. rewrite H8 in H7.
          unfold Int.eq, zeq in H7. simpl in H7.
          discriminate. 
        }
        assert (get_color_tree oppo2 <> Col2Z Red).
        {
          intro. rewrite H9 in H7.
          unfold Int.eq, zeq in H7. simpl in H7.
          rewrite andb_false_r in H7.
          discriminate. 
        }
        forward.        (* p_sib->color = RED; *)
        forward.        (* p = p_fa; *)
        forward.        (* p_fa = p->fa; *)
        destruct oppo1; destruct oppo2;
        simpl rbtree_rep;
        simpl in H1; simpl in H0.
        {
          Intros.
          Exists (T c_f t k_f v_f tg_f (T Red Empty k v tg Empty)) hft_list.
          Exists p_fa p_gfa.
          entailer!.
          simpl rbtree_rep.
          Exists p' p_oppo.
          Exists nullval nullval.
          entailer!.
        }
        {
          simpl get_color_tree in *.
          destruct c; [ contradiction | simpl in H0; discriminate ].
        }
        {
          simpl get_color_tree in *.
          destruct c; [ contradiction | simpl in H0; discriminate ].
        }
        {
          simpl get_color_tree in *.
          destruct c; [ contradiction | ].
          destruct c0; [ contradiction | ].
          Intros p_sib_lch_lch p_sib_lch_rch.
          Intros p_sib_rch_lch p_sib_rch_rch.
          Exists (T c_f t k_f v_f tg_f
            (T Red (T Black oppo1_1 k0 v0 t0 oppo1_2) k v tg
              (T Black oppo2_1 k1 v1 t1 oppo2_2))) hft_list.
          Exists p_fa p_gfa.
          entailer!.
          simpl rbtree_rep.
          Exists p' p_oppo.
          Exists p_sib_lch p_sib_rch.
          Exists p_sib_rch_lch p_sib_rch_rch.
          Exists p_sib_lch_lch p_sib_lch_rch.
          entailer!.
        }
      }
      {
        forward.
        forward_call (oppo2, p_sib_rch, p_oppo).
        apply semax_if_seq.
        (* TODO锛氳繖閲岀敱浜庡悗鏉′欢杩囦簬闀匡紝鍥犳鐢� semax_if_seq *)
        forward_if.   (* if (get_color(p_sib->right) != RED) *)
        {
          (* Case 3 *)
          rewrite <- negb_orb in H7.
          rewrite negb_false_iff in H7.
          apply orb_prop in H7.
          destruct H7; apply int_eq_e in H7; [ | contradiction ].
          destruct oppo1; [ simpl in H7; discriminate | ].
          simpl in H7.
          color_replace.
          simpl rbtree_rep.
          Intros p_sib_lch_lch p_sib_lch_rch.
          forward.
          forward_call (Red, k0, v0, t0, p_sib_lch_lch, p_sib_lch_rch, 
            p_oppo, p_sib_lch, oppo1_1, oppo1_2).
                          (* pushdown(p_sib->left); *)
          forward.
          forward.
          forward.    (* p_sib->left->tag = p_sib->tag; *)
          forward.    (* p_sib->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->left->color = BLACK; *)
          forward.    (* p_sib->color = RED; *)
          forward_call
          (Black, k0, v0 + t0, tg, 
            Red, k, v, default, p_fa, 
            (tag_tree_t t0 oppo1_1), (tag_tree_t t0 oppo1_2), oppo2, 
            p_sib_lch, p_oppo, 
            p_sib_rch, root, 
            (true, c_f, k_f, v_f, tg_f, t) :: hft_list).
          {
            simpl rbtree_rep.
            Exists p_sib_lch_lch p_sib_lch_rch.
            simpl partial_tree_rep.
            Exists p_gfa p'.
            entailer!.
          }
          Intros vret0.
          simpl rbtree_rep.
          Intros p_sib_lch' p_sib_rch'.
          simpl partial_tree_rep.
          clear p'.
          Intros p_gfa0 p'.
          (* TODO锛氳繖閲屽嚭鐜颁簡涓€涓粡鍏哥殑鎸囬拡鏀瑰彉浜嗙殑闂锛岄渶瑕佽В鍐炽€�*)
          forward.    (* p_sib = p_fa->right; *)

          forward_call (Black, k0, v0 + t0, tg, vret0, p_oppo, 
            p_fa, p_sib_lch, (tag_tree_t t0 oppo1_1), 
            (T Red (tag_tree_t t0 oppo1_2) k v default oppo2)).
                      (* pushdown(p_sib); *)
          {
            simpl rbtree_rep.
            Exists p_sib_lch' p_sib_rch'.
            entailer!.
          }
          simpl rbtree_rep.
          Intros p_oppo_lch p_oppo_rch.
          forward.
          forward.    (* p_sib->tag = p_fa->tag; *)
          forward.    (* p_fa->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->color = p_fa->color; *)
          forward.    (* p_fa->color = BLACK; *)
          forward.
          forward.    (* p_sib->right->color = BLACK; *)
          assert_PROP (is_pointer_or_null p_gfa0) by entailer!.
          forward_call
          (Black, k_f, v_f, default, p_gfa0, 
            c_f, k0, (v0 + t0 + tg), tg_f, 
            t, (tag_tree_t tg (tag_tree_t t0 oppo1_1)), 
              (T Black (tag_tree_t t0 oppo1_2) k v tg oppo2), 
            p_fa, p_sib_lch, 
            p', root, hft_list).
                      (* left_rotate_wrap(p_fa, root); *)
          {
            simpl rbtree_rep.
            Exists vret0 p_oppo.
            Exists p_oppo_lch p_oppo_rch.
            unfold BLACK_COLOR.
            entailer!.
            entailer!. (* ? *)
          }
          Intros vret1.
          simpl rbtree_rep at 1.
          Intros p_lch0 p_rch0.
          simpl rbtree_rep.
          Intros p_lch1 p_rch1.
          forward.    (* p = p_fa->fa; *)
          forward.    (* p_fa = p->fa; *)

          simpl tag_tree_t in *.
          Exists (T c_f
            (T Black t k_f v_f 0 (tag_tree_t tg (tag_tree_t t0 oppo1_1)))
            k0 (v0 + t0 + tg) tg_f
            (T Black (tag_tree_t t0 oppo1_2) k v tg oppo2)).
          Exists hft_list.
          Exists p_sib_lch p_gfa0.
          entailer!.
          {
            destruct oppo2; simpl CaseTTF_sol in *; rewrite Z.add_0_r in *.
            - split; [ rewrite <- H0 | rewrite H3 ]; reflexivity.
            - simpl in H8. color_replace.
              split; [ rewrite <- H0 | rewrite H3 ]; reflexivity.
          }
          simpl rbtree_rep.
          Exists p_fa vret1.
          Exists p_lch0 p_rch0.
          Exists p_lch1 p_rch1.
          entailer!.
        }
        {
        (* Case 4 *)
          destruct oppo2; [ simpl in H8; discriminate | ].
          simpl in H8.
          color_replace.
          simpl rbtree_rep.
          Intros p_sib_rch_lch p_sib_rch_rch.
          forward_call (Black, k, v, tg, p_sib_lch, p_sib_rch,
            p_fa, p_oppo, oppo1, 
            (T Red oppo2_1 k0 v0 t0 oppo2_2)).
                      (* pushdown(p_sib); *)
          {
            simpl rbtree_rep.
            Exists p_sib_rch_lch p_sib_rch_rch.
            entailer!.
          }
          simpl rbtree_rep.
          Intros p_oppo_lch p_oppo_rch.
          forward.
          forward.    (* p_sib->tag = p_fa->tag; *)
          forward.    (* p_fa->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->color = p_fa->color; *)
          forward.    (* p_fa->color = BLACK; *)
          forward.
          forward.    (* p_sib->right->color = BLACK; *)
          assert_PROP (is_pointer_or_null p_gfa) by entailer!.
          forward_call
          (Black, k_f, v_f, default, p_gfa, 
            c_f, k, (v + tg), tg_f, 
            t, (tag_tree_t tg oppo1), 
              (T Black oppo2_1 k0 v0 (tg + t0) oppo2_2), 
            p_fa, p_oppo, 
            p', root, hft_list).
                      (* left_rotate_wrap(p_fa, root); *)
          {
            simpl rbtree_rep.
            Exists p_sib_lch p_sib_rch.
            Exists p_oppo_lch p_oppo_rch.
            unfold BLACK_COLOR.
            entailer!.
          }
          Intros vret0.
          simpl rbtree_rep at 1.
          Intros p_lch0 p_rch0.
          simpl rbtree_rep.
          Intros p_lch1 p_rch1.
          forward.    (* p = p_fa->fa; *)
          forward.    (* p_fa = p->fa; *)
          Exists (T c_f (T Black t k_f v_f 0 (tag_tree_t tg oppo1)) k 
            (v + tg) tg_f (T Black oppo2_1 k0 v0 (tg + t0) oppo2_2)).
          Exists hft_list.
          Exists p_oppo p_gfa.
          entailer!.
          {
            destruct oppo1; simpl CaseTTF_sol in *.
            - split; [ rewrite <- H0 | rewrite H3 ]; reflexivity.
            - simpl in H8. 
              split; [ rewrite <- H0 | rewrite H3 ]; destruct c; reflexivity.
          }
          simpl rbtree_rep.
          Exists p_fa vret0.
          Exists p_lch0 p_rch0.
          Exists p_lch1 p_rch1.
          entailer!.
        }
      }
    }
    { (* p is the right child of p_fa *)
      forward.            (* p_sib = p_fa->right; *)
      destruct va_f; [ | contradiction ].
      forward.
      forward_if          (* if (p_sib->color == RED) *)
      (EX hft_list_changed : list Half_tree, 
        EX p_changed : val, 
        EX p_gfa_changed : val, 
        EX p_oppo_changed : val, 
        EX c_changed : color, 
        EX tg_changed : Tag, 
        EX k_sib : Key, 
        EX v_sib : Value, 
        EX tg_sib : Tag, 
        EX lch_sib : RBtree, 
        EX rch_sib : RBtree, 
        EX p_sib_lch : val, 
        EX p_sib_rch : val, 
        let hft := (true, c_changed, k_f, v_f, tg_changed, 
              (T Black lch_sib k_sib v_sib tg_sib rch_sib)) in
        PROP (delete_check (CaseTTF_sol t hft)
            hft_list_changed Black = true;
          CaseTTF_check t hft = true;
          delete_balance t_initial hft_list_initial Black
          = delete_balance (CaseTTF_sol t hft)
            hft_list_changed Black; 
            Int.min_signed <= k_sib <= Int.max_signed; 
            is_pointer_or_null p_gfa_changed)
        LOCAL (temp _root root; temp _p p; temp _p_fa p_fa; 
          temp _p_sib p_oppo_changed)
        SEP (rbtree_rep t p_changed p_fa;
          rbtree_rep lch_sib p_sib_lch p_oppo_changed;
          rbtree_rep rch_sib p_sib_rch p_oppo_changed;
          data_at Tsh t_struct_rbtree
          (Vint (Int.repr BLACK_COLOR),
          (Vint (Int.repr k_sib),
          (Vint (Int.repr v_sib),
          (Vint (Int.repr tg_sib), (p_sib_lch, (p_sib_rch, p_fa)))))) p_oppo_changed;
          data_at Tsh t_struct_rbtree
          (Vint (Int.repr (Col2Z c_changed)),
          (Vint (Int.repr k_f),
          (Vint (Int.repr v_f), (Vint (Int.repr tg_changed), 
            (p_oppo_changed, (p_changed, p_gfa_changed))))))
          p_fa;
          partial_tree_rep hft_list_changed root p_fa p_gfa_changed))%assert.
      (* TODO锛氳繖閲屾寜鐞嗘潵璇达紝_p 搴旇鏄� p_changed锛屼絾鏄疄闄呬笂涓嶆槸銆�
        铏界劧涓嶅奖鍝嶅悗缁殑璇佹槑銆�*)
      {
        color_replace.
        unfold CaseOne_sol in H1.
        (* show CaseOne_check is true *)
        assert ((CaseOne_check t
             (true, c_f, k_f, v_f, tg_f, T Red oppo1 k v t0 oppo2)) = true).
        {
          remember (CaseOne_check t
             (true, c_f, k_f, v_f, tg_f, T Red oppo1 k v t0 oppo2)) as bb.
          destruct bb.
          - reflexivity.
          - unfold delete_check in H0. rewrite <- Heqbb in H0.
            rewrite (match_color _ _ _ H4) in H0.
            discriminate.
        }
        apply case_one_true in H8; [ | assumption ].
        assert ((CaseTTF_check t
             (true, Red, k_f, v_f, default, tag_tree_t t0 oppo2)) = true).
        {
          simpl in H0. rewrite (match_color _ _ _ H4) in H0.
          rewrite if_else_then_true in H0. destruct H0 as [H0 _].
          rewrite if_else_then_true in H0. destruct H0 as [H0 _].
          exact H0.
        }
        pose proof H9 as H9_copy.
        apply (case_solve_not_null _ _ H4) in H9.
        (* a critical conclusion *)
        assert (
          delete_balance t_initial hft_list_initial Black = 
          delete_balance (CaseTTF_sol t
             (true, Red, k_f, v_f, default, tag_tree_t t0 oppo2)) 
          ((true, Black, k, f v t0, tg_f, tag_tree_t t0 oppo1) :: hft_list)
          Black).
        {
          rewrite H1.
          remember (CaseTTF_sol t (true, Red, k_f, v_f, default, tag_tree_t t0 oppo2))
            as t_t.
          destruct t_t; [ contradiction | ].
          destruct c.
          - simpl delete_balance. reflexivity.
          - destruct H8; destruct H8. 
            + discriminate H8.
            + destruct H10. destruct H11 as [H11 _]. 
              remember (tag_tree_t t0 oppo1) as t_t.
              destruct t_t.
              * discriminate H10.
              * destruct c; [ discriminate H10 | ].
                reflexivity.
        }

        forward_call (Red, k, v, t0, p_sib_lch, p_sib_rch, p_fa, p_oppo, 
          oppo1, oppo2).  (* pushdown(p_sib); *)
        forward.
        forward.          (* p_sib->tag = p_fa->tag; *)
        forward.          (* p_fa->tag = DEFAULT_TAG; *)
        forward.          (* p_sib->color = p_fa->color; *)
        forward.          (* p_fa->color = RED; *)
        assert_PROP (is_pointer_or_null p_gfa) by entailer!.
        forward_call      (* right_rotate_wrap(p_fa, root); *)
        (Black, k, (v + t0), tg_f, 
          Red, k_f, v_f, default, p_gfa,
          (tag_tree_t t0 oppo1), (tag_tree_t t0 oppo2), t, 
          p_oppo, p_fa, 
          p, root, hft_list).
        {
          simpl rbtree_rep.
          Exists p_sib_lch p_sib_rch.
          entailer!.
        }
        Intros vret0.
        simpl rbtree_rep at 2.
        Intros p' p_oppo'.
        forward.          (* p_sib = p_fa->left; *)
        destruct oppo2.
        { (* show oppo2 <> Empty *)
          simpl delete_check in H0.
          rewrite match_color in H0; [| assumption ].
          discriminate.
        }
        destruct c.
        { simpl in H9_copy. discriminate H9_copy. }
        simpl rbtree_rep.
        simpl tag_tree_t in H1.
        clear p_sib_lch. clear p_sib_rch.
        Intros p_sib_lch p_sib_rch.

        Exists ((true, Black, k, f v t0, tg_f, tag_tree_t t0 oppo1)
          :: hft_list).
        Exists p_oppo' p_oppo p'.
        Exists Red default k0 v0 (t0 + t1) oppo2_1 oppo2_2.
        Exists p_sib_lch p_sib_rch.
        simpl tag_tree_t in *.
        entailer!.
        {
          remember (CaseTTF_sol t
            (true, Red, k_f, v_f, default,
             T Black oppo2_1 k0 v0 (t0 + t1) oppo2_2)) as t_t.
          destruct t_t.
          - contradiction.
          - destruct H8; destruct H8.
            + simpl in H8. destruct c; [ | discriminate H8 ].
              simpl. reflexivity.
            + destruct H13. 
              remember (tag_tree_t t0 oppo1) as t_t.
              destruct t_t.
              * discriminate H13.
              * destruct c0; [ discriminate H13 | ].
                destruct H19.
                destruct c; [ discriminate H19 | ].
                unfold delete_check.
                rewrite H8.
                unfold delete_check in H0.
                rewrite (match_color _ _ _ H4) in H0.
                rewrite if_else_then_true in H0.
                destruct H0.
                rewrite H20 in H21.
                exact H21.
        }
        simpl partial_tree_rep.
        Exists p_gfa vret0.
        entailer!.
      }
      {
        forward.
        color_replace.
        Exists hft_list.
        Exists p p_gfa p_oppo.
        Exists c_f tg_f k v t0 oppo1 oppo2.
        Exists p_sib_lch p_sib_rch.
        entailer!.
        unfold delete_check in H0.
        rewrite (match_color _ _ _ H4) in H0.
        rewrite if_else_then_true in H0.
        destruct H0 as [H00 H0].
        split; assumption.
      }

      clear H0 H1 H3 H6 H7.
      clear c_f tg_f c oppo1 k v t0 oppo2 hft_list.
      clear vret p_gfa p_oppo p_sib_lch p_sib_rch.
      Intros hft_list p' p_gfa p_oppo.
      Intros c_f tg_f k v tg oppo1 oppo2.
      Intros p_sib_lch p_sib_rch.

      (* Case 2 *)
      forward.
      forward_call (oppo1, p_sib_lch, p_oppo).
      forward_if (temp _t'8
        (Val.of_bool 
          ((negb (Int.eq (Int.repr (get_color_tree oppo1)) (Int.repr 1))) &&
          (negb (Int.eq (Int.repr (get_color_tree oppo2)) (Int.repr 1)))))).
      {
        forward.
        forward_call (oppo2, p_sib_rch, p_oppo).
        forward.
        entailer!.
        apply f_equal.
        destruct oppo1.
        - simpl get_color_tree. 
          (* TODO: 杩欓噷鐨勬瘮杈冨ソ鍍忓湪鍒殑鍦版柟涔熷嚭鐜拌繃锛� *)
          unfold Int.eq, zeq. simpl. reflexivity.
        - destruct c; try contradiction.
          simpl get_color_tree.
          unfold Int.eq, zeq. simpl. reflexivity.
      }
      {
        forward.
        entailer!.
        destruct oppo1; simpl get_color_tree in *.
        - discriminate.
        - destruct c; try discriminate.
          unfold Int.eq, zeq. simpl. reflexivity.
      }
      forward_if.
        (* if (get_color(p_sib->left) != RED && get_color(p_sib->right) != RED) *)
      {
        assert (get_color_tree oppo1 <> Col2Z Red).
        {
          intro. rewrite H8 in H7.
          unfold Int.eq, zeq in H7. simpl in H7.
          discriminate. 
        }
        assert (get_color_tree oppo2 <> Col2Z Red).
        {
          intro. rewrite H9 in H7.
          unfold Int.eq, zeq in H7. simpl in H7.
          rewrite andb_false_r in H7.
          discriminate. 
        }
        forward.        (* p_sib->color = RED; *)
        forward.        (* p = p_fa; *)
        forward.        (* p_fa = p->fa; *)
        destruct oppo1; destruct oppo2; 
        simpl rbtree_rep.
        simpl in H1.
        simpl in H1; simpl in H0.
        {
          Intros.
          Exists (T c_f (T Red Empty k v tg Empty) k_f v_f tg_f t) hft_list.
          Exists p_fa p_gfa.
          entailer!.
          simpl rbtree_rep.
          Exists p_oppo p'.
          Exists nullval nullval.
          entailer!.
        }
        {
          simpl get_color_tree in *.
          destruct c; [ contradiction | simpl in H0; discriminate ].
        }
        {
          simpl get_color_tree in *.
          destruct c; [ contradiction | simpl in H0; discriminate ].
        }
        {
          simpl get_color_tree in *.
          destruct c; [ contradiction | ].
          destruct c0; [ contradiction | ].
          Intros p_sib_lch_lch p_sib_lch_rch.
          Intros p_sib_rch_lch p_sib_rch_rch.
          Exists (T c_f t k_f v_f tg_f
            (T Red (T Black oppo1_1 k0 v0 t0 oppo1_2) k v tg
              (T Black oppo2_1 k1 v1 t1 oppo2_2))) hft_list.
          Exists p_fa p_gfa.
          entailer!.
          simpl rbtree_rep.
          Exists p' p_oppo.
          Exists p_sib_lch p_sib_rch.
          Exists p_sib_rch_lch p_sib_rch_rch.
          Exists p_sib_lch_lch p_sib_lch_rch.
          entailer!.
        }
      }
      {
        forward.
        forward_call (oppo2, p_sib_rch, p_oppo).
        apply semax_if_seq.
        (* TODO锛氳繖閲岀敱浜庡悗鏉′欢杩囦簬闀匡紝鍥犳鐢� semax_if_seq *)
        forward_if.   (* if (get_color(p_sib->right) != RED) *)
        {
          (* Case 3 *)
          rewrite <- negb_orb in H7.
          rewrite negb_false_iff in H7.
          apply orb_prop in H7.
          destruct H7; apply int_eq_e in H7; [ | contradiction ].
          destruct oppo1; [ simpl in H7; discriminate | ].
          simpl in H7.
          color_replace.
          simpl rbtree_rep.
          Intros p_sib_lch_lch p_sib_lch_rch.
          forward.
          forward_call (Red, k0, v0, t0, p_sib_lch_lch, p_sib_lch_rch, 
            p_oppo, p_sib_lch, oppo1_1, oppo1_2).
                          (* pushdown(p_sib->left); *)
          forward.
          forward.
          forward.    (* p_sib->left->tag = p_sib->tag; *)
          forward.    (* p_sib->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->left->color = BLACK; *)
          forward.    (* p_sib->color = RED; *)
          forward_call
          (Black, k0, v0 + t0, tg, 
            Red, k, v, default, p_fa, 
            (tag_tree_t t0 oppo1_1), (tag_tree_t t0 oppo1_2), oppo2, 
            p_sib_lch, p_oppo, 
            p_sib_rch, root, 
            (true, c_f, k_f, v_f, tg_f, t) :: hft_list).
          {
            simpl rbtree_rep.
            Exists p_sib_lch_lch p_sib_lch_rch.
            simpl partial_tree_rep.
            Exists p_gfa p'.
            entailer!.
          }
          Intros vret0.
          simpl rbtree_rep.
          Intros p_sib_lch' p_sib_rch'.
          simpl partial_tree_rep.
          clear p'.
          Intros p_gfa0 p'.
          (* TODO锛氳繖閲屽嚭鐜颁簡涓€涓粡鍏哥殑鎸囬拡鏀瑰彉浜嗙殑闂锛岄渶瑕佽В鍐炽€�*)
          forward.    (* p_sib = p_fa->right; *)

          forward_call (Black, k0, v0 + t0, tg, vret0, p_oppo, 
            p_fa, p_sib_lch, (tag_tree_t t0 oppo1_1), 
            (T Red (tag_tree_t t0 oppo1_2) k v default oppo2)).
                      (* pushdown(p_sib); *)
          {
            simpl rbtree_rep.
            Exists p_sib_lch' p_sib_rch'.
            entailer!.
          }
          simpl rbtree_rep.
          Intros p_oppo_lch p_oppo_rch.
          forward.
          forward.    (* p_sib->tag = p_fa->tag; *)
          forward.    (* p_fa->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->color = p_fa->color; *)
          forward.    (* p_fa->color = BLACK; *)
          forward.
          forward.    (* p_sib->right->color = BLACK; *)
          assert_PROP (is_pointer_or_null p_gfa0) by entailer!.
          forward_call
          (Black, k_f, v_f, default, p_gfa0, 
            c_f, k0, (v0 + t0 + tg), tg_f, 
            t, (tag_tree_t tg (tag_tree_t t0 oppo1_1)), 
              (T Black (tag_tree_t t0 oppo1_2) k v tg oppo2), 
            p_fa, p_sib_lch, 
            p', root, hft_list).
                      (* left_rotate_wrap(p_fa, root); *)
          {
            simpl rbtree_rep.
            Exists vret0 p_oppo.
            Exists p_oppo_lch p_oppo_rch.
            unfold BLACK_COLOR.
            entailer!.
            entailer!. (* ? *)
          }
          Intros vret1.
          simpl rbtree_rep at 1.
          Intros p_lch0 p_rch0.
          simpl rbtree_rep.
          Intros p_lch1 p_rch1.
          forward.    (* p = p_fa->fa; *)
          forward.    (* p_fa = p->fa; *)

          simpl tag_tree_t in *.
          Exists (T c_f
            (T Black t k_f v_f 0 (tag_tree_t tg (tag_tree_t t0 oppo1_1)))
            k0 (v0 + t0 + tg) tg_f
            (T Black (tag_tree_t t0 oppo1_2) k v tg oppo2)).
          Exists hft_list.
          Exists p_sib_lch p_gfa0.
          entailer!.
          {
            destruct oppo2; simpl CaseTTF_sol in *; rewrite Z.add_0_r in *.
            - split; [ rewrite <- H0 | rewrite H3 ]; reflexivity.
            - simpl in H8. color_replace.
              split; [ rewrite <- H0 | rewrite H3 ]; reflexivity.
          }
          simpl rbtree_rep.
          Exists p_fa vret1.
          Exists p_lch0 p_rch0.
          Exists p_lch1 p_rch1.
          entailer!.
        }
        {
        (* Case 4 *)
          destruct oppo2; [ simpl in H8; discriminate | ].
          simpl in H8.
          color_replace.
          simpl rbtree_rep.
          Intros p_sib_rch_lch p_sib_rch_rch.
          forward_call (Black, k, v, tg, p_sib_lch, p_sib_rch,
            p_fa, p_oppo, oppo1, 
            (T Red oppo2_1 k0 v0 t0 oppo2_2)).
                      (* pushdown(p_sib); *)
          {
            simpl rbtree_rep.
            Exists p_sib_rch_lch p_sib_rch_rch.
            entailer!.
          }
          simpl rbtree_rep.
          Intros p_oppo_lch p_oppo_rch.
          forward.
          forward.    (* p_sib->tag = p_fa->tag; *)
          forward.    (* p_fa->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->color = p_fa->color; *)
          forward.    (* p_fa->color = BLACK; *)
          forward.
          forward.    (* p_sib->right->color = BLACK; *)
          assert_PROP (is_pointer_or_null p_gfa) by entailer!.
          forward_call
          (Black, k_f, v_f, default, p_gfa, 
            c_f, k, (v + tg), tg_f, 
            t, (tag_tree_t tg oppo1), 
              (T Black oppo2_1 k0 v0 (tg + t0) oppo2_2), 
            p_fa, p_oppo, 
            p', root, hft_list).
                      (* left_rotate_wrap(p_fa, root); *)
          {
            simpl rbtree_rep.
            Exists p_sib_lch p_sib_rch.
            Exists p_oppo_lch p_oppo_rch.
            unfold BLACK_COLOR.
            entailer!.
          }
          Intros vret0.
          simpl rbtree_rep at 1.
          Intros p_lch0 p_rch0.
          simpl rbtree_rep.
          Intros p_lch1 p_rch1.
          forward.    (* p = p_fa->fa; *)
          forward.    (* p_fa = p->fa; *)
          Exists (T c_f (T Black t k_f v_f 0 (tag_tree_t tg oppo1)) k 
            (v + tg) tg_f (T Black oppo2_1 k0 v0 (tg + t0) oppo2_2)).
          Exists hft_list.
          Exists p_oppo p_gfa.
          entailer!.
          {
            destruct oppo1; simpl CaseTTF_sol in *.
            - split; [ rewrite <- H0 | rewrite H3 ]; reflexivity.
            - simpl in H8. 
              split; [ rewrite <- H0 | rewrite H3 ]; destruct c; reflexivity.
          }
          simpl rbtree_rep.
          Exists p_fa vret0.
          Exists p_lch0 p_rch0.
          Exists p_lch1 p_rch1.
          entailer!.
        }
      }
    }
  }
Qed.

Theorem body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof. 
  start_function.
  forward.          (* root = t; *)
  unfold treeroot_rep.
  Intros p_root.
  forward_loop
  (EX t' : RBtree, 
  EX hft_list : list Half_tree, 
  EX p_fa : val,
  EX b0 : val, 
  PROP (delete_split x default t' hft_list = 
    delete_split x default t_tree nil)
  LOCAL (temp _x (Vint (Int.repr x)); 
        temp _t b0; temp _root b) 
  SEP (partial_treebox_rep hft_list b b0 p_fa;
      treebox_rep t' b0 p_fa)).
  (* almost the same as insertion *)
  {
    Exists t_tree.
    Exists (@nil Half_tree).
    Exists nullval.
    Exists b.
    unfold treebox_rep.
    Exists p_root.
    entailer!.
    simpl partial_treebox_rep.
    entailer!.
  } 
  { 
    Intros t' hft_list p_fa b0.
    unfold treebox_rep.
    Intros p.
    forward.          (* p = *t; *)
    forward_if.
    { (* if the target does not exist *)
      forward.        (* return; *)
      destruct t'.
      2: {
        simpl rbtree_rep.
        Intros p_lch p_rch.
        assert_PROP (False) by entailer!.
        contradiction.
      }
      simpl rbtree_rep.
      unfold delete. 
      unfold delete_into_base_half.
      unfold delete_with_no_balance.
      unfold delete_split, insert_split in *.
      simpl general_split in *.
      rewrite <- H0.
      simpl.
      remember (delete_balance Empty hft_list Red) as base_half.
      rewrite delete_balance_red in Heqbase_half.
      rewrite Heqbase_half.
      entailer!.
      apply delete_lemma.
    }
    { (* in searching for the target *)
      destruct t'.
      { (* assert t' <> Empty *)
        simpl rbtree_rep.
        Intros.
        contradiction.
      }
      simpl rbtree_rep.
      Intros p_lch p_rch.
      forward.        (* y = p->key; *)
      forward_call (c, k, v0, t, p_lch, p_rch, p_fa, p, t'1, t'2).
                      (* pushdown(p); *)
      forward_if.
      { (* x < y *)
        forward.      (* t = &(p->left); *)
        Exists (tag_tree_t t t'1). 
        Exists ((false, c, k, v0 + t, 0, tag_tree_t t t'2) :: hft_list).
        unfold treebox_rep.
        Exists p (offset_val 16 p).
        entailer!.
        {
          rewrite <- H0.
          unfold delete_split, insert_split.
          simpl.
          strip_0.
          arith_bool.
          rewrite H3.
          symmetry.
          apply general_split_tag. 
        }
        Exists p_lch.
        simpl partial_treebox_rep.
        Exists p_fa p_rch b0.
        replace (offset_val 16 p)
          with (field_address t_struct_rbtree [StructField _left] p)
          by (unfold field_address; simpl;
          rewrite if_true by auto with field_compatible; auto).
        unfold_data_at (data_at _ _ _ p).
        entailer!.
      }
      {
        forward_if.
        { (* x > y *)
          forward.      (* t = &(p->left); *)
          Exists (tag_tree_t t t'2). 
          Exists ((true, c, k, v0 + t, 0, tag_tree_t t t'1) :: hft_list).
          unfold treebox_rep.
          Exists p (offset_val 20 p).
          entailer!.
          {
            rewrite <- H0.
            unfold delete_split, insert_split.
            simpl.
            strip_0.
            arith_bool.
            rewrite H3, H4.
            symmetry.
            apply general_split_tag. 
          }
          Exists p_rch.
          simpl partial_treebox_rep.
          Exists p_fa p_lch b0.
          replace (offset_val 20 p)
            with (field_address t_struct_rbtree [StructField _right] p)
            by (unfold field_address; simpl;
            rewrite if_true by auto with field_compatible; auto).
          unfold_data_at (data_at _ _ _ p).
          entailer!.
        }
        { (* now at the delete point *)
          assert (k = x) by lia.
          clear H3 H4.
          forward.      (* original_color = p->color; *)
          forward.      (* p_fa = p->fa; *)
          forward.
          forward_if.   (* if (p->left == NULL) *)
          { (* left child is empty *)
            subst.
            destruct t'1; simpl rbtree_rep at 1.
            2: {
              Intros p_lch p_rch0.
              assert_PROP (False) by entailer!.
              contradiction.
            }
            forward.
            forward_if.   (* if (p->right == NULL) *)
            { (* right child is empty *)
              subst.
              destruct t'2; simpl rbtree_rep at 1.
              2: {
                Intros p_lch p_rch.
                assert_PROP (False) by entailer!.
                contradiction.
              }
              forward.    (* *t = NULL; *)
              forward_call (p, sizeof t_struct_rbtree).
              {
                entailer!.
                rewrite memory_block_data_at_ by auto.
                cancel.
              }
              apply semax_if_seq.
              forward_if.
              { (* try solve double black *)
                forward.
                forward_call (Empty, b, nullval, p_fa, b0, hft_list).
                { 
                  simpl rbtree_rep.
                  entailer!.
                }
                Intros vret.
                destruct vret as [[[t_balanced hft_list_balanced] b_balanced]
                      p_balanced].
                simpl fst in *.
                simpl snd in *.
                forward.        (* return; *)
                unfold delete.
                unfold delete_into_base_half.
                unfold delete_with_no_balance.
                rewrite <- H0.
                unfold delete_split, insert_split.
                simpl general_split.
                rewrite (Z.ltb_irrefl x).
                replace (v0 + (0 + t)) with (v0 + t) by lia.
                unfold delete_root.
                color_replace.
                rewrite <- H4.
                apply insert_lemma'.
              }
              {
                forward.        (* return; *)
                unfold delete.
                unfold delete_into_base_half.
                unfold delete_with_no_balance.
                rewrite <- H0.
                unfold delete_split, insert_split.
                simpl general_split.
                rewrite (Z.ltb_irrefl x).
                replace (v0 + (0 + t)) with (v0 + t) by lia.
                unfold delete_root.
                color_replace.
                rewrite delete_balance_red.
                apply delete_lemma.
              }
            }
            {
              (* right child is not empty *)
              destruct t'2; simpl rbtree_rep at 1.
              {
                Intros.
                contradiction.
              }
              Intros p_rch_lch p_rch_rch.
              forward.
              forward.    (* *t = p->right; *)
              forward.
              forward.    (* p->right->fa = p_fa; *)
              forward_call (p, sizeof t_struct_rbtree).
              {
                entailer!.
                rewrite memory_block_data_at_ by auto.
                cancel.
              }
              apply semax_if_seq.
              forward_if.
              { (* try solve double black *)
                forward.
                forward_call (T c0 t'2_1 k v1 (t + t0) t'2_2, b, p_rch, p_fa, b0, hft_list).
                { 
                  simpl rbtree_rep.
                  Exists p_rch_lch p_rch_rch.
                  entailer!.
                }
                Intros vret.
                destruct vret as [[[t_balanced hft_list_balanced] b_balanced]
                      p_balanced].
                simpl fst in *.
                simpl snd in *.
                forward.        (* return; *)
                unfold delete.
                unfold delete_into_base_half.
                unfold delete_with_no_balance.
                rewrite <- H0.
                unfold delete_split, insert_split.
                simpl general_split.
                rewrite (Z.ltb_irrefl x).
                replace (v0 + (0 + t)) with (v0 + t) by lia.
                unfold delete_root.
                color_replace.
                simpl Optt.
                replace (0 + t + t0 + 0) with (t + t0) by lia.
                rewrite <- H6.
                apply insert_lemma'.
              }
              {
                forward.        (* return; *)
                unfold delete.
                unfold delete_into_base_half.
                unfold delete_with_no_balance.
                rewrite <- H0.
                unfold delete_split, insert_split.
                simpl general_split.
                rewrite (Z.ltb_irrefl x).
                replace (v0 + (0 + t)) with (v0 + t) by lia.
                unfold delete_root.
                color_replace.
                simpl Optt.
                replace (0 + t + t0 + 0) with (t + t0) by lia.
                rewrite delete_balance_red.
                (* TODO锛氳繖閮ㄥ垎閲嶅鐨勫睘瀹炴湁鐐瑰銆傛€庝箞鍔烇紵 *)
                eapply derives_trans; [| 
                  apply (insert_lemma _ _ p_rch p_fa b b0)].
                simpl rbtree_rep.
                Exists p_rch_lch p_rch_rch.
                entailer!.
              }
            }
          }
          { (* left child is not null *)
            forward.
            destruct t'1 eqn:E_lch; simpl rbtree_rep at 1.
            {
              Intros.
              contradiction.
            }
            Intros p_lch_lch p_lch_rch.
            forward_if.
            { (* right child is null *)
              subst.
              destruct t'2.
              2: {
                simpl tag_tree_t.
                simpl rbtree_rep.
                Intros p_lch0 p_rch0.
                assert_PROP (False) by entailer!.
                contradiction.
              }
              forward.
              forward.    (* *t = p->left; *)
              forward.
              forward.    (* p->left->fa = p_fa; *)
              forward_call (p, sizeof t_struct_rbtree).
              {
                entailer!.
                rewrite memory_block_data_at_ by auto.
                cancel.
              }
              apply semax_if_seq.
              forward_if.
              { (* try solve double black *)
                forward.
                forward_call (T c0 r1 k0 v1 (t + t0) r2, b, p_lch, p_fa, b0, hft_list).
                { 
                  simpl rbtree_rep.
                  Exists p_lch_lch p_lch_rch.
                  entailer!.
                }
                Intros vret.
                destruct vret as [[[t_balanced hft_list_balanced] b_balanced]
                      p_balanced].
                simpl fst in *.
                simpl snd in *.
                forward.        (* return; *)
                unfold delete.
                unfold delete_into_base_half.
                unfold delete_with_no_balance.
                rewrite <- H0.
                unfold delete_split, insert_split.
                simpl general_split.
                rewrite (Z.ltb_irrefl x).
                replace (v0 + (0 + t)) with (v0 + t) by lia.
                unfold delete_root.
                color_replace.
                simpl Optt.
                replace (0 + t + t0 + 0) with (t + t0) by lia.
                rewrite <- H6.
                apply insert_lemma'.
              }
              {
                forward.        (* return; *)
                unfold delete.
                unfold delete_into_base_half.
                unfold delete_with_no_balance.
                rewrite <- H0.
                unfold delete_split, insert_split.
                simpl general_split.
                rewrite (Z.ltb_irrefl x).
                replace (v0 + (0 + t)) with (v0 + t) by lia.
                unfold delete_root.
                color_replace.
                simpl Optt.
                replace (0 + t + t0 + 0) with (t + t0) by lia.
                rewrite delete_balance_red.
                (* TODO锛氳繖閮ㄥ垎閲嶅鐨勫睘瀹炴湁鐐瑰銆傛€庝箞鍔烇紵 *)
                eapply derives_trans; [| 
                  apply (insert_lemma _ _ p_lch p_fa b b0)].
                simpl rbtree_rep.
                Exists p_lch_lch p_lch_rch.
                entailer!.
              }
            }
            { (* right child is not null *)
              destruct t'2 eqn:E_rch; simpl tag_tree_t; simpl rbtree_rep.
              {
                Intros.
                contradiction.
              }
              Intros p_rch_lch p_rch_rch.
              assert_PROP (field_compatible t_struct_rbtree [StructField _right] p)
                by entailer!.
              forward_call (t'2, (offset_val 20 p), p, (true, c, k, (v0 + t), default, t'1) :: hft_list, b).
              2: { subst t'2. intro. discriminate. }
              { 
                unfold treebox_rep.
                Exists p_rch.
                simpl partial_treebox_rep.
                Exists p_fa p_lch b0.
                replace (offset_val 20 p)
                  with (field_address t_struct_rbtree [StructField _right] p)
                  by (unfold field_address; simpl;
                  rewrite if_true by auto with field_compatible; auto).
                unfold_data_at (data_at _ _ _ p).
                entailer!.
                simpl rbtree_rep.
                Exists 
              
            

(* proof for free_tree *)
(* almost copied from verif_bst.v *)
Theorem body_tree_free: semax_body Vprog Gprog f_tree_free tree_free_spec.
Proof.
  start_function.
  forward_if (PROP()LOCAL()SEP()).
  + destruct t; simpl rbtree_rep.
      1: Intros. contradiction.
    Intros pa pb.
    forward.
    forward.
    forward_call (p, sizeof t_struct_rbtree).
    {
      entailer!.
      rewrite memory_block_data_at_ by auto.
      cancel.
    }
    forward_call (t1, pa, p).
    forward_call (t3, pb, p).
    entailer!.
  + forward.
    subst.
    entailer!.
    simpl; normalize.
    destruct t.
    - unfold rbtree_rep.
      entailer!.
    - simpl rbtree_rep. 
      Intros. Intros p_lch p_rch.
      entailer!. destruct H0. inversion H0.
  + entailer!. 
Qed.

(* proof for treebox_free *)
(* almost copied from verif_bst.v *)
Theorem body_treebox_free: semax_body Vprog Gprog f_treebox_free treebox_free_spec.
Proof.
  start_function.
  unfold treeroot_rep.
  Intros p.
  forward.
  forward_call (t, p, nullval).
  forward_call (b, sizeof (tptr t_struct_rbtree)).
  entailer!.
  rewrite memory_block_data_at_ by auto.
  cancel.
  forward.
Qed.

(* proof for Optt *)
Theorem body_Optt: semax_body Vprog Gprog f_Optt Optt_spec.
Proof.
  start_function.
  forward.
Qed.

(* proof for Opvt *)
Theorem body_Opvt: semax_body Vprog Gprog f_Opvt Opvt_spec.
Proof.
  start_function.
  forward.
Qed.

(* proof for tag_tree_t *)
Theorem body_tag_tree_t: semax_body Vprog Gprog f_tag_tree_t tag_tree_t_spec.
Proof.
  start_function.
  forward_if.
  {
    destruct t.
    - unfold rbtree_rep. 
      assert_PROP (x = nullval).
      { entailer!. }
      contradiction.
    - simpl rbtree_rep.
      Intros. Intros p_lch p_rch.
      forward.                (* _t'2 = (_x -> _tag); *)
      forward_call (t2, tag). (* _t'1 = _Optt(_t'2, _tag); *)
      forward.                (* (_x -> _tag) = _t'1; *)
      forward.                (* return; *)
      simpl rbtree_rep.
      entailer!.
      Exists p_lch p_rch.
      assert(t2 + tag = tag + t2) by omega.
      rewrite H3.
      apply derives_refl.
  }
  {
    forward.
    destruct t.
    - entailer!.
    - simpl rbtree_rep. 
      entailer!.
      Intros p_lch p_rch.
      Exists p_lch p_rch.
      entailer!.
      destruct H. inversion H.
  }
Qed.

(* proof for get_color *)
Theorem body_get_color: 
  semax_body Vprog Gprog f_get_color get_color_spec.
Proof.
  start_function.
  forward_if.
  {
    assert_PROP (t = Empty).
    {
      destruct t.
      - entailer!.
      - simpl rbtree_rep.
        Intros p_lch p_rch.
        subst x.
        entailer!.
    }
    subst t.
    simpl rbtree_rep.
    Intros.
    forward.
    simpl rbtree_rep.
    entailer!.
  }
  {
    destruct t.
    {
      simpl rbtree_rep.
      Intros.
      apply H in H0.
      destruct H0.
    }
    simpl rbtree_rep.
    Intros p_lch p_rch.
    forward.
    forward.
    simpl rbtree_rep.
    Exists p_lch p_rch.
    entailer!.
  }
Qed.

(* proof for make_black *)
Theorem body_make_black : semax_body Vprog Gprog f_make_black make_black_spec.
Proof.
  start_function.
  forward_if.
  {
    subst.
    forward.
    destruct t.
    - entailer!.
    - unfold treebox_rep.
      simpl rbtree_rep.
      Intros p p_lch p_rch.
      Exists p p_lch p_rch.
      entailer!.
      destruct H0. 
      contradiction.
  }
  {
    destruct t.
    {
      unfold treebox_rep.
      Intros p.
      simpl rbtree_rep.
      Intros.
      forward.
      forward_if.
      - forward.
        simpl.
        unfold treebox_rep.
        Exists nullval.
        simpl.
        entailer.
      - contradiction.
    }
    {
      unfold treebox_rep.
      Intros p.
      forward.
      forward_if.
      - subst.
        simpl rbtree_rep.
        Intros p_lch p_rch.
        forward.
        unfold_data_at (data_at _ _ _ nullval).
        Intros.
        destruct H3. contradiction.
      - simpl rbtree_rep.
        Intros p_lch p_rch.
        forward.
        entailer!.
        unfold treebox_rep.
        Exists p.
        simpl.
        Exists p_lch p_rch.
        entailer!.
    }
  }
Qed.

(* proof for left_rotate *)
Theorem body_left_rotate : semax_body Vprog Gprog f_left_rotate left_rotate_spec.
Proof.
  start_function.
  simpl rbtree_rep.
  Intros p_lch p_rch.
  forward.    (* r = l->right; *)
  forward.    (* mid = r->left; *)
  forward.    (* l->right = mid; *)  
  forward.
  forward.    (* r->left = l; *)
  forward.    (* r->fa = l->fa; *)
  forward.    (* l->fa = r; *)
  forward_if
  (
    PROP ()
    LOCAL (temp _t'1 fa_l; temp _mid p_lch; temp _r r; temp _l l)
    SEP (EX pc: val, data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (l, (pc, fa_l)))))) r *
          rbtree_rep tc pc r *
          rbtree_rep (T col_l ta key_l value_l tag_l tb) l r)).
  { (* p_lch <> nullval *)
    destruct tb.
    - simpl rbtree_rep.
      assert_PROP (p_lch = nullval).
      { Intros. contradiction. }
      contradiction.
    - simpl rbtree_rep.
      Intros p_lch0 p_rch0.
      forward.    (* (_mid -> _fa) = _l; *)
      Exists p_rch.
      entailer!.
      unfold rbtree_rep at 4; fold rbtree_rep.
      entailer!.
      Exists pa p_lch.
      entailer!.
      Exists p_lch0 p_rch0.
      entailer!.    (* TODO: remove some entailer!.s *)
  }
  { (* p_lch = nullval *)
    forward.      (* skip; *)
    Exists p_rch.
    entailer!.
    simpl rbtree_rep.
    entailer!.
    Exists pa nullval.
    entailer!.
    destruct tb.
    - simpl. entailer!.
    - simpl rbtree_rep. Intros. Intros p_lch p_rch0. entailer!.
        destruct H7. inversion H7.
  }
  forward.      (* return; *)
  Exists pc.
  entailer!.
Qed.

(* proof for right rotate *)
Theorem body_right_rotate : semax_body Vprog Gprog f_right_rotate right_rotate_spec.
Proof.
  start_function.
  simpl rbtree_rep.
  Intros p_lch p_rch.
  forward.    (* l = r->left; *)
  forward.    (* mid = l->right; *)
  forward.    (* r->left = mid; *)  
  forward.    (* l->right = r; *)
  forward.    
  forward.    (* r->fa = l->fa; *)
  forward.    (* l->fa = r; *)
  forward_if
  ( 
    PROP ()
    LOCAL (temp _t'1 fa_r; temp _mid p_rch; temp _l l; temp _r r)
    SEP (EX pa: val, data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (r, fa_r)))))) l *
          rbtree_rep ta pa l *
          rbtree_rep (T col_r tb key_r value_r tag_r tc) r l)).
  { 
    destruct tb.
    - simpl rbtree_rep.
      assert_PROP (p_rch = nullval).
      { entailer!. }
      contradiction.
    - simpl rbtree_rep.
      Intros p_lch0 p_rch0.
      forward.    (* (_mid -> _fa) = _l; *)
      Exists p_lch.
      entailer!.
      unfold rbtree_rep at 4; fold rbtree_rep.
      entailer!.
      Exists p_rch pc.
      entailer!.
      Exists p_lch0 p_rch0.
      entailer!.    (* TODO: remove some entailer!.s *)
  }
  {
    forward.
    Exists p_lch.
    entailer!.
    simpl rbtree_rep.
    entailer!.
    Exists nullval pc.
    entailer!.
    destruct tb.
    - simpl. entailer!.
    - simpl rbtree_rep. Intros. Intros p_lch0 p_rch. entailer!.
        (* TODO: 杩欎釜鎷� field_compatible nullval 鏄笉鏄篃鍙互鑷姩鍖栵紵*)
        destruct H7. inversion H7.
  }
  forward.      (* return; *)
  Exists pa.
  entailer!.
Qed. 

Theorem body_pushdown: semax_body Vprog Gprog f_pushdown pushdown_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_call (v, tg).             (* p->value = Opvt(p->value, p->tag); *)
  forward.
  forward.
  forward.
  forward_call (t'1, tg, p_lch, p). (* tag_tree_t(p->left, p->tag); *)
  forward.
  forward.
  forward_call (t'2, tg, p_rch, p). (* tag_tree_t(p->right, p->tag); *)
  forward.                          (* p->tag = DEFAULT_TAG; *)
  entailer!.
Qed.

Theorem body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  forward.          (* root = t; *)
  forward.          (* last_node = NULL; *)
  unfold treeroot_rep.
  Intros p_root.
  forward_loop 
  (EX t' : RBtree, 
  EX hft_list : list Half_tree, 
  EX p_fa : val,
  EX b0 : val, 
  PROP (let (h, b) := insert_split x default t' hft_list in 
    insert' x v t_tree = (h, insert_root x v b))
  LOCAL (temp _last_node p_fa; 
        temp _x (Vint (Int.repr x)); 
        temp _value (Vint (Int.repr v)); 
        temp _t b0; temp _root b) 
  SEP (partial_treebox_rep hft_list b b0 p_fa;
      treebox_rep t' b0 p_fa))%assert.
  {
    Exists t_tree.
    Exists (@nil Half_tree).
    Exists nullval.
    Exists b.
    unfold treebox_rep.
    Exists p_root.
    entailer!.
    - unfold insert'.
      remember (insert_split x default t_tree []) as hb.
      destruct hb as [h' b'].
      reflexivity.
    - simpl partial_treebox_rep.
      entailer!.
  } 
  { 
    Intros t' hft_list p_fa b0.
    unfold treebox_rep.
    Intros p.
    forward.          (* p = *t; *)
    forward_if.
    {
      (* first branch: arrive at the insert point *)
      forward_call (sizeof t_struct_rbtree).
      { 1: simpl; rep_omega. }
      Intros vret.
      subst p.
      rewrite memory_block_data_at_ by auto.
      forward.        (* p->color = RED; *)
      simpl.
      forward.        (* p->key = x; *)
      forward.        (* p->value = value; *)
      forward.        (* p->tag = DEFAULT_TAG; *)
      forward.        (* p->left = NULL; *)
      forward.        (* p->right = NULL;  *)
      forward.        (* p->fa = last_node; *)
      forward.        (* *t = p; *)
      assert_PROP (is_pointer_or_null p_fa) as H_p_fa.
      { entailer!. }
      simpl rbtree_rep at 1.
      forward_call ((T Red Empty x v default Empty), b, p_fa, b0, hft_list).
      2: { intro. discriminate H1. }
      1: {
        unfold treebox_rep.
        Exists vret.
        simpl rbtree_rep.
        Exists (Vint (Int.repr 0)) (Vint (Int.repr 0)).
        entailer!.
      }
      Intros ret_val.
      destruct ret_val as [[[t_balanced hft_list_balanced] b'] p'].
      simpl in H1.
      simpl treebox_rep.
      simpl partial_treebox_rep.
      unfold treebox_rep.
      Intros p.
      (* first eliminate nulltree *)
      destruct t'.
      2: {
        simpl rbtree_rep at 2.
        Intros p_lch p_rch.
        assert_PROP (False).
        { entailer!. }
        destruct H4.
      }
      simpl rbtree_rep at 2.
      Intros.
      forward_call ((complete_tree hft_list_balanced t_balanced), b).
      { 
        sep_apply (derives_trans (data_at Tsh (tptr t_struct_rbtree) p b' * rbtree_rep t_balanced p p' *
partial_treebox_rep hft_list_balanced b b' p')
(treebox_rep (complete_tree hft_list_balanced t_balanced) b nullval) (treebox_rep (complete_tree hft_list_balanced t_balanced) b nullval *
    fold_right_sepcon Frame)).
    3: { apply derives_refl. }
    1: { apply insert_lemma. }
        entailer!.
      }
      forward.
      Exists (makeBlack (complete_tree hft_list_balanced t_balanced)).
      unfold treeroot_rep.
      unfold treebox_rep.
      Intros p0.
      Exists p0.
      entailer!.
      (* pure proposition! *)
      pose proof (insert_intro x v t_tree hft_list (T Red Empty x v 0 Empty) 
        hft_list_balanced t_balanced).
      unfold insert_split in H0; simpl in H0.
      symmetry in H0.
      apply H5; auto.
    }
    {
      (* second branch: find the insert point *)
      destruct t'.
      { (* remove the impossible case *)
        simpl rbtree_rep at 1.
        Intros.
        apply H1 in H2; destruct H2.
      }
      simpl rbtree_rep at 1.
      Intros.
      Intros p_lch p_rch.
      forward.            (* int y = p->key; *)
      forward_call (c, k, v0, t, p_lch, p_rch, p_fa, p, t'1, t'2).
                          (* pushdown(p); *)
      forward_if.
      { 
        (* if x is already in the tree *)
        subst.
        forward.                      (* p->value = value; *)
        forward_call ((T c (tag_tree_t t t'1) k v default (tag_tree_t t t'2)), 
          b, p_fa, b0, hft_list).     (* solve_double_red(t, root); *)
        2: { intro. discriminate H3. }
        1: {
          unfold treebox_rep.
          Exists p.
          simpl rbtree_rep.
          Exists p_lch p_rch.
          entailer!.
        }
        Intros ret_val.
        destruct ret_val as [[[t_balanced hft_list_balanced] b'] p'].
        simpl in H3.
        simpl treebox_rep.
        simpl partial_treebox_rep.
        unfold treebox_rep.
        Intros p0.
        forward_call ((complete_tree hft_list_balanced t_balanced), b).
                                      (* make_black(root); *)
        { 
          entailer.
          sep_apply (derives_trans (data_at Tsh (tptr t_struct_rbtree) p0 b' * rbtree_rep t_balanced p0 p' *
partial_treebox_rep hft_list_balanced b b' p')
(treebox_rep (complete_tree hft_list_balanced t_balanced) b nullval) (treebox_rep (complete_tree hft_list_balanced t_balanced) b nullval *
    fold_right_sepcon Frame)).
          3: { apply derives_refl. }
          1: { apply insert_lemma. }
          entailer!.
        }
        forward.
        Exists (makeBlack (complete_tree hft_list_balanced t_balanced)).
        unfold treeroot_rep.
        unfold treebox_rep.
        Intros p1.
        Exists p1.
        entailer!.
        (* pure proposition! *)
        unfold insert_split, lt_bool in H0.
        simpl in H0.
        assert (k <? k = false).
        { apply Z.ltb_irrefl. }
        rewrite H6 in H0.
        pose proof (insert_intro k v t_tree hft_list (T c (tag_tree_t (0 + t) t'1) k v 0 (tag_tree_t (0 + t) t'2)) 
          hft_list_balanced t_balanced).
        apply H7; auto.
      }
      { 
        forward.          (* last_node = p; *)
        (* otherwise move down the tree *)
        forward_if.       (* determine whether x < y or not *)
        { 
          (* x < k *)
          forward.        (* t = &(p->left); *)
          Exists (tag_tree_t t t'1). 
          Exists ((false, c, k, v0 + t, 0, tag_tree_t t t'2) :: hft_list).
          unfold treebox_rep.
          Exists p (offset_val 16 p).
          entailer!.
          { 
            unfold insert_split, lt_bool in *.
            rewrite <- Z.ltb_lt in H4.
            simpl general_split in *.
            try rewrite H4 in *.
            rewrite general_split_tag in H0.
            strip_0.
            auto.
          }
          Exists p_lch.
          simpl partial_treebox_rep.
          Exists p_fa p_rch b0.
          replace (offset_val 16 p)
            with (field_address t_struct_rbtree [StructField _left] p)
            by (unfold field_address; simpl;
            rewrite if_true by auto with field_compatible; auto).
          unfold_data_at (data_at _ _ _ p).
          entailer!.
        }
        { 
          (* x > k, symmetric case *)
          forward.        (* t = &(p->p->right); *)
          Exists (tag_tree_t t t'2). 
          Exists ((true, c, k, v0 + t, 0, tag_tree_t t t'1) :: hft_list).
          unfold treebox_rep.
          Exists p (offset_val 20 p).
          entailer!.
          { 
            unfold insert_split, lt_bool in *.
            simpl general_split in *.
            assert (k < x) by lia. 
            assert (x <? k = false).
            { rewrite Z.ltb_nlt. lia. }
            rewrite <- Z.ltb_lt in H10.
            try rewrite H10, H11 in *.
            rewrite general_split_tag in H0.
            strip_0.
            auto.
          }
          Exists p_rch.
          simpl partial_treebox_rep.
          Exists p_fa p_lch b0.
          replace (offset_val 20 p)
            with (field_address t_struct_rbtree [StructField _right] p)
            by (unfold field_address; simpl;
            rewrite if_true by auto with field_compatible; auto).
          unfold_data_at (data_at _ _ _ p).
          entailer!.
        }
      }
    }
  }
Qed.

Theorem body_update_aux: 
  semax_body Vprog Gprog f_update_aux update_aux_spec.
Proof.
  start_function.
  forward_if.           (* if (t == NULL) *)
  { 
    forward.
    destruct t.
    - rewrite change_empty. apply derives_refl.
    - simpl rbtree_rep. Intros p_lch p_rch.
      entailer!. destruct H4; inversion H4.
  }
  (* t <> Empty *)
  destruct t; [simpl rbtree_rep; Intros; contradiction |].
  forward_if.           (* if (l > targ_r) *)
  { 
    forward.
    arith_bool.
    simpl change_segment'.
    rewrite H4.
    simpl. apply derives_refl.
  }
  (* targ_hi >= lo *)
  forward_if.           (* if (r < targ_l) *)
  { 
    forward.
    arith_bool.
    simpl change_segment'.
    rewrite H5, orb_true_r.
    apply derives_refl.
  }
  (* hi >= targ_lo *)
  forward_if (temp _t'4 
    (Val.of_bool ((targ_lo <=? lo) && (hi <=? targ_hi)))).
  {
    forward.
    entailer!.
    apply f_equal.
    arith_bool.
    repeat rewrite Z.leb_antisym.
    rewrite H6.
    simpl.
    apply f_equal.
    unfold Int.lt.
    repeat (rewrite Int.signed_repr; [| assumption ]).
    apply zlt_bool_1.
  }
  {
    forward.
    entailer!.
    arith_bool.
    repeat rewrite Z.leb_antisym.
    rewrite H6.
    simpl.
    reflexivity.
  }
  forward_if.           (* if (l >= targ_l && r <= targ_r) *)
  {
    (* inner *)
    simpl rbtree_rep.
    Intros p_lch p_rch.
    forward.
    forward_call (t2, tg).
    forward.                  (* t->tag = Optt(t->tag, tg); *)
    forward.
    simpl change_segment'.
    apply andb_prop in H6.
    destruct H6.
    arith_bool.
    simpl.
    unfold lte_bool, lt_bool.
    simpl.
    rewrite H4, H5.
    repeat rewrite arith_bool_1.
    rewrite H6, H11.
    simpl.
    Exists p_lch p_rch.
    rewrite Z.add_comm.
    entailer!.
  }
  {
    simpl rbtree_rep.
    Intros p_lch p_rch.
    forward.
    forward_if (temp _t'3
      (Val.of_bool ((targ_lo <=? k) && (k <=? targ_hi)))).
    {
      forward.
      forward.
      entailer!.
      apply f_equal.
      arith_bool.
      repeat rewrite Z.leb_antisym.
      rewrite H8.
      simpl.
      apply f_equal.
      unfold Int.lt.
      repeat (rewrite Int.signed_repr; [| assumption ]).
      apply zlt_bool_1.
    }
    { 
      forward.
      entailer!.
      arith_bool.
      repeat rewrite Z.leb_antisym.
      rewrite H8.
      simpl.
      reflexivity.
    }
    deadvars!.
    forward_if        (* if (targ_l <= t->key && t->key <= targ_r) *)
    (PROP ( )
    LOCAL (temp _t'3 (Val.of_bool ((targ_lo <=? k) && (k <=? targ_hi)));
    temp _t p; temp _tg (Vint (Int.repr tg)); temp _l (Vint (Int.repr lo));
    temp _r (Vint (Int.repr hi)); temp _targ_l (Vint (Int.repr targ_lo));
    temp _targ_r (Vint (Int.repr targ_hi)))
    SEP (data_at Tsh t_struct_rbtree
          (Vint (Int.repr (Col2Z c)),
          (Vint (Int.repr k),
          (Vint (Int.repr (if ((targ_lo <=? k) && (k <=? targ_hi))%bool then f v tg else v)), 
          (Vint (Int.repr t2), (p_lch, (p_rch, p_fa)))))) p;
    rbtree_rep t1 p_lch p; rbtree_rep t3 p_rch p)).
    {
      (* tag the root *)
      forward.
      forward_call (v, tg).
      forward.
      rewrite H8.
      simpl f.
      entailer!.
    }
    {
      forward.
      rewrite H8.
      entailer!.
    }
    arith_bool.
    forward.
    forward.
    forward_call (p_lch, p, t1, tg, targ_lo, targ_hi, lo, k).
    forward.
    forward.
    forward_call (p_rch, p, t3, tg, targ_lo, targ_hi, k, hi).
    entailer!.
    unfold lte_bool. 
    rewrite H4, H5.
    simpl.
    unfold lt_bool.
    repeat rewrite arith_bool_1.
    rewrite H6.
    simpl.
    Exists p_lch p_rch.
    entailer!.
  }
Qed.

Theorem body_update: 
  semax_body Vprog Gprog f_update update_spec.
Proof.
  start_function.
  destruct t.
  {
    unfold treeroot_rep.
    Intros p.
    simpl rbtree_rep.
    Intros. subst p.
    forward.
    forward_call (nullval, nullval, Empty, tg, targ_lo, targ_hi, -2147483647, 2147483647).
    { 
      simpl rbtree_rep.
      entailer!.
    }
    { rep_omega. }
    unfold change_segment.
    repeat rewrite change_empty.
    unfold treeroot_rep.
    entailer!.
    Exists nullval.
    entailer!.
  }
  {
    unfold treeroot_rep.
    Intros p.
    simpl rbtree_rep.
    Intros p_lch p_rch.
    forward.
    forward_call (p, nullval, (T c t1 k v t2 t3), tg, targ_lo, targ_hi, -2147483647, 2147483647).
    {
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
    }
    { rep_omega. }
    entailer!.
    unfold treeroot_rep.
    Exists p.
    unfold change_segment.
    entailer!.
  }
Qed.

(* proof for left_rotate_wrap *)
Theorem body_left_rotate_wrap:
  semax_body Vprog Gprog f_left_rotate_wrap left_rotate_wrap_spec.
Proof.
  start_function.
  simpl rbtree_rep.
  Intros p_lch p_rch.
  forward.
  forward_if.                     (* if (l->fa == NULL) *)
  { (* l is the root *) 
    forward_call 
    (col_l, key_l, value_l, tag_l, fa_l, 
      col_r, key_r, value_r, tag_r, 
      ta, tb, tc, 
      l, r, pa).
    {
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
    }
    Intros vret.
    simpl rbtree_rep.
    clear p_lch. clear p_rch.
    Intros p_lch p_rch.
    subst.
    destruct hft_list.
    2: {
      (* show that hft_list = [] *)
      destruct h as [[[[[vacancy_gfa c_gfa] k_gfa] v_gfa] tg_gfa] oppo_fa_tbd].
      simpl partial_tree_rep.
      Intros p_gfa p_oppo.
      sep_apply data_at_nullval.
      Intros. contradiction.
    }
    simpl partial_tree_rep.
    Intros.
    forward.                      (* *root = left_rotate(l); *)
    Exists vret.
    entailer!.
    simpl partial_tree_rep.
    simpl rbtree_rep.
    Exists p_lch p_rch.
    entailer!.
  }
  {
    forward.
    destruct hft_list.
    { (* show that hft_list <> [] *)
      simpl partial_tree_rep.
      Intros.
      contradiction.
    }
    destruct h as [[[[[vacancy_fa c_fa] k_fa] v_fa] tg_fa] oppo_tbd].
    simpl partial_tree_rep.
    Intros p_gfa p_oppo.
    forward.
    { destruct vacancy_fa; entailer!. }
    forward_if.
    { destruct vacancy_fa; entailer!. }
    {
      (* l is the left branch *)
      destruct vacancy_fa.
      { (* verify that l is on the left *)
        subst l.
        destruct oppo_tbd.
        - simpl rbtree_rep. Intros.
          subst p_oppo.
          assert_PROP (False). { entailer!. }
          contradiction.
        - simpl rbtree_rep. 
          Intros p_lch0 p_rch0.
          sep_apply data_at_conflict; [apply sepalg_Tsh| ].
          sep_apply FF_local_facts.
          Intros.
          contradiction.
      }
      subst.
      forward_call 
      (col_l, key_l, value_l, tag_l, fa_l, 
        col_r, key_r, value_r, tag_r, 
        ta, tb, tc, 
        l, r, pa).
      {
        simpl rbtree_rep.
        Exists p_lch p_rch.
        entailer!.
      }
      Intros vret.
      simpl rbtree_rep.
      clear p_lch. clear p_rch.
      Intros p_lch p_rch.
      forward.                    (* l_fa->left = left_rotate(l); *)
      Exists vret.
      entailer!.
      simpl partial_tree_rep.
      Exists p_gfa p_oppo.
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
    }
    {
      (* l is the right branch *)
      destruct vacancy_fa; [ | contradiction ].
      forward_call 
      (col_l, key_l, value_l, tag_l, fa_l, 
        col_r, key_r, value_r, tag_r, 
        ta, tb, tc, 
        l, r, pa).
      {
        simpl rbtree_rep.
        Exists p_lch p_rch.
        entailer!.
      }
      Intros vret.
      simpl rbtree_rep.
      clear p_lch. clear p_rch.
      Intros p_lch p_rch.
      forward.                    (* l_fa->right = left_rotate(l); *)
      Exists vret.
      entailer!.
      simpl partial_tree_rep.
      Exists p_gfa p_oppo.
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
      (* TODO: 涓婁竴娈佃瘉鏄庨噸澶嶅お澶氾紝鑰冭檻浼樺寲銆� *)
    }
  }
Qed.

(* proof for right_rotate_wrap *)
Theorem body_right_rotate_wrap:
  semax_body Vprog Gprog f_right_rotate_wrap right_rotate_wrap_spec.
Proof.
  start_function.
  simpl rbtree_rep.
  Intros p_lch p_rch.
  forward.
  forward_if.                     (* if (r->fa == NULL) *)
  { (* r is the root *) 
    forward_call 
    (col_l, key_l, value_l, tag_l, 
      col_r, key_r, value_r, tag_r, fa_r, 
      ta, tb, tc, 
      l, r, pc).
    {
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
    }
    Intros vret.
    simpl rbtree_rep.
    clear p_lch. clear p_rch.
    Intros p_lch p_rch.
    subst.
    destruct hft_list.
    2: {
      (* show that hft_list = [] *)
      destruct h as [[[[[vacancy_gfa c_gfa] k_gfa] v_gfa] tg_gfa] oppo_fa_tbd].
      simpl partial_tree_rep.
      Intros p_gfa p_oppo.
      sep_apply data_at_nullval.
      Intros. contradiction.
    }
    simpl partial_tree_rep.
    Intros.
    forward.                      (* *root = right_rotate(r); *)
    Exists vret.
    entailer!.
    simpl partial_tree_rep.
    simpl rbtree_rep.
    Exists p_lch p_rch.
    entailer!.
  }
  {
    forward.
    destruct hft_list.
    { (* show that hft_list <> [] *)
      simpl partial_tree_rep.
      Intros.
      contradiction.
    }
    destruct h as [[[[[vacancy_fa c_fa] k_fa] v_fa] tg_fa] oppo_tbd].
    simpl partial_tree_rep.
    Intros p_gfa p_oppo.
    forward.
    { destruct vacancy_fa; entailer!. }
    forward_if.
    { destruct vacancy_fa; entailer!. }
    {
      (* r is the left branch *)
      destruct vacancy_fa.
      { (* verify that r is on the left *)
        subst r.
        destruct oppo_tbd.
        - simpl rbtree_rep. Intros.
          subst p_oppo.
          assert_PROP (False). { entailer!. }
          contradiction.
        - simpl rbtree_rep. 
          Intros p_lch0 p_rch0.
          sep_apply data_at_conflict; [apply sepalg_Tsh| ].
          sep_apply FF_local_facts.
          Intros.
          contradiction.
      }
      subst.
      forward_call 
      (col_l, key_l, value_l, tag_l, 
        col_r, key_r, value_r, tag_r, fa_r, 
        ta, tb, tc, 
        l, r, pc).
      {
        simpl rbtree_rep.
        Exists p_lch p_rch.
        entailer!.
      }
      Intros vret.
      simpl rbtree_rep.
      clear p_lch. clear p_rch.
      Intros p_lch p_rch.
      forward.                    (* r_fa->left = right_rotate(r); *)
      Exists vret.
      entailer!.
      simpl partial_tree_rep.
      Exists p_gfa p_oppo.
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
    }
    {
      (* r is the right branch *)
      destruct vacancy_fa; [ | contradiction ].
      forward_call 
      (col_l, key_l, value_l, tag_l, 
        col_r, key_r, value_r, tag_r, fa_r, 
        ta, tb, tc, 
        l, r, pc).
      {
        simpl rbtree_rep.
        Exists p_lch p_rch.
        entailer!.
      }
      Intros vret.
      simpl rbtree_rep.
      clear p_lch. clear p_rch.
      Intros p_lch p_rch.
      forward.                    (* r_fa->right = right_rotate(r); *)
      Exists vret.
      entailer!.
      simpl partial_tree_rep.
      Exists p_gfa p_oppo.
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
      (* TODO: 涓婁竴娈佃瘉鏄庨噸澶嶅お澶氾紝鑰冭檻浼樺寲銆� *)
    }
  }
Qed.

(* proof for solve_double_red, tedious *)
Theorem body_solve_double_red: 
  semax_body Vprog Gprog f_solve_double_red solve_double_red_spec.
Proof.
  start_function.
  unfold treebox_rep.
  Intros p_initial.
  forward.
  forward_loop
  (EX t : RBtree, 
  EX hft_list : list Half_tree, 
  EX p : val, 
  EX p_fa : val,
  PROP (t <> Empty; balance' hft_list_initial t_initial = balance' hft_list t)
  LOCAL (temp _root root; temp _p p)
  SEP (rbtree_rep t p p_fa *
    partial_tree_rep hft_list root p p_fa)).
  {
    Exists t_initial.
    Exists hft_list_initial.
    Exists p_initial p_fa_initial.
    entailer!.
    apply partialtreebox_partialtree.
  }
  { 
    Intros t hft_list.
    Intros p p_fa.
    destruct t eqn:E.
    { (* remove the impossible case *)
      exfalso. apply H0. reflexivity. }
    rename t0 into tg.
    simpl rbtree_rep at 1.
    Intros p_lch p_rch. 
    forward.            (* p_fa = (p -> fa); *)
    forward_if.         (* if (p_fa == NULL) *)
    {
      forward.          (* return; *)
      Exists (T c r1 k v tg r2).
      Exists hft_list.
      unfold treebox_rep.
      Exists root nullval. 
      Exists p.
      destruct hft_list eqn:E'.
      - simpl partial_treebox_rep.
        simpl partial_tree_rep.
        Intros.
        rewrite H1.
        simpl balance' at 1.
        simpl rbtree_rep.
        Exists p_lch p_rch.
        entailer!.
      - destruct h as [[[[[vacancy col] key_] value_] tag_] opposite].
        simpl partial_treebox_rep.
        simpl partial_tree_rep.
        destruct vacancy;
        Intros p_gfa p_opposite.
        + assert_PROP (False). { entailer!. } destruct H6.
        + assert_PROP (False). { entailer!. } destruct H6.
    }
    {
      (* second branch: p_fa is not NULL *)
      destruct hft_list eqn:E'.
      { 
        simpl partial_tree_rep.
        Intros. contradiction.
      }
      destruct h as [[[[[vacancy_fa c_fa] k_fa] v_fa] tg_fa] oppo_tbd].
      simpl partial_tree_rep.
      Intros p_gfa p_oppo.
      forward.        (* p_gfa = p_fa->fa; *)
      forward_if.     (* if (p_gfa == NULL) *)
      {
        (* p_gfa is null, then return *)
        forward.      (* return ; *)
        Exists (T c r1 k v tg r2).
        Exists ((vacancy_fa, c_fa, k_fa, v_fa, tg_fa, oppo_tbd) :: l).
        destruct l eqn:E''.
        - rewrite H1.
          simpl balance' at 1.
          simpl partial_tree_rep.
          destruct vacancy_fa;
            [Exists (field_address t_struct_rbtree [StructField _right] p_fa) p_fa |
            Exists (field_address t_struct_rbtree [StructField _left] p_fa) p_fa];
            unfold treebox_rep;
            Exists p;
            simpl rbtree_rep;
            Exists p_lch p_rch;
            simpl partial_treebox_rep;
            Exists nullval p_oppo root;
            unfold_data_at (data_at _ _ _ p_fa);
            entailer!.
        - (* remove this case *)
          destruct h as [[[[[vacancy' c_gfa] k_gfa] v_gfa] t_gfa] oppo_fa_tbd].
          simpl partial_treebox_rep.
          simpl partial_tree_rep.
          destruct vacancy'; Intros p_gfa p_oppo0.
          (* solve these due to null storation. *)
          + assert_PROP (False). { entailer!. } contradiction.
          + assert_PROP (False). { entailer!. } contradiction.
      }
      { 
        (* otherwise, p_gfa is not null *)
        assert_PROP (l <> []).
        {
          destruct l eqn:E''.
          - simpl partial_tree_rep.
            Intros.
            contradiction.
          - entailer!. discriminate.
        }
        destruct l.
        { (* eliminate the case that l = [] *)
          contradiction. 
        }
        destruct h as [[[[[vacancy_gfa c_gfa] k_gfa] v_gfa] tg_gfa] oppo_fa_tbd].
        simpl partial_tree_rep.
        assert_PROP (is_pointer_or_null p_gfa) as H_ispn_gfa.
        { 
          (* will use this later *)
          entailer!. 
        } 
        Intros p_ggfa p_fa_oppo.
        forward.
        forward_if.           (* if (p_fa->color == BLACK) *)
        {
          (* there is no need to go upward *)
          color_replace.
          forward.    (* return ; *)
          Exists (T c r1 k v tg r2).
          Exists ((vacancy_fa, Black, k_fa, v_fa, tg_fa, oppo_tbd)
            :: (vacancy_gfa, c_gfa, k_gfa, v_gfa, tg_gfa, oppo_fa_tbd) :: l).
          destruct vacancy_fa.
          + Exists (field_address t_struct_rbtree [StructField _right] p_fa) p_fa.
            rewrite H1.
            unfold treebox_rep.
            Exists p.
            simpl rbtree_rep.
            Exists p_lch p_rch.
            simpl partial_treebox_rep.
            Exists p_gfa p_oppo.
            sep_apply partialtree_partialtreebox.
            Intros b_fa. 
            destruct vacancy_gfa;
              [Exists (field_address t_struct_rbtree [StructField _right] p_gfa) |
               Exists (field_address t_struct_rbtree [StructField _left] p_gfa)];
              Exists p_ggfa p_fa_oppo b_fa;
              unfold_data_at (data_at _ _ _ p_fa);
              unfold_data_at (data_at _ _ _ p_gfa);
              entailer!.
          + Exists (field_address t_struct_rbtree [StructField _left] p_fa) p_fa.
            rewrite H1.
            unfold treebox_rep.
            Exists p.
            simpl rbtree_rep.
            Exists p_lch p_rch.
            simpl partial_treebox_rep.
            Exists p_gfa p_oppo.
            sep_apply partialtree_partialtreebox.
            Intros b_fa. 
            destruct vacancy_gfa;
              [Exists (field_address t_struct_rbtree [StructField _right] p_gfa) |
               Exists (field_address t_struct_rbtree [StructField _left] p_gfa)];
              Exists p_ggfa p_fa_oppo b_fa;
              unfold_data_at (data_at _ _ _ p_fa);
              unfold_data_at (data_at _ _ _ p_gfa);
              entailer!.
        }
        {
          (* otherwise go upward *)
          assert_PROP (tc_val (tptr (Tstruct _tree noattr))
            (if vacancy_fa then p_oppo else p)) as H_p1.
          { destruct vacancy_fa; entailer!. }
          assert_PROP (tc_val (tptr (Tstruct _tree noattr))
            (if vacancy_fa then p else p_oppo)) as H_p2.
          { destruct vacancy_fa; entailer!. }
          assert_PROP (tc_val (tptr (Tstruct _tree noattr))
            (if vacancy_gfa then p_fa_oppo else p_fa)) as H_p3.
          { destruct vacancy_gfa; entailer!. }
          assert_PROP (tc_val (tptr (Tstruct _tree noattr))
            (if vacancy_gfa then p_fa else p_fa_oppo)) as H_p4.
          { destruct vacancy_gfa; entailer!. }
          (* TODO锛氳繖涓婇潰閮芥槸杈呭姪鎬х殑銆�*)
          
          forward.
          forward_if.       (* if (p == p_fa->left) *)
          { destruct vacancy_fa; entailer!. }
          {
            (* TODO锛氳繖閲屾槸鍏堟姽鎺夊彟涓€绉嶅彲鑳� *)
            destruct vacancy_fa.
            {
              (* eliminate the case *)
              subst p.
              destruct oppo_tbd.
              - simpl rbtree_rep. Intros.
                subst p_oppo.
                assert_PROP (False). { entailer!. }
                contradiction.
              - simpl rbtree_rep. 
                Intros p_lch0 p_rch0.
                sep_apply data_at_conflict; [apply sepalg_Tsh| ].
                sep_apply FF_local_facts.
                Intros.
                contradiction.
            }
            (* do some renaming *)
            rename p_oppo into p_fa_rch.
            rename oppo_tbd into t_fa_rch.
            forward.
            forward_if.     (* if (p_fa == p_gfa->left) *)
            { destruct vacancy_gfa; entailer!. }
            { 
              (* TODO锛氳繖閲屾槸鍏堟姽鎺夊彟涓€绉嶅彲鑳� *)
              destruct vacancy_gfa.
              {
                subst p_fa.
                destruct oppo_fa_tbd.
                - simpl rbtree_rep. Intros.
                  subst p_fa_oppo.
                  assert_PROP (False). { entailer!. }
                  contradiction.
                - simpl rbtree_rep. 
                  Intros p_lch0 p_rch0.
                  sep_apply (data_at_conflict Tsh t_struct_rbtree
                  (Vint (Int.repr (Col2Z c0)),
                  (Vint (Int.repr k0),
                  (Vint (Int.repr v0),
                  (Vint (Int.repr t0), (p_lch0, (p_rch0, p_gfa))))))
                  (Vint (Int.repr (Col2Z c_fa)),
                  (Vint (Int.repr k_fa),
                  (Vint (Int.repr v_fa),
                  (Vint (Int.repr tg_fa), (p, (p_fa_rch, p_gfa))))))
                  p_fa_oppo sepalg_Tsh).
                  sep_apply FF_local_facts.
                  Intros.
                  contradiction.
              }
              (* do some renaming *)
              rename p_fa_oppo into p_gfa_rch.
              rename oppo_fa_tbd into t_gfa_rch.
              forward.
              forward_call (t_gfa_rch, p_gfa_rch, p_gfa).
              color_replace.
              forward_if.     (* if (get_color(p_gfa->right) != RED) *)
              {
                (* perform rotations *)
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p_fa->color = BLACK; *)
                assert_PROP (is_pointer_or_null p_ggfa) as H_pggfa by entailer!.
                forward_call 
                (Black, k_fa, v_fa, tg_fa, 
                  Red, k_gfa, v_gfa, tg_gfa, p_ggfa, 
                  (T c r1 k v tg r2), t_fa_rch, t_gfa_rch,  
                  p_fa, p_gfa, 
                  p_gfa_rch, root, l).
                {   
                  simpl rbtree_rep.
                  Exists p p_fa_rch.
                  Exists p_lch p_rch.
                  entailer!.
                }
                Intros vret.
                forward.        (* return; *)
                Exists (T Black (T c r1 k v tg r2) k_fa v_fa tg_fa
                  (T Red t_fa_rch k_gfa v_gfa tg_gfa t_gfa_rch)).
                sep_apply partialtree_partialtreebox.
                Intros b.
                Exists l b p_ggfa.
                entailer!.
                {
                  rewrite H1. destruct t_gfa_rch.
                  - simpl balance'. reflexivity.
                  - simpl get_color_tree in *. color_replace. 
                    simpl balance'. reflexivity.
                }
                unfold treebox_rep.
                Exists p_fa.
                simpl rbtree_rep.
                Exists vret p_gfa.
                Intros p_lch0 p_rch0 p_lch1 p_rch1.
                Exists p_lch0 p_rch0 p_lch1 p_rch1.
                entailer!.
              }
              {
                (* otherwise change color and push up *)
                destruct t_gfa_rch.
                { 
                  (* will not be empty *)
                  simpl get_color_tree in *.
                  inversion H8.
                }
                destruct c0; [| inversion H8].
                simpl rbtree_rep.
                Intros p_gfa_rch_lch p_gfa_rch_rch.
                forward.          (* p_fa->color = BLACK; *)
                forward.
                forward.          (* p_gfa->left->color = BLACK; *)
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p = p_gfa; *)
                simpl balance' in H1.
                Exists 
                (T Red (T Black (T c r1 k v tg r2) k_fa v_fa tg_fa t_fa_rch)
                  k_gfa v_gfa tg_gfa (T Black t_gfa_rch1 k0 v0 t0 t_gfa_rch2)).
                Exists l.
                Exists p_gfa p_ggfa.
                simpl rbtree_rep.
                Exists p_fa p_gfa_rch.
                Exists p_gfa_rch_lch p.
                Exists p_gfa_rch_rch p_fa_rch.
                Exists p_lch p_rch.
                entailer!.
                discriminate.
              }
            }
            { 
              (* TODO锛氳繖閲屾槸鍏堟姽鎺夊彟涓€绉嶅彲鑳� *)
              destruct vacancy_gfa; [| contradiction ].
              rename p_fa_oppo into p_gfa_lch.
              rename oppo_fa_tbd into t_gfa_lch.
              forward.
              forward_call (t_gfa_lch, p_gfa_lch, p_gfa).
              forward_if. 
              {
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p_fa->color = BLACK; *)
                forward_call
                (Black, k, v, tg, 
                  c_fa, k_fa, v_fa, tg_fa, p_gfa, 
                  r1, r2, t_fa_rch, 
                  p, p_fa, 
                  p_fa_rch). 
                {
                  simpl rbtree_rep.
                  Exists p_lch p_rch.
                  entailer!.
                }
                Intros vret.
                simpl rbtree_rep.
                Intros p_fa_lch0 p_fa_rch0.
                forward.
                assert_PROP (is_pointer_or_null p_ggfa) as H_pggfa by entailer!.
                forward_call 
                (Red, k_gfa, v_gfa, tg_gfa, p_ggfa, 
                  Black, k, v, tg,  
                  t_gfa_lch, r1, (T c_fa r2 k_fa v_fa tg_fa t_fa_rch),
                  p_gfa, p, 
                  p_gfa_lch, root, l). 
                {   
                  simpl rbtree_rep.
                  Exists vret p_fa.
                  Exists p_fa_lch0 p_fa_rch0.
                  entailer!.
                }
                Intros vret0.
                forward.        (* return; *)
                Exists (T Black (T Red t_gfa_lch k_gfa v_gfa tg_gfa r1) k v tg
                  (T Red r2 k_fa v_fa tg_fa t_fa_rch)).
                sep_apply partialtree_partialtreebox.
                Intros b.
                Exists l b p_ggfa.
                color_replace.
                entailer!.
                {
                  rewrite H1. destruct t_gfa_lch.
                  - simpl balance'. reflexivity.
                  - simpl get_color_tree in *. color_replace. 
                    simpl balance'. reflexivity.
                }
                unfold treebox_rep.
                Exists p.
                simpl rbtree_rep.
                Exists p_gfa vret0.
                Intros p_lch0 p_rch0 p_lch1 p_rch1.
                Exists p_lch1 p_rch1 p_lch0 p_rch0.
                entailer!.
              }
              {
                (* otherwise change color and push up *)
                destruct t_gfa_lch.
                { 
                  (* will not be empty *)
                  simpl get_color_tree in *.
                  inversion H11.
                }
                destruct c0; [| inversion H11].
                simpl rbtree_rep.
                Intros p_gfa_lch_lch p_gfa_lch_rch.
                forward.          (* p_fa->color = BLACK; *)
                forward.
                forward.          (* p_gfa->right->color = BLACK; *)
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p = p_gfa; *)
                simpl balance' in H1.
                apply col_not_0 in H8.
                rewrite H8 in H1.
                Exists 
                (T Red (T Black t_gfa_lch1 k0 v0 t0 t_gfa_lch2) k_gfa v_gfa
                  tg_gfa (T Black (T c r1 k v tg r2) k_fa v_fa tg_fa t_fa_rch)).
                Exists l.
                Exists p_gfa p_ggfa.
                simpl rbtree_rep.
                Exists p_gfa_lch p_fa.
                Exists p p_gfa_lch_lch.
                Exists p_fa_rch p_gfa_lch_rch.
                Exists p_lch p_rch.
                entailer!.
                discriminate.
              }
            }
          }
          { 
            (* TODO: 杩欓噷鍏堟姽鎺夊彟涓€绉嶅彲鑳� *)
            destruct vacancy_fa; [| contradiction ].
            (* do some renaming *)
            rename p_oppo into p_fa_lch.
            rename oppo_tbd into t_fa_lch.
            forward.
            forward_if.     (* if (p_fa == p_gfa->left) *)
            { destruct vacancy_gfa; entailer!. }
            {
              (* TODO锛氳繖閲屾槸鍏堟姽鎺夊彟涓€绉嶅彲鑳� *)
              destruct vacancy_gfa.
              {
                subst p_fa.
                destruct oppo_fa_tbd.
                - simpl rbtree_rep. Intros.
                  subst p_fa_oppo.
                  assert_PROP (False). { entailer!. }
                  contradiction.
                - simpl rbtree_rep. 
                  Intros p_lch0 p_rch0.
                  sep_apply (data_at_conflict Tsh t_struct_rbtree
                  (Vint (Int.repr (Col2Z c0)),
                  (Vint (Int.repr k0),
                  (Vint (Int.repr v0),
                  (Vint (Int.repr t0), (p_lch0, (p_rch0, p_gfa))))))
                  (Vint (Int.repr (Col2Z c_fa)),
                  (Vint (Int.repr k_fa),
                  (Vint (Int.repr v_fa),
                  (Vint (Int.repr tg_fa), (p_fa_lch, (p, p_gfa))))))
                  p_fa_oppo sepalg_Tsh).
                  sep_apply FF_local_facts.
                  Intros.
                  contradiction.
              }
              (* do some renaming *)
              rename p_fa_oppo into p_gfa_rch.
              rename oppo_fa_tbd into t_gfa_rch.
              forward.
              forward_call (t_gfa_rch, p_gfa_rch, p_gfa).
              forward_if. 
              {
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p_fa->color = BLACK; *)
                forward_call
                (c_fa, k_fa, v_fa, tg_fa, p_gfa, 
                  Black, k, v, tg, 
                  t_fa_lch, r1, r2,
                  p_fa, p, 
                  p_fa_lch).
                {
                  simpl rbtree_rep.
                  Exists p_lch p_rch.
                  entailer!.
                }
                Intros vret.
                simpl rbtree_rep.
                Intros p_fa_lch0 p_fa_rch0.
                forward.
                assert_PROP (is_pointer_or_null p_ggfa) as H_pggfa by entailer!.
                forward_call 
                (Black, k, v, tg, 
                  Red, k_gfa, v_gfa, tg_gfa, p_ggfa, 
                  (T c_fa t_fa_lch k_fa v_fa tg_fa r1), r2, t_gfa_rch,
                  p, p_gfa, 
                  p_gfa_rch, root, l).
                {
                  simpl rbtree_rep.
                  Exists p_fa vret.
                  Exists p_fa_lch0 p_fa_rch0.
                  entailer!.
                }
                Intros vret0.
                forward.          (* return; *)
                Exists (T Black (T Red t_fa_lch k_fa v_fa tg_fa r1) 
                    k v tg (T Red r2 k_gfa v_gfa tg_gfa t_gfa_rch)).
                sep_apply partialtree_partialtreebox.
                Intros b.
                Exists l b p_ggfa.
                color_replace.
                entailer!.
                {
                  rewrite H1. destruct t_gfa_rch.
                  - simpl balance'. reflexivity.
                  - simpl get_color_tree in *. color_replace. 
                    simpl balance'. reflexivity.
                }
                unfold treebox_rep.
                Exists p.
                simpl rbtree_rep.
                Exists vret0 p_gfa.
                Intros p_lch0 p_rch0 p_lch1 p_rch1.
                Exists p_lch0 p_rch0 p_lch1 p_rch1.
                entailer!.
              }
              {
                (* otherwise change color and push up *)
                destruct t_gfa_rch.
                { 
                  (* will not be empty *)
                  simpl get_color_tree in *.
                  inversion H11.
                }
                destruct c0; [| inversion H11].
                simpl rbtree_rep.
                Intros p_gfa_rch_lch p_gfa_rch_rch.
                forward.          (* p_fa->color = BLACK; *)
                forward.
                forward.          (* p_gfa->right->color = BLACK; *)
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p = p_gfa; *)
                simpl balance' in H1.
                color_replace.
                Exists 
                (T Red (T Black t_fa_lch k_fa v_fa tg_fa (T c r1 k v tg r2))
                  k_gfa v_gfa tg_gfa (T Black t_gfa_rch1 k0 v0 t0 t_gfa_rch2)).
                Exists l.
                Exists p_gfa p_ggfa.
                simpl rbtree_rep.
                Exists p_fa p_gfa_rch.
                Exists p_gfa_rch_lch p_fa_lch. 
                Exists p_gfa_rch_rch p.
                Exists p_lch p_rch.
                entailer!.
                discriminate.
              }
            }
            {
              (* TODO锛氳繖閲屾槸鍏堟姽鎺夊彟涓€绉嶅彲鑳� *)
              destruct vacancy_gfa; [| contradiction ].
              (* do some renaming *)
              rename p_fa_oppo into p_gfa_lch.
              rename oppo_fa_tbd into t_gfa_lch.

              forward.
              forward_call (t_gfa_lch, p_gfa_lch, p_gfa).
              color_replace.
              forward_if.         (* if (get_color(p_gfa->left) != RED) *)
              {
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p_fa->color = BLACK; *)
                assert_PROP (is_pointer_or_null p_ggfa) as H_pggfa by entailer!.
                forward_call 
                (Red, k_gfa, v_gfa, tg_gfa, p_ggfa, 
                  Black, k_fa, v_fa, tg_fa, 
                  t_gfa_lch, t_fa_lch, (T c r1 k v tg r2), 
                  p_gfa, p_fa, 
                  p_gfa_lch, root, l).
                {   
                  simpl rbtree_rep.
                  Exists p_fa_lch p.
                  Exists p_lch p_rch.
                  entailer!.
                }
                Intros vret.
                forward.        (* return; *)
                Exists (T Black 
                    (T Red t_gfa_lch k_gfa v_gfa tg_gfa t_fa_lch)
                      k_fa v_fa tg_fa
                      (T c r1 k v tg r2)).
                sep_apply partialtree_partialtreebox.
                Intros b.
                Exists l b p_ggfa.
                entailer!.
                {
                  rewrite H1. destruct t_gfa_lch.
                  - simpl balance'. reflexivity.
                  - simpl get_color_tree in *. color_replace. 
                    simpl balance'. reflexivity.
                }
                unfold treebox_rep.
                Exists p_fa.
                simpl rbtree_rep.
                Exists p_gfa vret.
                Intros p_lch0 p_rch0 p_lch1 p_rch1.
                Exists p_lch1 p_rch1 p_lch0 p_rch0.
                entailer!.
              }
              {
                (* otherwise change color and push up *)
                destruct t_gfa_lch.
                { 
                  (* will not be empty *)
                  simpl get_color_tree in *.
                  inversion H8.
                }
                destruct c0; [| inversion H8].
                simpl rbtree_rep.
                Intros p_gfa_lch_lch p_gfa_lch_rch.
                forward.          (* p_fa->color = BLACK; *)
                forward.
                forward.          (* p_gfa->left->color = BLACK; *)
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p = p_gfa; *)
                simpl balance' in H1.
                Exists 
                (T Red (T Black t_gfa_lch1 k0 v0 t0 t_gfa_lch2) k_gfa v_gfa tg_gfa
                  (T Black t_fa_lch k_fa v_fa tg_fa (T c r1 k v tg r2))).
                Exists l.
                Exists p_gfa p_ggfa.
                simpl rbtree_rep.
                Exists p_gfa_lch p_fa.
                Exists p_fa_lch p_gfa_lch_lch.
                Exists p p_gfa_lch_rch.
                Exists p_lch p_rch.
                entailer!. 
                discriminate.
              }
            }
          }
        }
      }
    }
  }
Qed.

Theorem body_tree_minimum: semax_body Vprog Gprog f_tree_minimum tree_minimum_spec.
Proof. 
  start_function.
  forward_loop
  (EX t' : RBtree, 
    EX hft_list' : list Half_tree, 
    EX p_fa' : val,
    EX b' : val, 
    PROP (Up_split (minimum_split default t_tree hft_list) = 
      Up_split (minimum_split default t' hft_list'); 
      t' <> Empty)
    LOCAL (temp _t b')
    SEP (treebox_rep t' b' p_fa';
    partial_treebox_rep hft_list' root b' p_fa')).
  {
    Exists t_tree hft_list p_fa b.
    entailer!.
  }
  { 
    Intros t' hft_list' p_fa' b'.
    destruct t'; [ contradiction | ].
    unfold treebox_rep.
    Intros p.
    simpl rbtree_rep.
    Intros p_lch p_rch.
    forward.              (* tmp = *t; *)
    forward_call (c, k, v, t, p_lch, p_rch, p_fa', p, t'1, t'2).
                          (* pushdown(tmp); *)
    forward.
    forward_if.
    { 
      subst p_lch.
      destruct t'1.
      2: { 
        simpl rbtree_rep at 1. 
        Intros p_lch p_rch0.
        assert_PROP (False) by entailer!.
        Intros. contradiction.
      }
      forward.            (* return; *)
      Exists b' (T c Empty k (v + t) default (tag_tree_t t t'2)) p_fa' hft_list'.
      entailer!.
      - rewrite H0.
        simpl.
        strip_0.
        reflexivity.
      - unfold treebox_rep.
        Exists p.
        simpl rbtree_rep.
        Exists nullval p_rch.
        entailer!.
    }
    {
      destruct t'1 eqn:Et'1.
      { 
        simpl rbtree_rep at 1.
        Intros. contradiction.
      }
      forward.            (* t = &(tmp->left); *)
      Exists (tag_tree_t t t'1)
        ((false, c, k, (v + t), default, (tag_tree_t t t'2)) :: hft_list').
      Exists p (offset_val 16 p).
      entailer!.
      - rewrite H0.
        unfold minimum_split.
        simpl.
        split; [ | intro; discriminate ].
        do 4 f_equal.
        + do 3 f_equal. lia.
        + do 4 f_equal. lia.
      - unfold treebox_rep.
        Exists p_lch.
        simpl rbtree_rep.
        Intros p_lch0 p_rch0.
        Exists p_lch0 p_rch0.
        simpl partial_treebox_rep.
        Exists p_fa' p_rch b'.
        entailer!;
        replace (offset_val 16 p)
          with (field_address t_struct_rbtree [StructField _left] p)
          by (unfold field_address; simpl;
          rewrite if_true by auto with field_compatible; auto).
        + reflexivity.
        + unfold_data_at (data_at _ _ _ p).
          entailer!.
    }
  }
Qed.