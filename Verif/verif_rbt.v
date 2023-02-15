Require Import VST.floyd.proofauto.
Require Import RBT.Verif.verif_rbt_toolbox.
Require Import RBT.Verif.rbt.
Require Import Coq.Init.Tauto.

Require Import RBT.Verif.RBtree_Type.
Require Import RBT.Verif.RBtree_Definition.
Require Import RBT.Verif.Half_Tree.
Require Import RBT.Verif.relation_map.
Require Import RBT.Verif.Abstract.
Require Import RBT.Verif.general_split.
Require Import RBT.Verif.Insert.
Require Import RBT.Verif.lookup.
Require Import RBT.Verif.SegmentChange.
Require Import RBT.Verif.Delete.
Require Import RBT.Verif.Delete_check.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** Notations.

    To further simplify notations in VST, we customize some notations
    here.
*)

Definition t_struct_rbtree := Tstruct _tree noattr.

(** Environment setting.

    Here, we instantiate a red-black tree for the C implementation. 
    Keys, values and tags are all set to Z. And related properties
    are also set to those about Z.
*)

Instance Reb_Z : Reb Z := {
  Equal_bool x y := Z.eqb x y
}.

Instance Rlt_Z : Rlt Z := {
  lt_prop x y := Z.lt x y
}.

Instance Rltb_Z : Rltb Z := {
  lt_bool x y := Z.ltb x y
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
  intros. lia.
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
  - intros. destruct H as [H H']. lia.
  - intros. split; lia.
Qed.

Lemma lte_complete_Z: forall x y, (@lte_prop Z Rlt_Z x y) \/ (@lte_prop Z Rlt_Z y x).
Proof.
  intros. unfold lte_prop.
  simpl.
  lia.
Qed.

Program Instance C_RBT : RBtree_setting := {
  Key := Z;
  Value := Z;
  Tag := Z;

  KRb := Reb_Z;
  VRb := Reb_Z;
  LKR := Rlt_Z;
  LKRb := Rltb_Z;

  f v t := v + t;
  Optt t1 t2 := t1 + t2;

  default := 0
}.
Next Obligation.
  unfold Rb_spec. 
  intros. split; intros.
  - rewrite Z.eqb_eq. auto.
  - rewrite <- Z.eqb_eq. auto.
Qed.
Next Obligation.
  unfold Rltb_spec.
  intros. split; intros.
  - rewrite Z.ltb_lt. auto.
  - rewrite <- Z.ltb_lt. auto.
Qed.
Next Obligation.
  unfold Rlt_R.
  intros. split; intros.
  - destruct H. rewrite Z.nlt_ge in H, H0. 
    lia.
  - split; intro; subst y; pose proof (Z.lt_irrefl x); auto.
Qed.
Next Obligation.
  lia.
Qed.
Next Obligation.
  lia.
Qed.
(* Next Obligation. 
  lia.
Qed. *)
Next Obligation. 
  exists (k - 1)%Z. lia.
Qed.
Next Obligation. 
  exists (k + 1)%Z. lia.
Qed.
Program Instance C_RBT_comm : RBtree_with_tag_comm  := {}.
Next Obligation. 
  lia.
Qed.

(** Use Z to represent color. *)
Definition RED_COLOR : Z := 1.
Definition BLACK_COLOR : Z := 0.

Definition Col2Z (c : color) : Z :=  
  match c with
  | Red   => RED_COLOR
  | Black => BLACK_COLOR
  end.

Definition get_color_tree (t: RBtree) : Z :=
  match t with  
  | T c t1 k v tag t2 => Col2Z c
  | E => -1
  end.

Definition turn_left (h : Half_tree) : Prop :=
  let '(va, c, k, v, tg, oppo) := h in va = false.

Definition tag_default (h : Half_tree) : Prop :=
  let '(va, c, k, v, tg, oppo) := h in tg = default.

(* turn the result of the functional lookup to the C one *)
Definition Lookup2Z (x : Key) (t : RBtree) : Z :=
  match lookup x t with
  | None => 0%Z
  | Some v  => v
  end.

(* reverse the two arguments of complete_tree *)
Definition complete_tree_revarg (p : RBtree * (list Half_tree)) :=
  complete_tree (snd p) (fst p).

(** Representation predicates. 

    To describe red-black trees in memory, we need to define representation 
    predicates. In this part, we define predicates for both trees and partial 
    trees, with basic separating conjunctions. 
*)

(** For red-black trees. *)
Fixpoint rbtree_rep (t : RBtree) (p p_par : val) : mpred :=
  match t with
  | T c lch k v tg rch => 
    !! (Int.min_signed <= k <= Int.max_signed /\ 
      is_pointer_or_null p_par) &&
    EX p_lch : val, EX p_rch : val, 
    data_at Tsh t_struct_rbtree 
      (Vint (Int.repr (Col2Z c)), 
        (Vint (Int.repr k), 
          (Vint (Int.repr v), 
            (Vint (Int.repr tg), 
              (p_lch, (p_rch, p_par)))))) p
    * rbtree_rep lch p_lch p * rbtree_rep rch p_rch p
  | E => !! (p = nullval /\ is_pointer_or_null p_par) && emp 
  end.

(** For treeboxes. *)
Definition treebox_rep (t : RBtree) (b p_par : val) :=
  EX p : val, data_at Tsh (tptr t_struct_rbtree) p b * rbtree_rep t p p_par.

(** For partial trees. *)
Fixpoint partial_tree_rep (t : list Half_tree) (p_root p p_par p_top : val) : mpred :=
  match t with
  | [] => !! (p = p_root /\ p_par = p_top) && emp
  | (va, c, k, v, tg, sib) :: l  =>
    EX p_gpar: val, EX p_sib : val, 
        !! (Int.min_signed <= k <= Int.max_signed) &&
        rbtree_rep sib p_sib p_par *
        partial_tree_rep l p_root p_par p_gpar p_top *
        data_at Tsh t_struct_rbtree
        (Vint (Int.repr (Col2Z c)), 
          (Vint (Int.repr k), 
            (Vint (Int.repr v), 
              (Vint (Int.repr tg), 
                ((if va then p_sib else p), 
                ((if va then p else p_sib), p_gpar)))))) p_par
  end.

(** For partial treeboxes. *)
Fixpoint partial_treebox_rep (t : list Half_tree) (root b p_par p_top : val) : mpred :=
  match t with
  | [] => !! (p_par = p_top /\ root = b /\ is_pointer_or_null root) && emp 
  | (va, c, k, v, tg, sib) :: l  =>
    EX p_gpar: val, EX p_sib : val, EX b_par : val,
      !! (Int.min_signed <= k <= Int.max_signed) &&
      !! (b = 
        if va 
        then (field_address t_struct_rbtree [StructField _right] p_par)
        else (field_address t_struct_rbtree [StructField _left] p_par)) &&
      rbtree_rep sib p_sib p_par *
      field_at Tsh t_struct_rbtree [StructField _color] (Vint (Int.repr (Col2Z c))) p_par *
      field_at Tsh t_struct_rbtree [StructField _key] (Vint (Int.repr k)) p_par *
      field_at Tsh t_struct_rbtree [StructField _value] (Vint (Int.repr v)) p_par *
      field_at Tsh t_struct_rbtree [StructField _tag] (Vint (Int.repr tg)) p_par *
      (if va
       then (field_at Tsh t_struct_rbtree [StructField _left] p_sib p_par)
       else (field_at Tsh t_struct_rbtree [StructField _right] p_sib p_par)) *
      field_at Tsh t_struct_rbtree [StructField _par] p_gpar p_par *
      data_at Tsh (tptr t_struct_rbtree) p_par b_par *
      partial_treebox_rep l root b_par p_gpar p_top
  end.

(** Function specifications. 

    In this part, we write specifications for C functions. 
    Each specification contains three parts: 
    1.  What abstract objects are given for this function. 
        (WITH section)
    2.  Precondition (PRE section)
    3.  Postcondition (POST section)
*)

(* mallocN *)
Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n : Z
  PRE [ tint ]
     PROP (4 <= n <= Int.max_unsigned)
     PARAMS (Vint (Int.repr n))
     SEP ()
  POST [ tptr tvoid ]
     EX v : val,
     PROP (malloc_compatible n v)
     RETURN (v)
     SEP (memory_block Tsh n v).

(* freeN *)
Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ tptr tvoid , tint]
      PROP() 
      PARAMS (p; Vint (Int.repr n))
      SEP (memory_block Tsh n p)
  POST [ tvoid ]
    PROP () RETURN () SEP ().

(* treebox_new *)
Definition treebox_new_spec :=
 DECLARE _treebox_new
  WITH u : unit
  PRE  [  ]
       PROP() PARAMS() SEP ()
  POST [ tptr (tptr t_struct_rbtree) ]
    EX v : val,
    PROP()
    RETURN (v)
    SEP (data_at Tsh (tptr t_struct_rbtree) nullval v).

(* treebox_free *)
Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH t : RBtree, b : val
  PRE  [ tptr (tptr t_struct_rbtree) ]
       PROP() PARAMS(b) SEP (treebox_rep t b nullval)
  POST [ Tvoid ]
    PROP()
    RETURN ()
    SEP (emp).

(* tree_free *)
Definition tree_free_spec :=
 DECLARE _tree_free
  WITH t : RBtree, p : val, p_par : val
  PRE  [ tptr t_struct_rbtree ]
    PROP() 
    PARAMS (p) 
    SEP (rbtree_rep t p p_par)
  POST [ Tvoid ]
    PROP()
    RETURN ()
    SEP (emp).

(* Optt *)
Definition Optt_spec :=
 DECLARE _Optt
  WITH t1 : Tag, t2 : Tag
  PRE [ tuint , tuint ]
    PROP () 
    PARAMS (Vint (Int.repr t1); Vint (Int.repr t2))
    SEP ()
  POST [ tuint ]
     PROP ()
     RETURN (Vint (Int.repr (Optt t1 t2))) 
     SEP ().

(* Opvt *)
Definition Opvt_spec :=
 DECLARE _Opvt
  WITH v : Value, tg : Tag
  PRE [ tuint , tuint ]
    PROP () 
    PARAMS (Vint (Int.repr v); Vint (Int.repr tg))
    SEP ()
  POST [ tuint ]
     PROP ()
     RETURN (Vint (Int.repr (f v tg)))
     SEP ().

(** Left rotation. 

    Here is a diagram to illustrating the given tree:

       l                          r
      / \                        / \
     /   \                      /   \
    a     r        --->        l     c
         / \                  / \
        /   \                /   \
       b    c               a    b

*)
Definition left_rotate_spec :=
 DECLARE _left_rotate
  WITH 
    col_l : color, key_l : Key, value_l : Value, tag_l : Tag, pl_par : val, 
    col_r : color, key_r : Key, value_r : Value, tag_r : Tag,
    ta : RBtree, tb : RBtree, tc : RBtree, 
    pl : val, pr : val, pa : val, pb : val, pc : val
  PRE [ tptr t_struct_rbtree ]
    PROP (Int.min_signed <= key_l <= Int.max_signed; 
          is_pointer_or_null pl_par) 
    PARAMS (pl) 
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (pr, pl_par)))))) pl;
         data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (pb, (pc, pl)))))) pr;
         rbtree_rep ta pa pl;
         rbtree_rep tb pb pr;
         rbtree_rep tc pc pr)
  POST [ tptr t_struct_rbtree ] 
    PROP ()
    RETURN (pr)
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (pl, (pc, pl_par)))))) pr;
         data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (pb, pr)))))) pl;
         rbtree_rep ta pa pl;
         rbtree_rep tb pb pl;
         rbtree_rep tc pc pr).

(** A wrapper for left_rotate, considering that rotation may change the root. *)
Definition left_rotate_wrap_spec :=
 DECLARE _left_rotate_wrap
  WITH 
    col_l : color, key_l : Key, value_l : Value, tag_l : Tag, pl_par : val, 
    col_r : color, key_r : Key, value_r : Value, tag_r : Tag,  
    ta : RBtree, tb : RBtree, tc : RBtree, 
    pl : val, pr : val, pa : val, pb : val, pc : val, 
    root : val, p_root : val, ls : list Half_tree
  PRE  [ tptr t_struct_rbtree, tptr (tptr t_struct_rbtree) ]
    PROP (Int.min_signed <= key_l <= Int.max_signed; 
          is_pointer_or_null pl_par) 
    PARAMS (pl; root) 
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (pr, pl_par)))))) pl;
         data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (pb, (pc, pl)))))) pr;
         rbtree_rep ta pa pl;
         rbtree_rep tb pb pr;
         rbtree_rep tc pc pr;
         partial_tree_rep ls p_root pl pl_par nullval; 
         data_at Tsh (tptr t_struct_rbtree) p_root root)
  POST [ Tvoid ]
    EX p_root_new : val, 
    PROP (p_root_new = match ls with nil => pr | _ => p_root end)
    RETURN ()
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (pl, (pc, pl_par)))))) pr;
         data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (pb, pr)))))) pl;
         rbtree_rep ta pa pl;
         rbtree_rep tb pb pl;
         rbtree_rep tc pc pr; 
         partial_tree_rep ls p_root_new pr pl_par nullval;
         data_at Tsh (tptr t_struct_rbtree) p_root_new root).

(** Right rotation. 

    Here is a diagram illustrating the given tree:

          r                          l
         / \                        / \
        /   \                      /   \
       l    c         --->        a    r
      / \                             / \
     /   \                           /   \
    a    b                          b    c

*)
Definition right_rotate_spec :=
 DECLARE _right_rotate
  WITH 
    col_l : color, key_l : Key, value_l : Value, tag_l : Tag, 
    col_r : color, key_r : Key, value_r : Value, tag_r : Tag, pr_par : val, 
    ta : RBtree, tb : RBtree, tc : RBtree, 
    pl : val, pr : val, pa : val, pb : val, pc : val
  PRE  [ tptr t_struct_rbtree ]
    PROP (Int.min_signed <= key_r <= Int.max_signed;
          is_pointer_or_null pr_par)
    PARAMS (pr) 
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (pl, (pc, pr_par)))))) pr;
         data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (pb, pr)))))) pl;
         rbtree_rep ta pa pl;
         rbtree_rep tb pb pl;
         rbtree_rep tc pc pr)
  POST [ tptr t_struct_rbtree ]
    PROP ()
    RETURN (pl)
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (pr, pr_par)))))) pl;
         data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (pb, (pc, pl)))))) pr;
         rbtree_rep ta pa pl;
         rbtree_rep tb pb pr;
         rbtree_rep tc pc pr).

(** A wrapper for right_rotate, considering that rotation may change the root. *)
Definition right_rotate_wrap_spec :=
 DECLARE _right_rotate_wrap
  WITH 
    col_l : color, key_l : Key, value_l : Value, tag_l : Tag, 
    col_r : color, key_r : Key, value_r : Value, tag_r : Tag, pr_par : val, 
    ta : RBtree, tb : RBtree, tc : RBtree, 
    pl : val, pr : val, pa : val, pb : val, pc : val, 
    root : val, p_root : val, ls : list Half_tree
  PRE  [ tptr t_struct_rbtree, tptr (tptr t_struct_rbtree) ]
    PROP (Int.min_signed <= key_r <= Int.max_signed;
          is_pointer_or_null pr_par)
    PARAMS (pr; root) 
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (pl, (pc, pr_par)))))) pr;
         data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (pb, pr)))))) pl;
         rbtree_rep ta pa pl;
         rbtree_rep tb pb pl;
         rbtree_rep tc pc pr; 
         partial_tree_rep ls p_root pr pr_par nullval;
         data_at Tsh (tptr t_struct_rbtree) p_root root)
  POST [ Tvoid ]
    EX p_root_new : val, 
    PROP (p_root_new = match ls with nil => pl | _ => p_root end)
    RETURN ()
    SEP (data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_l)), 
              (Vint (Int.repr key_l),
                (Vint (Int.repr value_l), 
                  (Vint (Int.repr tag_l),
                    (pa, (pr, pr_par)))))) pl;
         data_at Tsh t_struct_rbtree 
            (Vint (Int.repr (Col2Z col_r)), 
              (Vint (Int.repr key_r),
                (Vint (Int.repr value_r), 
                  (Vint (Int.repr tag_r),
                    (pb, (pc, pl)))))) pr;
         rbtree_rep ta pa pl;
         rbtree_rep tb pb pr;
         rbtree_rep tc pc pr; 
         partial_tree_rep ls p_root_new pl pr_par nullval;
         data_at Tsh (tptr t_struct_rbtree) p_root_new root).

(* tag_tree_t *)
Definition tag_tree_t_spec :=
 DECLARE _tag_tree_t
  WITH t : RBtree, tg : Tag, p : val, p_par : val
  PRE  [ tptr (Tstruct _tree noattr), tuint ]
    PROP () 
    PARAMS (p; Vint (Int.repr tg)) 
    SEP (rbtree_rep t p p_par)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (rbtree_rep (tag_tree_t tg t) p p_par).

(* pushdown *)
Definition pushdown_spec :=
 DECLARE _pushdown
  WITH 
    c : color, k : Key, v : Value, tg : Tag, 
    p_lch : val, p_rch : val, p_par : val, p : val,
    (* first is the information about the tree *)
    lch : RBtree, rch : RBtree
  PRE  [ tptr t_struct_rbtree ]
    PROP () 
    PARAMS (p) 
    SEP (data_at Tsh t_struct_rbtree
          (Vint (Int.repr (Col2Z c)),
          (Vint (Int.repr k),
          (Vint (Int.repr v),
          (Vint (Int.repr tg),
          (p_lch, (p_rch, p_par)))))) p;
        rbtree_rep lch p_lch p;
        rbtree_rep rch p_rch p)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at Tsh t_struct_rbtree
          (Vint (Int.repr (Col2Z c)),
          (Vint (Int.repr k),
          (Vint (Int.repr (f v tg)),
          (Vint (Int.repr default),
          (p_lch, (p_rch, p_par)))))) p;
        rbtree_rep (tag_tree_t tg lch) p_lch p;
        rbtree_rep (tag_tree_t tg rch) p_rch p).

(* make_black *)
Definition make_black_spec :=
 DECLARE _make_black
  WITH t : RBtree, root : val
  PRE  [ tptr (tptr t_struct_rbtree) ]
    PROP () 
    PARAMS (root) 
    SEP (treebox_rep t root nullval)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (treebox_rep (makeBlack t) root nullval). 

(* get_color *)
Definition get_color_spec :=
 DECLARE _get_color
  WITH t : RBtree, p : val, p_par: val
  PRE  [ tptr t_struct_rbtree ]
    PROP () 
    PARAMS (p) 
    SEP (rbtree_rep t p p_par)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (get_color_tree t)))
    SEP (rbtree_rep t p p_par). 

(* update *)
Definition update_spec :=
  DECLARE _update
  WITH root : val, t : RBtree, tg : Tag, targ_lo : Key, targ_hi : Key
  PRE  [ tptr (tptr (Tstruct _tree noattr)), tuint, tint, tint ]
    PROP (Int.min_signed <= targ_lo <= Int.max_signed;
          Int.min_signed <= targ_hi <= Int.max_signed) 
    PARAMS (root; Vint (Int.repr tg); Vint (Int.repr targ_lo);
            Vint (Int.repr targ_hi)) 
    SEP (treebox_rep t root nullval)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (treebox_rep (change_segment' targ_lo targ_hi tg t 
      Int.min_signed Int.max_signed) root nullval). 

(* update_aux *)
Definition update_aux_spec :=
  DECLARE _update_aux
  WITH p : val, p_par : val, t : RBtree, tg : Tag, 
      targ_lo : Key, targ_hi : Key, lo : Key, hi : Key
  PRE  [ tptr (Tstruct _tree noattr), tuint, tint, tint, 
    tint, tint ]
    PROP (Int.min_signed <= targ_lo <= Int.max_signed;
          Int.min_signed <= targ_hi <= Int.max_signed; 
          Int.min_signed <= lo <= Int.max_signed;
          Int.min_signed <= hi <= Int.max_signed;
          targ_lo <= targ_hi) 
    PARAMS (p; Vint (Int.repr tg); 
            Vint (Int.repr lo);
            Vint (Int.repr hi);
            Vint (Int.repr targ_lo);
            Vint (Int.repr targ_hi)) 
    SEP (rbtree_rep t p p_par)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (rbtree_rep (change_segment' targ_lo targ_hi tg t lo hi) p p_par).

(* tree_minimum *)
Definition tree_minimum_spec :=
 DECLARE _tree_minimum
  WITH t : RBtree, b: val, p_par: val
  PRE  [ tptr (tptr t_struct_rbtree) ]
    PROP (t <> Empty) 
    PARAMS (b) 
    SEP (treebox_rep t b p_par)
  POST [ tptr (tptr t_struct_rbtree) ]
    EX min_b : val, 
    EX min_p_par : val, 
    EX min_ls : list Half_tree,
    EX min_tree_c : color, 
    EX min_tree_k : Key, 
    EX min_tree_v : Value, 
    EX min_tree_sib : RBtree, 
    PROP (Up_split (minimum_split default t nil) =
       (min_ls, T min_tree_c Empty min_tree_k min_tree_v default min_tree_sib); 
       Forall turn_left min_ls; 
       Forall tag_default min_ls)
    RETURN (min_b)
    SEP (treebox_rep (T min_tree_c Empty min_tree_k min_tree_v default min_tree_sib) min_b min_p_par; 
      partial_treebox_rep min_ls b min_b min_p_par p_par). 

(** Rebalance after insertion.

    Both its input and output are sets of treeboxes and 
    partial treeboxes.
*)
Definition insert_balance_spec :=
  DECLARE _insert_balance
  WITH t_initial: RBtree, 
      root: val,
      p_par_initial: val,
      b_initial: val, 
      ls_initial: list Half_tree
  PRE  [ tptr (tptr t_struct_rbtree), 
      tptr (tptr t_struct_rbtree) ]
    PROP (t_initial <> Empty)
    PARAMS (b_initial; root) 
    SEP (treebox_rep t_initial b_initial p_par_initial; 
      partial_treebox_rep ls_initial root b_initial 
        p_par_initial nullval)
  POST [ Tvoid ]
    EX t_balanced: RBtree, 
    EX ls_balanced: list Half_tree, 
    EX b_balanced: val, 
    EX p_par_balanced: val,
    PROP ((ls_balanced, t_balanced) = balance' ls_initial t_initial)
    RETURN ()
    SEP (treebox_rep t_balanced b_balanced p_par_balanced; 
        partial_treebox_rep ls_balanced root b_balanced 
          p_par_balanced nullval).

(** Rebalance after deletion.

    This is much like that of insertion.
*)
Definition delete_balance_spec :=
  DECLARE _delete_balance
  WITH t_initial: RBtree, 
      root: val,
      p_initial : val, 
      p_par_initial : val,
      b_initial: val, 
      ls_initial: list Half_tree
  PRE  [ tptr t_struct_rbtree, 
      tptr t_struct_rbtree,
      tptr (tptr t_struct_rbtree) ]
    PROP (delete_check t_initial ls_initial Black = true)    
    PARAMS (p_initial; p_par_initial; root) 
    SEP (rbtree_rep t_initial p_initial p_par_initial;
      data_at Tsh (tptr t_struct_rbtree) p_initial b_initial;
      partial_treebox_rep ls_initial root b_initial p_par_initial nullval)
  POST [ Tvoid ]
    EX t_balanced: RBtree, 
    EX ls_balanced: list Half_tree, 
    EX b_balanced: val, 
    EX p_par_balanced: val,
    PROP (complete_tree_revarg (t_balanced, ls_balanced) = 
      complete_tree_revarg (delete_balance t_initial ls_initial Black))
    RETURN ()
    SEP (treebox_rep t_balanced b_balanced p_par_balanced; 
        partial_treebox_rep ls_balanced root b_balanced p_par_balanced nullval).

(* insert *)
Definition insert_spec :=
 DECLARE _insert
  WITH t : RBtree, root : val, x : Key, v : Value
  PRE  [ tptr (tptr t_struct_rbtree), tint, tuint ]
    PROP (Int.min_signed <= x <= Int.max_signed) 
    PARAMS (root; Vint (Int.repr x); Vint (Int.repr v))
    SEP (treebox_rep t root nullval)
  POST [ Tvoid ]
    EX t_complete : RBtree, 
    PROP (insert x v t t_complete)
    RETURN ()
    SEP (treebox_rep t_complete root nullval).

(* delete *)
Definition delete_spec :=
 DECLARE _delete
  WITH t : RBtree, root : val, x : Key
  PRE  [ tptr (tptr t_struct_rbtree), tint ]
    PROP (Int.min_signed <= x <= Int.max_signed; 
      let '(ls, base, co) := delete_with_no_balance x t
      in (delete_check base ls co = true))
    PARAMS (root; Vint (Int.repr x))
    SEP (treebox_rep t root nullval)
  POST [ Tvoid ]
    EX t_complete : RBtree, 
    PROP ()
    RETURN ()
    SEP (treebox_rep (delete x t) root nullval).

(* lookup *)
Definition lookup_spec :=
 DECLARE _lookup
  WITH t : RBtree, x : Key, p : val, p_par : val
  PRE  [ tptr t_struct_rbtree, tint ]
    PROP (Int.min_signed <= x <= Int.max_signed; 
      is_pointer_or_null p_par) 
    PARAMS (p; Vint (Int.repr x)) 
    SEP (rbtree_rep t p p_par)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (Lookup2Z x t)))
    SEP (rbtree_rep t p p_par).

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
    insert_balance_spec;    (* OK! *)
    lookup_spec;            (* OK! *)
    update_aux_spec;        (* OK! *)
    update_spec;            (* OK! *) 
    pushdown_spec;          (* OK! *)
    tree_minimum_spec;      (* OK! *)
    delete_balance_spec;    (* OK! *)
    delete_spec             (* OK! *)
  ]).

Definition treemap_rep (mp: relate_map) (b: val) :=
  EX t: RBtree, !! (SearchTree' Int.min_signed t Int.max_signed /\ 
    Abs t mp /\ is_redblack t) && treebox_rep t b nullval. 

Definition abs_treebox_new_spec :=
 DECLARE _treebox_new
  WITH u : unit
  PRE  [  ]
       PROP() PARAMS() SEP ()
  POST [ tptr (tptr t_struct_rbtree) ]
    EX b : val,
    PROP ()
    RETURN (b)
    SEP (treemap_rep relate_default b).

Lemma subsume_treebox_new : funspec_sub (snd treebox_new_spec) (snd abs_treebox_new_spec).
Proof.
  do_funspec_sub.
  clear H.
  Exists emp.
  entailer!.
  intros.
  Exists (eval_id ret_temp x).
  unfold treemap_rep.
  Exists Empty.
  entailer!.
  - split; try split.
    + apply ST_E. apply minsigned_lt_maxsigned.
    + exact Abs_E.
    + unfold is_redblack. split.
      * apply IsRB_co_leaf.
      * exists O. apply IsRB_dep_em.
  - unfold treebox_rep.
    Exists nullval.
    simpl rbtree_rep.
    entailer!.
Qed.

Definition abs_treebox_free_spec :=
 DECLARE _treebox_free
  WITH mp: relate_map, b: val
  PRE  [ tptr (tptr t_struct_rbtree) ]
       PROP() PARAMS(b) SEP (treemap_rep mp b)
  POST [ Tvoid ]
    PROP()
    RETURN()
    SEP (emp).

Lemma subsume_treebox_free : funspec_sub (snd treebox_free_spec) (snd abs_treebox_free_spec).
Proof.
  do_funspec_sub.
  destruct w as [mp b].
  clear H.
  simpl. normalize.
  unfold treemap_rep.
  Intros t. 
  Exists (t, b) emp.
  entailer!.
Qed.

(* insert *)
Definition abs_insert_spec :=
 DECLARE _insert
  WITH mp: relate_map, x: Key, v: Value, b: val
  PRE  [ tptr (tptr t_struct_rbtree), tint, tuint ]
    PROP (Int.min_signed < x < Int.max_signed) 
    PARAMS (b; Vint (Int.repr x); Vint (Int.repr v))
    SEP (treemap_rep mp b)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (treemap_rep (v_update x v mp) b).

Lemma subsume_insert : funspec_sub (snd insert_spec) (snd abs_insert_spec).
Proof.
  do_funspec_sub.
  destruct w as [[[mp x] v] b].
  clear H.
  simpl. normalize.
  unfold treemap_rep.
  Intros t.
  unfold treebox_rep.
  Intros p.
  Exists (t, b, x, v) emp.
  entailer!.
  2: { Exists p. entailer!. }
  intros. 
  Exists x1 x2.
  entailer!.
  split; try split.
  - assert (SearchTree t). { eapply ST_intro; try eassumption. }
    pose proof insert_st t x v x1 H9 H7.
    eapply insert_st'; eauto.
  - assert (SearchTree t). { eapply ST_intro;try eassumption. }
    apply (insert_relate t x v mp x1 H9 H2 H7).
  - eapply insert_redblack. 
    + apply H3.
    + apply H7.
Qed.

(* delete *)
Definition abs_delete_spec :=
 DECLARE _delete
  WITH mp: relate_map, b: val, x: Key
  PRE  [ tptr (tptr t_struct_rbtree), tint ]
    PROP (Int.min_signed < x < Int.max_signed)
    PARAMS (b; Vint (Int.repr x))
    SEP (treemap_rep mp b)
  POST [ Tvoid ]
    EX t_complete : RBtree, 
    PROP ()
    RETURN ()
    SEP (treemap_rep (k_delete x mp) b).

Lemma subsume_delete : funspec_sub (snd delete_spec) (snd abs_delete_spec).
Proof.
  do_funspec_sub.
  destruct w as [[mp b] k].
  assert (exists (kk : Key), k = kk). { exists k. auto. }
  (* to avoid type alias issues *)
  destruct H0 as [kk H0].
  subst k.
  rename kk into k.  
  clear H.
  unfold treemap_rep.
  Intros t.
  unfold treebox_rep.
  Intros p.
  simpl.
  normalize.
  Exists (t, b, k) emp.
  remember (delete_with_no_balance k t) as pp1.
  destruct pp1 as [[ls base] co].
  entailer!.
  2: { Exists p. entailer!. }
  split.
  2: {
    destruct co.
    - destruct base; destruct ls; auto.
    - assert (SearchTree t). { eapply ST_intro;try eassumption. }
      pose proof delete_with_no_balance_st k t base ls Black H6 Heqpp1.
      do 3  destruct H7.
      pose proof delete_dep_with_nobalance k t ls base H6 H3 Heqpp1.
      destruct H9. destruct H9. destruct H9.
      pose proof delete_co_with_nobalance k t ls base H6 H3 Heqpp1.
      destruct H11.
      pose proof delete_check_Black ls base x x0 x1 x2.
      eapply H13;try eassumption. 
  }
  intros.
  Intros x.
  Exists (delete k t).
  Exists x.
  entailer!.
  split; try split.
  - assert (SearchTree t). { eapply ST_intro;try eassumption. }
    pose proof delete_st k t H8.
    eapply delete_st';eauto.
  - apply delete_relate; auto.
    econstructor. apply H1.
  - eapply (delete_redblack k ). 
    + econstructor. apply H1.
    + apply H3.
    + auto.
Qed.

(* segment_update *)
Definition abs_update_spec :=
  DECLARE _update
  WITH root: val, mp: relate_map, tg: Tag, targ_lo: Key, targ_hi: Key
  PRE  [ tptr (tptr t_struct_rbtree), tuint, tint, tint ]
    PROP (Int.min_signed <= targ_lo <= Int.max_signed;
          Int.min_signed <= targ_hi <= Int.max_signed) 
    PARAMS (root; Vint (Int.repr tg); Vint (Int.repr targ_lo);
            Vint (Int.repr targ_hi)) 
    SEP (treemap_rep mp root)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (treemap_rep (segment_update targ_lo targ_hi tg mp) root).

Lemma subsume_update : funspec_sub (snd update_spec) (snd abs_update_spec).
Proof.
  do_funspec_sub.
  destruct w as [[[[root mp] tg] targ_lo] targ_hi].
  clear H.
  simpl. normalize.
  unfold treemap_rep.
  Intros t.
  unfold treebox_rep.
  Intros p.
  Exists (root, t, tg, targ_lo, targ_hi) emp.
  entailer!.
  2: { Exists p. entailer!. }
  intros.
  assert (Ha : exists (a : Key), a = targ_lo). { exists targ_lo . auto. }
  destruct Ha as [a Ha]. subst targ_lo. rename a into targ_lo.
  assert (Ha : exists (a : Key), a = targ_hi). { exists targ_hi . auto. }
  destruct Ha as [a Ha]. subst targ_hi. rename a into targ_hi.
  remember (change_segment' targ_lo targ_hi tg t Int.min_signed Int.max_signed) as t_res.
  Exists t_res.
  assert (Hfinal : change_segment targ_lo targ_hi tg t t_res).
  { subst t_res. econstructor; auto. }
  Exists x0.
  entailer!.
  split; try split.
  - apply segment_st_pre. auto.
  - apply segement_abs; assumption.
  - eapply segement_keep. 
    3: { apply Hfinal. }
    + econstructor. apply H3.
    + apply H5.
Qed.

(** Simple lemmas about representation predicates.

    The following lemmas are proved to help automation of VST.
    They will not appear frequently in the proof. Also, considering
    newer versions of VST, we explicitly export them to hint database.
*)

Lemma rbtree_rep_saturate_local:
   forall t p p_par, rbtree_rep t p p_par |-- !! is_pointer_or_null p.
Proof.
  destruct t; simpl; intros.
  entailer!.
  Intros pa pb. entailer!.
Qed.
(* #[export] *)Hint Resolve rbtree_rep_saturate_local: saturate_local.

Lemma rbtree_rep_saturate_local_parent:
   forall t p p_par, rbtree_rep t p p_par |-- !! is_pointer_or_null p_par.
Proof.
  destruct t; simpl; intros.
  entailer!.
  Intros pa pb. entailer!.
Qed.
(* #[export] *)Hint Resolve rbtree_rep_saturate_local_parent: saturate_local.

Lemma rbtree_rep_valid_pointer:
  forall t p p_par, rbtree_rep t p p_par |-- valid_pointer p.
Proof.
  intros.
  destruct t. 
  - simpl. entailer!.
  - simpl; normalize; auto with valid_pointer.
Qed.
(* #[export] *)Hint Resolve rbtree_rep_valid_pointer: valid_pointer.

Lemma treebox_rep_saturate_local:
  forall t b p_par, treebox_rep t b p_par |-- 
    !! field_compatible (tptr t_struct_rbtree) [] b.
Proof.
  intros.
  unfold treebox_rep.
  Intros p.
  entailer!.
Qed.
(* #[export] *)Hint Resolve treebox_rep_saturate_local: saturate_local.

Lemma treebox_rep_saturate_local':
   forall t b p_par, treebox_rep t b p_par |-- !! is_pointer_or_null b.
Proof.
  intros.
  unfold treebox_rep.
  Intros p.
  entailer!.
Qed.
(* #[export] *)Hint Resolve treebox_rep_saturate_local': saturate_local.

Lemma treebox_rep_saturate_local_parent:
  forall t b p_par, treebox_rep t b p_par |-- 
    !! (is_pointer_or_null p_par).
Proof.
  intros.
  unfold treebox_rep.
  Intros p.
  entailer!.
Qed.
(* #[export] *)Hint Resolve treebox_rep_saturate_local_parent: saturate_local.

Lemma treebox_rep_valid_pointer:
   forall t b p_par, treebox_rep t b p_par |-- valid_pointer b.
Proof.
  intros.
  unfold treebox_rep.
  Intros p.
  entailer!.
Qed.
(* #[export] *)Hint Resolve treebox_rep_valid_pointer: valid_pointer.

Lemma partial_tree_rep_saturate_local_parent:
  forall ls root p p_par, 
    partial_tree_rep ls root p p_par nullval |-- 
      !! is_pointer_or_null p_par.
Proof.
  intros.
  destruct ls.
  - simpl. entailer!.
  - destruct h as [[[[[va c] k] v] tg] sib].
    destruct va; simpl; normalize; auto with valid_pointer; entailer!.
Qed.
(* #[export] *)Hint Resolve partial_tree_rep_saturate_local_parent: saturate_local.

Lemma partial_tree_rep_saturate_local_parent_ptop:
  forall ls root p p_par p_top,
    is_pointer_or_null p_top ->
    partial_tree_rep ls root p p_par p_top |-- 
      !! is_pointer_or_null p_par.
Proof.
  intros.
  destruct ls.
  - simpl. entailer!.
  - destruct h as [[[[[va c] k] v] tg] sib].
    destruct va; simpl; normalize; auto with valid_pointer; entailer!.
Qed.
(* #[export] *)Hint Resolve partial_tree_rep_saturate_local_parent_ptop: saturate_local.

Lemma partial_tree_rep_valid_pointer_parent:
  forall ls root p p_par, 
    partial_tree_rep ls root p p_par nullval |-- valid_pointer p_par.
Proof.
  intros.
  destruct ls.
  - simpl. entailer!.
  - destruct h as [[[[[va c] k] v] tg] sib].
    destruct va; simpl; normalize; auto with valid_pointer; entailer!.
Qed.
(* #[export] *)Hint Resolve partial_tree_rep_valid_pointer_parent: valid_pointer.

Lemma partial_treebox_rep_saturate_local_parent:
  forall ls root b p_par, 
    partial_treebox_rep ls root b p_par nullval |-- 
      !! is_pointer_or_null p_par.
Proof.
  intros.
  destruct ls.
  - simpl. entailer!.
  - destruct ls; destruct h as [[[[[va c] k] v] tg] sib];
    destruct va; simpl; normalize; auto with valid_pointer; entailer!.
Qed.
(* #[export] *)Hint Resolve partial_treebox_rep_saturate_local_parent: saturate_local.

Lemma partial_treebox_rep_saturate_local_parent_ptop:
  forall ls root b p_par p_top, 
    is_pointer_or_null p_top ->
    partial_treebox_rep ls root b p_par p_top |-- 
      !! is_pointer_or_null p_par.
Proof.
  intros.
  destruct ls.
  - simpl. entailer!.
  - destruct ls; destruct h as [[[[[va c] k] v] tg] sib];
    destruct va; simpl; normalize; auto with valid_pointer; entailer!.
Qed.
(* #[export] *)Hint Resolve partial_treebox_rep_saturate_local_parent_ptop: saturate_local.

Lemma partial_treebox_rep_valid_pointer_parent:
  forall ls root b p_par,
    partial_treebox_rep ls root b p_par nullval |-- valid_pointer p_par.
Proof.
  intros.
  destruct ls.
  - simpl partial_treebox_rep. entailer!.
  - destruct h as [[[[[va c] k] v] tg] sib].
    simpl.
    destruct va; Intros p_gpar p_sib b_par; Intros;
      rewrite field_at_data_at'; entailer!.
Qed.
(* #[export] *)Hint Resolve partial_treebox_rep_valid_pointer_parent: valid_pointer.

(** This lemma is only useful for the current definition. 
    For further use, we may need share accounting. *)
Lemma field_color_valid_pointer:
  forall c p, 
    field_at Tsh t_struct_rbtree [StructField _color] (Vint (Int.repr (Col2Z c))) p
    |-- valid_pointer p.
Proof.
  intros.
  rewrite field_at_data_at'.
  entailer!.
Qed.
(* #[export] *)Hint Resolve field_color_valid_pointer: valid_pointer.

Ltac aggregate_solve :=
  try (repeat sep_apply rbtree_rep_saturate_local; Intros; entailer!);
  try (repeat sep_apply rbtree_rep_saturate_local_parent; Intros; entailer!);
  try (repeat sep_apply partial_tree_rep_saturate_local_parent; Intros; entailer!);
  try (repeat sep_apply partial_tree_rep_saturate_local_parent_ptop; Intros; entailer!);
  try (repeat sep_apply partial_treebox_rep_saturate_local_parent; Intros; entailer!);
  try (repeat sep_apply partial_treebox_rep_saturate_local_parent_ptop; Intros; entailer!).

(** Other lemmas about representation predicates.

    The following lemmas are about intrinsic properties of
    those predicates. They will be useful in our proof.
*)

Local Open Scope logic.

Lemma rbtree_rep_nullval : forall (t: RBtree) p_par, 
  rbtree_rep t nullval p_par |-- !! (t = Empty) && !! (is_pointer_or_null p_par) && emp.
Proof.
  intros. 
  destruct t.
  - simpl. entailer!.
  - simpl rbtree_rep. Intros. Intros p_lch p_rch.
    entailer!.
    assert_PROP(False) by entailer!.
    contradiction. 
Qed.

Lemma data_at_rbtree_nullval : forall h, 
  data_at Tsh t_struct_rbtree h nullval |-- !! False.
Proof.
  intros.
  entailer!.
Qed.

Lemma partialtreebox_backward : 
  forall ls va c k v tg sib root b p_par p_top,
  !! (is_pointer_or_null b) &&
  partial_treebox_rep (ls ++ [(va, c, k, v, tg, sib)]) root b p_par p_top |--
    EX p : val, EX p_sib : val, 
    !! (Int.min_signed <= k <= Int.max_signed) &&
    rbtree_rep sib p_sib p *
    field_at Tsh t_struct_rbtree [StructField _color] (Vint (Int.repr (Col2Z c))) p *
    field_at Tsh t_struct_rbtree [StructField _key] (Vint (Int.repr k)) p *
    field_at Tsh t_struct_rbtree [StructField _value] (Vint (Int.repr v)) p *
    field_at Tsh t_struct_rbtree [StructField _tag] (Vint (Int.repr tg)) p *
    (if va
     then (field_at Tsh t_struct_rbtree [StructField _left] p_sib p)
     else (field_at Tsh t_struct_rbtree [StructField _right] p_sib p)) *
    field_at Tsh t_struct_rbtree [StructField _par] p_top p *
    data_at Tsh (tptr t_struct_rbtree) p root *
    (if va
     then (partial_treebox_rep ls (field_address t_struct_rbtree [StructField _right] p) b p_par p)
     else (partial_treebox_rep ls (field_address t_struct_rbtree [StructField _left] p) b p_par p)).
Proof.
  intros.
  revert b p_par.
  induction ls; intros.
  - simpl app.
    simpl partial_treebox_rep.
    Intros p_gpar p_sib b_par.
    destruct va; Intros; subst; Exists p_par p_sib; entailer!. 
  - destruct a as [[[[[va' c'] k'] v'] tg'] sib'].
    simpl partial_treebox_rep.
    Intros p_gpar p_sib b_par.
    destruct va'; 
      assert_PROP (is_pointer_or_null b_par) by entailer!; 
      sep_apply IHls; try assumption;
      Intros p p_sib0;
      destruct va;
        Exists p p_sib0;
        Exists p_gpar p_sib b_par;
        entailer!.
Qed.
(** This also shows that in a partial treebox,
    if b with the least height satisfies is_pointer_or_null, 
    then all the other b's will also satisfy it.
*)

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

(* several lemmas about colors *)
Lemma col_not_0: forall col, Int.repr (Col2Z col) <> Int.repr 0 -> col = Red.
Proof.
  intros. 
  destruct col; [ auto | simpl Col2Z in *; unfold BLACK_COLOR in *; contradiction ].
Qed.

Lemma col_not_1: forall col, Int.repr (Col2Z col) <> Int.repr 1 -> col = Black.
Proof.
  intros.
  destruct col; [ simpl Col2Z in *; unfold RED_COLOR in *; contradiction | auto ].
Qed.

Lemma col_is_black: forall col, Int.repr (Col2Z col) = Int.repr 0 -> col = Black.
Proof.
  intros. destruct col; [ discriminate | auto ].
Qed.

Lemma col_is_red: forall col, Int.repr (Col2Z col) = Int.repr 1 -> col = Red.
Proof.
  intros. destruct col; [ auto | discriminate ].
Qed.

(* a small tactic used to determine color and to substitution *)
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

(** Reconstruction lemma for treeboxes and partial treeboxes. 

    We can apply it to reconstruct a tree from a treebox and
    a partial treebox. Here, a treebox is unfolded so that the 
    the premise becomes weaker. 
*)
Lemma reconstruction_lemma_box : 
  forall ls t (p p_par root b : val), 
  data_at Tsh (tptr t_struct_rbtree) p b * rbtree_rep t p p_par *
    partial_treebox_rep ls root b p_par nullval
  |-- treebox_rep (complete_tree ls t) root nullval.
Proof.
  intros ls.
  induction ls as [ | a ls' IH ]; intros.
  - simpl.
    Intros.
    unfold treebox_rep.
    Exists p.
    subst p_par. subst b.
    entailer!.
  - destruct a as [[[[[va c] k] v] tg] sib].
    simpl partial_treebox_rep.
    Intros p_gpar p_sib b_par.
    pose proof (IH (T c 
      (if va then sib else t) 
        k v tg (if va then t else sib))
        p_par p_gpar root b_par) as HIH.
    clear IH.
    apply derives_trans with (Q:=
      (data_at Tsh (tptr t_struct_rbtree) p_par b_par *
      rbtree_rep (T c (if va then sib else t) 
        k v tg (if va then t else sib)) p_par p_gpar *
      partial_treebox_rep ls' root b_par p_gpar nullval)).
    {
      simpl rbtree_rep.
      Exists (if va then p_sib else p) (if va then p else p_sib).
      unfold_data_at (data_at _ _ _ p_par).
      destruct va; Intros; entailer!.
    }
    {
      sep_apply HIH.
      destruct va; simpl complete_tree; 
      apply derives_refl.
    }
Qed.

(** Reconstruction lemma for subtrees and partial trees. *) 
Lemma reconstruction_lemma : 
  forall ls t root p p_par p_top, 
  !! (is_pointer_or_null p_top) &&
    rbtree_rep t p p_par * partial_tree_rep ls root p p_par p_top
  |-- rbtree_rep (complete_tree ls t) root p_top.
Proof.
  intros ls.
  induction ls as [ | a ls' IH ]; intros.
  - simpl.
    Intros.
    entailer!.
  - destruct a as [[[[[va c] k] v] tg] sib].
    simpl partial_tree_rep.
    Intros p_gpar p_sib.
    simpl complete_tree.
    specialize IH with (t := 
      (if va 
        then (T c sib k v tg t) 
        else (T c t k v tg sib))) (p:=p_par) (p_par:=p_gpar).
    cancel.
    destruct va; 
      eapply derives_trans; try apply IH;
      entailer!;
      simpl rbtree_rep;
      [ Exists p_sib p | Exists p p_sib ];
      entailer!.
Qed.

(** Equivalence Lemma (with box -> without box). *)
Lemma equivalence_box_nobox : 
  forall ls p b root p_par p_top,
  !! (is_pointer_or_null p_top) &&
    data_at Tsh (tptr t_struct_rbtree) p b *
    partial_treebox_rep ls root b p_par p_top
  |-- EX p_root, partial_tree_rep ls p_root p p_par p_top *
      data_at Tsh (tptr t_struct_rbtree) p_root root.
Proof.
  intros ls.
  induction ls as [ | a ls' IH ]; intros.
  - simpl. Exists p. entailer.
  - destruct a as [[[[[va c] k] v] tg] sib].
    simpl.
    Intros p_gpar p_sib b_par.
    destruct va;
      sep_apply (IH p_par); try auto;
      Intros p_root;
      Exists p_root p_gpar p_sib;
      unfold_data_at (data_at _ _ _ p_par);
      entailer!.
Qed.

(** Equivalence Lemma (without box -> with box). *)
Lemma equivalence_nobox_box : 
  forall ls p root p_par p_root p_top,
  !! (is_pointer_or_null p_top) &&
    data_at Tsh (tptr t_struct_rbtree) p_root root * 
    partial_tree_rep ls p_root p p_par p_top
  |-- EX b, data_at Tsh (tptr t_struct_rbtree) p b *
    partial_treebox_rep ls root b p_par p_top.
Proof.
  intros ls.
  induction ls as [ | a ls' IH ]; intros.
  - simpl. 
    Exists root.
    entailer!.
  - destruct a as [[[[[va c] k] v] tg] sib].
    simpl.
    Intros p_gpar p_sib.
    Exists (
      if va
      then (field_address t_struct_rbtree [StructField _right] p_par)
      else (field_address t_struct_rbtree [StructField _left] p_par)).
    Exists p_gpar p_sib.
    sep_apply IH; try auto.
    Intros b_par. Exists b_par. 
    unfold_data_at (data_at _ _ _ p_par).
    destruct va; entailer!.
Qed.

(** Corollaries of equivalence lemmas, with p_top specified to be nullval. *)
Lemma equivalence_box_nobox' : 
  forall ls p b root p_par,
    data_at Tsh (tptr t_struct_rbtree) p b *
    partial_treebox_rep ls root b p_par nullval
  |-- EX p_root, partial_tree_rep ls p_root p p_par nullval *
      data_at Tsh (tptr t_struct_rbtree) p_root root.
Proof.
  intros. sep_apply equivalence_box_nobox; auto.
Qed.

Lemma equivalence_nobox_box' : 
  forall ls p root p_par p_root,
    data_at Tsh (tptr t_struct_rbtree) p_root root * 
    partial_tree_rep ls p_root p p_par nullval
  |-- EX b, data_at Tsh (tptr t_struct_rbtree) p b *
    partial_treebox_rep ls root b p_par nullval.
Proof.
  intros. sep_apply equivalence_nobox_box; auto.
Qed.

(*
Lemma delete_lemma : forall ls root b p_par,
  partial_treebox_rep ls root b p_par nullval *
  data_at Tsh (tptr t_struct_rbtree) nullval b
  |-- treeroot_rep (complete_tree ls Empty) root.
Proof.
  intros.
  pose proof (insert_lemma ls Empty).
  specialize (H nullval p_par root b).
  unfold treeroot_rep, treebox_rep in *.
  eapply derives_trans; [ | apply H].
  simpl rbtree_rep.
  entailer!.
Qed.
*)

Lemma delete_balance_t_color : 
  forall t va_f c_f k_f v_f tg_f sib ls,
  get_color_tree t <> Col2Z Red -> 
  delete_balance t ((va_f, c_f, k_f, v_f, tg_f, sib) :: ls) Black =
  match sib with
  | Empty => (t, ((va_f, c_f, k_f, v_f, tg_f, sib) :: ls))
  | T Red wl wk wv wt wr => 
    match (CaseOne_sol t (va_f, c_f, k_f, v_f, tg_f, sib) false) with
    | (ts, true) => (ts, ls)
    | (ts, false) => delete_balance ts ls Black
    end
  | T Black wl wk wv wt wr => 
    match (CaseTTF_sol t (va_f, c_f, k_f, v_f, tg_f, sib) false) with
    | (ts, true) => (ts, ls)
    | (ts, false) => delete_balance ts ls Black
    end
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

Lemma tag_tree_t_empty :
  forall t tg, tag_tree_t tg t = Empty <-> t = Empty.
Proof.
  intros.
  destruct t; split; intros; try reflexivity; try discriminate.
Qed.

Ltac quick_replace_offset_val p :=
  try replace (offset_val 16 p)
    with (field_address t_struct_rbtree [StructField _left] p)
    by (unfold field_address; simpl;
    rewrite if_true by auto with field_compatible; auto);
  try replace (offset_val 20 p)
    with (field_address t_struct_rbtree [StructField _right] p)
    by (unfold field_address; simpl;
    rewrite if_true by auto with field_compatible; auto).

(** Gather isolate fields into on data_at. *)
Lemma field_at_gather_right : 
  forall p c k v tg p_lch p_rch p_par, 
  data_at Tsh (tptr t_struct_rbtree) p_rch
    (field_address t_struct_rbtree [StructField _right] p) *
  field_at Tsh t_struct_rbtree [StructField _color] (Vint (Int.repr (Col2Z c))) p *
  field_at Tsh t_struct_rbtree [StructField _key] (Vint (Int.repr k)) p *
  field_at Tsh t_struct_rbtree [StructField _value] (Vint (Int.repr v)) p *
  field_at Tsh t_struct_rbtree [StructField _tag] (Vint (Int.repr tg)) p *
  field_at Tsh t_struct_rbtree [StructField _left] p_lch p *
  field_at Tsh t_struct_rbtree [StructField _par] p_par p |--
  data_at Tsh t_struct_rbtree
    (Vint (Int.repr (Col2Z c)),
    (Vint (Int.repr k),
    (Vint (Int.repr v), (Vint (Int.repr tg), (p_lch, (p_rch, p_par)))))) p.
Proof.
  intros. unfold_data_at (data_at _ _ _ p). entailer!.
Qed.

Lemma field_at_gather_left : 
  forall p c k v tg p_lch p_rch p_par, 
  data_at Tsh (tptr t_struct_rbtree) p_lch
    (field_address t_struct_rbtree [StructField _left] p) *
  field_at Tsh t_struct_rbtree [StructField _color] (Vint (Int.repr (Col2Z c))) p *
  field_at Tsh t_struct_rbtree [StructField _key] (Vint (Int.repr k)) p *
  field_at Tsh t_struct_rbtree [StructField _value] (Vint (Int.repr v)) p *
  field_at Tsh t_struct_rbtree [StructField _tag] (Vint (Int.repr tg)) p *
  field_at Tsh t_struct_rbtree [StructField _right] p_rch p *
  field_at Tsh t_struct_rbtree [StructField _par] p_par p |--
  data_at Tsh t_struct_rbtree
    (Vint (Int.repr (Col2Z c)),
    (Vint (Int.repr k),
    (Vint (Int.repr v), (Vint (Int.repr tg), (p_lch, (p_rch, p_par)))))) p.
Proof.
  intros. unfold_data_at (data_at _ _ _ p). entailer!.
Qed.

Lemma partialtreebox_link : 
  forall ls1 ls2 root b1 b2 p1 p2 p_top, 
  partial_treebox_rep ls1 b1 b2 p2 p1 *
  partial_treebox_rep ls2 root b1 p1 p_top |--
  partial_treebox_rep (ls1 ++ ls2) root b2 p2 p_top.
Proof.
  intros ls1.
  induction ls1 as [ | a ls1' IH ]; intros.
  - simpl partial_treebox_rep.
    entailer!.
  - destruct a as [[[[[va c] k] v] tg] sib].
    simpl partial_treebox_rep at 1.
    Intros p_gpar p_sib b_par.
    subst b2.
    sep_apply IH.
    simpl partial_treebox_rep.
    Exists p_gpar p_sib b_par.
    destruct va; Intros; entailer!.
Qed.

Lemma case_solve_not_null : forall t hft, 
  get_color_tree t <> Col2Z Red ->
  CaseTTF_check t hft = true ->
  let (ts, br) := CaseTTF_sol t hft false in
  ts <> Empty.
Proof.
  intros.
  destruct hft as [[[[[va_f c_f] k_f] v_f] tg_f] oppo].
  unfold CaseTTF_check in H0.
  unfold CaseTTF_sol.
  destruct va_f.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1.
    * destruct oppo2; [ simpl in H; discriminate | ].
      destruct c; [ | simpl in H; discriminate ].
      apply (case4_solve_not_null _ _ H0).
    * destruct c.
      - destruct oppo2; [ apply (case4_solve_not_null _ _ H0) | ].
        destruct c; [ apply (case4_solve_not_null _ _ H0) | ].
        apply (case4_solve_not_null _ _ H0).
      - destruct oppo2; [ simpl in H; discriminate | ].
        destruct c; [ apply (case4_solve_not_null _ _ H0) | ].
        apply (case2_solve_not_null _ _ H0).
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1.
    * destruct oppo2; [ simpl in H; discriminate | ].
      destruct c; [ | simpl in H; discriminate ].
      apply (case4_solve_not_null _ _ H0).
    * destruct c.
      - destruct oppo2; [ apply (case4_solve_not_null _ _ H0) | ].
        destruct c; [ apply (case4_solve_not_null _ _ H0) | ].
        apply (case4_solve_not_null _ _ H0).
      - destruct oppo2; [ simpl in H; discriminate | ].
        destruct c; [ apply (case4_solve_not_null _ _ H0) | ].
        apply (case2_solve_not_null _ _ H0).
Qed.

Lemma case_one_true : forall s pb pc p pv pt wc wl wk wv wt wr, 
  get_color_tree s <> Col2Z Red ->
  CaseOne_check s (pb, pc, p, pv, pt, T wc wl wk wv wt wr) = true ->
  let (ts, br) := (CaseTTF_sol s (pb, Red, p, pv, default, tag_tree_t wt 
    (if pb then wr else wl)) false) in
  match br with
  | true => CaseOne_sol s (pb, pc, p, pv, pt, T wc wl wk wv wt wr) false = 
      (T Black (if pb then (tag_tree_t wt wl) else ts) wk (f wv wt) pt 
        (if pb then ts else (tag_tree_t wt wr)), true)
  | false =>
    (get_color_tree ts = Col2Z Red /\
    CaseOne_sol s (pb, pc, p, pv, pt, T wc wl wk wv wt wr) false = 
      (T Black (if pb then (tag_tree_t wt wl) else (makeBlack ts)) wk (f wv wt) pt 
        (if pb then (makeBlack ts) else (tag_tree_t wt wr)), true))
    \/
    (CaseTTF_check ts
    (pb, Black, wk, f wv wt, pt, tag_tree_t wt (if pb then wl else wr)) = true /\
    get_color_tree (tag_tree_t wt (if pb then wl else wr)) = Col2Z Black /\
    get_color_tree ts = Col2Z Black /\
      CaseOne_sol s (pb, pc, p, pv, pt, T wc wl wk wv wt wr) false = 
        CaseTTF_sol ts (pb, Black, wk, f wv wt, pt, tag_tree_t wt 
          (if pb then wl else wr)) false)
  end.
Proof.
  assert (HLemma : forall (b res : bool), 
    (if b then res else false) = true <-> b = true /\ res = true)
    by (intros; destruct b; destruct res; tauto). 
  intros. unfold CaseOne_check in H0.
  destruct pb.
  - destruct wc; [ | discriminate ].
    rewrite HLemma in H0.
    destruct H0 as [H0_copy H0].
    remember (CaseTTF_sol s (true, Red, p, pv, default, tag_tree_t wt wr) false) as br_ts.
    destruct br_ts as [ts br].
    destruct br.
    { 
      unfold CaseOne_sol. rewrite <- Heqbr_ts.
      reflexivity.
    }
    destruct ts.
    + apply case_solve_not_null in H0_copy; [ | assumption ].
      rewrite <- Heqbr_ts in H0_copy.
      contradiction.
    + destruct c.
      * left. split.
        --  reflexivity.
        --  unfold CaseOne_sol. rewrite <- Heqbr_ts.
            reflexivity. 
      * right. split; [ exact H0 | ]. 
        destruct wl; [ simpl in H0; discriminate | ].
        destruct c; [ simpl in H0; discriminate | ].
        do 2 split; [ reflexivity | ].
        unfold CaseOne_sol. rewrite <- Heqbr_ts.
        reflexivity. 
  - destruct wc; [ | discriminate ].
    rewrite HLemma in H0.
    destruct H0 as [H0_copy H0].
    remember (CaseTTF_sol s (false, Red, p, pv, default, tag_tree_t wt wl) false) as br_ts.
    destruct br_ts as [ts br].
    destruct br.
    { 
      unfold CaseOne_sol. rewrite <- Heqbr_ts.
      reflexivity.
    }
    destruct ts.
    + apply case_solve_not_null in H0_copy; [ | assumption ].
      rewrite <- Heqbr_ts in H0_copy.
      contradiction.
    + destruct c.
      * left. split.
        --  reflexivity.
        --  unfold CaseOne_sol. rewrite <- Heqbr_ts.
            reflexivity. 
      * right. split; [ exact H0 | ]. 
        destruct wr; [ simpl in H0; discriminate | ].
        destruct c; [ simpl in H0; discriminate | ].
        do 2 split; [ reflexivity | ].
        unfold CaseOne_sol. rewrite <- Heqbr_ts.
        reflexivity. 
Qed.

Lemma if_else_then_true : forall (b res : bool), 
  (if b then res else false) = true <-> b = true /\ res = true.
Proof.
  intros. destruct b; destruct res; tauto.
Qed. 

Definition get_tag (t : RBtree) : Tag := 
  match t with
  | Empty => default
  | T _ _ _ _ t0 _ => t0
  end.

Definition f_partial (ov : option Value) (t0 : Tag) : option Value :=
  match ov with
  | Some v => Some (f v t0)
  | None => None
  end.

Local Open Scope Z.

(* TODO: this will be removed in newer version of Coq (e.g. 8.13.0)
    when its lia is stronger *)
Definition tri_div (a b c : bool) : Prop := 
  if a then b = false /\ c = false
  else if b then c = false
            else c = true.

Lemma tri_div_Z : forall (k x : Z), 
  tri_div (k <? x) (x <? k) (k =? x).
Proof.
  intros.
  unfold tri_div.
  destruct (k <? x) eqn:E.
  - rewrite Z.ltb_lt in E.
    split.
    + assert (k <= x) by lia.
      rewrite Zaux.Zlt_bool_false; auto.
    + rewrite Z.eqb_neq.
      lia.
  - destruct (x <? k) eqn:E'.
    + rewrite Z.ltb_lt in E'.
      rewrite Z.eqb_neq.
      lia.
    + rewrite Z.eqb_eq.
      rewrite Z.ltb_ge in E, E'.
      lia.
Qed.

Ltac nonempty_tree t :=
  destruct t; simpl rbtree_rep; [ Intros; contradiction | ].

Ltac empty_tree t :=
  sep_apply rbtree_rep_nullval; Intros; subst t.

Ltac nonempty_data := 
  sep_apply data_at_rbtree_nullval; Intros; contradiction.

Lemma partial_tree_par_nullval : 
  forall ls p_root p p_top, 
    partial_tree_rep ls p_root p nullval p_top |-- 
      !! (ls = nil) && !! (p_root = p) && !! (p_top = nullval) && emp.
Proof.
  intros.
  destruct ls; [ simpl partial_tree_rep; entailer! | ].
  destruct h as [[[[[va c] k] v] tg] sib].
  simpl partial_tree_rep.
  Intros pa pb.
  nonempty_data.
Qed.

Ltac empty_partialtree ls := 
  sep_apply (partial_tree_par_nullval ls); Intros; subst ls.

Ltac nonempty_partialtree ls :=
  destruct ls; simpl partial_tree_rep; [ Intros; contradiction | ].

Lemma rbtree_shareptr_false :
  forall (p : val) sib c k v tg (p_lch p_rch p_par p_par' : val), 
    data_at Tsh t_struct_rbtree
      (Vint (Int.repr (Col2Z c)),
      (Vint (Int.repr k),
      (Vint (Int.repr v),
      (Vint (Int.repr tg), (p_lch, (p_rch, p_par)))))) p *
    rbtree_rep sib p p_par' |-- !! False.
Proof.
  intros.
  destruct sib.
  - simpl rbtree_rep. Intros.
    subst p.
    assert_PROP (False). { entailer!. }
    contradiction.
  - simpl rbtree_rep. 
    Intros p_lch0 p_rch0.
    sep_apply data_at_conflict; [ apply sepalg_Tsh | ].
    sep_apply FF_local_facts.
    Intros.
    contradiction.
Qed.

Ltac common_pointer_solve p t :=
  sep_apply (rbtree_shareptr_false p t); Intros; contradiction.

Lemma col_repr_empty : 
  forall t, Int.repr (get_color_tree t) = Int.repr (-1) <->
    t = Empty.
Proof.
  intros. split. 
  - destruct t; intros.
    + auto. 
    + destruct c; simpl in H; try discriminate. 
  - intros. subst t. auto.
Qed.

Ltac nonempty_tree_bycol t := 
  destruct t; [ simpl get_color_tree in *; discriminate | ].

Theorem body_update_aux: 
  semax_body Vprog Gprog f_update_aux update_aux_spec.
Proof.
  start_function.
  rename H3 into Hini.
  assert (Htarglohi : targ_hi <? targ_lo = false).
  {
    destruct Hini.
    - unfold lt_prop, Rlt_Z in H3. arith_bool.
      pose proof (tri_div_Z targ_lo targ_hi).
      unfold tri_div in H4.
      rewrite H3 in H4.
      destruct H4. auto.
    - rewrite H3. apply Z.ltb_irrefl.
  }
  forward_if_wrp.           (* if (t == NULL) *)
  {
    subst p. empty_tree t. 
    forward.
    simpl. 
    repeat rewrite Tauto.if_same. 
    simpl rbtree_rep.
    entailer!.
  }
  (* t <> Empty *)
  nonempty_tree t.
  forward_if_wrp.           (* if (l > targ_r) *)
  { 
    forward.
    arith_bool.
    simpl change_segment'.
    rewrite H4.
    simpl. rewrite Tauto.if_same.
    simpl rbtree_rep.
    Exists p_lch p_rch.
    entailer!.
  }
  (* targ_hi >= lo *)
  forward_if_wrp.           (* if (r < targ_l) *)
  { 
    forward.
    arith_bool.
    simpl change_segment'.
    rewrite H5, orb_true_r.
    simpl. rewrite Tauto.if_same.
    simpl rbtree_rep.
    Exists p_lch p_rch.
    entailer!.
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
  forward_if_wrp.           (* if (l >= targ_l && r <= targ_r) *)
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
    rewrite Htarglohi.
    simpl rbtree_rep.
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
          (Vint (Int.repr t2), (p_lch, (p_rch, p_par)))))) p;
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
    forward; try aggregate_solve.
    forward.
    forward_call (p_lch, p, t1, tg, targ_lo, targ_hi, lo, k).
    forward; try aggregate_solve.
    forward.
    forward_call (p_rch, p, t3, tg, targ_lo, targ_hi, k, hi).
    entailer!.
    unfold lte_bool. 
    rewrite H4, H5.
    simpl.
    rewrite Htarglohi.
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
  forward_if (lte_prop targ_lo targ_hi /\ targ_lo <= targ_hi).
  {
    forward.
    arith_bool.
    unfold change_segment', lt_bool. simpl.
    destruct t; rewrite H1; entailer.
  }
  {
    forward.
    entailer!.
    unfold lte_prop.
    unfold lt_prop.
    simpl.
    lia.
  }
  Intros.
  destruct t; unfold treebox_rep; Intros p; simpl rbtree_rep.
  {
    Intros. subst p.
    forward.
    forward_call (nullval, nullval, Empty, tg, targ_lo, targ_hi, Int.min_signed, Int.max_signed).
    {
      simpl rbtree_rep.
      entailer!.
    }
    { repeat (split; try auto; try rep_lia). }
    entailer!.
    Exists nullval.
    repeat rewrite Tauto.if_same.
    rewrite change_Empty.
    entailer!.
  }
  {
    Intros p_lch p_rch.
    forward.
    forward_call (p, nullval, (T c t1 k v t2 t3), tg, targ_lo, targ_hi, Int.min_signed, Int.max_signed).
    {
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
    }
    { repeat (split; try auto; try rep_lia). }
    entailer!.
    Exists p.
    simpl change_segment' at 1.
    entailer!.
  }
Qed.

Theorem body_tree_minimum: semax_body Vprog Gprog f_tree_minimum tree_minimum_spec.
Proof. 
  start_function.
  forward_loop
  (EX t' : RBtree, 
    EX ls : list Half_tree, 
    EX p_par' : val,
    EX b' : val, 
    PROP (Up_split (minimum_split default t nil) = 
      Up_split (minimum_split default t' ls); 
      Forall turn_left ls; 
      Forall tag_default ls;
      t' <> Empty)
    LOCAL (temp _t b')
    SEP (treebox_rep t' b' p_par';
    partial_treebox_rep ls b b' p_par' p_par)).
  {
    Exists t (@nil Half_tree) p_par b.
    entailer!.
    simpl partial_treebox_rep.
    entailer!.
  }
  { 
    Intros t' ls p_par' b'.
    nonempty_tree t'.
    unfold treebox_rep.
    Intros p.
    simpl rbtree_rep.
    Intros p_lch p_rch.
    forward.              (* tmp = *t; *)
    forward_call (c, k, v, t0, p_lch, p_rch, p_par', p, t'1, t'2).
                          (* pushdown(tmp); *)
    forward; try aggregate_solve.
    forward_if_wrp.
    { 
      subst p_lch.
      remember (tag_tree_t t0 t'1) as lch.
      empty_tree lch.
      rewrite tag_tree_t_empty in H5.
      subst t'1.
      forward.            (* return; *)
      Exists b' p_par' ls c k (v + t0) (tag_tree_t t0 t'2).
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
      Exists (tag_tree_t t0 t'1)
        ((false, c, k, (v + t0), default, (tag_tree_t t0 t'2)) :: ls).
      Exists p (offset_val 16 p).
      entailer!.
      - split; [ | split; [ | split ] ]; try apply Forall_cons; try assumption.
        * rewrite H0.
          unfold minimum_split.
          simpl.
          strip_0.
          do 7 f_equal.
          lia.
        * unfold turn_left.
          reflexivity.
        * unfold tag_default.
          reflexivity.
        * intro; discriminate.
      - simpl rbtree_rep.
        Intros p_lch0 p_rch0.
        unfold treebox_rep.
        Exists p_lch.
        simpl rbtree_rep.
        Exists p_lch0 p_rch0.
        simpl partial_treebox_rep.
        Exists p_par' p_rch b'.
        entailer!;
        quick_replace_offset_val p; try auto.
        unfold_data_at (data_at _ _ _ p).
        entailer!.
    }
  }
Qed.

Theorem body_delete_balance: 
  semax_body Vprog Gprog f_delete_balance delete_balance_spec.
Proof. 
  start_function.
  sep_apply equivalence_box_nobox; try auto.
  Intros p_root.
  forward_loop
  (EX t : RBtree, 
  EX ls : list Half_tree, 
  EX p : val, 
  EX p_par : val,
  EX p_root' : val, 
  PROP (delete_check t ls Black = true /\
    complete_tree_revarg (delete_balance t_initial ls_initial Black)
   = complete_tree_revarg (delete_balance t ls Black))
  LOCAL (temp _root root; temp _p p; temp _p_par p_par)
  SEP (rbtree_rep t p p_par;
    partial_tree_rep ls p_root' p p_par nullval;
    data_at Tsh (tptr t_struct_rbtree) p_root' root)).
  {
    Exists t_initial.
    Exists ls_initial.
    Exists p_initial p_par_initial p_root.
    entailer!.
  }
  {
    Intros t ls p p_par p_root'.
    forward_if (p_par <> nullval); try pointer_destructor.
    { (* if p_fa is nullptr, then return directly *)
      subst p_par.
      empty_partialtree ls.
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
    nonempty_partialtree ls.
    destruct h as [[[[[va c] k] v] tg] sib].
    Intros p_gpar p_sib.
    forward_call (t, p, p_par).     (* getting color *)
    forward_if (get_color_tree t <> Col2Z Red); try pointer_destructor.
                                    (* if (get_color(p) == RED) *)
    { (* the color of t is red *)
      nonempty_tree_bycol t.
      simpl rbtree_rep.
      Intros p_lch p_rch.
      forward.                      (* p->color = BLACK; *)
      forward.                      (* return; *)

      simpl in H4.
      color_replace.
      rewrite H1.
      Exists (T Black t1 k0 v0 t2 t3) ((va, c, k, v, tg, sib) :: ls).

      simpl delete_balance.
      simpl partial_tree_rep.
      Exists (if va then (offset_val 20 p_par) else (offset_val 16 p_par)).
      Exists p_par.
      simpl partial_treebox_rep.
      Exists p_gpar p_sib.
      sep_apply equivalence_nobox_box'.
      Intros b_par.
      Exists b_par.
      unfold treebox_rep.
      Exists p.
      simpl rbtree_rep.
      Exists p_lch p_rch.
      destruct va;
        try assert_PROP (field_compatible t_struct_rbtree [StructField _right] p_par)
          by entailer!;
        try assert_PROP (field_compatible t_struct_rbtree [StructField _left] p_par)
          by entailer!;
        quick_replace_offset_val p_par;
        unfold_data_at (data_at _ _ _ p_par);
        entailer!.
    }
    {
      forward.
      entailer!.
      rewrite H9 in H4.
      simpl Col2Z in H4.
      unfold RED_COLOR in H4.
      contradiction.
    }
    Intros.
    rewrite delete_balance_t_color in H1; [ | assumption ].
    destruct sib.
    (* show sib <> Empty *)
    { simpl in H0. rewrite (match_color _ _ _ H4) in H0. discriminate. }
    simpl rbtree_rep.
    Intros p_sib_lch p_sib_rch.

    forward.
    { destruct va; aggregate_solve. }
    forward_if_wrp.                 (* if (p == p_fa->left) *)
    { destruct va; aggregate_solve. }
    { (* p is the left child of p_fa *)
      destruct va.
      {
        subst p_sib.
        common_pointer_solve p t.
      }
      forward.                      (* p_sib = p_fa->right; *)
      forward.
      forward_if          (* if (p_sib->color == RED) *)
      (EX ls_changed : list Half_tree, 
        EX p_changed : val, 
        EX p_gpar_changed : val, 
        EX p_sib_changed : val, 
        EX c_changed : color, 
        EX tg_changed : Tag, 
        EX k_sib : Key, 
        EX v_sib : Value, 
        EX tg_sib : Tag, 
        EX lch_sib : RBtree, 
        EX rch_sib : RBtree, 
        EX p_sib_lch : val, 
        EX p_sib_rch : val, 
        EX p_root' : val, 
        let hft := (false, c_changed, k, v, tg_changed, 
              (T Black lch_sib k_sib v_sib tg_sib rch_sib)) in
        let (ts, br) := (CaseTTF_sol t hft false) in
        PROP (
          (if br then true else delete_check ts
            ls_changed Black) = true;
          CaseTTF_check t hft = true;
          complete_tree_revarg (delete_balance t_initial ls_initial Black)
          = complete_tree_revarg (match (CaseTTF_sol t hft false) with
            | (ts, true) => (ts, ls_changed)
            | (ts, false) => delete_balance ts ls_changed Black
            end); 
            Int.min_signed <= k_sib <= Int.max_signed; 
            is_pointer_or_null p_gpar_changed)
        LOCAL (temp _root root; temp _p p; temp _p_par p_par; 
          temp _p_sib p_sib_changed)
        SEP (rbtree_rep t p_changed p_par;
          rbtree_rep lch_sib p_sib_lch p_sib_changed;
          rbtree_rep rch_sib p_sib_rch p_sib_changed;
          data_at Tsh t_struct_rbtree
          (Vint (Int.repr BLACK_COLOR),
          (Vint (Int.repr k_sib),
          (Vint (Int.repr v_sib),
          (Vint (Int.repr tg_sib), (p_sib_lch, (p_sib_rch, p_par)))))) p_sib_changed;
          data_at Tsh t_struct_rbtree
          (Vint (Int.repr (Col2Z c_changed)),
          (Vint (Int.repr k),
          (Vint (Int.repr v), (Vint (Int.repr tg_changed), 
            (p_changed, (p_sib_changed, p_gpar_changed))))))
          p_par;
          partial_tree_rep ls_changed p_root' p_par p_gpar_changed nullval;
          data_at Tsh (tptr t_struct_rbtree) p_root' root))%assert; try pointer_destructor.
      (** Note that here, _p should be p_changed, though this will not affect the 
          following proof. *)
      {
        color_replace.
        (* show CaseOne_check is true *)
        assert (Hcaseone: (CaseOne_check t
             (false, c, k, v, tg, T Red sib1 k0 v0 t0 sib2)) = true).
        {
          remember (CaseOne_check t
             (false, c, k, v, tg, T Red sib1 k0 v0 t0 sib2)) as bb.
          destruct bb.
          - reflexivity.
          - unfold delete_check in H0. rewrite <- Heqbb in H0.
            rewrite (match_color _ _ _ H4) in H0.
            discriminate.
        }
        apply case_one_true in Hcaseone; [ | assumption ].
        assert (Hcasettf: (CaseTTF_check t
             (false, Red, k, v, default, tag_tree_t t0 sib1)) = true).
        {
          simpl in H0. rewrite (match_color _ _ _ H4) in H0.
          rewrite if_else_then_true in H0. destruct H0 as [H0 _].
          rewrite if_else_then_true in H0. destruct H0 as [H0 _].
          exact H0.
        }
        pose proof Hcasettf as Hcopyttf.
        apply (case_solve_not_null _ _ H4) in Hcasettf.
        (* a critical conclusion *)
        assert (Hfinal:
          complete_tree_revarg (delete_balance t_initial ls_initial Black) = 
          complete_tree_revarg (match (CaseTTF_sol t
             (false, Red, k, v, default, tag_tree_t t0 sib1) false) with
          | (ts, true) => (ts, ((false, Black, k0, f v0 t0, tg, tag_tree_t t0 sib2) :: ls))
          | (ts, false) =>
            delete_balance ts
            ((false, Black, k0, f v0 t0, tg, tag_tree_t t0 sib2) :: ls)
            Black
          end)).
        {
          rewrite H1.
          remember (CaseTTF_sol t (false, Red, k, v, default, tag_tree_t t0 sib1) false)
            as br_ts.
          destruct br_ts as [t_t br].
          destruct br.
          {
            rewrite Hcaseone.
            reflexivity.
          }
          destruct t_t; [ contradiction | ].
          destruct Hcaseone as [Hcaseone | Hcaseone]; destruct Hcaseone as [Hco1 Hco2]. 
          - rewrite Hco2.
            simpl delete_balance. 
            destruct c0; unfold complete_tree_revarg; simpl complete_tree; 
            [ reflexivity | simpl in Hco1; discriminate ].
          - destruct Hco2 as [Hco2 Hco3]. 
            destruct Hco3 as [Hco3 Hco4].
            destruct c0; [ discriminate | ].
            remember (tag_tree_t t0 sib2) as t_t.
            destruct t_t.
            * discriminate Hco2.
            * destruct c0; [ discriminate Hco2 | ].
              rewrite Hco4.
              reflexivity.
        }
        forward_call (Red, k0, v0, t0, p_sib_lch, p_sib_rch, p_par, p_sib, 
          sib1, sib2).    (* pushdown(p_sib); *)
        forward.
        forward.          (* p_sib->tag = p_par->tag; *)
        forward.          (* p_par->tag = DEFAULT_TAG; *)
        forward.          (* p_sib->color = p_fa->color; *)
        forward.          (* p_fa->color = RED; *)
        assert_PROP (is_pointer_or_null p_gpar) as PNp_gpar by entailer!. 
        forward_call      (* left_rotate_wrap(p_par, root); *)
        (Red, k, v, default, p_gpar,
          Black, k0, (f v0 t0), tg, 
          t, (tag_tree_t t0 sib1), (tag_tree_t t0 sib2), 
          p_par, p_sib, p, p_sib_lch, p_sib_rch, 
          root, p_root', ls).
        Intros p_root_new.
        forward. try aggregate_solve.          (* p_sib = p_fa->right; *)
        nonempty_tree_bycol sib1.
        destruct c0.
        { simpl in Hcopyttf. discriminate Hcopyttf. }
        simpl rbtree_rep.
        Intros p_sib_lch_lch p_sib_lch_rch.

        Exists ((false, Black, k0, f v0 t0, tg, tag_tree_t t0 sib2)
          :: ls).
        Exists p p_sib p_sib_lch.
        Exists Red default k1 v1 (t0 + t1) sib1_1 sib1_2.
        Exists p_sib_lch_lch p_sib_lch_rch.
        Exists p_root_new.
        simpl tag_tree_t in *.
        remember (CaseTTF_sol t (false, Red, k, v, default, 
          T Black sib1_1 k1 v1 (t0 + t1) sib1_2) false) as t_t.
        destruct t_t as [ts br].
        entailer!.
        {
          destruct br; auto.
          destruct ts.
          - contradiction.
          - destruct Hcaseone as [Hcaseone | Hcaseone]; destruct Hcaseone as [Hco1 Hco2]. 
            + simpl in Hco1. destruct c0; [ | discriminate Hco1 ].
              simpl. reflexivity.
            + destruct Hco2 as [Hco2 Hco3].
              remember (tag_tree_t t0 sib2) as t_t.
              destruct t_t.
              * discriminate Hco1.
              * destruct c1; [ discriminate Hco1 | ].
                destruct Hco3 as [Hco3 Hco4].
                destruct c0; [ discriminate Hco3 | ].
                unfold delete_check.
                rewrite Hco1.
                unfold delete_check in H0.
                rewrite (match_color _ _ _ H4) in H0.
                rewrite if_else_then_true in H0.
                destruct H0 as [H0 Hco5].
                rewrite <- Hco4.
                rewrite Hco5.
                auto.
        }
        simpl partial_tree_rep.
        Exists p_gpar p_sib_rch.
        entailer!.
      }
      {
        forward.
        color_replace.
        Exists ls.
        Exists p p_gpar p_sib.
        Exists c tg k0 v0 t0 sib1 sib2.
        Exists p_sib_lch p_sib_rch.
        Exists p_root'.
        remember (CaseTTF_sol t (false, c, k, v, tg, T Black sib1 k0 v0 t0 sib2) false) as t_t.
        destruct t_t as [ts br].
        entailer!.
        unfold delete_check in H0.
        rewrite (match_color _ _ _ H4) in H0.
        rewrite if_else_then_true in H0.
        destruct H0 as [H00 H0].
        rewrite <- Heqt_t in H0.
        destruct br; [ split; auto | split; assumption ].
      }

      (* clear all the useless variables and hypothesis *)
      clear H6.
      clear p_root'.
      Intros ls_ p_ p_gpar_ p_sib_.
      Intros c_ tg_ k_ v_ t0_ sib1_ sib2_.
      Intros p_sib_lch_ p_sib_rch_.
      Intros p_root'.
      remember (CaseTTF_sol t (false, c_, k, v, tg_, T Black sib1_ k_ v_ t0_ sib2_) false) as t_t.
      destruct t_t as [ts br].

      (* Case 2 *)
      forward; try aggregate_solve.
      forward_call (sib1_, p_sib_lch_, p_sib_).
      forward_if (temp _t'4 
        (Val.of_bool 
          ((negb (Int.eq (Int.repr (get_color_tree sib1_)) (Int.repr 1))) &&
          (negb (Int.eq (Int.repr (get_color_tree sib2_)) (Int.repr 1)))))); try pointer_destructor.
      {
        forward; try aggregate_solve.
        forward_call (sib2_, p_sib_rch_, p_sib_).
        forward.
        entailer!.
        apply f_equal.
        destruct sib1_.
        - simpl get_color_tree. 
          unfold Int.eq, zeq. simpl. reflexivity.
        - destruct c1; try contradiction.
          simpl get_color_tree.
          unfold Int.eq, zeq. simpl. reflexivity.
      }
      {
        forward.
        nonempty_tree_bycol sib1_.
        simpl get_color_tree in *.
        color_replace.
        entailer!.
      }
      forward_if_wrp.
        (* if (get_color(p_sib->left) != RED && get_color(p_sib->right) != RED) *)
      {
        assert (Hleftnotred : get_color_tree sib1_ <> Col2Z Red).
        {
          intro. rewrite H11 in H10.
          unfold Int.eq, zeq in H10. simpl in H10.
          discriminate. 
        }
        assert (Hrightnotred : get_color_tree sib2_ <> Col2Z Red).
        {
          intro. rewrite H11 in H10.
          unfold Int.eq, zeq in H10. simpl in H10.
          rewrite andb_false_r in H10.
          discriminate. 
        }
        forward.        (* p_sib->color = RED; *)
        forward.        (* p = p_fa; *)
        forward.        (* p_fa = p->fa; *)
        destruct sib1_; destruct sib2_;
        simpl rbtree_rep;
        simpl in H1; simpl in H0.
        {
          Intros.
          Exists (T c_ t k v tg_ (T Red Empty k_ v_ t0_ Empty)) ls_.
          Exists p_par p_gpar_ p_root'.
          entailer!.
          {
            simpl in Heqt_t.
            inversion Heqt_t.
            destruct br; [ discriminate | ].
            (* Case 2, so br = false *)
            rewrite <- H12.
            split; assumption.
          }
          simpl rbtree_rep.
          Exists p_. Exists p_sib_.
          Exists nullval nullval.
          entailer!.
        }
        {
          simpl get_color_tree in *.
          destruct c1; [ contradiction | simpl in H0; discriminate ].
        }
        {
          simpl get_color_tree in *.
          destruct c1; [ contradiction | simpl in H0; discriminate ].
        }
        {
          simpl get_color_tree in *.
          destruct c1; [ contradiction | ].
          destruct c2; [ contradiction | ].
          Intros p_sib_lch_lch p_sib_lch_rch.
          Intros p_sib_rch_lch p_sib_rch_rch.
          Exists (T c_ t k v tg_
            (T Red (T Black sib1_1 k1 v1 t1 sib1_2) k_ v_ t0_
              (T Black sib2_1 k2 v2 t2 sib2_2))) ls_.
          Exists p_par p_gpar_ p_root'.
          entailer!.
          {
            simpl in Heqt_t.
            inversion Heqt_t.
            destruct br; [ discriminate | ].
            (* Case 2, so br = false *)
            rewrite <- H24.
            split; assumption.
          }
          simpl rbtree_rep.
          Exists p_ p_sib_. entailer!.
          Exists p_sib_lch_ p_sib_rch_. entailer!.
          Exists p_sib_rch_lch. Exists p_sib_lch_lch.
          Exists p_sib_lch_rch. Exists p_sib_rch_rch.
          entailer!.
        }
      }
      {
        forward; try aggregate_solve.
        forward_call (sib2_, p_sib_rch_, p_sib_).
        apply semax_if_seq.
        (** Here is a trade-off: we use semax_if_seq to avoid giving tedious
            post-condition. *)
        forward_if_wrp.   (* if (get_color(p_sib->right) != RED) *)
        {
          (* Case 3 *)
          rewrite <- negb_orb in H10.
          rewrite negb_false_iff in H10.
          apply orb_prop in H10.
          destruct H10 as [H10 | H10]; apply int_eq_e in H10; [ | contradiction ].
          destruct sib1_; [ simpl in H10; discriminate | ].
          simpl in H10.
          color_replace.
          simpl rbtree_rep.
          Intros p_sib_lch_lch p_sib_lch_rch.
          forward.
          forward_call (Red, k1, v1, t1, p_sib_lch_lch, p_sib_lch_rch, 
            p_sib_, p_sib_lch_, sib1_1, sib1_2).
                          (* pushdown(p_sib->left); *)
          forward.
          forward.
          forward.    (* p_sib->left->tag = p_sib->tag; *)
          forward.    (* p_sib->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->left->color = BLACK; *)
          forward.    (* p_sib->color = RED; *)
          forward_call
          (Black, k1, (f v1 t1), t0_, 
            Red, k_, v_, default, p_par, 
            (tag_tree_t t1 sib1_1), (tag_tree_t t1 sib1_2), sib2_, 
            p_sib_lch_, p_sib_, p_sib_lch_lch, p_sib_lch_rch, p_sib_rch_, 
            root, p_root', (true, c_, k, v, tg_, t) :: ls_).
          {
            simpl partial_tree_rep.
            Exists p_gpar_ p_.
            entailer!.
          }
          Intros p_root_new.
          subst p_root_new.
          simpl partial_tree_rep.
          clear PNp_gpar_ p_gpar_ p_.
          Intros p_gpar_ p_.
          forward.    (* p_sib = p_fa->right; *)

          assert_PROP (is_pointer_or_null p_sib_lch_) as PNp_sib_lch_ by entailer!.
          forward_call (Black, k1, (f v1 t1), t0_, p_sib_lch_lch, p_sib_, 
            p_par, p_sib_lch_, (tag_tree_t t1 sib1_1), 
            (T Red (tag_tree_t t1 sib1_2) k_ v_ default sib2_)).
                      (* pushdown(p_sib); *)
          {
            simpl rbtree_rep.
            Exists p_sib_lch_rch p_sib_rch_.
            entailer!.
          }
          simpl rbtree_rep.
          Intros p_lch p_rch.
          forward.
          forward.    (* p_sib->tag = p_fa->tag; *)
          forward.    (* p_fa->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->color = p_fa->color; *)
          forward.    (* p_fa->color = BLACK; *)
          forward.
          forward.    (* p_sib->right->color = BLACK; *)
          assert_PROP (is_pointer_or_null p_gpar_) as PNp_gpar_ by entailer!.
          forward_call
          (Black, k, v, default, p_gpar_, 
            c_, k1, (f (f v1 t1) t0_), tg_, 
            t, (tag_tree_t t0_ (tag_tree_t t1 sib1_1)), 
              (T Black (tag_tree_t t1 sib1_2) k_ v_ (t0_ + 0) sib2_), 
            p_par, p_sib_lch_, p_, p_sib_lch_lch, p_sib_, 
            root, p_root', ls_).
                      (* left_rotate_wrap(p_fa, root); *)
          {
            simpl rbtree_rep.
            Exists p_lch p_rch.
            entailer!.
          }
          Intros p_root_new.
          simpl rbtree_rep.
          clear p_lch p_rch.
          Intros p_lch p_rch.
          forward.    (* return ; *)

          simpl tag_tree_t in *.
          simpl in Heqt_t.
          assert (Htsbr : (ts, br) = 
             (T c_ (T Black t k v 0 (tag_tree_t t0_ (tag_tree_t t1 sib1_1))) k1 
               (v1 + t1 + t0_) tg_ (T Black (tag_tree_t t1 sib1_2) k_ v_ (t0_ + 0) sib2_), true)).
          {
            destruct sib2_.
            - assumption.
            - simpl in *. color_replace. assumption.
          }
          inversion Htsbr. clear Htsbr.
          subst br.
          Exists ts.
          Exists ls_.
          sep_apply equivalence_nobox_box'.
          Intros b.
          Exists b p_gpar_.
          entailer!.
          unfold treebox_rep.
          Exists p_sib_lch_.
          simpl rbtree_rep.
          Exists p_par p_sib_. entailer!.
          Exists p_lch. Exists p_.
          Exists p_sib_lch_lch. Exists p_rch.
          entailer!.
        }
        {
        (* Case 4 *)
          nonempty_tree_bycol sib2_.
          simpl in H11.
          color_replace.
          simpl rbtree_rep.
          Intros p_sib_rch_lch p_sib_rch_rch.
          forward_call (Black, k_, v_, t0_, p_sib_lch_, p_sib_rch_,
            p_par, p_sib_, sib1_, 
            (T Red sib2_1 k1 v1 t1 sib2_2)).
                      (* pushdown(p_sib); *)
          {
            simpl rbtree_rep.
            Exists p_sib_rch_lch p_sib_rch_rch.
            entailer!.
          }
          simpl rbtree_rep.
          clear p_sib_rch_lch p_sib_rch_rch.
          Intros p_sib_rch_lch p_sib_rch_rch.
          forward.
          forward.    (* p_sib->tag = p_fa->tag; *)
          forward.    (* p_fa->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->color = p_fa->color; *)
          forward.    (* p_fa->color = BLACK; *)
          forward.
          forward.    (* p_sib->right->color = BLACK; *)
          forward_call
          (Black, k, v, default, p_gpar_, 
            c_, k_, (f v_ t0_), tg_, 
            t, (tag_tree_t t0_ sib1_), 
              (T Black sib2_1 k1 v1 (t0_ + t1) sib2_2), 
            p_par, p_sib_, p_, p_sib_lch_, p_sib_rch_, 
            root, p_root', ls_).
                      (* left_rotate_wrap(p_fa, root); *)
          {
            simpl rbtree_rep.
            Exists p_sib_rch_lch p_sib_rch_rch.
            entailer!.
          }
          Intros p_root_new.
          simpl rbtree_rep.
          Intros p_lch p_rch.
          forward.    (* return ; *)

          simpl in Heqt_t.
          assert (Htsbr : (ts, br) = 
            (T c_ (T Black t k v 0 (tag_tree_t t0_ sib1_)) k_ (v_ + t0_) tg_
                (T Black sib2_1 k1 v1 (t0_ + t1) sib2_2), true)).
          {
            destruct sib1_; simpl in Heqt_t.
            - assumption.
            - destruct c1; assumption.
          }
          inversion Htsbr. clear Htsbr.
          subst br.
          Exists ts.
          Exists ls_.
          sep_apply equivalence_nobox_box'.
          Intros b.
          Exists b p_gpar_.
          entailer!.
          unfold treebox_rep.
          Exists p_sib_.
          simpl rbtree_rep.
          Exists p_par p_sib_rch_. entailer!.
          Exists p_lch. Exists p_.
          Exists p_sib_lch_. Exists p_rch.
          entailer!.
        }
      }
    }
    { (* p is the right child of p_fa *)
      destruct va; [ | contradiction ].
      forward.            (* p_sib = p_fa->right; *)
      forward.
      forward_if          (* if (p_sib->color == RED) *)
      (EX ls_changed : list Half_tree, 
        EX p_changed : val, 
        EX p_gpar_changed : val, 
        EX p_sib_changed : val, 
        EX c_changed : color, 
        EX tg_changed : Tag, 
        EX k_sib : Key, 
        EX v_sib : Value, 
        EX tg_sib : Tag, 
        EX lch_sib : RBtree, 
        EX rch_sib : RBtree, 
        EX p_sib_lch : val, 
        EX p_sib_rch : val, 
        EX p_root' : val, 
        let hft := (true, c_changed, k, v, tg_changed, 
              (T Black lch_sib k_sib v_sib tg_sib rch_sib)) in
        let (ts, br) := (CaseTTF_sol t hft false) in
        PROP (
          (if br then true else delete_check ts
          ls_changed Black) = true;
          CaseTTF_check t hft = true;
          complete_tree_revarg (delete_balance t_initial ls_initial Black)
          = complete_tree_revarg (match (CaseTTF_sol t hft false) with
            | (ts, true) => (ts, ls_changed)
            | (ts, false) => delete_balance ts ls_changed Black
            end); 
            Int.min_signed <= k_sib <= Int.max_signed; 
            is_pointer_or_null p_gpar_changed)
        LOCAL (temp _root root; temp _p p; temp _p_par p_par; 
          temp _p_sib p_sib_changed)
        SEP (rbtree_rep t p_changed p_par;
          rbtree_rep lch_sib p_sib_lch p_sib_changed;
          rbtree_rep rch_sib p_sib_rch p_sib_changed;
          data_at Tsh t_struct_rbtree
          (Vint (Int.repr BLACK_COLOR),
          (Vint (Int.repr k_sib),
          (Vint (Int.repr v_sib),
          (Vint (Int.repr tg_sib), (p_sib_lch, (p_sib_rch, p_par)))))) p_sib_changed;
          data_at Tsh t_struct_rbtree
          (Vint (Int.repr (Col2Z c_changed)),
          (Vint (Int.repr k),
          (Vint (Int.repr v), (Vint (Int.repr tg_changed), 
            (p_sib_changed, (p_changed, p_gpar_changed))))))
          p_par;
          partial_tree_rep ls_changed p_root' p_par p_gpar_changed nullval;
          data_at Tsh (tptr t_struct_rbtree) p_root' root))%assert; try pointer_destructor.
      (** Note that here, _p should be p_changed, though this will not affect the 
          following proof. *)
      {
        color_replace.
        (* show CaseOne_check is true *)
        assert (Hcaseone: (CaseOne_check t
             (true, c, k, v, tg, T Red sib1 k0 v0 t0 sib2)) = true).
        {
          remember (CaseOne_check t
             (true, c, k, v, tg, T Red sib1 k0 v0 t0 sib2)) as bb.
          destruct bb.
          - reflexivity.
          - unfold delete_check in H0. rewrite <- Heqbb in H0.
            rewrite (match_color _ _ _ H4) in H0.
            discriminate.
        }
        apply case_one_true in Hcaseone; [ | assumption ].
        assert (Hcasettf: (CaseTTF_check t
             (true, Red, k, v, default, tag_tree_t t0 sib2)) = true).
        {
          simpl in H0. rewrite (match_color _ _ _ H4) in H0.
          rewrite if_else_then_true in H0. destruct H0 as [H0 _].
          rewrite if_else_then_true in H0. destruct H0 as [H0 _].
          exact H0.
        }
        pose proof Hcasettf as Hcopyttf.
        apply (case_solve_not_null _ _ H4) in Hcasettf.
        (* a critical conclusion *)
        assert (Hfinal:
          complete_tree_revarg (delete_balance t_initial ls_initial Black) = 
          complete_tree_revarg (match (CaseTTF_sol t
             (true, Red, k, v, default, tag_tree_t t0 sib2) false) with
          | (ts, true) => (ts, ((true, Black, k0, f v0 t0, tg, tag_tree_t t0 sib1) :: ls))
          | (ts, false) =>
            delete_balance ts
            ((true, Black, k0, f v0 t0, tg, tag_tree_t t0 sib1) :: ls)
            Black
          end)).
        {
          rewrite H1.
          remember (CaseTTF_sol t (true, Red,  k, v, default, tag_tree_t t0 sib2) false)
            as br_ts.
          destruct br_ts as [t_t br].
          destruct br.
          {
            rewrite Hcaseone.
            reflexivity.
          }
          destruct t_t; [ contradiction | ].
          destruct Hcaseone as [Hcaseone | Hcaseone]; destruct Hcaseone as [Hco1 Hco2]. 
          - rewrite Hco2.
            simpl delete_balance. 
            destruct c0; unfold complete_tree_revarg; simpl complete_tree; 
            [ reflexivity | simpl in Hco1; discriminate ].
            - destruct Hco2 as [Hco2 Hco3]. 
            destruct Hco3 as [Hco3 Hco4].
            destruct c0; [ discriminate | ].
            remember (tag_tree_t t0 sib1) as t_t.
            destruct t_t.
            * discriminate Hco2.
            * destruct c0; [ discriminate Hco2 | ].
              rewrite Hco4.
              reflexivity.
        }
        forward_call (Red, k0, v0, t0, p_sib_lch, p_sib_rch, p_par, p_sib, 
          sib1, sib2).  (* pushdown(p_sib); *)
        forward.
        forward.          (* p_sib->tag = p_fa->tag; *)
        forward.          (* p_fa->tag = DEFAULT_TAG; *)
        forward.          (* p_sib->color = p_fa->color; *)
        forward.          (* p_fa->color = RED; *)
        assert_PROP (is_pointer_or_null p_gpar) as PNp_gpar by entailer!. 
        forward_call      (* right_rotate_wrap(p_fa, root); *)
        (Black, k0, (f v0 t0), tg, 
          Red, k, v, default, p_gpar,
          (tag_tree_t t0 sib1), (tag_tree_t t0 sib2), t, 
          p_sib, p_par, p_sib_lch, p_sib_rch, p, 
          root, p_root', ls).
        Intros p_root_new.
        forward. try aggregate_solve.         (* p_sib = p_fa->left; *)
        nonempty_tree_bycol sib2.
        destruct c0.
        { simpl in Hcopyttf. discriminate Hcopyttf. }
        simpl rbtree_rep.
        Intros p_sib_rch_lch p_sib_rch_rch.

        Exists ((true, Black, k0, f v0 t0, tg, tag_tree_t t0 sib1)
          :: ls).
        Exists p p_sib p_sib_rch.
        Exists Red default k1 v1 (t0 + t1) sib2_1 sib2_2.
        Exists p_sib_rch_lch p_sib_rch_rch.
        Exists p_root_new.
        simpl tag_tree_t in *.
        remember (CaseTTF_sol t (true, Red, k, v, default, 
          T Black sib2_1 k1 v1 (t0 + t1) sib2_2) false) as t_t.
        destruct t_t as [ts br].
        entailer!.
        {
          destruct br; auto.
          destruct ts.
          - contradiction.
          - destruct Hcaseone as [Hcaseone | Hcaseone]; destruct Hcaseone as [Hco1 Hco2]. 
            + simpl in Hco1. destruct c0; [ | discriminate Hco1 ].
              simpl. reflexivity.
            + destruct Hco2 as [Hco2 Hco3].
              remember (tag_tree_t t0 sib1) as t_t.
              destruct t_t.
              * discriminate Hco1.
              * destruct c1; [ discriminate Hco1 | ].
                destruct Hco3 as [Hco3 Hco4].
                destruct c0; [ discriminate Hco3 | ].
                unfold delete_check.
                rewrite Hco1.
                unfold delete_check in H0.
                rewrite (match_color _ _ _ H4) in H0.
                rewrite if_else_then_true in H0.
                destruct H0 as [H0 Hco5].
                rewrite <- Hco4.
                rewrite Hco5.
                auto.
        }
        simpl partial_tree_rep.
        Exists p_gpar p_sib_lch.
        entailer!.
      }
      {
        forward.
        color_replace.
        Exists ls.
        Exists p p_gpar p_sib.
        Exists c tg k0 v0 t0 sib1 sib2.
        Exists p_sib_lch p_sib_rch.
        Exists p_root'.
        remember (CaseTTF_sol t (true, c, k, v, tg, 
          T Black sib1 k0 v0 t0 sib2) false) as t_t.
        destruct t_t as [ts br].
        entailer!.
        unfold delete_check in H0.
        rewrite (match_color _ _ _ H4) in H0.
        rewrite if_else_then_true in H0.
        destruct H0 as [H00 H0].
        rewrite <- Heqt_t in H0.
        destruct br; [ split; auto | split; assumption ].
      }

      (* clear all the useless variables and hypothesis *)
      clear H6.
      clear p_root'.
      Intros ls_ p_ p_gpar_ p_sib_.
      Intros c_ tg_ k_ v_ t0_ sib1_ sib2_.
      Intros p_sib_lch_ p_sib_rch_.
      Intros p_root'.
      remember (CaseTTF_sol t (true, c_, k, v, tg_, 
        T Black sib1_ k_ v_ t0_ sib2_) false) as t_t.
      destruct t_t as [ts br].

      (* Case 2 *)
      forward; try aggregate_solve.
      forward_call (sib1_, p_sib_lch_, p_sib_).
      forward_if (temp _t'8
        (Val.of_bool 
          ((negb (Int.eq (Int.repr (get_color_tree sib1_)) (Int.repr 1))) &&
          (negb (Int.eq (Int.repr (get_color_tree sib2_)) (Int.repr 1)))))); try pointer_destructor.
      {
        forward; try aggregate_solve.
        forward_call (sib2_, p_sib_rch_, p_sib_).
        forward.
        entailer!.
        apply f_equal.
        destruct sib1_.
        - simpl get_color_tree. 
          unfold Int.eq, zeq. simpl. reflexivity.
        - destruct c1; try contradiction.
          simpl get_color_tree.
          unfold Int.eq, zeq. simpl. reflexivity.
      }
      {
        forward.
        nonempty_tree_bycol sib1_.
        simpl get_color_tree in *.
        color_replace.
        entailer!.
      }
      forward_if_wrp.
        (* if (get_color(p_sib->left) != RED && get_color(p_sib->right) != RED) *)
      {
        assert (Hleftnotred : get_color_tree sib1_ <> Col2Z Red).
        {
          intro. rewrite H11 in H10.
          unfold Int.eq, zeq in H10. simpl in H10.
          discriminate. 
        }
        assert (Hrightnotred : get_color_tree sib2_ <> Col2Z Red).
        {
          intro. rewrite H11 in H10.
          unfold Int.eq, zeq in H10. simpl in H10.
          rewrite andb_false_r in H10.
          discriminate. 
        }
        forward.        (* p_sib->color = RED; *)
        forward.        (* p = p_fa; *)
        forward.        (* p_fa = p->fa; *)
        destruct sib1_; destruct sib2_;
        simpl rbtree_rep;
        simpl in H1; simpl in H0.
        {
          Intros.
          Exists (T c_ (T Red Empty k_ v_ t0_ Empty) k v tg_ t) ls_.
          Exists p_par p_gpar_ p_root'.
          entailer!.
          {
            simpl in Heqt_t.
            inversion Heqt_t.
            destruct br; [ discriminate | ].
            (* Case 2, so br = false *)
            rewrite <- H12.
            split; assumption.
          }
          simpl rbtree_rep.
          Exists p_sib_. Exists p_.
          Exists nullval nullval.
          entailer!.
        }
        {
          simpl get_color_tree in *.
          destruct c1; [ contradiction | simpl in H0; discriminate ].
        }
        {
          simpl get_color_tree in *.
          destruct c1; [ contradiction | simpl in H0; discriminate ].
        }
        {
          simpl get_color_tree in *.
          destruct c1; [ contradiction | ].
          destruct c2; [ contradiction | ].
          Intros p_sib_lch_lch p_sib_lch_rch.
          Intros p_sib_rch_lch p_sib_rch_rch.
          Exists (T c_ (T Red (T Black sib1_1 k1 v1 t1 sib1_2) k_ v_ t0_
                (T Black sib2_1 k2 v2 t2 sib2_2)) k v tg_ t) ls_.
          Exists p_par p_gpar_ p_root'.
          entailer!.
          {
            simpl in Heqt_t.
            inversion Heqt_t.
            destruct br; [ discriminate | ].
            (* Case 2, so br = false *)
            rewrite <- H24.
            split; assumption.
          }
          simpl rbtree_rep.
          Exists p_sib_ p_. entailer!.
          Exists p_sib_lch_ p_sib_rch_. entailer!.
          Exists p_sib_rch_lch. Exists p_sib_lch_lch.
          Exists p_sib_lch_rch. Exists p_sib_rch_rch.
          entailer!.
        }
      }
      {
        forward; try aggregate_solve.
        forward_call (sib1_, p_sib_lch_, p_sib_).
        apply semax_if_seq.
        (** Here is a trade-off: we use semax_if_seq to avoid giving tedious
            post-condition. *)
        forward_if_wrp.   (* if (get_color(p_sib->left) != RED) *)
        {
          (* Case 3 *)
          rewrite <- negb_orb in H10.
          rewrite negb_false_iff in H10.
          apply orb_prop in H10.
          destruct H10 as [H10 | H10]; apply int_eq_e in H10; [ contradiction | ].
          destruct sib2_; [ simpl in H10; discriminate | ].
          simpl in H10.
          color_replace.
          simpl rbtree_rep.
          Intros p_sib_rch_lch p_sib_rch_rch.
          forward.
          forward_call (Red, k1, v1, t1, p_sib_rch_lch, p_sib_rch_rch, 
            p_sib_, p_sib_rch_, sib2_1, sib2_2).
                          (* pushdown(p_sib->right); *)
          forward.
          forward.
          forward.    (* p_sib->right->tag = p_sib->tag; *)
          forward.    (* p_sib->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->right->color = BLACK; *)
          forward.    (* p_sib->color = RED; *)
          forward_call
          (Red, k_, v_, default, p_par, 
            Black, k1, (f v1 t1), t0_, 
            sib1_, (tag_tree_t t1 sib2_1), (tag_tree_t t1 sib2_2), 
            p_sib_, p_sib_rch_, p_sib_lch_, p_sib_rch_lch, p_sib_rch_rch, 
            root, p_root', (false, c_, k, v, tg_, t) :: ls_).
                      (* left_rotate_wrap(p_sib, root); *)
          {
            simpl partial_tree_rep.
            Exists p_gpar_ p_.
            entailer!.
          }
          Intros p_root_new.
          subst p_root_new.
          simpl partial_tree_rep.
          clear PNp_gpar_ p_gpar_ p_.
          Intros p_gpar_ p_.
          forward.    (* p_sib = p_fa->left; *)

          assert_PROP (is_pointer_or_null p_sib_rch_) as PNp_sib_rch_ by entailer!.
          forward_call (Black, k1, (f v1 t1), t0_, p_sib_, p_sib_rch_rch, 
            p_par, p_sib_rch_, (T Red sib1_ k_ v_ default (tag_tree_t t1 sib2_1)), 
            (tag_tree_t t1 sib2_2)).
                      (* pushdown(p_sib); *)
          {
            simpl rbtree_rep.
            Exists p_sib_lch_ p_sib_rch_lch.
            entailer!.
          }
          simpl rbtree_rep.
          Intros p_lch p_rch.
          forward.
          forward.    (* p_sib->tag = p_fa->tag; *)
          forward.    (* p_fa->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->color = p_fa->color; *)
          forward.    (* p_fa->color = BLACK; *)
          forward.
          forward.    (* p_sib->left->color = BLACK; *)
          assert_PROP (is_pointer_or_null p_gpar_) as PNp_gpar_ by entailer!.
          forward_call
          (c_, k1, (f (f v1 t1) t0_), tg_, 
            Black, k, v, default, p_gpar_, 
            (T Black sib1_ k_ v_ (t0_ + 0) (tag_tree_t t1 sib2_1)), 
              (tag_tree_t t0_ (tag_tree_t t1 sib2_2)), t, 
            p_sib_rch_, p_par, p_sib_, p_sib_rch_rch, p_, 
            root, p_root', ls_).
                      (* right_rotate_wrap(p_fa, root); *)
          {
            simpl rbtree_rep.
            Exists p_lch p_rch.
            entailer!.
          }
          Intros p_root_new.
          simpl rbtree_rep.
          clear p_lch p_rch.
          Intros p_lch p_rch.
          forward.    (* return ; *)

          simpl tag_tree_t in *.
          simpl in Heqt_t.
          assert (Htsbr : (ts, br) = 
            (T c_ (T Black sib1_ k_ v_ (t0_ + 0) (tag_tree_t t1 sib2_1)) k1
            (v1 + t1 + t0_) tg_ (T Black (tag_tree_t t0_ (tag_tree_t t1 sib2_2)) k v 0 t), true)).
          {
            destruct sib1_.
            - assumption.
            - simpl in *. color_replace. assumption.
          }
          inversion Htsbr. clear Htsbr.
          subst br.
          Exists ts.
          Exists ls_.
          sep_apply equivalence_nobox_box'.
          Intros b.
          Exists b p_gpar_.
          entailer!.
          unfold treebox_rep.
          Exists p_sib_rch_.
          simpl rbtree_rep.
          Exists p_sib_ p_par. entailer!.
          Exists p_sib_rch_rch. Exists p_lch. 
          Exists p_rch. Exists p_.
          entailer!.
        }
        {
        (* Case 4 *)
          nonempty_tree_bycol sib1_.
          simpl in H11.
          color_replace.
          simpl rbtree_rep.
          Intros p_sib_lch_lch p_sib_lch_rch.
          forward_call (Black, k_, v_, t0_, p_sib_lch_, p_sib_rch_,
          p_par, p_sib_, (T Red sib1_1 k1 v1 t1 sib1_2), sib2_).
                      (* pushdown(p_sib); *)
          {
            simpl rbtree_rep.
            Exists p_sib_lch_lch p_sib_lch_rch.
            entailer!.
          }
          simpl rbtree_rep.
          clear p_sib_lch_lch p_sib_lch_rch.
          Intros p_sib_lch_lch p_sib_lch_rch.
          forward.
          forward.    (* p_sib->tag = p_fa->tag; *)
          forward.    (* p_fa->tag = DEFAULT_TAG; *)
          forward.
          forward.    (* p_sib->color = p_fa->color; *)
          forward.    (* p_fa->color = BLACK; *)
          forward.
          forward.    (* p_sib->right->color = BLACK; *)
          forward_call
          (c_, k_, (f v_ t0_), tg_, 
            Black, k, v, default, p_gpar_, 
            (T Black sib1_1 k1 v1 (t0_ + t1) sib1_2), 
              (tag_tree_t t0_ sib2_), t, 
            p_sib_, p_par, p_sib_lch_, p_sib_rch_, p_, 
            root, p_root', ls_).
                      (* left_rotate_wrap(p_fa, root); *)
          {
            simpl rbtree_rep.
            Exists p_sib_lch_lch p_sib_lch_rch.
            entailer!. 
          }
          Intros p_root_new.
          simpl rbtree_rep.
          Intros p_lch p_rch.
          forward.    (* return ; *)

          simpl in Heqt_t.
          inversion Heqt_t. clear Heqt_t.
          subst br.
          Exists ts.
          Exists ls_.
          sep_apply equivalence_nobox_box'.
          Intros b.
          Exists b p_gpar_.
          entailer!.
          unfold treebox_rep.
          Exists p_sib_.
          simpl rbtree_rep.
          Exists p_sib_lch_ p_par. entailer!.
          Exists p_sib_rch_. Exists p_lch. 
          Exists p_rch. Exists p_.
          entailer!.
        }
      }
    }
  }
Qed.

Lemma delete_balance_red : forall t hft_list, 
  delete_balance t hft_list Red = (t, hft_list).
Proof.
  intros.
  destruct hft_list; reflexivity.
Qed.

Theorem body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof. 
  start_function.
  forward.          (* root = t; *)
  unfold treebox_rep.
  Intros p_root.
  forward_loop
  (EX t' : RBtree, 
  EX ls : list Half_tree, 
  EX p_par : val,
  EX b : val, 
  PROP (delete_split x default t' ls = 
    delete_split x default t nil)
  LOCAL (temp _x (Vint (Int.repr x)); 
        temp _t b; temp _root root) 
  SEP (partial_treebox_rep ls root b p_par nullval;
      treebox_rep t' b p_par))
  break:
  (EX t_final : RBtree, 
  EX ls_final : list Half_tree, 
  EX color_final : color, 
  EX p_final : val, 
  EX p_par_final : val,
  EX b_final : val,  
  PROP ((ls_final, t_final, color_final) = 
    delete_with_no_balance x t)
  LOCAL (temp _x (Vint (Int.repr x)); 
        temp _original_color (Vint (Int.repr (Col2Z color_final)));
        temp _final_p p_final;
        temp _final_p_par p_par_final;
        temp _root root) 
  SEP (partial_treebox_rep ls_final root b_final p_par_final nullval;
      data_at Tsh (tptr t_struct_rbtree) p_final b_final; 
      rbtree_rep t_final p_final p_par_final)).
  (* almost the same as insertion... until tree_minimum *)
  {
    Exists t.
    Exists (@nil Half_tree).
    Exists nullval.
    Exists root.
    unfold treebox_rep.
    Exists p_root.
    entailer!.
    simpl partial_treebox_rep.
    entailer!.
  } 
  { 
    Intros t' ls p_par b.
    unfold treebox_rep.
    Intros p.
    forward; try aggregate_solve.          (* p = *t; *)
    forward_if_wrp.
    { (* if the target does not exist *)
      subst p.
      assert_PROP (t' = Empty) as Htempty by (sep_apply rbtree_rep_nullval; entailer).
      forward_call (complete_tree ls Empty, root).
      {
        sep_apply reconstruction_lemma_box.
        subst t'.
        entailer!.
      }
      forward.        (* return; *)
      unfold delete.
      unfold delete_into_base_half. 
      unfold delete_with_no_balance in *.
      rewrite <- H1 in H0.
      unfold delete_split, insert_split in *. 
      simpl general_split in *.
      simpl in H0.
      rewrite <- H1.
      simpl.
      rewrite delete_balance_red.
      unfold treebox_rep.
      Intros p.
      Exists p.
      entailer!.
    }
    { (* in searching for the target *)
      nonempty_tree t'.
      Intros p_lch p_rch.
      forward.        (* y = p->key; *)
      forward_call (c, k, v, t0, p_lch, p_rch, p_par, p, t'1, t'2).
                      (* pushdown(p); *)
      forward_if_wrp.
      { (* x < y *)
        forward.      (* t = &(p->left); *)
        Exists (tag_tree_t t0 t'1). 
        Exists ((false, c, k, v + t0, 0, tag_tree_t t0 t'2) :: ls).
        unfold treebox_rep.
        Exists p (offset_val 16 p).
        entailer!.
        {
          rewrite <- H1.
          unfold delete_split, insert_split.
          simpl.
          strip_0.
          arith_bool.
          rewrite H4.
          symmetry.
          apply general_split_tag. 
        }
        Exists p_lch.
        simpl partial_treebox_rep.
        Exists p_par p_rch b.
        quick_replace_offset_val p.
        unfold_data_at (data_at _ _ _ p).
        entailer!.
      }
      {
        forward_if_wrp.
        { (* x > y *)
          forward.      (* t = &(p->left); *)
          Exists (tag_tree_t t0 t'2). 
          Exists ((true, c, k, v + t0, 0, tag_tree_t t0 t'1) :: ls).
          unfold treebox_rep.
          Exists p (offset_val 20 p).
          entailer!.
          {
            rewrite <- H1.
            unfold delete_split, insert_split.
            simpl.
            strip_0.
            arith_bool.
            rewrite H4, H5.
            symmetry.
            apply general_split_tag. 
          }
          Exists p_rch.
          simpl partial_treebox_rep.
          Exists p_par p_lch b.
          quick_replace_offset_val p.
          unfold_data_at (data_at _ _ _ p).
          entailer!.
        }
        { (* now at the delete point *)
          assert (k = x) by lia.
          arith_bool.
          unfold delete_with_no_balance in H0.
          unfold delete_split at 1 in H1.
          unfold insert_split at 1 in H1.
          simpl general_split at 1 in H1.
          rewrite H5 in H1.
          rewrite H4 in H1.
          rewrite <- H1 in H0.
          simpl delete_root in H0.
          simpl.
          forward.      (* original_color = p->color; *)
          forward; try aggregate_solve.
          forward_if
            (p_lch = nullval \/ p_rch = nullval); try pointer_destructor.
                        (* if (p->left != NULL) *)
          {
            nonempty_tree t'1.
            Intros p_lch_lch p_lch_rch.
            forward; try aggregate_solve.
            forward_if_wrp.
            {
              nonempty_tree t'2.
              Intros p_rch_lch p_rch_rch.
              assert_PROP (field_compatible t_struct_rbtree [StructField _right] p)
                as FCP_right by entailer!.
              forward_call ((T c1 t'2_1 k1 v1 (t0 + t2) t'2_2), (offset_val 20 p), p).
                            (* tmp = tree_minimum(&(p->right)); *)
              2: { intro. discriminate. }
              { 
                unfold treebox_rep.
                Exists p_rch.
                quick_replace_offset_val p.
                unfold_data_at (data_at _ _ _ p).
                entailer!.
                simpl rbtree_rep.
                Exists p_rch_lch p_rch_rch.
                entailer!.
              }
              Intros vret.
              destruct vret as [[[[[[min_b min_p_par] min_ls] min_c] min_k] min_v] min_sib].
              simpl fst in *.
              simpl snd in *.
              unfold treebox_rep.
              Intros min_p.
              simpl rbtree_rep.
              Intros min_p_lch min_p_rch.
              subst min_p_lch.
              forward.      (* targ = *tmp; *)
              forward.      (* original_color = targ->color; *)
              forward.
              forward.      (* targ->left = p->left; *)
              forward.
              forward.      (* p->left->fa = targ; *)
              forward.
              forward.      (* targ->color = p->color; *)
              forward.
              apply semax_if_seq.
              (** Here, since the post-condition can be very complex, 
                  we apply semax_if_seq. *)
              forward_if_wrp.
              {
                (** In this case, min_ls must be empty. *)
                destruct min_ls; simpl partial_treebox_rep.
                - Intros. subst p. entailer!.
                - destruct h as [[[[[va ?] ?] ?] ?] ?].
                  simpl.
                  Intros p_gpar p_sib b_par.
                  destruct va; entailer!.
              }
              {
                destruct min_ls.
                2: {
                  destruct h as [[[[[va ?] ?] ?] ?] ?].
                  simpl.
                  Intros p_gpar p_sib b_par.
                  destruct va;
                    sep_apply field_at_conflict; try apply sepalg_Tsh;
                    sep_apply FF_local_facts;
                    Intros;
                    contradiction.
                }
                simpl partial_treebox_rep.
                Intros.
                subst min_b.
                forward; try aggregate_solve.
                forward.    (* final_p = targ->right; *)
                forward.    (* final_p_par = targ; *)
                forward.    (* targ->fa = p->fa; *)
                forward.    (* *t = targ; *)
                forward_call (p, sizeof t_struct_rbtree).
                            (* freeN(p, sizeof *p); *)
                {
                  quick_replace_offset_val p.
                  sep_apply field_at_gather_right.
                  entailer!.
                  rewrite memory_block_data_at_ by auto.
                  cancel.
                }
                forward.    (* break; *)

                simpl app in H0.
                unfold delete_with_no_balance.
                rewrite <- H1.
                simpl delete_root.
                replace (0 + t0 + t2) with (t0 + t2) by lia.
                simpl default in *.
                rewrite H11.
                simpl app.
                Exists min_sib.
                Exists ((true, c, min_k, min_v, 0, T c0 t'1_1 k0 v0 (0 + t0 + t1)%Z t'1_2) :: ls).
                Exists min_c.
                Exists min_p_rch.
                Exists min_p.
                Exists (offset_val 20 min_p).
                entailer!.
                simpl partial_treebox_rep.
                Exists p_par p_lch b.
                Exists p_lch_lch p_lch_rch.
                quick_replace_offset_val min_p.
                unfold_data_at (data_at _ _ _ min_p).
                entailer!.
              }
              {
                destruct min_ls.
                {
                  simpl partial_treebox_rep.
                  Intros.
                  contradiction.
                }
                forward; try aggregate_solve.
                forward_if
                (PROP ( )
                 LOCAL (temp _t'17 min_p_rch; temp _t'13 min_p_par;
                 temp _t'20 (Vint (Int.repr (Col2Z c))); 
                 temp _t'21 p_lch; temp _t'22 p_lch;
                 temp _original_color (Vint (Int.repr (Col2Z min_c)));
                 temp _targ min_p; temp _tmp min_b; temp _t'11 p_rch;
                 temp _t'10 p_lch; temp _y (Vint (Int.repr k)); 
                 temp _p p; temp _x (Vint (Int.repr x)); 
                 temp _t b; temp _root root)
                 SEP (data_at Tsh (tptr t_struct_rbtree) min_p min_b;
                 data_at Tsh t_struct_rbtree
                   (Vint (Int.repr (Col2Z c)),
                   (Vint (Int.repr min_k),
                   (Vint (Int.repr min_v),
                   (Vint (Int.repr 0), (p_lch, (min_p_rch, min_p_par))))))
                   min_p; emp; rbtree_rep min_sib min_p_rch min_p_par;
                 partial_treebox_rep (h :: min_ls) (offset_val 20 p) min_b
                   min_p_par p;
                 field_at Tsh t_struct_rbtree [StructField _color]
                   (Vint (Int.repr (Col2Z c))) p;
                 field_at Tsh t_struct_rbtree [StructField _key]
                   (Vint (Int.repr k)) p;
                 field_at Tsh t_struct_rbtree [StructField _value]
                   (Vint (Int.repr (v + t0))) p;
                 field_at Tsh t_struct_rbtree [StructField _tag]
                   (Vint (Int.repr 0)) p;
                 field_at Tsh t_struct_rbtree [StructField _left] p_lch p;
                 field_at Tsh t_struct_rbtree [StructField _par] p_par p;
                 data_at Tsh t_struct_rbtree
                   (Vint (Int.repr (Col2Z c0)),
                   (Vint (Int.repr k0),
                   (Vint (Int.repr v0),
                   (Vint (Int.repr (t0 + t1)),
                   (p_lch_lch, (p_lch_rch, min_p)))))) p_lch;
                 rbtree_rep t'1_1 p_lch_lch p_lch;
                 rbtree_rep t'1_2 p_lch_rch p_lch;
                 partial_treebox_rep ls root b p_par nullval;
                 data_at Tsh (tptr t_struct_rbtree) p b)); try pointer_destructor.
                {
                  nonempty_tree min_sib.
                  Intros min_p_rch_lch min_p_rch_rch.
                  forward.
                  forward.
                  forward.    (* targ->right->fa = targ->fa; *)
                  entailer!.
                  simpl rbtree_rep.
                  Exists min_p_rch_lch min_p_rch_rch.
                  entailer!.
                }
                {
                  subst min_p_rch.
                  empty_tree min_sib.
                  forward.
                  simpl rbtree_rep.
                  entailer!.
                }
                forward.
                forward.      (* *tmp = targ->right; *)
                pose proof (list_cons_app min_ls h) as Hlistcons.
                destruct Hlistcons as [ls2 [a Hlistcons]].
                destruct a as [[[[[va' c'] k'] v'] tg'] sib'].
                pose proof H12 as Hturnleftcopy.
                rewrite Hlistcons in Hturnleftcopy.
                rewrite Forall_app in Hturnleftcopy.
                destruct Hturnleftcopy as [_ Hturnleftcopy].
                inversion Hturnleftcopy.
                unfold turn_left in H18.
                subst va'.
                clear x0 l H19 H16 H17.
                (* remove temporary things generated by inversion *)
                rewrite Hlistcons.
                pose proof (partialtreebox_backward ls2 false c' k' v' tg' 
                  sib' (offset_val 20 p) min_b min_p_par p) as Hparback.
                assert_PROP (is_pointer_or_null min_b) as PNmin_b by entailer!.
                sep_apply Hparback; [ assumption | ].
                clear Hparback.
                Intros p_rch' p_rch_rch'. 
                quick_replace_offset_val p.
                Intros.
                sep_apply (field_at_gather_right p).
                forward.
                forward.      (* targ->right = p->right; *)
                forward.
                forward.      (* p->right->fa = targ; *)
                forward.      (* final_p = *tmp; *)
                forward.      (* final_p_par = targ->fa; *)
                forward.
                forward.      (* targ->fa = p->fa; *)
                forward.      (* *t = targ; *)
                forward_call (p, sizeof t_struct_rbtree).
                              (* freeN(p, sizeof *p); *)
                {
                  entailer!.
                  rewrite memory_block_data_at_ by auto.
                  cancel.
                }
                forward.      (* break; *)

                simpl app in H0.
                unfold delete_with_no_balance.
                rewrite <- H1.
                simpl delete_root.
                replace (0 + t0 + t2) with (t0 + t2) by lia.
                simpl default in *.
                rewrite H11.
                simpl app.
                Exists min_sib.
                Exists ((h :: min_ls) ++ (true, c, min_k, min_v, 0, 
                  T c0 t'1_1 k0 v0 (0 + t0 + t1)%Z t'1_2) :: ls).
                Exists min_c.
                Exists min_p_rch.
                Exists min_p_par.
                Exists min_b.
                entailer!.
                eapply derives_trans.
                2: {
                  apply partialtreebox_link with (b1:=(offset_val 20 min_p)) (p1:=min_p).
                }
                rewrite Hlistcons.
                simpl partial_treebox_rep.
                Exists p_par p_lch b.
                Exists p_lch_lch p_lch_rch.
                quick_replace_offset_val min_p.
                unfold_data_at (data_at _ _ _ min_p).
                entailer!.
                eapply derives_trans.
                2: {
                  apply partialtreebox_link with (b1:=
                    (field_address t_struct_rbtree [StructField _left] p_rch')) (p1:=p_rch').
                }
                simpl partial_treebox_rep.
                Exists min_p p_rch_rch' (field_address t_struct_rbtree [StructField _right] min_p).
                entailer!.
              }
            }
            {
              forward.
              entailer!.
              simpl rbtree_rep.
              Exists p_lch_lch p_lch_rch.
              entailer!. 
            }
          }
          {
            forward.
            entailer!.
          }
          Intros.
          forward.
          apply semax_if_seq.
          forward_if_wrp.
          {
            destruct H7; [ contradiction | ].
            subst p_rch.
            remember (tag_tree_t t0 t'2) as tagt'2.
            empty_tree tagt'2.
            rewrite tag_tree_t_empty in H7.
            subst t'2.
            nonempty_tree t'1.
            Intros p_lch_lch p_lch_rch. 
            forward.
            forward.          (* *t = p->left; *)
            forward.
            forward.
            forward.          (* p->left->fa = p->fa; *)
            forward.          (* final_p = *t; *)
            forward.          (* final_p_par = p->fa; *)
            forward_call (p, sizeof t_struct_rbtree).
                              (* freeN(p, sizeof *p); *)
            {
              entailer!.
              rewrite memory_block_data_at_ by auto.
              cancel.
            }
            forward.      (* break; *)

            simpl in H0.
            unfold delete_with_no_balance.
            rewrite <- H1.
            simpl delete_root.
            Exists (T c0 t'1_1 k0 v0 (0 + (0 + t0 + t1))%Z t'1_2).
            Exists ls.
            Exists c.
            Exists p_lch.
            Exists p_par.
            Exists b.
            entailer!.
            simpl rbtree_rep.
            Exists p_lch_lch p_lch_rch.
            entailer!.
          }
          {
            subst p_lch.
            remember (tag_tree_t t0 t'1) as tagt'1.
            empty_tree tagt'1.
            rewrite tag_tree_t_empty in H8.
            subst t'1.
            forward; try aggregate_solve.
            apply semax_if_seq.
            forward_if_wrp.
            {
              nonempty_tree t'2.
              Intros p_rch_lch p_rch_rch. 
              forward.
              forward.        (* *t = p->right; *)
              forward.
              forward.
              forward.        (* p->right->fa = p->fa; *)
              forward.        (* final_p = *t; *)
              forward.        (* final_p_par = p->fa; *)
              forward_call (p, sizeof t_struct_rbtree).
                              (* freeN(p, sizeof *p); *)
              {
                entailer!.
                rewrite memory_block_data_at_ by auto.
                cancel.
              }
              forward.      (* break; *)

              simpl in H0.
              unfold delete_with_no_balance.
              rewrite <- H1.
              simpl delete_root.
              Exists (T c0 t'2_1 k0 v0 (0 + (0 + t0 + t1))%Z t'2_2).
              Exists ls.
              Exists c.
              Exists p_rch.
              Exists p_par.
              Exists b.
              entailer!.
              simpl rbtree_rep.
              Exists p_rch_lch p_rch_rch. 
              entailer!.
            }
            {
              subst p_rch.
              remember (tag_tree_t t0 t'2) as tagt'2.
              empty_tree tagt'2.
              rewrite tag_tree_t_empty in H8.
              subst t'2.
              forward.        (* *t = NULL; *)
              forward.        (* final_p = *t; *)
              forward.        (* final_p_par = p->fa; *)
              forward_call (p, sizeof t_struct_rbtree).
                              (* freeN(p, sizeof *p); *)
              {
                entailer!.
                rewrite memory_block_data_at_ by auto.
                cancel.
              }
              forward.      (* break; *)

              simpl in H0.
              unfold delete_with_no_balance.
              rewrite <- H1.
              simpl delete_root.
              Exists Empty.
              Exists ls.
              Exists c.
              Exists nullval.
              Exists p_par.
              Exists b.
              entailer!.
              simpl rbtree_rep.
              entailer!.
            }
          }
        }
      }
    }
  }
  Intros t_final ls_final color_final p_final p_par_final b_final.
  rewrite <- H1 in H0.
  forward_if
  (EX t_balanced : RBtree, 
   EX ls_balanced : list Half_tree,
   EX b_balanced : val, 
   EX p_par_balanced : val,
   EX p_balanced : val,
  (PROP (complete_tree_revarg (t_balanced, ls_balanced) =
     complete_tree_revarg (delete_balance t_final ls_final color_final))
   LOCAL (temp _x (Vint (Int.repr x));
   temp _original_color (Vint (Int.repr (Col2Z color_final))); temp _final_p p_final;
   temp _final_p_par p_par_final; temp _root root)
   SEP (partial_treebox_rep ls_balanced root b_balanced p_par_balanced nullval;
   data_at Tsh (tptr t_struct_rbtree) p_balanced b_balanced; 
   rbtree_rep t_balanced p_balanced p_par_balanced))); try pointer_destructor.
  {
    color_replace.
    forward_call (t_final, root, p_final, p_par_final, b_final, ls_final).
                            (* delete_balance(final_p, final_p_par, root); *)
    Intros vret.
    destruct vret as [[[t_balanced ls_balanced] b_balanced] p_par_balanced].
    simpl fst in *.
    simpl snd in *.
    unfold treebox_rep.
    Intros p_balanced.
    Exists t_balanced ls_balanced b_balanced p_par_balanced p_balanced.
    entailer!.
  }
  {
    forward.
    Exists t_final ls_final b_final p_par_final p_final.
    entailer!.
    color_replace.
    rewrite delete_balance_red.
    reflexivity. 
  }
  Intros t_balanced ls_balanced b_balanced p_par_balanced p_balanced.
  forward_call ((complete_tree ls_balanced t_balanced), root).
  {
    sep_apply reconstruction_lemma_box.
    entailer!.
  }
  Exists (makeBlack (complete_tree ls_balanced t_balanced)).
  entailer!.
  unfold treebox_rep.
  Intros p.
  Exists p.
  entailer!.
  unfold delete.
  unfold delete_into_base_half.
  rewrite <- H1.
  remember (delete_balance t_final ls_final color_final) as bs_hf.
  destruct bs_hf as [base half].
  unfold complete_tree_revarg in H2.
  simpl in H2.
  rewrite H2.
  entailer!.
Qed.

(* proof for insert_balance *)
Theorem body_insert_balance: 
  semax_body Vprog Gprog f_insert_balance insert_balance_spec.
Proof.
  start_function.
  unfold treebox_rep.
  Intros p_initial.
  forward; try aggregate_solve.
  sep_apply equivalence_box_nobox'.
  Intros p_root.
  (*
  destruct t_initial as [ | c lch k v tg rch] eqn:Et_initial; [ contradiction | ].
  simpl rbtree_rep.
  Intros p_lch p_rch.
  *)
  forward_loop
  (EX t : RBtree, 
  EX ls : list Half_tree, 
  EX p : val, 
  EX p_par : val,
  PROP (t <> Empty; balance' ls_initial t_initial = balance' ls t)
  LOCAL (temp _root root; temp _p p)
  SEP (rbtree_rep t p p_par *
    partial_tree_rep ls p_root p p_par nullval;
    data_at Tsh (tptr t_struct_rbtree) p_root root)).
  {
    Exists t_initial.
    Exists ls_initial.
    Exists p_initial p_par_initial.
    entailer!.
  }
  {
    Intros t ls p p_par.
    destruct t as [ | c lch k v tg rch] eqn:Et; [ contradiction | ].
    simpl rbtree_rep.
    Intros p_lch p_rch.
    forward.            (* p_par = (p -> par); *)
    forward_if_wrp.         (* if (p_par == NULL) *)
    {
      subst p_par.
      empty_partialtree ls.
      forward.          (* return; *)
      Exists (T c lch k v tg rch).
      Exists (@nil Half_tree).
      Exists root nullval. 
      unfold treebox_rep.
      Exists p.
      simpl partial_treebox_rep.
      rewrite H1.
      simpl balance' at 1.
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
    }
    {
      (* second branch: p_par is not NULL *)
      nonempty_partialtree ls.
      destruct h as [[[[[va c_p] k_p] v_p] tg_p] sib].
      Intros p_gpar p_sib.
      forward.        (* p_gfa = p_fa->fa; *)
      forward_if_wrp.     (* if (p_gfa == NULL) *)
      {
        subst p_gpar.
        empty_partialtree ls.
        (* p_gfa is null, then return *)
        forward.      (* return ; *)
        Exists (T c lch k v tg rch).
        Exists ((va, c_p, k_p, v_p, tg_p, sib) :: nil).
        rewrite H1.
        simpl balance' at 1.
        simpl partial_tree_rep.
        destruct va;
          [Exists (field_address t_struct_rbtree [StructField _right] p_par) p_par |
          Exists (field_address t_struct_rbtree [StructField _left] p_par) p_par];
          unfold treebox_rep;
          Exists p;
          simpl rbtree_rep;
          Exists p_lch p_rch;
          simpl partial_treebox_rep;
          Exists nullval p_sib root;
          unfold_data_at (data_at _ _ _ p_par);
          entailer!.
      }
      {
        nonempty_partialtree ls.
        destruct h as [[[[[va_p c_g] k_g] v_g] tg_g] sib_p].
        assert_PROP (is_pointer_or_null p_gpar) as PNp_gpar by entailer!.
        Intros p_ggpar p_par_sib.
        forward.
        forward_if_wrp.           (* if (p_fa->color == BLACK) *)
        {
          (* there is no need to go upward *)
          color_replace.
          forward.    (* return ; *)
          Exists (T c lch k v tg rch).
          Exists ((va, Black, k_p, v_p, tg_p, sib)
            :: (va_p, c_g, k_g, v_g, tg_g, sib_p) :: ls).
          sep_apply equivalence_nobox_box'.
          Intros b_par.
          destruct va;
            [ Exists (field_address t_struct_rbtree [StructField _right] p_par) p_par |
              Exists (field_address t_struct_rbtree [StructField _left] p_par) p_par ];
            rewrite H1;
            unfold treebox_rep;
            Exists p;
            simpl rbtree_rep;
            Exists p_lch p_rch;
            simpl partial_treebox_rep;
            Exists p_gpar p_sib;
            destruct va_p;
              [ Exists (field_address t_struct_rbtree [StructField _right] p_gpar) |
                Exists (field_address t_struct_rbtree [StructField _left] p_gpar) |
                Exists (field_address t_struct_rbtree [StructField _right] p_gpar) |
                Exists (field_address t_struct_rbtree [StructField _left] p_gpar) ];
              Exists p_ggpar p_par_sib b_par;
              unfold_data_at (data_at _ _ _ p_par);
              unfold_data_at (data_at _ _ _ p_gpar);
              entailer!.
        }
        {
          (* otherwise go upward *)
          assert_PROP (tc_val (tptr t_struct_rbtree)
            (if va then p_sib else p)) as H_p1.
          { destruct va; aggregate_solve. }
          assert_PROP (tc_val (tptr t_struct_rbtree)
            (if va then p else p_sib)) as H_p2.
          { destruct va; aggregate_solve. }
          assert_PROP (tc_val (tptr t_struct_rbtree)
            (if va_p then p_par_sib else p_par)) as H_p3.
          { destruct va_p; aggregate_solve. }
          assert_PROP (tc_val (tptr t_struct_rbtree)
            (if va_p then p_par else p_par_sib)) as H_p4.
          { destruct va_p; aggregate_solve. }
          (** All the conclusions above are auxiliary. *)

          forward.
          forward_if_wrp.       (* if (p == p_fa->left) *)
          { destruct va; entailer!. }
          {
            destruct va.
            {
              (* eliminate the case *)
              subst p_sib.
              common_pointer_solve p sib.
            }
            forward.
            forward_if_wrp.     (* if (p_fa == p_gfa->left) *)
            { destruct va_p; entailer!. }
            {
              destruct va_p.
              {
                subst p_par_sib.
                common_pointer_solve p_par sib_p.
              }
              forward.
              forward_call (sib_p, p_par_sib, p_gpar).
              color_replace.
              forward_if_wrp.     (* if (get_color(p_gfa->right) != RED) *)
              {
                (* perform rotations *)
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p_fa->color = BLACK; *)
                assert_PROP (is_pointer_or_null p_ggpar) as PNp_ggpar by entailer!.
                forward_call 
                (Black, k_p, v_p, tg_p, 
                  Red, k_g, v_g, tg_g, p_ggpar, 
                  (T c lch k v tg rch), sib, sib_p,  
                  p_par, p_gpar, p, p_sib, p_par_sib, 
                  root, p_root, ls).
                { simpl rbtree_rep. Exists p_lch p_rch. entailer!. }
                Intros p_root_new.
                forward.        (* return; *)
                Exists (T Black (T c lch k v tg rch) k_p v_p tg_p
                  (T Red sib k_g v_g tg_g sib_p)).
                sep_apply equivalence_nobox_box'.
                Intros b_par.
                Exists ls b_par p_ggpar.
                entailer!.
                {
                  rewrite H1. destruct sib_p.
                  - simpl balance'. reflexivity.
                  - simpl get_color_tree in *. color_replace. 
                    simpl balance'. reflexivity.
                }
                unfold treebox_rep.
                Exists p_par.
                simpl rbtree_rep at 1.
                Intros p_lch0 p_rch0.
                simpl rbtree_rep.
                Exists p p_gpar.
                Exists p_sib p_par_sib.
                Exists p_lch0 p_rch0.
                entailer!.
              }
              {
                nonempty_tree_bycol sib_p.
                simpl in H7.
                color_replace.
                simpl rbtree_rep.
                Intros p_par_sib_lch p_par_sib_rch.
                forward.          (* p_fa->color = BLACK; *)
                forward.
                forward.          (* p_gfa->left->color = BLACK; *)
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p = p_gfa; *)
                simpl balance' in H1.
                Exists 
                (T Red (T Black (T c lch k v tg rch) k_p v_p tg_p sib)
                  k_g v_g tg_g (T Black sib_p1 k0 v0 t0 sib_p2)).
                Exists ls.
                Exists p_gpar p_ggpar.
                simpl rbtree_rep.
                Exists p_par p_par_sib.
                Exists p_par_sib_lch p.
                Exists p_par_sib_rch p_sib.
                Exists p_lch p_rch.
                entailer!.
                discriminate.
              }
            }
            {
              destruct va_p; [ | contradiction ].
              forward.
              forward_call (sib_p, p_par_sib, p_gpar).
              forward_if_wrp. 
              {
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p_fa->color = BLACK; *)
                forward_call
                (Black, k, v, tg, 
                  c_p, k_p, v_p, tg_p, p_gpar, 
                  lch, rch, sib, 
                  p, p_par, p_lch, p_rch, p_sib). 
                forward.
                assert_PROP (is_pointer_or_null p_ggpar) as PNp_ggpar by entailer!.
                forward_call 
                (Red, k_g, v_g, tg_g, p_ggpar, 
                  Black, k, v, tg,  
                  sib_p, lch, (T c_p rch k_p v_p tg_p sib), 
                  p_gpar, p, p_par_sib, p_lch, p_par, 
                  root, p_root, ls). 
                { simpl rbtree_rep. Exists p_rch p_sib. entailer!. }
                Intros p_root_new.
                forward.        (* return; *)
                Exists (T Black (T Red sib_p k_g v_g tg_g lch) k v tg
                  (T Red rch k_p v_p tg_p sib)).
                sep_apply equivalence_nobox_box'.
                Intros b_par.
                Exists ls b_par p_ggpar.
                entailer!.
                color_replace.
                {
                  rewrite H1. destruct sib_p.
                  - simpl balance'. reflexivity.
                  - simpl get_color_tree in *. color_replace. 
                    simpl balance'. reflexivity.
                }
                unfold treebox_rep.
                Exists p.
                simpl rbtree_rep.
                Intros p_lch0 p_rch0.
                Exists p_gpar p_par.
                entailer!.
                Exists p_lch0. Exists p_par_sib.
                Exists p_lch. Exists p_rch0.
                color_replace.
                entailer!.
              }
              {
                (* otherwise change color and push up *)
                nonempty_tree_bycol sib_p.
                simpl in H7, H10.
                color_replace.
                simpl rbtree_rep.
                Intros p_par_sib_lch p_par_sib_rch.
                forward.          (* p_fa->color = BLACK; *)
                forward.
                forward.          (* p_gfa->right->color = BLACK; *)
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p = p_gfa; *)
                simpl balance' in H1.
                Exists 
                (T Red (T Black sib_p1 k0 v0 t0 sib_p2) k_g v_g
                  tg_g (T Black (T c lch k v tg rch) k_p v_p tg_p sib)).
                Exists ls.
                Exists p_gpar p_ggpar.
                simpl rbtree_rep.
                Exists p_par_sib p_par.
                Exists p p_par_sib_lch.
                Exists p_sib p_par_sib_rch.
                Exists p_lch p_rch.
                entailer!.
                color_replace.
                rewrite H1.
                split; [ intro; discriminate | auto ].
              }
            }
          }
          {
            destruct va; [ | contradiction ].
            forward.
            forward_if_wrp.     (* if (p_fa == p_gfa->left) *)
            { destruct va_p; entailer!. }
            {
              destruct va_p. 
              {
                subst p_par_sib.
                common_pointer_solve p_par sib_p.
              }
              forward.
              forward_call (sib_p, p_par_sib, p_gpar).
              forward_if_wrp. 
              {
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p_fa->color = BLACK; *)
                forward_call
                (c_p, k_p, v_p, tg_p, p_gpar, 
                  Black, k, v, tg, 
                  sib, lch, rch,
                  p_par, p, p_sib, p_lch, p_rch).
                forward.
                assert_PROP (is_pointer_or_null p_ggpar) as PNp_ggpar by entailer!.
                forward_call 
                (Black, k, v, tg, 
                  Red, k_g, v_g, tg_g, p_ggpar, 
                  (T c_p sib k_p v_p tg_p lch), rch, sib_p,
                  p, p_gpar, p_par, p_rch, p_par_sib, 
                  root, p_root, ls).
                {
                  simpl rbtree_rep.
                  Exists p_sib p_lch.
                  entailer!.
                }
                Intros p_root_new.
                forward.          (* return; *)
                Exists (T Black (T Red sib k_p v_p tg_p lch) 
                    k v tg (T Red rch k_g v_g tg_g sib_p)).
                sep_apply equivalence_nobox_box'.
                Intros b_par.
                Exists ls b_par p_ggpar.
                color_replace.
                entailer!.
                {
                  rewrite H1. destruct sib_p.
                  - simpl balance'. reflexivity.
                  - simpl get_color_tree in *. color_replace. 
                    simpl balance'. reflexivity.
                }
                unfold treebox_rep.
                Exists p.
                simpl rbtree_rep.
                Intros p_lch0 p_rch0.
                Exists p_par p_gpar.
                entailer!.
                Exists p_rch. Exists p_lch0.
                Exists p_rch0. Exists p_par_sib.
                entailer!.
              }
              {
                (* otherwise change color and push up *)
                nonempty_tree_bycol sib_p.
                simpl in H7, H10.
                color_replace.
                simpl rbtree_rep.
                Intros p_par_sib_lch p_par_sib_rch.
                forward.          (* p_fa->color = BLACK; *)
                forward.
                forward.          (* p_gfa->right->color = BLACK; *)
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p = p_gfa; *)
                Exists 
                (T Red (T Black sib k_p v_p tg_p (T c lch k v tg rch))
                  k_g v_g tg_g (T Black sib_p1 k0 v0 t0 sib_p2)).
                Exists ls.
                Exists p_gpar p_ggpar.
                simpl rbtree_rep.
                Exists p_par p_par_sib.
                Exists p_par_sib_lch p_sib. 
                Exists p_par_sib_rch p.
                Exists p_lch p_rch.
                entailer!.
                simpl balance' in H1.
                color_replace.
                rewrite H1.
                split; [ intro; discriminate | auto ].
              }
            }
            {
              destruct va_p; [| contradiction ].
              forward.
              forward_call (sib_p, p_par_sib, p_gpar).
              color_replace.
              forward_if_wrp.         (* if (get_color(p_gfa->left) != RED) *)
              {
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p_fa->color = BLACK; *)
                assert_PROP (is_pointer_or_null p_ggpar) as PNp_ggpar by entailer!.
                forward_call 
                (Red, k_g, v_g, tg_g, p_ggpar, 
                  Black, k_p, v_p, tg_p, 
                  sib_p, sib, (T c lch k v tg rch), 
                  p_gpar, p_par, p_par_sib, p_sib, p, 
                  root, p_root, ls).
                {   
                  simpl rbtree_rep.
                  Exists p_lch p_rch.
                  entailer!.
                }
                Intros p_root_new.
                forward.        (* return; *)
                Exists (T Black (T Red sib_p k_g v_g tg_g sib)
                      k_p v_p tg_p (T c lch k v tg rch)).
                sep_apply equivalence_nobox_box'.
                Intros b_par.
                Exists ls b_par p_ggpar.
                entailer!.
                {
                  rewrite H1. destruct sib_p.
                  - simpl balance'. reflexivity.
                  - simpl get_color_tree in *. color_replace. 
                    simpl balance'. reflexivity.
                }
                unfold treebox_rep.
                Exists p_par.
                simpl rbtree_rep.
                Intros p_lch0 p_rch0.
                Exists p_gpar p.
                entailer!.
                Exists p_lch0. Exists p_par_sib.
                Exists p_sib. Exists p_rch0.
                entailer!.
              }
              {
                nonempty_tree_bycol sib_p.
                simpl in H7.
                color_replace.
                simpl rbtree_rep.
                Intros p_par_sib_lch p_par_sib_rch.
                forward.          (* p_fa->color = BLACK; *)
                forward.
                forward.          (* p_gfa->left->color = BLACK; *)
                forward.          (* p_gfa->color = RED; *)
                forward.          (* p = p_gfa; *)
                simpl balance' in H1.
                Exists 
                (T Red (T Black sib_p1 k0 v0 t0 sib_p2) k_g v_g tg_g
                  (T Black sib k_p v_p tg_p (T c lch k v tg rch))).
                Exists ls.
                Exists p_gpar p_ggpar.
                simpl rbtree_rep.
                Exists p_par_sib p_par.
                Exists p_sib p_par_sib_lch.
                Exists p p_par_sib_rch.
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

Theorem body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  forward.          (* root = t; *)
  forward.          (* last_node = NULL; *)
  forward_loop 
  (EX t' : RBtree, 
  EX ls : list Half_tree, 
  EX p_par : val,
  EX b : val, 
  PROP (let (ist_h, ist_b) := insert_split x default t' ls in 
    insert' x v t = (ist_h, insert_root x v ist_b))
  LOCAL (temp _last_node p_par; 
        temp _x (Vint (Int.repr x)); 
        temp _value (Vint (Int.repr v)); 
        temp _t b; temp _root root) 
  SEP (partial_treebox_rep ls root b p_par nullval;
      treebox_rep t' b p_par))
  break: 
  (EX t' : RBtree, 
  EX ls : list Half_tree, 
  EX p_par : val,
  EX p : val, 
  EX b : val, 
  PROP (t' <> Empty; insert' x v t = (ls, t'))
  LOCAL (temp _last_node p_par; 
        temp _x (Vint (Int.repr x)); 
        temp _value (Vint (Int.repr v)); 
        temp _t b; temp _root root;
        temp _p p)
  SEP (partial_treebox_rep ls root b p_par nullval;
      data_at Tsh (tptr t_struct_rbtree) p b;
      rbtree_rep t' p p_par)).
  {
    Exists t.
    Exists (@nil Half_tree).
    Exists nullval.
    Exists root.
    unfold treebox_rep.
    Intros p_root.
    Exists p_root.
    entailer!.
    - unfold insert'.
      remember (insert_split x default t []) as hb.
      destruct hb as [h' b'].
      reflexivity.
    - simpl partial_treebox_rep.
      entailer!.
  } 
  { 
    Intros t' ls p_par b.
    unfold treebox_rep.
    Intros p.
    forward; try aggregate_solve.          (* p = *t; *)
    forward_if_wrp.                   (* if (p = NULL) *)
    {
      subst p.
      empty_tree t'.
      simpl in H0.
      (* first branch: arrive at the insert point *)
      forward_call (sizeof t_struct_rbtree).
      { 1: simpl; rep_omega. }
      Intros vret.
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
      forward.        (* break; *)
      Exists (T Red Empty x v default Empty).
      Exists ls p_par vret b.
      entailer!; try discriminate.
      simpl rbtree_rep. 
      Exists nullval nullval.
      entailer!. 
    }
    {
      nonempty_tree t'.
      Intros p_lch p_rch.
      forward.            (* int y = p->key; *)
      forward_call (c, k, v0, t0, p_lch, p_rch, p_par, p, t'1, t'2).
                          (* pushdown(p); *)
      forward_if_wrp.
      { 
        (* if x is already in the tree *)
        subst x.
        forward.                      (* p->value = value; *)
        forward.                      (* break; *)
        Exists (T c (tag_tree_t t0 t'1) k v default (tag_tree_t t0 t'2)).
        Exists ls p_par p b.
        entailer!.
        {
          split; [ intro; discriminate | ].
          unfold insert_split in H0.
          simpl in H0.
          assert (Hkkrefl: (k <? k) = false) by apply Z.ltb_irrefl.
          rewrite Hkkrefl in H0.
          rewrite H0.
          auto.
        }
        {
          simpl rbtree_rep. 
          Exists p_lch p_rch.
          entailer!.
        }
      }
      { 
        forward.          (* last_node = p; *)
        (* otherwise move down the tree *)
        forward_if_wrp.       (* determine whether x < y or not *)
        { 
          (* x < k *)
          forward.        (* t = &(p->left); *)
          Exists (tag_tree_t t0 t'1). 
          Exists ((false, c, k, v0 + t0, 0, tag_tree_t t0 t'2) :: ls).
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
          Exists p_par p_rch b.
          quick_replace_offset_val p.
          unfold_data_at (data_at _ _ _ p).
          entailer!.
        }
        { 
          (* x > k, symmetric case *)
          forward.        (* t = &(p->p->right); *)
          Exists (tag_tree_t t0 t'2). 
          Exists ((true, c, k, v0 + t0, 0, tag_tree_t t0 t'1) :: ls).
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
          Exists p_par p_lch b.
          quick_replace_offset_val p.
          unfold_data_at (data_at _ _ _ p).
          entailer!.
        }
      }
    }
  }
  Intros t' ls p_par p b.
  nonempty_tree t'.
  simpl rbtree_rep.
  Intros p_lch p_rch.
  forward.
  apply semax_if_seq.
  forward_if.                   (* if (p->color == RED) *)
  {
    color_replace.
    forward_call ((T Red t'1 k v0 t0 t'2), root, p_par, b, ls).
    {
      unfold treebox_rep.
      Exists p.
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
    }
    {
      Intros vret.
      destruct vret as [[[t_balanced ls_balanced] b_balanced] p_par_balanced].
      simpl fst in *. simpl snd in *.
      unfold treebox_rep.
      Intros p_balanced.
      sep_apply reconstruction_lemma_box.
      remember (complete_tree ls_balanced t_balanced) as t_res.
      forward_call (t_res, root).
      Exists (makeBlack t_res).
      entailer!.
      eapply Insert.insert_intro.
      - rewrite <- H1. auto.
      - left. split; [ unfold Red_tree | ]; auto.
    }
  }
  {
    color_replace.
    remember (T Black t'1 k v0 t0 t'2) as t'.
    forward_call ((complete_tree ls t'), root).
    {
      instantiate (Frame := nil).
      subst Frame.
      normalize. 
      eapply derives_trans. 
      2: { apply reconstruction_lemma_box with (p:=p) (p_par:=p_par) (b:=b). }
      subst t'.
      simpl rbtree_rep.
      Exists p_lch p_rch.
      entailer!.
    }
    Exists (makeBlack (complete_tree ls t')).
    entailer!.
    eapply Insert.insert_intro.
    - rewrite <- H1. auto.
    - right. split; [ unfold Black_tree | ]; auto.
  }
Qed.

(* proof for free_tree *)
Theorem body_tree_free: semax_body Vprog Gprog f_tree_free tree_free_spec.
Proof.
  start_function.
  forward_if (PROP()LOCAL()SEP()).
  + destruct t; simpl rbtree_rep.
      1: Intros. contradiction.
    Intros pa pb.
    forward; try aggregate_solve.
    forward; try aggregate_solve.
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
Theorem body_treebox_free: semax_body Vprog Gprog f_treebox_free treebox_free_spec.
Proof.
  start_function.
  unfold treebox_rep.
  Intros p.
  forward; try aggregate_solve.
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
  forward_if_wrp.           (* if (x != NULL) *)
  {
    nonempty_tree t.
    Intros p_lch p_rch.
    forward.                (* _t'2 = (_x -> _tag); *)
    forward_call (t2, tg).  (* _t'1 = _Optt(_t'2, _tag); *)
    forward.                (* (_x -> _tag) = _t'1; *)
    simpl rbtree_rep.
    Exists p_lch p_rch.
    assert (Hcommu: t2 + tg = tg + t2) by lia.
    rewrite Hcommu.
    entailer!.
  }
  {
    forward.
    subst p.
    empty_tree t.
    simpl rbtree_rep. 
    entailer!.
  }
Qed.

(* proof for get_color *)
Theorem body_get_color: 
  semax_body Vprog Gprog f_get_color get_color_spec.
Proof.
  start_function.
  forward_if_wrp.
  {
    subst p.
    empty_tree t.
    forward.
    simpl rbtree_rep.
    entailer!.
  }
  {
    nonempty_tree t.
    Intros p_lch p_rch.
    forward.
    forward.
    simpl rbtree_rep.
    Exists p_lch p_rch.
    entailer!.
  }
Qed.

Lemma treebox_rep_nullval : forall (t: RBtree) p_par, 
  treebox_rep t nullval p_par |-- !! False.
Proof.
  intros. unfold treebox_rep. Intros p. assert_PROP (False) by entailer!. contradiction.
Qed.

Ltac empty_treebox t := 
  sep_apply (treebox_rep_nullval t); Intros; contradiction.

(* proof for make_black *)
Theorem body_make_black : semax_body Vprog Gprog f_make_black make_black_spec.
Proof.
  start_function.
  forward_if_wrp.
  {
    subst root.
    empty_treebox t.
  }
  {
    unfold treebox_rep.
    Intros p.
    forward; try aggregate_solve.
    forward_if.
    {
      subst p.
      empty_tree t.
      forward.
      unfold treebox_rep.
      Exists nullval.
      simpl rbtree_rep.
      entailer!.
    }
    {
      nonempty_tree t.
      Intros p_lch p_rch.
      forward.
      entailer!.
      unfold treebox_rep.
      simpl rbtree_rep.
      Exists p p_lch p_rch.
      entailer!.
    }
  }
Qed.


Theorem body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  forward.                    (* res = 0; *)
  forward_loop
  (EX t' : RBtree, EX ls' : list Half_tree, 
   EX p' : val, EX p_par' : val, 
   EX acc_tag : Tag, 
   PROP (is_pointer_or_null p_par'; 
    lookup x t = f_partial (lookup x t') acc_tag;
    complete_tree ls' t' = t)
   LOCAL (temp _res (Vint (Int.repr acc_tag)); temp _p p'; temp _x (Vint (Int.repr x)))
   SEP (rbtree_rep t' p' p_par'; 
    partial_tree_rep ls' p p' p_par' p_par))%assert.
  {
    Exists t (@nil Half_tree) p p_par.
    Exists default.
    simpl partial_tree_rep.
    entailer!.
    remember (lookup x t) as final_res.
    destruct final_res.
    - simpl. f_equal. lia.
    - simpl. reflexivity.
  }
  {
    Intros t' ls' p' p_par' acc_tag.
    (* res' need to be accumulated with tags *)
    (* if (p == NULL) *)
    forward_if (p' <> nullval); try pointer_destructor.
    {
      forward.
      assert_PROP (t' = Empty) by (sep_apply rbtree_rep_nullval; Intros; entailer).
      sep_apply reconstruction_lemma; auto.
      unfold Lookup2Z. rewrite H1.
      subst t'. simpl. entailer!.
    }
    {
      forward. entailer!.
    }
    Intros. nonempty_tree t'.
    Intros p_lch p_rch.
    forward.
    forward_call (acc_tag, t0).
    forward.
    forward.
    pose proof (tri_div_Z k x) as Htridiv.
    unfold tri_div in Htridiv.
    forward_if.
    {
      forward; try aggregate_solve.
      Exists t'2 ((true, c, k, v, t0, t'1) :: ls').
      Exists p_rch p'.
      Exists (Optt acc_tag t0).
      entailer!.
      - rewrite H1.
        simpl lookup.
        rewrite <- Z.ltb_lt in H5.
        rewrite H5 in Htridiv.
        destruct Htridiv.
        rewrite H2, H5.
        simpl Optt.
        remember (lookup x t'2) as partial_res.
        destruct partial_res.
        + simpl. f_equal. lia.
        + simpl. auto.
      - simpl.
        Exists p_par' p_lch.
        entailer!.
    }
    {
      apply Z.ge_le in H5.
      apply Zle_not_lt in H5.
      rewrite <- Z.ltb_nlt in H5.
      rewrite H5 in Htridiv.
      forward.
      forward_if_wrp.
      {
        rewrite <- Z.ltb_lt in H6.
        rewrite H6 in Htridiv.
        forward; try aggregate_solve.
        Exists t'1 ((false, c, k, v, t0, t'2) :: ls').
        Exists p_lch p'.
        Exists (Optt acc_tag t0).
        entailer!.
        - rewrite H1.
          simpl lookup.
          rewrite H5, H6.
          simpl Optt.
          remember (lookup x t'1) as partial_res.
          destruct partial_res.
          + simpl. f_equal. lia.
          + simpl. auto.
        - simpl.
          Exists p_par' p_rch.
          entailer!.
      }
      {
        apply Z.ge_le in H6.
        apply Zle_not_lt in H6.
        rewrite <- Z.ltb_nlt in H6.
        rewrite H6 in Htridiv.
        forward.
        forward_call (v, (Optt acc_tag t0)).
        forward.
        entailer!.
        - do 2 f_equal.
          unfold Lookup2Z.
          rewrite H1.
          simpl lookup.
          rewrite H5, H6.
          simpl.
          lia.
        - pose proof reconstruction_lemma.
          specialize H2 with (p:=p') (p_par:=p_par').
          eapply derives_trans.
          2: { apply H2. }
          entailer!.
          simpl rbtree_rep.
          Exists p_lch p_rch.
          entailer!.
      }
    }
  }
Qed.

(* proof for left_rotate *)
Theorem body_left_rotate : semax_body Vprog Gprog f_left_rotate left_rotate_spec.
Proof.
  start_function.
  forward.    (* r = l->right; *)
  forward; try aggregate_solve.    (* mid = r->left; *)
  forward.    (* l->right = mid; *)  
  forward.
  forward.    (* r->left = l; *)
  forward.    (* r->par = l->par; *)
  forward.    (* l->par = r; *)
  apply semax_if_seq.
  forward_if; try pointer_destructor.
  {
    nonempty_tree tb.
    Intros pb_lch pb_rch.
    forward.  (* mid->par = l; *)
    forward.  (* return r; *)
    simpl rbtree_rep. 
    Exists pb_lch pb_rch.
    entailer!. 
  }
  {
    subst pb. empty_tree tb.
    forward.
    simpl rbtree_rep. 
    entailer!.
  }
Qed.

(* proof for right rotate; it has the same proof script as above *)
Theorem body_right_rotate : semax_body Vprog Gprog f_right_rotate right_rotate_spec.
Proof.
  start_function.
  forward.    (* l = r->left; *)
  forward; try aggregate_solve.    (* mid = l->right; *)
  forward.    (* r->left = mid; *)  
  forward.    (* l->right = r; *)
  forward.
  forward.    (* r->par = l->par; *)
  forward.    (* l->par = r; *)
  apply semax_if_seq.
  forward_if; try pointer_destructor.
  {
    nonempty_tree tb.
    Intros pb_lch pb_rch.
    forward.  (* mid->par = r; *)
    forward.  (* return l; *)
    simpl rbtree_rep. 
    Exists pb_lch pb_rch.
    entailer!. 
  }
  {
    subst pb. empty_tree tb.
    forward.
    simpl rbtree_rep. 
    entailer!.
  }
Qed. 

Theorem body_pushdown: semax_body Vprog Gprog f_pushdown pushdown_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_call (v, tg).             (* p->value = Opvt(p->value, p->tag); *)
  forward.
  forward; try aggregate_solve.
  forward.
  forward_call (lch, tg, p_lch, p). (* tag_tree_t(p->left, p->tag); *)
  forward; try aggregate_solve.
  forward.
  forward_call (rch, tg, p_rch, p). (* tag_tree_t(p->right, p->tag); *)
  forward.                          (* p->tag = DEFAULT_TAG; *)
  entailer!.
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


(* proof for left_rotate_wrap *)
Theorem body_left_rotate_wrap:
  semax_body Vprog Gprog f_left_rotate_wrap left_rotate_wrap_spec.
Proof.
  start_function.
  forward.
  forward_if_wrp.                     (* if (l->par == NULL) *)
  { (* l is the root *)
    subst pl_par.
    empty_partialtree ls.
    forward_call 
    (col_l, key_l, value_l, tag_l, nullval, 
      col_r, key_r, value_r, tag_r, 
      ta, tb, tc, 
      pl, pr, pa, pb, pc).
    forward.                      (* *root = left_rotate(l); *)
    Exists pr.
    simpl partial_tree_rep.
    entailer!.
  }
  {
    forward.
    nonempty_partialtree ls.
    destruct h as [[[[[va c] k] v] tg] sib].
    Intros pl_gpar pl_sib.
    forward.
    { destruct va; aggregate_solve. }
    forward_if_wrp.
    { destruct va; aggregate_solve. }
    {
      (* l is the left branch *)
      destruct va.
      { (* verify that l is on the left *)
        subst pl_sib.
        common_pointer_solve pl sib.
      }
      forward_call 
      (col_l, key_l, value_l, tag_l, pl_par, 
        col_r, key_r, value_r, tag_r, 
        ta, tb, tc, 
        pl, pr, pa, pb, pc).
      forward.                    (* l_fa->left = left_rotate(l); *)
      Exists p_root.
      simpl partial_tree_rep.
      entailer!.
      Exists pl_gpar pl_sib.
      entailer!.
    }
    {
      (* l is the right branch *)
      destruct va; [ | contradiction ].
      forward_call 
      (col_l, key_l, value_l, tag_l, pl_par, 
        col_r, key_r, value_r, tag_r, 
        ta, tb, tc, 
        pl, pr, pa, pb, pc).
      forward.                    (* l_fa->right = left_rotate(l); *)
      Exists p_root.
      simpl partial_tree_rep.
      entailer!.
      Exists pl_gpar pl_sib.
      entailer!.
    }
  }
Qed.

(* proof for right_rotate_wrap *)
Theorem body_right_rotate_wrap:
  semax_body Vprog Gprog f_right_rotate_wrap right_rotate_wrap_spec.
Proof.
  start_function.
  forward.
  forward_if_wrp.                     (* if (r->par == NULL) *)
  { (* r is the root *) 
    subst pr_par.
    empty_partialtree ls.
    forward_call 
    (col_l, key_l, value_l, tag_l, 
      col_r, key_r, value_r, tag_r, nullval, 
      ta, tb, tc, 
      pl, pr, pa, pb, pc).
    forward.                      (* *root = right_rotate(r); *)
    Exists pl.
    simpl partial_tree_rep.
    entailer!.
  }
  {
    forward.
    nonempty_partialtree ls.
    destruct h as [[[[[va c] k] v] tg] sib].
    Intros pr_gpar pr_sib.
    forward.
    { destruct va; aggregate_solve. }
    forward_if_wrp.
    { destruct va; aggregate_solve. }
    {
      (* r is the left branch *)
      destruct va.
      { (* verify that r is on the left *)
        subst pr_sib.
        common_pointer_solve pr sib.
      }
      forward_call 
      (col_l, key_l, value_l, tag_l, 
        col_r, key_r, value_r, tag_r, pr_par, 
        ta, tb, tc, 
        pl, pr, pa, pb, pc).
      forward.                    (* r_fa->left = right_rotate(r); *)
      Exists p_root.
      simpl partial_tree_rep.
      entailer!.
      Exists pr_gpar pr_sib.
      entailer!.
    }
    {
      (* r is the right branch *)
      destruct va; [ | contradiction ].
      forward_call 
      (col_l, key_l, value_l, tag_l, 
        col_r, key_r, value_r, tag_r, pr_par, 
        ta, tb, tc, 
        pl, pr, pa, pb, pc).
      forward.                    (* r_fa->right = right_rotate(r); *)
      Exists p_root.
      simpl partial_tree_rep.
      entailer!.
      Exists pr_gpar pr_sib.
      entailer!.
    }
  }
Qed.