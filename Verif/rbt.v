From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "rbt_bst_6.c"%string.
  Definition normalized := true.
End Info.

Definition _Optt : ident := 64%positive.
Definition _Opvt : ident := 67%positive.
Definition ___builtin_annot : ident := 17%positive.
Definition ___builtin_annot_intval : ident := 18%positive.
Definition ___builtin_bswap : ident := 10%positive.
Definition ___builtin_bswap16 : ident := 12%positive.
Definition ___builtin_bswap32 : ident := 11%positive.
Definition ___builtin_bswap64 : ident := 9%positive.
Definition ___builtin_clz : ident := 43%positive.
Definition ___builtin_clzl : ident := 44%positive.
Definition ___builtin_clzll : ident := 45%positive.
Definition ___builtin_ctz : ident := 46%positive.
Definition ___builtin_ctzl : ident := 47%positive.
Definition ___builtin_ctzll : ident := 48%positive.
Definition ___builtin_debug : ident := 59%positive.
Definition ___builtin_fabs : ident := 13%positive.
Definition ___builtin_fmadd : ident := 51%positive.
Definition ___builtin_fmax : ident := 49%positive.
Definition ___builtin_fmin : ident := 50%positive.
Definition ___builtin_fmsub : ident := 52%positive.
Definition ___builtin_fnmadd : ident := 53%positive.
Definition ___builtin_fnmsub : ident := 54%positive.
Definition ___builtin_fsqrt : ident := 14%positive.
Definition ___builtin_membar : ident := 19%positive.
Definition ___builtin_memcpy_aligned : ident := 15%positive.
Definition ___builtin_read16_reversed : ident := 55%positive.
Definition ___builtin_read32_reversed : ident := 56%positive.
Definition ___builtin_sel : ident := 16%positive.
Definition ___builtin_va_arg : ident := 21%positive.
Definition ___builtin_va_copy : ident := 22%positive.
Definition ___builtin_va_end : ident := 23%positive.
Definition ___builtin_va_start : ident := 20%positive.
Definition ___builtin_write16_reversed : ident := 57%positive.
Definition ___builtin_write32_reversed : ident := 58%positive.
Definition ___compcert_i64_dtos : ident := 28%positive.
Definition ___compcert_i64_dtou : ident := 29%positive.
Definition ___compcert_i64_sar : ident := 40%positive.
Definition ___compcert_i64_sdiv : ident := 34%positive.
Definition ___compcert_i64_shl : ident := 38%positive.
Definition ___compcert_i64_shr : ident := 39%positive.
Definition ___compcert_i64_smod : ident := 36%positive.
Definition ___compcert_i64_smulh : ident := 41%positive.
Definition ___compcert_i64_stod : ident := 30%positive.
Definition ___compcert_i64_stof : ident := 32%positive.
Definition ___compcert_i64_udiv : ident := 35%positive.
Definition ___compcert_i64_umod : ident := 37%positive.
Definition ___compcert_i64_umulh : ident := 42%positive.
Definition ___compcert_i64_utod : ident := 31%positive.
Definition ___compcert_i64_utof : ident := 33%positive.
Definition ___compcert_va_composite : ident := 27%positive.
Definition ___compcert_va_float64 : ident := 26%positive.
Definition ___compcert_va_int32 : ident := 24%positive.
Definition ___compcert_va_int64 : ident := 25%positive.
Definition _b : ident := 73%positive.
Definition _color : ident := 1%positive.
Definition _delete : ident := 110%positive.
Definition _delete_balance : ident := 103%positive.
Definition _final_p : ident := 106%positive.
Definition _final_p_par : ident := 107%positive.
Definition _freeN : ident := 61%positive.
Definition _get_color : ident := 89%positive.
Definition _insert : ident := 96%positive.
Definition _insert_balance : ident := 93%positive.
Definition _insert_balance_simplified : ident := 92%positive.
Definition _key : ident := 2%positive.
Definition _l : ident := 75%positive.
Definition _l_par : ident := 80%positive.
Definition _last_node : ident := 94%positive.
Definition _left : ident := 6%positive.
Definition _left_rotate : ident := 78%positive.
Definition _left_rotate_wrap : ident := 81%positive.
Definition _lookup : ident := 112%positive.
Definition _main : ident := 113%positive.
Definition _make_black : ident := 88%positive.
Definition _mallocN : ident := 60%positive.
Definition _mid : ident := 77%positive.
Definition _original_color : ident := 108%positive.
Definition _p : ident := 68%positive.
Definition _p_gpar : ident := 91%positive.
Definition _p_par : ident := 90%positive.
Definition _p_sib : ident := 102%positive.
Definition _pa : ident := 70%positive.
Definition _par : ident := 8%positive.
Definition _pb : ident := 71%positive.
Definition _pushdown : ident := 87%positive.
Definition _r : ident := 76%positive.
Definition _r_par : ident := 83%positive.
Definition _res : ident := 111%positive.
Definition _right : ident := 7%positive.
Definition _right_rotate : ident := 82%positive.
Definition _right_rotate_wrap : ident := 84%positive.
Definition _root : ident := 79%positive.
Definition _t : ident := 66%positive.
Definition _t1 : ident := 62%positive.
Definition _t2 : ident := 63%positive.
Definition _tag : ident := 4%positive.
Definition _tag_tree_t : ident := 86%positive.
Definition _targ : ident := 109%positive.
Definition _targ_l : ident := 98%positive.
Definition _targ_r : ident := 99%positive.
Definition _tg : ident := 97%positive.
Definition _tmp : ident := 104%positive.
Definition _tree : ident := 5%positive.
Definition _tree_free : ident := 72%positive.
Definition _tree_minimum : ident := 105%positive.
Definition _treebox_free : ident := 74%positive.
Definition _treebox_new : ident := 69%positive.
Definition _update : ident := 101%positive.
Definition _update_aux : ident := 100%positive.
Definition _v : ident := 65%positive.
Definition _value : ident := 3%positive.
Definition _x : ident := 85%positive.
Definition _y : ident := 95%positive.
Definition _t'1 : ident := 114%positive.
Definition _t'10 : ident := 123%positive.
Definition _t'11 : ident := 124%positive.
Definition _t'12 : ident := 125%positive.
Definition _t'13 : ident := 126%positive.
Definition _t'14 : ident := 127%positive.
Definition _t'15 : ident := 128%positive.
Definition _t'16 : ident := 129%positive.
Definition _t'17 : ident := 130%positive.
Definition _t'18 : ident := 131%positive.
Definition _t'19 : ident := 132%positive.
Definition _t'2 : ident := 115%positive.
Definition _t'20 : ident := 133%positive.
Definition _t'21 : ident := 134%positive.
Definition _t'22 : ident := 135%positive.
Definition _t'23 : ident := 136%positive.
Definition _t'24 : ident := 137%positive.
Definition _t'25 : ident := 138%positive.
Definition _t'26 : ident := 139%positive.
Definition _t'27 : ident := 140%positive.
Definition _t'28 : ident := 141%positive.
Definition _t'29 : ident := 142%positive.
Definition _t'3 : ident := 116%positive.
Definition _t'30 : ident := 143%positive.
Definition _t'31 : ident := 144%positive.
Definition _t'32 : ident := 145%positive.
Definition _t'33 : ident := 146%positive.
Definition _t'34 : ident := 147%positive.
Definition _t'4 : ident := 117%positive.
Definition _t'5 : ident := 118%positive.
Definition _t'6 : ident := 119%positive.
Definition _t'7 : ident := 120%positive.
Definition _t'8 : ident := 121%positive.
Definition _t'9 : ident := 122%positive.

Definition f_Optt := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_t1, tuint) :: (_t2, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd (Etempvar _t1 tuint) (Etempvar _t2 tuint) tuint)))
|}.

Definition f_Opvt := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_v, tuint) :: (_t, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd (Etempvar _v tuint) (Etempvar _t tuint) tuint)))
|}.

Definition f_treebox_new := {|
  fn_return := (tptr (tptr (Tstruct _tree noattr)));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (tptr (Tstruct _tree noattr)))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (tptr (Tstruct _tree noattr)) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (tptr (Tstruct _tree noattr))))))
  (Ssequence
    (Sassign
      (Ederef (Etempvar _p (tptr (tptr (Tstruct _tree noattr))))
        (tptr (Tstruct _tree noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Sreturn (Some (Etempvar _p (tptr (tptr (Tstruct _tree noattr))))))))
|}.

Definition f_tree_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_pa, (tptr (Tstruct _tree noattr))) ::
               (_pb, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop One (Etempvar _p (tptr (Tstruct _tree noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Ssequence
    (Sset _pa
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
    (Ssequence
      (Sset _pb
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Scall None
          (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil))
                         tvoid cc_default))
          ((Etempvar _p (tptr (Tstruct _tree noattr))) ::
           (Esizeof (Tstruct _tree noattr) tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar _tree_free (Tfunction
                               (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                               tvoid cc_default))
            ((Etempvar _pa (tptr (Tstruct _tree noattr))) :: nil))
          (Scall None
            (Evar _tree_free (Tfunction
                               (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                               tvoid cc_default))
            ((Etempvar _pb (tptr (Tstruct _tree noattr))) :: nil))))))
  Sskip)
|}.

Definition f_treebox_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_b, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t
    (Ederef (Etempvar _b (tptr (tptr (Tstruct _tree noattr))))
      (tptr (Tstruct _tree noattr))))
  (Ssequence
    (Scall None
      (Evar _tree_free (Tfunction (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                         tvoid cc_default))
      ((Etempvar _t (tptr (Tstruct _tree noattr))) :: nil))
    (Scall None
      (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid
                     cc_default))
      ((Etempvar _b (tptr (tptr (Tstruct _tree noattr)))) ::
       (Esizeof (tptr (Tstruct _tree noattr)) tuint) :: nil))))
|}.

Definition f_left_rotate := {|
  fn_return := (tptr (Tstruct _tree noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _tree noattr))) ::
               (_mid, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _r
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
        (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr))))
  (Ssequence
    (Sset _mid
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr)))
        (Etempvar _mid (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr)))
          (Etempvar _l (tptr (Tstruct _tree noattr))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr)))
              (Etempvar _t'1 (tptr (Tstruct _tree noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr)))
              (Etempvar _r (tptr (Tstruct _tree noattr))))
            (Ssequence
              (Sifthenelse (Ebinop One
                             (Etempvar _mid (tptr (Tstruct _tree noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sassign
                  (Efield
                    (Ederef (Etempvar _mid (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _par
                    (tptr (Tstruct _tree noattr)))
                  (Etempvar _l (tptr (Tstruct _tree noattr))))
                Sskip)
              (Sreturn (Some (Etempvar _r (tptr (Tstruct _tree noattr))))))))))))
|}.

Definition f_left_rotate_wrap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _tree noattr))) ::
                (_root, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l_par, (tptr (Tstruct _tree noattr))) ::
               (_t'3, (tptr (Tstruct _tree noattr))) ::
               (_t'2, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree noattr))) ::
               (_t'5, (tptr (Tstruct _tree noattr))) ::
               (_t'4, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'4
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
        (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
  (Sifthenelse (Ebinop Oeq (Etempvar _t'4 (tptr (Tstruct _tree noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Scall (Some _t'1)
        (Evar _left_rotate (Tfunction
                             (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                             (tptr (Tstruct _tree noattr)) cc_default))
        ((Etempvar _l (tptr (Tstruct _tree noattr))) :: nil))
      (Sassign
        (Ederef (Etempvar _root (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr)))
        (Etempvar _t'1 (tptr (Tstruct _tree noattr)))))
    (Ssequence
      (Sset _l_par
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _l_par (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _t'5 (tptr (Tstruct _tree noattr)))
                       (Etempvar _l (tptr (Tstruct _tree noattr))) tint)
          (Ssequence
            (Scall (Some _t'2)
              (Evar _left_rotate (Tfunction
                                   (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                                   (tptr (Tstruct _tree noattr)) cc_default))
              ((Etempvar _l (tptr (Tstruct _tree noattr))) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _l_par (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left
                (tptr (Tstruct _tree noattr)))
              (Etempvar _t'2 (tptr (Tstruct _tree noattr)))))
          (Ssequence
            (Scall (Some _t'3)
              (Evar _left_rotate (Tfunction
                                   (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                                   (tptr (Tstruct _tree noattr)) cc_default))
              ((Etempvar _l (tptr (Tstruct _tree noattr))) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _l_par (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _right
                (tptr (Tstruct _tree noattr)))
              (Etempvar _t'3 (tptr (Tstruct _tree noattr))))))))))
|}.

Definition f_right_rotate := {|
  fn_return := (tptr (Tstruct _tree noattr));
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (Tstruct _tree noattr))) ::
               (_mid, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
        (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
  (Ssequence
    (Sset _mid
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr)))
        (Etempvar _mid (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr)))
          (Etempvar _r (tptr (Tstruct _tree noattr))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr)))
              (Etempvar _t'1 (tptr (Tstruct _tree noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr)))
              (Etempvar _l (tptr (Tstruct _tree noattr))))
            (Ssequence
              (Sifthenelse (Ebinop One
                             (Etempvar _mid (tptr (Tstruct _tree noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sassign
                  (Efield
                    (Ederef (Etempvar _mid (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _par
                    (tptr (Tstruct _tree noattr)))
                  (Etempvar _r (tptr (Tstruct _tree noattr))))
                Sskip)
              (Sreturn (Some (Etempvar _l (tptr (Tstruct _tree noattr))))))))))))
|}.

Definition f_right_rotate_wrap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _tree noattr))) ::
                (_root, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r_par, (tptr (Tstruct _tree noattr))) ::
               (_t'3, (tptr (Tstruct _tree noattr))) ::
               (_t'2, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree noattr))) ::
               (_t'5, (tptr (Tstruct _tree noattr))) ::
               (_t'4, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'4
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
        (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
  (Sifthenelse (Ebinop Oeq (Etempvar _t'4 (tptr (Tstruct _tree noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Scall (Some _t'1)
        (Evar _right_rotate (Tfunction
                              (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                              (tptr (Tstruct _tree noattr)) cc_default))
        ((Etempvar _r (tptr (Tstruct _tree noattr))) :: nil))
      (Sassign
        (Ederef (Etempvar _root (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr)))
        (Etempvar _t'1 (tptr (Tstruct _tree noattr)))))
    (Ssequence
      (Sset _r_par
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _r_par (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _t'5 (tptr (Tstruct _tree noattr)))
                       (Etempvar _r (tptr (Tstruct _tree noattr))) tint)
          (Ssequence
            (Scall (Some _t'2)
              (Evar _right_rotate (Tfunction
                                    (Tcons (tptr (Tstruct _tree noattr))
                                      Tnil) (tptr (Tstruct _tree noattr))
                                    cc_default))
              ((Etempvar _r (tptr (Tstruct _tree noattr))) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _r_par (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left
                (tptr (Tstruct _tree noattr)))
              (Etempvar _t'2 (tptr (Tstruct _tree noattr)))))
          (Ssequence
            (Scall (Some _t'3)
              (Evar _right_rotate (Tfunction
                                    (Tcons (tptr (Tstruct _tree noattr))
                                      Tnil) (tptr (Tstruct _tree noattr))
                                    cc_default))
              ((Etempvar _r (tptr (Tstruct _tree noattr))) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _r_par (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _right
                (tptr (Tstruct _tree noattr)))
              (Etempvar _t'3 (tptr (Tstruct _tree noattr))))))))))
|}.

Definition f_tag_tree_t := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _tree noattr))) :: (_tag, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop One (Etempvar _x (tptr (Tstruct _tree noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _tag tuint))
      (Scall (Some _t'1)
        (Evar _Optt (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                      cc_default))
        ((Etempvar _t'2 tuint) :: (Etempvar _tag tuint) :: nil)))
    (Sassign
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _tag tuint) (Etempvar _t'1 tuint)))
  Sskip)
|}.

Definition f_pushdown := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, (tptr (Tstruct _tree noattr))) ::
               (_t'3, tuint) :: (_t'2, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _value tuint))
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _tag tuint))
        (Scall (Some _t'1)
          (Evar _Opvt (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                        cc_default))
          ((Etempvar _t'6 tuint) :: (Etempvar _t'7 tuint) :: nil))))
    (Sassign
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _value tuint) (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _tag tuint))
        (Scall None
          (Evar _tag_tree_t (Tfunction
                              (Tcons (tptr (Tstruct _tree noattr))
                                (Tcons tuint Tnil)) tvoid cc_default))
          ((Etempvar _t'4 (tptr (Tstruct _tree noattr))) ::
           (Etempvar _t'5 tuint) :: nil))))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr))))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _tag tuint))
          (Scall None
            (Evar _tag_tree_t (Tfunction
                                (Tcons (tptr (Tstruct _tree noattr))
                                  (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _t'2 (tptr (Tstruct _tree noattr))) ::
             (Etempvar _t'3 tuint) :: nil))))
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _tag tuint)
        (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_make_black := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_root, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq
               (Etempvar _root (tptr (tptr (Tstruct _tree noattr))))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Sreturn None)
  (Ssequence
    (Sset _p
      (Ederef (Etempvar _root (tptr (tptr (Tstruct _tree noattr))))
        (tptr (Tstruct _tree noattr))))
    (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _tree noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn None)
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _color tint)
        (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_get_color := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _tree noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _color tint))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_insert_balance_simplified := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) ::
                (_root, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) ::
               (_p_par, (tptr (Tstruct _tree noattr))) ::
               (_p_gpar, (tptr (Tstruct _tree noattr))) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, (tptr (Tstruct _tree noattr))) ::
               (_t'2, tint) :: (_t'1, (tptr (Tstruct _tree noattr))) ::
               (_t'12, (tptr (Tstruct _tree noattr))) ::
               (_t'11, (tptr (Tstruct _tree noattr))) ::
               (_t'10, (tptr (Tstruct _tree noattr))) ::
               (_t'9, (tptr (Tstruct _tree noattr))) ::
               (_t'8, (tptr (Tstruct _tree noattr))) ::
               (_t'7, (tptr (Tstruct _tree noattr))) ::
               (_t'6, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
      (tptr (Tstruct _tree noattr))))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _p_par
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
        (Ssequence
          (Scall (Some _t'5)
            (Evar _get_color (Tfunction
                               (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                               tint cc_default))
            ((Etempvar _p_par (tptr (Tstruct _tree noattr))) :: nil))
          (Sifthenelse (Ebinop One (Etempvar _t'5 tint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Sreturn None)
            (Ssequence
              (Sset _p_gpar
                (Efield
                  (Ederef (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _par
                  (tptr (Tstruct _tree noattr))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sreturn None)
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _left
                      (tptr (Tstruct _tree noattr))))
                  (Sifthenelse (Ebinop Oeq
                                 (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                 (Etempvar _t'6 (tptr (Tstruct _tree noattr)))
                                 tint)
                    (Ssequence
                      (Ssequence
                        (Sset _t'12
                          (Efield
                            (Ederef
                              (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _right
                            (tptr (Tstruct _tree noattr))))
                        (Scall (Some _t'2)
                          (Evar _get_color (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _tree noattr))
                                               Tnil) tint cc_default))
                          ((Etempvar _t'12 (tptr (Tstruct _tree noattr))) ::
                           nil)))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                                     (Econst_int (Int.repr 1) tint) tint)
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _color tint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Ssequence
                              (Sset _t'11
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _right
                                  (tptr (Tstruct _tree noattr))))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _t'11 (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _color tint)
                                (Econst_int (Int.repr 0) tint)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _color tint)
                                (Econst_int (Int.repr 1) tint))
                              (Sset _p
                                (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))))))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _color tint)
                            (Econst_int (Int.repr 1) tint))
                          (Ssequence
                            (Sset _t'10
                              (Efield
                                (Ederef
                                  (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _right
                                (tptr (Tstruct _tree noattr))))
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _p (tptr (Tstruct _tree noattr)))
                                           (Etempvar _t'10 (tptr (Tstruct _tree noattr)))
                                           tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'1)
                                      (Evar _left_rotate (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _tree noattr))
                                                             Tnil)
                                                           (tptr (Tstruct _tree noattr))
                                                           cc_default))
                                      ((Etempvar _p_par (tptr (Tstruct _tree noattr))) ::
                                       nil))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _left
                                        (tptr (Tstruct _tree noattr)))
                                      (Etempvar _t'1 (tptr (Tstruct _tree noattr)))))
                                  (Scall None
                                    (Evar _right_rotate_wrap (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _tree noattr))
                                                                 (Tcons
                                                                   (tptr (tptr (Tstruct _tree noattr)))
                                                                   Tnil))
                                                               tvoid
                                                               cc_default))
                                    ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                     (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                     nil))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Scall None
                                  (Evar _right_rotate_wrap (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _tree noattr))
                                                               (Tcons
                                                                 (tptr (tptr (Tstruct _tree noattr)))
                                                                 Tnil)) tvoid
                                                             cc_default))
                                  ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                   (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                   nil))))))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'9
                          (Efield
                            (Ederef
                              (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _left
                            (tptr (Tstruct _tree noattr))))
                        (Scall (Some _t'4)
                          (Evar _get_color (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _tree noattr))
                                               Tnil) tint cc_default))
                          ((Etempvar _t'9 (tptr (Tstruct _tree noattr))) ::
                           nil)))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tint)
                                     (Econst_int (Int.repr 1) tint) tint)
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _color tint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Ssequence
                              (Sset _t'8
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _left
                                  (tptr (Tstruct _tree noattr))))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _t'8 (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _color tint)
                                (Econst_int (Int.repr 0) tint)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _color tint)
                                (Econst_int (Int.repr 1) tint))
                              (Sset _p
                                (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))))))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _color tint)
                            (Econst_int (Int.repr 1) tint))
                          (Ssequence
                            (Sset _t'7
                              (Efield
                                (Ederef
                                  (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _left
                                (tptr (Tstruct _tree noattr))))
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _p (tptr (Tstruct _tree noattr)))
                                           (Etempvar _t'7 (tptr (Tstruct _tree noattr)))
                                           tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'3)
                                      (Evar _right_rotate (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _tree noattr))
                                                              Tnil)
                                                            (tptr (Tstruct _tree noattr))
                                                            cc_default))
                                      ((Etempvar _p_par (tptr (Tstruct _tree noattr))) ::
                                       nil))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _right
                                        (tptr (Tstruct _tree noattr)))
                                      (Etempvar _t'3 (tptr (Tstruct _tree noattr)))))
                                  (Scall None
                                    (Evar _left_rotate_wrap (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _tree noattr))
                                                                (Tcons
                                                                  (tptr (tptr (Tstruct _tree noattr)))
                                                                  Tnil))
                                                              tvoid
                                                              cc_default))
                                    ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                     (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                     nil))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Scall None
                                  (Evar _left_rotate_wrap (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _tree noattr))
                                                              (Tcons
                                                                (tptr (tptr (Tstruct _tree noattr)))
                                                                Tnil)) tvoid
                                                            cc_default))
                                  ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                   (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                   nil))))))))))))))))
    Sskip))
|}.

Definition f_insert_balance := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) ::
                (_root, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) ::
               (_p_par, (tptr (Tstruct _tree noattr))) ::
               (_p_gpar, (tptr (Tstruct _tree noattr))) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, (tptr (Tstruct _tree noattr))) ::
               (_t'3, tint) :: (_t'2, (tptr (Tstruct _tree noattr))) ::
               (_t'1, tint) :: (_t'18, (tptr (Tstruct _tree noattr))) ::
               (_t'17, (tptr (Tstruct _tree noattr))) ::
               (_t'16, (tptr (Tstruct _tree noattr))) ::
               (_t'15, (tptr (Tstruct _tree noattr))) ::
               (_t'14, (tptr (Tstruct _tree noattr))) ::
               (_t'13, (tptr (Tstruct _tree noattr))) ::
               (_t'12, (tptr (Tstruct _tree noattr))) ::
               (_t'11, (tptr (Tstruct _tree noattr))) ::
               (_t'10, (tptr (Tstruct _tree noattr))) ::
               (_t'9, (tptr (Tstruct _tree noattr))) ::
               (_t'8, (tptr (Tstruct _tree noattr))) :: (_t'7, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
      (tptr (Tstruct _tree noattr))))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _p_par
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sreturn None)
          (Ssequence
            (Sset _p_gpar
              (Efield
                (Ederef (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _par (tptr (Tstruct _tree noattr))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sreturn None)
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _color tint))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Sreturn None)
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef
                          (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _left
                        (tptr (Tstruct _tree noattr))))
                    (Sifthenelse (Ebinop Oeq
                                   (Etempvar _p (tptr (Tstruct _tree noattr)))
                                   (Etempvar _t'8 (tptr (Tstruct _tree noattr)))
                                   tint)
                      (Ssequence
                        (Sset _t'14
                          (Efield
                            (Ederef
                              (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _left
                            (tptr (Tstruct _tree noattr))))
                        (Sifthenelse (Ebinop Oeq
                                       (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                       (Etempvar _t'14 (tptr (Tstruct _tree noattr)))
                                       tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'18
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _right
                                  (tptr (Tstruct _tree noattr))))
                              (Scall (Some _t'1)
                                (Evar _get_color (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _tree noattr))
                                                     Tnil) tint cc_default))
                                ((Etempvar _t'18 (tptr (Tstruct _tree noattr))) ::
                                 nil)))
                            (Sifthenelse (Ebinop One (Etempvar _t'1 tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _color tint)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Scall None
                                      (Evar _right_rotate_wrap (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _tree noattr))
                                                                   (Tcons
                                                                    (tptr (tptr (Tstruct _tree noattr)))
                                                                    Tnil))
                                                                 tvoid
                                                                 cc_default))
                                      ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                       (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                       nil))
                                    (Sreturn None))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'17
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _right
                                        (tptr (Tstruct _tree noattr))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'17 (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 0) tint)))
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 1) tint))
                                    (Sset _p
                                      (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))))))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'16
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _left
                                  (tptr (Tstruct _tree noattr))))
                              (Scall (Some _t'3)
                                (Evar _get_color (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _tree noattr))
                                                     Tnil) tint cc_default))
                                ((Etempvar _t'16 (tptr (Tstruct _tree noattr))) ::
                                 nil)))
                            (Sifthenelse (Ebinop One (Etempvar _t'3 tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _p (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _color tint)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'2)
                                        (Evar _right_rotate (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _tree noattr))
                                                                Tnil)
                                                              (tptr (Tstruct _tree noattr))
                                                              cc_default))
                                        ((Etempvar _p_par (tptr (Tstruct _tree noattr))) ::
                                         nil))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                            (Tstruct _tree noattr)) _right
                                          (tptr (Tstruct _tree noattr)))
                                        (Etempvar _t'2 (tptr (Tstruct _tree noattr)))))
                                    (Ssequence
                                      (Scall None
                                        (Evar _left_rotate_wrap (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _tree noattr))
                                                                    (Tcons
                                                                    (tptr (tptr (Tstruct _tree noattr)))
                                                                    Tnil))
                                                                  tvoid
                                                                  cc_default))
                                        ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                         (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                         nil))
                                      (Sreturn None)))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'15
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _left
                                        (tptr (Tstruct _tree noattr))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'15 (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 0) tint)))
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 1) tint))
                                    (Sset _p
                                      (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))))))))))
                      (Ssequence
                        (Sset _t'9
                          (Efield
                            (Ederef
                              (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _left
                            (tptr (Tstruct _tree noattr))))
                        (Sifthenelse (Ebinop Oeq
                                       (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                       (Etempvar _t'9 (tptr (Tstruct _tree noattr)))
                                       tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'13
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _right
                                  (tptr (Tstruct _tree noattr))))
                              (Scall (Some _t'5)
                                (Evar _get_color (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _tree noattr))
                                                     Tnil) tint cc_default))
                                ((Etempvar _t'13 (tptr (Tstruct _tree noattr))) ::
                                 nil)))
                            (Sifthenelse (Ebinop One (Etempvar _t'5 tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _p (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _color tint)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'4)
                                        (Evar _left_rotate (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _tree noattr))
                                                               Tnil)
                                                             (tptr (Tstruct _tree noattr))
                                                             cc_default))
                                        ((Etempvar _p_par (tptr (Tstruct _tree noattr))) ::
                                         nil))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                            (Tstruct _tree noattr)) _left
                                          (tptr (Tstruct _tree noattr)))
                                        (Etempvar _t'4 (tptr (Tstruct _tree noattr)))))
                                    (Ssequence
                                      (Scall None
                                        (Evar _right_rotate_wrap (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _tree noattr))
                                                                    (Tcons
                                                                    (tptr (tptr (Tstruct _tree noattr)))
                                                                    Tnil))
                                                                   tvoid
                                                                   cc_default))
                                        ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                         (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                         nil))
                                      (Sreturn None)))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'12
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _right
                                        (tptr (Tstruct _tree noattr))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'12 (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 0) tint)))
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 1) tint))
                                    (Sset _p
                                      (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))))))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'11
                                (Efield
                                  (Ederef
                                    (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _left
                                  (tptr (Tstruct _tree noattr))))
                              (Scall (Some _t'6)
                                (Evar _get_color (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _tree noattr))
                                                     Tnil) tint cc_default))
                                ((Etempvar _t'11 (tptr (Tstruct _tree noattr))) ::
                                 nil)))
                            (Sifthenelse (Ebinop One (Etempvar _t'6 tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _color tint)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Scall None
                                      (Evar _left_rotate_wrap (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _tree noattr))
                                                                  (Tcons
                                                                    (tptr (tptr (Tstruct _tree noattr)))
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                      ((Etempvar _p_gpar (tptr (Tstruct _tree noattr))) ::
                                       (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                       nil))
                                    (Sreturn None))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'10
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _left
                                        (tptr (Tstruct _tree noattr))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'10 (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 0) tint)))
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_gpar (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 1) tint))
                                    (Sset _p
                                      (Etempvar _p_gpar (tptr (Tstruct _tree noattr))))))))))))))))))))
    Sskip))
|}.

Definition f_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) :: (_x, tint) ::
                (_value, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_root, (tptr (tptr (Tstruct _tree noattr)))) ::
               (_p, (tptr (Tstruct _tree noattr))) ::
               (_last_node, (tptr (Tstruct _tree noattr))) :: (_y, tint) ::
               (_t'1, (tptr tvoid)) :: (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _root (Etempvar _t (tptr (tptr (Tstruct _tree noattr)))))
  (Ssequence
    (Sset _last_node (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Sset _p
              (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                (tptr (Tstruct _tree noattr))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _p (tptr (Tstruct _tree noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)
                                     cc_default))
                    ((Esizeof (Tstruct _tree noattr) tuint) :: nil))
                  (Sset _p
                    (Ecast (Etempvar _t'1 (tptr tvoid))
                      (tptr (Tstruct _tree noattr)))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _color tint)
                    (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _key tint)
                      (Etempvar _x tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _value tuint)
                        (Etempvar _value tuint))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _tag tuint)
                          (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _left
                              (tptr (Tstruct _tree noattr)))
                            (Ecast (Econst_int (Int.repr 0) tint)
                              (tptr tvoid)))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _p (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _right
                                (tptr (Tstruct _tree noattr)))
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _p (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _par
                                  (tptr (Tstruct _tree noattr)))
                                (Etempvar _last_node (tptr (Tstruct _tree noattr))))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                                    (tptr (Tstruct _tree noattr)))
                                  (Etempvar _p (tptr (Tstruct _tree noattr))))
                                Sbreak)))))))))
              (Ssequence
                (Sset _y
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _key tint))
                (Ssequence
                  (Scall None
                    (Evar _pushdown (Tfunction
                                      (Tcons (tptr (Tstruct _tree noattr))
                                        Tnil) tvoid cc_default))
                    ((Etempvar _p (tptr (Tstruct _tree noattr))) :: nil))
                  (Sifthenelse (Ebinop Oeq (Etempvar _x tint)
                                 (Etempvar _y tint) tint)
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _value tuint)
                        (Etempvar _value tuint))
                      Sbreak)
                    (Ssequence
                      (Sset _last_node
                        (Etempvar _p (tptr (Tstruct _tree noattr))))
                      (Sifthenelse (Ebinop Olt (Etempvar _x tint)
                                     (Etempvar _y tint) tint)
                        (Sset _t
                          (Eaddrof
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _left
                              (tptr (Tstruct _tree noattr)))
                            (tptr (tptr (Tstruct _tree noattr)))))
                        (Sset _t
                          (Eaddrof
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _right
                              (tptr (Tstruct _tree noattr)))
                            (tptr (tptr (Tstruct _tree noattr)))))))))))))
        Sskip)
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _color tint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Scall None
              (Evar _insert_balance (Tfunction
                                      (Tcons
                                        (tptr (tptr (Tstruct _tree noattr)))
                                        (Tcons
                                          (tptr (tptr (Tstruct _tree noattr)))
                                          Tnil)) tvoid cc_default))
              ((Etempvar _t (tptr (tptr (Tstruct _tree noattr)))) ::
               (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) :: nil))
            Sskip))
        (Scall None
          (Evar _make_black (Tfunction
                              (Tcons (tptr (tptr (Tstruct _tree noattr)))
                                Tnil) tvoid cc_default))
          ((Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) :: nil))))))
|}.

Definition f_update_aux := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _tree noattr))) :: (_tg, tuint) ::
                (_l, tint) :: (_r, tint) :: (_targ_l, tint) ::
                (_targ_r, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tint) :: (_t'3, tint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: (_t'12, tuint) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, tuint) :: (_t'8, tint) ::
               (_t'7, (tptr (Tstruct _tree noattr))) :: (_t'6, tint) ::
               (_t'5, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _t (tptr (Tstruct _tree noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Ogt (Etempvar _l tint) (Etempvar _targ_r tint) tint)
      (Sreturn None)
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _r tint) (Etempvar _targ_l tint)
                     tint)
        (Sreturn None)
        Sskip)
      (Ssequence
        (Sifthenelse (Ebinop Oge (Etempvar _l tint) (Etempvar _targ_l tint)
                       tint)
          (Sset _t'4
            (Ecast
              (Ebinop Ole (Etempvar _r tint) (Etempvar _targ_r tint) tint)
              tbool))
          (Sset _t'4 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'4 tint)
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _tag tuint))
                (Scall (Some _t'1)
                  (Evar _Optt (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                tuint cc_default))
                  ((Etempvar _t'12 tuint) :: (Etempvar _tg tuint) :: nil)))
              (Sassign
                (Efield
                  (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _tag tuint)
                (Etempvar _t'1 tuint)))
            (Sreturn None))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _key tint))
                (Sifthenelse (Ebinop Ole (Etempvar _targ_l tint)
                               (Etempvar _t'10 tint) tint)
                  (Ssequence
                    (Sset _t'11
                      (Efield
                        (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _key tint))
                    (Sset _t'3
                      (Ecast
                        (Ebinop Ole (Etempvar _t'11 tint)
                          (Etempvar _targ_r tint) tint) tbool)))
                  (Sset _t'3 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'3 tint)
                (Ssequence
                  (Ssequence
                    (Sset _t'9
                      (Efield
                        (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _value tuint))
                    (Scall (Some _t'2)
                      (Evar _Opvt (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                    tuint cc_default))
                      ((Etempvar _t'9 tuint) :: (Etempvar _tg tuint) :: nil)))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _value tuint)
                    (Etempvar _t'2 tuint)))
                Sskip))
            (Ssequence
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _left
                    (tptr (Tstruct _tree noattr))))
                (Ssequence
                  (Sset _t'8
                    (Efield
                      (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _key tint))
                  (Scall None
                    (Evar _update_aux (Tfunction
                                        (Tcons (tptr (Tstruct _tree noattr))
                                          (Tcons tuint
                                            (Tcons tint
                                              (Tcons tint
                                                (Tcons tint
                                                  (Tcons tint Tnil))))))
                                        tvoid cc_default))
                    ((Etempvar _t'7 (tptr (Tstruct _tree noattr))) ::
                     (Etempvar _tg tuint) :: (Etempvar _l tint) ::
                     (Etempvar _t'8 tint) :: (Etempvar _targ_l tint) ::
                     (Etempvar _targ_r tint) :: nil))))
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _right
                    (tptr (Tstruct _tree noattr))))
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _key tint))
                  (Scall None
                    (Evar _update_aux (Tfunction
                                        (Tcons (tptr (Tstruct _tree noattr))
                                          (Tcons tuint
                                            (Tcons tint
                                              (Tcons tint
                                                (Tcons tint
                                                  (Tcons tint Tnil))))))
                                        tvoid cc_default))
                    ((Etempvar _t'5 (tptr (Tstruct _tree noattr))) ::
                     (Etempvar _tg tuint) :: (Etempvar _t'6 tint) ::
                     (Etempvar _r tint) :: (Etempvar _targ_l tint) ::
                     (Etempvar _targ_r tint) :: nil)))))))))))
|}.

Definition f_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_root, (tptr (tptr (Tstruct _tree noattr)))) ::
                (_tg, tuint) :: (_targ_l, tint) :: (_targ_r, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _targ_r tint) (Etempvar _targ_l tint)
                 tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Sset _t'1
      (Ederef (Etempvar _root (tptr (tptr (Tstruct _tree noattr))))
        (tptr (Tstruct _tree noattr))))
    (Scall None
      (Evar _update_aux (Tfunction
                          (Tcons (tptr (Tstruct _tree noattr))
                            (Tcons tuint
                              (Tcons tint
                                (Tcons tint (Tcons tint (Tcons tint Tnil))))))
                          tvoid cc_default))
      ((Etempvar _t'1 (tptr (Tstruct _tree noattr))) ::
       (Etempvar _tg tuint) ::
       (Ebinop Osub (Eunop Oneg (Econst_int (Int.repr 2147483647) tint) tint)
         (Econst_int (Int.repr 1) tint) tint) ::
       (Econst_int (Int.repr 2147483647) tint) :: (Etempvar _targ_l tint) ::
       (Etempvar _targ_r tint) :: nil))))
|}.

Definition f_delete_balance := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree noattr))) ::
                (_p_par, (tptr (Tstruct _tree noattr))) ::
                (_root, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p_sib, (tptr (Tstruct _tree noattr))) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'34, tuint) ::
               (_t'33, tint) :: (_t'32, (tptr (Tstruct _tree noattr))) ::
               (_t'31, (tptr (Tstruct _tree noattr))) ::
               (_t'30, (tptr (Tstruct _tree noattr))) ::
               (_t'29, (tptr (Tstruct _tree noattr))) :: (_t'28, tuint) ::
               (_t'27, (tptr (Tstruct _tree noattr))) ::
               (_t'26, (tptr (Tstruct _tree noattr))) :: (_t'25, tuint) ::
               (_t'24, tint) :: (_t'23, (tptr (Tstruct _tree noattr))) ::
               (_t'22, tuint) :: (_t'21, tint) ::
               (_t'20, (tptr (Tstruct _tree noattr))) ::
               (_t'19, (tptr (Tstruct _tree noattr))) ::
               (_t'18, (tptr (Tstruct _tree noattr))) ::
               (_t'17, (tptr (Tstruct _tree noattr))) :: (_t'16, tuint) ::
               (_t'15, (tptr (Tstruct _tree noattr))) ::
               (_t'14, (tptr (Tstruct _tree noattr))) :: (_t'13, tuint) ::
               (_t'12, tint) :: (_t'11, (tptr (Tstruct _tree noattr))) ::
               (_t'10, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sassign
            (Ederef (Etempvar _root (tptr (tptr (Tstruct _tree noattr))))
              (tptr (Tstruct _tree noattr)))
            (Etempvar _p (tptr (Tstruct _tree noattr))))
          (Sreturn None))
        Sskip)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _get_color (Tfunction
                               (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                               tint cc_default))
            ((Etempvar _p (tptr (Tstruct _tree noattr))) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _color tint)
                (Econst_int (Int.repr 0) tint))
              (Sreturn None))
            Sskip))
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _p (tptr (Tstruct _tree noattr)))
                         (Etempvar _t'10 (tptr (Tstruct _tree noattr))) tint)
            (Ssequence
              (Sset _p_sib
                (Efield
                  (Ederef (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _right
                  (tptr (Tstruct _tree noattr))))
              (Ssequence
                (Ssequence
                  (Sset _t'33
                    (Efield
                      (Ederef (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _color tint))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'33 tint)
                                 (Econst_int (Int.repr 1) tint) tint)
                    (Ssequence
                      (Scall None
                        (Evar _pushdown (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _tree noattr))
                                            Tnil) tvoid cc_default))
                        ((Etempvar _p_sib (tptr (Tstruct _tree noattr))) ::
                         nil))
                      (Ssequence
                        (Ssequence
                          (Sset _t'34
                            (Efield
                              (Ederef
                                (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _tag tuint))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _tag tuint)
                            (Etempvar _t'34 tuint)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _tag tuint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _color tint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _color tint)
                                (Econst_int (Int.repr 1) tint))
                              (Ssequence
                                (Scall None
                                  (Evar _left_rotate_wrap (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _tree noattr))
                                                              (Tcons
                                                                (tptr (tptr (Tstruct _tree noattr)))
                                                                Tnil)) tvoid
                                                            cc_default))
                                  ((Etempvar _p_par (tptr (Tstruct _tree noattr))) ::
                                   (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                   nil))
                                (Sset _p_sib
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _right
                                    (tptr (Tstruct _tree noattr))))))))))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'32
                        (Efield
                          (Ederef
                            (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _left
                          (tptr (Tstruct _tree noattr))))
                      (Scall (Some _t'3)
                        (Evar _get_color (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _tree noattr))
                                             Tnil) tint cc_default))
                        ((Etempvar _t'32 (tptr (Tstruct _tree noattr))) ::
                         nil)))
                    (Sifthenelse (Ebinop One (Etempvar _t'3 tint)
                                   (Econst_int (Int.repr 1) tint) tint)
                      (Ssequence
                        (Ssequence
                          (Sset _t'31
                            (Efield
                              (Ederef
                                (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _right
                              (tptr (Tstruct _tree noattr))))
                          (Scall (Some _t'5)
                            (Evar _get_color (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _tree noattr))
                                                 Tnil) tint cc_default))
                            ((Etempvar _t'31 (tptr (Tstruct _tree noattr))) ::
                             nil)))
                        (Sset _t'4
                          (Ecast
                            (Ebinop One (Etempvar _t'5 tint)
                              (Econst_int (Int.repr 1) tint) tint) tbool)))
                      (Sset _t'4 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'4 tint)
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _color tint)
                        (Econst_int (Int.repr 1) tint))
                      (Ssequence
                        (Sset _p
                          (Etempvar _p_par (tptr (Tstruct _tree noattr))))
                        (Sset _p_par
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _par
                            (tptr (Tstruct _tree noattr))))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'30
                            (Efield
                              (Ederef
                                (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _right
                              (tptr (Tstruct _tree noattr))))
                          (Scall (Some _t'2)
                            (Evar _get_color (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _tree noattr))
                                                 Tnil) tint cc_default))
                            ((Etempvar _t'30 (tptr (Tstruct _tree noattr))) ::
                             nil)))
                        (Sifthenelse (Ebinop One (Etempvar _t'2 tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'29
                                (Efield
                                  (Ederef
                                    (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _left
                                  (tptr (Tstruct _tree noattr))))
                              (Scall None
                                (Evar _pushdown (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _tree noattr))
                                                    Tnil) tvoid cc_default))
                                ((Etempvar _t'29 (tptr (Tstruct _tree noattr))) ::
                                 nil)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'27
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _left
                                    (tptr (Tstruct _tree noattr))))
                                (Ssequence
                                  (Sset _t'28
                                    (Efield
                                      (Ederef
                                        (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _tag tuint))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'27 (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _tag tuint)
                                    (Etempvar _t'28 tuint))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _tag tuint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'26
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _left
                                        (tptr (Tstruct _tree noattr))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'26 (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 0) tint)))
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 1) tint))
                                    (Ssequence
                                      (Scall None
                                        (Evar _right_rotate_wrap (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _tree noattr))
                                                                    (Tcons
                                                                    (tptr (tptr (Tstruct _tree noattr)))
                                                                    Tnil))
                                                                   tvoid
                                                                   cc_default))
                                        ((Etempvar _p_sib (tptr (Tstruct _tree noattr))) ::
                                         (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                         nil))
                                      (Sset _p_sib
                                        (Efield
                                          (Ederef
                                            (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                            (Tstruct _tree noattr)) _right
                                          (tptr (Tstruct _tree noattr))))))))))
                          Sskip))
                      (Ssequence
                        (Scall None
                          (Evar _pushdown (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _tree noattr))
                                              Tnil) tvoid cc_default))
                          ((Etempvar _p_sib (tptr (Tstruct _tree noattr))) ::
                           nil))
                        (Ssequence
                          (Ssequence
                            (Sset _t'25
                              (Efield
                                (Ederef
                                  (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _tag tuint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _tag tuint)
                              (Etempvar _t'25 tuint)))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _tag tuint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Ssequence
                                (Sset _t'24
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Etempvar _t'24 tint)))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'23
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _right
                                        (tptr (Tstruct _tree noattr))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'23 (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 0) tint)))
                                  (Ssequence
                                    (Scall None
                                      (Evar _left_rotate_wrap (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _tree noattr))
                                                                  (Tcons
                                                                    (tptr (tptr (Tstruct _tree noattr)))
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                      ((Etempvar _p_par (tptr (Tstruct _tree noattr))) ::
                                       (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                       nil))
                                    (Sreturn None)))))))))))))
            (Ssequence
              (Sset _p_sib
                (Efield
                  (Ederef (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _left
                  (tptr (Tstruct _tree noattr))))
              (Ssequence
                (Ssequence
                  (Sset _t'21
                    (Efield
                      (Ederef (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _color tint))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'21 tint)
                                 (Econst_int (Int.repr 1) tint) tint)
                    (Ssequence
                      (Scall None
                        (Evar _pushdown (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _tree noattr))
                                            Tnil) tvoid cc_default))
                        ((Etempvar _p_sib (tptr (Tstruct _tree noattr))) ::
                         nil))
                      (Ssequence
                        (Ssequence
                          (Sset _t'22
                            (Efield
                              (Ederef
                                (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _tag tuint))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _tag tuint)
                            (Etempvar _t'22 tuint)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _tag tuint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _color tint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _color tint)
                                (Econst_int (Int.repr 1) tint))
                              (Ssequence
                                (Scall None
                                  (Evar _right_rotate_wrap (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _tree noattr))
                                                               (Tcons
                                                                 (tptr (tptr (Tstruct _tree noattr)))
                                                                 Tnil)) tvoid
                                                             cc_default))
                                  ((Etempvar _p_par (tptr (Tstruct _tree noattr))) ::
                                   (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                   nil))
                                (Sset _p_sib
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _left
                                    (tptr (Tstruct _tree noattr))))))))))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'20
                        (Efield
                          (Ederef
                            (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _left
                          (tptr (Tstruct _tree noattr))))
                      (Scall (Some _t'7)
                        (Evar _get_color (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _tree noattr))
                                             Tnil) tint cc_default))
                        ((Etempvar _t'20 (tptr (Tstruct _tree noattr))) ::
                         nil)))
                    (Sifthenelse (Ebinop One (Etempvar _t'7 tint)
                                   (Econst_int (Int.repr 1) tint) tint)
                      (Ssequence
                        (Ssequence
                          (Sset _t'19
                            (Efield
                              (Ederef
                                (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _right
                              (tptr (Tstruct _tree noattr))))
                          (Scall (Some _t'9)
                            (Evar _get_color (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _tree noattr))
                                                 Tnil) tint cc_default))
                            ((Etempvar _t'19 (tptr (Tstruct _tree noattr))) ::
                             nil)))
                        (Sset _t'8
                          (Ecast
                            (Ebinop One (Etempvar _t'9 tint)
                              (Econst_int (Int.repr 1) tint) tint) tbool)))
                      (Sset _t'8 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'8 tint)
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _color tint)
                        (Econst_int (Int.repr 1) tint))
                      (Ssequence
                        (Sset _p
                          (Etempvar _p_par (tptr (Tstruct _tree noattr))))
                        (Sset _p_par
                          (Efield
                            (Ederef
                              (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _par
                            (tptr (Tstruct _tree noattr))))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'18
                            (Efield
                              (Ederef
                                (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _left
                              (tptr (Tstruct _tree noattr))))
                          (Scall (Some _t'6)
                            (Evar _get_color (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _tree noattr))
                                                 Tnil) tint cc_default))
                            ((Etempvar _t'18 (tptr (Tstruct _tree noattr))) ::
                             nil)))
                        (Sifthenelse (Ebinop One (Etempvar _t'6 tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'17
                                (Efield
                                  (Ederef
                                    (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _right
                                  (tptr (Tstruct _tree noattr))))
                              (Scall None
                                (Evar _pushdown (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _tree noattr))
                                                    Tnil) tvoid cc_default))
                                ((Etempvar _t'17 (tptr (Tstruct _tree noattr))) ::
                                 nil)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'15
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _right
                                    (tptr (Tstruct _tree noattr))))
                                (Ssequence
                                  (Sset _t'16
                                    (Efield
                                      (Ederef
                                        (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _tag tuint))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'15 (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _tag tuint)
                                    (Etempvar _t'16 tuint))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _tag tuint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'14
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _right
                                        (tptr (Tstruct _tree noattr))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'14 (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 0) tint)))
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 1) tint))
                                    (Ssequence
                                      (Scall None
                                        (Evar _left_rotate_wrap (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _tree noattr))
                                                                    (Tcons
                                                                    (tptr (tptr (Tstruct _tree noattr)))
                                                                    Tnil))
                                                                  tvoid
                                                                  cc_default))
                                        ((Etempvar _p_sib (tptr (Tstruct _tree noattr))) ::
                                         (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                         nil))
                                      (Sset _p_sib
                                        (Efield
                                          (Ederef
                                            (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                            (Tstruct _tree noattr)) _left
                                          (tptr (Tstruct _tree noattr))))))))))
                          Sskip))
                      (Ssequence
                        (Scall None
                          (Evar _pushdown (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _tree noattr))
                                              Tnil) tvoid cc_default))
                          ((Etempvar _p_sib (tptr (Tstruct _tree noattr))) ::
                           nil))
                        (Ssequence
                          (Ssequence
                            (Sset _t'13
                              (Efield
                                (Ederef
                                  (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _tag tuint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _tag tuint)
                              (Etempvar _t'13 tuint)))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _tag tuint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Ssequence
                                (Sset _t'12
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Etempvar _t'12 tint)))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _p_par (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _color tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'11
                                      (Efield
                                        (Ederef
                                          (Etempvar _p_sib (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _left
                                        (tptr (Tstruct _tree noattr))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'11 (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _color
                                        tint) (Econst_int (Int.repr 0) tint)))
                                  (Ssequence
                                    (Scall None
                                      (Evar _right_rotate_wrap (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _tree noattr))
                                                                   (Tcons
                                                                    (tptr (tptr (Tstruct _tree noattr)))
                                                                    Tnil))
                                                                 tvoid
                                                                 cc_default))
                                      ((Etempvar _p_par (tptr (Tstruct _tree noattr))) ::
                                       (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                                       nil))
                                    (Sreturn None))))))))))))))))))
  Sskip)
|}.

Definition f_tree_minimum := {|
  fn_return := (tptr (tptr (Tstruct _tree noattr)));
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tmp, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _tmp
        (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Scall None
          (Evar _pushdown (Tfunction
                            (Tcons (tptr (Tstruct _tree noattr)) Tnil) tvoid
                            cc_default))
          ((Etempvar _tmp (tptr (Tstruct _tree noattr))) :: nil))
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _tmp (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _t'1 (tptr (Tstruct _tree noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sreturn (Some (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))))
            (Sset _t
              (Eaddrof
                (Efield
                  (Ederef (Etempvar _tmp (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _left
                  (tptr (Tstruct _tree noattr)))
                (tptr (tptr (Tstruct _tree noattr))))))))))
  Sskip)
|}.

Definition f_delete := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) :: (_x, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_root, (tptr (tptr (Tstruct _tree noattr)))) ::
               (_final_p, (tptr (Tstruct _tree noattr))) ::
               (_final_p_par, (tptr (Tstruct _tree noattr))) ::
               (_original_color, tint) ::
               (_p, (tptr (Tstruct _tree noattr))) :: (_y, tint) ::
               (_tmp, (tptr (tptr (Tstruct _tree noattr)))) ::
               (_targ, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (tptr (Tstruct _tree noattr)))) ::
               (_t'22, (tptr (Tstruct _tree noattr))) ::
               (_t'21, (tptr (Tstruct _tree noattr))) :: (_t'20, tint) ::
               (_t'19, (tptr (Tstruct _tree noattr))) ::
               (_t'18, (tptr (Tstruct _tree noattr))) ::
               (_t'17, (tptr (Tstruct _tree noattr))) ::
               (_t'16, (tptr (Tstruct _tree noattr))) ::
               (_t'15, (tptr (Tstruct _tree noattr))) ::
               (_t'14, (tptr (Tstruct _tree noattr))) ::
               (_t'13, (tptr (Tstruct _tree noattr))) ::
               (_t'12, (tptr (Tstruct _tree noattr))) ::
               (_t'11, (tptr (Tstruct _tree noattr))) ::
               (_t'10, (tptr (Tstruct _tree noattr))) ::
               (_t'9, (tptr (Tstruct _tree noattr))) ::
               (_t'8, (tptr (Tstruct _tree noattr))) ::
               (_t'7, (tptr (Tstruct _tree noattr))) ::
               (_t'6, (tptr (Tstruct _tree noattr))) ::
               (_t'5, (tptr (Tstruct _tree noattr))) ::
               (_t'4, (tptr (Tstruct _tree noattr))) ::
               (_t'3, (tptr (Tstruct _tree noattr))) ::
               (_t'2, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _root (Etempvar _t (tptr (tptr (Tstruct _tree noattr)))))
  (Ssequence
    (Sloop
      (Ssequence
        Sskip
        (Ssequence
          (Sset _p
            (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
              (tptr (Tstruct _tree noattr))))
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _p (tptr (Tstruct _tree noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Ssequence
              (Scall None
                (Evar _make_black (Tfunction
                                    (Tcons
                                      (tptr (tptr (Tstruct _tree noattr)))
                                      Tnil) tvoid cc_default))
                ((Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) ::
                 nil))
              (Sreturn None))
            (Ssequence
              (Sset _y
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _key tint))
              (Ssequence
                (Scall None
                  (Evar _pushdown (Tfunction
                                    (Tcons (tptr (Tstruct _tree noattr))
                                      Tnil) tvoid cc_default))
                  ((Etempvar _p (tptr (Tstruct _tree noattr))) :: nil))
                (Sifthenelse (Ebinop Olt (Etempvar _x tint)
                               (Etempvar _y tint) tint)
                  (Sset _t
                    (Eaddrof
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _left
                        (tptr (Tstruct _tree noattr)))
                      (tptr (tptr (Tstruct _tree noattr)))))
                  (Sifthenelse (Ebinop Ogt (Etempvar _x tint)
                                 (Etempvar _y tint) tint)
                    (Sset _t
                      (Eaddrof
                        (Efield
                          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _right
                          (tptr (Tstruct _tree noattr)))
                        (tptr (tptr (Tstruct _tree noattr)))))
                    (Ssequence
                      (Sset _original_color
                        (Efield
                          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _color tint))
                      (Ssequence
                        (Ssequence
                          (Sset _t'10
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _left
                              (tptr (Tstruct _tree noattr))))
                          (Sifthenelse (Ebinop One
                                         (Etempvar _t'10 (tptr (Tstruct _tree noattr)))
                                         (Ecast
                                           (Econst_int (Int.repr 0) tint)
                                           (tptr tvoid)) tint)
                            (Ssequence
                              (Sset _t'11
                                (Efield
                                  (Ederef
                                    (Etempvar _p (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _right
                                  (tptr (Tstruct _tree noattr))))
                              (Sifthenelse (Ebinop One
                                             (Etempvar _t'11 (tptr (Tstruct _tree noattr)))
                                             (Ecast
                                               (Econst_int (Int.repr 0) tint)
                                               (tptr tvoid)) tint)
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'1)
                                      (Evar _tree_minimum (Tfunction
                                                            (Tcons
                                                              (tptr (tptr (Tstruct _tree noattr)))
                                                              Tnil)
                                                            (tptr (tptr (Tstruct _tree noattr)))
                                                            cc_default))
                                      ((Eaddrof
                                         (Efield
                                           (Ederef
                                             (Etempvar _p (tptr (Tstruct _tree noattr)))
                                             (Tstruct _tree noattr)) _right
                                           (tptr (Tstruct _tree noattr)))
                                         (tptr (tptr (Tstruct _tree noattr)))) ::
                                       nil))
                                    (Sset _tmp
                                      (Etempvar _t'1 (tptr (tptr (Tstruct _tree noattr))))))
                                  (Ssequence
                                    (Sset _targ
                                      (Ederef
                                        (Etempvar _tmp (tptr (tptr (Tstruct _tree noattr))))
                                        (tptr (Tstruct _tree noattr))))
                                    (Ssequence
                                      (Sset _original_color
                                        (Efield
                                          (Ederef
                                            (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                            (Tstruct _tree noattr)) _color
                                          tint))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'22
                                            (Efield
                                              (Ederef
                                                (Etempvar _p (tptr (Tstruct _tree noattr)))
                                                (Tstruct _tree noattr)) _left
                                              (tptr (Tstruct _tree noattr))))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                (Tstruct _tree noattr)) _left
                                              (tptr (Tstruct _tree noattr)))
                                            (Etempvar _t'22 (tptr (Tstruct _tree noattr)))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'21
                                              (Efield
                                                (Ederef
                                                  (Etempvar _p (tptr (Tstruct _tree noattr)))
                                                  (Tstruct _tree noattr))
                                                _left
                                                (tptr (Tstruct _tree noattr))))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'21 (tptr (Tstruct _tree noattr)))
                                                  (Tstruct _tree noattr))
                                                _par
                                                (tptr (Tstruct _tree noattr)))
                                              (Etempvar _targ (tptr (Tstruct _tree noattr)))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'20
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _p (tptr (Tstruct _tree noattr)))
                                                    (Tstruct _tree noattr))
                                                  _color tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                    (Tstruct _tree noattr))
                                                  _color tint)
                                                (Etempvar _t'20 tint)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'13
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                      (Tstruct _tree noattr))
                                                    _par
                                                    (tptr (Tstruct _tree noattr))))
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _t'13 (tptr (Tstruct _tree noattr)))
                                                               (Etempvar _p (tptr (Tstruct _tree noattr)))
                                                               tint)
                                                  (Ssequence
                                                    (Sset _final_p
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                          (Tstruct _tree noattr))
                                                        _right
                                                        (tptr (Tstruct _tree noattr))))
                                                    (Sset _final_p_par
                                                      (Etempvar _targ (tptr (Tstruct _tree noattr)))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'17
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                            (Tstruct _tree noattr))
                                                          _right
                                                          (tptr (Tstruct _tree noattr))))
                                                      (Sifthenelse (Ebinop One
                                                                    (Etempvar _t'17 (tptr (Tstruct _tree noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                        (Ssequence
                                                          (Sset _t'18
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                                (Tstruct _tree noattr))
                                                              _right
                                                              (tptr (Tstruct _tree noattr))))
                                                          (Ssequence
                                                            (Sset _t'19
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                                  (Tstruct _tree noattr))
                                                                _par
                                                                (tptr (Tstruct _tree noattr))))
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _t'18 (tptr (Tstruct _tree noattr)))
                                                                  (Tstruct _tree noattr))
                                                                _par
                                                                (tptr (Tstruct _tree noattr)))
                                                              (Etempvar _t'19 (tptr (Tstruct _tree noattr))))))
                                                        Sskip))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'16
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                              (Tstruct _tree noattr))
                                                            _right
                                                            (tptr (Tstruct _tree noattr))))
                                                        (Sassign
                                                          (Ederef
                                                            (Etempvar _tmp (tptr (tptr (Tstruct _tree noattr))))
                                                            (tptr (Tstruct _tree noattr)))
                                                          (Etempvar _t'16 (tptr (Tstruct _tree noattr)))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'15
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _p (tptr (Tstruct _tree noattr)))
                                                                (Tstruct _tree noattr))
                                                              _right
                                                              (tptr (Tstruct _tree noattr))))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                                (Tstruct _tree noattr))
                                                              _right
                                                              (tptr (Tstruct _tree noattr)))
                                                            (Etempvar _t'15 (tptr (Tstruct _tree noattr)))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'14
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _p (tptr (Tstruct _tree noattr)))
                                                                  (Tstruct _tree noattr))
                                                                _right
                                                                (tptr (Tstruct _tree noattr))))
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _t'14 (tptr (Tstruct _tree noattr)))
                                                                  (Tstruct _tree noattr))
                                                                _par
                                                                (tptr (Tstruct _tree noattr)))
                                                              (Etempvar _targ (tptr (Tstruct _tree noattr)))))
                                                          (Ssequence
                                                            (Sset _final_p
                                                              (Ederef
                                                                (Etempvar _tmp (tptr (tptr (Tstruct _tree noattr))))
                                                                (tptr (Tstruct _tree noattr))))
                                                            (Sset _final_p_par
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                                  (Tstruct _tree noattr))
                                                                _par
                                                                (tptr (Tstruct _tree noattr)))))))))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'12
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _p (tptr (Tstruct _tree noattr)))
                                                        (Tstruct _tree noattr))
                                                      _par
                                                      (tptr (Tstruct _tree noattr))))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _targ (tptr (Tstruct _tree noattr)))
                                                        (Tstruct _tree noattr))
                                                      _par
                                                      (tptr (Tstruct _tree noattr)))
                                                    (Etempvar _t'12 (tptr (Tstruct _tree noattr)))))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                                                      (tptr (Tstruct _tree noattr)))
                                                    (Etempvar _targ (tptr (Tstruct _tree noattr))))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _freeN (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                      ((Etempvar _p (tptr (Tstruct _tree noattr))) ::
                                                       (Esizeof (Tstruct _tree noattr) tuint) ::
                                                       nil))
                                                    Sbreak))))))))))
                                Sskip))
                            Sskip))
                        (Ssequence
                          (Ssequence
                            (Sset _t'2
                              (Efield
                                (Ederef
                                  (Etempvar _p (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _left
                                (tptr (Tstruct _tree noattr))))
                            (Sifthenelse (Ebinop One
                                           (Etempvar _t'2 (tptr (Tstruct _tree noattr)))
                                           (Ecast
                                             (Econst_int (Int.repr 0) tint)
                                             (tptr tvoid)) tint)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'9
                                    (Efield
                                      (Ederef
                                        (Etempvar _p (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _left
                                      (tptr (Tstruct _tree noattr))))
                                  (Sassign
                                    (Ederef
                                      (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                                      (tptr (Tstruct _tree noattr)))
                                    (Etempvar _t'9 (tptr (Tstruct _tree noattr)))))
                                (Ssequence
                                  (Sset _t'7
                                    (Efield
                                      (Ederef
                                        (Etempvar _p (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _left
                                      (tptr (Tstruct _tree noattr))))
                                  (Ssequence
                                    (Sset _t'8
                                      (Efield
                                        (Ederef
                                          (Etempvar _p (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _par
                                        (tptr (Tstruct _tree noattr))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'7 (tptr (Tstruct _tree noattr)))
                                          (Tstruct _tree noattr)) _par
                                        (tptr (Tstruct _tree noattr)))
                                      (Etempvar _t'8 (tptr (Tstruct _tree noattr)))))))
                              (Ssequence
                                (Sset _t'3
                                  (Efield
                                    (Ederef
                                      (Etempvar _p (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _right
                                    (tptr (Tstruct _tree noattr))))
                                (Sifthenelse (Ebinop One
                                               (Etempvar _t'3 (tptr (Tstruct _tree noattr)))
                                               (Ecast
                                                 (Econst_int (Int.repr 0) tint)
                                                 (tptr tvoid)) tint)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'6
                                        (Efield
                                          (Ederef
                                            (Etempvar _p (tptr (Tstruct _tree noattr)))
                                            (Tstruct _tree noattr)) _right
                                          (tptr (Tstruct _tree noattr))))
                                      (Sassign
                                        (Ederef
                                          (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                                          (tptr (Tstruct _tree noattr)))
                                        (Etempvar _t'6 (tptr (Tstruct _tree noattr)))))
                                    (Ssequence
                                      (Sset _t'4
                                        (Efield
                                          (Ederef
                                            (Etempvar _p (tptr (Tstruct _tree noattr)))
                                            (Tstruct _tree noattr)) _right
                                          (tptr (Tstruct _tree noattr))))
                                      (Ssequence
                                        (Sset _t'5
                                          (Efield
                                            (Ederef
                                              (Etempvar _p (tptr (Tstruct _tree noattr)))
                                              (Tstruct _tree noattr)) _par
                                            (tptr (Tstruct _tree noattr))))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _t'4 (tptr (Tstruct _tree noattr)))
                                              (Tstruct _tree noattr)) _par
                                            (tptr (Tstruct _tree noattr)))
                                          (Etempvar _t'5 (tptr (Tstruct _tree noattr)))))))
                                  (Sassign
                                    (Ederef
                                      (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                                      (tptr (Tstruct _tree noattr)))
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)))))))
                          (Ssequence
                            (Sset _final_p
                              (Ederef
                                (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                                (tptr (Tstruct _tree noattr))))
                            (Ssequence
                              (Sset _final_p_par
                                (Efield
                                  (Ederef
                                    (Etempvar _p (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _par
                                  (tptr (Tstruct _tree noattr))))
                              (Ssequence
                                (Scall None
                                  (Evar _freeN (Tfunction
                                                 (Tcons (tptr tvoid)
                                                   (Tcons tint Tnil)) tvoid
                                                 cc_default))
                                  ((Etempvar _p (tptr (Tstruct _tree noattr))) ::
                                   (Esizeof (Tstruct _tree noattr) tuint) ::
                                   nil))
                                Sbreak)))))))))))))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _original_color tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Scall None
          (Evar _delete_balance (Tfunction
                                  (Tcons (tptr (Tstruct _tree noattr))
                                    (Tcons (tptr (Tstruct _tree noattr))
                                      (Tcons
                                        (tptr (tptr (Tstruct _tree noattr)))
                                        Tnil))) tvoid cc_default))
          ((Etempvar _final_p (tptr (Tstruct _tree noattr))) ::
           (Etempvar _final_p_par (tptr (Tstruct _tree noattr))) ::
           (Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) :: nil))
        Sskip)
      (Scall None
        (Evar _make_black (Tfunction
                            (Tcons (tptr (tptr (Tstruct _tree noattr))) Tnil)
                            tvoid cc_default))
        ((Etempvar _root (tptr (tptr (Tstruct _tree noattr)))) :: nil)))))
|}.

Definition f_lookup := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree noattr))) :: (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tuint) :: (_t'2, tuint) :: (_t'1, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tint) ::
               (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _res (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _tree noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip)
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _tag tuint))
              (Scall (Some _t'1)
                (Evar _Optt (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                              cc_default))
                ((Etempvar _res tuint) :: (Etempvar _t'6 tuint) :: nil)))
            (Sset _res (Etempvar _t'1 tuint)))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _key tint))
            (Sifthenelse (Ebinop Olt (Etempvar _t'3 tint) (Etempvar _x tint)
                           tint)
              (Sset _p
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _right
                  (tptr (Tstruct _tree noattr))))
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _key tint))
                (Sifthenelse (Ebinop Ogt (Etempvar _t'4 tint)
                               (Etempvar _x tint) tint)
                  (Sset _p
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _left
                      (tptr (Tstruct _tree noattr))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'5
                        (Efield
                          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _value tuint))
                      (Scall (Some _t'2)
                        (Evar _Opvt (Tfunction
                                      (Tcons tuint (Tcons tuint Tnil)) tuint
                                      cc_default))
                        ((Etempvar _t'5 tuint) :: (Etempvar _res tuint) ::
                         nil)))
                    (Sreturn (Some (Etempvar _t'2 tuint)))))))))))
    Sskip))
|}.

Definition composites : list composite_definition :=
(Composite _tree Struct
   ((_color, tint) :: (_key, tint) :: (_value, tuint) :: (_tag, tuint) ::
    (_left, (tptr (Tstruct _tree noattr))) ::
    (_right, (tptr (Tstruct _tree noattr))) ::
    (_par, (tptr (Tstruct _tree noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_freeN,
   Gfun(External (EF_external "freeN"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tint Tnil))
     tvoid cc_default)) :: (_Optt, Gfun(Internal f_Optt)) ::
 (_Opvt, Gfun(Internal f_Opvt)) ::
 (_treebox_new, Gfun(Internal f_treebox_new)) ::
 (_tree_free, Gfun(Internal f_tree_free)) ::
 (_treebox_free, Gfun(Internal f_treebox_free)) ::
 (_left_rotate, Gfun(Internal f_left_rotate)) ::
 (_left_rotate_wrap, Gfun(Internal f_left_rotate_wrap)) ::
 (_right_rotate, Gfun(Internal f_right_rotate)) ::
 (_right_rotate_wrap, Gfun(Internal f_right_rotate_wrap)) ::
 (_tag_tree_t, Gfun(Internal f_tag_tree_t)) ::
 (_pushdown, Gfun(Internal f_pushdown)) ::
 (_make_black, Gfun(Internal f_make_black)) ::
 (_get_color, Gfun(Internal f_get_color)) ::
 (_insert_balance_simplified, Gfun(Internal f_insert_balance_simplified)) ::
 (_insert_balance, Gfun(Internal f_insert_balance)) ::
 (_insert, Gfun(Internal f_insert)) ::
 (_update_aux, Gfun(Internal f_update_aux)) ::
 (_update, Gfun(Internal f_update)) ::
 (_delete_balance, Gfun(Internal f_delete_balance)) ::
 (_tree_minimum, Gfun(Internal f_tree_minimum)) ::
 (_delete, Gfun(Internal f_delete)) :: (_lookup, Gfun(Internal f_lookup)) ::
 nil).

Definition public_idents : list ident :=
(_lookup :: _delete :: _tree_minimum :: _delete_balance :: _update ::
 _update_aux :: _insert :: _insert_balance :: _insert_balance_simplified ::
 _get_color :: _make_black :: _pushdown :: _tag_tree_t ::
 _right_rotate_wrap :: _right_rotate :: _left_rotate_wrap :: _left_rotate ::
 _treebox_free :: _tree_free :: _treebox_new :: _Opvt :: _Optt :: _freeN ::
 _mallocN :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


