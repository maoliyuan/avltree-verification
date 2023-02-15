/**
 * 
 * Author: zqy1018
 * Update time: 2021. 4. 23
 * Encoded with UTF-8
 * 
 * Features:
 * 1. Specified the value and tag as Z (Integers), and operation as addition.
 * 2. Specified value and tag as unsigned int, to avoid adding too many constraints.
 * 
 */

#include <stddef.h>

#define RED 1
#define BLACK 0

#define DEFAULT_TAG 0

extern void *mallocN (int n);

extern void freeN (void *p, int n);

unsigned int Optt (unsigned int t1, unsigned int t2) {
    return t1 + t2;
}

unsigned int Opvt (unsigned int v, unsigned int t) {
    return v + t;
}

struct tree {
    int color;
    int key;
    unsigned int value;
    unsigned int tag;
    struct tree *left, *right, *par;
};

typedef struct tree ** treebox;

treebox treebox_new () {
    treebox p = (treebox) mallocN (sizeof (*p));
    *p = NULL;
    return p;
}

void tree_free (struct tree *p) {
    struct tree *pa, *pb;
    if (p != NULL) {
        pa = p->left;
        pb = p->right;
        freeN(p, sizeof (*p));
        tree_free(pa);
        tree_free(pb);
    }
}

void treebox_free (treebox b) {
    struct tree *t = *b;
    tree_free(t);
    freeN(b, sizeof (*b));
}

struct tree * left_rotate (struct tree * l) {
    struct tree * r = l->right;
    struct tree * mid = r->left;
    l->right = mid;
    r->left = l;
    r->par = l->par;
    l->par = r;
    if (mid != NULL) {
        mid->par = l;
    }
    return r;
}

void left_rotate_wrap (struct tree * l, treebox root) {
    if (l->par == NULL) {
        *root = left_rotate(l);
    } else {
        struct tree * l_par = l->par;
        if (l_par->left == l) {
            l_par->left = left_rotate(l);
        } else {
            l_par->right = left_rotate(l);
        }
    }
}

struct tree * right_rotate (struct tree * r) {
    struct tree * l = r->left;
    struct tree * mid = l->right;
    r->left = mid;
    l->right = r;
    l->par = r->par;
    r->par = l;
    if (mid != NULL) {
        mid->par = r;
    }
    return l;
}

void right_rotate_wrap (struct tree * r, treebox root) {
    if (r->par == NULL) {
        *root = right_rotate(r);
    } else {
        struct tree * r_par = r->par;
        if (r_par->left == r) {
            r_par->left = right_rotate(r);
        } else {
            r_par->right = right_rotate(r);
        }
    }
}

void tag_tree_t (struct tree * x, unsigned int tag) {
    if (x != NULL) {
        x->tag = Optt(x->tag, tag); 
    }
}

void pushdown (struct tree * p) {
    p->value = Opvt(p->value, p->tag);
    tag_tree_t(p->left, p->tag);
    tag_tree_t(p->right, p->tag);
    p->tag = DEFAULT_TAG;   
}

void make_black (treebox root) {
    if (root == NULL) {
        return ;
    } else {
        struct tree * p = *root;
        if (p == NULL) {
            return;
        } else {
            p->color = BLACK;
        }
    }
}

int get_color (struct tree *p) {
    if (p == NULL) {
        return -1;
    } else {
        return p->color;
    }
}

/* another implementation of insert_balance function */
void insert_balance_simplified (treebox t, treebox root) {
    struct tree * p = *t;
    struct tree * p_par, * p_gpar;
    for (; ; ) {
        p_par = p->par;
        if (get_color(p_par) != RED) {
            return ;
        } else {
            p_gpar = p_par->par;
            if (p_gpar == NULL) {
                return ;
            } else {
                if (p_par == p_gpar->left) {
                    if (get_color(p_gpar->right) == RED) {
                        p_par->color = BLACK;
                        p_gpar->right->color = BLACK;
                        p_gpar->color = RED;
                        p = p_gpar;
                    } else {
                        p_gpar->color = RED;
                        if (p == p_par->right) {
                            p->color = BLACK;
                            p_gpar->left = left_rotate(p_par);
                            right_rotate_wrap(p_gpar, root);
                        } else {
                            p_par->color = BLACK;
                            right_rotate_wrap(p_gpar, root);
                        }
                    }
                } else {
                    if (get_color(p_gpar->left) == RED) {
                        p_par->color = BLACK;
                        p_gpar->left->color = BLACK;
                        p_gpar->color = RED;
                        p = p_gpar;
                    } else {
                        p_gpar->color = RED;
                        if (p == p_par->left) {
                            p->color = BLACK;
                            p_gpar->right = right_rotate(p_par);
                            left_rotate_wrap(p_gpar, root);
                        } else {
                            p_par->color = BLACK;
                            left_rotate_wrap(p_gpar, root);
                        }
                    }
                }
            }
        }
    }
}

void insert_balance (treebox t, treebox root) {
    struct tree * p = *t;
    struct tree * p_par, * p_gpar;
    for (; ; ) {
        p_par = p->par;
        if (p_par == NULL) {
            return ;
        } else {
            p_gpar = p_par->par;
            if (p_gpar == NULL) {
                return ;
            } else {
                if (p_par->color == BLACK) {
                    return ;
                } else if (p == p_par->left) {
                    if (p_par == p_gpar->left) {
                        if (get_color(p_gpar->right) != RED) {
                            p_gpar->color = RED;
                            p_par->color = BLACK;
                            right_rotate_wrap(p_gpar, root);
                            return ;
                        } else {
                            p_par->color = BLACK;
                            p_gpar->right->color = BLACK;
                            p_gpar->color = RED;
                            p = p_gpar;
                        }
                    } else {
                        if (get_color(p_gpar->left) != RED) {
                            p_gpar->color = RED;
                            p->color = BLACK;
                            p_gpar->right = right_rotate(p_par);
                            left_rotate_wrap(p_gpar, root);
                            return ;
                        } else {
                            p_par->color = BLACK;
                            p_gpar->left->color = BLACK;
                            p_gpar->color = RED;
                            p = p_gpar;
                        }
                    }
                } else {
                    if (p_par == p_gpar->left) {
                        if (get_color(p_gpar->right) != RED) {
                            p_gpar->color = RED;
                            p->color = BLACK;
                            p_gpar->left = left_rotate(p_par);
                            right_rotate_wrap(p_gpar, root);
                            return ;
                        } else {
                            p_par->color = BLACK;
                            p_gpar->right->color = BLACK;
                            p_gpar->color = RED;
                            p = p_gpar;
                        }
                    } else {
                        if (get_color(p_gpar->left) != RED) {
                            p_gpar->color = RED;
                            p_par->color = BLACK;
                            left_rotate_wrap(p_gpar, root);
                            return ;
                        } else {
                            p_par->color = BLACK;
                            p_gpar->left->color = BLACK;
                            p_gpar->color = RED;
                            p = p_gpar;
                        }
                    }
                }
            }
        }
    }
}

void insert (treebox t, int x, unsigned int value) {
    treebox root = t;
    struct tree * p;
    struct tree * last_node = NULL;
    for (; ; ) {
        p = *t;
        if (p == NULL) {
            p = (struct tree *) mallocN (sizeof *p);
            p->color = RED;
            p->key = x;                 
            p->value = value; 
            p->tag = DEFAULT_TAG;
            p->left = NULL; 
            p->right = NULL;
            p->par = last_node;
            *t = p;
            break;
        } else {
            int y = p->key;
            pushdown(p);
            if (x == y) {
                p->value = value;
                break;
            } else {
                last_node = p;
                if (x < y) {
                    t = &(p->left); 
                } else {
                    t = &(p->right);
                }
            }
        }
    }
    if (p->color == RED) {
        insert_balance(t, root);
    }
    make_black(root);
}

void update_aux (struct tree * t, unsigned int tg, int l, int r, int targ_l, int targ_r) {
    if (t == NULL) {
        return ;
    }
    if (l > targ_r) {
        return ;
    }
    if (r < targ_l) {
        return ;
    }
    if (l >= targ_l && r <= targ_r) {
        t->tag = Optt(t->tag, tg);
        return ;
    } else {
        if (targ_l <= t->key && t->key <= targ_r) {
            t->value = Opvt(t->value, tg);
        }
        update_aux(t->left, tg, l, t->key, targ_l, targ_r);
        update_aux(t->right, tg, t->key, r, targ_l, targ_r);
    }
}

void update (treebox root, unsigned int tg, int targ_l, int targ_r) {
    if (targ_r < targ_l){
        return ;
    }
    update_aux(*root, tg, -2147483647 - 1, 2147483647, targ_l, targ_r);
}

void delete_balance (struct tree * p, struct tree * p_par, treebox root) {
    struct tree * p_sib;
    for (; ; ) {
        if (p_par == NULL) {
            *root = p;
            return ;
        }
        if (get_color(p) == RED) {
            p->color = BLACK;
            return ;
        }
        if (p == p_par->left) {
            p_sib = p_par->right;
            if (p_sib->color == RED) {
                /* Case 1 */
                pushdown(p_sib);
                p_sib->tag = p_par->tag;
                p_par->tag = DEFAULT_TAG;
                p_sib->color = BLACK;
                p_par->color = RED;
                left_rotate_wrap(p_par, root);
                p_sib = p_par->right;
            }
            if (get_color(p_sib->left) != RED && get_color(p_sib->right) != RED) {
                /* Case 2 */
                p_sib->color = RED;
                p = p_par;
                p_par = p->par;
            } else {
                if (get_color(p_sib->right) != RED) {
                    /* Case 3 */
                    pushdown(p_sib->left);
                    p_sib->left->tag = p_sib->tag;
                    p_sib->tag = DEFAULT_TAG;
                    p_sib->left->color = BLACK;
                    p_sib->color = RED;
                    right_rotate_wrap(p_sib, root);
                    p_sib = p_par->right;
                }
                /* Case 4 */
                pushdown(p_sib);
                p_sib->tag = p_par->tag;
                p_par->tag = DEFAULT_TAG;
                p_sib->color = p_par->color;
                p_par->color = BLACK;
                p_sib->right->color = BLACK;
                left_rotate_wrap(p_par, root);
                return ;
            }
        } else {
            p_sib = p_par->left;
            if (p_sib->color == RED) {
                pushdown(p_sib);
                p_sib->tag = p_par->tag;
                p_par->tag = DEFAULT_TAG;
                p_sib->color = BLACK;
                p_par->color = RED;
                right_rotate_wrap(p_par, root);
                p_sib = p_par->left;
            }
            if (get_color(p_sib->left) != RED && get_color(p_sib->right) != RED) {
                p_sib->color = RED;
                p = p_par;
                p_par = p_par->par;
            } else {
                if (get_color(p_sib->left) != RED) {
                    pushdown(p_sib->right);
                    p_sib->right->tag = p_sib->tag;
                    p_sib->tag = DEFAULT_TAG;
                    p_sib->right->color = BLACK;
                    p_sib->color = RED;
                    left_rotate_wrap(p_sib, root);
                    p_sib = p_par->left;
                }
                pushdown(p_sib);
                p_sib->tag = p_par->tag;
                p_par->tag = DEFAULT_TAG;
                p_sib->color = p_par->color;
                p_par->color = BLACK;
                p_sib->left->color = BLACK;
                right_rotate_wrap(p_par, root);
                return ;
            }
        }
    }
}

treebox tree_minimum (treebox t) {
    struct tree * tmp;
    for (; ; ) {
        tmp = *t;
        pushdown(tmp);
        if (tmp->left == NULL) {
            return t;
        } else {
            t = &(tmp->left);
        }
    }
}

void delete (treebox t, int x) {
    treebox root = t;
    struct tree * final_p;
    struct tree * final_p_par;
    int original_color;
    for (; ; ) {
        struct tree * p = *t;
        if (p == NULL) {
            make_black(root);       /* a dummy change */
            return ;
        } else {
            int y = p->key;
            pushdown(p);
            if (x < y) {
                t = &(p->left);
            } else if (x > y) {
                t = &(p->right);
            } else {
                original_color = p->color;
                if (p->left != NULL){
                    if (p->right != NULL){
                        treebox tmp = tree_minimum(&(p->right));
                        struct tree * targ = *tmp;
                        original_color = targ->color;
                        // move targ itself, instead of copying 
                        // all fields of targ to p
                        targ->left = p->left;
                        p->left->par = targ;
                        targ->color = p->color;
                        if (targ->par == p) {
                            final_p = targ->right;
                            final_p_par = targ;
                        } else {
                            if (targ->right != NULL) {
                                targ->right->par = targ->par;
                            }
                            *tmp = targ->right;
                            targ->right = p->right;
                            p->right->par = targ;
                            final_p = *tmp;
                            final_p_par = targ->par;
                        }
                        targ->par = p->par;
                        *t = targ;
                        freeN(p, sizeof *p);
                        break;
                    }
                }
                if (p->left != NULL) {
                    *t = p->left;
                    p->left->par = p->par;
                } else if (p->right != NULL) {
                    *t = p->right;
                    p->right->par = p->par;
                } else {
                    *t = NULL;
                }
                final_p = *t;
                final_p_par = p->par;
                freeN(p, sizeof *p);
                break;
            }
        }
    }
    if (original_color == BLACK) {
        delete_balance(final_p, final_p_par, root);
    }
    make_black(root);
}

unsigned int lookup (struct tree * p, int x) {
    unsigned int res = 0;
    for (; ; ) {
        if (p == NULL){
            return 0;
        }
        res = Optt(res, p->tag);
        if (p->key < x) {
            p = p->right;
        } else if (p->key > x) {
            p = p->left;
        } else {
            return Opvt(p->value, res);
        }
    }
}