# 几种红黑树的实现

下面列出各类书或库提供的红黑树的实现，并作一定的比较。

## 《Verified Functional Algorithms》

[相关链接](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)

来自《Software Foundations》第三卷的实现。该版本基于论文《Red-Black Trees in a Functional Setting》，只实现了插入操作。

插入对于红黑性质的修正方式是：先向下递归寻找插入位置，插入完成后再上推修正。

相关核心代码：
```coq
Definition balance rb t1 k vk t2 :=
 match rb with Red => T Red t1 k vk t2
 | _ =>
 match t1 with
 | T Red (T Red a x vx b) y vy c =>
      T Red (T Black a x vx b) y vy (T Black c k vk t2)
 | T Red a x vx (T Red b y vy c) =>
      T Red (T Black a x vx b) y vy (T Black c k vk t2)
 | a => match t2 with
            | T Red (T Red b y vy c) z vz d =>
                T Red (T Black t1 k vk b) y vy (T Black c z vz d)
            | T Red b y vy (T Red c z vz d) =>
                T Red (T Black t1 k vk b) y vy (T Black c z vz d)
            | _ => T Black t1 k vk t2
            end
  end
 end.
Definition makeBlack t :=
  match t with
  | E => E
  | T _ a x vx b => T Black a x vx b
  end.
Fixpoint ins x vx s :=
 match s with
 | E => T Red E x vx E
 | T c a y vy b => if ltb x y then balance c (ins x vx a) y vy b
                        else if ltb y x then balance c a y vy (ins x vx b)
                        else T c a x vx b
 end.
Definition insert x vx s := makeBlack (ins x vx s).
```

## Coq Standard Library

[相关链接](https://coq.inria.fr/stdlib/Coq.MSets.MSetRBT.html)

该版本基于论文《Efficient Verified Red-Black Trees》，包含插入和删除的实现。

插入的实现与本文上一版本相同。删除操作通过对删除点的左右子树用某种方式合并，再向上旋转平衡的方式实现。

原始论文中还给出了用于证明删除操作正确性的不变量。

删除操作代码：
```coq
Definition lbal l k r :=
 match l with
 | Rd (Rd a x b) y c => Rd (Bk a x b) y (Bk c k r)
 | Rd a x (Rd b y c) => Rd (Bk a x b) y (Bk c k r)
 | _ => Bk l k r
 end.

Definition rbal' l k r :=
 match r with
 | Rd b y (Rd c z d) => Rd (Bk l k b) y (Bk c z d)
 | Rd (Rd b y c) z d => Rd (Bk l k b) y (Bk c z d)
 | _ => Bk l k r
 end.

Definition lbalS l k r :=
 match l with
 | Rd a x b => Rd (Bk a x b) k r
 | _ =>
   match r with
   | Bk a y b => rbal' l k (Rd a y b)
   | Rd (Bk a y b) z c => Rd (Bk l k a) y (rbal' b z (makeRed c))
   | _ => Rd l k r
   end
 end.

Definition rbalS l k r :=
 match r with
 | Rd b y c => Rd l k (Bk b y c)
 | _ =>
   match l with
   | Bk a x b => lbal (Rd a x b) k r
   | Rd a x (Bk b y c) => Rd (lbal (makeRed a) x b) y (Bk c k r)
   | _ => Rd l k r
   end
 end.

Fixpoint append (l:tree) : tree -> tree :=
 match l with
 | Leaf => fun r => r
 | Node lc ll lx lr =>
   fix append_l (r:tree) : tree :=
   match r with
   | Leaf => l
   | Node rc rl rx rr =>
     match lc, rc with
     | Red, Red =>
       let lrl := append lr rl in
       match lrl with
       | Rd lr' x rl' => Rd (Rd ll lx lr') x (Rd rl' rx rr)
       | _ => Rd ll lx (Rd lrl rx rr)
       end
     | Black, Black =>
       let lrl := append lr rl in
       match lrl with
       | Rd lr' x rl' => Rd (Bk ll lx lr') x (Bk rl' rx rr)
       | _ => lbalS ll lx (Bk lrl rx rr)
       end
     | Black, Red => Rd (append_l rl) rx rr
     | Red, Black => Rd ll lx (append lr r)
     end
   end
 end.

Fixpoint del x t :=
 match t with
 | Leaf => Leaf
 | Node _ a y b =>
   match X.compare x y with
   | Eq => append a b
   | Lt =>
     match a with
     | Bk _ _ _ => lbalS (del x a) y b
     | _ => Rd (del x a) y b
     end
   | Gt =>
     match b with
     | Bk _ _ _ => rbalS a y (del x b)
     | _ => Rd a y (del x b)
     end
   end
 end.

Definition remove x t := makeBlack (del x t).
```

## Linux 内核

[相关链接](https://github.com/torvalds/linux/blob/master/lib/rbtree.c)

该版本实现了插入和删除操作，同时具有一定的可扩展性（见[此处](https://github.com/torvalds/linux/blob/cbafe18c71028d5e0ee1626b4776fea5d5824a78/tools/include/linux/rbtree_augmented.h)）。插入和删除基本上是按照《算法导论》实现的。

## Microsoft's C++ Standard Library

[相关链接](https://github.com/microsoft/STL/blob/e4bc00e70cbb539f90b803a64a31f0259e21f28e/stl/inc/xtree)

该 STL 中的 map 和 set 底层实现均为 xtree，即红黑树。

该版本实现了插入（见 _Insert_node 方法）和删除（见 _Extract 方法）操作。插入与删除方式与《算法导论》中基本相同。

## MinGW G++ STL

该版本实现了插入和删除。对该版本的描述如下：

```cpp
  // Red-black tree class, designed for use in implementing STL
  // associative containers (set, multiset, map, and multimap). The
  // insertion and deletion algorithms are based on those in Cormen,
  // Leiserson, and Rivest, Introduction to Algorithms (MIT Press,
  // 1990), except that
  //
  // (1) the header cell is maintained with links not only to the root
  // but also to the leftmost node of the tree, to enable constant
  // time begin(), and to the rightmost node of the tree, to enable
  // linear time performance when used with the generic set algorithms
  // (set_union, etc.)
  // 
  // (2) when a node being deleted has two children its successor node
  // is relinked into its place, rather than copied, so that the only
  // iterators invalidated are those referring to the deleted node.
```

## 《数据结构：算法与实现（第 2 版）》

（相关链接等待补充）

该版本实现了插入和删除操作。删除的实现较为特别，采用的是自顶向下的删除，核心思想在于：从根向下遍历时，试图将到待删除的节点的路径上的每个点都涂成红色，最后被删除节点为红色即可直接删除。

相关核心代码：等待补充。

## 小结

对以上实现做比对如下。

| 来源名称                               | 实现语言          | 插入实现方式 | 删除实现方式 | 备注 |
| -------------------------------------- | ----------------- | ------------ | ------------ | -------------------- |
| 《Verified Functional Algorithms》     | Gallina / Haskell |  自插入点向上平衡，讨论高度对称 | 未实现       | 提供了和一般二叉搜索树在性能上的对比 |
| Coq Standard Library                   | Gallina           |  同上   | 合并删除点子树，向上旋转平衡  |     论文中证明了正确性  |
| Linux  内核            |     C          |     见《算法导论》 |  见《算法导论》    |    可扩展     |
| Microsoft's C++ Standard Library    |   C++     |    见《算法导论》   |  见《算法导论》  |    高度封装    |
| MinGW G++ STL                         |   C++        |    见《算法导论》   |  见《算法导论》      |    高度封装     |
| 《数据结构：算法与实现（第 2 版）》    | C++               |   见《算法导论》   | 自根向下修改，直接删除             |                      |

可以看出，大部分 C/C++ 的实现都采用了《算法导论》中的方式。