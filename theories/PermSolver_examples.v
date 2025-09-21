(*****************************************)
(*                                       *)
(* Copyright (c) 2025 Nadeem Abdul Hamid *)
(* Distributed under terms of the        *)
(* MIT License. (See LICENSE file)       *)
(*                                       *)
(*****************************************)

(*
To compile:

coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
*)

From Coq Require Import Lists.List.
From Coq Require Import Permutation.
Import ListNotations.

From PS Require Import PermSolver.


Check (refl_equal : depths [0; 0; 1; 1; 2; 2; 3; 3] = [2; 4; 6; 8]).

(* this example shows why you can't necessarily remove_common before trying all the subst's *)
Check (refl_equal : check_unify [([1; 0], [3; 2]); ([0], [4; 2])]
                  [1; 4; 2] 
                  [3; 2] = true).

Compute
(check_unify_depth 3
                  [([1; 0], [3; 2]); ([0], [4; 2])]
                  [1; 4; 2] 
                  [3; 2]
                  false).

Check (refl_equal : check_unify_fd 4 [([1; 0], [3; 2]); ([0], [4; 2])]
[1; 4; 2; 1; 4; 2] 
[3; 2; 3; 2] = true).



(* multiple substitutions necessary? *)
Check (refl_equal : check_unify_fd 10 [([1; 0], [3; 2]); ([0], [4; 2])]
                  [1; 4; 2; 1; 4; 2] 
                  [3; 2; 3; 2] = true).


(* these examples check sensitivity to the order of the env pairs *)
Check (refl_equal : check_unify [
                    ([23],     [21]) ;
                    ([18;16],  [21]) ;
                    ([30; 28], [16]) ;
                    ([34; 32], [28])
                  ]
                    [34;32;30;18] [23] = true).

                  (* reversed version of the next *)
Check (refl_equal : check_unify [
                    ([34; 32], [28]) ;
                    ([30; 28], [16]) ;
                    ([23],     [21]) ;
                    ([18;16],  [21]) 
                  ]
                    [34;32;30;18] [23] = true).

Check (refl_equal : check_unify ([
                    ([18;16],  [21]) ;
                    ([23],     [21]) ;  (* swapped *)
                    ([30; 28], [16]) ;
                    ([34; 32], [28])
                  ])
                    [34;32;30;18] [23] = true).

Check (refl_equal : check_unify ([
                    ([18;16],  [21]) ;
                    ([23],     [21]) ;  (* swapped *)
                    ([34; 32], [28]) ;
                    ([30; 28], [16])
                  ])
                    [34;32;30;18] [23] = true).



Check (refl_equal : (check_unify 
        [ ([1; 2], [3; 4]) ; ([6], [5]) ; ([26], [1]) ]
        [2; 6; 26]   [4; 3; 5]) = true).
Check refl_equal : (check_unify   
        [ ([6], [5]) ; ([26], [1]); ([1; 2], [3; 4]) ]
        [2; 6; 26]   [4; 3; 5]) = true.
Check refl_equal : (check_unify
        [ ([7], [3; 4]) ; ([10; 9], [2]) ; ([1], [3; 10]) ; ([4; 9], [11]) ]
        [11; 1]   [7; 2]) = true. 
Check refl_equal : (check_unify
        [ ([7], [3; 4]) ; ([10; 9], [2]) ; ([1], [3; 10]) ; ([4; 9], [11]) ]
        [7; 3]   [12; 5]) = false.
Check refl_equal : (check_unify
        [ ([7], [3; 4]) ; ([10; 9], [2]) ; ([1], [3; 10]) ; ([4; 9], [11]) ]
        [7; 10]   [1]) = false.
Check refl_equal : (check_unify
        [ ([7], [3; 4]) ; ([10; 9], [2]) ; ([1], [3; 10]) ; ([4; 9], [11]) ; 
          ([7; 2; 4], [8; 10]) ; ([3; 6; 7], [1; 9; 2]) ; ([4; 2], [11; 3; 7; 10; 1])]
        [7; 10]   [1]) = false.
Check refl_equal : (check_unify
        [ ([7], [3; 4]) ; ([10; 9], [2]) ; ([1], [3; 10]) ; ([4; 9], [11]) ; 
          ([7; 2; 4], [8; 10]) ; ([3; 6; 7], [1; 9; 2]) ; ([4; 2], [11; 3; 7; 10; 1])]
        [7; 10; 2; 9; 11; 3; 4; 10; 8]   [7; 10; 3; 10; 10; 9; 11; 3; 10; 8; 11; 3; 7]) = true. 
Check refl_equal : (check_unify
        [ ([7], [3; 4]) ; ([10; 9], [2]) ; ([1], [3; 10]) ; ([4; 9], [11]) ; 
          ([7; 2; 4], [8; 10]) ; ([3; 6; 7], [1; 9; 2]) ; ([4; 2], [11; 3; 7; 10; 1])]
        [7; 10; 2; 9; 11; 3; 4; 10; 8]   [7; 3; 10; 10; 9; 11; 3; 10; 8; 11; 3; 7]) = false.


        
Goal 
    forall A (a b c d e f g h : list A),
    Permutation (a ++ b) c ->
    Permutation d c ->
    Permutation (e ++ f) h ->
    Permutation (g ++ h) b ->
    Permutation (e ++ f ++ g ++ a) d.
intros; perm_solver.
Qed.

Lemma s1 :
    forall (a b c d e f g h : list nat),
    Permutation (a ++ b) c ->
    Permutation d c ->
    Permutation (e ++ f) h ->
    Permutation (g ++ h) b ->
    Permutation (e ++ f ++ g ++ a) d.
intros; perm_solver.
Qed.

Print s1.



Goal forall A (pq:list A) pqsm pqlg D Dsm Dlg R L x y,
    Permutation pq (x :: pqsm ++ rev pqlg) ->
    Permutation (rev pqlg) pqlg ->
    Permutation (Dsm ++ Dlg) D ->
    Permutation R (pqsm ++ y :: Dsm) ->
    Permutation L (Dlg ++ pqlg) ->
    Permutation (R ++ x :: L) (y :: D ++ pq).
(*
  (R ++ x :: L) (y :: D ++ pq)
  (pqsm ++ y :: Dsm ++ x :: Dlg ++ pqlg) (y :: Dsm ++ Dlg ++ x :: pqsm ++ rev pqlg)
  (pqsm ++ Dsm ++ Dlg ++ pqlg) (Dsm ++ Dlg ++ pqsm ++ pqlg)
*)

Proof.
  intros.
  perm_solver.
(*  perm_solver_fd 10.*)
Qed.



(* ====== FROM https://github.com/foreverbell/permutation-solver/blob/master/Examples.v ===== *)

Goal
  forall (a b c d e : list nat) (x y : nat),
    Permutation (a ++ e) (x :: c) ->
    Permutation b (y :: d) ->
    Permutation (a ++ b ++ e) (x :: y :: c ++ d).
Proof.
  intros; perm_solver.
Qed.

Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

Goal
  forall (a b : list nat) (x y : nat),
    Permutation a b ->
    Permutation [x] [y] ->
    Permutation (a ++ [x]) (y :: b).
Proof.
  intros; perm_solver.
Qed.

Goal
  forall (b u t e r f l y : nat) (xs ys : list nat),
    Permutation xs ys ->
    Permutation ([b;u;t;t;e;r]++[f;l;y]++xs) ([f;l;u;t;t;e;r]++ys++[b;y]).
Proof.
  intros; perm_solver.
Qed.

(** Proving preorder, inorder and postorder of a BST are permutation of each
  other. *)
  Inductive tree : Set :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.
  
  Fixpoint inorder (t : tree) : list nat :=
  match t with
  | Leaf => nil
  | Node l v r => inorder l ++ v :: inorder r
  end.
  
  Fixpoint preorder (t : tree) : list nat :=
  match t with
  | Leaf => nil
  | Node l v r => v :: preorder l ++ preorder r
  end.
  
  Fixpoint postorder (t : tree) : list nat :=
  match t with
  | Leaf => nil
  | Node l v r => postorder l ++ postorder r ++ [v]
  end.
  
  Theorem tree_orders :
  forall (t : tree),
    Permutation (inorder t) (preorder t) /\
    Permutation (inorder t) (postorder t).
  Proof.
  intros t.
  induction t; simpl; intuition; perm_solver.
Qed.




(* -============================ stress testing ======================= *)


Check (refl_equal : true = check_unify
        [ 
          ([9], [6]) ; 
          ([9], [12]) ;
          ([24;22], [9]) ; 
          ([28;27], [9]) ;
          ([3; 30], [6]) ;
          ([15;14], [12]) ;
          ([25;24], [3]) ;
          ([34;33], [24]) ;
          ([23;22], [30]) ;
          ([32;31], [22]) ;
          ([30;28], [15]) ; 
          ([34;32], [28]) ;
          ([29;27], [14]) ;
          ([33;31], [27]) ;
          ([1; 30], [2]) ; 
          ([4; 3], [5]) ;
          ([4; 1], [7]) ;
          ([4; 1], [8]) ;
          ([16;14], [19]) ;
          ([17;16], [18]) ;
          ([17;15], [20]) ;
          ([21], [19]) ;
          ([25;23], [26]) ;
          ([30;29], [26]) ;
          ([29;33;31], [14]) ;  
          ([34;25;4;33], [5]) 
        ]
        
          [9] [15;14] ).


      
Check (refl_equal : true = check_unify
        [ ([1; 30], [2]) ; 
          ([4; 3], [5]) ;
          ([3; 30], [6]) ;
          ([4; 1], [7]) ;
          ([4; 1], [8]) ;
          ([9], [6]) ; 
          ([10], [11]) ;
          ([9], [12]) ;     (* THIS *)
          ([10], [13]) ;
          ([15;14], [12]) ;  (* THIS *)
          ([17;16], [18]) ;
         ([16;14], [19]) ;
          ([17;15], [20]) ;
          ([21], [19]) ;
         ([23;22], [30]) ;
          ([25;24], [3]) ;
          ([24;22], [9]) ; 
          ([25;23], [26]) ;
          ([28;27], [9]) ;
          ([30;29], [26]) ;
          ([29;27], [14]) ;
          ([30;28], [15]) ; 
          ([24;22], [9]) ;
          ([28;27], [9]) ; 
          ([32;31], [22]) ;
          ([34;33], [24]) ;
          ([33;31], [27]) ;
          ([34;32], [28]) ;
          ([29;33;31], [14]) ;  
          ([34;25;4;33], [5]) ]
        
          [9] [15;14] ).



Goal
forall A (eSm eLg lstSm lstLg resi resiSm lftConts leftoveri lst
        pqlstLft loLft lresSm lresLg rgtConts rgttreeSm rgttreeLg
        pqlstRgt loRgt result eSmSm eSmLg lstSmSm  lstSmLg
        resiSmSm resiSmLg lfttreeSmSm lfttreeSmLg eSmSmSm eSmSmLg
        lstSmSmSm lstSmSmLg 
            lfttreeLg:list A) 
      pt e',
    Permutation (eSm ++ eLg) [pt] ->
    Permutation (lstSm ++ lstLg) lst ->
    Permutation (eSm ++ lstSm) resi ->
    Permutation (eLg ++ lstLg) leftoveri ->
    Permutation (eLg ++ lstLg) [e'] ->
    Permutation resiSm resi ->
    Permutation lfttreeLg lftConts ->
    Permutation resiSm pqlstLft ->
    Permutation lfttreeLg loLft ->
    Permutation (lresSm ++ lresLg) pqlstLft ->
    Permutation (rgttreeSm ++ rgttreeLg) rgtConts ->
    Permutation (lresSm ++ rgttreeSm) pqlstRgt ->
    Permutation (lresLg ++ rgttreeLg) loRgt ->
    Permutation result pqlstRgt ->
    Permutation (eSmSm ++ eSmLg) eSm  ->
    Permutation (lstSmSm ++ lstSmLg) lstSm ->
    Permutation (eSmSm ++ lstSmSm) resiSm  ->
    Permutation (eSmLg ++ lstSmLg) []  ->
    Permutation (resiSmSm ++ resiSmLg) resiSm ->
    Permutation (lfttreeSmSm ++ lfttreeSmLg) []  ->
    Permutation (resiSmSm ++ lfttreeSmSm) lresSm  ->
    Permutation (resiSmLg ++ lfttreeSmLg) lresLg ->
    Permutation (eSmSm ++ lstSmSm) resiSm ->
    Permutation (resiSmSm ++ resiSmLg) resiSm ->
    Permutation (eSmSmSm ++ eSmSmLg) eSmSm ->
    Permutation (lstSmSmSm ++ lstSmSmLg) lstSmSm ->
    Permutation (eSmSmSm ++ lstSmSmSm) resiSmSm  ->
    Permutation (eSmSmLg ++ lstSmSmLg) resiSmLg ->
    Permutation (eSmSmSm ++ lstSmSmSm ++ lfttreeSmSm) lresSm ->
    Permutation (lstSmSmSm ++ lstLg ++ lstSmLg ++ lstSmSmLg) lst ->
Permutation resiSm (lresSm ++ lresLg).
Proof.
intros.
perm_solver.
Qed.


Goal
forall A (resiSm lresSm lresLg pqlstLft:list A),
    Permutation resiSm pqlstLft ->
    Permutation (lresSm ++ lresLg) pqlstLft ->
Permutation resiSm (lresSm ++ lresLg).
Proof.
intros.
perm_solver.
Qed.


(*
Examples for paper
*)


Goal
  forall A (h:A) (a b a' t a1 a2:list A)
  (H1 : Permutation (a ++ b) (h :: t))
  (H2 : Permutation a (h :: a'))
  (H3 : Permutation (a' ++ b) t)
  (H4 : Permutation (a1 ++ a2) a'),
  Permutation ((a1 ++ b) ++ h :: a2) (a ++ b).
intros. perm_solver. Qed.

Goal
  forall A (p1 p2 p3 p4 p5 p6 p7 p8 p9:list A)
  (H1 : Permutation (p5 ++ p7) p6)
  (H2 : Permutation (p2 ++ p8) p9)
  (H3 : Permutation (p2 ++ p3) p5)
  (H4 : Permutation (p5 ++ p4) p1),
  Permutation (p2 ++ p3 ++ p4) p1.
intros.
perm_solver.
Qed.

(* contrived - multiple replace *)

Goal forall A (p0 p1 p2 p3 p4:list A),
  Permutation (p1 ++ p0) (p3 ++ p2) ->
  Permutation p0 (p4 ++ p2) ->
  Permutation (p1 ++ p4 ++ (p2 ++ p1) ++ p4 ++ p2)
              (p3 ++ (p2 ++ p3) ++ p2).
intros.
perm_solver_fd 10.
Qed.

Check (refl_equal : check_unify_depth 5 [([1; 0], [3; 2]); ([0], [4; 2])]
                    [1; 4; 2; 1; 4; 2]   (* lft *)
                    [3; 2; 3; 2]         (* rgt *)
                    true = true).

Compute
let env := [([1; 0], [3; 2]); ([0], [4; 2]); ([1; 2], [3; 3])]
 in check_unify_depth 5 env [1; 4; 2; 1; 4; 2] [3; 2; 3; 2] true.


