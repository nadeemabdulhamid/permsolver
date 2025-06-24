(*****************************************)
(*                                       *)
(* Copyright (c) 2025 Nadeem Abdul Hamid *)
(* Distributed under terms of the        *)
(* MIT License. (See LICENSE file)       *)
(*                                       *)
(*****************************************)

Require Import Nat.
Require Import PeanoNat.
From Coq Require Import Lists.List.
From Coq Require Import Permutation.
Import ListNotations.

From Coq Require Import Bool.Bool.

Require Import FMaps FMapFacts.
Module Import NatMap := FMapList.Make(Nat_as_OT).
Module Import NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.
Import NatMapFacts.


(* Remove the first occurrence of `x` from `l`. *)
Fixpoint remove_first (x : nat) (l : list nat) {struct l} : list nat :=
    match l with
      | nil => nil
      | y::tl => if (x =? y) then tl else y::(remove_first x tl)
    end.


(* Reduces both `cs` and `ds` to a pair of lists where any common
   elements in both have been deleted. *)    
Fixpoint remove_common (cs ds: list nat) : (list nat * list nat) :=
  match (cs, ds) with 
  | (nil, _) => (cs, ds)
  | (_, nil) => (cs, ds)
  | (c::cs, ds) => 
    if List.find (Nat.eqb c) ds 
    then remove_common cs (remove_first c ds)
    else match (remove_common cs ds) with 
         | (cs', ds') => (c::cs', ds')
         end
  end.

Goal (remove_common [1; 4; 7; 2; 3; 4; 8]  [6; 3; 1; 8; 2]) = ([4; 7; 4], [6]).
reflexivity. Qed.


(* Is everything in `bs` in `cs`? *)
Fixpoint is_sublist (bs cs:list nat) : bool :=
    match bs with
    | [] => true
    | b :: bs => if List.find (Nat.eqb b) cs   (* in_dec Nat.eq_dec b cs*)
                 then is_sublist bs (remove_first b cs)
                 else false
    end.

Goal (is_sublist [2; 7; 3] [8; 3; 9; 4; 7; 1; 2; 8]) = true. reflexivity. Qed.
Goal (is_sublist [2; 7; 7; 3] [8; 3; 9; 4; 7; 1; 2; 8]) = false. reflexivity. Qed. 
Goal (is_sublist [2; 7; 7; 3] [7; 8; 3; 9; 4; 7; 1; 2; 8]) = true. reflexivity. Qed.
Goal (is_sublist [] [2; 7; 4]) = true. reflexivity. Qed.


(* Substitutes `bs` with `cs` in `ds`; meaning it removes all the `bs` elements 
   from `ds` and appends `cs` to the result *)
Definition subst (bs cs ds : list nat) :=
    if (is_sublist bs ds) 
    then cs ++ snd (remove_common bs ds)
    else ds.

Goal (subst [4; 2; 1] [7; 9] [8; 2; 3; 1; 5; 4; 4; 7]) = 
      [7; 9; 8; 3; 5; 4; 7]. reflexivity. Qed. 
Goal (subst [] [7; 9] [8; 2; 3; 1; 5; 4; 4; 7]) = 
      [7; 9; 8; 2; 3; 1; 5; 4; 4; 7]. reflexivity. Qed. 


(* Produces indexes of all substitution pairs from `env` that could apply to `target`.
   Since `env` is deconstructed in the recursion, `cur` keeps track of what the index 
   of the current head of `env` is, with respect to the initial call.
   
   Defining the helper fixpoint as a standalone, in order to be able to 
   reason independently about it later. 
*)
Fixpoint applicable_subs_help (env: list (list nat * list nat)) (target: list nat) (cur : nat) : list nat :=
  match env with 
  | nil => nil
  | ((e1, e2) :: tail) =>
    let subs_tail := applicable_subs_help tail target (S cur) in
    if is_sublist e1 target || is_sublist e2 target then
    cur :: subs_tail else
    subs_tail
  end.

Definition applicable_subs (env: list (list nat * list nat)) (target: list nat)  : list nat :=
  applicable_subs_help env target 0.

(* Removes the `n`th pair from the `env`. *)
Fixpoint drop_nth (n : nat)  (env: list (list nat * list nat))  : list (list nat * list nat) :=
  match env with
  | nil => nil
  | (hd :: tail) =>
    match n with 
    | 0 => tail
    | S n' => hd :: (drop_nth n' tail)
    end
  end.


(* Recursively attempt to apply substitutions from `env` to `cs` until either 
  `cs` and `ds` contain the same elements (return `true`) or `depth` is reached (return `false`).  
  If `allow_repeat_subs`, then substitution pairs in `env` are retained as they are applied, so
  they may be applied multiple times; otherwise, once a substitution pair is attempted, it is
  removed from `env`, so only a maximum depth of |env| could even be reached. (In that case,
  if the `env` becomes empty before the `depth` is reached, the fold would end the process with
  the `false` result.)
*)
Fixpoint check_unify_depth (depth:nat)
                           (env: list (list nat * list nat))
                           (lft rgt: list nat)
                           (rpt : bool) : bool :=
  match depth with 
  | 0 => false 
  | S d' =>
    match (remove_common lft rgt) with
    | (nil, nil) => true
    | _ => fold_left 
            (fun result i => 
              result || 
              let env' := if rpt then env else (drop_nth i env) in
              let (e1, e2) := nth i env (nil, nil) in
                   (is_sublist e1 lft && check_unify_depth d' env' (subst e1 e2 lft) rgt rpt)
                || (is_sublist e2 lft && check_unify_depth d' env' (subst e2 e1 lft) rgt rpt))
            (applicable_subs env lft)
            false
    end
  end.


(* Produce quartiles of the length of the given list. That is, produce a
   4-tuple with numbers that are |env|/4, |env|/2, 3|env|/4, and |env|.

  depths []     = (0, 0, 0, 0)
  depths [a]    = (0, 0, 0, 1)
  depths [a, b] = (0, 1, 1, 2)
  depths [a, b, c]    = (0, 1, 2, 3)
  depths [a, b, c, d] = (1, 2, 3, 4)
  depths [a, a, b, b, c, c, d, d] = (2, 4, 6, 8)
*)
Fixpoint depths {A} (env: list A) : (list nat) :=  (* produces 1/4, 1/2, 3/4, 1.0 *)
  match env with 
  | nil => [0; 0; 0; 0]
  | _::nil => [0; 0; 0; 1]
  | _::_::nil => [0; 1; 1; 2]
  | _::_::_::nil => [0; 1; 2; 3]
  | _::_::_::_::nil => [1; 2; 3; 4]
  | _::_::_::_::env' => match depths env' with
                        [q; h; t; f] => [1+q; 2+h; 3+t; 4+f]
                        | _ => [0; 0; 0; 0]
                        end
  end.


(* Perform iterative deepening search with check_unify_depth based on the `depths` given.
*)
Fixpoint check_unify_ids (depths: list nat) env cs ds allow_repeat_subs : bool :=
  match depths with
  | nil => false
  | dp::dps => check_unify_depth (S dp) env cs ds allow_repeat_subs || check_unify_ids dps env cs ds allow_repeat_subs
  end.


(* This variant generates a list of iteratively deepening depths up to the length of the
   environment as the limiting depths for the search. 
   For this variant, `allow_repeat_subs` is set to `false`, so each pair in the `env` is
   only substituted at most once.
*)
Definition check_unify (env: list (list nat * list nat))
                     (cs ds: list nat) : bool :=
  check_unify_ids (depths env) env cs ds false.


(* Fixed-depth variant: this one takes the search depth limit explicitly as a parameter.
   For this variant, `allow_repeat_subs` is set to `true`, so the same substitution 
   might be applied multiple times (i.e. maybe even in reverse). *)
Definition check_unify_fd (maxd:nat)
                      (env: list (list nat * list nat))
                      (cs ds: list nat) : bool :=
  check_unify_ids [maxd] env cs ds true.



(* ========================================= *)


Inductive nattree :=
    | leaf : nat -> nattree
    | branch : nattree -> nattree -> nattree.

Fixpoint flatten (nt : nattree) : list nat := 
    match nt with
    | leaf n => (n :: nil)
    | branch nt1 nt2 => flatten nt1 ++ flatten nt2
    end.
    
Goal flatten (branch (branch (leaf 4) (leaf 5))
                         (branch (leaf 1) (leaf 2))) = 
             (4 :: 5 :: 1 :: 2 :: nil). reflexivity. Qed.


Fixpoint lift {A} (ms : list nat) (lenv : NatMap.t (list A)) : list A :=
    match ms with
    | nil => nil
(*    | x :: nil => 
    match (find x lenv) with
        | Some v => v
        | None => nil
        end *)
    | x :: xs =>
    match (find x lenv) with
        | Some v => lift xs lenv ++ v
        | None => lift xs lenv
        end
    end.

Definition nattree_to_list_flat {A} (nt : nattree) (lenv : NatMap.t (list A)) : list A :=
    lift (flatten nt) lenv.

(* here, problem is that flattening loses the original append parse tree structure, 
   so we need a nattree_to_list that maintains it
*)

Fixpoint nattree_to_list {A} (nt : nattree) (lenv : NatMap.t (list A)) : list A :=
    match nt with
    | leaf n => match (find n lenv) with Some v => v | None => nil end
    | branch nt1 nt2 => (nattree_to_list nt2 lenv) ++ (nattree_to_list nt1 lenv)
    end.


Fixpoint flatten_env (tenv: list (nattree * nattree)) : list (list nat * list nat) :=
  match tenv with
  | nil => nil
  | (t1, t2) :: tenv' => (flatten t1, flatten t2) :: flatten_env tenv'
  end.


(* ========================================= *)




Lemma lift_some_assoc : 
  forall A tl h (lst:list A) env, 
  find h env = Some lst ->
  lift (h :: tl) env = lift tl env ++ lst.
Proof.
  induction tl as [ | t tl]; intros h lst env Hfind;
  simpl; rewrite Hfind; auto.
Qed.


Lemma lift_distr :
    forall A l1 l2 env, 
    @lift A (l1 ++ l2) env
        = lift (l2) env ++ lift (l1) env.
Proof.
    induction l1 as [ | h t IH ]; auto; intros l2 env; simpl.
    - rewrite app_nil_r; auto.
    - 
    destruct (find h env) eqn:Hfind; auto.
    rewrite IH.
    rewrite <- app_assoc.
    rewrite app_inv_head_iff; auto.
Qed.


Lemma lift_permutation : forall A lst1 lst2 env, 
    Permutation lst1 lst2 ->
    Permutation ((lift lst1 env) : list A) (lift lst2 env).
Proof.
    induction lst1 as [ | h t IH ]; intros lst2 env Hp.
    - apply Permutation_nil in Hp; rewrite Hp; auto.
    - simpl.
    apply Permutation_in with (x := h) in Hp as Hpi; try left; auto.
    apply in_split in Hpi. destruct Hpi as (l1, (l2, Hpi)).
    rewrite Hpi in *; clear lst2 Hpi.
    rewrite lift_distr.

    destruct (find h env) eqn:Hfind; auto.
        --
        rewrite lift_some_assoc with (lst:=l); auto.
        rewrite <- app_assoc.
        apply Permutation_trans with (l ++ lift l2 env ++ lift l1 env); auto using Permutation_app_swap_app.
        apply Permutation_trans with (l ++ lift t env); auto using Permutation_app_comm.
        apply Permutation_app_head.
        rewrite <- lift_distr.
        apply IH.
        apply Permutation_cons_app_inv with h; auto.
        -- (* find = None *)
        replace (lift (h :: l2) env) with (lift l2 env); [ | simpl; rewrite Hfind; auto].
        rewrite <- lift_distr; apply IH; auto.
        apply Permutation_cons_app_inv with h; auto.
Qed.


Lemma flatten_env_lift : 
  forall l1 l2 tenv,
  List.In (l1, l2) (flatten_env tenv) ->
  exists t1 t2, List.In (t1, t2) tenv /\ l1 = flatten t1 /\ l2 = flatten t2.
Proof.
  induction tenv as [ | (t1, t2) tenv' IHt]; simpl; try tauto.
  intros Hin.
  destruct Hin as [ Hlft | Hrgt ].
  injection Hlft; exists t1; exists t2; repeat split; auto.
  destruct (IHt Hrgt) as (t1', (t2', (H1, (H2, H3)))).
  exists t1'; exists t2'; repeat split; auto.
Qed.

Lemma nattree_to_list_nattree_to_list_flat :
    forall A nt env, 
    (@nattree_to_list A nt env) = (@nattree_to_list_flat A nt env).
Proof.
    induction nt.
    - unfold nattree_to_list_flat; simpl.
        intros.
        destruct (find (elt:=list A)); auto using app_nil_r.
    - unfold nattree_to_list_flat; simpl.
        intros. 
        rewrite lift_distr.
        rewrite IHnt1, IHnt2.
        auto.
Qed.


Lemma list_permutation_cons :
  forall (l1 l2 : list nat) (x : nat),
    Permutation l1 l2 ->
    Permutation (x :: l1) (x :: l2).
Proof.
  intros l1 l2 x H_perm.
  induction H_perm as [|y l1' l2' H_eq | y1 y2 l | ].
  - (* Base case: reflexivity *)
    apply Permutation_refl.
  - (* In the first step: Cons and Permutation_skip *)
    simpl. apply perm_skip. auto.
  - (* Transitivity: Permutation_swap *)
  apply perm_skip. apply perm_swap.
  - (* Transitivity: Permutation_trans *)
    apply perm_skip. apply Permutation_trans with (l := l) in H_perm2; auto.
Qed.  


Lemma find_remove_perm :
    forall c ds n,
        List.find (Nat.eqb c) ds = Some n ->
        Permutation ds (c :: remove_first c ds).
Proof.
    induction ds as [ | d ds IH ]; intros n Hf.
    inversion Hf.
    simpl in *.
    destruct (c =? d) eqn:Hcd.
    apply Nat.eqb_eq in Hcd; replace d with c in *; auto.
    apply perm_trans with (d :: c :: remove_first c ds); auto.
    apply perm_skip. apply IH with n; auto.
    apply perm_swap; auto.
Qed.


Lemma remove_common_perm_induce :
    forall cs ds cs' ds',
        remove_common cs ds = (cs', ds') ->
        exists cs'' ds'',  (* these are the common pieces *)
            Permutation cs'' ds'' /\
            Permutation cs (cs' ++ cs'') /\
            Permutation ds (ds' ++ ds'').
Proof.
    induction cs as [ | c cs IHcs ];
        intros ds cs' ds' Hr.
    - (* cs = [] *)
        inversion Hr.
        exists []; exists []; repeat split; try (rewrite app_nil_r); auto.
    -
        simpl in Hr. 
        destruct ds as [ | d ds ].
    -- (* ds = [] *)
        inversion Hr.   
        exists []; exists []; repeat split; try rewrite app_nil_r; auto.
    -- 
        destruct (List.find (Nat.eqb c) (d :: ds)) eqn:Hf.
        --- (* c in ds *)
        apply IHcs in Hr as IHHr.
        destruct IHHr as (cs2, (ds2, (Hp1, (Hp2, Hp3)))).
        exists (c :: cs2); exists (c :: ds2); repeat split; auto.
        apply Permutation_cons_app; auto.
        apply perm_trans with (c :: (remove_first c (d :: ds))); auto.
        apply find_remove_perm in Hf as Hfp; auto.
        apply Permutation_cons_app; auto.
        ---  (* c not in ds *)
        destruct (remove_common cs (d :: ds)) as (cs2,ds2) eqn:Hrc.
        inversion Hr. rewrite <- H0 in *; rewrite <- H1 in *; clear cs' ds' H0 H1.
        apply IHcs in Hrc as IHHrc.
        destruct IHHrc as (cs3, (ds3, (Hp1, (Hp2, Hp3)))).
        exists cs3; exists ds3; repeat split; auto.
        apply list_permutation_cons; auto.
Qed.


Lemma remove_common_nil_perm :
  forall l1 l2,
  remove_common l1 l2 = ([], []) ->
  Permutation l1 l2.
Proof.
  intros l1 l2 H.
  apply remove_common_perm_induce in H.
  destruct H as (cs, (ds, (H1, (H2, H3)))).
  simpl in *.
  apply perm_trans with cs; auto.
  apply perm_trans with ds; auto.
  symmetry; auto.
Qed.


Lemma sublist_remove_common_empty_fst :
  forall cs ds,
  is_sublist cs ds = true ->
  fst (remove_common cs ds) = nil.
Proof.
  induction cs as [ | c cs IHcs ]; simpl; auto.
  intros ds Hs.
  destruct ds as [ | d ds ]; try discriminate.
  destruct (List.find (Nat.eqb c) (d :: ds)) eqn:Hf; auto.
  discriminate.
Qed.  


Lemma lift_subst_perm :
  forall A (lenv : NatMap.t (list A)) l e1 e2,
  Permutation (lift e1 lenv) (lift e2 lenv) ->
  Permutation (lift l lenv) (lift (subst e1 e2 l) lenv).
Proof.
  intros A lenv l e1 e2 Hp.
  unfold subst.
  destruct (is_sublist e1 l) eqn:Hsub; auto.
  rewrite lift_distr.
  destruct (remove_common e1 l) as (cs, ds) eqn:Hrc; simpl.
  apply sublist_remove_common_empty_fst in Hsub as Hsub'.
  rewrite Hrc in Hsub'; simpl in Hsub'; rewrite Hsub' in Hrc.
  apply remove_common_perm_induce in Hrc.
  destruct Hrc as (cs', (ds', (Hp1, (Hp2, Hp3)))).
  simpl in Hp2.
  apply (lift_permutation A _ _ lenv) in Hp1, Hp2, Hp3.
  repeat rewrite lift_distr in *.
  apply perm_trans with (lift ds' lenv ++ lift ds lenv); auto.
  apply perm_trans with (lift ds lenv ++ lift ds' lenv); try apply Permutation_app_comm; auto.
  apply Permutation_app_head; auto.
  apply perm_trans with (lift cs' lenv); try symmetry; auto.
  apply perm_trans with (lift e1 lenv); try symmetry; auto.
  symmetry; auto.
Qed.


Lemma applicable_subs_in_env' : 
  forall env' env pref target cur s,
    env = rev pref ++ env' ->
    cur = length pref ->
    List.In s (applicable_subs_help env' target cur) -> 
    s < length env.
Proof.
  induction env' as [ | (e1, e2) env' ]; simpl; try intuition.
  destruct (is_sublist e1 target || is_sublist e2 target).
  {
    destruct H1 as [ Hlft | Hrgt ]; rewrite H.
    rewrite Hlft in *.
    rewrite length_app, length_rev, H0; simpl. auto with *.
    rewrite <- H.
    apply (IHenv' env ((e1,e2)::pref) target (S cur) s); auto.
    simpl.
    rewrite <- app_assoc; auto.
    simpl; auto with *.
  }

  apply (IHenv' env ((e1,e2)::pref) target (S cur) s); auto.
  simpl.
  rewrite <- app_assoc; auto.
  simpl; auto with *.
Qed.


Lemma applicable_subs_in_env : 
  forall env target s, List.In s (applicable_subs env target) -> s < length env.
Proof.
  intros.
  apply applicable_subs_in_env' with (pref := []) (env' := env) (target := target) (cur := 0); auto.
Qed.


Lemma drop_nth_In : 
  forall i env v, List.In v (drop_nth i env) -> List.In v env.
Proof.
  induction i as [ | i]; simpl; intros.
  destruct env; auto; right; auto.
  destruct env; auto.
  destruct H.
  left; auto.
  right; auto.
Qed.


Lemma check_unify_depth_perm :
  forall A dp (lenv : NatMap.t (list A)) env l1 l2 allow_repeat_subs,
  (forall l1' l2' : list nat, List.In (l1', l2') env -> 
            Permutation (lift l1' lenv) (lift l2' lenv)) ->
  check_unify_depth dp env l1 l2 allow_repeat_subs = true ->
  Permutation (lift l1 lenv) (lift l2 lenv).
Proof.
  induction dp as [ | dp ].
  simpl; discriminate.
  intros lenv env l1 l2 allow_repeat_subs Hlenv Hcud.
  simpl in Hcud.
  destruct (remove_common l1 l2) as (l1', l2') eqn:Hrc.
  assert ((l1' = nil /\ l2' = nil) \/ (l1' <> nil) \/ (l2' <> nil)).
  {
    destruct l1'; destruct l2'; auto; try discriminate; try auto.
    right; right; discriminate.
    right; left; discriminate.
    right; right; discriminate.
  }

  destruct H as [ (H1, H2) | H ].
  {
  rewrite H1, H2 in *.
  apply remove_common_nil_perm in Hrc.
  apply lift_permutation; auto.
  }

  assert (fold_left 
            (fun result d => 
              result || 
              let env' := if allow_repeat_subs then env else (drop_nth d env) in
              match (nth d env (nil, nil)) with (e1, e2) =>
                  (is_sublist e1 l1 && check_unify_depth dp env' (subst e1 e2 l1) l2 allow_repeat_subs)
                || (is_sublist e2 l1 && check_unify_depth dp env' (subst e2 e1 l1) l2 allow_repeat_subs)
              end)
            (applicable_subs env l1)
            false = true) as Hcudd.
  {
    destruct H as [ H | H ]; destruct l1'; destruct l2'; auto; try discriminate.
  }
  clear Hcud.

  apply remove_common_perm_induce in Hrc.
  destruct Hrc as (cs, (ds, (Hp1, (Hp2, Hp3)))).
  apply (lift_permutation A _ _ lenv) in Hp1, Hp2, Hp3.
  
  revert Hcudd; generalize (applicable_subs_in_env env l1); generalize (applicable_subs env l1).
  induction l as [ | sub subs ]; simpl; try discriminate.
  destruct (nth sub env ([], [])) as (e1, e2) eqn:Hnth; intros Hasin Hcud.
  assert (Permutation (lift e1 lenv) (lift e2 lenv)) as Hp4.
  { apply Hlenv. rewrite <- Hnth; apply nth_In; auto. }
  
  destruct allow_repeat_subs eqn:Hars.
  {
    destruct (is_sublist e1 l1 && check_unify_depth dp env (subst e1 e2 l1) l2 true) eqn:Hcu1; simpl in Hcud; [ clear Hcud | clear Hcu1 ].
    destruct (andb_prop _ _ Hcu1) as (_, Hcu).
    {
      apply IHdp with (lenv:=lenv) in Hcu; [ | intros; apply Hlenv; eauto using drop_nth_In ].
      apply perm_trans with (lift (subst e1 e2 l1) lenv); auto.
      apply lift_subst_perm; auto.
    }

    destruct (is_sublist e2 l1 && check_unify_depth dp env (subst e2 e1 l1) l2 true) eqn:Hcu1; simpl in Hcud; [ clear Hcud | clear Hcu1 ].
    destruct (andb_prop _ _ Hcu1) as (_, Hcu).
    {
      apply IHdp with (lenv:=lenv) in Hcu; [ | intros; apply Hlenv; eauto using drop_nth_In ].
      apply perm_trans with (lift (subst e2 e1 l1) lenv); auto.
      apply lift_subst_perm; symmetry; auto.
    }

    apply IHsubs; auto.
  }
  {
    destruct (is_sublist e1 l1 && check_unify_depth dp (drop_nth sub env) (subst e1 e2 l1) l2 false) eqn:Hcu1; simpl in Hcud; [ clear Hcud | clear Hcu1 ].
    destruct (andb_prop _ _ Hcu1) as (_, Hcu).
    {
      apply IHdp with (lenv:=lenv) in Hcu; [ | intros; apply Hlenv; eauto using drop_nth_In ].
      apply perm_trans with (lift (subst e1 e2 l1) lenv); auto.
      apply lift_subst_perm; auto.
    }

    destruct (is_sublist e2 l1 && check_unify_depth dp (drop_nth sub env) (subst e2 e1 l1) l2 false) eqn:Hcu1; simpl in Hcud; [ clear Hcud | clear Hcu1 ].
    destruct (andb_prop _ _ Hcu1) as (_, Hcu).
    {
      apply IHdp with (lenv:=lenv) in Hcu; [ | intros; apply Hlenv; eauto using drop_nth_In ].
      apply perm_trans with (lift (subst e2 e1 l1) lenv); auto.
      apply lift_subst_perm; symmetry; auto.
    }

    apply IHsubs; auto.
  }
Qed.


Lemma check_unify_perm :
  forall A (lenv : NatMap.t (list A)) env l1 l2,
  (forall l1' l2' : list nat, List.In (l1', l2') env -> 
            Permutation (lift l1' lenv) (lift l2' lenv)) ->
  check_unify env l1 l2 = true ->
  Permutation (lift l1 lenv) (lift l2 lenv).
Proof.
  intros.
  unfold check_unify in *.
  induction (depths env); simpl; try discriminate.
  unfold check_unify_ids in H0; fold check_unify_ids in H0.
  destruct (check_unify_depth (S a) env l1 l2) eqn:Hcud; auto.
  eapply check_unify_depth_perm in Hcud; eauto. 
Qed.


Theorem final : 
  forall A (tenv: list (nattree * nattree)) (nt1 nt2: nattree) (lenv : NatMap.t (list A)),
  (forall t1 t2, List.In (t1, t2) tenv 
              -> Permutation (nattree_to_list_flat t1 lenv) (nattree_to_list_flat t2 lenv)) -> 
  check_unify (flatten_env tenv) (flatten nt1) (flatten nt2) = true ->
  Permutation (nattree_to_list_flat nt1 lenv) (nattree_to_list_flat nt2 lenv).
Proof.
  unfold nattree_to_list_flat; intros.
  assert (forall l1 l2, List.In (l1, l2) (flatten_env tenv)
            -> Permutation (lift l1 lenv) (lift l2 lenv)).
  {
    intros.            
    destruct (flatten_env_lift _ _ _ H1) as (t1, (t2, (Ht1, (Ht2, Ht3)))).
    rewrite Ht2, Ht3; auto.
  }

  apply check_unify_perm with (flatten_env tenv); auto.
Qed.

Theorem check_unify_permutation :
  forall A (tenv: list (nattree * nattree)) (nt1 nt2: nattree) (lenv : NatMap.t (list A)),
  (forall t1 t2, List.In (t1, t2) tenv 
              -> Permutation (nattree_to_list t1 lenv) (nattree_to_list t2 lenv)) -> 
  check_unify (flatten_env tenv) (flatten nt1) (flatten nt2) = true ->
  Permutation (nattree_to_list nt1 lenv) (nattree_to_list nt2 lenv).
Proof.
  intros.
  repeat rewrite nattree_to_list_nattree_to_list_flat.
  apply final with tenv; auto.
  intros.
  repeat rewrite <- nattree_to_list_nattree_to_list_flat; auto.
Qed.



(* --- fixed depth versions --- *)

Lemma check_unify_perm_fd :
  forall A maxd (lenv : NatMap.t (list A)) env l1 l2,
  (forall l1' l2' : list nat, List.In (l1', l2') env -> 
            Permutation (lift l1' lenv) (lift l2' lenv)) ->
  check_unify_fd maxd env l1 l2 = true ->
  Permutation (lift l1 lenv) (lift l2 lenv).
Proof.
  intros.
  unfold check_unify_fd in *.
  apply check_unify_depth_perm with (S maxd) env true; auto.
  unfold check_unify_ids in H0; fold check_unify_ids in H0.
  destruct (check_unify_depth (S maxd) env l1 l2) eqn:Hcud; auto.
Qed.

Theorem final_fd : 
  forall A maxd (tenv: list (nattree * nattree)) (nt1 nt2: nattree) (lenv : NatMap.t (list A)),
  (forall t1 t2, List.In (t1, t2) tenv 
              -> Permutation (nattree_to_list_flat t1 lenv) (nattree_to_list_flat t2 lenv)) -> 
  check_unify_fd maxd (flatten_env tenv) (flatten nt1) (flatten nt2) = true ->
  Permutation (nattree_to_list_flat nt1 lenv) (nattree_to_list_flat nt2 lenv).
Proof.
  unfold nattree_to_list_flat; intros.
  assert (forall l1 l2, List.In (l1, l2) (flatten_env tenv)
            -> Permutation (lift l1 lenv) (lift l2 lenv)).
  {
    intros.            
    destruct (flatten_env_lift _ _ _ H1) as (t1, (t2, (Ht1, (Ht2, Ht3)))).
    rewrite Ht2, Ht3; auto.
  }

  apply check_unify_perm_fd with maxd (flatten_env tenv); auto.
Qed.

Theorem check_unify_permutation_fd :
  forall A maxd (tenv: list (nattree * nattree)) (nt1 nt2: nattree) (lenv : NatMap.t (list A)),
  (forall t1 t2, List.In (t1, t2) tenv 
              -> Permutation (nattree_to_list t1 lenv) (nattree_to_list t2 lenv)) -> 
  check_unify_fd maxd (flatten_env tenv) (flatten nt1) (flatten nt2) = true ->
  Permutation (nattree_to_list nt1 lenv) (nattree_to_list nt2 lenv).
Proof.
  intros.
  repeat rewrite nattree_to_list_nattree_to_list_flat.
  apply final_fd with maxd tenv; auto.
  intros.
  repeat rewrite <- nattree_to_list_nattree_to_list_flat; auto.
Qed.


(* --- end fixed depth versions --- *)




Inductive tenv_perm : forall A, list (nattree * nattree) ->  NatMap.t (list A) -> Prop :=
 | tp_nil : forall A lenv, tenv_perm A [] lenv
 | tp_cons : forall A lenv t1 t2 tenv,
            Permutation (nattree_to_list t1 lenv) (nattree_to_list t2 lenv) ->
            tenv_perm A tenv lenv ->
            tenv_perm A ((t1, t2) :: tenv) lenv.



Lemma tenv_perm_forall : 
  forall A tenv (lenv : NatMap.t (list A)),
  tenv_perm A tenv lenv ->
  (forall t1 t2, List.In (t1, t2) tenv 
              -> Permutation (nattree_to_list t1 lenv) (nattree_to_list t2 lenv)).
Proof.
  intros A tenv lenv Htp.
  induction Htp.
  simpl; tauto.

  simpl; intros t1' t2' Hin.
  destruct Hin as [ Hin | Hin ].
  injection Hin as Hin1 Hin2; rewrite <- Hin1; rewrite <- Hin2; auto.
  apply IHHtp; auto.
Qed.



(* -------------------------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------------------------- *)
(* ---------------- How it would get used   --------------------------------------------------- *)


(* ctr is a nat
   env is a M.t (list A)  (i.e. a NatMap to (list A) -- whatever type of lists we are working with)
                                               this is the *mapping environment* in the paper
   rmap is a Ltac kind of thingy  ( (<exp>, <nat>),  ... )   a reverse map of env basically 
   
   cont's are continuations that take the three things above
*)

(* checks rmap' (which is a tail portion of rmap, used to recurse through rmap)
   to see if exp is paired with a number already, if so, just continues; 
   otherwise it adds a new mapping to env and rmap for exp *)
Ltac add_if_new exp rmap' ctr env rmap cont :=
  lazymatch rmap' with 
  | ((exp, ?n), _) => cont ctr env rmap
  | ((_, _), ?tail) => add_if_new exp tail ctr env rmap cont 
  | tt => cont constr:(S ctr) constr:(add ctr exp env) ((exp,ctr), rmap)
  end.


(* adds mappings to the env for any un-mapped portions of the list_exp. The "reverse map" rmap
   is used by add_if_new to figure out a subexpression, X, is already mapped by a label in env *)
Ltac gen_map list_exp ctr env rmap cont :=
  (*idtac "gen_map" list_exp;*)
  lazymatch list_exp with
  | ?X ++ ?Y =>
      gen_map X ctr env rmap ltac:(fun ctr' env' rmap' => gen_map Y ctr' env' rmap'
                                       ltac:(fun ctr'' env'' rmap'' => cont ctr'' env'' rmap''))
  | ?X => add_if_new X rmap ctr env rmap cont 
  end.


(* apply gen_map to add pieces of the lists in the given expressions to the mapping environment *)
Ltac gen_map_all list_exps ctr env rmap cont :=
  lazymatch list_exps with
  | (?X, ?tail) =>
    gen_map X ctr env rmap ltac:(fun ctr' env' rmap' => gen_map_all tail ctr' env' rmap' cont)
  | tt => cont ctr env rmap
  end.


(* cont : tuples of list exps -> ... *)
(* Looks for all list expressions in all Permutation premises and collects them in a list
   that is passed to the `cont`inuation   *)
Ltac collect_hyps_perm_terms A acc cont :=
  lazymatch goal with
  | H : @Permutation A ?X ?Y |- _ =>
      (*idtac "collect" H;*)
      revert H;
      collect_hyps_perm_terms A (X, (Y, acc)) ltac:(fun acc' => intro H; cont acc')
  | _ => cont acc
  end.


(* find the number label associated with a term in the reverse map *)
Ltac find_num exp rmap :=
  lazymatch rmap with 
  | ((exp, ?n), _) => constr:(n)
  | ((_, _), ?tail) => find_num exp tail
  | tt => constr:(0)
  end.


(* reifies a list expression into nattrees; concatenations (++) create branches; atomic terms
   turn into leaf nodes with the associated label from the rmap *)
Ltac build_nattree list_exp rmap :=
  lazymatch list_exp with 
  | ?X ++ ?Y => 
      let xt := build_nattree X rmap in
      let yt := build_nattree Y rmap in
      constr:(branch yt xt)
  | ?X => let num := find_num list_exp rmap in
      constr:(leaf num)
  end.


(* rewrites the subterms of every Permutation term in the goal context with 
   convertible (nattree_to_list ...) expressions, using build_nattree above to 
   reify the original lists into nattrees.
*)
Ltac rewrite_hyp_perms A rmap envname := 
  lazymatch goal with 
  | |- @Permutation A ?X ?Y => 
      let xt := build_nattree X rmap in
      let yt := build_nattree Y rmap in
      (* idtac "X" X "xt" xt "Y" Y "yt" yt "rmap" rmap;  *)
      change (Permutation (nattree_to_list xt envname) (nattree_to_list yt envname)); auto;
      cut True; auto;
      rewrite_hyp_perms A rmap envname
  | H : @Permutation A ?X ?Y |- _ =>
        let xt := build_nattree X rmap in
        let yt := build_nattree Y rmap in
        cut (Permutation (nattree_to_list xt envname) (nattree_to_list yt envname)); [ | auto];
        clear H;
        rewrite_hyp_perms A rmap envname;
        intro H
  | _ => idtac
  end.


(* builds the *substitution environment* in the paper: for every Permutation premise, 
   introduces a pair of the corresponding nattrees into the environment list. The initial
   `tenv` should be an empty list of nattree pairs. *)
Ltac build_tenv tenv cont :=
  lazymatch goal with 
  | H : Permutation (nattree_to_list ?T1 _) (nattree_to_list ?T2 _) |- _ =>
        revert H;
        build_tenv constr:(cons (T1, T2) tenv) ltac:(fun tenv' => intro H; cont tenv')
  | _ => cont tenv 
  end.


(* transforms cons (::) operations into concatentation of singleton list,
   and removes concatenations to empty lists *)
Ltac normalize_append_term T :=
  match T with 
  | ?h :: nil => idtac
  | ?h :: ?tl => replace (h :: tl) with ([h] ++ tl); auto; normalize_append_term tl
  | ?X ++ [] => rewrite app_nil_r; normalize_append_term X
  | ?X ++ ?Y => normalize_append_term X; normalize_append_term Y
  | _ => idtac
  end.


(* normalizes list subterms in all hypotheses in the goal context *)  
Ltac normalize_append_hyps A :=
  lazymatch goal with
  | H : (@Permutation A ?X ?Y) |- _ =>
      revert H;
      normalize_append_term X; 
      normalize_append_term Y;
      normalize_append_hyps A;
      intro H
  | _ => idtac
  end.


(* normalizes list subterms in the goal term itself; and then normalizes 
   in all hypotheses (using normalize_append_hyps) *)
Ltac normalize_append A :=
  match goal with 
  |- (@Permutation A ?X ?Y) => simpl X; simpl Y;
    match goal with 
       |- (@Permutation A ?X' ?Y') =>normalize_append_term X'; normalize_append_term Y'
    end
  end;
  normalize_append_hyps A.


(*
     SUB-TACTIC                 |      PURPOSE
  ------------------------------|-------------------------------------------------------------------------------
  split_all_hyps                | split all conjuctions in assumptions (which may embed Permutation facts)   -- happens in perm_solver
  normalize_append              | normalizes all hypotheses
  collect_hyps_perm_terms       | collects a list of all atomic list terms seperated by concatenations (++) in the goal and hypotheses -- hyps_perm_terms
  gen_map_all                   | generates the mapping environment (env) and reverse map (rmap) from hyps_perm_terms 
      --- (add a local definition of env to the proof context) ---
  rewrite_hyp_perms             | rewrites the subterms of every Permutation term in the goal context with 
                                |    convertible (nattree_to_list ...) expressions, using the build_nattree tactic to 
                                |    reify the original lists into nattrees
  build_tenv                    | builds the *substitution environment* in the paper: for every Permutation premise,
                                |    introduces a pair of the corresponding nattrees into an environment list. The initial
                                |    `tenv` should be an empty list of nattree pairs  
       --- (add a local definition of the tenv to the proof context) ---
  apply check_unify_permutation | the reflection theorem
  apply tenv_perm_forall        | clear the obligations relating the substitution environment to Permutation assumptions
*)  
Ltac build_env_and_go A :=
  (* idtac "A is" A; *)
  normalize_append A;
  match goal with
  |- (@Permutation A ?X ?Y) => 
     collect_hyps_perm_terms A constr:((X, (Y, tt)))
        ltac:(fun hyps_perm_terms => gen_map_all hyps_perm_terms constr:(0) constr:(empty (list A)) tt
                ltac:(fun ctr env rmap =>
                              let name := (fresh "env") in set (name := env);
                              rewrite_hyp_perms A rmap name;
                              let ign := (fresh "useless") in intro ign; clear ign; (* there's an extra True -> ... in the goal*)
                              build_tenv constr:((@nil (nattree * nattree)))
                                ltac:(fun tenv => let tname := (fresh "tenv") in set (tname := tenv);
                                      apply check_unify_permutation with tname; 
                                      [ apply tenv_perm_forall; repeat (apply tp_cons; auto); apply tp_nil | reflexivity ]
                )))
  end.


Ltac split_all_hyps :=
    repeat match goal with
    | H : _ /\ _ |- _ => let s1 := (fresh "spl") in let s2 := (fresh "spl") in destruct H as (s1, s2)
    end.
  

Ltac perm_solver :=
  (*idtac ""; idtac "perm_solver";*)
  match goal with
  |- (@Permutation ?A _ _) => split_all_hyps; build_env_and_go A
  end.



(* fixed-depth search versions *)

Ltac build_env_and_go_fd A maxd :=
  (* idtac "A is" A; *)
  normalize_append A;
  match goal with
  |- (@Permutation A ?X ?Y) => 
     collect_hyps_perm_terms A constr:((X, (Y, tt)))
        ltac:(fun hyps_perm_terms => gen_map_all hyps_perm_terms constr:(0) constr:(empty (list A)) tt
                ltac:(fun ctr env rmap =>
                              let name := (fresh "env") in set (name := env);
                              rewrite_hyp_perms A rmap name;
                              let ign := (fresh "useless") in intro ign; clear ign;
                              build_tenv constr:((@nil (nattree * nattree)))
                                ltac:(fun tenv => let tname := (fresh "tenv") in set (tname := tenv);
                                      apply check_unify_permutation_fd with maxd tname;
                                      [ apply tenv_perm_forall;  repeat (apply tp_cons; auto); apply tp_nil | reflexivity ])))
  end.

Ltac perm_solver_fd maxd :=
  (*idtac ""; idtac "perm_solver";*)
  match goal with
  |- (@Permutation ?A _ _) => split_all_hyps; build_env_and_go_fd A maxd
  end.
