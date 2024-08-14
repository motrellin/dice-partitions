From Equations Require Import Equations.
From Coq Require Import List Lia.

Equations partitions (w s : nat) : list (list nat) by wf w :=
partitions 0 0 := nil :: nil;
partitions 0 (S s) := nil;
partitions 1 0 := nil;
partitions 1 1 := (1 :: nil) :: nil;
partitions 1 2 := (2 :: nil) :: nil;
partitions 1 3 := (3 :: nil) :: nil;
partitions 1 4 := (4 :: nil) :: nil;
partitions 1 5 := (5 :: nil) :: nil;
partitions 1 6 := (6 :: nil) :: nil;
partitions 1 _ := nil;
partitions (S (S w'')) s :=
  let r := fun k => map (fun ln => k :: ln) (partitions (S w'') (s - k)) in
  let ks := 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: nil in
  list_rec
  _
  nil
  (fun ns1 t ns2 => ns1 ++ ns2)
  (map r ks).

Compute (partitions 0 0).
Compute (partitions 1 0).
Compute (partitions 1 1).
Compute (partitions 2 7).

Theorem partitions_correct_length :
  forall w s ns,
    In ns (partitions w s) ->
    length ns = w.
Proof.
  intros w s.
  funelim (partitions w s).
  all: intros ns H1.
  all: try (destruct H1 as [H1|H1]; [subst ns; reflexivity | contradiction]).
  all: try contradiction.

  (* TODO This has to be prettier! *)
  simpl in *.
  rewrite <- Heqcall in H1.
  clear Heqcall.
  repeat apply in_app_or in H1 as [H1|H1].
  all: try apply in_map_iff in H1 as [ns' [H1 H2]].
  all: try subst ns.
  all: simpl; f_equal.
  all: try (eapply H).
  all: try reflexivity.
  all: try exact H2.
  all: try contradiction.
  Unshelve.
  exact 0.
  exact 0.
Qed.

Lemma partitions_0_r :
  forall w'',
    partitions (S w'') 0 = nil.
Proof.
  intros w.
  induction w as [|w' IH].
  -
    rewrite partitions_equation_3.
    reflexivity.
  -
    rewrite partitions_equation_11.
    simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem partitions_correct_sum :
  forall w s ns,
    In ns (partitions w s) ->
    list_sum ns = s.
Proof.
  intros w s.
  funelim (partitions w s).
  all: intros ns H1.
  all: try (destruct H1 as [H1|H1]; [subst ns; reflexivity | contradiction]).
  all: try contradiction.

  (* TODO This has to be prettier! *)
  rewrite <- Heqcall in H1.
  simpl in *.
  clear Heqcall.
  repeat apply in_app_or in H1 as [H1|H1].
  all: try contradiction.
  all: apply in_map_iff in H1 as [ns' [H1 H2]].
  all: subst ns.
  -
    destruct s as [|s'].
    all: simpl in H2.
    all: try rewrite partitions_0_r in H2.
    all: try contradiction.

    rewrite PeanoNat.Nat.sub_0_r in H2.
    simpl.
    do 1 f_equal.
    apply H with (k := 1) (w := S w'').
    f_equal. lia. f_equal. lia.
    exact H2.
  -
    destruct s as [|[|s']].
    all: simpl in H2.
    all: try rewrite partitions_0_r in H2.
    all: try contradiction.

    rewrite PeanoNat.Nat.sub_0_r in H2.
    simpl.
    do 2 f_equal.
    apply H with (k := 2) (w := S w'').
    f_equal. lia. f_equal. lia.
    exact H2.
  -
    destruct s as [|[|[|s']]].
    all: simpl in H2.
    all: try rewrite partitions_0_r in H2.
    all: try contradiction.

    rewrite PeanoNat.Nat.sub_0_r in H2.
    simpl.
    do 3 f_equal.
    apply H with (k := 3) (w := S w'').
    f_equal. lia. f_equal. lia.
    exact H2.
  -
    destruct s as [|[|[|[|s']]]].
    all: simpl in H2.
    all: try rewrite partitions_0_r in H2.
    all: try contradiction.

    rewrite PeanoNat.Nat.sub_0_r in H2.
    simpl.
    do 4 f_equal.
    apply H with (k := 4) (w := S w'').
    f_equal. lia. f_equal. lia.
    exact H2.
  -
    destruct s as [|[|[|[|[|s']]]]].
    all: simpl in H2.
    all: try rewrite partitions_0_r in H2.
    all: try contradiction.

    rewrite PeanoNat.Nat.sub_0_r in H2.
    simpl.
    do 5 f_equal.
    apply H with (k := 5) (w := S w'').
    f_equal. lia. f_equal. lia.
    exact H2.
  -
    destruct s as [|[|[|[|[|[|s']]]]]].
    all: simpl in H2.
    all: try rewrite partitions_0_r in H2.
    all: try contradiction.

    rewrite PeanoNat.Nat.sub_0_r in H2.
    simpl.
    do 6 f_equal.
    apply H with (k := 6) (w := S w'').
    f_equal. lia. f_equal. lia.
    exact H2.
Qed.

Theorem partitions_correct_elements :
  forall w s ns,
    In ns (partitions w s) ->
    forall n,
      In n ns ->
      1 <= n <= 6.
Proof.
  intros w s ns H1 n1 H2.
  funelim (partitions w s).
  -
    rewrite partitions_equation_1 in H1.
    destruct H1 as [H1|H1]; [subst ns; contradiction | contradiction].
  -
    rewrite partitions_equation_2 in H1.
    contradiction.
  -
    rewrite partitions_equation_3 in H1.
    contradiction.
  -
    rewrite partitions_equation_4 in H1.
    destruct H1 as [H1|H1]; [subst ns | contradiction].
    destruct H2 as [H2|H2]; [subst n1; lia | contradiction].
  -
    rewrite partitions_equation_5 in H1.
    destruct H1 as [H1|H1]; [subst ns | contradiction].
    destruct H2 as [H2|H2]; [subst n1; lia | contradiction].
  -
    rewrite partitions_equation_6 in H1.
    destruct H1 as [H1|H1]; [subst ns | contradiction].
    destruct H2 as [H2|H2]; [subst n1; lia | contradiction].
  -
    rewrite partitions_equation_7 in H1.
    destruct H1 as [H1|H1]; [subst ns | contradiction].
    destruct H2 as [H2|H2]; [subst n1; lia | contradiction].
  -
    rewrite partitions_equation_8 in H1.
    destruct H1 as [H1|H1]; [subst ns | contradiction].
    destruct H2 as [H2|H2]; [subst n1; lia | contradiction].
  -
    rewrite partitions_equation_9 in H1.
    destruct H1 as [H1|H1]; [subst ns | contradiction].
    destruct H2 as [H2|H2]; [subst n1; lia | contradiction].
  -
    rewrite partitions_equation_10 in H1.
    contradiction.
  -
    simpl in *.
    rewrite <- Heqcall in H1.
    clear Heqcall.
    repeat apply in_app_or in H1 as [H1|H1].
    all: try contradiction.
    all: apply in_map_iff in H1 as [ns' [H1 H3]].
    all: subst ns.
    all: simpl in *.
    all: destruct H2 as [H2|H2].
    all: try lia.
    all: eauto.
Qed.

Theorem correct_partitions :
  forall ns,
    (forall n, In n ns -> 1 <= n /\ n <= 6) ->
    In ns (partitions (length ns) (list_sum ns)).
Proof.
  induction ns as [|n1 [|n2 ns'] IH].
  all: intros H1.
  -
    simpl.
    rewrite partitions_equation_1.
    left.
    reflexivity.
  -
    simpl in *.
    rewrite partitions_equation_1 in IH.
    rewrite PeanoNat.Nat.add_0_r.
    clear IH.
    destruct n1 as [|[|[|[|[|[|[|n1']]]]]]].
    +
      destruct (H1 0). left; reflexivity.
      lia.
    +
      rewrite partitions_equation_4.
      left; reflexivity.
    +
      rewrite partitions_equation_5.
      left; reflexivity.
    +
      rewrite partitions_equation_6.
      left; reflexivity.
    +
      rewrite partitions_equation_7.
      left; reflexivity.
    +
      rewrite partitions_equation_8.
      left; reflexivity.
    +
      rewrite partitions_equation_9.
      left; reflexivity.
    +
      edestruct H1. left; reflexivity.
      lia.
  -
    simpl in *.
    rewrite partitions_equation_11.
    simpl.
    apply in_or_app.
    destruct n1 as [|[|[|[|[|[|[|n1']]]]]]].
    all: simpl in *.
    +
      destruct (H1 0). left; reflexivity.
      lia.
    +
      left; apply in_map_iff.
      eexists.
      split.
      *
        reflexivity.
      *
        rewrite PeanoNat.Nat.sub_0_r.
        apply IH.
        intros n3 [H2|H2].
        --
           subst.
           apply H1; lia.
        --
           apply H1; right; right; exact H2.
    +
      do 1 (right; apply in_or_app).
      left; apply in_map_iff.
      eexists.
      split.
      *
        reflexivity.
      *
        rewrite PeanoNat.Nat.sub_0_r.
        apply IH.
        intros n3 [H2|H2].
        --
           subst.
           apply H1; lia.
        --
           apply H1; right; right; exact H2.
    +
      do 2 (right; apply in_or_app).
      left; apply in_map_iff.
      eexists.
      split.
      *
        reflexivity.
      *
        rewrite PeanoNat.Nat.sub_0_r.
        apply IH.
        intros n3 [H2|H2].
        --
           subst.
           apply H1; lia.
        --
           apply H1; right; right; exact H2.
    +
      do 3 (right; apply in_or_app).
      left; apply in_map_iff.
      eexists.
      split.
      *
        reflexivity.
      *
        rewrite PeanoNat.Nat.sub_0_r.
        apply IH.
        intros n3 [H2|H2].
        --
           subst.
           apply H1; lia.
        --
           apply H1; right; right; exact H2.
    +
      do 4 (right; apply in_or_app).
      left; apply in_map_iff.
      eexists.
      split.
      *
        reflexivity.
      *
        rewrite PeanoNat.Nat.sub_0_r.
        apply IH.
        intros n3 [H2|H2].
        --
           subst.
           apply H1; lia.
        --
           apply H1; right; right; exact H2.
    +
      do 5 (right; apply in_or_app).
      left; apply in_map_iff.
      eexists.
      split.
      *
        reflexivity.
      *
        rewrite PeanoNat.Nat.sub_0_r.
        apply IH.
        intros n3 [H2|H2].
        --
           subst.
           apply H1; lia.
        --
           apply H1; right; right; exact H2.
    +
      do 5 (right; apply in_or_app); right.
      edestruct H1. left; reflexivity.
      lia.
Qed.
