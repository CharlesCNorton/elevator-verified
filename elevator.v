(******************************************************************************)
(*                                                                            *)
(*          Elevator Fire Service / Recall: Safety Invariants                 *)
(*                                                                            *)
(*   A comprehensive formalization of ASME A17.1 elevator fire service.       *)
(*   Models Phase I recall and Phase II fire service with multi-car support.  *)
(*                                                                            *)
(*   Proves:                                                                  *)
(*   - Doors stay closed while moving.                                        *)
(*   - Hall calls are ignored outside Normal mode.                            *)
(*   - Fire Service enables only on pressurized floors for designated car.    *)
(*   - Safety invariant preserved over any command sequence.                  *)
(*                                                                            *)
(*   Elisha Otis (1854) — "All safe, gentlemen, all safe."                    *)
(*                                                                            *)
(*   Author: Charles C. Norton                                                *)
(*   Date: December 2025                                                      *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import Lia Bool List.
Import ListNotations.

Set Implicit Arguments.

Module ElevatorFire.

  (** Modes: normal operation, Phase I recall, Phase II fire service. *)
  Inductive Mode := Normal | FireRecall | FireService.

  (** Door state. *)
  Inductive Door := Open | Closed.

  (** Car state: includes motion flag, target floor, and Phase II key status. *)
  Record Car := {
    car_id : nat;         (* Unique car identifier *)
    mode : Mode;
    door : Door;
    moving : bool;
    floor : nat;
    target : option nat;
    phaseII : bool;       (* Phase II key turned on inside the car *)
    door_hold : bool;     (* Phase II door open button being held *)
    recall_floor : nat;   (* Primary designated recall floor *)
    alt_recall_floor : nat; (* Alternate recall floor if primary has smoke *)
    recall_deadline : nat;  (* Ticks remaining before recall timeout alarm *)
    alarm : bool            (* Timeout alarm active *)
  }.

  (** Commands that may be issued. *)
  Inductive Cmd :=
  | HallCall (f:nat)
  | CarCall (f:nat)
  | Recall
  | FireServiceEnable
  | EnablePhaseII
  | DisablePhaseII
  | StartMove (f:nat)
  | Arrive
  | OpenDoor
  | CloseDoor
  | HoldDoorOpen      (* Phase II: hold door open button *)
  | ReleaseDoorOpen   (* Phase II: release door open button *)
  | Tick.             (* Time tick for watchdog timer *)

  (** External fact: shaft pressurization status by floor. *)
  Parameter pressurized : nat -> bool.

  (** External fact: smoke detector status by floor. *)
  Parameter smoke_detected : nat -> bool.

  (** Default recall deadline in ticks. *)
  Parameter default_recall_deadline : nat.

  (** The car designated for fire service operation. Only this car can enter FireService mode. *)
  Parameter designated_fire_car : nat.

  (** Safety: moving implies doors closed; fire modes impose stricter conditions.
      In FireService, doors may be open only when door_hold is active (constant pressure). *)
  Definition safe (c:Car) : Prop :=
    (moving c = true -> door c = Closed) /\
    match mode c with
    | Normal => True
    | FireRecall => door c = Closed
    | FireService =>
        pressurized (floor c) = true /\
        (door c = Open -> door_hold c = true)
    end.

  (** Helper to start motion toward a floor. *)
  Definition start_move (c:Car) (f:nat) : Car :=
    {| car_id := car_id c;
       mode := mode c;
       door := Closed;
       moving := true;
       floor := floor c;
       target := Some f;
       phaseII := phaseII c;
       door_hold := false;
       recall_floor := recall_floor c;
       alt_recall_floor := alt_recall_floor c;
       recall_deadline := recall_deadline c;
       alarm := alarm c |}.

  (** Helper to finish motion if a target exists.
      If the target floor is not pressurized, emergency stop at current floor. *)
  Definition arrive (c:Car) : Car :=
    match target c with
    | None => c
    | Some f =>
        if pressurized f
        then {| car_id := car_id c;
                mode := mode c;
                door := Closed;
                moving := false;
                floor := f;
                target := None;
                phaseII := phaseII c;
                door_hold := false;
                recall_floor := recall_floor c;
                alt_recall_floor := alt_recall_floor c;
                recall_deadline := recall_deadline c;
                alarm := alarm c |}
        else {| car_id := car_id c;
                mode := mode c;
                door := Closed;
                moving := false;
                floor := floor c;
                target := None;
                phaseII := phaseII c;
                door_hold := false;
                recall_floor := recall_floor c;
                alt_recall_floor := alt_recall_floor c;
                recall_deadline := recall_deadline c;
                alarm := alarm c |}
    end.

  (** Helper to set door without changing other fields. *)
  Definition set_door (d:Door) (c:Car) : Car :=
    {| car_id := car_id c;
       mode := mode c;
       door := d;
       moving := moving c;
       floor := floor c;
       target := target c;
       phaseII := phaseII c;
       door_hold := if match d with Closed => true | Open => false end
                    then false else door_hold c;
       recall_floor := recall_floor c;
       alt_recall_floor := alt_recall_floor c;
       recall_deadline := recall_deadline c;
       alarm := alarm c |}.

  (** Helper to set door hold state. *)
  Definition set_door_hold (hold:bool) (c:Car) : Car :=
    {| car_id := car_id c;
       mode := mode c;
       door := if hold then Open else Closed;
       moving := moving c;
       floor := floor c;
       target := target c;
       phaseII := phaseII c;
       door_hold := hold;
       recall_floor := recall_floor c;
       alt_recall_floor := alt_recall_floor c;
       recall_deadline := recall_deadline c;
       alarm := alarm c |}.

  (** Compute effective recall floor considering smoke detection. *)
  Definition effective_recall_floor (c:Car) : nat :=
    if smoke_detected (recall_floor c)
    then alt_recall_floor c
    else recall_floor c.

  (** Apply a command with conservative, safety-first semantics. *)
  Definition apply (c:Car) (cmd:Cmd) : Car :=
    match cmd with
    | Recall =>
        let eff_rf := effective_recall_floor c in
        if Nat.eqb (floor c) eff_rf
        then {| car_id := car_id c;
                mode := FireRecall;
                door := Closed;
                moving := false;
                floor := eff_rf;
                target := None;
                phaseII := false;
                door_hold := false;
                recall_floor := recall_floor c;
                alt_recall_floor := alt_recall_floor c;
                recall_deadline := 0;
                alarm := false |}
        else {| car_id := car_id c;
                mode := FireRecall;
                door := Closed;
                moving := true;
                floor := floor c;
                target := Some eff_rf;
                phaseII := false;
                door_hold := false;
                recall_floor := recall_floor c;
                alt_recall_floor := alt_recall_floor c;
                recall_deadline := default_recall_deadline;
                alarm := false |}
    | FireServiceEnable =>
        if andb (Nat.eqb (car_id c) designated_fire_car) (pressurized (floor c))
        then {| car_id := car_id c;
                mode := FireService;
                door := Closed;
                moving := false;
                floor := floor c;
                target := None;
                phaseII := false;
                door_hold := false;
                recall_floor := recall_floor c;
                alt_recall_floor := alt_recall_floor c;
                recall_deadline := 0;
                alarm := alarm c |}
        else c
    | EnablePhaseII =>
        match mode c with
        | FireService => {| car_id := car_id c;
                            mode := FireService; door := door c; moving := moving c;
                            floor := floor c; target := target c; phaseII := true;
                            door_hold := door_hold c; recall_floor := recall_floor c;
                            alt_recall_floor := alt_recall_floor c;
                            recall_deadline := recall_deadline c; alarm := alarm c |}
        | _ => c
        end
    | DisablePhaseII =>
        match mode c with
        | FireService => {| car_id := car_id c;
                            mode := FireService; door := Closed; moving := moving c;
                            floor := floor c; target := target c; phaseII := false;
                            door_hold := false; recall_floor := recall_floor c;
                            alt_recall_floor := alt_recall_floor c;
                            recall_deadline := recall_deadline c; alarm := alarm c |}
        | _ => c
        end
    | HallCall f =>
        match mode c with
        | Normal =>
            if moving c then c else start_move c f
        | _ => c
        end
    | CarCall f =>
        match mode c with
        | Normal =>
            if moving c then c else start_move c f
        | FireService =>
            if phaseII c then if moving c then c else start_move c f else c
        | FireRecall => c
        end
    | StartMove f =>
        if moving c then c else start_move c f
    | Arrive =>
        if moving c then arrive c else c
    | OpenDoor =>
        if moving c then c else
          match mode c with
          | Normal => set_door Open c
          | FireService => c
          | FireRecall => c
          end
    | CloseDoor =>
        set_door Closed c
    | HoldDoorOpen =>
        if moving c then c else
          match mode c with
          | FireService =>
              if phaseII c then set_door_hold true c else c
          | _ => c
          end
    | ReleaseDoorOpen =>
        match mode c with
        | FireService => set_door_hold false c
        | _ => c
        end
    | Tick =>
        match mode c with
        | FireRecall =>
            if moving c then
              match recall_deadline c with
              | 0 => {| car_id := car_id c;
                        mode := mode c; door := door c; moving := moving c;
                        floor := floor c; target := target c; phaseII := phaseII c;
                        door_hold := door_hold c; recall_floor := recall_floor c;
                        alt_recall_floor := alt_recall_floor c;
                        recall_deadline := 0; alarm := true |}
              | S n => {| car_id := car_id c;
                          mode := mode c; door := door c; moving := moving c;
                          floor := floor c; target := target c; phaseII := phaseII c;
                          door_hold := door_hold c; recall_floor := recall_floor c;
                          alt_recall_floor := alt_recall_floor c;
                          recall_deadline := n; alarm := alarm c |}
              end
            else c
        | _ => c
        end
    end.

  (** Basic properties of helpers. *)
  Lemma start_move_safe : forall c f,
    safe c -> safe (start_move c f).
  Proof.
    intros c f [Hmv Hmode]. split; simpl.
    - intros _. reflexivity.
    - destruct (mode c); simpl in *; auto.
      destruct Hmode as [Hprs Hdh]. split.
      + exact Hprs.
      + intros Habs. discriminate Habs.
  Qed.

  Lemma arrive_safe : forall c, safe c -> safe (arrive c).
  Proof.
    intros c [Hmv Hmode]. unfold arrive.
    destruct (target c) as [f|] eqn:Ht; simpl.
    - destruct (pressurized f) eqn:Hp; simpl.
      + split; [intros _; reflexivity|].
        destruct (mode c); simpl in *.
        * trivial.
        * reflexivity.
        * split; [exact Hp|intros Habs; discriminate Habs].
      + split; [intros _; reflexivity|].
        destruct (mode c); simpl in *.
        * trivial.
        * reflexivity.
        * destruct Hmode as [Hprs _]. split; [exact Hprs|intros Habs; discriminate Habs].
    - exact (conj Hmv Hmode).
  Qed.

  (** Run a list of commands. *)
  Fixpoint run_cmds (cmds:list Cmd) (c:Car) {struct cmds} : Car :=
    match cmds with
    | nil => c
    | cons cmd0 rest => run_cmds rest (apply c cmd0)
    end.

  (** Safety preservation across one command. *)
  Lemma apply_preserves_safe : forall c cmd, safe c -> safe (apply c cmd).
  Proof.
    intros [cid m d mv fl tg ph dh rf arf rdl alm] cmd [Hmv Hmode]; simpl in *.
    split.
    - intro Hmoving.
      destruct cmd; simpl in *.
      + destruct m; simpl in *; try (apply Hmv; assumption).
        destruct mv; simpl in *; [apply Hmv; assumption|reflexivity].
      + destruct m; simpl in *; try (apply Hmv; assumption).
        * destruct mv; simpl in *; [apply Hmv; assumption|reflexivity].
        * destruct ph; simpl in *; try (apply Hmv; assumption).
          destruct mv; simpl in *; [apply Hmv; assumption|reflexivity].
      + unfold effective_recall_floor; simpl.
        destruct (smoke_detected rf) eqn:Hs; simpl.
        * destruct (Nat.eqb fl arf) eqn:Heq; simpl in *; reflexivity.
        * destruct (Nat.eqb fl rf) eqn:Heq; simpl in *; reflexivity.
      + destruct (Nat.eqb cid designated_fire_car); destruct (pressurized fl); simpl in *;
        try reflexivity; apply Hmv; assumption.
      + destruct m; simpl in *; auto; apply Hmv; assumption.
      + destruct m; simpl in *; auto; apply Hmv; assumption.
      + destruct mv; simpl in *; [apply Hmv; assumption|reflexivity].
      + destruct mv; simpl in *.
        * destruct tg as [f0|]; simpl in *.
          -- unfold arrive in *; simpl in *.
             destruct (pressurized f0); simpl in *; [reflexivity|discriminate Hmoving].
          -- unfold arrive in *; simpl in *; apply Hmv; exact Hmoving.
        * discriminate Hmoving.
      + destruct mv; simpl in *; [apply Hmv; assumption|].
        destruct m; simpl in *; try discriminate Hmoving; auto.
      + reflexivity.
      + destruct mv; simpl in *; [apply Hmv; assumption|].
        destruct m; simpl in *; try (apply Hmv; assumption).
        destruct ph; simpl in *; [discriminate Hmoving|apply Hmv; assumption].
      + destruct m; simpl in *; [apply Hmv; assumption|apply Hmv; assumption|reflexivity].
      + destruct m; simpl in *; try (apply Hmv; assumption).
        destruct mv; simpl in *; try (apply Hmv; assumption).
        destruct rdl; simpl in *; apply Hmv; assumption.
    - destruct cmd; simpl in *.
      + destruct m; simpl in *;
          try (destruct mv; auto; apply start_move_safe; split; auto).
      + destruct m; simpl in *;
          [destruct mv; auto; apply start_move_safe; split; auto
          | exact Hmode
          | destruct ph; simpl in *;
              [destruct mv; auto; apply start_move_safe; split; auto; destruct Hmode; tauto
              | exact Hmode] ].
      + unfold effective_recall_floor; simpl.
        destruct (smoke_detected rf) eqn:Hs; simpl.
        * destruct (Nat.eqb fl arf) eqn:Heq; simpl in *; reflexivity.
        * destruct (Nat.eqb fl rf) eqn:Heq; simpl in *; reflexivity.
      + destruct (Nat.eqb cid designated_fire_car) eqn:Hcar; destruct (pressurized fl) eqn:Hp; simpl in *.
        * split; [exact Hp|intros Habs; discriminate Habs].
        * destruct m; simpl in *; auto.
          destruct Hmode as [Hprs _]. exfalso. rewrite Hprs in Hp. discriminate.
        * destruct m; simpl in *; auto. destruct Hmode as [_ Hdh]. split; [exact Hp|exact Hdh].
        * destruct m; simpl in *; auto.
          destruct Hmode as [Hprs _]. exfalso. rewrite Hprs in Hp. discriminate.
      + destruct m; simpl in *; auto.
      + destruct m; simpl in *; auto.
        split; [destruct Hmode; auto|intros Habs; discriminate Habs].
      + destruct mv; simpl in *; auto.
        destruct m; simpl in *;
          [destruct (@start_move_safe
                {| car_id := cid; mode := Normal; door := d; moving := false;
                   floor := fl; target := tg; phaseII := ph; door_hold := dh;
                   recall_floor := rf; alt_recall_floor := arf;
                   recall_deadline := rdl; alarm := alm |}
                f (conj Hmv I)) as [_ Hsmode]; exact Hsmode
          | destruct (@start_move_safe
                {| car_id := cid; mode := FireRecall; door := d; moving := false;
                   floor := fl; target := tg; phaseII := ph; door_hold := dh;
                   recall_floor := rf; alt_recall_floor := arf;
                   recall_deadline := rdl; alarm := alm |}
                f (conj Hmv Hmode)) as [_ Hsmode]; exact Hsmode
          | destruct (@start_move_safe
                {| car_id := cid; mode := FireService; door := d; moving := false;
                   floor := fl; target := tg; phaseII := ph; door_hold := dh;
                   recall_floor := rf; alt_recall_floor := arf;
                   recall_deadline := rdl; alarm := alm |}
                f (conj Hmv Hmode)) as [_ Hsmode]; exact Hsmode ].
      + destruct mv; simpl in *; auto. apply arrive_safe; split; auto.
      + destruct mv; simpl in *; auto. destruct m; simpl in *; auto.
      + destruct m; simpl in *; auto.
        destruct Hmode as [Hprs Hdh]. split; [exact Hprs|intros Habs; discriminate Habs].
      + destruct mv; simpl in *; auto.
        destruct m; simpl in *; auto.
        destruct ph; simpl in *; auto.
        destruct Hmode as [Hprs Hdh]. split; [exact Hprs|intros _; reflexivity].
      + destruct m; simpl in *; auto.
        destruct Hmode as [Hprs Hdh]. split; [exact Hprs|intros Habs; discriminate Habs].
      + destruct m; simpl in *; auto.
        destruct mv; simpl in *; auto.
        destruct rdl; simpl in *; auto.
  Qed.

  (** Safety preserved over any sequence of commands. *)
  Lemma run_preserves_safe : forall cmds c,
    safe c -> safe (run_cmds cmds c).
  Proof.
    intros cmds; induction cmds as [|cmd rest IH]; intros c Hs; simpl; auto.
    apply IH. apply apply_preserves_safe; assumption.
  Qed.

  (** Hall calls have no effect outside Normal. *)
  Lemma hall_calls_ignored_in_fire_modes :
    forall c f, mode c <> Normal -> apply c (HallCall f) = c.
  Proof.
    intros c f Hm. destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in *.
    destruct m; simpl; congruence.
  Qed.

  (** Doors remain closed while moving, for any run. *)
  Corollary run_moving_has_closed_doors : forall c cmds,
    safe c -> moving (run_cmds cmds c) = true -> door (run_cmds cmds c) = Closed.
  Proof.
    intros c cmds Hsafe Hmv.
    destruct (@run_preserves_safe cmds c Hsafe) as [Hmcond _].
    apply Hmcond; assumption.
  Qed.

  (** Non-designated cars cannot enter FireService mode via FireServiceEnable.
      If the car was not already in FireService, it cannot enter it. *)
  Lemma non_designated_car_blocked_from_fire_service :
    forall c, car_id c <> designated_fire_car -> mode c <> FireService ->
              mode (apply c FireServiceEnable) <> FireService.
  Proof.
    intros c Hne Hm.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in *.
    destruct (Nat.eqb cid designated_fire_car) eqn:Hcar; simpl.
    - exfalso. apply Hne. apply PeanoNat.Nat.eqb_eq. exact Hcar.
    - destruct (pressurized fl); simpl; exact Hm.
  Qed.

  (** In FireRecall mode while moving, deadline decrements each tick. *)
  Lemma tick_decrements_deadline :
    forall c, mode c = FireRecall -> moving c = true -> recall_deadline c > 0 ->
              recall_deadline (apply c Tick) = pred (recall_deadline c).
  Proof.
    intros c Hm Hmv Hdl.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in *.
    rewrite Hm, Hmv.
    destruct rdl as [|n]; simpl.
    - lia.
    - reflexivity.
  Qed.

  (** Alarm is raised when deadline expires during recall travel. *)
  Lemma timeout_raises_alarm :
    forall c, mode c = FireRecall -> moving c = true -> recall_deadline c = 0 ->
              alarm (apply c Tick) = true.
  Proof.
    intros c Hm Hmv Hdl.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in *.
    rewrite Hm, Hmv, Hdl.
    reflexivity.
  Qed.

  (** ===== WITNESSES AND COUNTEREXAMPLES ===== *)

  (** A safe initial car: parked at floor 0, Normal mode, doors closed. *)
  Definition initial_car (cid rf arf : nat) : Car :=
    {| car_id := cid;
       mode := Normal;
       door := Closed;
       moving := false;
       floor := 0;
       target := None;
       phaseII := false;
       door_hold := false;
       recall_floor := rf;
       alt_recall_floor := arf;
       recall_deadline := 0;
       alarm := false |}.

  Lemma initial_car_is_safe : forall cid rf arf, safe (initial_car cid rf arf).
  Proof.
    intros cid rf arf.
    split.
    - intros Habs.
      discriminate Habs.
    - exact I.
  Qed.

  (** Unsafe witness 1: moving with doors open. *)
  Definition unsafe_moving_open : Car :=
    {| car_id := 0;
       mode := Normal;
       door := Open;
       moving := true;
       floor := 0;
       target := Some 5;
       phaseII := false;
       door_hold := false;
       recall_floor := 0;
       alt_recall_floor := 1;
       recall_deadline := 0;
       alarm := false |}.

  Lemma unsafe_moving_open_is_unsafe : ~safe unsafe_moving_open.
  Proof.
    intros [Hmv _].
    simpl in Hmv.
    specialize (Hmv eq_refl).
    discriminate Hmv.
  Qed.

  (** Unsafe witness 2: FireRecall with doors open. *)
  Definition unsafe_recall_open : Car :=
    {| car_id := 0;
       mode := FireRecall;
       door := Open;
       moving := false;
       floor := 0;
       target := None;
       phaseII := false;
       door_hold := false;
       recall_floor := 0;
       alt_recall_floor := 1;
       recall_deadline := 0;
       alarm := false |}.

  Lemma unsafe_recall_open_is_unsafe : ~safe unsafe_recall_open.
  Proof.
    intros [_ Hmode].
    simpl in Hmode.
    discriminate Hmode.
  Qed.

  (** Unsafe witness 3: FireService on unpressurized floor.
      Requires assumption that floor 99 is not pressurized. *)
  Definition unsafe_fire_unpressurized : Car :=
    {| car_id := 0;
       mode := FireService;
       door := Closed;
       moving := false;
       floor := 99;
       target := None;
       phaseII := true;
       door_hold := false;
       recall_floor := 0;
       alt_recall_floor := 1;
       recall_deadline := 0;
       alarm := false |}.

  Lemma unsafe_fire_unpressurized_is_unsafe :
    pressurized 99 = false -> ~safe unsafe_fire_unpressurized.
  Proof.
    intros Hunpres [_ Hmode].
    simpl in Hmode.
    destruct Hmode as [Hpres _].
    rewrite Hunpres in Hpres.
    discriminate Hpres.
  Qed.

  (** Unsafe witness 4: FireService with door open but no constant pressure. *)
  Definition unsafe_fire_no_hold : Car :=
    {| car_id := 0;
       mode := FireService;
       door := Open;
       moving := false;
       floor := 0;
       target := None;
       phaseII := true;
       door_hold := false;
       recall_floor := 0;
       alt_recall_floor := 1;
       recall_deadline := 0;
       alarm := false |}.

  Lemma unsafe_fire_no_hold_is_unsafe :
    pressurized 0 = true -> ~safe unsafe_fire_no_hold.
  Proof.
    intros Hpres [_ Hmode].
    simpl in Hmode.
    destruct Hmode as [_ Hdh].
    specialize (Hdh eq_refl).
    discriminate Hdh.
  Qed.

  (** ===== REACHABILITY PROOFS ===== *)

  (** FireRecall is reachable from Normal via Recall command. *)
  Lemma reachable_fire_recall : forall c,
    mode c = Normal ->
    mode (apply c Recall) = FireRecall.
  Proof.
    intros c Hm.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in *.
    rewrite Hm.
    unfold effective_recall_floor; simpl.
    destruct (smoke_detected rf); destruct (Nat.eqb fl _); reflexivity.
  Qed.

  (** FireRecall is reachable from any mode. *)
  Lemma recall_always_enters_fire_recall : forall c,
    mode (apply c Recall) = FireRecall.
  Proof.
    intros c.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl.
    unfold effective_recall_floor; simpl.
    destruct (smoke_detected rf); destruct (Nat.eqb fl _); reflexivity.
  Qed.

  (** FireService is reachable from FireRecall for designated car on pressurized floor. *)
  Lemma reachable_fire_service : forall c,
    mode c = FireRecall ->
    car_id c = designated_fire_car ->
    pressurized (floor c) = true ->
    mode (apply c FireServiceEnable) = FireService.
  Proof.
    intros c Hm Hcar Hpres.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in *.
    rewrite Hcar.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite Hpres.
    reflexivity.
  Qed.

  (** Complete path: Normal -> FireRecall -> FireService. *)
  Lemma reachable_fire_service_from_normal : forall c,
    mode c = Normal ->
    car_id c = designated_fire_car ->
    smoke_detected (recall_floor c) = false ->
    floor c = recall_floor c ->
    pressurized (floor c) = true ->
    mode (apply (apply c Recall) FireServiceEnable) = FireService.
  Proof.
    intros c Hm Hcar Hsmoke Hfl Hpres.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in *.
    rewrite Hm.
    unfold effective_recall_floor; simpl.
    rewrite Hsmoke.
    rewrite <- Hfl.
    rewrite PeanoNat.Nat.eqb_refl.
    simpl.
    rewrite Hcar.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite Hpres.
    reflexivity.
  Qed.

  (** Witness: concrete command sequence reaching FireService. *)
  Definition reach_fire_service_cmds : list Cmd := Recall :: FireServiceEnable :: nil.

  Lemma witness_fire_service_reachable :
    pressurized 0 = true ->
    smoke_detected 0 = false ->
    mode (run_cmds reach_fire_service_cmds (initial_car designated_fire_car 0 1)) = FireService.
  Proof.
    intros Hpres Hsmoke.
    unfold reach_fire_service_cmds, run_cmds, initial_car, apply; simpl.
    unfold effective_recall_floor; simpl.
    rewrite Hsmoke; simpl.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite Hpres; simpl.
    reflexivity.
  Qed.

  (** ===== MULTI-CAR SYSTEM ===== *)

  (** A building contains a list of elevator cars. *)
  Definition Building := list Car.

  (** All cars in the building are individually safe. *)
  Definition all_cars_safe (b : Building) : Prop :=
    forall c, In c b -> safe c.

  (** At most one car is in FireService mode. *)
  Fixpoint count_fire_service (b : Building) : nat :=
    match b with
    | nil => 0
    | c :: rest =>
        match mode c with
        | FireService => S (count_fire_service rest)
        | _ => count_fire_service rest
        end
    end.

  Definition at_most_one_fire_service (b : Building) : Prop :=
    count_fire_service b <= 1.

  (** System-level safety: all cars safe and at most one in FireService. *)
  Definition system_safe (b : Building) : Prop :=
    all_cars_safe b /\ at_most_one_fire_service b.

  (** Apply command to a specific car by index. *)
  Fixpoint apply_to_car (idx : nat) (cmd : Cmd) (b : Building) : Building :=
    match b with
    | nil => nil
    | c :: rest =>
        match idx with
        | 0 => apply c cmd :: rest
        | S n => c :: apply_to_car n cmd rest
        end
    end.

  (** Helper: In preserved under apply_to_car. *)
  Lemma in_apply_to_car : forall idx cmd b c,
    In c (apply_to_car idx cmd b) ->
    (exists c', In c' b /\ c = apply c' cmd) \/ In c b.
  Proof.
    intros idx cmd b.
    generalize dependent idx.
    induction b as [|hd tl IH]; intros idx c Hin.
    - destruct idx; simpl in Hin; exfalso; exact Hin.
    - destruct idx as [|n]; simpl in *.
      + destruct Hin as [Heq | Hin].
        * left.
          exists hd.
          split.
          -- left.
             reflexivity.
          -- symmetry.
             exact Heq.
        * right.
          right.
          exact Hin.
      + destruct Hin as [Heq | Hin].
        * right.
          left.
          exact Heq.
        * destruct (IH n c Hin) as [[c' [Hin' Heq]] | Hin'].
          -- left.
             exists c'.
             split.
             ++ right.
                exact Hin'.
             ++ exact Heq.
          -- right.
             right.
             exact Hin'.
  Qed.

  (** All cars safe preserved when applying command to one car. *)
  Lemma all_cars_safe_preserved : forall idx cmd b,
    all_cars_safe b -> all_cars_safe (apply_to_car idx cmd b).
  Proof.
    intros idx cmd b Hsafe c Hin.
    destruct (in_apply_to_car idx cmd b c Hin) as [[c' [Hin' Heq]] | Hin'].
    - rewrite Heq.
      apply apply_preserves_safe.
      apply Hsafe.
      exact Hin'.
    - apply Hsafe.
      exact Hin'.
  Qed.

  (** Only designated car can enter FireService. *)
  Lemma fire_service_only_designated : forall c,
    mode c <> FireService ->
    mode (apply c FireServiceEnable) = FireService ->
    car_id c = designated_fire_car.
  Proof.
    intros c Hnot Hfs.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in Hnot.
    unfold apply in Hfs; simpl in Hfs.
    destruct (Nat.eqb cid designated_fire_car) eqn:Hcar.
    - apply PeanoNat.Nat.eqb_eq.
      exact Hcar.
    - simpl in Hfs.
      destruct m; exfalso; apply Hnot; exact Hfs.
  Qed.

  (** Initial building: all cars start in Normal mode. *)
  Definition initial_building (car_ids : list nat) (rf arf : nat) : Building :=
    map (fun cid => initial_car cid rf arf) car_ids.

  Lemma initial_building_all_safe : forall car_ids rf arf,
    all_cars_safe (initial_building car_ids rf arf).
  Proof.
    intros car_ids rf arf c Hin.
    unfold initial_building in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [cid [Heq _]].
    rewrite <- Heq.
    apply initial_car_is_safe.
  Qed.

  Lemma initial_building_no_fire_service : forall car_ids rf arf,
    count_fire_service (initial_building car_ids rf arf) = 0.
  Proof.
    intros car_ids rf arf.
    induction car_ids as [|cid rest IH]; simpl.
    - reflexivity.
    - exact IH.
  Qed.

  Lemma initial_building_system_safe : forall car_ids rf arf,
    system_safe (initial_building car_ids rf arf).
  Proof.
    intros car_ids rf arf.
    split.
    - apply initial_building_all_safe.
    - unfold at_most_one_fire_service.
      rewrite initial_building_no_fire_service.
      lia.
  Qed.

  (** ===== LIVENESS / CONTROLLABILITY ===== *)

  (** Arrive brings car to target floor if pressurized. *)
  Lemma arrive_reaches_target : forall c f,
    target c = Some f ->
    pressurized f = true ->
    floor (arrive c) = f.
  Proof.
    intros c f Htgt Hpres.
    unfold arrive.
    rewrite Htgt.
    rewrite Hpres.
    reflexivity.
  Qed.

  (** Arrive completes movement. *)
  Lemma arrive_stops_moving : forall c,
    target c <> None ->
    moving (arrive c) = false.
  Proof.
    intros c Htgt.
    unfold arrive.
    destruct (target c) as [f|].
    - destruct (pressurized f); reflexivity.
    - exfalso.
      apply Htgt.
      reflexivity.
  Qed.

  (** Recall sets target to effective recall floor if not already there. *)
  Lemma recall_targets_recall_floor : forall c,
    floor c <> effective_recall_floor c ->
    target (apply c Recall) = Some (effective_recall_floor c).
  Proof.
    intros c Hneq.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in *.
    unfold effective_recall_floor in *; simpl in *.
    destruct (smoke_detected rf) eqn:Hs.
    - destruct (Nat.eqb fl arf) eqn:Heq.
      + exfalso.
        apply Hneq.
        apply PeanoNat.Nat.eqb_eq in Heq.
        exact Heq.
      + reflexivity.
    - destruct (Nat.eqb fl rf) eqn:Heq.
      + exfalso.
        apply Hneq.
        apply PeanoNat.Nat.eqb_eq in Heq.
        exact Heq.
      + reflexivity.
  Qed.

  (** Car at recall floor after Recall is in FireRecall with doors closed. *)
  Lemma recall_at_floor_complete : forall c,
    floor c = effective_recall_floor c ->
    let c' := apply c Recall in
    mode c' = FireRecall /\ door c' = Closed /\ moving c' = false /\ floor c' = effective_recall_floor c.
  Proof.
    intros c Heq.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in *.
    unfold effective_recall_floor in *; simpl in *.
    destruct (smoke_detected rf) eqn:Hs; simpl.
    - rewrite <- Heq.
      rewrite PeanoNat.Nat.eqb_refl.
      auto.
    - rewrite <- Heq.
      rewrite PeanoNat.Nat.eqb_refl.
      auto.
  Qed.

  (** Witness: complete recall sequence for car already at recall floor. *)
  Definition recall_at_floor_cmds : list Cmd := Recall :: nil.

  Lemma witness_recall_completes_at_floor :
    forall cid arf,
    smoke_detected 0 = false ->
    let c := initial_car cid 0 arf in
    let c' := run_cmds recall_at_floor_cmds c in
    mode c' = FireRecall /\ floor c' = 0 /\ moving c' = false.
  Proof.
    intros cid arf Hsmoke.
    unfold recall_at_floor_cmds, run_cmds, initial_car, apply; simpl.
    unfold effective_recall_floor; simpl.
    rewrite Hsmoke; simpl.
    auto.
  Qed.

  (** Witness: recall sequence for car not at recall floor (concrete instance). *)
  Definition recall_travel_cmds : list Cmd := Recall :: Arrive :: nil.

  Lemma witness_recall_travel_completes_concrete :
    smoke_detected 1 = false ->
    pressurized 1 = true ->
    let c' := run_cmds recall_travel_cmds (initial_car 0 1 2) in
    mode c' = FireRecall /\ floor c' = 1 /\ moving c' = false.
  Proof.
    intros Hsmoke Hpres.
    unfold recall_travel_cmds, run_cmds, initial_car.
    simpl.
    unfold effective_recall_floor.
    simpl.
    rewrite Hsmoke.
    simpl.
    unfold arrive.
    simpl.
    rewrite Hpres.
    auto.
  Qed.

  (** Strong controllability: from any safe state in FireRecall moving toward
      recall floor, Arrive brings car to recall floor. *)
  Lemma fire_recall_controllable : forall c f,
    safe c ->
    mode c = FireRecall ->
    moving c = true ->
    target c = Some f ->
    pressurized f = true ->
    let c' := apply c Arrive in
    floor c' = f /\ moving c' = false /\ mode c' = FireRecall.
  Proof.
    intros c f Hsafe Hm Hmv Htgt Hpres.
    destruct c as [cid m d mv fl tg ph dh rf arf rdl alm]; simpl in *.
    rewrite Hm, Hmv; simpl.
    rewrite Htgt.
    unfold arrive; simpl.
    rewrite Hpres.
    auto.
  Qed.

End ElevatorFire.
