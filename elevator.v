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

From Coq Require Import Lia Bool.

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

End ElevatorFire.
