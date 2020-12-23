%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:12 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   92 (1216 expanded)
%              Number of clauses        :   63 ( 383 expanded)
%              Number of leaves         :   13 ( 297 expanded)
%              Depth                    :   13
%              Number of atoms          :  590 (13169 expanded)
%              Number of equality atoms :   28 (  87 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   48 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_tsep_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ( ( m1_pre_topc(X2,X4)
                      & r1_tsep_1(X4,X3) )
                   => ( v1_tsep_1(X2,k1_tsep_1(X1,X2,X3))
                      & m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
                      & v1_tsep_1(X2,k1_tsep_1(X1,X3,X2))
                      & m1_pre_topc(X2,k1_tsep_1(X1,X3,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(commutativity_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(t25_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(t22_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => m1_pre_topc(X2,k1_tsep_1(X1,X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

fof(t39_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( ~ ( ~ r1_tsep_1(k1_tsep_1(X1,X2,X3),X4)
                        & r1_tsep_1(X2,X4)
                        & r1_tsep_1(X3,X4) )
                    & ~ ( ~ ( r1_tsep_1(X2,X4)
                            & r1_tsep_1(X3,X4) )
                        & r1_tsep_1(k1_tsep_1(X1,X2,X3),X4) )
                    & ~ ( ~ r1_tsep_1(X4,k1_tsep_1(X1,X2,X3))
                        & r1_tsep_1(X4,X2)
                        & r1_tsep_1(X4,X3) )
                    & ~ ( ~ ( r1_tsep_1(X4,X2)
                            & r1_tsep_1(X4,X3) )
                        & r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tmap_1)).

fof(t33_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( m1_pre_topc(X2,X3)
                   => ( ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) )
                      | ( k2_tsep_1(X1,X3,k1_tsep_1(X1,X2,X4)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                        & k2_tsep_1(X1,X3,k1_tsep_1(X1,X4,X2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tmap_1)).

fof(t14_tmap_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> ( v1_tsep_1(X3,X1)
                    & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

fof(t44_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_tsep_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X3,X2)
               => ( v1_tsep_1(k2_tsep_1(X1,X3,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X1,X3,X2),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tmap_1)).

fof(t22_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( m1_pre_topc(X2,X3)
               => ( ~ r1_tsep_1(X2,X3)
                  & ~ r1_tsep_1(X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_tsep_1(X4,X1)
                      & m1_pre_topc(X4,X1) )
                   => ( ( m1_pre_topc(X2,X4)
                        & r1_tsep_1(X4,X3) )
                     => ( v1_tsep_1(X2,k1_tsep_1(X1,X2,X3))
                        & m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
                        & v1_tsep_1(X2,k1_tsep_1(X1,X3,X2))
                        & m1_pre_topc(X2,k1_tsep_1(X1,X3,X2)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_tmap_1])).

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | l1_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & v1_tsep_1(esk4_0,esk1_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & m1_pre_topc(esk2_0,esk4_0)
    & r1_tsep_1(esk4_0,esk3_0)
    & ( ~ v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))
      | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X6,X5)
      | v2_pre_topc(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_16,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v2_struct_0(k1_tsep_1(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) )
      & ( v1_pre_topc(k1_tsep_1(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) )
      & ( m1_pre_topc(k1_tsep_1(X12,X13,X14),X12)
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_17,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X10,X9)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,X9)
      | k1_tsep_1(X9,X10,X11) = k1_tsep_1(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

fof(c_0_18,plain,(
    ! [X1,X2,X4,X3] :
      ( epred1_4(X3,X4,X2,X1)
    <=> ( ~ ( ~ r1_tsep_1(k1_tsep_1(X1,X2,X3),X4)
            & r1_tsep_1(X2,X4)
            & r1_tsep_1(X3,X4) )
        & ~ ( ~ ( r1_tsep_1(X2,X4)
                & r1_tsep_1(X3,X4) )
            & r1_tsep_1(k1_tsep_1(X1,X2,X3),X4) )
        & ~ ( ~ r1_tsep_1(X4,k1_tsep_1(X1,X2,X3))
            & r1_tsep_1(X4,X2)
            & r1_tsep_1(X4,X3) )
        & ~ ( ~ ( r1_tsep_1(X4,X2)
                & r1_tsep_1(X4,X3) )
            & r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)) ) ) ) ),
    introduced(definition)).

fof(c_0_19,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X28,X27)
      | k1_tsep_1(X27,X28,X28) = g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).

cnf(c_0_20,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X24,X25,X26] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X25,X24)
      | v2_struct_0(X26)
      | ~ m1_pre_topc(X26,X24)
      | m1_pre_topc(X25,k1_tsep_1(X24,X25,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

cnf(c_0_26,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_31,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => epred1_4(X3,X4,X2,X1) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t39_tmap_1,c_0_18])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_21]),c_0_22]),c_0_24])])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_22])]),c_0_28]),c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk3_0) = k1_tsep_1(esk1_0,esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_22])]),c_0_28]),c_0_29])).

fof(c_0_42,plain,(
    ! [X37,X38,X39,X40] :
      ( v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | v2_struct_0(X38)
      | ~ m1_pre_topc(X38,X37)
      | v2_struct_0(X39)
      | ~ m1_pre_topc(X39,X37)
      | v2_struct_0(X40)
      | ~ m1_pre_topc(X40,X37)
      | epred1_4(X39,X40,X38,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).

fof(c_0_43,plain,(
    ! [X33,X34,X35,X36] :
      ( ( k2_tsep_1(X33,X35,k1_tsep_1(X33,X34,X36)) = g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))
        | ~ r1_tsep_1(X35,X36)
        | ~ m1_pre_topc(X34,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( k2_tsep_1(X33,X35,k1_tsep_1(X33,X36,X34)) = g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))
        | ~ r1_tsep_1(X35,X36)
        | ~ m1_pre_topc(X34,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( k2_tsep_1(X33,X35,k1_tsep_1(X33,X34,X36)) = g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))
        | ~ r1_tsep_1(X36,X35)
        | ~ m1_pre_topc(X34,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( k2_tsep_1(X33,X35,k1_tsep_1(X33,X36,X34)) = g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))
        | ~ r1_tsep_1(X36,X35)
        | ~ m1_pre_topc(X34,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_tmap_1])])])])])).

fof(c_0_44,plain,(
    ! [X18,X19,X20] :
      ( ( v1_tsep_1(X20,X18)
        | ~ v1_tsep_1(X19,X18)
        | ~ m1_pre_topc(X19,X18)
        | X20 != g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_pre_topc(X20,X18)
        | ~ v1_tsep_1(X19,X18)
        | ~ m1_pre_topc(X19,X18)
        | X20 != g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( v1_tsep_1(X19,X18)
        | ~ v1_tsep_1(X20,X18)
        | ~ m1_pre_topc(X20,X18)
        | X20 != g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_pre_topc(X19,X18)
        | ~ v1_tsep_1(X20,X18)
        | ~ m1_pre_topc(X20,X18)
        | X20 != g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_tmap_1])])])])).

cnf(c_0_45,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k1_tsep_1(esk4_0,esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_46,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(X1,k1_tsep_1(esk1_0,X1,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_22]),c_0_24])]),c_0_28]),c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_34])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk3_0,esk2_0) = k1_tsep_1(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_34])).

fof(c_0_50,plain,(
    ! [X1,X2,X4,X3] :
      ( epred1_4(X3,X4,X2,X1)
     => ( ~ ( ~ r1_tsep_1(k1_tsep_1(X1,X2,X3),X4)
            & r1_tsep_1(X2,X4)
            & r1_tsep_1(X3,X4) )
        & ~ ( ~ ( r1_tsep_1(X2,X4)
                & r1_tsep_1(X3,X4) )
            & r1_tsep_1(k1_tsep_1(X1,X2,X3),X4) )
        & ~ ( ~ r1_tsep_1(X4,k1_tsep_1(X1,X2,X3))
            & r1_tsep_1(X4,X2)
            & r1_tsep_1(X4,X3) )
        & ~ ( ~ ( r1_tsep_1(X4,X2)
                & r1_tsep_1(X4,X3) )
            & r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_18])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | epred1_4(X3,X4,X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( k2_tsep_1(X1,X2,k1_tsep_1(X1,X3,X4)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | X3 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k1_tsep_1(esk4_0,esk2_0,esk2_0) = k1_tsep_1(esk1_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_40]),c_0_22]),c_0_24])]),c_0_34]),c_0_29]),c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_47]),c_0_22])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_40]),c_0_27]),c_0_22])]),c_0_34]),c_0_28]),c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( v2_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_47]),c_0_22]),c_0_24])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_61,plain,(
    ! [X48,X49,X50,X51] :
      ( ( r1_tsep_1(k1_tsep_1(X48,X49,X51),X50)
        | ~ r1_tsep_1(X49,X50)
        | ~ r1_tsep_1(X51,X50)
        | ~ epred1_4(X51,X50,X49,X48) )
      & ( r1_tsep_1(X49,X50)
        | ~ r1_tsep_1(k1_tsep_1(X48,X49,X51),X50)
        | ~ epred1_4(X51,X50,X49,X48) )
      & ( r1_tsep_1(X51,X50)
        | ~ r1_tsep_1(k1_tsep_1(X48,X49,X51),X50)
        | ~ epred1_4(X51,X50,X49,X48) )
      & ( r1_tsep_1(X50,k1_tsep_1(X48,X49,X51))
        | ~ r1_tsep_1(X50,X49)
        | ~ r1_tsep_1(X50,X51)
        | ~ epred1_4(X51,X50,X49,X48) )
      & ( r1_tsep_1(X50,X49)
        | ~ r1_tsep_1(X50,k1_tsep_1(X48,X49,X51))
        | ~ epred1_4(X51,X50,X49,X48) )
      & ( r1_tsep_1(X50,X51)
        | ~ r1_tsep_1(X50,k1_tsep_1(X48,X49,X51))
        | ~ epred1_4(X51,X50,X49,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_50])])])])).

cnf(c_0_62,negated_conjecture,
    ( epred1_4(X1,esk4_0,X2,esk1_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_21]),c_0_22]),c_0_24])]),c_0_35]),c_0_29])).

fof(c_0_63,plain,(
    ! [X41,X42,X43] :
      ( ( v1_tsep_1(k2_tsep_1(X41,X43,X42),X42)
        | r1_tsep_1(X43,X42)
        | v2_struct_0(X43)
        | ~ v1_tsep_1(X43,X41)
        | ~ m1_pre_topc(X43,X41)
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( m1_pre_topc(k2_tsep_1(X41,X43,X42),X42)
        | r1_tsep_1(X43,X42)
        | v2_struct_0(X43)
        | ~ v1_tsep_1(X43,X41)
        | ~ m1_pre_topc(X43,X41)
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_tmap_1])])])])])).

cnf(c_0_64,negated_conjecture,
    ( k2_tsep_1(X1,esk4_0,k1_tsep_1(X1,X2,esk3_0)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_28]),c_0_35])).

cnf(c_0_65,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_54,c_0_23]),c_0_20])])).

cnf(c_0_66,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k1_tsep_1(esk1_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_40]),c_0_22])])).

cnf(c_0_68,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_40]),c_0_22]),c_0_24])])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),X1,esk2_0),k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_56]),c_0_57])]),c_0_34]),c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( k1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0,esk2_0) = k1_tsep_1(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_56]),c_0_57]),c_0_59])]),c_0_34]),c_0_45]),c_0_55]),c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_56])])).

cnf(c_0_72,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(X1,k1_tsep_1(X3,X4,X2))
    | ~ epred1_4(X2,X1,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( epred1_4(esk2_0,esk4_0,X1,esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_40]),c_0_34])).

cnf(c_0_74,plain,
    ( v1_tsep_1(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_21]),c_0_22]),c_0_24])]),c_0_29])).

cnf(c_0_76,negated_conjecture,
    ( v1_tsep_1(esk2_0,X1)
    | ~ v1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk2_0),X1)
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk2_0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])])).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk2_0),k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_56]),c_0_70]),c_0_34])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_49]),c_0_49]),c_0_56])])).

cnf(c_0_79,plain,
    ( r1_tsep_1(X1,esk2_0)
    | ~ epred1_4(esk2_0,X1,esk3_0,esk1_0)
    | ~ r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_49])).

cnf(c_0_80,negated_conjecture,
    ( epred1_4(esk2_0,esk4_0,esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_27]),c_0_28])).

cnf(c_0_81,negated_conjecture,
    ( r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | v1_tsep_1(k2_tsep_1(esk1_0,X1,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v1_tsep_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_47]),c_0_22]),c_0_24])]),c_0_29]),c_0_58])).

cnf(c_0_82,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_83,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) = k1_tsep_1(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_33]),c_0_45]),c_0_55]),c_0_40])]),c_0_34])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk2_0),k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_57]),c_0_59])]),c_0_78])).

fof(c_0_85,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r1_tsep_1(X22,X23)
        | ~ m1_pre_topc(X22,X23)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_tsep_1(X23,X22)
        | ~ m1_pre_topc(X22,X23)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).

cnf(c_0_86,plain,
    ( r1_tsep_1(esk4_0,esk2_0)
    | ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_21]),c_0_82])]),c_0_35]),c_0_83]),c_0_84])).

cnf(c_0_88,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_89,plain,
    ( r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_90,plain,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_33])]),c_0_34]),c_0_35])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_40]),c_0_21]),c_0_22]),c_0_24])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:45:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.10/3.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 3.10/3.37  # and selection function SelectNewComplexAHP.
% 3.10/3.37  #
% 3.10/3.37  # Preprocessing time       : 0.031 s
% 3.10/3.37  # Presaturation interreduction done
% 3.10/3.37  
% 3.10/3.37  # Proof found!
% 3.10/3.37  # SZS status Theorem
% 3.10/3.37  # SZS output start CNFRefutation
% 3.10/3.37  fof(t46_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X1))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X4)&r1_tsep_1(X4,X3))=>(((v1_tsep_1(X2,k1_tsep_1(X1,X2,X3))&m1_pre_topc(X2,k1_tsep_1(X1,X2,X3)))&v1_tsep_1(X2,k1_tsep_1(X1,X3,X2)))&m1_pre_topc(X2,k1_tsep_1(X1,X3,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tmap_1)).
% 3.10/3.37  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.10/3.37  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.10/3.37  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 3.10/3.37  fof(commutativity_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>k1_tsep_1(X1,X2,X3)=k1_tsep_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k1_tsep_1)).
% 3.10/3.37  fof(t25_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 3.10/3.37  fof(t22_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tsep_1)).
% 3.10/3.37  fof(t39_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(((~(((~(r1_tsep_1(k1_tsep_1(X1,X2,X3),X4))&r1_tsep_1(X2,X4))&r1_tsep_1(X3,X4)))&~((~((r1_tsep_1(X2,X4)&r1_tsep_1(X3,X4)))&r1_tsep_1(k1_tsep_1(X1,X2,X3),X4))))&~(((~(r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)))&r1_tsep_1(X4,X2))&r1_tsep_1(X4,X3))))&~((~((r1_tsep_1(X4,X2)&r1_tsep_1(X4,X3)))&r1_tsep_1(X4,k1_tsep_1(X1,X2,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_tmap_1)).
% 3.10/3.37  fof(t33_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))|(k2_tsep_1(X1,X3,k1_tsep_1(X1,X2,X4))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&k2_tsep_1(X1,X3,k1_tsep_1(X1,X4,X2))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tmap_1)).
% 3.10/3.37  fof(t14_tmap_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X3=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(v1_tsep_1(X3,X1)&m1_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tmap_1)).
% 3.10/3.37  fof(t44_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((~(v2_struct_0(X3))&v1_tsep_1(X3,X1))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X3,X2))=>(v1_tsep_1(k2_tsep_1(X1,X3,X2),X2)&m1_pre_topc(k2_tsep_1(X1,X3,X2),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tmap_1)).
% 3.10/3.37  fof(t22_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(m1_pre_topc(X2,X3)=>(~(r1_tsep_1(X2,X3))&~(r1_tsep_1(X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 3.10/3.37  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X1))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X4)&r1_tsep_1(X4,X3))=>(((v1_tsep_1(X2,k1_tsep_1(X1,X2,X3))&m1_pre_topc(X2,k1_tsep_1(X1,X2,X3)))&v1_tsep_1(X2,k1_tsep_1(X1,X3,X2)))&m1_pre_topc(X2,k1_tsep_1(X1,X3,X2))))))))), inference(assume_negation,[status(cth)],[t46_tmap_1])).
% 3.10/3.37  fof(c_0_13, plain, ![X7, X8]:(~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|l1_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 3.10/3.37  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&(((~v2_struct_0(esk4_0)&v1_tsep_1(esk4_0,esk1_0))&m1_pre_topc(esk4_0,esk1_0))&((m1_pre_topc(esk2_0,esk4_0)&r1_tsep_1(esk4_0,esk3_0))&(~v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))|~m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 3.10/3.37  fof(c_0_15, plain, ![X5, X6]:(~v2_pre_topc(X5)|~l1_pre_topc(X5)|(~m1_pre_topc(X6,X5)|v2_pre_topc(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 3.10/3.37  fof(c_0_16, plain, ![X12, X13, X14]:(((~v2_struct_0(k1_tsep_1(X12,X13,X14))|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12)))&(v1_pre_topc(k1_tsep_1(X12,X13,X14))|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12))))&(m1_pre_topc(k1_tsep_1(X12,X13,X14),X12)|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 3.10/3.37  fof(c_0_17, plain, ![X9, X10, X11]:(v2_struct_0(X9)|~l1_pre_topc(X9)|v2_struct_0(X10)|~m1_pre_topc(X10,X9)|v2_struct_0(X11)|~m1_pre_topc(X11,X9)|k1_tsep_1(X9,X10,X11)=k1_tsep_1(X9,X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).
% 3.10/3.37  fof(c_0_18, plain, ![X1, X2, X4, X3]:(epred1_4(X3,X4,X2,X1)<=>(((~(((~(r1_tsep_1(k1_tsep_1(X1,X2,X3),X4))&r1_tsep_1(X2,X4))&r1_tsep_1(X3,X4)))&~((~((r1_tsep_1(X2,X4)&r1_tsep_1(X3,X4)))&r1_tsep_1(k1_tsep_1(X1,X2,X3),X4))))&~(((~(r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)))&r1_tsep_1(X4,X2))&r1_tsep_1(X4,X3))))&~((~((r1_tsep_1(X4,X2)&r1_tsep_1(X4,X3)))&r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)))))), introduced(definition)).
% 3.10/3.37  fof(c_0_19, plain, ![X27, X28]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(v2_struct_0(X28)|~m1_pre_topc(X28,X27)|k1_tsep_1(X27,X28,X28)=g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).
% 3.10/3.37  cnf(c_0_20, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.10/3.37  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_23, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.10/3.37  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  fof(c_0_25, plain, ![X24, X25, X26]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X24)|(v2_struct_0(X26)|~m1_pre_topc(X26,X24)|m1_pre_topc(X25,k1_tsep_1(X24,X25,X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).
% 3.10/3.37  cnf(c_0_26, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.10/3.37  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_30, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|k1_tsep_1(X1,X2,X3)=k1_tsep_1(X1,X3,X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.10/3.37  fof(c_0_31, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>epred1_4(X3,X4,X2,X1))))), inference(apply_def,[status(thm)],[t39_tmap_1, c_0_18])).
% 3.10/3.37  cnf(c_0_32, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.10/3.37  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 3.10/3.37  cnf(c_0_37, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_21]), c_0_22]), c_0_24])])).
% 3.10/3.37  cnf(c_0_38, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.10/3.37  cnf(c_0_39, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_22])]), c_0_28]), c_0_29])).
% 3.10/3.37  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_41, negated_conjecture, (k1_tsep_1(esk1_0,X1,esk3_0)=k1_tsep_1(esk1_0,esk3_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_27]), c_0_22])]), c_0_28]), c_0_29])).
% 3.10/3.37  fof(c_0_42, plain, ![X37, X38, X39, X40]:(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(v2_struct_0(X38)|~m1_pre_topc(X38,X37)|(v2_struct_0(X39)|~m1_pre_topc(X39,X37)|(v2_struct_0(X40)|~m1_pre_topc(X40,X37)|epred1_4(X39,X40,X38,X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).
% 3.10/3.37  fof(c_0_43, plain, ![X33, X34, X35, X36]:(((k2_tsep_1(X33,X35,k1_tsep_1(X33,X34,X36))=g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))|~r1_tsep_1(X35,X36)|~m1_pre_topc(X34,X35)|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|(v2_struct_0(X34)|~m1_pre_topc(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(k2_tsep_1(X33,X35,k1_tsep_1(X33,X36,X34))=g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))|~r1_tsep_1(X35,X36)|~m1_pre_topc(X34,X35)|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|(v2_struct_0(X34)|~m1_pre_topc(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&((k2_tsep_1(X33,X35,k1_tsep_1(X33,X34,X36))=g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))|~r1_tsep_1(X36,X35)|~m1_pre_topc(X34,X35)|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|(v2_struct_0(X34)|~m1_pre_topc(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(k2_tsep_1(X33,X35,k1_tsep_1(X33,X36,X34))=g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))|~r1_tsep_1(X36,X35)|~m1_pre_topc(X34,X35)|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|(v2_struct_0(X34)|~m1_pre_topc(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_tmap_1])])])])])).
% 3.10/3.37  fof(c_0_44, plain, ![X18, X19, X20]:(((v1_tsep_1(X20,X18)|(~v1_tsep_1(X19,X18)|~m1_pre_topc(X19,X18))|X20!=g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))|(~v2_pre_topc(X20)|~l1_pre_topc(X20))|(~v2_pre_topc(X19)|~l1_pre_topc(X19))|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(m1_pre_topc(X20,X18)|(~v1_tsep_1(X19,X18)|~m1_pre_topc(X19,X18))|X20!=g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))|(~v2_pre_topc(X20)|~l1_pre_topc(X20))|(~v2_pre_topc(X19)|~l1_pre_topc(X19))|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))&((v1_tsep_1(X19,X18)|(~v1_tsep_1(X20,X18)|~m1_pre_topc(X20,X18))|X20!=g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))|(~v2_pre_topc(X20)|~l1_pre_topc(X20))|(~v2_pre_topc(X19)|~l1_pre_topc(X19))|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(m1_pre_topc(X19,X18)|(~v1_tsep_1(X20,X18)|~m1_pre_topc(X20,X18))|X20!=g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))|(~v2_pre_topc(X20)|~l1_pre_topc(X20))|(~v2_pre_topc(X19)|~l1_pre_topc(X19))|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_tmap_1])])])])).
% 3.10/3.37  cnf(c_0_45, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k1_tsep_1(esk4_0,esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 3.10/3.37  cnf(c_0_46, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(X1,k1_tsep_1(esk1_0,X1,esk3_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_27]), c_0_22]), c_0_24])]), c_0_28]), c_0_29])).
% 3.10/3.37  cnf(c_0_47, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_34])).
% 3.10/3.37  cnf(c_0_48, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.10/3.37  cnf(c_0_49, negated_conjecture, (k1_tsep_1(esk1_0,esk3_0,esk2_0)=k1_tsep_1(esk1_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_34])).
% 3.10/3.37  fof(c_0_50, plain, ![X1, X2, X4, X3]:(epred1_4(X3,X4,X2,X1)=>(((~(((~(r1_tsep_1(k1_tsep_1(X1,X2,X3),X4))&r1_tsep_1(X2,X4))&r1_tsep_1(X3,X4)))&~((~((r1_tsep_1(X2,X4)&r1_tsep_1(X3,X4)))&r1_tsep_1(k1_tsep_1(X1,X2,X3),X4))))&~(((~(r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)))&r1_tsep_1(X4,X2))&r1_tsep_1(X4,X3))))&~((~((r1_tsep_1(X4,X2)&r1_tsep_1(X4,X3)))&r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)))))), inference(split_equiv,[status(thm)],[c_0_18])).
% 3.10/3.37  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|epred1_4(X3,X4,X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.10/3.37  cnf(c_0_52, plain, (k2_tsep_1(X1,X2,k1_tsep_1(X1,X3,X4))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X1)|~r1_tsep_1(X2,X4)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.10/3.37  cnf(c_0_53, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_54, plain, (v1_tsep_1(X1,X2)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|X3!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 3.10/3.37  cnf(c_0_55, negated_conjecture, (k1_tsep_1(esk4_0,esk2_0,esk2_0)=k1_tsep_1(esk1_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_40]), c_0_22]), c_0_24])]), c_0_34]), c_0_29]), c_0_45])).
% 3.10/3.37  cnf(c_0_56, negated_conjecture, (m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_34])).
% 3.10/3.37  cnf(c_0_57, negated_conjecture, (l1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_47]), c_0_22])])).
% 3.10/3.37  cnf(c_0_58, negated_conjecture, (~v2_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_40]), c_0_27]), c_0_22])]), c_0_34]), c_0_28]), c_0_29])).
% 3.10/3.37  cnf(c_0_59, negated_conjecture, (v2_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_47]), c_0_22]), c_0_24])])).
% 3.10/3.37  cnf(c_0_60, negated_conjecture, (~v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))|~m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  fof(c_0_61, plain, ![X48, X49, X50, X51]:((((r1_tsep_1(k1_tsep_1(X48,X49,X51),X50)|~r1_tsep_1(X49,X50)|~r1_tsep_1(X51,X50)|~epred1_4(X51,X50,X49,X48))&((r1_tsep_1(X49,X50)|~r1_tsep_1(k1_tsep_1(X48,X49,X51),X50)|~epred1_4(X51,X50,X49,X48))&(r1_tsep_1(X51,X50)|~r1_tsep_1(k1_tsep_1(X48,X49,X51),X50)|~epred1_4(X51,X50,X49,X48))))&(r1_tsep_1(X50,k1_tsep_1(X48,X49,X51))|~r1_tsep_1(X50,X49)|~r1_tsep_1(X50,X51)|~epred1_4(X51,X50,X49,X48)))&((r1_tsep_1(X50,X49)|~r1_tsep_1(X50,k1_tsep_1(X48,X49,X51))|~epred1_4(X51,X50,X49,X48))&(r1_tsep_1(X50,X51)|~r1_tsep_1(X50,k1_tsep_1(X48,X49,X51))|~epred1_4(X51,X50,X49,X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_50])])])])).
% 3.10/3.37  cnf(c_0_62, negated_conjecture, (epred1_4(X1,esk4_0,X2,esk1_0)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_21]), c_0_22]), c_0_24])]), c_0_35]), c_0_29])).
% 3.10/3.37  fof(c_0_63, plain, ![X41, X42, X43]:((v1_tsep_1(k2_tsep_1(X41,X43,X42),X42)|r1_tsep_1(X43,X42)|(v2_struct_0(X43)|~v1_tsep_1(X43,X41)|~m1_pre_topc(X43,X41))|(v2_struct_0(X42)|~m1_pre_topc(X42,X41))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(m1_pre_topc(k2_tsep_1(X41,X43,X42),X42)|r1_tsep_1(X43,X42)|(v2_struct_0(X43)|~v1_tsep_1(X43,X41)|~m1_pre_topc(X43,X41))|(v2_struct_0(X42)|~m1_pre_topc(X42,X41))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_tmap_1])])])])])).
% 3.10/3.37  cnf(c_0_64, negated_conjecture, (k2_tsep_1(X1,esk4_0,k1_tsep_1(X1,X2,esk3_0))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_28]), c_0_35])).
% 3.10/3.37  cnf(c_0_65, plain, (v1_tsep_1(X1,X2)|~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_54, c_0_23]), c_0_20])])).
% 3.10/3.37  cnf(c_0_66, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k1_tsep_1(esk1_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_45, c_0_55])).
% 3.10/3.37  cnf(c_0_67, negated_conjecture, (l1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_40]), c_0_22])])).
% 3.10/3.37  cnf(c_0_68, negated_conjecture, (v2_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_40]), c_0_22]), c_0_24])])).
% 3.10/3.37  cnf(c_0_69, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),X1,esk2_0),k1_tsep_1(esk1_0,esk2_0,esk3_0))|~m1_pre_topc(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_56]), c_0_57])]), c_0_34]), c_0_58])).
% 3.10/3.37  cnf(c_0_70, negated_conjecture, (k1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0,esk2_0)=k1_tsep_1(esk1_0,esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_56]), c_0_57]), c_0_59])]), c_0_34]), c_0_45]), c_0_55]), c_0_58])).
% 3.10/3.37  cnf(c_0_71, negated_conjecture, (~v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))|~m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_56])])).
% 3.10/3.37  cnf(c_0_72, plain, (r1_tsep_1(X1,X2)|~r1_tsep_1(X1,k1_tsep_1(X3,X4,X2))|~epred1_4(X2,X1,X4,X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 3.10/3.37  cnf(c_0_73, negated_conjecture, (epred1_4(esk2_0,esk4_0,X1,esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_40]), c_0_34])).
% 3.10/3.37  cnf(c_0_74, plain, (v1_tsep_1(k2_tsep_1(X1,X2,X3),X3)|r1_tsep_1(X2,X3)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X1)|~v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 3.10/3.37  cnf(c_0_75, negated_conjecture, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,X1,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_27]), c_0_21]), c_0_22]), c_0_24])]), c_0_29])).
% 3.10/3.37  cnf(c_0_76, negated_conjecture, (v1_tsep_1(esk2_0,X1)|~v1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk2_0),X1)|~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk2_0),X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68])])).
% 3.10/3.37  cnf(c_0_77, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk2_0),k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_56]), c_0_70]), c_0_34])).
% 3.10/3.37  cnf(c_0_78, negated_conjecture, (~v1_tsep_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_49]), c_0_49]), c_0_56])])).
% 3.10/3.37  cnf(c_0_79, plain, (r1_tsep_1(X1,esk2_0)|~epred1_4(esk2_0,X1,esk3_0,esk1_0)|~r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_72, c_0_49])).
% 3.10/3.37  cnf(c_0_80, negated_conjecture, (epred1_4(esk2_0,esk4_0,esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_27]), c_0_28])).
% 3.10/3.37  cnf(c_0_81, negated_conjecture, (r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))|v1_tsep_1(k2_tsep_1(esk1_0,X1,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v1_tsep_1(X1,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_47]), c_0_22]), c_0_24])]), c_0_29]), c_0_58])).
% 3.10/3.37  cnf(c_0_82, negated_conjecture, (v1_tsep_1(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.10/3.37  cnf(c_0_83, negated_conjecture, (k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))=k1_tsep_1(esk1_0,esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_33]), c_0_45]), c_0_55]), c_0_40])]), c_0_34])).
% 3.10/3.37  cnf(c_0_84, negated_conjecture, (~v1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk2_0),k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_57]), c_0_59])]), c_0_78])).
% 3.10/3.37  fof(c_0_85, plain, ![X21, X22, X23]:((~r1_tsep_1(X22,X23)|~m1_pre_topc(X22,X23)|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~m1_pre_topc(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~r1_tsep_1(X23,X22)|~m1_pre_topc(X22,X23)|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~m1_pre_topc(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).
% 3.10/3.37  cnf(c_0_86, plain, (r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 3.10/3.37  cnf(c_0_87, negated_conjecture, (r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_21]), c_0_82])]), c_0_35]), c_0_83]), c_0_84])).
% 3.10/3.37  cnf(c_0_88, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 3.10/3.37  cnf(c_0_89, plain, (r1_tsep_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 3.10/3.37  cnf(c_0_90, plain, (v2_struct_0(X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_33])]), c_0_34]), c_0_35])).
% 3.10/3.37  cnf(c_0_91, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_40]), c_0_21]), c_0_22]), c_0_24])]), c_0_29]), ['proof']).
% 3.10/3.37  # SZS output end CNFRefutation
% 3.10/3.37  # Proof object total steps             : 92
% 3.10/3.37  # Proof object clause steps            : 63
% 3.10/3.37  # Proof object formula steps           : 29
% 3.10/3.37  # Proof object conjectures             : 48
% 3.10/3.37  # Proof object clause conjectures      : 45
% 3.10/3.37  # Proof object formula conjectures     : 3
% 3.10/3.37  # Proof object initial clauses used    : 26
% 3.10/3.37  # Proof object initial formulas used   : 12
% 3.10/3.37  # Proof object generating inferences   : 32
% 3.10/3.37  # Proof object simplifying inferences  : 119
% 3.10/3.37  # Training examples: 0 positive, 0 negative
% 3.10/3.37  # Parsed axioms                        : 14
% 3.10/3.37  # Removed by relevancy pruning/SinE    : 0
% 3.10/3.37  # Initial clauses                      : 44
% 3.10/3.37  # Removed in clause preprocessing      : 0
% 3.10/3.37  # Initial clauses in saturation        : 44
% 3.10/3.37  # Processed clauses                    : 12659
% 3.10/3.37  # ...of these trivial                  : 193
% 3.10/3.37  # ...subsumed                          : 1032
% 3.10/3.37  # ...remaining for further processing  : 11434
% 3.10/3.37  # Other redundant clauses eliminated   : 4
% 3.10/3.37  # Clauses deleted for lack of memory   : 0
% 3.10/3.37  # Backward-subsumed                    : 2
% 3.10/3.37  # Backward-rewritten                   : 1330
% 3.10/3.37  # Generated clauses                    : 252730
% 3.10/3.37  # ...of the previous two non-trivial   : 251431
% 3.10/3.37  # Contextual simplify-reflections      : 413
% 3.10/3.37  # Paramodulations                      : 252726
% 3.10/3.37  # Factorizations                       : 0
% 3.10/3.37  # Equation resolutions                 : 4
% 3.10/3.37  # Propositional unsat checks           : 0
% 3.10/3.37  #    Propositional check models        : 0
% 3.10/3.37  #    Propositional check unsatisfiable : 0
% 3.10/3.37  #    Propositional clauses             : 0
% 3.10/3.37  #    Propositional clauses after purity: 0
% 3.10/3.37  #    Propositional unsat core size     : 0
% 3.10/3.37  #    Propositional preprocessing time  : 0.000
% 3.10/3.37  #    Propositional encoding time       : 0.000
% 3.10/3.37  #    Propositional solver time         : 0.000
% 3.10/3.37  #    Success case prop preproc time    : 0.000
% 3.10/3.37  #    Success case prop encoding time   : 0.000
% 3.10/3.37  #    Success case prop solver time     : 0.000
% 3.10/3.37  # Current number of processed clauses  : 10056
% 3.10/3.37  #    Positive orientable unit clauses  : 4253
% 3.10/3.37  #    Positive unorientable unit clauses: 0
% 3.10/3.37  #    Negative unit clauses             : 197
% 3.10/3.37  #    Non-unit-clauses                  : 5606
% 3.10/3.37  # Current number of unprocessed clauses: 237873
% 3.10/3.37  # ...number of literals in the above   : 509130
% 3.10/3.37  # Current number of archived formulas  : 0
% 3.10/3.37  # Current number of archived clauses   : 1374
% 3.10/3.37  # Clause-clause subsumption calls (NU) : 3809949
% 3.10/3.37  # Rec. Clause-clause subsumption calls : 3341590
% 3.10/3.37  # Non-unit clause-clause subsumptions  : 1416
% 3.10/3.37  # Unit Clause-clause subsumption calls : 2857389
% 3.10/3.37  # Rewrite failures with RHS unbound    : 0
% 3.10/3.37  # BW rewrite match attempts            : 299365
% 3.10/3.37  # BW rewrite match successes           : 197
% 3.10/3.37  # Condensation attempts                : 0
% 3.10/3.37  # Condensation successes               : 0
% 3.10/3.37  # Termbank termtop insertions          : 10671813
% 3.21/3.38  
% 3.21/3.38  # -------------------------------------------------
% 3.21/3.38  # User time                : 2.918 s
% 3.21/3.38  # System time              : 0.127 s
% 3.21/3.38  # Total time               : 3.045 s
% 3.21/3.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
