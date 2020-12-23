%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:06 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 621 expanded)
%              Number of clauses        :   58 ( 208 expanded)
%              Number of leaves         :   11 ( 154 expanded)
%              Depth                    :   12
%              Number of atoms          :  329 (5427 expanded)
%              Number of equality atoms :   36 ( 100 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_tmap_1,conjecture,(
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X3) )
                   => m1_pre_topc(k1_tsep_1(X1,X2,X4),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).

fof(t25_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(d2_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_pre_topc(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( X4 = k1_tsep_1(X1,X2,X3)
                  <=> u1_struct_0(X4) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(commutativity_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(c_0_11,negated_conjecture,(
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
                      & m1_pre_topc(X4,X1) )
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X4,X3) )
                     => m1_pre_topc(k1_tsep_1(X1,X2,X4),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tmap_1])).

fof(c_0_12,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X28,X27)
      | k1_tsep_1(X27,X28,X28) = g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & m1_pre_topc(esk2_0,esk3_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | l1_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
    ! [X29,X30,X31] :
      ( ( ~ r1_tarski(u1_struct_0(X30),u1_struct_0(X31))
        | m1_pre_topc(X30,X31)
        | ~ m1_pre_topc(X31,X29)
        | ~ m1_pre_topc(X30,X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ m1_pre_topc(X30,X31)
        | r1_tarski(u1_struct_0(X30),u1_struct_0(X31))
        | ~ m1_pre_topc(X31,X29)
        | ~ m1_pre_topc(X30,X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

fof(c_0_17,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X20 != k1_tsep_1(X17,X18,X19)
        | u1_struct_0(X20) = k2_xboole_0(u1_struct_0(X18),u1_struct_0(X19))
        | v2_struct_0(X20)
        | ~ v1_pre_topc(X20)
        | ~ m1_pre_topc(X20,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17) )
      & ( u1_struct_0(X20) != k2_xboole_0(u1_struct_0(X18),u1_struct_0(X19))
        | X20 = k1_tsep_1(X17,X18,X19)
        | v2_struct_0(X20)
        | ~ v1_pre_topc(X20)
        | ~ m1_pre_topc(X20,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

fof(c_0_18,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v2_struct_0(k1_tsep_1(X21,X22,X23))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21) )
      & ( v1_pre_topc(k1_tsep_1(X21,X22,X23))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21) )
      & ( m1_pre_topc(k1_tsep_1(X21,X22,X23),X21)
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_19,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))
      | m1_pre_topc(X13,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_29,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | k1_tsep_1(X14,X15,X16) = k1_tsep_1(X14,X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

cnf(c_0_30,plain,
    ( u1_struct_0(X1) = k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k1_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k1_tsep_1(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_23])])).

cnf(c_0_37,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(X1,k1_tsep_1(esk1_0,X1,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25])).

fof(c_0_38,plain,(
    ! [X5,X6] :
      ( ~ r1_tarski(X5,X6)
      | k2_xboole_0(X5,X6) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk3_0,k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_24])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_49,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk3_0) = k1_tsep_1(esk1_0,esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0)) = u1_struct_0(k1_tsep_1(esk3_0,X1,esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_36])]),c_0_24]),c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_21]),c_0_23])]),c_0_25]),c_0_24])).

cnf(c_0_55,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) = u1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk2_0,esk3_0) = k1_tsep_1(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0)) = u1_struct_0(k1_tsep_1(esk3_0,X1,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_50]),c_0_36])]),c_0_24]),c_0_51])).

fof(c_0_59,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(k2_xboole_0(X7,X9),k2_xboole_0(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

cnf(c_0_60,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_23])]),c_0_25]),c_0_44])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) = u1_struct_0(k1_tsep_1(esk3_0,esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk2_0)) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_40]),c_0_44]),c_0_55]),c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k1_tsep_1(esk3_0,X1,esk4_0) = k1_tsep_1(esk3_0,esk4_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_50]),c_0_36])]),c_0_51]),c_0_24])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_57]),c_0_23])]),c_0_25]),c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) = u1_struct_0(k1_tsep_1(esk3_0,esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_44])).

cnf(c_0_66,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_57]),c_0_50])])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk3_0,esk3_0,esk2_0)) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_21]),c_0_24]),c_0_61]),c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( k1_tsep_1(esk3_0,esk4_0,esk2_0) = k1_tsep_1(esk3_0,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_41]),c_0_44])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk3_0,esk2_0,esk4_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_40]),c_0_44]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k2_xboole_0(u1_struct_0(esk4_0),X1),k2_xboole_0(u1_struct_0(esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_50]),c_0_51]),c_0_69]),c_0_70])).

cnf(c_0_74,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_77,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_57]),c_0_23])]),c_0_51]),c_0_25])).

cnf(c_0_78,negated_conjecture,
    ( ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_40]),c_0_44])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_22]),c_0_21]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.63  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.47/0.63  # and selection function SelectComplexG.
% 0.47/0.63  #
% 0.47/0.63  # Preprocessing time       : 0.028 s
% 0.47/0.63  # Presaturation interreduction done
% 0.47/0.63  
% 0.47/0.63  # Proof found!
% 0.47/0.63  # SZS status Theorem
% 0.47/0.63  # SZS output start CNFRefutation
% 0.47/0.63  fof(t29_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X3))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tmap_1)).
% 0.47/0.63  fof(t25_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 0.47/0.63  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.47/0.63  fof(t22_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 0.47/0.63  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.47/0.63  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 0.47/0.63  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.47/0.63  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.47/0.63  fof(commutativity_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>k1_tsep_1(X1,X2,X3)=k1_tsep_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k1_tsep_1)).
% 0.47/0.63  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.47/0.63  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 0.47/0.63  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X3))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),X3))))))), inference(assume_negation,[status(cth)],[t29_tmap_1])).
% 0.47/0.63  fof(c_0_12, plain, ![X27, X28]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(v2_struct_0(X28)|~m1_pre_topc(X28,X27)|k1_tsep_1(X27,X28,X28)=g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).
% 0.47/0.63  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((m1_pre_topc(esk2_0,esk3_0)&m1_pre_topc(esk4_0,esk3_0))&~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.47/0.63  fof(c_0_14, plain, ![X10, X11]:(~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|l1_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.47/0.63  fof(c_0_15, plain, ![X24, X25, X26]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X24)|(v2_struct_0(X26)|~m1_pre_topc(X26,X24)|m1_pre_topc(X25,k1_tsep_1(X24,X25,X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).
% 0.47/0.63  fof(c_0_16, plain, ![X29, X30, X31]:((~r1_tarski(u1_struct_0(X30),u1_struct_0(X31))|m1_pre_topc(X30,X31)|~m1_pre_topc(X31,X29)|~m1_pre_topc(X30,X29)|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(~m1_pre_topc(X30,X31)|r1_tarski(u1_struct_0(X30),u1_struct_0(X31))|~m1_pre_topc(X31,X29)|~m1_pre_topc(X30,X29)|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.47/0.63  fof(c_0_17, plain, ![X17, X18, X19, X20]:((X20!=k1_tsep_1(X17,X18,X19)|u1_struct_0(X20)=k2_xboole_0(u1_struct_0(X18),u1_struct_0(X19))|(v2_struct_0(X20)|~v1_pre_topc(X20)|~m1_pre_topc(X20,X17))|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~l1_pre_topc(X17)))&(u1_struct_0(X20)!=k2_xboole_0(u1_struct_0(X18),u1_struct_0(X19))|X20=k1_tsep_1(X17,X18,X19)|(v2_struct_0(X20)|~v1_pre_topc(X20)|~m1_pre_topc(X20,X17))|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 0.47/0.63  fof(c_0_18, plain, ![X21, X22, X23]:(((~v2_struct_0(k1_tsep_1(X21,X22,X23))|(v2_struct_0(X21)|~l1_pre_topc(X21)|v2_struct_0(X22)|~m1_pre_topc(X22,X21)|v2_struct_0(X23)|~m1_pre_topc(X23,X21)))&(v1_pre_topc(k1_tsep_1(X21,X22,X23))|(v2_struct_0(X21)|~l1_pre_topc(X21)|v2_struct_0(X22)|~m1_pre_topc(X22,X21)|v2_struct_0(X23)|~m1_pre_topc(X23,X21))))&(m1_pre_topc(k1_tsep_1(X21,X22,X23),X21)|(v2_struct_0(X21)|~l1_pre_topc(X21)|v2_struct_0(X22)|~m1_pre_topc(X22,X21)|v2_struct_0(X23)|~m1_pre_topc(X23,X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.47/0.63  fof(c_0_19, plain, ![X12, X13]:(~l1_pre_topc(X12)|(~m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))|m1_pre_topc(X13,X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.47/0.64  cnf(c_0_20, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_26, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.64  cnf(c_0_27, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.64  cnf(c_0_28, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.64  fof(c_0_29, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~l1_pre_topc(X14)|v2_struct_0(X15)|~m1_pre_topc(X15,X14)|v2_struct_0(X16)|~m1_pre_topc(X16,X14)|k1_tsep_1(X14,X15,X16)=k1_tsep_1(X14,X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).
% 0.47/0.64  cnf(c_0_30, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.64  cnf(c_0_31, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.64  cnf(c_0_32, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.64  cnf(c_0_33, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.64  cnf(c_0_34, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.64  cnf(c_0_35, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k1_tsep_1(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24]), c_0_25])).
% 0.47/0.64  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_21]), c_0_23])])).
% 0.47/0.64  cnf(c_0_37, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(X1,k1_tsep_1(esk1_0,X1,esk3_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_22]), c_0_23])]), c_0_24]), c_0_25])).
% 0.47/0.64  fof(c_0_38, plain, ![X5, X6]:(~r1_tarski(X5,X6)|k2_xboole_0(X5,X6)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.47/0.64  cnf(c_0_39, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_21]), c_0_22]), c_0_23])])).
% 0.47/0.64  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|k1_tsep_1(X1,X2,X3)=k1_tsep_1(X1,X3,X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.64  cnf(c_0_43, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.47/0.64  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_45, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.47/0.64  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk3_0,k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_24])).
% 0.47/0.64  cnf(c_0_47, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.64  cnf(c_0_48, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.47/0.64  cnf(c_0_49, negated_conjecture, (k1_tsep_1(esk1_0,X1,esk3_0)=k1_tsep_1(esk1_0,esk3_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_21]), c_0_23])]), c_0_24]), c_0_25])).
% 0.47/0.64  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_52, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))=u1_struct_0(k1_tsep_1(esk3_0,X1,esk2_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_41]), c_0_36])]), c_0_24]), c_0_44])).
% 0.47/0.64  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.47/0.64  cnf(c_0_54, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_21]), c_0_23])]), c_0_25]), c_0_24])).
% 0.47/0.64  cnf(c_0_55, negated_conjecture, (k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))=u1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.47/0.64  cnf(c_0_56, negated_conjecture, (k1_tsep_1(esk1_0,esk2_0,esk3_0)=k1_tsep_1(esk1_0,esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_44])).
% 0.47/0.64  cnf(c_0_57, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_58, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))=u1_struct_0(k1_tsep_1(esk3_0,X1,esk4_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_50]), c_0_36])]), c_0_24]), c_0_51])).
% 0.47/0.64  fof(c_0_59, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|r1_tarski(k2_xboole_0(X7,X9),k2_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 0.47/0.64  cnf(c_0_60, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))=u1_struct_0(k1_tsep_1(esk1_0,X1,esk2_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_23])]), c_0_25]), c_0_44])).
% 0.47/0.64  cnf(c_0_61, negated_conjecture, (k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))=u1_struct_0(k1_tsep_1(esk3_0,esk3_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_24])).
% 0.47/0.64  cnf(c_0_62, negated_conjecture, (u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk2_0))=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_40]), c_0_44]), c_0_55]), c_0_56])).
% 0.47/0.64  cnf(c_0_63, negated_conjecture, (k1_tsep_1(esk3_0,X1,esk4_0)=k1_tsep_1(esk3_0,esk4_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_50]), c_0_36])]), c_0_51]), c_0_24])).
% 0.47/0.64  cnf(c_0_64, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))=u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_57]), c_0_23])]), c_0_25]), c_0_51])).
% 0.47/0.64  cnf(c_0_65, negated_conjecture, (k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))=u1_struct_0(k1_tsep_1(esk3_0,esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_44])).
% 0.47/0.64  cnf(c_0_66, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.47/0.64  cnf(c_0_67, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_57]), c_0_50])])).
% 0.47/0.64  cnf(c_0_68, negated_conjecture, (u1_struct_0(k1_tsep_1(esk3_0,esk3_0,esk2_0))=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_21]), c_0_24]), c_0_61]), c_0_62])).
% 0.47/0.64  cnf(c_0_69, negated_conjecture, (k1_tsep_1(esk3_0,esk4_0,esk2_0)=k1_tsep_1(esk3_0,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_41]), c_0_44])).
% 0.47/0.64  cnf(c_0_70, negated_conjecture, (u1_struct_0(k1_tsep_1(esk3_0,esk2_0,esk4_0))=u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_40]), c_0_44]), c_0_65])).
% 0.47/0.64  cnf(c_0_71, negated_conjecture, (r1_tarski(k2_xboole_0(u1_struct_0(esk4_0),X1),k2_xboole_0(u1_struct_0(esk3_0),X1))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.47/0.64  cnf(c_0_72, negated_conjecture, (k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[c_0_61, c_0_68])).
% 0.47/0.64  cnf(c_0_73, negated_conjecture, (k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))=u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_50]), c_0_51]), c_0_69]), c_0_70])).
% 0.47/0.64  cnf(c_0_74, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.64  cnf(c_0_75, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)),u1_struct_0(esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 0.47/0.64  cnf(c_0_76, negated_conjecture, (~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_77, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_57]), c_0_23])]), c_0_51]), c_0_25])).
% 0.47/0.64  cnf(c_0_78, negated_conjecture, (~v2_pre_topc(X1)|~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.47/0.64  cnf(c_0_79, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_40]), c_0_44])).
% 0.47/0.64  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_22]), c_0_21]), c_0_23])]), ['proof']).
% 0.47/0.64  # SZS output end CNFRefutation
% 0.47/0.64  # Proof object total steps             : 81
% 0.47/0.64  # Proof object clause steps            : 58
% 0.47/0.64  # Proof object formula steps           : 23
% 0.47/0.64  # Proof object conjectures             : 47
% 0.47/0.64  # Proof object clause conjectures      : 44
% 0.47/0.64  # Proof object formula conjectures     : 3
% 0.47/0.64  # Proof object initial clauses used    : 25
% 0.47/0.64  # Proof object initial formulas used   : 11
% 0.47/0.64  # Proof object generating inferences   : 31
% 0.47/0.64  # Proof object simplifying inferences  : 81
% 0.47/0.64  # Training examples: 0 positive, 0 negative
% 0.47/0.64  # Parsed axioms                        : 11
% 0.47/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.64  # Initial clauses                      : 26
% 0.47/0.64  # Removed in clause preprocessing      : 0
% 0.47/0.64  # Initial clauses in saturation        : 26
% 0.47/0.64  # Processed clauses                    : 2198
% 0.47/0.64  # ...of these trivial                  : 102
% 0.47/0.64  # ...subsumed                          : 244
% 0.47/0.64  # ...remaining for further processing  : 1852
% 0.47/0.64  # Other redundant clauses eliminated   : 1
% 0.47/0.64  # Clauses deleted for lack of memory   : 0
% 0.47/0.64  # Backward-subsumed                    : 8
% 0.47/0.64  # Backward-rewritten                   : 848
% 0.47/0.64  # Generated clauses                    : 18371
% 0.47/0.64  # ...of the previous two non-trivial   : 18358
% 0.47/0.64  # Contextual simplify-reflections      : 9
% 0.47/0.64  # Paramodulations                      : 18370
% 0.47/0.64  # Factorizations                       : 0
% 0.47/0.64  # Equation resolutions                 : 1
% 0.47/0.64  # Propositional unsat checks           : 0
% 0.47/0.64  #    Propositional check models        : 0
% 0.47/0.64  #    Propositional check unsatisfiable : 0
% 0.47/0.64  #    Propositional clauses             : 0
% 0.47/0.64  #    Propositional clauses after purity: 0
% 0.47/0.64  #    Propositional unsat core size     : 0
% 0.47/0.64  #    Propositional preprocessing time  : 0.000
% 0.47/0.64  #    Propositional encoding time       : 0.000
% 0.47/0.64  #    Propositional solver time         : 0.000
% 0.47/0.64  #    Success case prop preproc time    : 0.000
% 0.47/0.64  #    Success case prop encoding time   : 0.000
% 0.47/0.64  #    Success case prop solver time     : 0.000
% 0.47/0.64  # Current number of processed clauses  : 969
% 0.47/0.64  #    Positive orientable unit clauses  : 578
% 0.47/0.64  #    Positive unorientable unit clauses: 0
% 0.47/0.64  #    Negative unit clauses             : 25
% 0.47/0.64  #    Non-unit-clauses                  : 366
% 0.47/0.64  # Current number of unprocessed clauses: 15262
% 0.47/0.64  # ...number of literals in the above   : 37822
% 0.47/0.64  # Current number of archived formulas  : 0
% 0.47/0.64  # Current number of archived clauses   : 882
% 0.47/0.64  # Clause-clause subsumption calls (NU) : 21615
% 0.47/0.64  # Rec. Clause-clause subsumption calls : 14030
% 0.47/0.64  # Non-unit clause-clause subsumptions  : 210
% 0.47/0.64  # Unit Clause-clause subsumption calls : 10752
% 0.47/0.64  # Rewrite failures with RHS unbound    : 0
% 0.47/0.64  # BW rewrite match attempts            : 10914
% 0.47/0.64  # BW rewrite match successes           : 132
% 0.47/0.64  # Condensation attempts                : 0
% 0.47/0.64  # Condensation successes               : 0
% 0.47/0.64  # Termbank termtop insertions          : 670276
% 0.47/0.64  
% 0.47/0.64  # -------------------------------------------------
% 0.47/0.64  # User time                : 0.285 s
% 0.47/0.64  # System time              : 0.013 s
% 0.47/0.64  # Total time               : 0.298 s
% 0.47/0.64  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
