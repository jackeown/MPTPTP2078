%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:05 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   95 (2134 expanded)
%              Number of clauses        :   76 ( 685 expanded)
%              Number of leaves         :    9 ( 520 expanded)
%              Depth                    :   19
%              Number of atoms          :  378 (21439 expanded)
%              Number of equality atoms :   45 ( 236 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_tmap_1,conjecture,(
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
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X4,X5) )
                       => m1_pre_topc(k1_tsep_1(X1,X2,X4),k1_tsep_1(X1,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(t23_tsep_1,axiom,(
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
              <=> k1_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_9,negated_conjecture,(
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
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X4,X5) )
                         => m1_pre_topc(k1_tsep_1(X1,X2,X4),k1_tsep_1(X1,X3,X5)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_tmap_1])).

fof(c_0_10,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X13)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X14,X12)
      | k1_tsep_1(X12,X13,X14) = k1_tsep_1(X12,X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & m1_pre_topc(esk2_0,esk3_0)
    & m1_pre_topc(esk4_0,esk5_0)
    & ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v2_struct_0(k1_tsep_1(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19) )
      & ( v1_pre_topc(k1_tsep_1(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19) )
      & ( m1_pre_topc(k1_tsep_1(X19,X20,X21),X19)
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk5_0) = k1_tsep_1(esk1_0,esk5_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ m1_pre_topc(X26,X25)
      | k1_tsep_1(X25,X26,X26) = g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk5_0,esk3_0) = k1_tsep_1(esk1_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_26,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X18 != k1_tsep_1(X15,X16,X17)
        | u1_struct_0(X18) = k2_xboole_0(u1_struct_0(X16),u1_struct_0(X17))
        | v2_struct_0(X18)
        | ~ v1_pre_topc(X18)
        | ~ m1_pre_topc(X18,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15) )
      & ( u1_struct_0(X18) != k2_xboole_0(u1_struct_0(X16),u1_struct_0(X17))
        | X18 = k1_tsep_1(X15,X16,X17)
        | v2_struct_0(X18)
        | ~ v1_pre_topc(X18)
        | ~ m1_pre_topc(X18,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

fof(c_0_27,plain,(
    ! [X22,X23,X24] :
      ( ( ~ m1_pre_topc(X23,X24)
        | k1_tsep_1(X22,X23,X24) = g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( k1_tsep_1(X22,X23,X24) != g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))
        | m1_pre_topc(X23,X24)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tsep_1])])])])])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20]),c_0_14]),c_0_15])]),c_0_21]),c_0_16]),c_0_17])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( m1_pre_topc(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | k1_tsep_1(X1,X2,X3) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)),u1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk5_0))) = k1_tsep_1(esk1_0,k1_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_15])]),c_0_17]),c_0_31])).

cnf(c_0_36,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_18]),c_0_33]),c_0_24])).

fof(c_0_37,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_tarski(u1_struct_0(X28),u1_struct_0(X29))
        | m1_pre_topc(X28,X29)
        | ~ m1_pre_topc(X29,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ m1_pre_topc(X28,X29)
        | r1_tarski(u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_pre_topc(X29,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk5_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | k1_tsep_1(X2,X1,k1_tsep_1(esk1_0,esk3_0,esk5_0)) != k1_tsep_1(esk1_0,k1_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk5_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_31])).

fof(c_0_39,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_14]),c_0_15])]),c_0_17]),c_0_16])).

cnf(c_0_41,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk5_0))
    | v2_struct_0(X1)
    | k1_tsep_1(esk1_0,X1,k1_tsep_1(esk1_0,esk3_0,esk5_0)) != k1_tsep_1(esk1_0,k1_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_30]),c_0_15])]),c_0_17])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk5_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_20]),c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_30]),c_0_15])])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_42]),c_0_29])]),c_0_31])).

cnf(c_0_47,plain,
    ( k1_tsep_1(X3,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k1_tsep_1(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_30]),c_0_15])]),c_0_21]),c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_20]),c_0_15])]),c_0_17]),c_0_21])).

fof(c_0_50,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X11,X10)
      | r1_tarski(k2_xboole_0(X9,X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),X1)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_29])])).

cnf(c_0_53,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk3_0) = k1_tsep_1(esk1_0,esk3_0,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_20]),c_0_30]),c_0_15])]),c_0_17]),c_0_21]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_14]),c_0_16]),c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = k1_tsep_1(esk1_0,esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_14]),c_0_30]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_20]),c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk3_0,esk3_0) = k1_tsep_1(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk5_0),X1)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk5_0) = k1_tsep_1(esk1_0,esk5_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_14]),c_0_58]),c_0_30]),c_0_15])]),c_0_17]),c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_67,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_54]),c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,u1_struct_0(esk3_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))
    | ~ r1_tarski(X1,u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk5_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_52])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_14]),c_0_16])).

cnf(c_0_73,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk5_0,esk5_0) = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])]),c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),X1)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_60]),c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_65]),c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,u1_struct_0(esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))
    | ~ r1_tarski(X1,u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk4_0) = k1_tsep_1(esk1_0,esk4_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_65]),c_0_15])]),c_0_67]),c_0_17])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),X1)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_71]),c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_54]),c_0_15])]),c_0_17]),c_0_56])).

cnf(c_0_84,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk4_0,esk2_0) = k1_tsep_1(esk1_0,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_54]),c_0_56])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,u1_struct_0(esk2_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))
    | ~ r1_tarski(X1,u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_65]),c_0_67]),c_0_84])).

cnf(c_0_88,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_91,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_65]),c_0_15])]),c_0_67]),c_0_17])).

cnf(c_0_92,negated_conjecture,
    ( ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk5_0),X1)
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_54]),c_0_56])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_29]),c_0_30]),c_0_93]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:52:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 2.68/2.86  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 2.68/2.86  # and selection function SelectComplexG.
% 2.68/2.86  #
% 2.68/2.86  # Preprocessing time       : 0.028 s
% 2.68/2.86  # Presaturation interreduction done
% 2.68/2.86  
% 2.68/2.86  # Proof found!
% 2.68/2.86  # SZS status Theorem
% 2.68/2.86  # SZS output start CNFRefutation
% 2.68/2.86  fof(t27_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X5))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),k1_tsep_1(X1,X3,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tmap_1)).
% 2.68/2.86  fof(commutativity_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>k1_tsep_1(X1,X2,X3)=k1_tsep_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k1_tsep_1)).
% 2.68/2.86  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 2.68/2.86  fof(t25_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 2.68/2.86  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 2.68/2.86  fof(t23_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(m1_pre_topc(X2,X3)<=>k1_tsep_1(X1,X2,X3)=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 2.68/2.86  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.68/2.86  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.68/2.86  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.68/2.86  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X5))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),k1_tsep_1(X1,X3,X5))))))))), inference(assume_negation,[status(cth)],[t27_tmap_1])).
% 2.68/2.86  fof(c_0_10, plain, ![X12, X13, X14]:(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12)|k1_tsep_1(X12,X13,X14)=k1_tsep_1(X12,X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).
% 2.68/2.86  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((m1_pre_topc(esk2_0,esk3_0)&m1_pre_topc(esk4_0,esk5_0))&~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk5_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 2.68/2.86  fof(c_0_12, plain, ![X19, X20, X21]:(((~v2_struct_0(k1_tsep_1(X19,X20,X21))|(v2_struct_0(X19)|~l1_pre_topc(X19)|v2_struct_0(X20)|~m1_pre_topc(X20,X19)|v2_struct_0(X21)|~m1_pre_topc(X21,X19)))&(v1_pre_topc(k1_tsep_1(X19,X20,X21))|(v2_struct_0(X19)|~l1_pre_topc(X19)|v2_struct_0(X20)|~m1_pre_topc(X20,X19)|v2_struct_0(X21)|~m1_pre_topc(X21,X19))))&(m1_pre_topc(k1_tsep_1(X19,X20,X21),X19)|(v2_struct_0(X19)|~l1_pre_topc(X19)|v2_struct_0(X20)|~m1_pre_topc(X20,X19)|v2_struct_0(X21)|~m1_pre_topc(X21,X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 2.68/2.86  cnf(c_0_13, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|k1_tsep_1(X1,X2,X3)=k1_tsep_1(X1,X3,X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.68/2.86  cnf(c_0_14, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_18, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.68/2.86  cnf(c_0_19, negated_conjecture, (k1_tsep_1(esk1_0,X1,esk5_0)=k1_tsep_1(esk1_0,esk5_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 2.68/2.86  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  fof(c_0_22, plain, ![X25, X26]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~m1_pre_topc(X26,X25)|k1_tsep_1(X25,X26,X26)=g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).
% 2.68/2.86  cnf(c_0_23, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 2.68/2.86  cnf(c_0_24, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.68/2.86  cnf(c_0_25, negated_conjecture, (k1_tsep_1(esk1_0,esk5_0,esk3_0)=k1_tsep_1(esk1_0,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 2.68/2.86  fof(c_0_26, plain, ![X15, X16, X17, X18]:((X18!=k1_tsep_1(X15,X16,X17)|u1_struct_0(X18)=k2_xboole_0(u1_struct_0(X16),u1_struct_0(X17))|(v2_struct_0(X18)|~v1_pre_topc(X18)|~m1_pre_topc(X18,X15))|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~l1_pre_topc(X15)))&(u1_struct_0(X18)!=k2_xboole_0(u1_struct_0(X16),u1_struct_0(X17))|X18=k1_tsep_1(X15,X16,X17)|(v2_struct_0(X18)|~v1_pre_topc(X18)|~m1_pre_topc(X18,X15))|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 2.68/2.86  fof(c_0_27, plain, ![X22, X23, X24]:((~m1_pre_topc(X23,X24)|k1_tsep_1(X22,X23,X24)=g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))|(v2_struct_0(X24)|~m1_pre_topc(X24,X22))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(k1_tsep_1(X22,X23,X24)!=g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))|m1_pre_topc(X23,X24)|(v2_struct_0(X24)|~m1_pre_topc(X24,X22))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tsep_1])])])])])).
% 2.68/2.86  cnf(c_0_28, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.68/2.86  cnf(c_0_29, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_21])).
% 2.68/2.86  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_31, negated_conjecture, (~v2_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_20]), c_0_14]), c_0_15])]), c_0_21]), c_0_16]), c_0_17])).
% 2.68/2.86  cnf(c_0_32, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.68/2.86  cnf(c_0_33, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.68/2.86  cnf(c_0_34, plain, (m1_pre_topc(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|k1_tsep_1(X1,X2,X3)!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.68/2.86  cnf(c_0_35, negated_conjecture, (g1_pre_topc(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)),u1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk5_0)))=k1_tsep_1(esk1_0,k1_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_15])]), c_0_17]), c_0_31])).
% 2.68/2.86  cnf(c_0_36, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_18]), c_0_33]), c_0_24])).
% 2.68/2.86  fof(c_0_37, plain, ![X27, X28, X29]:((~r1_tarski(u1_struct_0(X28),u1_struct_0(X29))|m1_pre_topc(X28,X29)|~m1_pre_topc(X29,X27)|~m1_pre_topc(X28,X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~m1_pre_topc(X28,X29)|r1_tarski(u1_struct_0(X28),u1_struct_0(X29))|~m1_pre_topc(X29,X27)|~m1_pre_topc(X28,X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 2.68/2.86  cnf(c_0_38, negated_conjecture, (m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk5_0))|v2_struct_0(X2)|v2_struct_0(X1)|k1_tsep_1(X2,X1,k1_tsep_1(esk1_0,esk3_0,esk5_0))!=k1_tsep_1(esk1_0,k1_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk3_0,esk5_0))|~v2_pre_topc(X2)|~m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk5_0),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_31])).
% 2.68/2.86  fof(c_0_39, plain, ![X6, X7, X8]:(~r1_tarski(k2_xboole_0(X6,X7),X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 2.68/2.86  cnf(c_0_40, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0))=u1_struct_0(k1_tsep_1(esk1_0,X1,esk5_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_14]), c_0_15])]), c_0_17]), c_0_16])).
% 2.68/2.86  cnf(c_0_41, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.68/2.86  cnf(c_0_42, negated_conjecture, (m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk5_0))|v2_struct_0(X1)|k1_tsep_1(esk1_0,X1,k1_tsep_1(esk1_0,esk3_0,esk5_0))!=k1_tsep_1(esk1_0,k1_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk3_0,esk5_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_29]), c_0_30]), c_0_15])]), c_0_17])).
% 2.68/2.86  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.68/2.86  cnf(c_0_44, negated_conjecture, (k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk5_0))=u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_20]), c_0_21])).
% 2.68/2.86  cnf(c_0_45, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))|~m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk5_0))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_30]), c_0_15])])).
% 2.68/2.86  cnf(c_0_46, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_42]), c_0_29])]), c_0_31])).
% 2.68/2.86  cnf(c_0_47, plain, (k1_tsep_1(X3,X1,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.68/2.86  cnf(c_0_48, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k1_tsep_1(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_30]), c_0_15])]), c_0_21]), c_0_17])).
% 2.68/2.86  cnf(c_0_49, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_20]), c_0_15])]), c_0_17]), c_0_21])).
% 2.68/2.86  fof(c_0_50, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X11,X10)|r1_tarski(k2_xboole_0(X9,X11),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 2.68/2.86  cnf(c_0_51, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),X1)|~r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 2.68/2.86  cnf(c_0_52, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_29])])).
% 2.68/2.86  cnf(c_0_53, negated_conjecture, (k1_tsep_1(esk1_0,X1,esk3_0)=k1_tsep_1(esk1_0,esk3_0,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk3_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_20]), c_0_30]), c_0_15])]), c_0_17]), c_0_21]), c_0_48])).
% 2.68/2.86  cnf(c_0_54, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_55, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_56, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_57, negated_conjecture, (k2_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_14]), c_0_16]), c_0_25])).
% 2.68/2.86  cnf(c_0_58, negated_conjecture, (g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=k1_tsep_1(esk1_0,esk5_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_14]), c_0_30]), c_0_15])]), c_0_16]), c_0_17])).
% 2.68/2.86  cnf(c_0_59, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.68/2.86  cnf(c_0_60, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 2.68/2.86  cnf(c_0_61, negated_conjecture, (k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_20]), c_0_21])).
% 2.68/2.86  cnf(c_0_62, negated_conjecture, (k1_tsep_1(esk1_0,esk3_0,esk3_0)=k1_tsep_1(esk1_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])]), c_0_56])).
% 2.68/2.86  cnf(c_0_63, negated_conjecture, (r1_tarski(u1_struct_0(esk5_0),X1)|~r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)),X1)), inference(spm,[status(thm)],[c_0_43, c_0_57])).
% 2.68/2.86  cnf(c_0_64, negated_conjecture, (k1_tsep_1(esk1_0,X1,esk5_0)=k1_tsep_1(esk1_0,esk5_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_14]), c_0_58]), c_0_30]), c_0_15])]), c_0_17]), c_0_16])).
% 2.68/2.86  cnf(c_0_65, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_66, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_67, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_68, negated_conjecture, (k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_54]), c_0_56])).
% 2.68/2.86  cnf(c_0_69, negated_conjecture, (r1_tarski(k2_xboole_0(X1,u1_struct_0(esk3_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))|~r1_tarski(X1,u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 2.68/2.86  cnf(c_0_70, negated_conjecture, (k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 2.68/2.86  cnf(c_0_71, negated_conjecture, (r1_tarski(u1_struct_0(esk5_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_63, c_0_52])).
% 2.68/2.86  cnf(c_0_72, negated_conjecture, (k2_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0))=u1_struct_0(k1_tsep_1(esk1_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_14]), c_0_16])).
% 2.68/2.86  cnf(c_0_73, negated_conjecture, (k1_tsep_1(esk1_0,esk5_0,esk5_0)=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])]), c_0_67])).
% 2.68/2.86  cnf(c_0_74, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),X1)|~r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_43, c_0_68])).
% 2.68/2.86  cnf(c_0_75, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_60]), c_0_70])).
% 2.68/2.86  cnf(c_0_76, negated_conjecture, (k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0))=u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_65]), c_0_67])).
% 2.68/2.86  cnf(c_0_77, negated_conjecture, (r1_tarski(k2_xboole_0(X1,u1_struct_0(esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))|~r1_tarski(X1,u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_59, c_0_71])).
% 2.68/2.86  cnf(c_0_78, negated_conjecture, (k2_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0))=u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 2.68/2.86  cnf(c_0_79, negated_conjecture, (k1_tsep_1(esk1_0,X1,esk4_0)=k1_tsep_1(esk1_0,esk4_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_65]), c_0_15])]), c_0_67]), c_0_17])).
% 2.68/2.86  cnf(c_0_80, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 2.68/2.86  cnf(c_0_81, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),X1)|~r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),X1)), inference(spm,[status(thm)],[c_0_43, c_0_76])).
% 2.68/2.86  cnf(c_0_82, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_71]), c_0_78])).
% 2.68/2.86  cnf(c_0_83, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))=u1_struct_0(k1_tsep_1(esk1_0,X1,esk2_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_54]), c_0_15])]), c_0_17]), c_0_56])).
% 2.68/2.86  cnf(c_0_84, negated_conjecture, (k1_tsep_1(esk1_0,esk4_0,esk2_0)=k1_tsep_1(esk1_0,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_54]), c_0_56])).
% 2.68/2.86  cnf(c_0_85, negated_conjecture, (r1_tarski(k2_xboole_0(X1,u1_struct_0(esk2_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))|~r1_tarski(X1,u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_59, c_0_80])).
% 2.68/2.86  cnf(c_0_86, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 2.68/2.86  cnf(c_0_87, negated_conjecture, (k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))=u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_65]), c_0_67]), c_0_84])).
% 2.68/2.86  cnf(c_0_88, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.68/2.86  cnf(c_0_89, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk5_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 2.68/2.86  cnf(c_0_90, negated_conjecture, (~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.86  cnf(c_0_91, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_65]), c_0_15])]), c_0_67]), c_0_17])).
% 2.68/2.86  cnf(c_0_92, negated_conjecture, (~v2_pre_topc(X1)|~m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk5_0),X1)|~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 2.68/2.86  cnf(c_0_93, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_54]), c_0_56])).
% 2.68/2.86  cnf(c_0_94, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_29]), c_0_30]), c_0_93]), c_0_15])]), ['proof']).
% 2.68/2.86  # SZS output end CNFRefutation
% 2.68/2.86  # Proof object total steps             : 95
% 2.68/2.86  # Proof object clause steps            : 76
% 2.68/2.86  # Proof object formula steps           : 19
% 2.68/2.86  # Proof object conjectures             : 66
% 2.68/2.86  # Proof object clause conjectures      : 63
% 2.68/2.86  # Proof object formula conjectures     : 3
% 2.68/2.86  # Proof object initial clauses used    : 26
% 2.68/2.86  # Proof object initial formulas used   : 9
% 2.68/2.86  # Proof object generating inferences   : 47
% 2.68/2.86  # Proof object simplifying inferences  : 108
% 2.68/2.86  # Training examples: 0 positive, 0 negative
% 2.68/2.86  # Parsed axioms                        : 9
% 2.68/2.86  # Removed by relevancy pruning/SinE    : 0
% 2.68/2.86  # Initial clauses                      : 27
% 2.68/2.86  # Removed in clause preprocessing      : 0
% 2.68/2.86  # Initial clauses in saturation        : 27
% 2.68/2.86  # Processed clauses                    : 6212
% 2.68/2.86  # ...of these trivial                  : 114
% 2.68/2.86  # ...subsumed                          : 333
% 2.68/2.86  # ...remaining for further processing  : 5765
% 2.68/2.86  # Other redundant clauses eliminated   : 1
% 2.68/2.86  # Clauses deleted for lack of memory   : 0
% 2.68/2.86  # Backward-subsumed                    : 5
% 2.68/2.86  # Backward-rewritten                   : 1476
% 2.68/2.86  # Generated clauses                    : 246503
% 2.68/2.86  # ...of the previous two non-trivial   : 246722
% 2.68/2.86  # Contextual simplify-reflections      : 3
% 2.68/2.86  # Paramodulations                      : 246482
% 2.68/2.86  # Factorizations                       : 0
% 2.68/2.86  # Equation resolutions                 : 21
% 2.68/2.86  # Propositional unsat checks           : 0
% 2.68/2.86  #    Propositional check models        : 0
% 2.68/2.86  #    Propositional check unsatisfiable : 0
% 2.68/2.86  #    Propositional clauses             : 0
% 2.68/2.86  #    Propositional clauses after purity: 0
% 2.68/2.86  #    Propositional unsat core size     : 0
% 2.68/2.86  #    Propositional preprocessing time  : 0.000
% 2.68/2.86  #    Propositional encoding time       : 0.000
% 2.68/2.86  #    Propositional solver time         : 0.000
% 2.68/2.86  #    Success case prop preproc time    : 0.000
% 2.68/2.86  #    Success case prop encoding time   : 0.000
% 2.68/2.86  #    Success case prop solver time     : 0.000
% 2.68/2.86  # Current number of processed clauses  : 4256
% 2.68/2.86  #    Positive orientable unit clauses  : 2247
% 2.68/2.86  #    Positive unorientable unit clauses: 0
% 2.68/2.86  #    Negative unit clauses             : 152
% 2.68/2.86  #    Non-unit-clauses                  : 1857
% 2.68/2.86  # Current number of unprocessed clauses: 237062
% 2.68/2.86  # ...number of literals in the above   : 519207
% 2.68/2.86  # Current number of archived formulas  : 0
% 2.68/2.86  # Current number of archived clauses   : 1508
% 2.68/2.86  # Clause-clause subsumption calls (NU) : 997468
% 2.68/2.86  # Rec. Clause-clause subsumption calls : 941814
% 2.68/2.86  # Non-unit clause-clause subsumptions  : 321
% 2.68/2.86  # Unit Clause-clause subsumption calls : 118981
% 2.68/2.86  # Rewrite failures with RHS unbound    : 0
% 2.68/2.86  # BW rewrite match attempts            : 857945
% 2.68/2.86  # BW rewrite match successes           : 503
% 2.68/2.86  # Condensation attempts                : 0
% 2.68/2.86  # Condensation successes               : 0
% 2.68/2.86  # Termbank termtop insertions          : 12848642
% 2.68/2.87  
% 2.68/2.87  # -------------------------------------------------
% 2.68/2.87  # User time                : 2.400 s
% 2.68/2.87  # System time              : 0.133 s
% 2.68/2.87  # Total time               : 2.534 s
% 2.68/2.87  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
