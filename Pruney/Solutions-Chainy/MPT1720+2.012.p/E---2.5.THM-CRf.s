%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:07 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 477 expanded)
%              Number of clauses        :   48 ( 165 expanded)
%              Number of leaves         :    9 ( 119 expanded)
%              Depth                    :   12
%              Number of atoms          :  275 (4063 expanded)
%              Number of equality atoms :   21 (  70 expanded)
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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

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

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X4,X3) )
                     => m1_pre_topc(k1_tsep_1(X1,X2,X4),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tmap_1])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | l1_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

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
    & m1_pre_topc(esk2_0,esk3_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X16 != k1_tsep_1(X13,X14,X15)
        | u1_struct_0(X16) = k2_xboole_0(u1_struct_0(X14),u1_struct_0(X15))
        | v2_struct_0(X16)
        | ~ v1_pre_topc(X16)
        | ~ m1_pre_topc(X16,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13) )
      & ( u1_struct_0(X16) != k2_xboole_0(u1_struct_0(X14),u1_struct_0(X15))
        | X16 = k1_tsep_1(X13,X14,X15)
        | v2_struct_0(X16)
        | ~ v1_pre_topc(X16)
        | ~ m1_pre_topc(X16,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

fof(c_0_13,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v2_struct_0(k1_tsep_1(X17,X18,X19))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) )
      & ( v1_pre_topc(k1_tsep_1(X17,X18,X19))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) )
      & ( m1_pre_topc(k1_tsep_1(X17,X18,X19),X17)
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_14,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | m1_pre_topc(X22,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_15,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X23,X24,X25] :
      ( ( ~ r1_tarski(u1_struct_0(X24),u1_struct_0(X25))
        | m1_pre_topc(X24,X25)
        | ~ m1_pre_topc(X25,X23)
        | ~ m1_pre_topc(X24,X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ m1_pre_topc(X24,X25)
        | r1_tarski(u1_struct_0(X24),u1_struct_0(X25))
        | ~ m1_pre_topc(X25,X23)
        | ~ m1_pre_topc(X24,X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_25,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_32,plain,(
    ! [X5,X6,X7,X8] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(k2_xboole_0(X5,X7),k2_xboole_0(X6,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_16]),c_0_26]),c_0_17])])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0)) = u1_struct_0(k1_tsep_1(esk3_0,X1,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24])]),c_0_29]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk3_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_31]),c_0_24])]),c_0_29])).

cnf(c_0_40,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28])])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_34]),c_0_17])]),c_0_35]),c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) = u1_struct_0(k1_tsep_1(esk3_0,esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_16]),c_0_17])]),c_0_35]),c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_31]),c_0_29])).

fof(c_0_47,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | v2_struct_0(X21)
      | ~ m1_pre_topc(X21,X20)
      | k1_tsep_1(X20,X21,X21) = g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,u1_struct_0(esk4_0)),k2_xboole_0(X2,u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_42]),c_0_37])])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk3_0,esk2_0,esk4_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_42]),c_0_38]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk3_0,esk3_0,esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_16]),c_0_29]),c_0_46])).

fof(c_0_52,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))
      | m1_pre_topc(X12,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_44]),c_0_50]),c_0_46]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_17])]),c_0_29]),c_0_35])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_34]),c_0_17])]),c_0_30]),c_0_35])).

cnf(c_0_58,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k1_tsep_1(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_16]),c_0_26]),c_0_17])]),c_0_29]),c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),X1)
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_16]),c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_42]),c_0_38])).

cnf(c_0_63,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_24])])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_26]),c_0_62]),c_0_17])])).

cnf(c_0_65,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:42:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.91/1.10  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.91/1.10  # and selection function SelectComplexG.
% 0.91/1.10  #
% 0.91/1.10  # Preprocessing time       : 0.028 s
% 0.91/1.10  # Presaturation interreduction done
% 0.91/1.10  
% 0.91/1.10  # Proof found!
% 0.91/1.10  # SZS status Theorem
% 0.91/1.10  # SZS output start CNFRefutation
% 0.91/1.10  fof(t29_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X3))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tmap_1)).
% 0.91/1.10  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.91/1.10  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 0.91/1.10  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.91/1.10  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.91/1.10  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.91/1.10  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 0.91/1.10  fof(t25_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 0.91/1.10  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.91/1.10  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X3))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),X3))))))), inference(assume_negation,[status(cth)],[t29_tmap_1])).
% 0.91/1.10  fof(c_0_10, plain, ![X9, X10]:(~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|l1_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.91/1.10  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((m1_pre_topc(esk2_0,esk3_0)&m1_pre_topc(esk4_0,esk3_0))&~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.91/1.10  fof(c_0_12, plain, ![X13, X14, X15, X16]:((X16!=k1_tsep_1(X13,X14,X15)|u1_struct_0(X16)=k2_xboole_0(u1_struct_0(X14),u1_struct_0(X15))|(v2_struct_0(X16)|~v1_pre_topc(X16)|~m1_pre_topc(X16,X13))|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~m1_pre_topc(X14,X13))|(v2_struct_0(X13)|~l1_pre_topc(X13)))&(u1_struct_0(X16)!=k2_xboole_0(u1_struct_0(X14),u1_struct_0(X15))|X16=k1_tsep_1(X13,X14,X15)|(v2_struct_0(X16)|~v1_pre_topc(X16)|~m1_pre_topc(X16,X13))|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~m1_pre_topc(X14,X13))|(v2_struct_0(X13)|~l1_pre_topc(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 0.91/1.10  fof(c_0_13, plain, ![X17, X18, X19]:(((~v2_struct_0(k1_tsep_1(X17,X18,X19))|(v2_struct_0(X17)|~l1_pre_topc(X17)|v2_struct_0(X18)|~m1_pre_topc(X18,X17)|v2_struct_0(X19)|~m1_pre_topc(X19,X17)))&(v1_pre_topc(k1_tsep_1(X17,X18,X19))|(v2_struct_0(X17)|~l1_pre_topc(X17)|v2_struct_0(X18)|~m1_pre_topc(X18,X17)|v2_struct_0(X19)|~m1_pre_topc(X19,X17))))&(m1_pre_topc(k1_tsep_1(X17,X18,X19),X17)|(v2_struct_0(X17)|~l1_pre_topc(X17)|v2_struct_0(X18)|~m1_pre_topc(X18,X17)|v2_struct_0(X19)|~m1_pre_topc(X19,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.91/1.10  fof(c_0_14, plain, ![X22]:(~l1_pre_topc(X22)|m1_pre_topc(X22,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.91/1.10  cnf(c_0_15, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.91/1.10  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  fof(c_0_18, plain, ![X23, X24, X25]:((~r1_tarski(u1_struct_0(X24),u1_struct_0(X25))|m1_pre_topc(X24,X25)|~m1_pre_topc(X25,X23)|~m1_pre_topc(X24,X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~m1_pre_topc(X24,X25)|r1_tarski(u1_struct_0(X24),u1_struct_0(X25))|~m1_pre_topc(X25,X23)|~m1_pre_topc(X24,X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.91/1.10  cnf(c_0_19, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.91/1.10  cnf(c_0_20, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.91/1.10  cnf(c_0_21, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.91/1.10  cnf(c_0_22, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.91/1.10  cnf(c_0_23, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.91/1.10  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.91/1.10  cnf(c_0_25, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.91/1.10  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_27, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.91/1.10  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.91/1.10  fof(c_0_32, plain, ![X5, X6, X7, X8]:(~r1_tarski(X5,X6)|~r1_tarski(X7,X8)|r1_tarski(k2_xboole_0(X5,X7),k2_xboole_0(X6,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 0.91/1.10  cnf(c_0_33, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_16]), c_0_26]), c_0_17])])).
% 0.91/1.10  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_36, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))=u1_struct_0(k1_tsep_1(esk3_0,X1,esk4_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_24])]), c_0_29]), c_0_30])).
% 0.91/1.10  cnf(c_0_37, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_39, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk3_0,X1,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_31]), c_0_24])]), c_0_29])).
% 0.91/1.10  cnf(c_0_40, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.91/1.10  cnf(c_0_41, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28])])).
% 0.91/1.10  cnf(c_0_42, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_43, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))=u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_34]), c_0_17])]), c_0_35]), c_0_30])).
% 0.91/1.10  cnf(c_0_44, negated_conjecture, (k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))=u1_struct_0(k1_tsep_1(esk3_0,esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.91/1.10  cnf(c_0_45, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_16]), c_0_17])]), c_0_35]), c_0_29])).
% 0.91/1.10  cnf(c_0_46, negated_conjecture, (k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_31]), c_0_29])).
% 0.91/1.10  fof(c_0_47, plain, ![X20, X21]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|(v2_struct_0(X21)|~m1_pre_topc(X21,X20)|k1_tsep_1(X20,X21,X21)=g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).
% 0.91/1.10  cnf(c_0_48, negated_conjecture, (r1_tarski(k2_xboole_0(X1,u1_struct_0(esk4_0)),k2_xboole_0(X2,u1_struct_0(esk3_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.91/1.10  cnf(c_0_49, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_42]), c_0_37])])).
% 0.91/1.10  cnf(c_0_50, negated_conjecture, (u1_struct_0(k1_tsep_1(esk3_0,esk2_0,esk4_0))=u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_42]), c_0_38]), c_0_44])).
% 0.91/1.10  cnf(c_0_51, negated_conjecture, (u1_struct_0(k1_tsep_1(esk3_0,esk3_0,esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_16]), c_0_29]), c_0_46])).
% 0.91/1.10  fof(c_0_52, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_pre_topc(X12,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))|m1_pre_topc(X12,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.91/1.10  cnf(c_0_53, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.91/1.10  cnf(c_0_54, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.91/1.10  cnf(c_0_55, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_44]), c_0_50]), c_0_46]), c_0_51])).
% 0.91/1.10  cnf(c_0_56, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_16]), c_0_17])]), c_0_29]), c_0_35])).
% 0.91/1.10  cnf(c_0_57, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_34]), c_0_17])]), c_0_30]), c_0_35])).
% 0.91/1.10  cnf(c_0_58, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.91/1.10  cnf(c_0_59, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k1_tsep_1(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_16]), c_0_26]), c_0_17])]), c_0_29]), c_0_35])).
% 0.91/1.10  cnf(c_0_60, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0))|~v2_pre_topc(X1)|~m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),X1)|~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.91/1.10  cnf(c_0_61, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_16]), c_0_29])).
% 0.91/1.10  cnf(c_0_62, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_42]), c_0_38])).
% 0.91/1.10  cnf(c_0_63, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_24])])).
% 0.91/1.10  cnf(c_0_64, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_26]), c_0_62]), c_0_17])])).
% 0.91/1.10  cnf(c_0_65, negated_conjecture, (~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.91/1.10  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), ['proof']).
% 0.91/1.10  # SZS output end CNFRefutation
% 0.91/1.10  # Proof object total steps             : 67
% 0.91/1.10  # Proof object clause steps            : 48
% 0.91/1.10  # Proof object formula steps           : 19
% 0.91/1.10  # Proof object conjectures             : 39
% 0.91/1.10  # Proof object clause conjectures      : 36
% 0.91/1.10  # Proof object formula conjectures     : 3
% 0.91/1.10  # Proof object initial clauses used    : 23
% 0.91/1.10  # Proof object initial formulas used   : 9
% 0.91/1.10  # Proof object generating inferences   : 24
% 0.91/1.10  # Proof object simplifying inferences  : 60
% 0.91/1.10  # Training examples: 0 positive, 0 negative
% 0.91/1.10  # Parsed axioms                        : 9
% 0.91/1.10  # Removed by relevancy pruning/SinE    : 0
% 0.91/1.10  # Initial clauses                      : 24
% 0.91/1.10  # Removed in clause preprocessing      : 0
% 0.91/1.10  # Initial clauses in saturation        : 24
% 0.91/1.10  # Processed clauses                    : 3135
% 0.91/1.10  # ...of these trivial                  : 2
% 0.91/1.10  # ...subsumed                          : 3
% 0.91/1.10  # ...remaining for further processing  : 3130
% 0.91/1.10  # Other redundant clauses eliminated   : 1
% 0.91/1.10  # Clauses deleted for lack of memory   : 0
% 0.91/1.10  # Backward-subsumed                    : 9
% 0.91/1.10  # Backward-rewritten                   : 525
% 0.91/1.10  # Generated clauses                    : 76788
% 0.91/1.10  # ...of the previous two non-trivial   : 76317
% 0.91/1.10  # Contextual simplify-reflections      : 7
% 0.91/1.10  # Paramodulations                      : 76783
% 0.91/1.10  # Factorizations                       : 0
% 0.91/1.10  # Equation resolutions                 : 5
% 0.91/1.10  # Propositional unsat checks           : 0
% 0.91/1.10  #    Propositional check models        : 0
% 0.91/1.10  #    Propositional check unsatisfiable : 0
% 0.91/1.10  #    Propositional clauses             : 0
% 0.91/1.10  #    Propositional clauses after purity: 0
% 0.91/1.10  #    Propositional unsat core size     : 0
% 0.91/1.10  #    Propositional preprocessing time  : 0.000
% 0.91/1.10  #    Propositional encoding time       : 0.000
% 0.91/1.10  #    Propositional solver time         : 0.000
% 0.91/1.10  #    Success case prop preproc time    : 0.000
% 0.91/1.10  #    Success case prop encoding time   : 0.000
% 0.91/1.10  #    Success case prop solver time     : 0.000
% 0.91/1.10  # Current number of processed clauses  : 2571
% 0.91/1.10  #    Positive orientable unit clauses  : 1334
% 0.91/1.10  #    Positive unorientable unit clauses: 0
% 0.91/1.10  #    Negative unit clauses             : 5
% 0.91/1.10  #    Non-unit-clauses                  : 1232
% 0.91/1.10  # Current number of unprocessed clauses: 73210
% 0.91/1.10  # ...number of literals in the above   : 125524
% 0.91/1.10  # Current number of archived formulas  : 0
% 0.91/1.10  # Current number of archived clauses   : 558
% 0.91/1.10  # Clause-clause subsumption calls (NU) : 160810
% 0.91/1.10  # Rec. Clause-clause subsumption calls : 122772
% 0.91/1.10  # Non-unit clause-clause subsumptions  : 17
% 0.91/1.10  # Unit Clause-clause subsumption calls : 56009
% 0.91/1.10  # Rewrite failures with RHS unbound    : 0
% 0.91/1.10  # BW rewrite match attempts            : 54705
% 0.91/1.10  # BW rewrite match successes           : 396
% 0.91/1.10  # Condensation attempts                : 0
% 0.91/1.10  # Condensation successes               : 0
% 0.91/1.10  # Termbank termtop insertions          : 2335246
% 0.91/1.11  
% 0.91/1.11  # -------------------------------------------------
% 0.91/1.11  # User time                : 0.727 s
% 0.91/1.11  # System time              : 0.040 s
% 0.91/1.11  # Total time               : 0.767 s
% 0.91/1.11  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
