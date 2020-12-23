%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:40 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 (3458 expanded)
%              Number of clauses        :   91 (1676 expanded)
%              Number of leaves         :    9 ( 887 expanded)
%              Depth                    :   12
%              Number of atoms          :  407 (6382 expanded)
%              Number of equality atoms :  111 (3072 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t23_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ ( X2 != k2_struct_0(X1)
                & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
            & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                & X2 = k2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_pre_topc)).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_10,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k7_subset_1(X12,X13,X14) = k4_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X11] : m1_subset_1(k2_subset_1(X11),k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_16,plain,(
    ! [X10] : k2_subset_1(X10) = X10 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_19,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_13]),
    [final]).

cnf(c_0_20,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X17,X18] :
      ( ~ l1_struct_0(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k7_subset_1(u1_struct_0(X17),k2_struct_0(X17),k7_subset_1(u1_struct_0(X17),k2_struct_0(X17),X18)) = X18 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_13]),
    [final]).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | k7_subset_1(X3,X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]),
    [final]).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21]),
    [final]).

cnf(c_0_26,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_27,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_19]),
    [final]).

cnf(c_0_28,plain,
    ( k7_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19]),
    [final]).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | k7_subset_1(X1,X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_31,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27]),
    [final]).

cnf(c_0_32,plain,
    ( k7_subset_1(X1,X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25]),
    [final]).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_35,plain,
    ( r1_tarski(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_25])])]),
    [final]).

cnf(c_0_36,plain,
    ( k7_subset_1(X1,X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33]),
    [final]).

cnf(c_0_37,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35]),
    [final]).

fof(c_0_38,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_39,plain,
    ( k7_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_27]),c_0_25])]),
    [final]).

cnf(c_0_40,plain,
    ( k7_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0),k2_struct_0(X1),X2) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37]),
    [final]).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_39])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

cnf(c_0_44,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_40]),c_0_37]),
    [final]).

cnf(c_0_45,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k7_subset_1(X2,k2_struct_0(X1),k1_xboole_0)))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27]),
    [final]).

cnf(c_0_46,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39]),
    [final]).

cnf(c_0_47,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_41]),
    [final]).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25]),
    [final]).

fof(c_0_49,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
      | esk2_0 != k2_struct_0(esk1_0) )
    & ( esk2_0 = k2_struct_0(esk1_0)
      | esk2_0 != k2_struct_0(esk1_0) )
    & ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
      | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 )
    & ( esk2_0 = k2_struct_0(esk1_0)
      | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])])).

cnf(c_0_50,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27]),
    [final]).

cnf(c_0_51,plain,
    ( r1_tarski(k2_struct_0(X1),X2)
    | k7_subset_1(k7_subset_1(X3,k2_struct_0(X1),k1_xboole_0),k2_struct_0(X1),X2) != k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_45]),
    [final]).

cnf(c_0_52,plain,
    ( k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_35]),
    [final]).

cnf(c_0_53,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k7_subset_1(X3,k2_struct_0(X2),X1)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_27]),
    [final]).

cnf(c_0_54,plain,
    ( k7_subset_1(X1,X2,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_25])]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_41]),
    [final]).

cnf(c_0_59,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4)) = X4
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27]),
    [final]).

cnf(c_0_60,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27]),
    [final]).

cnf(c_0_61,plain,
    ( k7_subset_1(k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0),k2_struct_0(X2),X3) = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_45]),
    [final]).

cnf(c_0_62,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X1))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_19]),
    [final]).

cnf(c_0_63,plain,
    ( r1_tarski(k2_struct_0(X1),X2)
    | k7_subset_1(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k1_xboole_0,k2_struct_0(X1))),k2_struct_0(X1),X2) != k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_41]),
    [final]).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_41]),
    [final]).

cnf(c_0_65,plain,
    ( k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),k1_xboole_0)) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_27]),
    [final]).

cnf(c_0_66,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X1))))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_19]),
    [final]).

cnf(c_0_67,plain,
    ( r1_tarski(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),k1_xboole_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27]),
    [final]).

cnf(c_0_68,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = k2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_54]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_55]),c_0_56]),c_0_57])]),
    [final]).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_39])).

cnf(c_0_71,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_54])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_48]),c_0_25])]),
    [final]).

cnf(c_0_74,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(k2_struct_0(X2),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_40]),c_0_37]),
    [final]).

cnf(c_0_75,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_40]),c_0_37]),
    [final]).

cnf(c_0_76,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(X3,k2_struct_0(X2)))) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_47]),
    [final]).

cnf(c_0_77,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3))) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_19]),
    [final]).

cnf(c_0_78,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_59]),
    [final]).

cnf(c_0_79,plain,
    ( k7_subset_1(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k1_xboole_0,k2_struct_0(X1))),k2_struct_0(X1),X2) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_19]),c_0_41]),
    [final]).

cnf(c_0_80,plain,
    ( k7_subset_1(k1_xboole_0,k2_struct_0(X1),X2) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0)
    | ~ r1_tarski(k2_struct_0(X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_40]),c_0_37]),
    [final]).

cnf(c_0_81,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(X1,k2_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_47]),
    [final]).

cnf(c_0_82,plain,
    ( k2_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))
    | ~ r1_tarski(k2_struct_0(X1),k7_subset_1(X3,k2_struct_0(X1),k2_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_47]),
    [final]).

cnf(c_0_83,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(k2_struct_0(X2),k1_xboole_0)
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_23]),
    [final]).

cnf(c_0_84,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(k2_struct_0(X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39]),
    [final]).

cnf(c_0_85,plain,
    ( k2_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_54]),
    [final]).

cnf(c_0_86,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(X2,k2_struct_0(X1)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_47]),
    [final]).

cnf(c_0_87,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_19]),
    [final]).

cnf(c_0_88,plain,
    ( r1_tarski(k2_struct_0(X1),X2)
    | k7_subset_1(k1_xboole_0,k2_struct_0(X1),X2) != k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))
    | ~ r1_tarski(k2_struct_0(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64]),
    [final]).

cnf(c_0_89,plain,
    ( k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_31]),
    [final]).

cnf(c_0_90,plain,
    ( k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k1_xboole_0,k2_struct_0(X1)))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_19]),c_0_41]),
    [final]).

cnf(c_0_91,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k5_xboole_0(k2_struct_0(X2),k3_xboole_0(X1,k2_struct_0(X2)))))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_47]),
    [final]).

cnf(c_0_92,plain,
    ( k2_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k7_subset_1(X2,k2_struct_0(X1),k2_struct_0(X1))))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_47]),
    [final]).

cnf(c_0_93,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_23]),
    [final]).

cnf(c_0_94,plain,
    ( r1_tarski(k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k1_xboole_0,k2_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_19]),c_0_41]),
    [final]).

cnf(c_0_95,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k1_xboole_0,k2_struct_0(X1)))))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_19]),c_0_41]),
    [final]).

cnf(c_0_96,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_39]),
    [final]).

cnf(c_0_97,plain,
    ( r1_tarski(k2_struct_0(X1),X2)
    | k7_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0),k2_struct_0(X1),X2) != k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_37]),
    [final]).

cnf(c_0_98,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39]),
    [final]).

cnf(c_0_99,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39]),
    [final]).

cnf(c_0_100,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = k2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_68]),
    [final]).

cnf(c_0_101,plain,
    ( k2_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_68]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_68]),c_0_56])]),
    [final]).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_25]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( k2_struct_0(esk1_0) != esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_39]),
    [final]).

cnf(c_0_105,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | k2_struct_0(esk1_0) != esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_27]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k1_xboole_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_57]),
    [final]).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_57]),
    [final]).

cnf(c_0_108,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_25]),
    [final]).

cnf(c_0_109,plain,
    ( k7_subset_1(X1,X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_73]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.027 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # No proof found!
% 0.20/0.40  # SZS status CounterSatisfiable
% 0.20/0.40  # SZS output start Saturation
% 0.20/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.40  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.20/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.40  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.20/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.40  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.20/0.40  fof(c_0_9, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.40  fof(c_0_10, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.40  fof(c_0_11, plain, ![X12, X13, X14]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k7_subset_1(X12,X13,X14)=k4_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.20/0.40  cnf(c_0_12, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_14, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  fof(c_0_15, plain, ![X11]:m1_subset_1(k2_subset_1(X11),k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.40  fof(c_0_16, plain, ![X10]:k2_subset_1(X10)=X10, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.40  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_18, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.20/0.40  cnf(c_0_19, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_14, c_0_13]), ['final']).
% 0.20/0.40  cnf(c_0_20, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_21, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  fof(c_0_22, plain, ![X17, X18]:(~l1_struct_0(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|k7_subset_1(u1_struct_0(X17),k2_struct_0(X17),k7_subset_1(u1_struct_0(X17),k2_struct_0(X17),X18))=X18)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.20/0.40  cnf(c_0_23, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_13]), ['final']).
% 0.20/0.40  cnf(c_0_24, plain, (r1_tarski(X1,X2)|k7_subset_1(X3,X1,X2)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_20, c_0_21]), ['final']).
% 0.20/0.40  cnf(c_0_26, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.20/0.40  cnf(c_0_27, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_19, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_28, plain, (k7_subset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_23, c_0_19]), ['final']).
% 0.20/0.40  fof(c_0_29, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.40  cnf(c_0_30, plain, (r1_tarski(X1,X2)|k7_subset_1(X1,X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.20/0.40  cnf(c_0_31, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_32, plain, (k7_subset_1(X1,X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_25]), ['final']).
% 0.20/0.40  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.20/0.40  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.20/0.40  cnf(c_0_35, plain, (r1_tarski(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_25])])]), ['final']).
% 0.20/0.40  cnf(c_0_36, plain, (k7_subset_1(X1,X1,X2)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_32, c_0_33]), ['final']).
% 0.20/0.40  cnf(c_0_37, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_34, c_0_35]), ['final']).
% 0.20/0.40  fof(c_0_38, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.40  cnf(c_0_39, plain, (k7_subset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_27]), c_0_25])]), ['final']).
% 0.20/0.40  cnf(c_0_40, plain, (k7_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0),k2_struct_0(X1),X2)=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_37]), ['final']).
% 0.20/0.40  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.20/0.40  cnf(c_0_42, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_19, c_0_39])).
% 0.20/0.40  fof(c_0_43, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.20/0.40  cnf(c_0_44, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_40]), c_0_37]), ['final']).
% 0.20/0.40  cnf(c_0_45, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k7_subset_1(X2,k2_struct_0(X1),k1_xboole_0)))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_46, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_26, c_0_39]), ['final']).
% 0.20/0.40  cnf(c_0_47, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k3_xboole_0(X3,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_41]), ['final']).
% 0.20/0.40  cnf(c_0_48, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_42, c_0_25]), ['final']).
% 0.20/0.40  fof(c_0_49, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])])).
% 0.20/0.40  cnf(c_0_50, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))|~r1_tarski(k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X1))), inference(spm,[status(thm)],[c_0_44, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_51, plain, (r1_tarski(k2_struct_0(X1),X2)|k7_subset_1(k7_subset_1(X3,k2_struct_0(X1),k1_xboole_0),k2_struct_0(X1),X2)!=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_24, c_0_45]), ['final']).
% 0.20/0.40  cnf(c_0_52, plain, (k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_32, c_0_35]), ['final']).
% 0.20/0.40  cnf(c_0_53, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k7_subset_1(X3,k2_struct_0(X2),X1)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_46, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_54, plain, (k7_subset_1(X1,X2,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_25])]), ['final']).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49]), ['final']).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_49]), ['final']).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_49]), ['final']).
% 0.20/0.40  cnf(c_0_58, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_41]), ['final']).
% 0.20/0.40  cnf(c_0_59, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4))=X4|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_31, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_60, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_26, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_61, plain, (k7_subset_1(k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0),k2_struct_0(X2),X3)=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~r1_tarski(k2_struct_0(X2),X3)), inference(spm,[status(thm)],[c_0_28, c_0_45]), ['final']).
% 0.20/0.40  cnf(c_0_62, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))|~r1_tarski(k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X1)))), inference(spm,[status(thm)],[c_0_50, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_63, plain, (r1_tarski(k2_struct_0(X1),X2)|k7_subset_1(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k1_xboole_0,k2_struct_0(X1))),k2_struct_0(X1),X2)!=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_19]), c_0_41]), ['final']).
% 0.20/0.40  cnf(c_0_64, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_41]), ['final']).
% 0.20/0.40  cnf(c_0_65, plain, (k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),k1_xboole_0))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_52, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_66, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X1))))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_53, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_67, plain, (r1_tarski(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),k1_xboole_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_35, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_68, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=k2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_26, c_0_54]), ['final']).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_55]), c_0_56]), c_0_57])]), ['final']).
% 0.20/0.40  cnf(c_0_70, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_47, c_0_39])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_49]), ['final']).
% 0.20/0.40  cnf(c_0_72, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_19, c_0_54])).
% 0.20/0.40  cnf(c_0_73, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_48]), c_0_25])]), ['final']).
% 0.20/0.40  cnf(c_0_74, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~r1_tarski(k2_struct_0(X2),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_40]), c_0_37]), ['final']).
% 0.20/0.40  cnf(c_0_75, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_40]), c_0_37]), ['final']).
% 0.20/0.40  cnf(c_0_76, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(X3,k2_struct_0(X2))))=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_59, c_0_47]), ['final']).
% 0.20/0.40  cnf(c_0_77, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(k2_struct_0(X2),X3)))=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_59, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_78, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))=X3|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_19, c_0_59]), ['final']).
% 0.20/0.40  cnf(c_0_79, plain, (k7_subset_1(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k1_xboole_0,k2_struct_0(X1))),k2_struct_0(X1),X2)=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))|~r1_tarski(k2_struct_0(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_19]), c_0_41]), ['final']).
% 0.20/0.40  cnf(c_0_80, plain, (k7_subset_1(k1_xboole_0,k2_struct_0(X1),X2)=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)|~r1_tarski(k2_struct_0(X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_40]), c_0_37]), ['final']).
% 0.20/0.40  cnf(c_0_81, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))|~r1_tarski(k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k3_xboole_0(X1,k2_struct_0(X2))))), inference(spm,[status(thm)],[c_0_50, c_0_47]), ['final']).
% 0.20/0.40  cnf(c_0_82, plain, (k2_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))|~r1_tarski(k2_struct_0(X1),k7_subset_1(X3,k2_struct_0(X1),k2_struct_0(X1)))), inference(spm,[status(thm)],[c_0_62, c_0_47]), ['final']).
% 0.20/0.40  cnf(c_0_83, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))|~r1_tarski(k2_struct_0(X2),k1_xboole_0)|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_62, c_0_23]), ['final']).
% 0.20/0.40  cnf(c_0_84, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~r1_tarski(k2_struct_0(X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_39]), ['final']).
% 0.20/0.40  cnf(c_0_85, plain, (k2_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_54]), ['final']).
% 0.20/0.40  cnf(c_0_86, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(X2,k2_struct_0(X1))))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_60, c_0_47]), ['final']).
% 0.20/0.40  cnf(c_0_87, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_60, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_88, plain, (r1_tarski(k2_struct_0(X1),X2)|k7_subset_1(k1_xboole_0,k2_struct_0(X1),X2)!=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))|~r1_tarski(k2_struct_0(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_64]), ['final']).
% 0.20/0.40  cnf(c_0_89, plain, (k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_19, c_0_31]), ['final']).
% 0.20/0.40  cnf(c_0_90, plain, (k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k1_xboole_0,k2_struct_0(X1))))=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_19]), c_0_41]), ['final']).
% 0.20/0.40  cnf(c_0_91, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k5_xboole_0(k2_struct_0(X2),k3_xboole_0(X1,k2_struct_0(X2)))))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_53, c_0_47]), ['final']).
% 0.20/0.40  cnf(c_0_92, plain, (k2_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k7_subset_1(X2,k2_struct_0(X1),k2_struct_0(X1))))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_66, c_0_47]), ['final']).
% 0.20/0.40  cnf(c_0_93, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))|~r1_tarski(k2_struct_0(X2),X1)), inference(spm,[status(thm)],[c_0_66, c_0_23]), ['final']).
% 0.20/0.40  cnf(c_0_94, plain, (r1_tarski(k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k1_xboole_0,k2_struct_0(X1))))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_19]), c_0_41]), ['final']).
% 0.20/0.40  cnf(c_0_95, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k5_xboole_0(k2_struct_0(X1),k3_xboole_0(k1_xboole_0,k2_struct_0(X1)))))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_19]), c_0_41]), ['final']).
% 0.20/0.40  cnf(c_0_96, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_31, c_0_39]), ['final']).
% 0.20/0.40  cnf(c_0_97, plain, (r1_tarski(k2_struct_0(X1),X2)|k7_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0),k2_struct_0(X1),X2)!=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_24, c_0_37]), ['final']).
% 0.20/0.40  cnf(c_0_98, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_26, c_0_39]), ['final']).
% 0.20/0.40  cnf(c_0_99, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_46, c_0_39]), ['final']).
% 0.20/0.40  cnf(c_0_100, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=k2_struct_0(X2)|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_68]), ['final']).
% 0.20/0.40  cnf(c_0_101, plain, (k2_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_39, c_0_68]), ['final']).
% 0.20/0.40  cnf(c_0_102, negated_conjecture, (k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_68]), c_0_56])]), ['final']).
% 0.20/0.40  cnf(c_0_103, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_70, c_0_25]), ['final']).
% 0.20/0.40  cnf(c_0_104, negated_conjecture, (k2_struct_0(esk1_0)!=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_71, c_0_39]), ['final']).
% 0.20/0.40  cnf(c_0_105, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k2_struct_0(esk1_0)!=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_71, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_106, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k1_xboole_0|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_57]), ['final']).
% 0.20/0.40  cnf(c_0_107, negated_conjecture, (r1_tarski(esk2_0,X1)|k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_57]), ['final']).
% 0.20/0.40  cnf(c_0_108, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_25]), ['final']).
% 0.20/0.40  cnf(c_0_109, plain, (k7_subset_1(X1,X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_73]), ['final']).
% 0.20/0.40  # SZS output end Saturation
% 0.20/0.40  # Proof object total steps             : 110
% 0.20/0.40  # Proof object clause steps            : 91
% 0.20/0.40  # Proof object formula steps           : 19
% 0.20/0.40  # Proof object conjectures             : 13
% 0.20/0.40  # Proof object clause conjectures      : 10
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 14
% 0.20/0.40  # Proof object initial formulas used   : 9
% 0.20/0.40  # Proof object generating inferences   : 73
% 0.20/0.40  # Proof object simplifying inferences  : 27
% 0.20/0.40  # Parsed axioms                        : 9
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 16
% 0.20/0.40  # Removed in clause preprocessing      : 4
% 0.20/0.40  # Initial clauses in saturation        : 12
% 0.20/0.40  # Processed clauses                    : 421
% 0.20/0.40  # ...of these trivial                  : 1
% 0.20/0.40  # ...subsumed                          : 318
% 0.20/0.40  # ...remaining for further processing  : 102
% 0.20/0.40  # Other redundant clauses eliminated   : 8
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 7
% 0.20/0.40  # Backward-rewritten                   : 1
% 0.20/0.40  # Generated clauses                    : 446
% 0.20/0.40  # ...of the previous two non-trivial   : 401
% 0.20/0.40  # Contextual simplify-reflections      : 4
% 0.20/0.40  # Paramodulations                      : 438
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 8
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 82
% 0.20/0.40  #    Positive orientable unit clauses  : 6
% 0.20/0.40  #    Positive unorientable unit clauses: 1
% 0.20/0.40  #    Negative unit clauses             : 0
% 0.20/0.40  #    Non-unit-clauses                  : 75
% 0.20/0.40  # Current number of unprocessed clauses: 0
% 0.20/0.40  # ...number of literals in the above   : 0
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 22
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 5764
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1194
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 329
% 0.20/0.40  # Unit Clause-clause subsumption calls : 27
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 24
% 0.20/0.40  # BW rewrite match successes           : 3
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 14443
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.052 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.056 s
% 0.20/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
