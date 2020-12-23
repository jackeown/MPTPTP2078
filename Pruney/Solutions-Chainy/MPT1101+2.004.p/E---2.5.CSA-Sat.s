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
% DateTime   : Thu Dec  3 11:08:31 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   83 (1285 expanded)
%              Number of clauses        :   64 ( 630 expanded)
%              Number of leaves         :    9 ( 313 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 (2960 expanded)
%              Number of equality atoms :   69 ( 827 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t18_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

fof(t25_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_9,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_10,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | m1_subset_1(k3_subset_1(X8,X9),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t18_pre_topc])).

fof(c_0_16,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | k4_subset_1(X16,X17,k3_subset_1(X16,X17)) = k2_subset_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).

fof(c_0_17,plain,(
    ! [X15] : k2_subset_1(X15) = k3_subset_1(X15,k1_subset_1(X15)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_18,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | k3_subset_1(X10,k3_subset_1(X10,X11)) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

fof(c_0_21,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) != k2_struct_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | k4_subset_1(X12,X13,X14) = k2_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_23,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = k2_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

fof(c_0_26,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_28,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_30,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_31,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = k3_subset_1(X2,k1_subset_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_20]),
    [final]).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_34,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_29]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_29]),
    [final]).

cnf(c_0_37,plain,
    ( k4_subset_1(X1,X2,X1) = k2_xboole_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20]),
    [final]).

cnf(c_0_38,plain,
    ( k4_subset_1(X1,k3_subset_1(X1,X1),X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_32])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k3_subset_1(X1,X1),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k1_subset_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,esk2_0) = k2_xboole_0(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),k1_subset_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_35]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_35]),
    [final]).

cnf(c_0_45,plain,
    ( k4_subset_1(X1,X2,k3_subset_1(X1,X1)) = k2_xboole_0(X2,k3_subset_1(X1,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28]),
    [final]).

cnf(c_0_46,plain,
    ( k4_subset_1(X1,X1,k3_subset_1(X1,X1)) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_35]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29]),
    [final]).

cnf(c_0_49,plain,
    ( k3_subset_1(X1,k1_subset_1(X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_38]),c_0_39]),
    [final]).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k1_subset_1(u1_struct_0(esk1_0))) != k2_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_14]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),k1_subset_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k2_xboole_0(esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k1_subset_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_29]),c_0_41])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k3_subset_1(X1,X1)) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_20]),c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_47]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(esk2_0,u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_48]),
    [final]).

cnf(c_0_58,plain,
    ( k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_49]),
    [final]).

cnf(c_0_59,plain,
    ( k3_subset_1(X1,X1) = X1
    | ~ r1_tarski(X1,k3_subset_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_34]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),esk2_0) = u1_struct_0(esk1_0)
    | ~ r1_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_47]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ r1_tarski(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( k2_struct_0(esk1_0) != u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_49]),
    [final]).

cnf(c_0_63,plain,
    ( k4_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1)) = k3_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_28]),c_0_52]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) = k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_28]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) = k2_xboole_0(esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_29]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_xboole_0(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_20]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_49]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_35]),c_0_52]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_49]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_49]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_49]),
    [final]).

cnf(c_0_73,plain,
    ( k4_subset_1(X1,X1,k3_subset_1(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_46,c_0_49]),
    [final]).

cnf(c_0_74,plain,
    ( k4_subset_1(X1,k3_subset_1(X1,X1),X1) = X1 ),
    inference(rw,[status(thm)],[c_0_38,c_0_49]),
    [final]).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_55,c_0_49]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0) = k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_28]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0) = k2_xboole_0(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_20]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_35]),c_0_56]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_57]),
    [final]).

cnf(c_0_80,plain,
    ( k4_subset_1(X1,X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_52]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_52]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:12:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.13/0.40  # and selection function SelectComplexG.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.044 s
% 0.13/0.40  
% 0.13/0.40  # No proof found!
% 0.13/0.40  # SZS status CounterSatisfiable
% 0.13/0.40  # SZS output start Saturation
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.13/0.40  fof(t18_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_pre_topc)).
% 0.13/0.40  fof(t25_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 0.13/0.40  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 0.13/0.40  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.13/0.40  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.13/0.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.13/0.40  fof(c_0_9, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  fof(c_0_10, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  cnf(c_0_11, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  fof(c_0_12, plain, ![X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|m1_subset_1(k3_subset_1(X8,X9),k1_zfmisc_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.13/0.40  cnf(c_0_13, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.40  cnf(c_0_14, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.40  fof(c_0_15, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k4_subset_1(u1_struct_0(X1),X2,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)))), inference(assume_negation,[status(cth)],[t18_pre_topc])).
% 0.13/0.40  fof(c_0_16, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|k4_subset_1(X16,X17,k3_subset_1(X16,X17))=k2_subset_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).
% 0.13/0.40  fof(c_0_17, plain, ![X15]:k2_subset_1(X15)=k3_subset_1(X15,k1_subset_1(X15)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.13/0.40  fof(c_0_18, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|k3_subset_1(X10,k3_subset_1(X10,X11))=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.13/0.40  cnf(c_0_19, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.40  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.13/0.40  fof(c_0_21, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))!=k2_struct_0(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.13/0.40  fof(c_0_22, plain, ![X12, X13, X14]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|~m1_subset_1(X14,k1_zfmisc_1(X12))|k4_subset_1(X12,X13,X14)=k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.13/0.40  cnf(c_0_23, plain, (k4_subset_1(X2,X1,k3_subset_1(X2,X1))=k2_subset_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_24, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_25, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.40  fof(c_0_26, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.13/0.40  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.40  cnf(c_0_28, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.40  cnf(c_0_30, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.13/0.40  cnf(c_0_31, plain, (k4_subset_1(X2,X1,k3_subset_1(X2,X1))=k3_subset_1(X2,k1_subset_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.40  cnf(c_0_32, plain, (k3_subset_1(X1,k3_subset_1(X1,X1))=X1), inference(spm,[status(thm)],[c_0_25, c_0_20]), ['final']).
% 0.13/0.40  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.13/0.40  cnf(c_0_34, plain, (r1_tarski(k3_subset_1(X1,X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_19, c_0_29]), ['final']).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_25, c_0_29]), ['final']).
% 0.13/0.40  cnf(c_0_37, plain, (k4_subset_1(X1,X2,X1)=k2_xboole_0(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_20]), ['final']).
% 0.13/0.40  cnf(c_0_38, plain, (k4_subset_1(X1,k3_subset_1(X1,X1),X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_32])).
% 0.13/0.40  cnf(c_0_39, plain, (k2_xboole_0(k3_subset_1(X1,X1),X1)=X1), inference(spm,[status(thm)],[c_0_33, c_0_34]), ['final']).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),k1_subset_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,esk2_0)=k2_xboole_0(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_30, c_0_29]), ['final']).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0)=k3_subset_1(u1_struct_0(esk1_0),k1_subset_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_35]), c_0_36])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_30, c_0_35]), ['final']).
% 0.13/0.40  cnf(c_0_45, plain, (k4_subset_1(X1,X2,k3_subset_1(X1,X1))=k2_xboole_0(X2,k3_subset_1(X1,X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_28]), ['final']).
% 0.13/0.40  cnf(c_0_46, plain, (k4_subset_1(X1,X1,k3_subset_1(X1,X1))=k3_subset_1(X1,k1_subset_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_20])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_35]), ['final']).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_29]), ['final']).
% 0.13/0.40  cnf(c_0_49, plain, (k3_subset_1(X1,k1_subset_1(X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_28]), c_0_38]), c_0_39]), ['final']).
% 0.13/0.40  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k1_subset_1(u1_struct_0(esk1_0)))!=k2_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.40  cnf(c_0_52, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_33, c_0_14]), ['final']).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0)=k3_subset_1(u1_struct_0(esk1_0),k1_subset_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_43])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (k2_xboole_0(esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),k1_subset_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_29]), c_0_41])).
% 0.13/0.40  cnf(c_0_55, plain, (k2_xboole_0(X1,k3_subset_1(X1,X1))=k3_subset_1(X1,k1_subset_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_20]), c_0_46])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_33, c_0_47]), ['final']).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (k2_xboole_0(esk2_0,u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_33, c_0_48]), ['final']).
% 0.13/0.40  cnf(c_0_58, plain, (k4_subset_1(X1,X2,k3_subset_1(X1,X2))=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_31, c_0_49]), ['final']).
% 0.13/0.40  cnf(c_0_59, plain, (k3_subset_1(X1,X1)=X1|~r1_tarski(X1,k3_subset_1(X1,X1))), inference(spm,[status(thm)],[c_0_50, c_0_34]), ['final']).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),esk2_0)=u1_struct_0(esk1_0)|~r1_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_47]), ['final']).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk1_0)=esk2_0|~r1_tarski(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_48]), ['final']).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (k2_struct_0(esk1_0)!=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_51, c_0_49]), ['final']).
% 0.13/0.40  cnf(c_0_63, plain, (k4_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1))=k3_subset_1(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_28]), c_0_52]), ['final']).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))=k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_45, c_0_35]), ['final']).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_44, c_0_28]), ['final']).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))=k2_xboole_0(esk2_0,k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_45, c_0_29]), ['final']).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_xboole_0(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_44, c_0_20]), ['final']).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0)=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_53, c_0_49]), ['final']).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_35]), c_0_52]), ['final']).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_41, c_0_49]), ['final']).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0)=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_43, c_0_49]), ['final']).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, (k2_xboole_0(esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_54, c_0_49]), ['final']).
% 0.13/0.40  cnf(c_0_73, plain, (k4_subset_1(X1,X1,k3_subset_1(X1,X1))=X1), inference(rw,[status(thm)],[c_0_46, c_0_49]), ['final']).
% 0.13/0.40  cnf(c_0_74, plain, (k4_subset_1(X1,k3_subset_1(X1,X1),X1)=X1), inference(rw,[status(thm)],[c_0_38, c_0_49]), ['final']).
% 0.13/0.40  cnf(c_0_75, plain, (k2_xboole_0(X1,k3_subset_1(X1,X1))=X1), inference(rw,[status(thm)],[c_0_55, c_0_49]), ['final']).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0)=k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_28]), ['final']).
% 0.13/0.40  cnf(c_0_77, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0)=k2_xboole_0(u1_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_20]), ['final']).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_35]), c_0_56]), ['final']).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_29]), c_0_57]), ['final']).
% 0.13/0.40  cnf(c_0_80, plain, (k4_subset_1(X1,X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_20]), c_0_52]), ['final']).
% 0.13/0.40  cnf(c_0_81, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_29]), c_0_52]), ['final']).
% 0.13/0.40  cnf(c_0_82, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.40  # SZS output end Saturation
% 0.13/0.40  # Proof object total steps             : 83
% 0.13/0.40  # Proof object clause steps            : 64
% 0.13/0.40  # Proof object formula steps           : 19
% 0.13/0.40  # Proof object conjectures             : 36
% 0.13/0.40  # Proof object clause conjectures      : 33
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 13
% 0.13/0.40  # Proof object initial formulas used   : 9
% 0.13/0.40  # Proof object generating inferences   : 39
% 0.13/0.40  # Proof object simplifying inferences  : 25
% 0.13/0.40  # Parsed axioms                        : 9
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 14
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 13
% 0.13/0.40  # Processed clauses                    : 64
% 0.13/0.40  # ...of these trivial                  : 1
% 0.13/0.40  # ...subsumed                          : 0
% 0.13/0.40  # ...remaining for further processing  : 63
% 0.13/0.40  # Other redundant clauses eliminated   : 2
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 0
% 0.13/0.40  # Backward-rewritten                   : 10
% 0.13/0.40  # Generated clauses                    : 53
% 0.13/0.40  # ...of the previous two non-trivial   : 51
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 51
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 2
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 51
% 0.13/0.40  #    Positive orientable unit clauses  : 35
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 1
% 0.13/0.40  #    Non-unit-clauses                  : 15
% 0.13/0.40  # Current number of unprocessed clauses: 0
% 0.13/0.40  # ...number of literals in the above   : 0
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 11
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 16
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 16
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.40  # Unit Clause-clause subsumption calls : 33
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 84
% 0.13/0.40  # BW rewrite match successes           : 3
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 1714
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.050 s
% 0.13/0.40  # System time              : 0.002 s
% 0.13/0.40  # Total time               : 0.052 s
% 0.13/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
