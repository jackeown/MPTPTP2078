%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:01 EST 2020

% Result     : Theorem 5.97s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :  186 (5983124041 expanded)
%              Number of clauses        :  169 (2662711748 expanded)
%              Number of leaves         :    8 (1617932598 expanded)
%              Depth                    :   59
%              Number of atoms          :  193 (6574953716 expanded)
%              Number of equality atoms :  184 (5898576944 expanded)
%              Maximal formula depth    :    6 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(c_0_8,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_9,plain,(
    ! [X18,X19] : k2_xboole_0(X18,X19) = k5_xboole_0(X18,k4_xboole_0(X19,X18)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

fof(c_0_11,plain,(
    ! [X8,X9] : k3_xboole_0(X8,k2_xboole_0(X8,X9)) = X8 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_12,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    & k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_16,plain,(
    ! [X12,X13,X14] : k3_xboole_0(X12,k4_xboole_0(X13,X14)) = k4_xboole_0(k3_xboole_0(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_17,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_14]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k5_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_19]),c_0_19])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19]),c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X15,X16,X17] : k4_xboole_0(X15,k4_xboole_0(X16,X17)) = k2_xboole_0(k4_xboole_0(X15,X16),k3_xboole_0(X15,X17)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X3) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1))) = k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,X1),X2))) = k4_xboole_0(k4_xboole_0(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_14]),c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1))) = k4_xboole_0(k4_xboole_0(esk3_0,esk3_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_33]),c_0_34])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2))))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1)) = k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3))) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0))) = k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)),X2) = k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk3_0)) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,X1))) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0)) = k4_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_43]),c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_44]),c_0_26]),c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_44]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_46]),c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,X2)))) = k4_xboole_0(esk3_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_47]),c_0_37]),c_0_26])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk3_0,k5_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0))) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,X1),X2))) = k4_xboole_0(k4_xboole_0(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_48]),c_0_26]),c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_24]),c_0_47]),c_0_50])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,esk3_0)) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,X1)) = k4_xboole_0(k4_xboole_0(esk3_0,X1),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,X1),X1)) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_55]),c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),X1) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_56]),c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(esk3_0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X2,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_57]),c_0_37])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_58]),c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(esk3_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_59]),c_0_37]),c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,X1),X2)) = k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,X1),X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_48]),c_0_37])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0) = k4_xboole_0(k4_xboole_0(esk3_0,X1),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_44]),c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k4_xboole_0(esk3_0,k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_24])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(esk3_0,esk3_0),k4_xboole_0(esk3_0,X1)) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_54]),c_0_45]),c_0_45])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk2_0,X2))) = k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk3_0,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_61]),c_0_37])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk2_0,X2)) = k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_62]),c_0_37])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,esk3_0),k4_xboole_0(esk3_0,X1))) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_54]),c_0_64]),c_0_54]),c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,esk3_0)))) = k4_xboole_0(esk3_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_47]),c_0_49])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk2_0,X2)),X3)) = k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk3_0,X2)),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_66]),c_0_37])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),esk3_0) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_57]),c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(k4_xboole_0(esk2_0,X2),X3)) = k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(k4_xboole_0(esk3_0,X2),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_67]),c_0_37])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,esk3_0),X1)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_27]),c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,X1)) = k4_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_48]),c_0_61]),c_0_72]),c_0_49]),c_0_55]),c_0_71]),c_0_49]),c_0_26]),c_0_45])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_27]),c_0_49])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,X1)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X2,X2))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_76]),c_0_47])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,esk3_0),X1) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(X1,X1),X2)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_77]),c_0_46]),c_0_78]),c_0_75]),c_0_26]),c_0_45])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X2)))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_27])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_26]),c_0_26])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_53])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)))) = k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))) = k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_75])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X3))) = k4_xboole_0(k4_xboole_0(X1,X1),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0)) = k4_xboole_0(X1,k4_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_83]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_63,c_0_76])).

cnf(c_0_88,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1)))))) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_26])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))) = k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_58])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(esk3_0,esk3_0)) = k4_xboole_0(k4_xboole_0(X1,X1),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_85]),c_0_87])).

cnf(c_0_91,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X1))))))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_27])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_27])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(esk3_0,X2)) = k4_xboole_0(k4_xboole_0(X1,X1),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_90]),c_0_37]),c_0_78]),c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k4_xboole_0(X1,X1),esk3_0)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_77]),c_0_92]),c_0_93])).

cnf(c_0_95,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_94]),c_0_93]),c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk3_0,X1),X2)) = k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_86]),c_0_37]),c_0_78])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0))) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_75])).

cnf(c_0_98,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X2))) = k4_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_95]),c_0_95]),c_0_95]),c_0_95]),c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(esk3_0,X1),X2),X3)) = k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_96]),c_0_37]),c_0_78])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(esk3_0,esk3_0)) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(esk3_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_96]),c_0_97])).

cnf(c_0_101,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X4))) = k4_xboole_0(k4_xboole_0(X1,X3),X4) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_102,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(esk3_0,X1),X3))) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(esk3_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_99]),c_0_97]),c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_95]),c_0_95])).

cnf(c_0_106,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_75])).

cnf(c_0_107,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_105,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_103]),c_0_67]),c_0_45]),c_0_55]),c_0_71]),c_0_26]),c_0_45])).

cnf(c_0_110,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,X1)))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_51]),c_0_45]),c_0_71])).

cnf(c_0_111,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_27])).

cnf(c_0_112,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X3) = k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_95]),c_0_39])).

cnf(c_0_113,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_109]),c_0_110]),c_0_51])).

cnf(c_0_115,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),X3) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_108])).

cnf(c_0_116,negated_conjecture,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113]),c_0_24])).

cnf(c_0_117,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_27])).

cnf(c_0_118,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk3_0,X1)),X2) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_115,c_0_86])).

cnf(c_0_119,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_24,c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,X2)))) = k4_xboole_0(X1,k4_xboole_0(esk3_0,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_111]),c_0_37]),c_0_26])).

cnf(c_0_121,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(X2,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_27]),c_0_26]),c_0_49])).

cnf(c_0_122,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X2,esk3_0))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_75]),c_0_47])).

cnf(c_0_123,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(esk3_0,X1),X3)) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_103]),c_0_101])).

cnf(c_0_124,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk3_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_118]),c_0_120]),c_0_102]),c_0_119]),c_0_119])).

cnf(c_0_125,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_121]),c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(esk3_0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_123,c_0_113])).

cnf(c_0_127,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(esk3_0,X1))) = k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_77])).

cnf(c_0_128,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126]),c_0_102]),c_0_119])).

cnf(c_0_129,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_119]),c_0_119])).

cnf(c_0_130,negated_conjecture,
    ( k5_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_119]),c_0_127]),c_0_95]),c_0_119])).

cnf(c_0_131,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_128]),c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_130,c_0_108])).

cnf(c_0_133,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_45])).

cnf(c_0_134,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_116]),c_0_37])).

cnf(c_0_135,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_26]),c_0_26]),c_0_37])).

cnf(c_0_136,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_116]),c_0_26]),c_0_39])).

cnf(c_0_137,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_128]),c_0_102]),c_0_132])).

cnf(c_0_138,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_128,c_0_128])).

cnf(c_0_139,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k5_xboole_0(esk2_0,k4_xboole_0(X1,esk2_0)))) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_28])).

cnf(c_0_140,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)),k4_xboole_0(esk3_0,X1)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_133]),c_0_45]),c_0_55]),c_0_71]),c_0_49]),c_0_76])).

cnf(c_0_141,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_134]),c_0_134]),c_0_136]),c_0_101])).

cnf(c_0_142,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_137]),c_0_132])).

cnf(c_0_143,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_138]),c_0_128]),c_0_132])).

cnf(c_0_144,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_128,c_0_137])).

cnf(c_0_145,negated_conjecture,
    ( k4_xboole_0(esk3_0,k5_xboole_0(esk2_0,k4_xboole_0(X1,esk2_0))) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_139])).

cnf(c_0_146,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)),k4_xboole_0(esk3_0,X1)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_140,c_0_27])).

cnf(c_0_147,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_141,c_0_27])).

cnf(c_0_148,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_53])).

cnf(c_0_149,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X1))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_150,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_137]),c_0_138]),c_0_132])).

cnf(c_0_151,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_75])).

cnf(c_0_152,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))) = k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_48]),c_0_53]),c_0_31])).

cnf(c_0_153,negated_conjecture,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3))) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_144])).

cnf(c_0_154,negated_conjecture,
    ( k4_xboole_0(esk3_0,k5_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(X1,esk2_0),X2))) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_144])).

cnf(c_0_155,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,X1),esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_95]),c_0_95]),c_0_76])).

cnf(c_0_156,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_157,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_149,c_0_27])).

cnf(c_0_158,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_150]),c_0_141])).

cnf(c_0_159,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_150]),c_0_148])).

cnf(c_0_160,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X2),X4)) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_150]),c_0_37])).

cnf(c_0_161,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,esk2_0),k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))) = k4_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_151])).

cnf(c_0_162,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(esk3_0,X2)) = k4_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_108])).

cnf(c_0_163,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_164,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_148]),c_0_148])).

cnf(c_0_165,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(X1,esk2_0),X2)),esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154]),c_0_75]),c_0_155])).

cnf(c_0_166,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_156]),c_0_157]),c_0_158]),c_0_159]),c_0_160]),c_0_157])).

cnf(c_0_167,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X4,X1)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_142]),c_0_148])).

cnf(c_0_168,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk2_0,esk3_0)) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_104]),c_0_27]),c_0_48]),c_0_45]),c_0_162])).

cnf(c_0_169,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_163,c_0_14]),c_0_19])).

cnf(c_0_170,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_164,c_0_165])).

cnf(c_0_171,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4))),k4_xboole_0(X4,X2)) = k4_xboole_0(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_142]),c_0_166]),c_0_159])).

cnf(c_0_172,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_27]),c_0_167])).

cnf(c_0_173,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0)))) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_168]),c_0_48])).

cnf(c_0_174,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)),k4_xboole_0(esk1_0,esk2_0))) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_169,c_0_27])).

cnf(c_0_175,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))) = k4_xboole_0(k4_xboole_0(X1,X2),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_170]),c_0_157])).

cnf(c_0_176,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X2,X4)) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_172]),c_0_104]),c_0_129])).

cnf(c_0_177,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,X4))))) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_148]),c_0_148])).

cnf(c_0_178,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X2))),esk2_0) = k4_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_141,c_0_173])).

cnf(c_0_179,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))))) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_174,c_0_26]),c_0_27])).

cnf(c_0_180,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_131,c_0_27])).

cnf(c_0_181,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk2_0,X2)) = k4_xboole_0(X1,k4_xboole_0(esk2_0,k4_xboole_0(X2,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_176]),c_0_177]),c_0_166])).

cnf(c_0_182,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),esk2_0) = k4_xboole_0(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_116]),c_0_75])).

cnf(c_0_183,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,esk1_0))) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_179,c_0_53]),c_0_33])).

cnf(c_0_184,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,X1))) = k4_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_181]),c_0_182])).

cnf(c_0_185,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_183,c_0_184])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:08:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 5.97/6.19  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 5.97/6.19  # and selection function SelectNewComplexAHP.
% 5.97/6.19  #
% 5.97/6.19  # Preprocessing time       : 0.026 s
% 5.97/6.19  
% 5.97/6.19  # Proof found!
% 5.97/6.19  # SZS status Theorem
% 5.97/6.19  # SZS output start CNFRefutation
% 5.97/6.19  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.97/6.19  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.97/6.19  fof(t117_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 5.97/6.19  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.97/6.19  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.97/6.19  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.97/6.19  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.97/6.19  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 5.97/6.19  fof(c_0_8, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 5.97/6.19  fof(c_0_9, plain, ![X18, X19]:k2_xboole_0(X18,X19)=k5_xboole_0(X18,k4_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 5.97/6.19  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t117_xboole_1])).
% 5.97/6.19  fof(c_0_11, plain, ![X8, X9]:k3_xboole_0(X8,k2_xboole_0(X8,X9))=X8, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 5.97/6.19  fof(c_0_12, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 5.97/6.19  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 5.97/6.19  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 5.97/6.19  fof(c_0_15, negated_conjecture, (r1_tarski(esk3_0,esk2_0)&k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 5.97/6.19  fof(c_0_16, plain, ![X12, X13, X14]:k3_xboole_0(X12,k4_xboole_0(X13,X14))=k4_xboole_0(k3_xboole_0(X12,X13),X14), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 5.97/6.19  fof(c_0_17, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 5.97/6.19  cnf(c_0_18, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.97/6.19  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.97/6.19  cnf(c_0_20, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 5.97/6.19  cnf(c_0_21, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.97/6.19  cnf(c_0_22, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.97/6.19  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.97/6.19  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_14]), c_0_19])).
% 5.97/6.19  cnf(c_0_25, negated_conjecture, (k5_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk3_0))=esk2_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 5.97/6.19  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_19]), c_0_19])).
% 5.97/6.19  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_19]), c_0_19])).
% 5.97/6.19  cnf(c_0_28, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))=esk3_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 5.97/6.19  fof(c_0_29, plain, ![X15, X16, X17]:k4_xboole_0(X15,k4_xboole_0(X16,X17))=k2_xboole_0(k4_xboole_0(X15,X16),k3_xboole_0(X15,X17)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 5.97/6.19  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),X3)=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 5.97/6.19  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)))=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_28])).
% 5.97/6.19  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 5.97/6.19  cnf(c_0_33, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1)))=k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 5.97/6.19  cnf(c_0_34, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,X1),X2)))=k4_xboole_0(k4_xboole_0(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 5.97/6.19  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_14]), c_0_19])).
% 5.97/6.19  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1)))=k4_xboole_0(k4_xboole_0(esk3_0,esk3_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_33]), c_0_34])).
% 5.97/6.19  cnf(c_0_37, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2)))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_35, c_0_26])).
% 5.97/6.19  cnf(c_0_38, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1))=k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 5.97/6.19  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3)))=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 5.97/6.19  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0)))=k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_37])).
% 5.97/6.19  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)),X2)=k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_26]), c_0_31])).
% 5.97/6.19  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk3_0))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_39])).
% 5.97/6.19  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,X1)))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_26])).
% 5.97/6.19  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0))=k4_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_43]), c_0_37])).
% 5.97/6.19  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_44]), c_0_26]), c_0_31])).
% 5.97/6.19  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=k4_xboole_0(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_44]), c_0_39])).
% 5.97/6.19  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)))=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_27])).
% 5.97/6.19  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_46]), c_0_37])).
% 5.97/6.19  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,X2))))=k4_xboole_0(esk3_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_47]), c_0_37]), c_0_26])).
% 5.97/6.19  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk3_0,k5_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0)))=k4_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_24])).
% 5.97/6.19  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,X1),X2)))=k4_xboole_0(k4_xboole_0(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_48]), c_0_26]), c_0_34])).
% 5.97/6.19  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0)))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_24]), c_0_47]), c_0_50])).
% 5.97/6.19  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_26])).
% 5.97/6.19  cnf(c_0_54, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,esk3_0))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_45])).
% 5.97/6.19  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,X1))=k4_xboole_0(k4_xboole_0(esk3_0,X1),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_51])).
% 5.97/6.19  cnf(c_0_56, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,X1),X1))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_55]), c_0_47])).
% 5.97/6.19  cnf(c_0_57, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),X1)=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_56]), c_0_45])).
% 5.97/6.19  cnf(c_0_58, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(esk3_0,k4_xboole_0(X1,X2))))=k4_xboole_0(X1,k4_xboole_0(X2,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_57]), c_0_37])).
% 5.97/6.19  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_58]), c_0_47])).
% 5.97/6.19  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k4_xboole_0(esk3_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_59]), c_0_37]), c_0_26])).
% 5.97/6.19  cnf(c_0_61, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,X1),X2))=k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,X1),X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_48]), c_0_37])).
% 5.97/6.19  cnf(c_0_62, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0)=k4_xboole_0(k4_xboole_0(esk3_0,X1),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_44]), c_0_34])).
% 5.97/6.19  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k4_xboole_0(esk3_0,k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_60, c_0_24])).
% 5.97/6.19  cnf(c_0_64, negated_conjecture, (k5_xboole_0(k4_xboole_0(esk3_0,esk3_0),k4_xboole_0(esk3_0,X1))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_54]), c_0_45]), c_0_45])).
% 5.97/6.19  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_28, c_0_44])).
% 5.97/6.19  cnf(c_0_66, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk2_0,X2)))=k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk3_0,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_61]), c_0_37])).
% 5.97/6.19  cnf(c_0_67, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk2_0,X2))=k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_62]), c_0_37])).
% 5.97/6.19  cnf(c_0_68, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,esk3_0),k4_xboole_0(esk3_0,X1)))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_54]), c_0_64]), c_0_54]), c_0_65])).
% 5.97/6.19  cnf(c_0_69, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,esk3_0))))=k4_xboole_0(esk3_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_47]), c_0_49])).
% 5.97/6.19  cnf(c_0_70, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk2_0,X2)),X3))=k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk3_0,X2)),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_66]), c_0_37])).
% 5.97/6.19  cnf(c_0_71, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),esk3_0)=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_57]), c_0_55])).
% 5.97/6.19  cnf(c_0_72, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(k4_xboole_0(esk2_0,X2),X3))=k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(k4_xboole_0(esk3_0,X2),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_67]), c_0_37])).
% 5.97/6.19  cnf(c_0_73, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk3_0,esk3_0),X1))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_27]), c_0_69])).
% 5.97/6.19  cnf(c_0_74, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,X1))=k4_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_48]), c_0_61]), c_0_72]), c_0_49]), c_0_55]), c_0_71]), c_0_49]), c_0_26]), c_0_45])).
% 5.97/6.19  cnf(c_0_75, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_27]), c_0_49])).
% 5.97/6.19  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,X1))=esk3_0), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 5.97/6.19  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X2,X2)))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_76]), c_0_47])).
% 5.97/6.19  cnf(c_0_78, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,esk3_0),X1)=k4_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_73])).
% 5.97/6.19  cnf(c_0_79, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(X1,X1),X2))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_77]), c_0_46]), c_0_78]), c_0_75]), c_0_26]), c_0_45])).
% 5.97/6.19  cnf(c_0_80, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X2))))=esk3_0), inference(spm,[status(thm)],[c_0_79, c_0_27])).
% 5.97/6.19  cnf(c_0_81, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))=k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_26]), c_0_26])).
% 5.97/6.19  cnf(c_0_82, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))=esk3_0), inference(spm,[status(thm)],[c_0_80, c_0_53])).
% 5.97/6.19  cnf(c_0_83, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))))=k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 5.97/6.19  cnf(c_0_84, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)))=k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_75])).
% 5.97/6.19  cnf(c_0_85, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X3)))=k4_xboole_0(k4_xboole_0(X1,X1),X3)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 5.97/6.19  cnf(c_0_86, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0))=k4_xboole_0(X1,k4_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_83]), c_0_84])).
% 5.97/6.19  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=esk3_0), inference(rw,[status(thm)],[c_0_63, c_0_76])).
% 5.97/6.19  cnf(c_0_88, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1))))))=X1), inference(spm,[status(thm)],[c_0_24, c_0_26])).
% 5.97/6.19  cnf(c_0_89, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)))=k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_58])).
% 5.97/6.19  cnf(c_0_90, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(esk3_0,esk3_0))=k4_xboole_0(k4_xboole_0(X1,X1),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_85]), c_0_87])).
% 5.97/6.19  cnf(c_0_91, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_88, c_0_27])).
% 5.97/6.19  cnf(c_0_92, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_89, c_0_27])).
% 5.97/6.19  cnf(c_0_93, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(esk3_0,X2))=k4_xboole_0(k4_xboole_0(X1,X1),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_90]), c_0_37]), c_0_78]), c_0_90])).
% 5.97/6.19  cnf(c_0_94, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k4_xboole_0(X1,X1),esk3_0))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_77]), c_0_92]), c_0_93])).
% 5.97/6.19  cnf(c_0_95, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_94]), c_0_93]), c_0_94])).
% 5.97/6.19  cnf(c_0_96, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk3_0,X1),X2))=k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_86]), c_0_37]), c_0_78])).
% 5.97/6.19  cnf(c_0_97, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0)))=k4_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_75])).
% 5.97/6.19  cnf(c_0_98, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X2)))=k4_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_95]), c_0_95]), c_0_95]), c_0_95]), c_0_95])).
% 5.97/6.19  cnf(c_0_99, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(esk3_0,X1),X2),X3))=k4_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_96]), c_0_37]), c_0_78])).
% 5.97/6.19  cnf(c_0_100, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(esk3_0,esk3_0))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(esk3_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_96]), c_0_97])).
% 5.97/6.19  cnf(c_0_101, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X4)))=k4_xboole_0(k4_xboole_0(X1,X3),X4)), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 5.97/6.19  cnf(c_0_102, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_53, c_0_98])).
% 5.97/6.19  cnf(c_0_103, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(esk3_0,X1),X3)))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(esk3_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_99]), c_0_97]), c_0_100])).
% 5.97/6.19  cnf(c_0_104, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 5.97/6.19  cnf(c_0_105, negated_conjecture, (k4_xboole_0(X1,X1)=k4_xboole_0(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_95]), c_0_95])).
% 5.97/6.19  cnf(c_0_106, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_103, c_0_75])).
% 5.97/6.19  cnf(c_0_107, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X1))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_27, c_0_104])).
% 5.97/6.19  cnf(c_0_108, negated_conjecture, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_105, c_0_105])).
% 5.97/6.19  cnf(c_0_109, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_103]), c_0_67]), c_0_45]), c_0_55]), c_0_71]), c_0_26]), c_0_45])).
% 5.97/6.19  cnf(c_0_110, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,X1))))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_51]), c_0_45]), c_0_71])).
% 5.97/6.19  cnf(c_0_111, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)))=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_106, c_0_27])).
% 5.97/6.19  cnf(c_0_112, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X3)=k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_95]), c_0_39])).
% 5.97/6.19  cnf(c_0_113, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 5.97/6.19  cnf(c_0_114, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(X1,X2))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_109]), c_0_110]), c_0_51])).
% 5.97/6.19  cnf(c_0_115, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),X3)=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_26, c_0_108])).
% 5.97/6.19  cnf(c_0_116, negated_conjecture, (k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113]), c_0_24])).
% 5.97/6.19  cnf(c_0_117, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_114, c_0_27])).
% 5.97/6.19  cnf(c_0_118, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk3_0,X1)),X2)=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_115, c_0_86])).
% 5.97/6.19  cnf(c_0_119, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_24, c_0_116])).
% 5.97/6.19  cnf(c_0_120, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,X2))))=k4_xboole_0(X1,k4_xboole_0(esk3_0,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_111]), c_0_37]), c_0_26])).
% 5.97/6.19  cnf(c_0_121, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(X2,X1))))=k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_27]), c_0_26]), c_0_49])).
% 5.97/6.19  cnf(c_0_122, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X2,esk3_0)))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_75]), c_0_47])).
% 5.97/6.19  cnf(c_0_123, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(esk3_0,X1),X3))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_103]), c_0_101])).
% 5.97/6.19  cnf(c_0_124, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk3_0,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_118]), c_0_120]), c_0_102]), c_0_119]), c_0_119])).
% 5.97/6.19  cnf(c_0_125, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_121]), c_0_122])).
% 5.97/6.19  cnf(c_0_126, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(esk3_0,X1))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_123, c_0_113])).
% 5.97/6.19  cnf(c_0_127, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(esk3_0,X1)))=k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_77])).
% 5.97/6.19  cnf(c_0_128, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_126]), c_0_102]), c_0_119])).
% 5.97/6.19  cnf(c_0_129, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_119]), c_0_119])).
% 5.97/6.19  cnf(c_0_130, negated_conjecture, (k5_xboole_0(X1,k4_xboole_0(esk3_0,esk3_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_119]), c_0_127]), c_0_95]), c_0_119])).
% 5.97/6.19  cnf(c_0_131, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_128]), c_0_129])).
% 5.97/6.19  cnf(c_0_132, negated_conjecture, (k5_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_130, c_0_108])).
% 5.97/6.19  cnf(c_0_133, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_45])).
% 5.97/6.19  cnf(c_0_134, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_116]), c_0_37])).
% 5.97/6.19  cnf(c_0_135, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_26]), c_0_26]), c_0_37])).
% 5.97/6.19  cnf(c_0_136, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_116]), c_0_26]), c_0_39])).
% 5.97/6.19  cnf(c_0_137, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_128]), c_0_102]), c_0_132])).
% 5.97/6.19  cnf(c_0_138, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_128, c_0_128])).
% 5.97/6.19  cnf(c_0_139, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k5_xboole_0(esk2_0,k4_xboole_0(X1,esk2_0))))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_28])).
% 5.97/6.19  cnf(c_0_140, negated_conjecture, (k5_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)),k4_xboole_0(esk3_0,X1))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_133]), c_0_45]), c_0_55]), c_0_71]), c_0_49]), c_0_76])).
% 5.97/6.19  cnf(c_0_141, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_134]), c_0_134]), c_0_136]), c_0_101])).
% 5.97/6.19  cnf(c_0_142, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_137]), c_0_132])).
% 5.97/6.19  cnf(c_0_143, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_138]), c_0_128]), c_0_132])).
% 5.97/6.19  cnf(c_0_144, negated_conjecture, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_128, c_0_137])).
% 5.97/6.19  cnf(c_0_145, negated_conjecture, (k4_xboole_0(esk3_0,k5_xboole_0(esk2_0,k4_xboole_0(X1,esk2_0)))=k4_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_139])).
% 5.97/6.19  cnf(c_0_146, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)),k4_xboole_0(esk3_0,X1))=esk3_0), inference(spm,[status(thm)],[c_0_140, c_0_27])).
% 5.97/6.19  cnf(c_0_147, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3)=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_141, c_0_27])).
% 5.97/6.19  cnf(c_0_148, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_136, c_0_53])).
% 5.97/6.19  cnf(c_0_149, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X1)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_142, c_0_143])).
% 5.97/6.19  cnf(c_0_150, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_137]), c_0_138]), c_0_132])).
% 5.97/6.19  cnf(c_0_151, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,esk2_0))=esk3_0), inference(rw,[status(thm)],[c_0_44, c_0_75])).
% 5.97/6.19  cnf(c_0_152, negated_conjecture, (k5_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))=k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_48]), c_0_53]), c_0_31])).
% 5.97/6.19  cnf(c_0_153, negated_conjecture, (k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3)))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_116, c_0_144])).
% 5.97/6.19  cnf(c_0_154, negated_conjecture, (k4_xboole_0(esk3_0,k5_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(X1,esk2_0),X2)))=k4_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_145, c_0_144])).
% 5.97/6.19  cnf(c_0_155, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,X1),esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_95]), c_0_95]), c_0_76])).
% 5.97/6.19  cnf(c_0_156, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_147, c_0_148])).
% 5.97/6.19  cnf(c_0_157, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_149, c_0_27])).
% 5.97/6.19  cnf(c_0_158, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_150]), c_0_141])).
% 5.97/6.19  cnf(c_0_159, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X4,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_150]), c_0_148])).
% 5.97/6.19  cnf(c_0_160, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X2),X4))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_150]), c_0_37])).
% 5.97/6.19  cnf(c_0_161, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,esk2_0),k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)))=k4_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_151])).
% 5.97/6.19  cnf(c_0_162, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(esk3_0,X2))=k4_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_64, c_0_108])).
% 5.97/6.19  cnf(c_0_163, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.97/6.19  cnf(c_0_164, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X2,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_148]), c_0_148])).
% 5.97/6.19  cnf(c_0_165, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(k4_xboole_0(X1,esk2_0),X2)),esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_154]), c_0_75]), c_0_155])).
% 5.97/6.19  cnf(c_0_166, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_156]), c_0_157]), c_0_158]), c_0_159]), c_0_160]), c_0_157])).
% 5.97/6.20  cnf(c_0_167, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X4,X1))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_142]), c_0_148])).
% 5.97/6.20  cnf(c_0_168, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk2_0,esk3_0))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_104]), c_0_27]), c_0_48]), c_0_45]), c_0_162])).
% 5.97/6.20  cnf(c_0_169, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_163, c_0_14]), c_0_19])).
% 5.97/6.20  cnf(c_0_170, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)))=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_164, c_0_165])).
% 5.97/6.20  cnf(c_0_171, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4))),k4_xboole_0(X4,X2))=k4_xboole_0(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_142]), c_0_166]), c_0_159])).
% 5.97/6.20  cnf(c_0_172, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_27]), c_0_167])).
% 5.97/6.20  cnf(c_0_173, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0))))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_168]), c_0_48])).
% 5.97/6.20  cnf(c_0_174, negated_conjecture, (k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)),k4_xboole_0(esk1_0,esk2_0)))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_169, c_0_27])).
% 5.97/6.20  cnf(c_0_175, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)))=k4_xboole_0(k4_xboole_0(X1,X2),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_170]), c_0_157])).
% 5.97/6.20  cnf(c_0_176, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X2,X4))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_172]), c_0_104]), c_0_129])).
% 5.97/6.20  cnf(c_0_177, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,X4)))))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_148]), c_0_148])).
% 5.97/6.20  cnf(c_0_178, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X2))),esk2_0)=k4_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_141, c_0_173])).
% 5.97/6.20  cnf(c_0_179, negated_conjecture, (k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)))))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_174, c_0_26]), c_0_27])).
% 5.97/6.20  cnf(c_0_180, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_131, c_0_27])).
% 5.97/6.20  cnf(c_0_181, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk2_0,X2))=k4_xboole_0(X1,k4_xboole_0(esk2_0,k4_xboole_0(X2,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_176]), c_0_177]), c_0_166])).
% 5.97/6.20  cnf(c_0_182, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),esk2_0)=k4_xboole_0(X1,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_116]), c_0_75])).
% 5.97/6.20  cnf(c_0_183, negated_conjecture, (k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,esk1_0)))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_179, c_0_53]), c_0_33])).
% 5.97/6.20  cnf(c_0_184, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,X1)))=k4_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_181]), c_0_182])).
% 5.97/6.20  cnf(c_0_185, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_183, c_0_184])]), ['proof']).
% 5.97/6.20  # SZS output end CNFRefutation
% 5.97/6.20  # Proof object total steps             : 186
% 5.97/6.20  # Proof object clause steps            : 169
% 5.97/6.20  # Proof object formula steps           : 17
% 5.97/6.20  # Proof object conjectures             : 150
% 5.97/6.20  # Proof object clause conjectures      : 147
% 5.97/6.20  # Proof object formula conjectures     : 3
% 5.97/6.20  # Proof object initial clauses used    : 9
% 5.97/6.20  # Proof object initial formulas used   : 8
% 5.97/6.20  # Proof object generating inferences   : 144
% 5.97/6.20  # Proof object simplifying inferences  : 190
% 5.97/6.20  # Training examples: 0 positive, 0 negative
% 5.97/6.20  # Parsed axioms                        : 8
% 5.97/6.20  # Removed by relevancy pruning/SinE    : 0
% 5.97/6.20  # Initial clauses                      : 9
% 5.97/6.20  # Removed in clause preprocessing      : 2
% 5.97/6.20  # Initial clauses in saturation        : 7
% 5.97/6.20  # Processed clauses                    : 15265
% 5.97/6.20  # ...of these trivial                  : 2028
% 5.97/6.20  # ...subsumed                          : 12348
% 5.97/6.20  # ...remaining for further processing  : 889
% 5.97/6.20  # Other redundant clauses eliminated   : 0
% 5.97/6.20  # Clauses deleted for lack of memory   : 0
% 5.97/6.20  # Backward-subsumed                    : 2
% 5.97/6.20  # Backward-rewritten                   : 488
% 5.97/6.20  # Generated clauses                    : 579225
% 5.97/6.20  # ...of the previous two non-trivial   : 351440
% 5.97/6.20  # Contextual simplify-reflections      : 0
% 5.97/6.20  # Paramodulations                      : 579225
% 5.97/6.20  # Factorizations                       : 0
% 5.97/6.20  # Equation resolutions                 : 0
% 5.97/6.20  # Propositional unsat checks           : 0
% 5.97/6.20  #    Propositional check models        : 0
% 5.97/6.20  #    Propositional check unsatisfiable : 0
% 5.97/6.20  #    Propositional clauses             : 0
% 5.97/6.20  #    Propositional clauses after purity: 0
% 5.97/6.20  #    Propositional unsat core size     : 0
% 5.97/6.20  #    Propositional preprocessing time  : 0.000
% 5.97/6.20  #    Propositional encoding time       : 0.000
% 5.97/6.20  #    Propositional solver time         : 0.000
% 5.97/6.20  #    Success case prop preproc time    : 0.000
% 5.97/6.20  #    Success case prop encoding time   : 0.000
% 5.97/6.20  #    Success case prop solver time     : 0.000
% 5.97/6.20  # Current number of processed clauses  : 399
% 5.97/6.20  #    Positive orientable unit clauses  : 355
% 5.97/6.20  #    Positive unorientable unit clauses: 43
% 5.97/6.20  #    Negative unit clauses             : 0
% 5.97/6.20  #    Non-unit-clauses                  : 1
% 5.97/6.20  # Current number of unprocessed clauses: 294475
% 5.97/6.20  # ...number of literals in the above   : 294475
% 5.97/6.20  # Current number of archived formulas  : 0
% 5.97/6.20  # Current number of archived clauses   : 492
% 5.97/6.20  # Clause-clause subsumption calls (NU) : 0
% 5.97/6.20  # Rec. Clause-clause subsumption calls : 0
% 5.97/6.20  # Non-unit clause-clause subsumptions  : 0
% 5.97/6.20  # Unit Clause-clause subsumption calls : 2455
% 5.97/6.20  # Rewrite failures with RHS unbound    : 920
% 5.97/6.20  # BW rewrite match attempts            : 37613
% 5.97/6.20  # BW rewrite match successes           : 1879
% 5.97/6.20  # Condensation attempts                : 0
% 5.97/6.20  # Condensation successes               : 0
% 5.97/6.20  # Termbank termtop insertions          : 14512434
% 6.04/6.22  
% 6.04/6.22  # -------------------------------------------------
% 6.04/6.22  # User time                : 5.615 s
% 6.04/6.22  # System time              : 0.254 s
% 6.04/6.22  # Total time               : 5.869 s
% 6.04/6.22  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
