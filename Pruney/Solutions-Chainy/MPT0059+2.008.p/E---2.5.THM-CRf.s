%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:24 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   79 (7291 expanded)
%              Number of clauses        :   60 (3420 expanded)
%              Number of leaves         :    9 (1935 expanded)
%              Depth                    :   23
%              Number of atoms          :   83 (8423 expanded)
%              Number of equality atoms :   71 (6396 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t52_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | X14 = k2_xboole_0(X13,k4_xboole_0(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_10,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_11,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_14,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),X9) = k4_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X19,X20,X21] : k3_xboole_0(X19,k4_xboole_0(X20,X21)) = k4_xboole_0(k3_xboole_0(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_18,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X10,X11,X12] : k4_xboole_0(k4_xboole_0(X10,X11),X12) = k4_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k3_xboole_0(X15,X16)) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_24])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_26])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_28])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_32]),c_0_20])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_19]),c_0_12])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_37]),c_0_26]),c_0_38]),c_0_30])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_26])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_41])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_42]),c_0_42])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_20])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X2),X3)) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_42])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X2,X3))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_26])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_48]),c_0_20])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X4))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_31]),c_0_31]),c_0_26]),c_0_33])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X2),X3)),X3) = k4_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_49]),c_0_49])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X2),X1),X3)) = X1 ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_51])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_26]),c_0_33]),c_0_49])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X2),k2_xboole_0(X3,X2)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_54]),c_0_26]),c_0_26]),c_0_12]),c_0_30]),c_0_40]),c_0_26]),c_0_12]),c_0_55])).

cnf(c_0_58,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_26])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_49]),c_0_41]),c_0_38]),c_0_49])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_12]),c_0_36])).

cnf(c_0_61,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_60])).

fof(c_0_63,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t52_xboole_1])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_59])).

fof(c_0_66,negated_conjecture,(
    k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_63])])])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_64])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_12]),c_0_65])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_31])).

cnf(c_0_70,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1)))) = k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_36]),c_0_68])).

cnf(c_0_74,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_20])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_72,c_0_23])).

cnf(c_0_76,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_59])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_26]),c_0_77]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.78/0.94  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.78/0.94  # and selection function SelectNewComplexAHP.
% 0.78/0.94  #
% 0.78/0.94  # Preprocessing time       : 0.026 s
% 0.78/0.94  # Presaturation interreduction done
% 0.78/0.94  
% 0.78/0.94  # Proof found!
% 0.78/0.94  # SZS status Theorem
% 0.78/0.94  # SZS output start CNFRefutation
% 0.78/0.94  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 0.78/0.94  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.78/0.94  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.78/0.94  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.78/0.94  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.78/0.94  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.78/0.94  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.78/0.94  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.78/0.94  fof(t52_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.78/0.94  fof(c_0_9, plain, ![X13, X14]:(~r1_tarski(X13,X14)|X14=k2_xboole_0(X13,k4_xboole_0(X14,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 0.78/0.94  fof(c_0_10, plain, ![X6, X7]:k2_xboole_0(X6,k4_xboole_0(X7,X6))=k2_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.78/0.94  cnf(c_0_11, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.78/0.94  cnf(c_0_12, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.78/0.94  fof(c_0_13, plain, ![X4, X5]:r1_tarski(k4_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.78/0.94  fof(c_0_14, plain, ![X8, X9]:k4_xboole_0(k2_xboole_0(X8,X9),X9)=k4_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.78/0.94  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.78/0.94  cnf(c_0_16, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.78/0.94  fof(c_0_17, plain, ![X19, X20, X21]:k3_xboole_0(X19,k4_xboole_0(X20,X21))=k4_xboole_0(k3_xboole_0(X19,X20),X21), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.78/0.94  fof(c_0_18, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.78/0.94  cnf(c_0_19, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.78/0.94  cnf(c_0_20, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.78/0.94  fof(c_0_21, plain, ![X10, X11, X12]:k4_xboole_0(k4_xboole_0(X10,X11),X12)=k4_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.78/0.94  cnf(c_0_22, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.94  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.94  cnf(c_0_24, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.78/0.94  fof(c_0_25, plain, ![X15, X16]:k4_xboole_0(X15,k3_xboole_0(X15,X16))=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.78/0.94  cnf(c_0_26, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.78/0.94  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])).
% 0.78/0.94  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_16, c_0_24])).
% 0.78/0.94  cnf(c_0_29, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.78/0.94  cnf(c_0_30, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[c_0_24, c_0_26])).
% 0.78/0.94  cnf(c_0_31, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.78/0.94  cnf(c_0_32, plain, (k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_28])).
% 0.78/0.94  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_23])).
% 0.78/0.94  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.78/0.94  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_32]), c_0_20])).
% 0.78/0.94  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.78/0.94  cnf(c_0_37, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 0.78/0.94  cnf(c_0_38, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_19]), c_0_12])).
% 0.78/0.94  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=X1), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 0.78/0.94  cnf(c_0_40, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_37]), c_0_26]), c_0_38]), c_0_30])).
% 0.78/0.94  cnf(c_0_41, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_26]), c_0_26]), c_0_26])).
% 0.78/0.94  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.78/0.94  cnf(c_0_43, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_12, c_0_26])).
% 0.78/0.94  cnf(c_0_44, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_30, c_0_41])).
% 0.78/0.94  cnf(c_0_45, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_42]), c_0_42])).
% 0.78/0.94  cnf(c_0_46, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.78/0.94  cnf(c_0_47, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=X1), inference(spm,[status(thm)],[c_0_45, c_0_43])).
% 0.78/0.94  cnf(c_0_48, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_38, c_0_20])).
% 0.78/0.94  cnf(c_0_49, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X2),X3))=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_26, c_0_42])).
% 0.78/0.94  cnf(c_0_50, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X2,X3)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_26])).
% 0.78/0.94  cnf(c_0_51, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_48]), c_0_20])).
% 0.78/0.94  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X4)))=k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_31]), c_0_31]), c_0_26]), c_0_33])).
% 0.78/0.94  cnf(c_0_53, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X2),X3)),X3)=k4_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_49]), c_0_49])).
% 0.78/0.94  cnf(c_0_54, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X2),X1),X3))=X1), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.78/0.94  cnf(c_0_55, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_37, c_0_51])).
% 0.78/0.94  cnf(c_0_56, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_26]), c_0_33]), c_0_49])).
% 0.78/0.94  cnf(c_0_57, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X2),k2_xboole_0(X3,X2))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_54]), c_0_26]), c_0_26]), c_0_12]), c_0_30]), c_0_40]), c_0_26]), c_0_12]), c_0_55])).
% 0.78/0.94  cnf(c_0_58, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_16, c_0_26])).
% 0.78/0.94  cnf(c_0_59, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k4_xboole_0(X1,k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_49]), c_0_41]), c_0_38]), c_0_49])).
% 0.78/0.94  cnf(c_0_60, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_12]), c_0_36])).
% 0.78/0.94  cnf(c_0_61, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.78/0.94  cnf(c_0_62, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X2,X1),X3))=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_26, c_0_60])).
% 0.78/0.94  fof(c_0_63, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t52_xboole_1])).
% 0.78/0.94  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.78/0.94  cnf(c_0_65, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_43, c_0_59])).
% 0.78/0.94  fof(c_0_66, negated_conjecture, k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_63])])])).
% 0.78/0.94  cnf(c_0_67, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2))=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_15, c_0_64])).
% 0.78/0.94  cnf(c_0_68, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_12]), c_0_65])).
% 0.78/0.94  cnf(c_0_69, plain, (k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))))=k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_12, c_0_31])).
% 0.78/0.94  cnf(c_0_70, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_26])).
% 0.78/0.94  cnf(c_0_71, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1))))=k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_43, c_0_31])).
% 0.78/0.94  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.78/0.94  cnf(c_0_73, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))=k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_36]), c_0_68])).
% 0.78/0.94  cnf(c_0_74, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_20])).
% 0.78/0.94  cnf(c_0_75, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_72, c_0_23])).
% 0.78/0.94  cnf(c_0_76, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.78/0.94  cnf(c_0_77, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_59])).
% 0.78/0.94  cnf(c_0_78, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_26]), c_0_77]), c_0_33])]), ['proof']).
% 0.78/0.94  # SZS output end CNFRefutation
% 0.78/0.94  # Proof object total steps             : 79
% 0.78/0.94  # Proof object clause steps            : 60
% 0.78/0.94  # Proof object formula steps           : 19
% 0.78/0.94  # Proof object conjectures             : 6
% 0.78/0.94  # Proof object clause conjectures      : 3
% 0.78/0.94  # Proof object formula conjectures     : 3
% 0.78/0.94  # Proof object initial clauses used    : 9
% 0.78/0.94  # Proof object initial formulas used   : 9
% 0.78/0.94  # Proof object generating inferences   : 44
% 0.78/0.94  # Proof object simplifying inferences  : 48
% 0.78/0.94  # Training examples: 0 positive, 0 negative
% 0.78/0.94  # Parsed axioms                        : 9
% 0.78/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.94  # Initial clauses                      : 9
% 0.78/0.94  # Removed in clause preprocessing      : 1
% 0.78/0.94  # Initial clauses in saturation        : 8
% 0.78/0.94  # Processed clauses                    : 1085
% 0.78/0.94  # ...of these trivial                  : 626
% 0.78/0.94  # ...subsumed                          : 46
% 0.78/0.94  # ...remaining for further processing  : 413
% 0.78/0.94  # Other redundant clauses eliminated   : 0
% 0.78/0.94  # Clauses deleted for lack of memory   : 0
% 0.78/0.94  # Backward-subsumed                    : 0
% 0.78/0.94  # Backward-rewritten                   : 142
% 0.78/0.94  # Generated clauses                    : 100616
% 0.78/0.94  # ...of the previous two non-trivial   : 43791
% 0.78/0.94  # Contextual simplify-reflections      : 0
% 0.78/0.94  # Paramodulations                      : 100616
% 0.78/0.94  # Factorizations                       : 0
% 0.78/0.94  # Equation resolutions                 : 0
% 0.78/0.94  # Propositional unsat checks           : 0
% 0.78/0.94  #    Propositional check models        : 0
% 0.78/0.94  #    Propositional check unsatisfiable : 0
% 0.78/0.94  #    Propositional clauses             : 0
% 0.78/0.94  #    Propositional clauses after purity: 0
% 0.78/0.94  #    Propositional unsat core size     : 0
% 0.78/0.94  #    Propositional preprocessing time  : 0.000
% 0.78/0.94  #    Propositional encoding time       : 0.000
% 0.78/0.94  #    Propositional solver time         : 0.000
% 0.78/0.94  #    Success case prop preproc time    : 0.000
% 0.78/0.94  #    Success case prop encoding time   : 0.000
% 0.78/0.94  #    Success case prop solver time     : 0.000
% 0.78/0.94  # Current number of processed clauses  : 263
% 0.78/0.94  #    Positive orientable unit clauses  : 261
% 0.78/0.94  #    Positive unorientable unit clauses: 1
% 0.78/0.94  #    Negative unit clauses             : 0
% 0.78/0.94  #    Non-unit-clauses                  : 1
% 0.78/0.94  # Current number of unprocessed clauses: 42286
% 0.78/0.94  # ...number of literals in the above   : 42286
% 0.78/0.94  # Current number of archived formulas  : 0
% 0.78/0.94  # Current number of archived clauses   : 151
% 0.78/0.94  # Clause-clause subsumption calls (NU) : 0
% 0.78/0.94  # Rec. Clause-clause subsumption calls : 0
% 0.78/0.94  # Non-unit clause-clause subsumptions  : 0
% 0.78/0.94  # Unit Clause-clause subsumption calls : 65
% 0.78/0.94  # Rewrite failures with RHS unbound    : 0
% 0.78/0.94  # BW rewrite match attempts            : 1785
% 0.78/0.94  # BW rewrite match successes           : 239
% 0.78/0.94  # Condensation attempts                : 0
% 0.78/0.94  # Condensation successes               : 0
% 0.78/0.94  # Termbank termtop insertions          : 1057644
% 0.78/0.95  
% 0.78/0.95  # -------------------------------------------------
% 0.78/0.95  # User time                : 0.572 s
% 0.78/0.95  # System time              : 0.036 s
% 0.78/0.95  # Total time               : 0.608 s
% 0.78/0.95  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
