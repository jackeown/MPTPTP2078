%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:01 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   70 (5509 expanded)
%              Number of clauses        :   51 (2302 expanded)
%              Number of leaves         :    9 (1603 expanded)
%              Depth                    :   18
%              Number of atoms          :   70 (5509 expanded)
%              Number of equality atoms :   69 (5508 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t94_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(c_0_9,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,X8)) = k2_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_10,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,plain,(
    ! [X20,X21,X22] : k4_xboole_0(X20,k4_xboole_0(X21,X22)) = k2_xboole_0(k4_xboole_0(X20,X21),k3_xboole_0(X20,X22)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_12,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X18,X19] : k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X18 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])).

fof(c_0_19,plain,(
    ! [X15,X16,X17] : k2_xboole_0(k2_xboole_0(X15,X16),X17) = k2_xboole_0(X15,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X1) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_18]),c_0_13])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_14])).

fof(c_0_25,plain,(
    ! [X10,X11,X12] : k4_xboole_0(k4_xboole_0(X10,X11),X12) = k4_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_13])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_16])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X1)) = k3_xboole_0(X1,k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_26]),c_0_22])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X1,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_22])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_28]),c_0_28])).

cnf(c_0_34,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),k3_xboole_0(X1,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,k2_xboole_0(X1,k5_xboole_0(X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_30]),c_0_30]),c_0_13]),c_0_29])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X1,X1))) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_14]),c_0_30]),c_0_15]),c_0_33])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,k5_xboole_0(X1,X1)),k4_xboole_0(X1,X1))) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_34]),c_0_30]),c_0_35]),c_0_29]),c_0_15])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_13]),c_0_22])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_16])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,k5_xboole_0(X1,X1)),k4_xboole_0(X1,X1))) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_37]),c_0_14]),c_0_21])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,X1)) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_28]),c_0_13])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X1))) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_14]),c_0_30])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X1,X1))) = k3_xboole_0(X1,k2_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_29]),c_0_24]),c_0_14]),c_0_21]),c_0_29])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X1)) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_26]),c_0_14]),c_0_21])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_41]),c_0_26]),c_0_14]),c_0_21]),c_0_29])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_21]),c_0_22]),c_0_35]),c_0_26])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(X2,X1))) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_47])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_47])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_30])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_14])).

fof(c_0_54,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t94_xboole_1])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_50]),c_0_16])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_20]),c_0_16])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_16])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_16])).

fof(c_0_59,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_28])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_30]),c_0_30]),c_0_57]),c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_60]),c_0_30]),c_0_47]),c_0_13])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_60])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_33])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_33]),c_0_16]),c_0_66]),c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.31  % Computer   : n009.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 14:19:26 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  # Version: 2.5pre002
% 0.16/0.31  # No SInE strategy applied
% 0.16/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.44  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.16/0.44  # and selection function SelectNewComplexAHP.
% 0.16/0.44  #
% 0.16/0.44  # Preprocessing time       : 0.025 s
% 0.16/0.44  # Presaturation interreduction done
% 0.16/0.44  
% 0.16/0.44  # Proof found!
% 0.16/0.44  # SZS status Theorem
% 0.16/0.44  # SZS output start CNFRefutation
% 0.16/0.44  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.16/0.44  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.16/0.44  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.16/0.44  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.16/0.44  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.16/0.44  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.16/0.44  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.16/0.44  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.16/0.44  fof(t94_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.16/0.44  fof(c_0_9, plain, ![X8, X9]:k2_xboole_0(X8,k4_xboole_0(X9,X8))=k2_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.16/0.44  fof(c_0_10, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.16/0.44  fof(c_0_11, plain, ![X20, X21, X22]:k4_xboole_0(X20,k4_xboole_0(X21,X22))=k2_xboole_0(k4_xboole_0(X20,X21),k3_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.16/0.44  fof(c_0_12, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.16/0.44  cnf(c_0_13, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.44  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.44  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.16/0.44  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.44  fof(c_0_17, plain, ![X18, X19]:k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19))=X18, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.16/0.44  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])).
% 0.16/0.44  fof(c_0_19, plain, ![X15, X16, X17]:k2_xboole_0(k2_xboole_0(X15,X16),X17)=k2_xboole_0(X15,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.16/0.44  cnf(c_0_20, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.44  cnf(c_0_21, plain, (k3_xboole_0(X1,X1)=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_18]), c_0_13])).
% 0.16/0.44  cnf(c_0_22, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.16/0.44  fof(c_0_23, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.16/0.44  cnf(c_0_24, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_14, c_0_14])).
% 0.16/0.44  fof(c_0_25, plain, ![X10, X11, X12]:k4_xboole_0(k4_xboole_0(X10,X11),X12)=k4_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.16/0.44  cnf(c_0_26, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_13])).
% 0.16/0.44  cnf(c_0_27, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_14]), c_0_16])).
% 0.16/0.44  cnf(c_0_28, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.16/0.44  cnf(c_0_29, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X1))=k3_xboole_0(X1,k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.16/0.44  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.16/0.44  cnf(c_0_31, plain, (k2_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_26]), c_0_22])).
% 0.16/0.44  cnf(c_0_32, plain, (k2_xboole_0(X1,k2_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X1,X1))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_22])).
% 0.16/0.44  cnf(c_0_33, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_28]), c_0_28])).
% 0.16/0.44  cnf(c_0_34, plain, (k3_xboole_0(k4_xboole_0(X1,X1),k3_xboole_0(X1,k4_xboole_0(X1,X1)))=k4_xboole_0(X1,k2_xboole_0(X1,k5_xboole_0(X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_30]), c_0_30]), c_0_13]), c_0_29])).
% 0.16/0.44  cnf(c_0_35, plain, (k2_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X1,X1)))=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.16/0.44  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=k5_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_14]), c_0_30]), c_0_15]), c_0_33])).
% 0.16/0.44  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,k5_xboole_0(X1,X1)),k4_xboole_0(X1,X1)))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_34]), c_0_30]), c_0_35]), c_0_29]), c_0_15])).
% 0.16/0.44  cnf(c_0_38, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_13]), c_0_22])).
% 0.16/0.44  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X2))=k5_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_16])).
% 0.16/0.44  cnf(c_0_40, plain, (k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,k5_xboole_0(X1,X1)),k4_xboole_0(X1,X1)))=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_37]), c_0_14]), c_0_21])).
% 0.16/0.44  cnf(c_0_41, plain, (k2_xboole_0(X1,k5_xboole_0(X2,X1))=k2_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_28]), c_0_13])).
% 0.16/0.44  cnf(c_0_42, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X1)))=k5_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_14]), c_0_30])).
% 0.16/0.44  cnf(c_0_43, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X1,X1)))=k3_xboole_0(X1,k2_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_29]), c_0_24]), c_0_14]), c_0_21]), c_0_29])).
% 0.16/0.44  cnf(c_0_44, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X1))=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_26]), c_0_14]), c_0_21])).
% 0.16/0.44  cnf(c_0_45, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_41]), c_0_26]), c_0_14]), c_0_21]), c_0_29])).
% 0.16/0.44  cnf(c_0_46, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_29]), c_0_21]), c_0_22]), c_0_35]), c_0_26])).
% 0.16/0.44  cnf(c_0_47, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])).
% 0.16/0.44  cnf(c_0_48, plain, (k2_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(X2,X1)))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_16])).
% 0.16/0.44  cnf(c_0_49, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_47])).
% 0.16/0.44  cnf(c_0_50, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[c_0_21, c_0_47])).
% 0.16/0.44  cnf(c_0_51, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.16/0.44  cnf(c_0_52, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_13, c_0_30])).
% 0.16/0.44  cnf(c_0_53, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_30, c_0_14])).
% 0.16/0.44  fof(c_0_54, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t94_xboole_1])).
% 0.16/0.44  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_50]), c_0_16])).
% 0.16/0.44  cnf(c_0_56, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_20]), c_0_16])).
% 0.16/0.44  cnf(c_0_57, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_52, c_0_16])).
% 0.16/0.44  cnf(c_0_58, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_53, c_0_16])).
% 0.16/0.44  fof(c_0_59, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).
% 0.16/0.44  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.16/0.44  cnf(c_0_61, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_53, c_0_28])).
% 0.16/0.44  cnf(c_0_62, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_30]), c_0_30]), c_0_57]), c_0_58])).
% 0.16/0.44  cnf(c_0_63, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.16/0.44  cnf(c_0_64, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_60]), c_0_30]), c_0_47]), c_0_13])).
% 0.16/0.44  cnf(c_0_65, plain, (k4_xboole_0(X1,k5_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_60])).
% 0.16/0.44  cnf(c_0_66, plain, (k2_xboole_0(X1,k5_xboole_0(X1,X2))=k2_xboole_0(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_41, c_0_33])).
% 0.16/0.44  cnf(c_0_67, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_63, c_0_33])).
% 0.16/0.44  cnf(c_0_68, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_33]), c_0_16]), c_0_66]), c_0_51])).
% 0.16/0.44  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_16])]), ['proof']).
% 0.16/0.44  # SZS output end CNFRefutation
% 0.16/0.44  # Proof object total steps             : 70
% 0.16/0.44  # Proof object clause steps            : 51
% 0.16/0.44  # Proof object formula steps           : 19
% 0.16/0.44  # Proof object conjectures             : 6
% 0.16/0.44  # Proof object clause conjectures      : 3
% 0.16/0.44  # Proof object formula conjectures     : 3
% 0.16/0.44  # Proof object initial clauses used    : 9
% 0.16/0.44  # Proof object initial formulas used   : 9
% 0.16/0.44  # Proof object generating inferences   : 33
% 0.16/0.44  # Proof object simplifying inferences  : 67
% 0.16/0.44  # Training examples: 0 positive, 0 negative
% 0.16/0.44  # Parsed axioms                        : 9
% 0.16/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.44  # Initial clauses                      : 9
% 0.16/0.44  # Removed in clause preprocessing      : 0
% 0.16/0.44  # Initial clauses in saturation        : 9
% 0.16/0.44  # Processed clauses                    : 697
% 0.16/0.44  # ...of these trivial                  : 266
% 0.16/0.44  # ...subsumed                          : 191
% 0.16/0.44  # ...remaining for further processing  : 240
% 0.16/0.44  # Other redundant clauses eliminated   : 0
% 0.16/0.44  # Clauses deleted for lack of memory   : 0
% 0.16/0.44  # Backward-subsumed                    : 0
% 0.16/0.44  # Backward-rewritten                   : 67
% 0.16/0.44  # Generated clauses                    : 13449
% 0.16/0.44  # ...of the previous two non-trivial   : 8195
% 0.16/0.44  # Contextual simplify-reflections      : 0
% 0.16/0.44  # Paramodulations                      : 13449
% 0.16/0.44  # Factorizations                       : 0
% 0.16/0.44  # Equation resolutions                 : 0
% 0.16/0.44  # Propositional unsat checks           : 0
% 0.16/0.44  #    Propositional check models        : 0
% 0.16/0.44  #    Propositional check unsatisfiable : 0
% 0.16/0.44  #    Propositional clauses             : 0
% 0.16/0.44  #    Propositional clauses after purity: 0
% 0.16/0.44  #    Propositional unsat core size     : 0
% 0.16/0.44  #    Propositional preprocessing time  : 0.000
% 0.16/0.44  #    Propositional encoding time       : 0.000
% 0.16/0.44  #    Propositional solver time         : 0.000
% 0.16/0.44  #    Success case prop preproc time    : 0.000
% 0.16/0.44  #    Success case prop encoding time   : 0.000
% 0.16/0.44  #    Success case prop solver time     : 0.000
% 0.16/0.44  # Current number of processed clauses  : 164
% 0.16/0.44  #    Positive orientable unit clauses  : 158
% 0.16/0.44  #    Positive unorientable unit clauses: 6
% 0.16/0.44  #    Negative unit clauses             : 0
% 0.16/0.44  #    Non-unit-clauses                  : 0
% 0.16/0.44  # Current number of unprocessed clauses: 7212
% 0.16/0.44  # ...number of literals in the above   : 7212
% 0.16/0.44  # Current number of archived formulas  : 0
% 0.16/0.44  # Current number of archived clauses   : 76
% 0.16/0.44  # Clause-clause subsumption calls (NU) : 0
% 0.16/0.44  # Rec. Clause-clause subsumption calls : 0
% 0.16/0.44  # Non-unit clause-clause subsumptions  : 0
% 0.16/0.44  # Unit Clause-clause subsumption calls : 31
% 0.16/0.44  # Rewrite failures with RHS unbound    : 40
% 0.16/0.44  # BW rewrite match attempts            : 371
% 0.16/0.44  # BW rewrite match successes           : 129
% 0.16/0.44  # Condensation attempts                : 0
% 0.16/0.44  # Condensation successes               : 0
% 0.16/0.44  # Termbank termtop insertions          : 114021
% 0.16/0.45  
% 0.16/0.45  # -------------------------------------------------
% 0.16/0.45  # User time                : 0.125 s
% 0.16/0.45  # System time              : 0.010 s
% 0.16/0.45  # Total time               : 0.135 s
% 0.16/0.45  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
