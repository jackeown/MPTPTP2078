%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:20 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 (5557 expanded)
%              Number of clauses        :   48 (2430 expanded)
%              Number of leaves         :    9 (1563 expanded)
%              Depth                    :   18
%              Number of atoms          :   67 (5557 expanded)
%              Number of equality atoms :   66 (5556 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t50_xboole_1,conjecture,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(c_0_9,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k3_xboole_0(X16,X17)) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X20,X21,X22] : k3_xboole_0(X20,k4_xboole_0(X21,X22)) = k4_xboole_0(k3_xboole_0(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_14,plain,(
    ! [X11,X12] : k4_xboole_0(k2_xboole_0(X11,X12),X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_15,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_16,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_11]),c_0_12])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_22,plain,(
    ! [X6,X7,X8] : k3_xboole_0(X6,k2_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_25]),c_0_26])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_20])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_29]),c_0_11])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),X2) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_28])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_26]),c_0_26])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X1) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_30]),c_0_31])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_32]),c_0_32]),c_0_29])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_23])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_19])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_32]),c_0_31])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_12]),c_0_20]),c_0_20]),c_0_30])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_36]),c_0_26]),c_0_33]),c_0_26]),c_0_34]),c_0_35])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X1),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_37]),c_0_12]),c_0_19]),c_0_18])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_23])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_36]),c_0_32]),c_0_35])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_11]),c_0_39]),c_0_20])).

cnf(c_0_45,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_11])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_38]),c_0_24])).

cnf(c_0_47,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_32]),c_0_37]),c_0_24])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_11]),c_0_44]),c_0_12]),c_0_18]),c_0_45])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_26]),c_0_20]),c_0_44])).

cnf(c_0_50,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_48])).

cnf(c_0_51,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_25]),c_0_42])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_49]),c_0_24]),c_0_32])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_25]),c_0_50]),c_0_51]),c_0_26]),c_0_20]),c_0_23])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_52]),c_0_11])).

fof(c_0_56,negated_conjecture,(
    ~ ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t50_xboole_1])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_18])).

cnf(c_0_58,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X2) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_53]),c_0_54]),c_0_55])).

fof(c_0_59,negated_conjecture,(
    k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).

cnf(c_0_60,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_11]),c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_12]),c_0_18])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) != k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_18])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_60]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:10:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.19/0.45  # and selection function SelectNewComplexAHP.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.025 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.45  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.45  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.19/0.45  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.19/0.45  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.45  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.45  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.19/0.45  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.19/0.45  fof(t50_xboole_1, conjecture, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.19/0.45  fof(c_0_9, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.45  fof(c_0_10, plain, ![X16, X17]:k4_xboole_0(X16,k3_xboole_0(X16,X17))=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.45  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  cnf(c_0_12, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.45  fof(c_0_13, plain, ![X20, X21, X22]:k3_xboole_0(X20,k4_xboole_0(X21,X22))=k4_xboole_0(k3_xboole_0(X20,X21),X22), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.19/0.45  fof(c_0_14, plain, ![X11, X12]:k4_xboole_0(k2_xboole_0(X11,X12),X12)=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.19/0.45  fof(c_0_15, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.45  fof(c_0_16, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.45  cnf(c_0_17, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_11]), c_0_12])).
% 0.19/0.45  cnf(c_0_18, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_19, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.45  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.45  fof(c_0_21, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.19/0.45  fof(c_0_22, plain, ![X6, X7, X8]:k3_xboole_0(X6,k2_xboole_0(X7,X8))=k2_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.19/0.45  cnf(c_0_23, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  cnf(c_0_24, plain, (k4_xboole_0(k3_xboole_0(X1,X1),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.45  cnf(c_0_25, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.45  cnf(c_0_26, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  cnf(c_0_27, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  cnf(c_0_28, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_23])).
% 0.19/0.45  cnf(c_0_29, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_25]), c_0_26])).
% 0.19/0.45  cnf(c_0_30, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_20])).
% 0.19/0.45  cnf(c_0_31, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_29]), c_0_11])).
% 0.19/0.45  cnf(c_0_32, plain, (k2_xboole_0(k3_xboole_0(X1,X1),X2)=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_28])).
% 0.19/0.45  cnf(c_0_33, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_26]), c_0_26])).
% 0.19/0.45  cnf(c_0_34, plain, (k2_xboole_0(X1,X1)=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_30]), c_0_31])).
% 0.19/0.45  cnf(c_0_35, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_32]), c_0_32]), c_0_29])).
% 0.19/0.45  cnf(c_0_36, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k3_xboole_0(k4_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_23])).
% 0.19/0.45  cnf(c_0_37, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k3_xboole_0(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_11, c_0_19])).
% 0.19/0.45  cnf(c_0_38, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_32]), c_0_31])).
% 0.19/0.45  cnf(c_0_39, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k3_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_12]), c_0_20]), c_0_20]), c_0_30])).
% 0.19/0.45  cnf(c_0_40, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_36]), c_0_26]), c_0_33]), c_0_26]), c_0_34]), c_0_35])).
% 0.19/0.45  cnf(c_0_41, plain, (k4_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X1),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_37]), c_0_12]), c_0_19]), c_0_18])).
% 0.19/0.45  cnf(c_0_42, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_19, c_0_23])).
% 0.19/0.45  cnf(c_0_43, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k3_xboole_0(k4_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_36]), c_0_32]), c_0_35])).
% 0.19/0.45  cnf(c_0_44, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_11]), c_0_39]), c_0_20])).
% 0.19/0.45  cnf(c_0_45, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_11])).
% 0.19/0.45  cnf(c_0_46, plain, (k4_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_32]), c_0_38]), c_0_24])).
% 0.19/0.45  cnf(c_0_47, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_32]), c_0_37]), c_0_24])).
% 0.19/0.45  cnf(c_0_48, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(k3_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_11]), c_0_44]), c_0_12]), c_0_18]), c_0_45])).
% 0.19/0.45  cnf(c_0_49, plain, (k4_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_26]), c_0_20]), c_0_44])).
% 0.19/0.45  cnf(c_0_50, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_36, c_0_48])).
% 0.19/0.45  cnf(c_0_51, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_25]), c_0_42])).
% 0.19/0.45  cnf(c_0_52, plain, (k4_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_49]), c_0_24]), c_0_32])).
% 0.19/0.45  cnf(c_0_53, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k4_xboole_0(X2,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_25]), c_0_50]), c_0_51]), c_0_26]), c_0_20]), c_0_23])).
% 0.19/0.45  cnf(c_0_54, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_18, c_0_11])).
% 0.19/0.45  cnf(c_0_55, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X2,X1)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_52]), c_0_11])).
% 0.19/0.45  fof(c_0_56, negated_conjecture, ~(![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t50_xboole_1])).
% 0.19/0.45  cnf(c_0_57, plain, (k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_12, c_0_18])).
% 0.19/0.45  cnf(c_0_58, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X2)=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_53]), c_0_54]), c_0_55])).
% 0.19/0.45  fof(c_0_59, negated_conjecture, k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).
% 0.19/0.45  cnf(c_0_60, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_11]), c_0_54])).
% 0.19/0.45  cnf(c_0_61, negated_conjecture, (k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.45  cnf(c_0_62, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_12]), c_0_18])).
% 0.19/0.45  cnf(c_0_63, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_60])).
% 0.19/0.45  cnf(c_0_64, negated_conjecture, (k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))!=k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_61, c_0_18])).
% 0.19/0.45  cnf(c_0_65, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_60]), c_0_62])).
% 0.19/0.45  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 67
% 0.19/0.45  # Proof object clause steps            : 48
% 0.19/0.45  # Proof object formula steps           : 19
% 0.19/0.45  # Proof object conjectures             : 6
% 0.19/0.45  # Proof object clause conjectures      : 3
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 9
% 0.19/0.45  # Proof object initial formulas used   : 9
% 0.19/0.45  # Proof object generating inferences   : 34
% 0.19/0.45  # Proof object simplifying inferences  : 63
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 9
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 9
% 0.19/0.45  # Removed in clause preprocessing      : 0
% 0.19/0.45  # Initial clauses in saturation        : 9
% 0.19/0.45  # Processed clauses                    : 593
% 0.19/0.45  # ...of these trivial                  : 150
% 0.19/0.45  # ...subsumed                          : 272
% 0.19/0.45  # ...remaining for further processing  : 171
% 0.19/0.45  # Other redundant clauses eliminated   : 0
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 0
% 0.19/0.45  # Backward-rewritten                   : 61
% 0.19/0.45  # Generated clauses                    : 9032
% 0.19/0.45  # ...of the previous two non-trivial   : 6653
% 0.19/0.45  # Contextual simplify-reflections      : 0
% 0.19/0.45  # Paramodulations                      : 9032
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 0
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 101
% 0.19/0.45  #    Positive orientable unit clauses  : 94
% 0.19/0.45  #    Positive unorientable unit clauses: 7
% 0.19/0.45  #    Negative unit clauses             : 0
% 0.19/0.45  #    Non-unit-clauses                  : 0
% 0.19/0.45  # Current number of unprocessed clauses: 5723
% 0.19/0.45  # ...number of literals in the above   : 5723
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 70
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.45  # Unit Clause-clause subsumption calls : 124
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 518
% 0.19/0.45  # BW rewrite match successes           : 137
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 83527
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.108 s
% 0.19/0.45  # System time              : 0.006 s
% 0.19/0.45  # Total time               : 0.115 s
% 0.19/0.45  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
