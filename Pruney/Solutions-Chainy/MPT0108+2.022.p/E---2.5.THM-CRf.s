%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 (2260 expanded)
%              Number of clauses        :   55 (1009 expanded)
%              Number of leaves         :   11 ( 625 expanded)
%              Depth                    :   20
%              Number of atoms          :   78 (2260 expanded)
%              Number of equality atoms :   77 (2259 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t101_xboole_1,conjecture,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

fof(c_0_11,plain,(
    ! [X28,X29] : k2_xboole_0(X28,X29) = k5_xboole_0(X28,k4_xboole_0(X29,X28)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X20,X21,X22] : k3_xboole_0(X20,k4_xboole_0(X21,X22)) = k4_xboole_0(k3_xboole_0(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_13,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k3_xboole_0(X13,X14)) = X13 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_22,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_24,plain,(
    ! [X23,X24] : k2_xboole_0(k3_xboole_0(X23,X24),k4_xboole_0(X23,X24)) = X23 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_25,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_21]),c_0_22]),c_0_14])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X15,X16,X17] : k4_xboole_0(k2_xboole_0(X15,X16),X17) = k2_xboole_0(k4_xboole_0(X15,X17),k4_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_29])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X2)) = k4_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_15])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_26])).

fof(c_0_40,plain,(
    ! [X25,X26,X27] : k5_xboole_0(k5_xboole_0(X25,X26),X27) = k5_xboole_0(X25,k5_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_27]),c_0_22])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_38]),c_0_39])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_41])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_42,c_0_31])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_43]),c_0_43])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_41])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_37])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k3_xboole_0(X2,k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_29]),c_0_15])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_38]),c_0_49])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_27])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3))) = k4_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_44])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_29])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,k5_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_44])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_50]),c_0_27])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_51]),c_0_52]),c_0_36]),c_0_50]),c_0_26])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_29])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(rw,[status(thm)],[c_0_49,c_0_53])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_50])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2))) = k2_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_60]),c_0_45])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_61])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_62])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k5_xboole_0(X2,X1)),k3_xboole_0(X1,k5_xboole_0(X2,X1))) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_15]),c_0_65]),c_0_38]),c_0_66])).

cnf(c_0_69,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k3_xboole_0(X3,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_36])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_50])).

fof(c_0_71,negated_conjecture,(
    ~ ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t101_xboole_1])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_22])).

fof(c_0_73,negated_conjecture,(
    k5_xboole_0(esk1_0,esk2_0) != k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_71])])])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_72]),c_0_44]),c_0_56]),c_0_14]),c_0_59])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(esk1_0,esk2_0) != k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_74]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:50:00 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.20/0.45  # and selection function SelectNewComplexAHP.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.026 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.45  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.45  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.20/0.45  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.20/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.45  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.45  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.20/0.45  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.45  fof(t101_xboole_1, conjecture, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_xboole_1)).
% 0.20/0.45  fof(c_0_11, plain, ![X28, X29]:k2_xboole_0(X28,X29)=k5_xboole_0(X28,k4_xboole_0(X29,X28)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.45  fof(c_0_12, plain, ![X20, X21, X22]:k3_xboole_0(X20,k4_xboole_0(X21,X22))=k4_xboole_0(k3_xboole_0(X20,X21),X22), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.45  fof(c_0_13, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.45  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.45  cnf(c_0_15, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.45  fof(c_0_16, plain, ![X13, X14]:k2_xboole_0(X13,k3_xboole_0(X13,X14))=X13, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.20/0.45  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.45  cnf(c_0_18, plain, (k5_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X3,X1)))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.45  cnf(c_0_19, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.45  fof(c_0_20, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.20/0.45  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.20/0.45  cnf(c_0_22, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  fof(c_0_23, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.45  fof(c_0_24, plain, ![X23, X24]:k2_xboole_0(k3_xboole_0(X23,X24),k4_xboole_0(X23,X24))=X23, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.45  fof(c_0_25, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.45  cnf(c_0_26, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_21]), c_0_22]), c_0_14])).
% 0.20/0.45  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  cnf(c_0_28, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.45  fof(c_0_30, plain, ![X15, X16, X17]:k4_xboole_0(k2_xboole_0(X15,X16),X17)=k2_xboole_0(k4_xboole_0(X15,X17),k4_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.20/0.45  cnf(c_0_31, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.20/0.45  cnf(c_0_32, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_19, c_0_29])).
% 0.20/0.45  cnf(c_0_33, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_27, c_0_21])).
% 0.20/0.45  cnf(c_0_34, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.45  cnf(c_0_35, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.20/0.45  cnf(c_0_36, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.20/0.45  cnf(c_0_37, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X2)=X2), inference(spm,[status(thm)],[c_0_35, c_0_29])).
% 0.20/0.45  cnf(c_0_38, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X2))=k4_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_15])).
% 0.20/0.45  cnf(c_0_39, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_21]), c_0_26])).
% 0.20/0.45  fof(c_0_40, plain, ![X25, X26, X27]:k5_xboole_0(k5_xboole_0(X25,X26),X27)=k5_xboole_0(X25,k5_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.45  cnf(c_0_41, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_27, c_0_21])).
% 0.20/0.45  cnf(c_0_42, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_27]), c_0_22])).
% 0.20/0.45  cnf(c_0_43, plain, (k2_xboole_0(k4_xboole_0(X1,X1),X2)=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_38]), c_0_39])).
% 0.20/0.45  cnf(c_0_44, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.45  cnf(c_0_45, plain, (k5_xboole_0(X1,X1)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_17, c_0_41])).
% 0.20/0.45  cnf(c_0_46, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)=k4_xboole_0(k2_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_34, c_0_21])).
% 0.20/0.45  cnf(c_0_47, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_42, c_0_31])).
% 0.20/0.45  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_43]), c_0_43])).
% 0.20/0.45  cnf(c_0_49, plain, (k5_xboole_0(k4_xboole_0(X1,X1),X2)=k5_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.45  cnf(c_0_50, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_41])).
% 0.20/0.45  cnf(c_0_51, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_27]), c_0_37])).
% 0.20/0.45  cnf(c_0_52, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k3_xboole_0(X2,k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_29]), c_0_15])).
% 0.20/0.45  cnf(c_0_53, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_38]), c_0_49])).
% 0.20/0.45  cnf(c_0_54, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_27, c_0_27])).
% 0.20/0.45  cnf(c_0_55, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3)))=k4_xboole_0(k5_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_17, c_0_44])).
% 0.20/0.45  cnf(c_0_56, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_29])).
% 0.20/0.45  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,k5_xboole_0(X1,X2))))=k2_xboole_0(k5_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_14, c_0_44])).
% 0.20/0.45  cnf(c_0_58, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_50]), c_0_27])).
% 0.20/0.45  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_51]), c_0_52]), c_0_36]), c_0_50]), c_0_26])).
% 0.20/0.45  cnf(c_0_60, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_29])).
% 0.20/0.45  cnf(c_0_61, plain, (k5_xboole_0(k4_xboole_0(X1,X1),X2)=X2), inference(rw,[status(thm)],[c_0_49, c_0_53])).
% 0.20/0.45  cnf(c_0_62, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_50])).
% 0.20/0.45  cnf(c_0_63, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X1,X2)))=k4_xboole_0(k5_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.45  cnf(c_0_64, plain, (k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2)))=k2_xboole_0(X2,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.20/0.45  cnf(c_0_65, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_60]), c_0_45])).
% 0.20/0.45  cnf(c_0_66, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_22, c_0_61])).
% 0.20/0.45  cnf(c_0_67, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X2,k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_52, c_0_62])).
% 0.20/0.45  cnf(c_0_68, plain, (k4_xboole_0(k2_xboole_0(X1,k5_xboole_0(X2,X1)),k3_xboole_0(X1,k5_xboole_0(X2,X1)))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_15]), c_0_65]), c_0_38]), c_0_66])).
% 0.20/0.45  cnf(c_0_69, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k3_xboole_0(X3,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_52, c_0_36])).
% 0.20/0.45  cnf(c_0_70, plain, (k4_xboole_0(X1,k5_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_50])).
% 0.20/0.45  fof(c_0_71, negated_conjecture, ~(![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t101_xboole_1])).
% 0.20/0.45  cnf(c_0_72, plain, (k4_xboole_0(X1,k5_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_22])).
% 0.20/0.45  fof(c_0_73, negated_conjecture, k5_xboole_0(esk1_0,esk2_0)!=k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_71])])])).
% 0.20/0.45  cnf(c_0_74, plain, (k2_xboole_0(X1,k5_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_72]), c_0_44]), c_0_56]), c_0_14]), c_0_59])).
% 0.20/0.45  cnf(c_0_75, negated_conjecture, (k5_xboole_0(esk1_0,esk2_0)!=k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.45  cnf(c_0_76, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_74]), c_0_72])).
% 0.20/0.45  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 78
% 0.20/0.45  # Proof object clause steps            : 55
% 0.20/0.45  # Proof object formula steps           : 23
% 0.20/0.45  # Proof object conjectures             : 5
% 0.20/0.45  # Proof object clause conjectures      : 2
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 11
% 0.20/0.45  # Proof object initial formulas used   : 11
% 0.20/0.45  # Proof object generating inferences   : 40
% 0.20/0.45  # Proof object simplifying inferences  : 38
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 12
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 12
% 0.20/0.45  # Removed in clause preprocessing      : 0
% 0.20/0.45  # Initial clauses in saturation        : 12
% 0.20/0.45  # Processed clauses                    : 1021
% 0.20/0.45  # ...of these trivial                  : 243
% 0.20/0.45  # ...subsumed                          : 586
% 0.20/0.45  # ...remaining for further processing  : 192
% 0.20/0.45  # Other redundant clauses eliminated   : 0
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 0
% 0.20/0.45  # Backward-rewritten                   : 40
% 0.20/0.45  # Generated clauses                    : 9404
% 0.20/0.45  # ...of the previous two non-trivial   : 6129
% 0.20/0.45  # Contextual simplify-reflections      : 0
% 0.20/0.45  # Paramodulations                      : 9404
% 0.20/0.45  # Factorizations                       : 0
% 0.20/0.45  # Equation resolutions                 : 0
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 140
% 0.20/0.45  #    Positive orientable unit clauses  : 131
% 0.20/0.45  #    Positive unorientable unit clauses: 9
% 0.20/0.45  #    Negative unit clauses             : 0
% 0.20/0.45  #    Non-unit-clauses                  : 0
% 0.20/0.45  # Current number of unprocessed clauses: 4907
% 0.20/0.45  # ...number of literals in the above   : 4907
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 52
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.45  # Unit Clause-clause subsumption calls : 42
% 0.20/0.45  # Rewrite failures with RHS unbound    : 36
% 0.20/0.45  # BW rewrite match attempts            : 430
% 0.20/0.45  # BW rewrite match successes           : 180
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 72669
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.101 s
% 0.20/0.45  # System time              : 0.006 s
% 0.20/0.45  # Total time               : 0.107 s
% 0.20/0.45  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
