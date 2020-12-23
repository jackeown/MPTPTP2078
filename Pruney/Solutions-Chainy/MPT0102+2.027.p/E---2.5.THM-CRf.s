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
% DateTime   : Thu Dec  3 10:34:05 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   87 (2256 expanded)
%              Number of clauses        :   58 (1019 expanded)
%              Number of leaves         :   14 ( 618 expanded)
%              Depth                    :   14
%              Number of atoms          :   87 (2256 expanded)
%              Number of equality atoms :   86 (2255 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t95_xboole_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_14,plain,(
    ! [X32] : k5_xboole_0(X32,X32) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_15,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_16,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X8] : k2_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_19,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_20,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_21,plain,(
    ! [X27,X28,X29] : k4_xboole_0(X27,k4_xboole_0(X28,X29)) = k2_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(X27,X29)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X14,X15] : k2_xboole_0(X14,k4_xboole_0(X15,X14)) = k2_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_27,plain,(
    ! [X18,X19,X20] : k4_xboole_0(k4_xboole_0(X18,X19),X20) = k4_xboole_0(X18,k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_28,plain,(
    ! [X33,X34] : k2_xboole_0(X33,X34) = k2_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X16,X17] : k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_34,plain,(
    ! [X30,X31] : k2_xboole_0(X30,k2_xboole_0(X30,X31)) = k2_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X24,X25,X26] : k2_xboole_0(k2_xboole_0(X24,X25),X26) = k2_xboole_0(X24,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_31])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_35]),c_0_32])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_17])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_39])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_29]),c_0_30]),c_0_39]),c_0_25])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_30])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X2,X1),k3_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_45]),c_0_25]),c_0_46])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_47]),c_0_43]),c_0_47])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_50])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_29])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_39]),c_0_51]),c_0_39])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_35])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_25])).

fof(c_0_58,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t95_xboole_1])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_53,c_0_25])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_54]),c_0_25]),c_0_55])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_24])).

fof(c_0_62,plain,(
    ! [X21,X22,X23] : k4_xboole_0(k2_xboole_0(X21,X22),X23) = k2_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

fof(c_0_63,negated_conjecture,(
    k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_50]),c_0_30])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_30])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_64]),c_0_24])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)) = k3_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_47]),c_0_31])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_65]),c_0_39]),c_0_25])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_50])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_25])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_74,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_17]),c_0_17])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_70]),c_0_38])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_50])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,X3)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X4),X3) ),
    inference(spm,[status(thm)],[c_0_66,c_0_35])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_32]),c_0_71]),c_0_35]),c_0_32]),c_0_72])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_73]),c_0_35])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_46])).

cnf(c_0_82,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk2_0,esk1_0))) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_75]),c_0_38]),c_0_76])).

cnf(c_0_84,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X3,X2),X4)) = k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X1,X3)),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_77]),c_0_78]),c_0_25]),c_0_79])).

cnf(c_0_85,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),k2_xboole_0(X1,X4)) = k4_xboole_0(X3,k2_xboole_0(X1,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_30]),c_0_24]),c_0_38]),c_0_83]),c_0_85]),c_0_35]),c_0_41]),c_0_42]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:31:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 4.26/4.45  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 4.26/4.45  # and selection function SelectNewComplexAHP.
% 4.26/4.45  #
% 4.26/4.45  # Preprocessing time       : 0.026 s
% 4.26/4.45  # Presaturation interreduction done
% 4.26/4.45  
% 4.26/4.45  # Proof found!
% 4.26/4.45  # SZS status Theorem
% 4.26/4.45  # SZS output start CNFRefutation
% 4.26/4.45  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.26/4.45  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.26/4.45  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.26/4.45  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.26/4.45  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.26/4.45  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.26/4.45  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.26/4.45  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.26/4.45  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 4.26/4.45  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.26/4.45  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 4.26/4.45  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.26/4.45  fof(t95_xboole_1, conjecture, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.26/4.45  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 4.26/4.45  fof(c_0_14, plain, ![X32]:k5_xboole_0(X32,X32)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 4.26/4.45  fof(c_0_15, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 4.26/4.45  cnf(c_0_16, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.26/4.45  cnf(c_0_17, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.26/4.45  fof(c_0_18, plain, ![X8]:k2_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 4.26/4.45  fof(c_0_19, plain, ![X11]:k2_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t1_boole])).
% 4.26/4.45  fof(c_0_20, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 4.26/4.45  fof(c_0_21, plain, ![X27, X28, X29]:k4_xboole_0(X27,k4_xboole_0(X28,X29))=k2_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(X27,X29)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 4.26/4.45  cnf(c_0_22, plain, (k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 4.26/4.45  cnf(c_0_23, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.26/4.45  cnf(c_0_24, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.26/4.45  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.26/4.45  fof(c_0_26, plain, ![X14, X15]:k2_xboole_0(X14,k4_xboole_0(X15,X14))=k2_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 4.26/4.45  fof(c_0_27, plain, ![X18, X19, X20]:k4_xboole_0(k4_xboole_0(X18,X19),X20)=k4_xboole_0(X18,k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 4.26/4.45  fof(c_0_28, plain, ![X33, X34]:k2_xboole_0(X33,X34)=k2_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 4.26/4.45  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.26/4.45  cnf(c_0_30, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 4.26/4.45  cnf(c_0_31, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 4.26/4.45  cnf(c_0_32, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.26/4.45  fof(c_0_33, plain, ![X16, X17]:k4_xboole_0(k2_xboole_0(X16,X17),X17)=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 4.26/4.45  fof(c_0_34, plain, ![X30, X31]:k2_xboole_0(X30,k2_xboole_0(X30,X31))=k2_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 4.26/4.45  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.26/4.45  fof(c_0_36, plain, ![X24, X25, X26]:k2_xboole_0(k2_xboole_0(X24,X25),X26)=k2_xboole_0(X24,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 4.26/4.45  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.26/4.45  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 4.26/4.45  cnf(c_0_39, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_31]), c_0_31])).
% 4.26/4.45  cnf(c_0_40, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.26/4.45  cnf(c_0_41, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 4.26/4.45  cnf(c_0_42, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_35]), c_0_32])).
% 4.26/4.45  cnf(c_0_43, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 4.26/4.45  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_37, c_0_17])).
% 4.26/4.45  cnf(c_0_45, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_30]), c_0_39])).
% 4.26/4.45  cnf(c_0_46, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_38]), c_0_29]), c_0_30]), c_0_39]), c_0_25])).
% 4.26/4.45  cnf(c_0_47, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_30])).
% 4.26/4.45  cnf(c_0_48, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 4.26/4.45  cnf(c_0_49, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X2,X1),k3_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_43])).
% 4.26/4.45  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_45]), c_0_25]), c_0_46])).
% 4.26/4.45  cnf(c_0_51, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_47]), c_0_43]), c_0_47])).
% 4.26/4.45  cnf(c_0_52, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 4.26/4.45  cnf(c_0_53, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_50])).
% 4.26/4.45  cnf(c_0_54, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_25, c_0_29])).
% 4.26/4.45  cnf(c_0_55, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_39]), c_0_51]), c_0_39])).
% 4.26/4.45  cnf(c_0_56, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_32, c_0_35])).
% 4.26/4.45  cnf(c_0_57, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_25])).
% 4.26/4.45  fof(c_0_58, negated_conjecture, ~(![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t95_xboole_1])).
% 4.26/4.45  cnf(c_0_59, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(spm,[status(thm)],[c_0_53, c_0_25])).
% 4.26/4.45  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_54]), c_0_25]), c_0_55])).
% 4.26/4.45  cnf(c_0_61, plain, (k2_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_24])).
% 4.26/4.45  fof(c_0_62, plain, ![X21, X22, X23]:k4_xboole_0(k2_xboole_0(X21,X22),X23)=k2_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 4.26/4.45  fof(c_0_63, negated_conjecture, k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).
% 4.26/4.45  cnf(c_0_64, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_50]), c_0_30])).
% 4.26/4.45  cnf(c_0_65, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_30])).
% 4.26/4.45  cnf(c_0_66, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 4.26/4.45  cnf(c_0_67, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 4.26/4.45  cnf(c_0_68, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_64]), c_0_24])).
% 4.26/4.45  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))=k3_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_47]), c_0_31])).
% 4.26/4.45  cnf(c_0_70, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_65]), c_0_39]), c_0_25])).
% 4.26/4.45  cnf(c_0_71, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_66, c_0_50])).
% 4.26/4.45  cnf(c_0_72, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_56, c_0_25])).
% 4.26/4.45  cnf(c_0_73, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_25])).
% 4.26/4.45  cnf(c_0_74, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)!=k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_17]), c_0_17])).
% 4.26/4.45  cnf(c_0_75, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 4.26/4.45  cnf(c_0_76, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_70]), c_0_38])).
% 4.26/4.45  cnf(c_0_77, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3))=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_50])).
% 4.26/4.45  cnf(c_0_78, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,X3))=k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X4),X3)), inference(spm,[status(thm)],[c_0_66, c_0_35])).
% 4.26/4.45  cnf(c_0_79, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_32]), c_0_71]), c_0_35]), c_0_32]), c_0_72])).
% 4.26/4.45  cnf(c_0_80, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_73]), c_0_35])).
% 4.26/4.45  cnf(c_0_81, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k2_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_43, c_0_46])).
% 4.26/4.45  cnf(c_0_82, negated_conjecture, (k2_xboole_0(k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk2_0,esk1_0)))!=k3_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 4.26/4.45  cnf(c_0_83, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_75]), c_0_38]), c_0_76])).
% 4.26/4.45  cnf(c_0_84, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X3,X2),X4))=k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X1,X3)),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_77]), c_0_78]), c_0_25]), c_0_79])).
% 4.26/4.45  cnf(c_0_85, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),k2_xboole_0(X1,X4))=k4_xboole_0(X3,k2_xboole_0(X1,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_80])).
% 4.26/4.45  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_30]), c_0_24]), c_0_38]), c_0_83]), c_0_85]), c_0_35]), c_0_41]), c_0_42]), c_0_24])]), ['proof']).
% 4.26/4.45  # SZS output end CNFRefutation
% 4.26/4.45  # Proof object total steps             : 87
% 4.26/4.45  # Proof object clause steps            : 58
% 4.26/4.45  # Proof object formula steps           : 29
% 4.26/4.45  # Proof object conjectures             : 7
% 4.26/4.45  # Proof object clause conjectures      : 4
% 4.26/4.45  # Proof object formula conjectures     : 3
% 4.26/4.45  # Proof object initial clauses used    : 14
% 4.26/4.45  # Proof object initial formulas used   : 14
% 4.26/4.45  # Proof object generating inferences   : 37
% 4.26/4.45  # Proof object simplifying inferences  : 61
% 4.26/4.45  # Training examples: 0 positive, 0 negative
% 4.26/4.45  # Parsed axioms                        : 16
% 4.26/4.45  # Removed by relevancy pruning/SinE    : 0
% 4.26/4.45  # Initial clauses                      : 17
% 4.26/4.45  # Removed in clause preprocessing      : 1
% 4.26/4.45  # Initial clauses in saturation        : 16
% 4.26/4.45  # Processed clauses                    : 10816
% 4.26/4.45  # ...of these trivial                  : 4709
% 4.26/4.45  # ...subsumed                          : 4676
% 4.26/4.45  # ...remaining for further processing  : 1430
% 4.26/4.45  # Other redundant clauses eliminated   : 0
% 4.26/4.45  # Clauses deleted for lack of memory   : 0
% 4.26/4.45  # Backward-subsumed                    : 4
% 4.26/4.45  # Backward-rewritten                   : 282
% 4.26/4.45  # Generated clauses                    : 639440
% 4.26/4.45  # ...of the previous two non-trivial   : 429869
% 4.26/4.45  # Contextual simplify-reflections      : 0
% 4.26/4.45  # Paramodulations                      : 639425
% 4.26/4.45  # Factorizations                       : 0
% 4.26/4.45  # Equation resolutions                 : 15
% 4.26/4.45  # Propositional unsat checks           : 0
% 4.26/4.45  #    Propositional check models        : 0
% 4.26/4.45  #    Propositional check unsatisfiable : 0
% 4.26/4.45  #    Propositional clauses             : 0
% 4.26/4.45  #    Propositional clauses after purity: 0
% 4.26/4.45  #    Propositional unsat core size     : 0
% 4.26/4.45  #    Propositional preprocessing time  : 0.000
% 4.26/4.45  #    Propositional encoding time       : 0.000
% 4.26/4.45  #    Propositional solver time         : 0.000
% 4.26/4.45  #    Success case prop preproc time    : 0.000
% 4.26/4.45  #    Success case prop encoding time   : 0.000
% 4.26/4.45  #    Success case prop solver time     : 0.000
% 4.26/4.45  # Current number of processed clauses  : 1128
% 4.26/4.45  #    Positive orientable unit clauses  : 1047
% 4.26/4.45  #    Positive unorientable unit clauses: 10
% 4.26/4.45  #    Negative unit clauses             : 0
% 4.26/4.45  #    Non-unit-clauses                  : 71
% 4.26/4.45  # Current number of unprocessed clauses: 415414
% 4.26/4.45  # ...number of literals in the above   : 430926
% 4.26/4.45  # Current number of archived formulas  : 0
% 4.26/4.45  # Current number of archived clauses   : 303
% 4.26/4.45  # Clause-clause subsumption calls (NU) : 3060
% 4.26/4.45  # Rec. Clause-clause subsumption calls : 3060
% 4.26/4.45  # Non-unit clause-clause subsumptions  : 808
% 4.26/4.45  # Unit Clause-clause subsumption calls : 206
% 4.26/4.45  # Rewrite failures with RHS unbound    : 0
% 4.26/4.45  # BW rewrite match attempts            : 7492
% 4.26/4.45  # BW rewrite match successes           : 616
% 4.26/4.45  # Condensation attempts                : 0
% 4.26/4.45  # Condensation successes               : 0
% 4.26/4.45  # Termbank termtop insertions          : 7030966
% 4.29/4.47  
% 4.29/4.47  # -------------------------------------------------
% 4.29/4.47  # User time                : 3.905 s
% 4.29/4.47  # System time              : 0.228 s
% 4.29/4.47  # Total time               : 4.133 s
% 4.29/4.47  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
