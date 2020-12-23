%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:31 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 (8197 expanded)
%              Number of clauses        :   53 (3614 expanded)
%              Number of leaves         :   13 (2291 expanded)
%              Depth                    :   16
%              Number of atoms          :   80 (8197 expanded)
%              Number of equality atoms :   79 (8196 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,conjecture,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(c_0_13,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_14,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k5_xboole_0(X21,k4_xboole_0(X22,X21)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_17,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k3_xboole_0(X11,X12)) = X11 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_24,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_19]),c_0_19]),c_0_20]),c_0_20])).

fof(c_0_26,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_19]),c_0_20])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_20]),c_0_20])).

cnf(c_0_34,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_33])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_28])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_34]),c_0_34])).

fof(c_0_39,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_35])).

fof(c_0_42,plain,(
    ! [X18,X19,X20] : k5_xboole_0(k5_xboole_0(X18,X19),X20) = k5_xboole_0(X18,k5_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_34]),c_0_40])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_37]),c_0_40])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_47,plain,(
    ! [X23,X24] : k2_tarski(X23,X24) = k2_xboole_0(k1_tarski(X23),k1_tarski(X24)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_48,plain,(
    ! [X28] : k2_tarski(X28,X28) = k1_tarski(X28) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_51,plain,
    ( k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,negated_conjecture,(
    ~ ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t70_enumset1])).

fof(c_0_55,plain,(
    ! [X25,X26,X27] : k1_enumset1(X25,X26,X27) = k2_xboole_0(k1_tarski(X25),k2_tarski(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_46])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_40])).

cnf(c_0_58,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53]),c_0_19]),c_0_20])).

fof(c_0_59,negated_conjecture,(
    k1_enumset1(esk1_0,esk1_0,esk2_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).

cnf(c_0_60,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_28])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_37]),c_0_37]),c_0_40]),c_0_40])).

cnf(c_0_63,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X1),X2) = k5_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1))) = k5_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_46])).

cnf(c_0_65,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( k1_enumset1(esk1_0,esk1_0,esk2_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_53]),c_0_19]),c_0_20])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_50])).

cnf(c_0_69,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),X3) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)),X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_58]),c_0_46])).

cnf(c_0_70,plain,
    ( k5_xboole_0(k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)),k2_tarski(X1,X2)) = k5_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk2_0),k2_tarski(esk1_0,esk1_0)))) != k2_tarski(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_68]),c_0_50])).

cnf(c_0_73,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_28])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k2_tarski(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_57]),c_0_45])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk2_0)))) != k2_tarski(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_28])).

cnf(c_0_76,plain,
    ( k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2)) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_57])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X2,X1),X3)) = X3 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_74]),c_0_44])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.21/0.42  # and selection function SelectNewComplexAHP.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.040 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.21/0.42  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.42  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.21/0.42  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.21/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.42  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.21/0.42  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.21/0.42  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.21/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.42  fof(t70_enumset1, conjecture, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.42  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.21/0.42  fof(c_0_13, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.21/0.42  fof(c_0_14, plain, ![X21, X22]:k2_xboole_0(X21,X22)=k5_xboole_0(X21,k4_xboole_0(X22,X21)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.42  fof(c_0_15, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.42  fof(c_0_16, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.21/0.42  fof(c_0_17, plain, ![X11, X12]:k2_xboole_0(X11,k3_xboole_0(X11,X12))=X11, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.21/0.42  cnf(c_0_18, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.42  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.42  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.42  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.42  cnf(c_0_22, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.42  fof(c_0_23, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.42  cnf(c_0_24, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.21/0.42  cnf(c_0_25, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.21/0.42  fof(c_0_26, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.42  cnf(c_0_27, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_19]), c_0_20])).
% 0.21/0.42  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.42  cnf(c_0_29, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))=X1), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.42  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.42  cnf(c_0_31, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.42  cnf(c_0_32, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.21/0.42  cnf(c_0_33, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_20]), c_0_20])).
% 0.21/0.42  cnf(c_0_34, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.42  cnf(c_0_35, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_33, c_0_33])).
% 0.21/0.42  cnf(c_0_36, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)))=X1), inference(spm,[status(thm)],[c_0_24, c_0_28])).
% 0.21/0.42  cnf(c_0_37, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_34])).
% 0.21/0.42  cnf(c_0_38, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_34]), c_0_34])).
% 0.21/0.42  fof(c_0_39, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.21/0.42  cnf(c_0_40, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.21/0.42  cnf(c_0_41, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_35])).
% 0.21/0.42  fof(c_0_42, plain, ![X18, X19, X20]:k5_xboole_0(k5_xboole_0(X18,X19),X20)=k5_xboole_0(X18,k5_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.21/0.42  cnf(c_0_43, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.42  cnf(c_0_44, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_34]), c_0_40])).
% 0.21/0.42  cnf(c_0_45, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_37]), c_0_37]), c_0_40])).
% 0.21/0.42  cnf(c_0_46, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.42  fof(c_0_47, plain, ![X23, X24]:k2_tarski(X23,X24)=k2_xboole_0(k1_tarski(X23),k1_tarski(X24)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.21/0.42  fof(c_0_48, plain, ![X28]:k2_tarski(X28,X28)=k1_tarski(X28), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.42  cnf(c_0_49, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_19]), c_0_20]), c_0_20]), c_0_20]), c_0_20])).
% 0.21/0.42  cnf(c_0_50, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.21/0.42  cnf(c_0_51, plain, (k1_xboole_0=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 0.21/0.42  cnf(c_0_52, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.42  cnf(c_0_53, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.42  fof(c_0_54, negated_conjecture, ~(![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t70_enumset1])).
% 0.21/0.42  fof(c_0_55, plain, ![X25, X26, X27]:k1_enumset1(X25,X26,X27)=k2_xboole_0(k1_tarski(X25),k2_tarski(X26,X27)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.21/0.42  cnf(c_0_56, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))), inference(rw,[status(thm)],[c_0_49, c_0_46])).
% 0.21/0.42  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_40])).
% 0.21/0.42  cnf(c_0_58, plain, (k2_tarski(X1,X2)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53]), c_0_19]), c_0_20])).
% 0.21/0.42  fof(c_0_59, negated_conjecture, k1_enumset1(esk1_0,esk1_0,esk2_0)!=k2_tarski(esk1_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).
% 0.21/0.42  cnf(c_0_60, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.42  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))))), inference(spm,[status(thm)],[c_0_56, c_0_28])).
% 0.21/0.42  cnf(c_0_62, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_37]), c_0_37]), c_0_40]), c_0_40])).
% 0.21/0.42  cnf(c_0_63, plain, (k3_xboole_0(k5_xboole_0(X1,X1),X2)=k5_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_34, c_0_45])).
% 0.21/0.42  cnf(c_0_64, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1)))=k5_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_57, c_0_46])).
% 0.21/0.42  cnf(c_0_65, plain, (k2_tarski(X1,X2)=k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))))), inference(spm,[status(thm)],[c_0_25, c_0_58])).
% 0.21/0.42  cnf(c_0_66, negated_conjecture, (k1_enumset1(esk1_0,esk1_0,esk2_0)!=k2_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.42  cnf(c_0_67, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_53]), c_0_19]), c_0_20])).
% 0.21/0.42  cnf(c_0_68, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_50])).
% 0.21/0.42  cnf(c_0_69, plain, (k5_xboole_0(k2_tarski(X1,X2),X3)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)),X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_58]), c_0_46])).
% 0.21/0.42  cnf(c_0_70, plain, (k5_xboole_0(k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)),k2_tarski(X1,X2))=k5_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.42  cnf(c_0_71, negated_conjecture, (k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk2_0),k2_tarski(esk1_0,esk1_0))))!=k2_tarski(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.21/0.42  cnf(c_0_72, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_68]), c_0_50])).
% 0.21/0.42  cnf(c_0_73, plain, (k2_tarski(X1,X2)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))))), inference(spm,[status(thm)],[c_0_58, c_0_28])).
% 0.21/0.42  cnf(c_0_74, plain, (k5_xboole_0(k2_tarski(X1,X2),k2_tarski(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_57]), c_0_45])).
% 0.21/0.42  cnf(c_0_75, negated_conjecture, (k5_xboole_0(k2_tarski(esk1_0,esk1_0),k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk2_0))))!=k2_tarski(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_71, c_0_28])).
% 0.21/0.42  cnf(c_0_76, plain, (k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2))=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.21/0.42  cnf(c_0_77, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_57])).
% 0.21/0.42  cnf(c_0_78, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X2,X1),X3))=X3), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_74]), c_0_44])).
% 0.21/0.42  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78])]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 80
% 0.21/0.42  # Proof object clause steps            : 53
% 0.21/0.42  # Proof object formula steps           : 27
% 0.21/0.42  # Proof object conjectures             : 7
% 0.21/0.42  # Proof object clause conjectures      : 4
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 13
% 0.21/0.42  # Proof object initial formulas used   : 13
% 0.21/0.42  # Proof object generating inferences   : 25
% 0.21/0.42  # Proof object simplifying inferences  : 51
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 13
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 13
% 0.21/0.42  # Removed in clause preprocessing      : 4
% 0.21/0.42  # Initial clauses in saturation        : 9
% 0.21/0.42  # Processed clauses                    : 651
% 0.21/0.42  # ...of these trivial                  : 116
% 0.21/0.42  # ...subsumed                          : 456
% 0.21/0.42  # ...remaining for further processing  : 79
% 0.21/0.42  # Other redundant clauses eliminated   : 0
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 0
% 0.21/0.42  # Backward-rewritten                   : 21
% 0.21/0.42  # Generated clauses                    : 2436
% 0.21/0.42  # ...of the previous two non-trivial   : 1671
% 0.21/0.42  # Contextual simplify-reflections      : 0
% 0.21/0.42  # Paramodulations                      : 2436
% 0.21/0.42  # Factorizations                       : 0
% 0.21/0.42  # Equation resolutions                 : 0
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 49
% 0.21/0.42  #    Positive orientable unit clauses  : 33
% 0.21/0.42  #    Positive unorientable unit clauses: 16
% 0.21/0.42  #    Negative unit clauses             : 0
% 0.21/0.42  #    Non-unit-clauses                  : 0
% 0.21/0.42  # Current number of unprocessed clauses: 912
% 0.21/0.42  # ...number of literals in the above   : 912
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 34
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 0
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.42  # Unit Clause-clause subsumption calls : 69
% 0.21/0.42  # Rewrite failures with RHS unbound    : 46
% 0.21/0.42  # BW rewrite match attempts            : 443
% 0.21/0.42  # BW rewrite match successes           : 237
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 21426
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.077 s
% 0.21/0.43  # System time              : 0.008 s
% 0.21/0.43  # Total time               : 0.086 s
% 0.21/0.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
