%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:38 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 515 expanded)
%              Number of clauses        :   35 ( 216 expanded)
%              Number of leaves         :   13 ( 149 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 ( 515 expanded)
%              Number of equality atoms :   61 ( 514 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(t52_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(t64_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(t71_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(c_0_13,plain,(
    ! [X20,X21,X22,X23] : k2_enumset1(X20,X21,X22,X23) = k2_xboole_0(k1_tarski(X20),k1_enumset1(X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_14,plain,(
    ! [X62] : k2_tarski(X62,X62) = k1_tarski(X62) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X63,X64] : k1_enumset1(X63,X63,X64) = k2_tarski(X63,X64) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k5_xboole_0(X9,k4_xboole_0(X10,X9)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_17,plain,(
    ! [X11,X12,X13,X14,X15,X16] : k4_enumset1(X11,X12,X13,X14,X15,X16) = k2_xboole_0(k1_enumset1(X11,X12,X13),k1_enumset1(X14,X15,X16)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

fof(c_0_18,plain,(
    ! [X29,X30,X31,X32,X33] : k3_enumset1(X29,X30,X31,X32,X33) = k2_xboole_0(k2_tarski(X29,X30),k1_enumset1(X31,X32,X33)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_19,plain,(
    ! [X34,X35,X36,X37,X38,X39] : k4_enumset1(X34,X35,X36,X37,X38,X39) = k2_xboole_0(k2_tarski(X34,X35),k2_enumset1(X36,X37,X38,X39)) ),
    inference(variable_rename,[status(thm)],[t52_enumset1])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52,X53] : k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53) = k2_xboole_0(k2_tarski(X46,X47),k4_enumset1(X48,X49,X50,X51,X52,X53)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

fof(c_0_26,plain,(
    ! [X24,X25,X26,X27,X28] : k3_enumset1(X24,X25,X26,X27,X28) = k2_xboole_0(k1_tarski(X24),k2_enumset1(X25,X26,X27,X28)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_31,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X54,X55,X56,X57,X58,X59,X60,X61] : k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) = k2_xboole_0(k1_enumset1(X54,X55,X56),k3_enumset1(X57,X58,X59,X60,X61)) ),
    inference(variable_rename,[status(thm)],[t64_enumset1])).

fof(c_0_33,plain,(
    ! [X17,X18,X19] : k1_enumset1(X17,X18,X19) = k2_xboole_0(k2_tarski(X17,X18),k1_tarski(X19)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_22]),c_0_23])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))) = k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X3,X3,X3))),k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_22]),c_0_23]),c_0_29]),c_0_30])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X4,X5),k4_xboole_0(k1_enumset1(X6,X7,X8),k1_enumset1(X3,X4,X5))),k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_22]),c_0_23]),c_0_30])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t71_enumset1])).

fof(c_0_41,plain,(
    ! [X40,X41,X42,X43,X44,X45] : k4_enumset1(X40,X41,X42,X43,X44,X45) = k2_xboole_0(k3_enumset1(X40,X41,X42,X43,X44),k1_tarski(X45)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))) = k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_21]),c_0_22]),c_0_23]),c_0_29]),c_0_35])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X2,X3,X3,X3,X4,X5,X6) = k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_enumset1(X4,X4,X5),k4_xboole_0(k1_enumset1(X6,X7,X8),k1_enumset1(X4,X4,X5))),k1_enumset1(X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_23]),c_0_35])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_21]),c_0_22]),c_0_22]),c_0_23])).

fof(c_0_46,negated_conjecture,(
    k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k1_enumset1(X1,X1,X1))) = k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X6) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))),k4_xboole_0(k1_enumset1(X6,X6,X6),k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_21]),c_0_22]),c_0_23]),c_0_35]),c_0_35]),c_0_30])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X2,X3,X3,X4,X5,X6,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(spm,[status(thm)],[c_0_44,c_0_37])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X2,X2,X2,X2,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_37]),c_0_45])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k6_enumset1(X4,X4,X5,X5,X5,X6,X7,X8),k1_enumset1(X1,X2,X3))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k4_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk1_0,esk1_0,esk1_0))) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X2,X2,X2,X3,X4,X5),k4_xboole_0(k1_enumset1(X6,X6,X6),k6_enumset1(X1,X1,X2,X2,X2,X3,X4,X5))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_43])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X1,X1,X2,X2,X2,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))) = k6_enumset1(X1,X1,X1,X2,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_48,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_43])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_45]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:41 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.026 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.38  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 0.20/0.38  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 0.20/0.38  fof(t52_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 0.20/0.38  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 0.20/0.38  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.20/0.38  fof(t64_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_enumset1)).
% 0.20/0.38  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.20/0.38  fof(t71_enumset1, conjecture, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.20/0.38  fof(c_0_13, plain, ![X20, X21, X22, X23]:k2_enumset1(X20,X21,X22,X23)=k2_xboole_0(k1_tarski(X20),k1_enumset1(X21,X22,X23)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.20/0.38  fof(c_0_14, plain, ![X62]:k2_tarski(X62,X62)=k1_tarski(X62), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_15, plain, ![X63, X64]:k1_enumset1(X63,X63,X64)=k2_tarski(X63,X64), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_16, plain, ![X9, X10]:k2_xboole_0(X9,X10)=k5_xboole_0(X9,k4_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.38  fof(c_0_17, plain, ![X11, X12, X13, X14, X15, X16]:k4_enumset1(X11,X12,X13,X14,X15,X16)=k2_xboole_0(k1_enumset1(X11,X12,X13),k1_enumset1(X14,X15,X16)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 0.20/0.38  fof(c_0_18, plain, ![X29, X30, X31, X32, X33]:k3_enumset1(X29,X30,X31,X32,X33)=k2_xboole_0(k2_tarski(X29,X30),k1_enumset1(X31,X32,X33)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.20/0.38  fof(c_0_19, plain, ![X34, X35, X36, X37, X38, X39]:k4_enumset1(X34,X35,X36,X37,X38,X39)=k2_xboole_0(k2_tarski(X34,X35),k2_enumset1(X36,X37,X38,X39)), inference(variable_rename,[status(thm)],[t52_enumset1])).
% 0.20/0.38  cnf(c_0_20, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_24, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  fof(c_0_25, plain, ![X46, X47, X48, X49, X50, X51, X52, X53]:k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53)=k2_xboole_0(k2_tarski(X46,X47),k4_enumset1(X48,X49,X50,X51,X52,X53)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 0.20/0.38  fof(c_0_26, plain, ![X24, X25, X26, X27, X28]:k3_enumset1(X24,X25,X26,X27,X28)=k2_xboole_0(k1_tarski(X24),k2_enumset1(X25,X26,X27,X28)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.20/0.38  cnf(c_0_27, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_28, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_29, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])).
% 0.20/0.38  cnf(c_0_30, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))), inference(rw,[status(thm)],[c_0_24, c_0_23])).
% 0.20/0.38  cnf(c_0_31, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  fof(c_0_32, plain, ![X54, X55, X56, X57, X58, X59, X60, X61]:k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)=k2_xboole_0(k1_enumset1(X54,X55,X56),k3_enumset1(X57,X58,X59,X60,X61)), inference(variable_rename,[status(thm)],[t64_enumset1])).
% 0.20/0.38  fof(c_0_33, plain, ![X17, X18, X19]:k1_enumset1(X17,X18,X19)=k2_xboole_0(k2_tarski(X17,X18),k1_tarski(X19)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.20/0.38  cnf(c_0_34, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_35, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_22]), c_0_23])).
% 0.20/0.38  cnf(c_0_36, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))=k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X3,X3,X3))),k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_22]), c_0_23]), c_0_29]), c_0_30])).
% 0.20/0.38  cnf(c_0_37, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X4,X5),k4_xboole_0(k1_enumset1(X6,X7,X8),k1_enumset1(X3,X4,X5))),k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_22]), c_0_23]), c_0_30])).
% 0.20/0.38  cnf(c_0_38, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_39, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  fof(c_0_40, negated_conjecture, ~(![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_41, plain, ![X40, X41, X42, X43, X44, X45]:k4_enumset1(X40,X41,X42,X43,X44,X45)=k2_xboole_0(k3_enumset1(X40,X41,X42,X43,X44),k1_tarski(X45)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.20/0.38  cnf(c_0_42, plain, (k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))=k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_21]), c_0_22]), c_0_23]), c_0_29]), c_0_35])).
% 0.20/0.38  cnf(c_0_43, plain, (k6_enumset1(X1,X2,X3,X3,X3,X4,X5,X6)=k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.38  cnf(c_0_44, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_enumset1(X4,X4,X5),k4_xboole_0(k1_enumset1(X6,X7,X8),k1_enumset1(X4,X4,X5))),k1_enumset1(X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_23]), c_0_35])).
% 0.20/0.38  cnf(c_0_45, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_21]), c_0_22]), c_0_22]), c_0_23])).
% 0.20/0.38  fof(c_0_46, negated_conjecture, k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).
% 0.20/0.38  cnf(c_0_47, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.38  cnf(c_0_48, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k1_enumset1(X1,X1,X1)))=k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.38  cnf(c_0_49, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X6)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.38  cnf(c_0_51, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))),k4_xboole_0(k1_enumset1(X6,X6,X6),k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_21]), c_0_22]), c_0_23]), c_0_35]), c_0_35]), c_0_30])).
% 0.20/0.38  cnf(c_0_52, plain, (k6_enumset1(X1,X2,X3,X3,X4,X5,X6,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(spm,[status(thm)],[c_0_44, c_0_37])).
% 0.20/0.38  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X2,X2,X2,X2,X2,X3)=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_37]), c_0_45])).
% 0.20/0.38  cnf(c_0_54, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k6_enumset1(X4,X4,X5,X5,X5,X6,X7,X8),k1_enumset1(X1,X2,X3)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k4_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk1_0,esk1_0,esk1_0)))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_50, c_0_29])).
% 0.20/0.38  cnf(c_0_56, plain, (k5_xboole_0(k6_enumset1(X1,X1,X2,X2,X2,X3,X4,X5),k4_xboole_0(k1_enumset1(X6,X6,X6),k6_enumset1(X1,X1,X2,X2,X2,X3,X4,X5)))=k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))), inference(spm,[status(thm)],[c_0_51, c_0_43])).
% 0.20/0.38  cnf(c_0_57, plain, (k6_enumset1(X1,X1,X1,X2,X2,X2,X2,X3)=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.38  cnf(c_0_58, plain, (k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))=k6_enumset1(X1,X1,X1,X2,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_48, c_0_54])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_55, c_0_43])).
% 0.20/0.38  cnf(c_0_60, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_45]), c_0_58])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 62
% 0.20/0.38  # Proof object clause steps            : 35
% 0.20/0.38  # Proof object formula steps           : 27
% 0.20/0.38  # Proof object conjectures             : 7
% 0.20/0.38  # Proof object clause conjectures      : 4
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 13
% 0.20/0.38  # Proof object initial formulas used   : 13
% 0.20/0.38  # Proof object generating inferences   : 7
% 0.20/0.38  # Proof object simplifying inferences  : 41
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 13
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 13
% 0.20/0.38  # Removed in clause preprocessing      : 6
% 0.20/0.38  # Initial clauses in saturation        : 7
% 0.20/0.38  # Processed clauses                    : 101
% 0.20/0.38  # ...of these trivial                  : 23
% 0.20/0.38  # ...subsumed                          : 35
% 0.20/0.38  # ...remaining for further processing  : 43
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 9
% 0.20/0.38  # Generated clauses                    : 354
% 0.20/0.38  # ...of the previous two non-trivial   : 225
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 354
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 27
% 0.20/0.38  #    Positive orientable unit clauses  : 21
% 0.20/0.38  #    Positive unorientable unit clauses: 6
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 0
% 0.20/0.38  # Current number of unprocessed clauses: 137
% 0.20/0.38  # ...number of literals in the above   : 137
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 22
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 23
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 411
% 0.20/0.38  # BW rewrite match successes           : 44
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3936
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
