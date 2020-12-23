%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 (1015 expanded)
%              Number of clauses        :   38 ( 386 expanded)
%              Number of leaves         :   17 ( 314 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 (1015 expanded)
%              Number of equality atoms :   72 (1014 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(t131_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(t52_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_18,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(X14,k4_xboole_0(X15,X14)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_19,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_21,plain,(
    ! [X66,X67] : k1_enumset1(X66,X66,X67) = k2_tarski(X66,X67) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X68,X69,X70] : k2_enumset1(X68,X68,X69,X70) = k1_enumset1(X68,X69,X70) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X71,X72,X73,X74] : k3_enumset1(X71,X71,X72,X73,X74) = k2_enumset1(X71,X72,X73,X74) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_32,plain,(
    ! [X37,X38,X39,X40] : k2_enumset1(X37,X38,X39,X40) = k2_enumset1(X40,X39,X38,X37) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_33,plain,(
    ! [X50,X51,X52,X53] : k2_enumset1(X50,X51,X52,X53) = k2_xboole_0(k1_enumset1(X50,X51,X52),k1_tarski(X53)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_34,plain,(
    ! [X65] : k2_tarski(X65,X65) = k1_tarski(X65) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_35,plain,(
    ! [X20,X21,X22,X23,X24] : k3_enumset1(X20,X21,X22,X23,X24) = k2_xboole_0(k1_enumset1(X20,X21,X22),k2_tarski(X23,X24)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_42,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48,X49] : k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) = k2_xboole_0(k3_enumset1(X41,X42,X43,X44,X45),k2_enumset1(X46,X47,X48,X49)) ),
    inference(variable_rename,[status(thm)],[t131_enumset1])).

fof(c_0_43,plain,(
    ! [X59,X60,X61,X62,X63,X64] : k4_enumset1(X59,X60,X61,X62,X63,X64) = k2_xboole_0(k2_tarski(X59,X60),k2_enumset1(X61,X62,X63,X64)) ),
    inference(variable_rename,[status(thm)],[t52_enumset1])).

fof(c_0_44,plain,(
    ! [X54,X55,X56,X57,X58] : k3_enumset1(X54,X55,X56,X57,X58) = k2_xboole_0(k2_tarski(X54,X55),k1_enumset1(X56,X57,X58)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_45,plain,(
    ! [X16,X17,X18,X19] : k2_enumset1(X16,X17,X18,X19) = k2_xboole_0(k2_tarski(X16,X17),k2_tarski(X18,X19)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_46,plain,(
    ! [X29,X30,X31,X32] : k2_enumset1(X29,X30,X31,X32) = k2_enumset1(X29,X32,X31,X30) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

fof(c_0_47,plain,(
    ! [X25,X26,X27,X28] : k2_enumset1(X25,X26,X27,X28) = k2_enumset1(X25,X27,X28,X26) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_30]),c_0_30])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_52,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_59,plain,
    ( k3_enumset1(X1,X2,X3,X4,X4) = k3_enumset1(X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(k3_enumset1(X6,X6,X7,X8,X9),k3_xboole_0(k3_enumset1(X6,X6,X7,X8,X9),k3_enumset1(X1,X2,X3,X4,X5)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_28]),c_0_30]),c_0_30])).

cnf(c_0_61,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_62,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_63,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_27]),c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_64,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_30]),c_0_30])).

cnf(c_0_65,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_30]),c_0_30])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(k3_enumset1(X6,X6,X7,X8,X9),k3_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X6,X6,X7,X8,X9)))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(spm,[status(thm)],[c_0_60,c_0_37])).

cnf(c_0_68,plain,
    ( k7_enumset1(X1,X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_69,plain,
    ( k4_enumset1(X1,X2,X3,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_70,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_63,c_0_62])).

cnf(c_0_71,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69]),c_0_70]),c_0_65]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:46:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.027 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 0.20/0.45  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.45  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 0.20/0.45  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.20/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.45  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 0.20/0.45  fof(t131_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_enumset1)).
% 0.20/0.45  fof(t52_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 0.20/0.45  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 0.20/0.45  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.20/0.45  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 0.20/0.45  fof(t105_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 0.20/0.45  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.20/0.45  fof(c_0_18, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(X14,k4_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.45  fof(c_0_19, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.45  fof(c_0_20, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.20/0.45  fof(c_0_21, plain, ![X66, X67]:k1_enumset1(X66,X66,X67)=k2_tarski(X66,X67), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.45  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  fof(c_0_24, plain, ![X68, X69, X70]:k2_enumset1(X68,X68,X69,X70)=k1_enumset1(X68,X69,X70), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.45  fof(c_0_25, plain, ![X71, X72, X73, X74]:k3_enumset1(X71,X71,X72,X73,X74)=k2_enumset1(X71,X72,X73,X74), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.45  cnf(c_0_26, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.45  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.45  fof(c_0_31, plain, ![X10, X11]:k3_xboole_0(X10,X11)=k3_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.45  fof(c_0_32, plain, ![X37, X38, X39, X40]:k2_enumset1(X37,X38,X39,X40)=k2_enumset1(X40,X39,X38,X37), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.20/0.45  fof(c_0_33, plain, ![X50, X51, X52, X53]:k2_enumset1(X50,X51,X52,X53)=k2_xboole_0(k1_enumset1(X50,X51,X52),k1_tarski(X53)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.20/0.45  fof(c_0_34, plain, ![X65]:k2_tarski(X65,X65)=k1_tarski(X65), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.45  fof(c_0_35, plain, ![X20, X21, X22, X23, X24]:k3_enumset1(X20,X21,X22,X23,X24)=k2_xboole_0(k1_enumset1(X20,X21,X22),k2_tarski(X23,X24)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.20/0.45  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.45  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.45  cnf(c_0_38, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.45  cnf(c_0_39, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.45  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.45  cnf(c_0_41, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.45  fof(c_0_42, plain, ![X41, X42, X43, X44, X45, X46, X47, X48, X49]:k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)=k2_xboole_0(k3_enumset1(X41,X42,X43,X44,X45),k2_enumset1(X46,X47,X48,X49)), inference(variable_rename,[status(thm)],[t131_enumset1])).
% 0.20/0.45  fof(c_0_43, plain, ![X59, X60, X61, X62, X63, X64]:k4_enumset1(X59,X60,X61,X62,X63,X64)=k2_xboole_0(k2_tarski(X59,X60),k2_enumset1(X61,X62,X63,X64)), inference(variable_rename,[status(thm)],[t52_enumset1])).
% 0.20/0.45  fof(c_0_44, plain, ![X54, X55, X56, X57, X58]:k3_enumset1(X54,X55,X56,X57,X58)=k2_xboole_0(k2_tarski(X54,X55),k1_enumset1(X56,X57,X58)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.20/0.45  fof(c_0_45, plain, ![X16, X17, X18, X19]:k2_enumset1(X16,X17,X18,X19)=k2_xboole_0(k2_tarski(X16,X17),k2_tarski(X18,X19)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.20/0.45  fof(c_0_46, plain, ![X29, X30, X31, X32]:k2_enumset1(X29,X30,X31,X32)=k2_enumset1(X29,X32,X31,X30), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 0.20/0.45  fof(c_0_47, plain, ![X25, X26, X27, X28]:k2_enumset1(X25,X26,X27,X28)=k2_enumset1(X25,X27,X28,X26), inference(variable_rename,[status(thm)],[t105_enumset1])).
% 0.20/0.45  cnf(c_0_48, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.45  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_30]), c_0_30])).
% 0.20/0.45  cnf(c_0_50, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.45  cnf(c_0_51, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.45  cnf(c_0_52, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.45  cnf(c_0_53, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_tarski(X1,X2),k2_enumset1(X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.45  cnf(c_0_54, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  cnf(c_0_55, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.45  cnf(c_0_56, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.45  cnf(c_0_57, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.45  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_49]), c_0_49]), c_0_49])).
% 0.20/0.45  cnf(c_0_59, plain, (k3_enumset1(X1,X2,X3,X4,X4)=k3_enumset1(X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.45  cnf(c_0_60, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(k3_enumset1(X6,X6,X7,X8,X9),k3_xboole_0(k3_enumset1(X6,X6,X7,X8,X9),k3_enumset1(X1,X2,X3,X4,X5))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_28]), c_0_30]), c_0_30])).
% 0.20/0.45  cnf(c_0_61, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X3,X3,X4,X5,X6),k3_enumset1(X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.45  cnf(c_0_62, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.45  cnf(c_0_63, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_27]), c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.45  cnf(c_0_64, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_30]), c_0_30])).
% 0.20/0.45  cnf(c_0_65, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_30]), c_0_30])).
% 0.20/0.45  cnf(c_0_66, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59]), c_0_59])).
% 0.20/0.45  cnf(c_0_67, plain, (k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(k3_enumset1(X6,X6,X7,X8,X9),k3_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X6,X6,X7,X8,X9))))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(spm,[status(thm)],[c_0_60, c_0_37])).
% 0.20/0.45  cnf(c_0_68, plain, (k7_enumset1(X1,X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_61, c_0_60])).
% 0.20/0.45  cnf(c_0_69, plain, (k4_enumset1(X1,X2,X3,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_62, c_0_61])).
% 0.20/0.45  cnf(c_0_70, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_63, c_0_62])).
% 0.20/0.45  cnf(c_0_71, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X2,X4,X3)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.45  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69]), c_0_70]), c_0_65]), c_0_71])]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 73
% 0.20/0.45  # Proof object clause steps            : 38
% 0.20/0.45  # Proof object formula steps           : 35
% 0.20/0.45  # Proof object conjectures             : 9
% 0.20/0.45  # Proof object clause conjectures      : 6
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 17
% 0.20/0.45  # Proof object initial formulas used   : 17
% 0.20/0.45  # Proof object generating inferences   : 2
% 0.20/0.45  # Proof object simplifying inferences  : 99
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 18
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 18
% 0.20/0.45  # Removed in clause preprocessing      : 6
% 0.20/0.45  # Initial clauses in saturation        : 12
% 0.20/0.45  # Processed clauses                    : 391
% 0.20/0.45  # ...of these trivial                  : 2
% 0.20/0.45  # ...subsumed                          : 276
% 0.20/0.45  # ...remaining for further processing  : 113
% 0.20/0.45  # Other redundant clauses eliminated   : 0
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 2
% 0.20/0.45  # Backward-rewritten                   : 6
% 0.20/0.45  # Generated clauses                    : 12723
% 0.20/0.45  # ...of the previous two non-trivial   : 12107
% 0.20/0.45  # Contextual simplify-reflections      : 0
% 0.20/0.45  # Paramodulations                      : 12723
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
% 0.20/0.45  # Current number of processed clauses  : 93
% 0.20/0.45  #    Positive orientable unit clauses  : 9
% 0.20/0.45  #    Positive unorientable unit clauses: 84
% 0.20/0.45  #    Negative unit clauses             : 0
% 0.20/0.45  #    Non-unit-clauses                  : 0
% 0.20/0.45  # Current number of unprocessed clauses: 11740
% 0.20/0.45  # ...number of literals in the above   : 11740
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 26
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.45  # Unit Clause-clause subsumption calls : 2785
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 5215
% 0.20/0.45  # BW rewrite match successes           : 2142
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 39584
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.099 s
% 0.20/0.45  # System time              : 0.008 s
% 0.20/0.45  # Total time               : 0.107 s
% 0.20/0.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
