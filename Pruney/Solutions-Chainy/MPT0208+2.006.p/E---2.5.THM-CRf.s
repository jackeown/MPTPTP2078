%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 522 expanded)
%              Number of clauses        :   26 ( 191 expanded)
%              Number of leaves         :   13 ( 165 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 522 expanded)
%              Number of equality atoms :   52 ( 521 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t127_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(t134_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(c_0_13,plain,(
    ! [X10,X11,X12] : k2_xboole_0(k2_xboole_0(X10,X11),X12) = k2_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_14,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k5_xboole_0(X13,k4_xboole_0(X14,X13)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53,X54] : k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) = k2_xboole_0(k5_enumset1(X47,X48,X49,X50,X51,X52,X53),k1_tarski(X54)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_16,plain,(
    ! [X55] : k2_tarski(X55,X55) = k1_tarski(X55) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X56,X57] : k1_enumset1(X56,X56,X57) = k2_tarski(X56,X57) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X58,X59,X60] : k2_enumset1(X58,X58,X59,X60) = k1_enumset1(X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X61,X62,X63,X64] : k3_enumset1(X61,X61,X62,X63,X64) = k2_enumset1(X61,X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X65,X66,X67,X68,X69] : k4_enumset1(X65,X65,X66,X67,X68,X69) = k3_enumset1(X65,X66,X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X70,X71,X72,X73,X74,X75] : k5_enumset1(X70,X70,X71,X72,X73,X74,X75) = k4_enumset1(X70,X71,X72,X73,X74,X75) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X76,X77,X78,X79,X80,X81,X82] : k6_enumset1(X76,X76,X77,X78,X79,X80,X81,X82) = k5_enumset1(X76,X77,X78,X79,X80,X81,X82) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_23,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22,X23] : k7_enumset1(X15,X16,X17,X18,X19,X20,X21,X22,X23) = k2_xboole_0(k1_tarski(X15),k6_enumset1(X16,X17,X18,X19,X20,X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[t127_enumset1])).

fof(c_0_24,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46] : k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) = k2_xboole_0(k1_tarski(X39),k5_enumset1(X40,X41,X42,X43,X44,X45,X46)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(assume_negation,[status(cth)],[t134_enumset1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_38,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_27]),c_0_27])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_27]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_41,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_29]),c_0_30]),c_0_27]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_29]),c_0_30]),c_0_27]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k4_xboole_0(X9,k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))) = k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k4_xboole_0(X9,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k5_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k4_xboole_0(X10,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k5_xboole_0(k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9),k4_xboole_0(X10,k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_46,plain,
    ( k7_enumset1(X1,X2,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k5_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k4_xboole_0(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_29]),c_0_30]),c_0_27]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))) = k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k4_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_40])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k4_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_41]),c_0_46]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k4_xboole_0(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk9_0),k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))) != k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.028 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.43  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.43  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 0.20/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.43  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.43  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.43  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.43  fof(t127_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 0.20/0.43  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 0.20/0.43  fof(t134_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 0.20/0.43  fof(c_0_13, plain, ![X10, X11, X12]:k2_xboole_0(k2_xboole_0(X10,X11),X12)=k2_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.43  fof(c_0_14, plain, ![X13, X14]:k2_xboole_0(X13,X14)=k5_xboole_0(X13,k4_xboole_0(X14,X13)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.43  fof(c_0_15, plain, ![X47, X48, X49, X50, X51, X52, X53, X54]:k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)=k2_xboole_0(k5_enumset1(X47,X48,X49,X50,X51,X52,X53),k1_tarski(X54)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 0.20/0.43  fof(c_0_16, plain, ![X55]:k2_tarski(X55,X55)=k1_tarski(X55), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.43  fof(c_0_17, plain, ![X56, X57]:k1_enumset1(X56,X56,X57)=k2_tarski(X56,X57), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.43  fof(c_0_18, plain, ![X58, X59, X60]:k2_enumset1(X58,X58,X59,X60)=k1_enumset1(X58,X59,X60), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.43  fof(c_0_19, plain, ![X61, X62, X63, X64]:k3_enumset1(X61,X61,X62,X63,X64)=k2_enumset1(X61,X62,X63,X64), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.43  fof(c_0_20, plain, ![X65, X66, X67, X68, X69]:k4_enumset1(X65,X65,X66,X67,X68,X69)=k3_enumset1(X65,X66,X67,X68,X69), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.43  fof(c_0_21, plain, ![X70, X71, X72, X73, X74, X75]:k5_enumset1(X70,X70,X71,X72,X73,X74,X75)=k4_enumset1(X70,X71,X72,X73,X74,X75), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.43  fof(c_0_22, plain, ![X76, X77, X78, X79, X80, X81, X82]:k6_enumset1(X76,X76,X77,X78,X79,X80,X81,X82)=k5_enumset1(X76,X77,X78,X79,X80,X81,X82), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.43  fof(c_0_23, plain, ![X15, X16, X17, X18, X19, X20, X21, X22, X23]:k7_enumset1(X15,X16,X17,X18,X19,X20,X21,X22,X23)=k2_xboole_0(k1_tarski(X15),k6_enumset1(X16,X17,X18,X19,X20,X21,X22,X23)), inference(variable_rename,[status(thm)],[t127_enumset1])).
% 0.20/0.43  fof(c_0_24, plain, ![X39, X40, X41, X42, X43, X44, X45, X46]:k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)=k2_xboole_0(k1_tarski(X39),k5_enumset1(X40,X41,X42,X43,X44,X45,X46)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.20/0.43  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(assume_negation,[status(cth)],[t134_enumset1])).
% 0.20/0.43  cnf(c_0_26, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_28, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.43  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_36, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_37, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  fof(c_0_38, negated_conjecture, k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.20/0.43  cnf(c_0_39, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27]), c_0_27]), c_0_27])).
% 0.20/0.43  cnf(c_0_40, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_27]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_35]), c_0_35])).
% 0.20/0.43  cnf(c_0_41, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_29]), c_0_30]), c_0_27]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.20/0.43  cnf(c_0_42, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_29]), c_0_30]), c_0_27]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35])).
% 0.20/0.43  cnf(c_0_43, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.43  cnf(c_0_44, plain, (k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k4_xboole_0(X9,k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))=k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k4_xboole_0(X9,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.43  cnf(c_0_45, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k5_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k4_xboole_0(X10,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=k5_xboole_0(k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9),k4_xboole_0(X10,k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)))), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 0.20/0.43  cnf(c_0_46, plain, (k7_enumset1(X1,X2,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_42, c_0_41])).
% 0.20/0.43  cnf(c_0_47, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k5_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k4_xboole_0(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_29]), c_0_30]), c_0_27]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.43  cnf(c_0_48, plain, (k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))=k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k4_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))), inference(spm,[status(thm)],[c_0_44, c_0_40])).
% 0.20/0.43  cnf(c_0_49, plain, (k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k4_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_41]), c_0_46]), c_0_46])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k4_xboole_0(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk9_0),k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)))!=k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.43  cnf(c_0_51, plain, (k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.43  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 53
% 0.20/0.43  # Proof object clause steps            : 26
% 0.20/0.43  # Proof object formula steps           : 27
% 0.20/0.43  # Proof object conjectures             : 7
% 0.20/0.43  # Proof object clause conjectures      : 4
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 13
% 0.20/0.43  # Proof object initial formulas used   : 13
% 0.20/0.43  # Proof object generating inferences   : 4
% 0.20/0.43  # Proof object simplifying inferences  : 57
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 16
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 16
% 0.20/0.43  # Removed in clause preprocessing      : 8
% 0.20/0.43  # Initial clauses in saturation        : 8
% 0.20/0.43  # Processed clauses                    : 490
% 0.20/0.43  # ...of these trivial                  : 14
% 0.20/0.43  # ...subsumed                          : 409
% 0.20/0.43  # ...remaining for further processing  : 67
% 0.20/0.43  # Other redundant clauses eliminated   : 0
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 6
% 0.20/0.43  # Backward-rewritten                   : 7
% 0.20/0.43  # Generated clauses                    : 5259
% 0.20/0.43  # ...of the previous two non-trivial   : 4388
% 0.20/0.43  # Contextual simplify-reflections      : 0
% 0.20/0.43  # Paramodulations                      : 5259
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 0
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 46
% 0.20/0.43  #    Positive orientable unit clauses  : 12
% 0.20/0.43  #    Positive unorientable unit clauses: 34
% 0.20/0.43  #    Negative unit clauses             : 0
% 0.20/0.43  #    Non-unit-clauses                  : 0
% 0.20/0.43  # Current number of unprocessed clauses: 3838
% 0.20/0.43  # ...number of literals in the above   : 3838
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 29
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.43  # Unit Clause-clause subsumption calls : 767
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 1903
% 0.20/0.43  # BW rewrite match successes           : 555
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 49262
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.084 s
% 0.20/0.43  # System time              : 0.006 s
% 0.20/0.43  # Total time               : 0.091 s
% 0.20/0.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
