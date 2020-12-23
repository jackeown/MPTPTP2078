%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:52 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   72 (1736 expanded)
%              Number of clauses        :   41 ( 635 expanded)
%              Number of leaves         :   15 ( 550 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 (1736 expanded)
%              Number of equality atoms :   71 (1735 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t98_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t102_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(t100_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(c_0_15,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_18,plain,(
    ! [X23,X24,X25,X26,X27,X28] : k4_enumset1(X23,X24,X25,X26,X27,X28) = k2_xboole_0(k3_enumset1(X23,X24,X25,X26,X27),k1_tarski(X28)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X45,X46,X47,X48,X49] : k4_enumset1(X45,X45,X46,X47,X48,X49) = k3_enumset1(X45,X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X50,X51,X52,X53,X54,X55] : k5_enumset1(X50,X50,X51,X52,X53,X54,X55) = k4_enumset1(X50,X51,X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X56,X57,X58,X59,X60,X61,X62] : k6_enumset1(X56,X56,X57,X58,X59,X60,X61,X62) = k5_enumset1(X56,X57,X58,X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_24,plain,(
    ! [X63,X64,X65] : k1_enumset1(X63,X64,X65) = k1_enumset1(X63,X65,X64) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

fof(c_0_25,plain,(
    ! [X38,X39,X40] : k2_enumset1(X38,X38,X39,X40) = k1_enumset1(X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X41,X42,X43,X44] : k3_enumset1(X41,X41,X42,X43,X44) = k2_enumset1(X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35] : k5_enumset1(X29,X30,X31,X32,X33,X34,X35) = k2_xboole_0(k3_enumset1(X29,X30,X31,X32,X33),k2_tarski(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

fof(c_0_28,plain,(
    ! [X36,X37] : k1_enumset1(X36,X36,X37) = k2_tarski(X36,X37) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X15,X16,X17] : k1_enumset1(X15,X16,X17) = k1_enumset1(X17,X16,X15) ),
    inference(variable_rename,[status(thm)],[t102_enumset1])).

fof(c_0_30,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_31,plain,(
    ! [X12,X13,X14] : k1_enumset1(X12,X13,X14) = k1_enumset1(X13,X14,X12) ),
    inference(variable_rename,[status(thm)],[t100_enumset1])).

fof(c_0_32,plain,(
    ! [X18,X19,X20,X21,X22] : k3_enumset1(X18,X19,X20,X21,X22) = k2_xboole_0(k1_tarski(X18),k2_enumset1(X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_34]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_42]),c_0_42]),c_0_34]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_34]),c_0_40]),c_0_40]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_54,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X3,X2,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_47])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k6_enumset1(X3,X3,X3,X3,X2,X1,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0)))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_50]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X7),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))) = k6_enumset1(X1,X1,X2,X3,X4,X5,X7,X6) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X3,X3,X3,X3,X3,X1,X2,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_52]),c_0_47])).

cnf(c_0_59,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2),k1_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_50])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4) = k6_enumset1(X2,X2,X2,X2,X2,X3,X1,X4) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk3_0,esk1_0) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X3,X3,X2,X4) ),
    inference(spm,[status(thm)],[c_0_58,c_0_55])).

cnf(c_0_63,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X4,X4,X3,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_59])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X7,X7,X7,X6),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X7,X7,X7,X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(spm,[status(thm)],[c_0_57,c_0_60])).

cnf(c_0_65,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X3),k1_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_48])).

cnf(c_0_66,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X3),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X1,X4,X5),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X1,X4,X5),k1_tarski(X3)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk1_0) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_54])).

cnf(c_0_68,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X7,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_63]),c_0_64])).

cnf(c_0_69,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X1,X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_58])).

cnf(c_0_70,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4) = k6_enumset1(X2,X2,X2,X2,X2,X1,X4,X3) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:51:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.92/1.13  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.92/1.13  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.92/1.13  #
% 0.92/1.13  # Preprocessing time       : 0.026 s
% 0.92/1.13  # Presaturation interreduction done
% 0.92/1.13  
% 0.92/1.13  # Proof found!
% 0.92/1.13  # SZS status Theorem
% 0.92/1.13  # SZS output start CNFRefutation
% 0.92/1.13  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.92/1.13  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.92/1.13  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 0.92/1.13  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.92/1.13  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.92/1.13  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.92/1.13  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.92/1.13  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 0.92/1.13  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.92/1.13  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.92/1.13  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 0.92/1.13  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.92/1.13  fof(t102_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 0.92/1.13  fof(t100_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 0.92/1.13  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.92/1.13  fof(c_0_15, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k5_xboole_0(X10,k4_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.92/1.13  fof(c_0_16, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.92/1.13  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.92/1.13  fof(c_0_18, plain, ![X23, X24, X25, X26, X27, X28]:k4_enumset1(X23,X24,X25,X26,X27,X28)=k2_xboole_0(k3_enumset1(X23,X24,X25,X26,X27),k1_tarski(X28)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.92/1.13  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.92/1.13  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.92/1.13  fof(c_0_21, plain, ![X45, X46, X47, X48, X49]:k4_enumset1(X45,X45,X46,X47,X48,X49)=k3_enumset1(X45,X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.92/1.13  fof(c_0_22, plain, ![X50, X51, X52, X53, X54, X55]:k5_enumset1(X50,X50,X51,X52,X53,X54,X55)=k4_enumset1(X50,X51,X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.92/1.13  fof(c_0_23, plain, ![X56, X57, X58, X59, X60, X61, X62]:k6_enumset1(X56,X56,X57,X58,X59,X60,X61,X62)=k5_enumset1(X56,X57,X58,X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.92/1.13  fof(c_0_24, plain, ![X63, X64, X65]:k1_enumset1(X63,X64,X65)=k1_enumset1(X63,X65,X64), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 0.92/1.13  fof(c_0_25, plain, ![X38, X39, X40]:k2_enumset1(X38,X38,X39,X40)=k1_enumset1(X38,X39,X40), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.92/1.13  fof(c_0_26, plain, ![X41, X42, X43, X44]:k3_enumset1(X41,X41,X42,X43,X44)=k2_enumset1(X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.92/1.13  fof(c_0_27, plain, ![X29, X30, X31, X32, X33, X34, X35]:k5_enumset1(X29,X30,X31,X32,X33,X34,X35)=k2_xboole_0(k3_enumset1(X29,X30,X31,X32,X33),k2_tarski(X34,X35)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 0.92/1.13  fof(c_0_28, plain, ![X36, X37]:k1_enumset1(X36,X36,X37)=k2_tarski(X36,X37), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.92/1.13  fof(c_0_29, plain, ![X15, X16, X17]:k1_enumset1(X15,X16,X17)=k1_enumset1(X17,X16,X15), inference(variable_rename,[status(thm)],[t102_enumset1])).
% 0.92/1.13  fof(c_0_30, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.92/1.13  fof(c_0_31, plain, ![X12, X13, X14]:k1_enumset1(X12,X13,X14)=k1_enumset1(X13,X14,X12), inference(variable_rename,[status(thm)],[t100_enumset1])).
% 0.92/1.13  fof(c_0_32, plain, ![X18, X19, X20, X21, X22]:k3_enumset1(X18,X19,X20,X21,X22)=k2_xboole_0(k1_tarski(X18),k2_enumset1(X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.92/1.13  cnf(c_0_33, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.92/1.13  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.92/1.13  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.92/1.13  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.92/1.13  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.92/1.13  cnf(c_0_38, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.92/1.13  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.92/1.13  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.92/1.13  cnf(c_0_41, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.92/1.13  cnf(c_0_42, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.13  cnf(c_0_43, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.92/1.13  cnf(c_0_44, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.92/1.13  cnf(c_0_45, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.92/1.13  cnf(c_0_46, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.92/1.13  cnf(c_0_47, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 0.92/1.13  cnf(c_0_48, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.92/1.13  cnf(c_0_49, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_34]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.92/1.13  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.92/1.13  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_42]), c_0_42]), c_0_34]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.92/1.13  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.92/1.13  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_34]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 0.92/1.13  cnf(c_0_54, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X3,X2,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_47])).
% 0.92/1.13  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k6_enumset1(X3,X3,X3,X3,X2,X1,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_49])).
% 0.92/1.13  cnf(c_0_56, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 0.92/1.13  cnf(c_0_57, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X7),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))))=k6_enumset1(X1,X1,X2,X3,X4,X5,X7,X6)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.92/1.13  cnf(c_0_58, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X3,X3,X3,X3,X3,X1,X2,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_52]), c_0_47])).
% 0.92/1.13  cnf(c_0_59, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2),k1_tarski(X1))))), inference(spm,[status(thm)],[c_0_53, c_0_50])).
% 0.92/1.13  cnf(c_0_60, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k6_enumset1(X2,X2,X2,X2,X2,X3,X1,X4)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.92/1.13  cnf(c_0_61, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk3_0,esk1_0)!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.92/1.13  cnf(c_0_62, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X3,X3,X2,X4)), inference(spm,[status(thm)],[c_0_58, c_0_55])).
% 0.92/1.13  cnf(c_0_63, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X4,X4,X3,X2)), inference(spm,[status(thm)],[c_0_53, c_0_59])).
% 0.92/1.13  cnf(c_0_64, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X7,X7,X7,X6),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X7,X7,X7,X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))))=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(spm,[status(thm)],[c_0_57, c_0_60])).
% 0.92/1.13  cnf(c_0_65, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X3),k1_tarski(X1))))), inference(spm,[status(thm)],[c_0_53, c_0_48])).
% 0.92/1.13  cnf(c_0_66, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X3),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X1,X4,X5),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X1,X4,X5),k1_tarski(X3))))), inference(spm,[status(thm)],[c_0_53, c_0_55])).
% 0.92/1.13  cnf(c_0_67, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk1_0)!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_54])).
% 0.92/1.13  cnf(c_0_68, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X7,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_63]), c_0_64])).
% 0.92/1.13  cnf(c_0_69, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X1,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2)), inference(spm,[status(thm)],[c_0_48, c_0_58])).
% 0.92/1.13  cnf(c_0_70, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k6_enumset1(X2,X2,X2,X2,X2,X1,X4,X3)), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 0.92/1.13  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70])]), ['proof']).
% 0.92/1.13  # SZS output end CNFRefutation
% 0.92/1.13  # Proof object total steps             : 72
% 0.92/1.13  # Proof object clause steps            : 41
% 0.92/1.13  # Proof object formula steps           : 31
% 0.92/1.13  # Proof object conjectures             : 9
% 0.92/1.13  # Proof object clause conjectures      : 6
% 0.92/1.13  # Proof object formula conjectures     : 3
% 0.92/1.13  # Proof object initial clauses used    : 15
% 0.92/1.13  # Proof object initial formulas used   : 15
% 0.92/1.13  # Proof object generating inferences   : 13
% 0.92/1.13  # Proof object simplifying inferences  : 115
% 0.92/1.13  # Training examples: 0 positive, 0 negative
% 0.92/1.13  # Parsed axioms                        : 15
% 0.92/1.13  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.13  # Initial clauses                      : 15
% 0.92/1.13  # Removed in clause preprocessing      : 8
% 0.92/1.13  # Initial clauses in saturation        : 7
% 0.92/1.13  # Processed clauses                    : 3427
% 0.92/1.13  # ...of these trivial                  : 133
% 0.92/1.13  # ...subsumed                          : 2943
% 0.92/1.13  # ...remaining for further processing  : 351
% 0.92/1.13  # Other redundant clauses eliminated   : 0
% 0.92/1.13  # Clauses deleted for lack of memory   : 0
% 0.92/1.13  # Backward-subsumed                    : 21
% 0.92/1.13  # Backward-rewritten                   : 15
% 0.92/1.13  # Generated clauses                    : 205210
% 0.92/1.13  # ...of the previous two non-trivial   : 184781
% 0.92/1.13  # Contextual simplify-reflections      : 0
% 0.92/1.13  # Paramodulations                      : 205210
% 0.92/1.13  # Factorizations                       : 0
% 0.92/1.13  # Equation resolutions                 : 0
% 0.92/1.13  # Propositional unsat checks           : 0
% 0.92/1.13  #    Propositional check models        : 0
% 0.92/1.13  #    Propositional check unsatisfiable : 0
% 0.92/1.13  #    Propositional clauses             : 0
% 0.92/1.13  #    Propositional clauses after purity: 0
% 0.92/1.13  #    Propositional unsat core size     : 0
% 0.92/1.13  #    Propositional preprocessing time  : 0.000
% 0.92/1.13  #    Propositional encoding time       : 0.000
% 0.92/1.13  #    Propositional solver time         : 0.000
% 0.92/1.13  #    Success case prop preproc time    : 0.000
% 0.92/1.13  #    Success case prop encoding time   : 0.000
% 0.92/1.13  #    Success case prop solver time     : 0.000
% 0.92/1.13  # Current number of processed clauses  : 308
% 0.92/1.13  #    Positive orientable unit clauses  : 32
% 0.92/1.13  #    Positive unorientable unit clauses: 276
% 0.92/1.13  #    Negative unit clauses             : 0
% 0.92/1.13  #    Non-unit-clauses                  : 0
% 0.92/1.13  # Current number of unprocessed clauses: 179044
% 0.92/1.13  # ...number of literals in the above   : 179044
% 0.92/1.13  # Current number of archived formulas  : 0
% 0.92/1.13  # Current number of archived clauses   : 51
% 0.92/1.13  # Clause-clause subsumption calls (NU) : 0
% 0.92/1.14  # Rec. Clause-clause subsumption calls : 0
% 0.92/1.14  # Non-unit clause-clause subsumptions  : 0
% 0.92/1.14  # Unit Clause-clause subsumption calls : 47184
% 0.92/1.14  # Rewrite failures with RHS unbound    : 0
% 0.92/1.14  # BW rewrite match attempts            : 70763
% 0.92/1.14  # BW rewrite match successes           : 17755
% 0.92/1.14  # Condensation attempts                : 0
% 0.92/1.14  # Condensation successes               : 0
% 0.92/1.14  # Termbank termtop insertions          : 726787
% 0.92/1.14  
% 0.92/1.14  # -------------------------------------------------
% 0.92/1.14  # User time                : 0.743 s
% 0.92/1.14  # System time              : 0.045 s
% 0.92/1.14  # Total time               : 0.788 s
% 0.92/1.14  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
