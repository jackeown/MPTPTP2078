%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:52 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :   72 (1655 expanded)
%              Number of clauses        :   41 ( 608 expanded)
%              Number of leaves         :   15 ( 523 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 (1655 expanded)
%              Number of equality atoms :   71 (1654 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

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
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_18,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k4_enumset1(X24,X25,X26,X27,X28,X29) = k2_xboole_0(k3_enumset1(X24,X25,X26,X27,X28),k1_tarski(X29)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X47,X48,X49,X50,X51] : k4_enumset1(X47,X47,X48,X49,X50,X51) = k3_enumset1(X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X52,X53,X54,X55,X56,X57] : k5_enumset1(X52,X52,X53,X54,X55,X56,X57) = k4_enumset1(X52,X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X58,X59,X60,X61,X62,X63,X64] : k6_enumset1(X58,X58,X59,X60,X61,X62,X63,X64) = k5_enumset1(X58,X59,X60,X61,X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_24,plain,(
    ! [X65,X66,X67] : k1_enumset1(X65,X66,X67) = k1_enumset1(X65,X67,X66) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

fof(c_0_25,plain,(
    ! [X40,X41,X42] : k2_enumset1(X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X43,X44,X45,X46] : k3_enumset1(X43,X43,X44,X45,X46) = k2_enumset1(X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] : k6_enumset1(X30,X31,X32,X33,X34,X35,X36,X37) = k2_xboole_0(k4_enumset1(X30,X31,X32,X33,X34,X35),k2_tarski(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

fof(c_0_28,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X16,X17,X18] : k1_enumset1(X16,X17,X18) = k1_enumset1(X18,X17,X16) ),
    inference(variable_rename,[status(thm)],[t102_enumset1])).

fof(c_0_30,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_31,plain,(
    ! [X13,X14,X15] : k1_enumset1(X13,X14,X15) = k1_enumset1(X14,X15,X13) ),
    inference(variable_rename,[status(thm)],[t100_enumset1])).

fof(c_0_32,plain,(
    ! [X19,X20,X21,X22,X23] : k3_enumset1(X19,X20,X21,X22,X23) = k2_xboole_0(k1_tarski(X19),k2_enumset1(X20,X21,X22,X23)) ),
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
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
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
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_34]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

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
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X8),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X8),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X8,X7) ),
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
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X8,X8,X8,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X8,X8,X8,X7),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
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
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X8,X7) ),
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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:19:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.93/1.17  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.93/1.17  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.93/1.17  #
% 0.93/1.17  # Preprocessing time       : 0.026 s
% 0.93/1.17  # Presaturation interreduction done
% 0.93/1.17  
% 0.93/1.17  # Proof found!
% 0.93/1.17  # SZS status Theorem
% 0.93/1.17  # SZS output start CNFRefutation
% 0.93/1.17  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.93/1.17  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.93/1.17  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 0.93/1.17  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.93/1.17  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.93/1.17  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.93/1.17  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.93/1.17  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 0.93/1.17  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.93/1.17  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.93/1.17  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 0.93/1.17  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.93/1.17  fof(t102_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 0.93/1.17  fof(t100_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 0.93/1.17  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.93/1.17  fof(c_0_15, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(X11,k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.93/1.17  fof(c_0_16, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.93/1.17  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.93/1.17  fof(c_0_18, plain, ![X24, X25, X26, X27, X28, X29]:k4_enumset1(X24,X25,X26,X27,X28,X29)=k2_xboole_0(k3_enumset1(X24,X25,X26,X27,X28),k1_tarski(X29)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.93/1.17  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.93/1.17  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.93/1.17  fof(c_0_21, plain, ![X47, X48, X49, X50, X51]:k4_enumset1(X47,X47,X48,X49,X50,X51)=k3_enumset1(X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.93/1.17  fof(c_0_22, plain, ![X52, X53, X54, X55, X56, X57]:k5_enumset1(X52,X52,X53,X54,X55,X56,X57)=k4_enumset1(X52,X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.93/1.17  fof(c_0_23, plain, ![X58, X59, X60, X61, X62, X63, X64]:k6_enumset1(X58,X58,X59,X60,X61,X62,X63,X64)=k5_enumset1(X58,X59,X60,X61,X62,X63,X64), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.93/1.17  fof(c_0_24, plain, ![X65, X66, X67]:k1_enumset1(X65,X66,X67)=k1_enumset1(X65,X67,X66), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 0.93/1.17  fof(c_0_25, plain, ![X40, X41, X42]:k2_enumset1(X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.93/1.17  fof(c_0_26, plain, ![X43, X44, X45, X46]:k3_enumset1(X43,X43,X44,X45,X46)=k2_enumset1(X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.93/1.17  fof(c_0_27, plain, ![X30, X31, X32, X33, X34, X35, X36, X37]:k6_enumset1(X30,X31,X32,X33,X34,X35,X36,X37)=k2_xboole_0(k4_enumset1(X30,X31,X32,X33,X34,X35),k2_tarski(X36,X37)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 0.93/1.17  fof(c_0_28, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.93/1.17  fof(c_0_29, plain, ![X16, X17, X18]:k1_enumset1(X16,X17,X18)=k1_enumset1(X18,X17,X16), inference(variable_rename,[status(thm)],[t102_enumset1])).
% 0.93/1.17  fof(c_0_30, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.93/1.17  fof(c_0_31, plain, ![X13, X14, X15]:k1_enumset1(X13,X14,X15)=k1_enumset1(X14,X15,X13), inference(variable_rename,[status(thm)],[t100_enumset1])).
% 0.93/1.17  fof(c_0_32, plain, ![X19, X20, X21, X22, X23]:k3_enumset1(X19,X20,X21,X22,X23)=k2_xboole_0(k1_tarski(X19),k2_enumset1(X20,X21,X22,X23)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.93/1.17  cnf(c_0_33, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.93/1.17  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.93/1.17  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.93/1.17  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.93/1.17  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.93/1.17  cnf(c_0_38, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.93/1.17  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.93/1.17  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.93/1.17  cnf(c_0_41, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.93/1.17  cnf(c_0_42, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.93/1.17  cnf(c_0_43, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.93/1.17  cnf(c_0_44, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.93/1.17  cnf(c_0_45, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.93/1.17  cnf(c_0_46, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.93/1.17  cnf(c_0_47, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 0.93/1.17  cnf(c_0_48, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.93/1.17  cnf(c_0_49, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_34]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.93/1.17  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.93/1.17  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_42]), c_0_42]), c_0_34]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.93/1.17  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.93/1.17  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_34]), c_0_40]), c_0_40]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 0.93/1.17  cnf(c_0_54, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X3,X2,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_47])).
% 0.93/1.17  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k6_enumset1(X3,X3,X3,X3,X2,X1,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_49])).
% 0.93/1.17  cnf(c_0_56, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 0.93/1.17  cnf(c_0_57, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X8),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X8,X8),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X8,X7)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.93/1.17  cnf(c_0_58, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X3,X3,X3,X3,X3,X1,X2,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_52]), c_0_47])).
% 0.93/1.17  cnf(c_0_59, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2),k1_tarski(X1))))), inference(spm,[status(thm)],[c_0_53, c_0_50])).
% 0.93/1.17  cnf(c_0_60, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k6_enumset1(X2,X2,X2,X2,X2,X3,X1,X4)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.93/1.17  cnf(c_0_61, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk3_0,esk1_0)!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.93/1.17  cnf(c_0_62, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X3,X3,X2,X4)), inference(spm,[status(thm)],[c_0_58, c_0_55])).
% 0.93/1.17  cnf(c_0_63, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X4,X4,X3,X2)), inference(spm,[status(thm)],[c_0_53, c_0_59])).
% 0.93/1.17  cnf(c_0_64, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X8,X8,X8,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X8,X8,X8,X7),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_57, c_0_60])).
% 0.93/1.17  cnf(c_0_65, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X3),k1_tarski(X1))))), inference(spm,[status(thm)],[c_0_53, c_0_48])).
% 0.93/1.17  cnf(c_0_66, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X3),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X1,X4,X5),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X1,X4,X5),k1_tarski(X3))))), inference(spm,[status(thm)],[c_0_53, c_0_55])).
% 0.93/1.17  cnf(c_0_67, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk1_0)!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_54])).
% 0.93/1.17  cnf(c_0_68, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X8,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_63]), c_0_64])).
% 0.93/1.17  cnf(c_0_69, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X1,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2)), inference(spm,[status(thm)],[c_0_48, c_0_58])).
% 0.93/1.17  cnf(c_0_70, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k6_enumset1(X2,X2,X2,X2,X2,X1,X4,X3)), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 0.93/1.17  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70])]), ['proof']).
% 0.93/1.17  # SZS output end CNFRefutation
% 0.93/1.17  # Proof object total steps             : 72
% 0.93/1.17  # Proof object clause steps            : 41
% 0.93/1.17  # Proof object formula steps           : 31
% 0.93/1.17  # Proof object conjectures             : 9
% 0.93/1.17  # Proof object clause conjectures      : 6
% 0.93/1.17  # Proof object formula conjectures     : 3
% 0.93/1.17  # Proof object initial clauses used    : 15
% 0.93/1.17  # Proof object initial formulas used   : 15
% 0.93/1.17  # Proof object generating inferences   : 13
% 0.93/1.17  # Proof object simplifying inferences  : 112
% 0.93/1.17  # Training examples: 0 positive, 0 negative
% 0.93/1.17  # Parsed axioms                        : 15
% 0.93/1.17  # Removed by relevancy pruning/SinE    : 0
% 0.93/1.17  # Initial clauses                      : 15
% 0.93/1.17  # Removed in clause preprocessing      : 8
% 0.93/1.17  # Initial clauses in saturation        : 7
% 0.93/1.17  # Processed clauses                    : 3416
% 0.93/1.17  # ...of these trivial                  : 122
% 0.93/1.17  # ...subsumed                          : 2940
% 0.93/1.17  # ...remaining for further processing  : 354
% 0.93/1.17  # Other redundant clauses eliminated   : 0
% 0.93/1.17  # Clauses deleted for lack of memory   : 0
% 0.93/1.17  # Backward-subsumed                    : 22
% 0.93/1.17  # Backward-rewritten                   : 15
% 0.93/1.17  # Generated clauses                    : 207563
% 0.93/1.17  # ...of the previous two non-trivial   : 189285
% 0.93/1.17  # Contextual simplify-reflections      : 0
% 0.93/1.17  # Paramodulations                      : 207563
% 0.93/1.17  # Factorizations                       : 0
% 0.93/1.17  # Equation resolutions                 : 0
% 0.93/1.17  # Propositional unsat checks           : 0
% 0.93/1.17  #    Propositional check models        : 0
% 0.93/1.17  #    Propositional check unsatisfiable : 0
% 0.93/1.17  #    Propositional clauses             : 0
% 0.93/1.17  #    Propositional clauses after purity: 0
% 0.93/1.17  #    Propositional unsat core size     : 0
% 0.93/1.17  #    Propositional preprocessing time  : 0.000
% 0.93/1.17  #    Propositional encoding time       : 0.000
% 0.93/1.17  #    Propositional solver time         : 0.000
% 0.93/1.17  #    Success case prop preproc time    : 0.000
% 0.93/1.17  #    Success case prop encoding time   : 0.000
% 0.93/1.17  #    Success case prop solver time     : 0.000
% 0.93/1.17  # Current number of processed clauses  : 310
% 0.93/1.17  #    Positive orientable unit clauses  : 29
% 0.93/1.17  #    Positive unorientable unit clauses: 281
% 0.93/1.17  #    Negative unit clauses             : 0
% 0.93/1.17  #    Non-unit-clauses                  : 0
% 0.93/1.17  # Current number of unprocessed clauses: 183525
% 0.93/1.17  # ...number of literals in the above   : 183525
% 0.93/1.17  # Current number of archived formulas  : 0
% 0.93/1.17  # Current number of archived clauses   : 52
% 0.93/1.17  # Clause-clause subsumption calls (NU) : 0
% 0.93/1.17  # Rec. Clause-clause subsumption calls : 0
% 0.93/1.17  # Non-unit clause-clause subsumptions  : 0
% 0.93/1.17  # Unit Clause-clause subsumption calls : 48189
% 0.93/1.17  # Rewrite failures with RHS unbound    : 0
% 0.93/1.17  # BW rewrite match attempts            : 75441
% 0.93/1.17  # BW rewrite match successes           : 19453
% 0.93/1.17  # Condensation attempts                : 0
% 0.93/1.17  # Condensation successes               : 0
% 0.93/1.17  # Termbank termtop insertions          : 714054
% 0.93/1.17  
% 0.93/1.17  # -------------------------------------------------
% 0.93/1.17  # User time                : 0.760 s
% 0.93/1.17  # System time              : 0.071 s
% 0.93/1.17  # Total time               : 0.831 s
% 0.93/1.17  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
