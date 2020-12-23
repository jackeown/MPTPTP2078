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
% DateTime   : Thu Dec  3 10:36:53 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   82 (1654 expanded)
%              Number of clauses        :   43 ( 607 expanded)
%              Number of leaves         :   19 ( 523 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 (1654 expanded)
%              Number of equality atoms :   81 (1653 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t54_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(t132_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(t129_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

fof(t113_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(c_0_19,plain,(
    ! [X17,X18] : k2_xboole_0(X17,X18) = k5_xboole_0(X17,k4_xboole_0(X18,X17)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_22,plain,(
    ! [X15,X16] : k2_xboole_0(X15,X16) = k5_xboole_0(k5_xboole_0(X15,X16),k3_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_26,plain,(
    ! [X67,X68] : k1_enumset1(X67,X67,X68) = k2_tarski(X67,X68) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X69,X70,X71] : k2_enumset1(X69,X69,X70,X71) = k1_enumset1(X69,X70,X71) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X72,X73,X74,X75] : k3_enumset1(X72,X72,X73,X74,X75) = k2_enumset1(X72,X73,X74,X75) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X76,X77,X78,X79,X80] : k4_enumset1(X76,X76,X77,X78,X79,X80) = k3_enumset1(X76,X77,X78,X79,X80) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X81,X82,X83,X84,X85,X86] : k5_enumset1(X81,X81,X82,X83,X84,X85,X86) = k4_enumset1(X81,X82,X83,X84,X85,X86) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_33,plain,(
    ! [X12,X13,X14] : k5_xboole_0(k5_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X27,X28,X29,X30] : k2_enumset1(X27,X28,X29,X30) = k2_enumset1(X30,X29,X28,X27) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_43,plain,(
    ! [X49,X50,X51,X52,X53] : k3_enumset1(X49,X50,X51,X52,X53) = k2_xboole_0(k2_enumset1(X49,X50,X51,X52),k1_tarski(X53)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_44,plain,(
    ! [X66] : k2_tarski(X66,X66) = k1_tarski(X66) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_45,plain,(
    ! [X60,X61,X62,X63,X64,X65] : k4_enumset1(X60,X61,X62,X63,X64,X65) = k2_xboole_0(k2_enumset1(X60,X61,X62,X63),k2_tarski(X64,X65)) ),
    inference(variable_rename,[status(thm)],[t54_enumset1])).

fof(c_0_46,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46,X47,X48] : k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) = k2_xboole_0(k4_enumset1(X40,X41,X42,X43,X44,X45),k1_enumset1(X46,X47,X48)) ),
    inference(variable_rename,[status(thm)],[t132_enumset1])).

fof(c_0_47,plain,(
    ! [X54,X55,X56,X57,X58,X59] : k4_enumset1(X54,X55,X56,X57,X58,X59) = k2_xboole_0(k1_tarski(X54),k3_enumset1(X55,X56,X57,X58,X59)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_48,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37,X38,X39] : k7_enumset1(X31,X32,X33,X34,X35,X36,X37,X38,X39) = k2_xboole_0(k1_enumset1(X31,X32,X33),k4_enumset1(X34,X35,X36,X37,X38,X39)) ),
    inference(variable_rename,[status(thm)],[t129_enumset1])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_32]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_58,plain,(
    ! [X23,X24,X25,X26] : k2_enumset1(X23,X24,X25,X26) = k2_enumset1(X24,X26,X25,X23) ),
    inference(variable_rename,[status(thm)],[t113_enumset1])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0)))) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_61,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X5),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_35]),c_0_32]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_62,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_35]),c_0_32]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_63,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X4,X5,X6)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_32]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_64,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_53]),c_0_35]),c_0_32]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_65,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X5,X6,X7,X8,X9),k3_xboole_0(k5_enumset1(X4,X4,X5,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_32]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_66,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_67,plain,(
    ! [X19,X20,X21,X22] : k2_enumset1(X19,X20,X21,X22) = k2_enumset1(X19,X22,X21,X20) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0)))) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_60]),c_0_60]),c_0_60])).

cnf(c_0_69,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X5) = k5_enumset1(X1,X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( k7_enumset1(X1,X1,X1,X2,X3,X4,X5,X5,X6) = k5_enumset1(X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( k7_enumset1(X1,X1,X1,X2,X2,X3,X4,X5,X6) = k5_enumset1(X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X2,X2,X2,X2,X4,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_73,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)))) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_69]),c_0_69]),c_0_69]),c_0_69]),c_0_69]),c_0_69]),c_0_69])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X8,X9)))) = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(spm,[status(thm)],[c_0_50,c_0_63])).

cnf(c_0_76,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X4,X5) = k5_enumset1(X1,X1,X2,X2,X3,X4,X5) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X1,X1,X1,X1,X3,X4,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_72])).

cnf(c_0_78,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X1,X1,X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_79,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_71]),c_0_76]),c_0_77])).

cnf(c_0_80,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X1,X1,X1,X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_78,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.027 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.39  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 0.13/0.39  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.39  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.13/0.39  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 0.13/0.39  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t54_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 0.13/0.39  fof(t132_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_enumset1)).
% 0.13/0.39  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 0.13/0.39  fof(t129_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_enumset1)).
% 0.13/0.39  fof(t113_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 0.13/0.39  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 0.13/0.39  fof(c_0_19, plain, ![X17, X18]:k2_xboole_0(X17,X18)=k5_xboole_0(X17,k4_xboole_0(X18,X17)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.39  fof(c_0_20, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.39  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.13/0.39  fof(c_0_22, plain, ![X15, X16]:k2_xboole_0(X15,X16)=k5_xboole_0(k5_xboole_0(X15,X16),k3_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.13/0.39  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  fof(c_0_25, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.13/0.39  fof(c_0_26, plain, ![X67, X68]:k1_enumset1(X67,X67,X68)=k2_tarski(X67,X68), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_27, plain, ![X69, X70, X71]:k2_enumset1(X69,X69,X70,X71)=k1_enumset1(X69,X70,X71), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_28, plain, ![X72, X73, X74, X75]:k3_enumset1(X72,X72,X73,X74,X75)=k2_enumset1(X72,X73,X74,X75), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.39  fof(c_0_29, plain, ![X76, X77, X78, X79, X80]:k4_enumset1(X76,X76,X77,X78,X79,X80)=k3_enumset1(X76,X77,X78,X79,X80), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.39  fof(c_0_30, plain, ![X81, X82, X83, X84, X85, X86]:k5_enumset1(X81,X81,X82,X83,X84,X85,X86)=k4_enumset1(X81,X82,X83,X84,X85,X86), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.39  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.39  fof(c_0_33, plain, ![X12, X13, X14]:k5_xboole_0(k5_xboole_0(X12,X13),X14)=k5_xboole_0(X12,k5_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_38, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_39, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.39  cnf(c_0_41, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.39  fof(c_0_42, plain, ![X27, X28, X29, X30]:k2_enumset1(X27,X28,X29,X30)=k2_enumset1(X30,X29,X28,X27), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.13/0.39  fof(c_0_43, plain, ![X49, X50, X51, X52, X53]:k3_enumset1(X49,X50,X51,X52,X53)=k2_xboole_0(k2_enumset1(X49,X50,X51,X52),k1_tarski(X53)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.13/0.39  fof(c_0_44, plain, ![X66]:k2_tarski(X66,X66)=k1_tarski(X66), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_45, plain, ![X60, X61, X62, X63, X64, X65]:k4_enumset1(X60,X61,X62,X63,X64,X65)=k2_xboole_0(k2_enumset1(X60,X61,X62,X63),k2_tarski(X64,X65)), inference(variable_rename,[status(thm)],[t54_enumset1])).
% 0.13/0.39  fof(c_0_46, plain, ![X40, X41, X42, X43, X44, X45, X46, X47, X48]:k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)=k2_xboole_0(k4_enumset1(X40,X41,X42,X43,X44,X45),k1_enumset1(X46,X47,X48)), inference(variable_rename,[status(thm)],[t132_enumset1])).
% 0.13/0.39  fof(c_0_47, plain, ![X54, X55, X56, X57, X58, X59]:k4_enumset1(X54,X55,X56,X57,X58,X59)=k2_xboole_0(k1_tarski(X54),k3_enumset1(X55,X56,X57,X58,X59)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.13/0.39  fof(c_0_48, plain, ![X31, X32, X33, X34, X35, X36, X37, X38, X39]:k7_enumset1(X31,X32,X33,X34,X35,X36,X37,X38,X39)=k2_xboole_0(k1_enumset1(X31,X32,X33),k4_enumset1(X34,X35,X36,X37,X38,X39)), inference(variable_rename,[status(thm)],[t129_enumset1])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_35]), c_0_32]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.13/0.39  cnf(c_0_50, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.39  cnf(c_0_51, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.39  cnf(c_0_52, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_53, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_54, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.39  cnf(c_0_55, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_56, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.39  cnf(c_0_57, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.39  fof(c_0_58, plain, ![X23, X24, X25, X26]:k2_enumset1(X23,X24,X25,X26)=k2_enumset1(X24,X26,X25,X23), inference(variable_rename,[status(thm)],[t113_enumset1])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0))))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.39  cnf(c_0_60, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.13/0.39  cnf(c_0_61, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X5),k5_enumset1(X1,X1,X1,X1,X2,X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_35]), c_0_32]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.13/0.39  cnf(c_0_62, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X1,X1,X1,X1,X2,X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_35]), c_0_32]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.13/0.39  cnf(c_0_63, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X4,X5,X6))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_32]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.13/0.39  cnf(c_0_64, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_53]), c_0_35]), c_0_32]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.13/0.39  cnf(c_0_65, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X5,X6,X7,X8,X9),k3_xboole_0(k5_enumset1(X4,X4,X5,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_32]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.13/0.39  cnf(c_0_66, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.39  fof(c_0_67, plain, ![X19, X20, X21, X22]:k2_enumset1(X19,X20,X21,X22)=k2_enumset1(X19,X22,X21,X20), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk3_0,esk3_0))))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_60]), c_0_60]), c_0_60])).
% 0.13/0.39  cnf(c_0_69, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X5)=k5_enumset1(X1,X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.13/0.39  cnf(c_0_70, plain, (k7_enumset1(X1,X1,X1,X2,X3,X4,X5,X5,X6)=k5_enumset1(X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.39  cnf(c_0_71, plain, (k7_enumset1(X1,X1,X1,X2,X2,X3,X4,X5,X6)=k5_enumset1(X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.39  cnf(c_0_72, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X2,X2,X2,X2,X4,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.13/0.39  cnf(c_0_73, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_69]), c_0_69]), c_0_69]), c_0_69]), c_0_69]), c_0_69]), c_0_69])).
% 0.13/0.39  cnf(c_0_75, plain, (k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k3_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X8,X9))))=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)), inference(spm,[status(thm)],[c_0_50, c_0_63])).
% 0.13/0.39  cnf(c_0_76, plain, (k5_enumset1(X1,X1,X2,X3,X4,X4,X5)=k5_enumset1(X1,X1,X2,X2,X3,X4,X5)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.13/0.39  cnf(c_0_77, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X1,X1,X1,X1,X3,X4,X2)), inference(spm,[status(thm)],[c_0_60, c_0_72])).
% 0.13/0.39  cnf(c_0_78, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X1,X1,X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_71]), c_0_76]), c_0_77])).
% 0.13/0.39  cnf(c_0_80, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X1,X1,X1,X1,X2,X4,X3)), inference(spm,[status(thm)],[c_0_78, c_0_77])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 82
% 0.13/0.39  # Proof object clause steps            : 43
% 0.13/0.39  # Proof object formula steps           : 39
% 0.13/0.39  # Proof object conjectures             : 10
% 0.13/0.39  # Proof object clause conjectures      : 7
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 19
% 0.13/0.39  # Proof object initial formulas used   : 19
% 0.13/0.39  # Proof object generating inferences   : 4
% 0.13/0.39  # Proof object simplifying inferences  : 140
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 19
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 19
% 0.13/0.39  # Removed in clause preprocessing      : 8
% 0.13/0.39  # Initial clauses in saturation        : 11
% 0.13/0.39  # Processed clauses                    : 90
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 35
% 0.13/0.39  # ...remaining for further processing  : 53
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 7
% 0.13/0.39  # Generated clauses                    : 1479
% 0.13/0.39  # ...of the previous two non-trivial   : 1358
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 1479
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 35
% 0.13/0.39  #    Positive orientable unit clauses  : 9
% 0.13/0.39  #    Positive unorientable unit clauses: 26
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 0
% 0.13/0.39  # Current number of unprocessed clauses: 1290
% 0.13/0.39  # ...number of literals in the above   : 1290
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 26
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 271
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 834
% 0.13/0.39  # BW rewrite match successes           : 365
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 10340
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.043 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.048 s
% 0.13/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
