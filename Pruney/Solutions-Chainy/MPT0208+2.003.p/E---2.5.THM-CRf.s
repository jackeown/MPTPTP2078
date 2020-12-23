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
% DateTime   : Thu Dec  3 10:36:41 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :  113 (9515 expanded)
%              Number of clauses        :   72 (3644 expanded)
%              Number of leaves         :   20 (2935 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 (9515 expanded)
%              Number of equality atoms :  112 (9514 expanded)
%              Maximal formula depth    :   11 (   3 average)
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

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t58_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(t127_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(t134_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(t133_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(c_0_20,plain,(
    ! [X44,X45,X46,X47] : k2_enumset1(X44,X45,X46,X47) = k2_xboole_0(k1_tarski(X44),k1_enumset1(X45,X46,X47)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_21,plain,(
    ! [X99] : k2_tarski(X99,X99) = k1_tarski(X99) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X100,X101] : k1_enumset1(X100,X100,X101) = k2_tarski(X100,X101) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k5_xboole_0(X12,k4_xboole_0(X13,X12)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_24,plain,(
    ! [X102,X103,X104] : k2_enumset1(X102,X102,X103,X104) = k1_enumset1(X102,X103,X104) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X53,X54,X55,X56,X57,X58,X59] : k5_enumset1(X53,X54,X55,X56,X57,X58,X59) = k2_xboole_0(k1_enumset1(X53,X54,X55),k2_enumset1(X56,X57,X58,X59)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

fof(c_0_26,plain,(
    ! [X111,X112,X113,X114,X115,X116,X117] : k6_enumset1(X111,X111,X112,X113,X114,X115,X116,X117) = k5_enumset1(X111,X112,X113,X114,X115,X116,X117) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_27,plain,(
    ! [X60,X61,X62,X63,X64,X65,X66] : k5_enumset1(X60,X61,X62,X63,X64,X65,X66) = k2_xboole_0(k4_enumset1(X60,X61,X62,X63,X64,X65),k1_tarski(X66)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

fof(c_0_28,plain,(
    ! [X105,X106,X107,X108,X109,X110] : k5_enumset1(X105,X105,X106,X107,X108,X109,X110) = k4_enumset1(X105,X106,X107,X108,X109,X110) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X83,X84,X85,X86,X87,X88,X89,X90] : k6_enumset1(X83,X84,X85,X86,X87,X88,X89,X90) = k2_xboole_0(k4_enumset1(X83,X84,X85,X86,X87,X88),k2_tarski(X89,X90)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X1,X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_33]),c_0_34]),c_0_34]),c_0_36])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k2_enumset1(X7,X7,X7,X7),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_38]),c_0_38]),c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k2_enumset1(X7,X7,X7,X8),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_32]),c_0_33]),c_0_34]),c_0_38]),c_0_38]),c_0_36]),c_0_36])).

fof(c_0_44,plain,(
    ! [X48,X49,X50,X51,X52] : k3_enumset1(X48,X49,X50,X51,X52) = k2_xboole_0(k1_tarski(X48),k2_enumset1(X49,X50,X51,X52)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_45,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30,X31] : k7_enumset1(X23,X24,X25,X26,X27,X28,X29,X30,X31) = k2_xboole_0(k1_tarski(X23),k6_enumset1(X24,X25,X26,X27,X28,X29,X30,X31)) ),
    inference(variable_rename,[status(thm)],[t127_enumset1])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_48,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(assume_negation,[status(cth)],[t134_enumset1])).

fof(c_0_49,plain,(
    ! [X41,X42,X43] : k1_enumset1(X41,X42,X43) = k2_xboole_0(k1_tarski(X41),k2_tarski(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_50,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21,X22] : k7_enumset1(X14,X15,X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k3_enumset1(X18,X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X1,X2,X2,X3,X4,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_54,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_55,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).

cnf(c_0_56,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_59,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X1,X2,X2,X3,X4,X4,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_47,c_0_53])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_62,plain,(
    ! [X75,X76,X77,X78,X79,X80,X81,X82] : k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82) = k2_xboole_0(k2_tarski(X75,X76),k4_enumset1(X77,X78,X79,X80,X81,X82)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

fof(c_0_63,plain,(
    ! [X91,X92,X93,X94,X95,X96,X97,X98] : k6_enumset1(X91,X92,X93,X94,X95,X96,X97,X98) = k2_xboole_0(k5_enumset1(X91,X92,X93,X94,X95,X96,X97),k1_tarski(X98)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_64,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39,X40] : k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) = k2_xboole_0(k5_enumset1(X32,X33,X34,X35,X36,X37,X38),k2_tarski(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t133_enumset1])).

fof(c_0_65,plain,(
    ! [X67,X68,X69,X70,X71,X72,X73,X74] : k6_enumset1(X67,X68,X69,X70,X71,X72,X73,X74) = k2_xboole_0(k1_tarski(X67),k5_enumset1(X68,X69,X70,X71,X72,X73,X74)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

cnf(c_0_66,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k2_enumset1(X1,X1,X1,X1))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k2_enumset1(X5,X5,X5,X5),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k2_enumset1(X5,X5,X5,X5))),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_33]),c_0_58]),c_0_59])).

cnf(c_0_69,plain,
    ( k6_enumset1(X1,X2,X2,X3,X4,X4,X4,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_47,c_0_60])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_33]),c_0_33])).

cnf(c_0_71,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))) != k5_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k4_xboole_0(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_59])).

cnf(c_0_76,plain,
    ( k2_enumset1(X1,X2,X2,X3) = k2_enumset1(X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_67,c_0_40])).

cnf(c_0_77,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k2_enumset1(X1,X1,X1,X1))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_41])).

cnf(c_0_78,plain,
    ( k6_enumset1(X1,X1,X2,X3,X3,X3,X3,X3) = k2_enumset1(X1,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_69])).

cnf(c_0_79,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X1,X2,X3,X4))) = k6_enumset1(X5,X5,X6,X7,X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_70,c_0_41])).

cnf(c_0_80,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X8),k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_32]),c_0_33]),c_0_34]),c_0_34]),c_0_38]),c_0_36])).

cnf(c_0_81,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k2_enumset1(X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_36]),c_0_36])).

cnf(c_0_82,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k2_enumset1(X1,X1,X1,X1))) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k2_enumset1(X8,X8,X8,X9),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_32]),c_0_33]),c_0_34]),c_0_36]),c_0_36]),c_0_59])).

cnf(c_0_83,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_34]),c_0_36])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k4_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))) != k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_70])).

cnf(c_0_85,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X5,X6) = k6_enumset1(X1,X1,X2,X3,X4,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_76]),c_0_41])).

cnf(c_0_86,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_41]),c_0_46]),c_0_46]),c_0_79])).

cnf(c_0_87,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k6_enumset1(X3,X3,X4,X5,X6,X7,X8,X8),k2_enumset1(X1,X1,X1,X2))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_80,c_0_47])).

cnf(c_0_88,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X7,X8,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_80]),c_0_43])).

cnf(c_0_89,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X8),k2_enumset1(X1,X1,X1,X1))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X1) = k2_enumset1(X2,X3,X4,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_78]),c_0_41]),c_0_46]),c_0_60]),c_0_60]),c_0_79])).

cnf(c_0_91,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X8,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_83]),c_0_81])).

cnf(c_0_92,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X6,X7,X8),k2_enumset1(X1,X1,X1,X1))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_47]),c_0_43])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk9_0,esk1_0,esk2_0,esk3_0),k4_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk9_0,esk1_0,esk2_0,esk3_0))) != k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_84,c_0_77])).

cnf(c_0_94,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_46])).

cnf(c_0_95,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X2,X3,X4,X5,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_47]),c_0_43])).

cnf(c_0_96,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k6_enumset1(X3,X4,X5,X6,X7,X7,X8,X8),k2_enumset1(X1,X1,X1,X2))) = k6_enumset1(X1,X2,X8,X3,X4,X5,X6,X7) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_97,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_47]),c_0_89])).

cnf(c_0_98,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_46]),c_0_92])).

cnf(c_0_100,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X2,X3),k4_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8),k2_enumset1(X1,X2,X2,X3))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_83,c_0_77])).

cnf(c_0_101,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k2_enumset1(X3,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_90])).

cnf(c_0_102,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk9_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))) != k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_94]),c_0_77])).

cnf(c_0_103,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X4,X5,X6,X7,X8,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_95]),c_0_96])).

cnf(c_0_104,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X8,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_105,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k6_enumset1(X3,X3,X4,X4,X5,X6,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_46]),c_0_83]),c_0_79])).

cnf(c_0_106,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X2,X3),k4_xboole_0(k6_enumset1(X4,X4,X4,X5,X6,X6,X7,X8),k2_enumset1(X1,X2,X2,X3))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_100,c_0_95])).

cnf(c_0_107,plain,
    ( k2_enumset1(X1,X2,X2,X3) = k2_enumset1(X3,X3,X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_86]),c_0_53])).

cnf(c_0_108,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k2_enumset1(X7,X8,X8,X7),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X8,X7) ),
    inference(spm,[status(thm)],[c_0_43,c_0_101])).

cnf(c_0_109,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk7_0,esk8_0,esk4_0,esk5_0,esk6_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))) != k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_103]),c_0_104]),c_0_104]),c_0_104])).

cnf(c_0_110,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X6,X7,X8,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_105]),c_0_106])).

cnf(c_0_111,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X8,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_107]),c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110]),c_0_103]),c_0_110]),c_0_103]),c_0_104]),c_0_111])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:28:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 7.05/7.23  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 7.05/7.23  # and selection function SelectComplexExceptUniqMaxHorn.
% 7.05/7.23  #
% 7.05/7.23  # Preprocessing time       : 0.027 s
% 7.05/7.23  # Presaturation interreduction done
% 7.05/7.23  
% 7.05/7.23  # Proof found!
% 7.05/7.23  # SZS status Theorem
% 7.05/7.23  # SZS output start CNFRefutation
% 7.05/7.23  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 7.05/7.23  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.05/7.23  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.05/7.23  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.05/7.23  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.05/7.23  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 7.05/7.23  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 7.05/7.23  fof(t61_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 7.05/7.23  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 7.05/7.23  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 7.05/7.23  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 7.05/7.23  fof(t127_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_enumset1)).
% 7.05/7.23  fof(t134_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_enumset1)).
% 7.05/7.23  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 7.05/7.23  fof(l142_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l142_enumset1)).
% 7.05/7.23  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.05/7.23  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 7.05/7.23  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 7.05/7.23  fof(t133_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_enumset1)).
% 7.05/7.23  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 7.05/7.23  fof(c_0_20, plain, ![X44, X45, X46, X47]:k2_enumset1(X44,X45,X46,X47)=k2_xboole_0(k1_tarski(X44),k1_enumset1(X45,X46,X47)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 7.05/7.23  fof(c_0_21, plain, ![X99]:k2_tarski(X99,X99)=k1_tarski(X99), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 7.05/7.23  fof(c_0_22, plain, ![X100, X101]:k1_enumset1(X100,X100,X101)=k2_tarski(X100,X101), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 7.05/7.23  fof(c_0_23, plain, ![X12, X13]:k2_xboole_0(X12,X13)=k5_xboole_0(X12,k4_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 7.05/7.23  fof(c_0_24, plain, ![X102, X103, X104]:k2_enumset1(X102,X102,X103,X104)=k1_enumset1(X102,X103,X104), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 7.05/7.23  fof(c_0_25, plain, ![X53, X54, X55, X56, X57, X58, X59]:k5_enumset1(X53,X54,X55,X56,X57,X58,X59)=k2_xboole_0(k1_enumset1(X53,X54,X55),k2_enumset1(X56,X57,X58,X59)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 7.05/7.23  fof(c_0_26, plain, ![X111, X112, X113, X114, X115, X116, X117]:k6_enumset1(X111,X111,X112,X113,X114,X115,X116,X117)=k5_enumset1(X111,X112,X113,X114,X115,X116,X117), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 7.05/7.23  fof(c_0_27, plain, ![X60, X61, X62, X63, X64, X65, X66]:k5_enumset1(X60,X61,X62,X63,X64,X65,X66)=k2_xboole_0(k4_enumset1(X60,X61,X62,X63,X64,X65),k1_tarski(X66)), inference(variable_rename,[status(thm)],[t61_enumset1])).
% 7.05/7.23  fof(c_0_28, plain, ![X105, X106, X107, X108, X109, X110]:k5_enumset1(X105,X105,X106,X107,X108,X109,X110)=k4_enumset1(X105,X106,X107,X108,X109,X110), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 7.05/7.23  fof(c_0_29, plain, ![X83, X84, X85, X86, X87, X88, X89, X90]:k6_enumset1(X83,X84,X85,X86,X87,X88,X89,X90)=k2_xboole_0(k4_enumset1(X83,X84,X85,X86,X87,X88),k2_tarski(X89,X90)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 7.05/7.23  cnf(c_0_30, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 7.05/7.23  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.05/7.23  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 7.05/7.23  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.05/7.23  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 7.05/7.23  cnf(c_0_35, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 7.05/7.23  cnf(c_0_36, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 7.05/7.23  cnf(c_0_37, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.05/7.23  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.05/7.23  cnf(c_0_39, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 7.05/7.23  cnf(c_0_40, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_34]), c_0_34])).
% 7.05/7.23  cnf(c_0_41, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X1,X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_33]), c_0_34]), c_0_34]), c_0_36])).
% 7.05/7.23  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k2_enumset1(X7,X7,X7,X7),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_38]), c_0_38]), c_0_36]), c_0_36]), c_0_36])).
% 7.05/7.23  cnf(c_0_43, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k2_enumset1(X7,X7,X7,X8),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_32]), c_0_33]), c_0_34]), c_0_38]), c_0_38]), c_0_36]), c_0_36])).
% 7.05/7.23  fof(c_0_44, plain, ![X48, X49, X50, X51, X52]:k3_enumset1(X48,X49,X50,X51,X52)=k2_xboole_0(k1_tarski(X48),k2_enumset1(X49,X50,X51,X52)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 7.05/7.23  fof(c_0_45, plain, ![X23, X24, X25, X26, X27, X28, X29, X30, X31]:k7_enumset1(X23,X24,X25,X26,X27,X28,X29,X30,X31)=k2_xboole_0(k1_tarski(X23),k6_enumset1(X24,X25,X26,X27,X28,X29,X30,X31)), inference(variable_rename,[status(thm)],[t127_enumset1])).
% 7.05/7.23  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 7.05/7.23  cnf(c_0_47, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 7.05/7.23  fof(c_0_48, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(assume_negation,[status(cth)],[t134_enumset1])).
% 7.05/7.23  fof(c_0_49, plain, ![X41, X42, X43]:k1_enumset1(X41,X42,X43)=k2_xboole_0(k1_tarski(X41),k2_tarski(X42,X43)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 7.05/7.23  fof(c_0_50, plain, ![X14, X15, X16, X17, X18, X19, X20, X21, X22]:k7_enumset1(X14,X15,X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k3_enumset1(X18,X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[l142_enumset1])).
% 7.05/7.23  cnf(c_0_51, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 7.05/7.23  cnf(c_0_52, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 7.05/7.23  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X1,X2,X2,X3,X4,X4)=k2_enumset1(X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 7.05/7.23  fof(c_0_54, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k2_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 7.05/7.23  fof(c_0_55, negated_conjecture, k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).
% 7.05/7.23  cnf(c_0_56, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 7.05/7.23  cnf(c_0_57, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 7.05/7.23  cnf(c_0_58, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_34])).
% 7.05/7.23  cnf(c_0_59, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_34])).
% 7.05/7.23  cnf(c_0_60, plain, (k6_enumset1(X1,X1,X2,X2,X3,X4,X4,X4)=k2_enumset1(X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_47, c_0_53])).
% 7.05/7.23  cnf(c_0_61, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 7.05/7.23  fof(c_0_62, plain, ![X75, X76, X77, X78, X79, X80, X81, X82]:k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82)=k2_xboole_0(k2_tarski(X75,X76),k4_enumset1(X77,X78,X79,X80,X81,X82)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 7.05/7.23  fof(c_0_63, plain, ![X91, X92, X93, X94, X95, X96, X97, X98]:k6_enumset1(X91,X92,X93,X94,X95,X96,X97,X98)=k2_xboole_0(k5_enumset1(X91,X92,X93,X94,X95,X96,X97),k1_tarski(X98)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 7.05/7.23  fof(c_0_64, plain, ![X32, X33, X34, X35, X36, X37, X38, X39, X40]:k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)=k2_xboole_0(k5_enumset1(X32,X33,X34,X35,X36,X37,X38),k2_tarski(X39,X40)), inference(variable_rename,[status(thm)],[t133_enumset1])).
% 7.05/7.23  fof(c_0_65, plain, ![X67, X68, X69, X70, X71, X72, X73, X74]:k6_enumset1(X67,X68,X69,X70,X71,X72,X73,X74)=k2_xboole_0(k1_tarski(X67),k5_enumset1(X68,X69,X70,X71,X72,X73,X74)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 7.05/7.23  cnf(c_0_66, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 7.05/7.23  cnf(c_0_67, plain, (k2_enumset1(X1,X1,X2,X3)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34])).
% 7.05/7.23  cnf(c_0_68, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k2_enumset1(X1,X1,X1,X1)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k2_enumset1(X5,X5,X5,X5),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k2_enumset1(X5,X5,X5,X5))),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_33]), c_0_58]), c_0_59])).
% 7.05/7.23  cnf(c_0_69, plain, (k6_enumset1(X1,X2,X2,X3,X4,X4,X4,X4)=k2_enumset1(X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_47, c_0_60])).
% 7.05/7.23  cnf(c_0_70, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_33]), c_0_33])).
% 7.05/7.23  cnf(c_0_71, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 7.05/7.23  cnf(c_0_72, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 7.05/7.23  cnf(c_0_73, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k2_tarski(X8,X9))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 7.05/7.23  cnf(c_0_74, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 7.05/7.23  cnf(c_0_75, negated_conjecture, (k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))!=k5_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k4_xboole_0(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_59])).
% 7.05/7.23  cnf(c_0_76, plain, (k2_enumset1(X1,X2,X2,X3)=k2_enumset1(X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_67, c_0_40])).
% 7.05/7.23  cnf(c_0_77, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k2_enumset1(X1,X1,X1,X1)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[c_0_68, c_0_41])).
% 7.05/7.23  cnf(c_0_78, plain, (k6_enumset1(X1,X1,X2,X3,X3,X3,X3,X3)=k2_enumset1(X1,X1,X2,X3)), inference(spm,[status(thm)],[c_0_47, c_0_69])).
% 7.05/7.23  cnf(c_0_79, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X1,X2,X3,X4)))=k6_enumset1(X5,X5,X6,X7,X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_70, c_0_41])).
% 7.05/7.23  cnf(c_0_80, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X8),k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_32]), c_0_33]), c_0_34]), c_0_34]), c_0_38]), c_0_36])).
% 7.05/7.23  cnf(c_0_81, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k2_enumset1(X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_36]), c_0_36])).
% 7.05/7.23  cnf(c_0_82, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k2_enumset1(X1,X1,X1,X1)))=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k2_enumset1(X8,X8,X8,X9),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_32]), c_0_33]), c_0_34]), c_0_36]), c_0_36]), c_0_59])).
% 7.05/7.23  cnf(c_0_83, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_34]), c_0_36])).
% 7.05/7.23  cnf(c_0_84, negated_conjecture, (k5_xboole_0(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k4_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)))!=k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))), inference(rw,[status(thm)],[c_0_75, c_0_70])).
% 7.05/7.23  cnf(c_0_85, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X5,X6)=k6_enumset1(X1,X1,X2,X3,X4,X4,X5,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_76]), c_0_41])).
% 7.05/7.23  cnf(c_0_86, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X3,X4)=k2_enumset1(X2,X3,X4,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_41]), c_0_46]), c_0_46]), c_0_79])).
% 7.05/7.23  cnf(c_0_87, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k6_enumset1(X3,X3,X4,X5,X6,X7,X8,X8),k2_enumset1(X1,X1,X1,X2)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_80, c_0_47])).
% 7.05/7.23  cnf(c_0_88, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X7,X8,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_80]), c_0_43])).
% 7.05/7.23  cnf(c_0_89, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X8),k2_enumset1(X1,X1,X1,X1)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 7.05/7.23  cnf(c_0_90, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X1)=k2_enumset1(X2,X3,X4,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_78]), c_0_41]), c_0_46]), c_0_60]), c_0_60]), c_0_79])).
% 7.05/7.23  cnf(c_0_91, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X8,X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_83]), c_0_81])).
% 7.05/7.23  cnf(c_0_92, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X6,X7,X8),k2_enumset1(X1,X1,X1,X1)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_47]), c_0_43])).
% 7.05/7.23  cnf(c_0_93, negated_conjecture, (k5_xboole_0(k2_enumset1(esk9_0,esk1_0,esk2_0,esk3_0),k4_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk9_0,esk1_0,esk2_0,esk3_0)))!=k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))), inference(rw,[status(thm)],[c_0_84, c_0_77])).
% 7.05/7.23  cnf(c_0_94, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X1,X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_46])).
% 7.05/7.23  cnf(c_0_95, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k6_enumset1(X1,X2,X3,X4,X5,X5,X6,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_47]), c_0_43])).
% 7.05/7.23  cnf(c_0_96, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k6_enumset1(X3,X4,X5,X6,X7,X7,X8,X8),k2_enumset1(X1,X1,X1,X2)))=k6_enumset1(X1,X2,X8,X3,X4,X5,X6,X7)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 7.05/7.23  cnf(c_0_97, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_47]), c_0_89])).
% 7.05/7.23  cnf(c_0_98, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X2,X3,X4,X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 7.05/7.23  cnf(c_0_99, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_46]), c_0_92])).
% 7.05/7.23  cnf(c_0_100, plain, (k5_xboole_0(k2_enumset1(X1,X2,X2,X3),k4_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8),k2_enumset1(X1,X2,X2,X3)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_83, c_0_77])).
% 7.05/7.23  cnf(c_0_101, plain, (k2_enumset1(X1,X1,X2,X3)=k2_enumset1(X3,X1,X2,X3)), inference(spm,[status(thm)],[c_0_46, c_0_90])).
% 7.05/7.23  cnf(c_0_102, negated_conjecture, (k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk9_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))!=k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94]), c_0_94]), c_0_77])).
% 7.05/7.23  cnf(c_0_103, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X4,X5,X6,X7,X8,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_95]), c_0_96])).
% 7.05/7.23  cnf(c_0_104, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X8,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 7.05/7.23  cnf(c_0_105, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k6_enumset1(X3,X3,X4,X4,X5,X6,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_46]), c_0_83]), c_0_79])).
% 7.05/7.23  cnf(c_0_106, plain, (k5_xboole_0(k2_enumset1(X1,X2,X2,X3),k4_xboole_0(k6_enumset1(X4,X4,X4,X5,X6,X6,X7,X8),k2_enumset1(X1,X2,X2,X3)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_100, c_0_95])).
% 7.05/7.23  cnf(c_0_107, plain, (k2_enumset1(X1,X2,X2,X3)=k2_enumset1(X3,X3,X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_86]), c_0_53])).
% 7.05/7.23  cnf(c_0_108, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k2_enumset1(X7,X8,X8,X7),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)))=k6_enumset1(X1,X2,X3,X4,X5,X6,X8,X7)), inference(spm,[status(thm)],[c_0_43, c_0_101])).
% 7.05/7.23  cnf(c_0_109, negated_conjecture, (k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk7_0,esk8_0,esk4_0,esk5_0,esk6_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))!=k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_103]), c_0_104]), c_0_104]), c_0_104])).
% 7.05/7.23  cnf(c_0_110, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X6,X7,X8,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_105]), c_0_106])).
% 7.05/7.23  cnf(c_0_111, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X8,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_107]), c_0_108])).
% 7.05/7.23  cnf(c_0_112, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110]), c_0_103]), c_0_110]), c_0_103]), c_0_104]), c_0_111])]), ['proof']).
% 7.05/7.23  # SZS output end CNFRefutation
% 7.05/7.23  # Proof object total steps             : 113
% 7.05/7.23  # Proof object clause steps            : 72
% 7.05/7.23  # Proof object formula steps           : 41
% 7.05/7.23  # Proof object conjectures             : 10
% 7.05/7.23  # Proof object clause conjectures      : 7
% 7.05/7.23  # Proof object formula conjectures     : 3
% 7.05/7.23  # Proof object initial clauses used    : 20
% 7.05/7.23  # Proof object initial formulas used   : 20
% 7.05/7.23  # Proof object generating inferences   : 28
% 7.05/7.23  # Proof object simplifying inferences  : 124
% 7.05/7.23  # Training examples: 0 positive, 0 negative
% 7.05/7.23  # Parsed axioms                        : 20
% 7.05/7.23  # Removed by relevancy pruning/SinE    : 0
% 7.05/7.23  # Initial clauses                      : 20
% 7.05/7.23  # Removed in clause preprocessing      : 8
% 7.05/7.23  # Initial clauses in saturation        : 12
% 7.05/7.23  # Processed clauses                    : 38792
% 7.05/7.23  # ...of these trivial                  : 239
% 7.05/7.23  # ...subsumed                          : 37458
% 7.05/7.23  # ...remaining for further processing  : 1095
% 7.05/7.23  # Other redundant clauses eliminated   : 0
% 7.05/7.23  # Clauses deleted for lack of memory   : 0
% 7.05/7.23  # Backward-subsumed                    : 59
% 7.05/7.23  # Backward-rewritten                   : 138
% 7.05/7.23  # Generated clauses                    : 1556593
% 7.05/7.23  # ...of the previous two non-trivial   : 1493896
% 7.05/7.23  # Contextual simplify-reflections      : 0
% 7.05/7.23  # Paramodulations                      : 1556593
% 7.05/7.23  # Factorizations                       : 0
% 7.05/7.23  # Equation resolutions                 : 0
% 7.05/7.23  # Propositional unsat checks           : 0
% 7.05/7.23  #    Propositional check models        : 0
% 7.05/7.23  #    Propositional check unsatisfiable : 0
% 7.05/7.23  #    Propositional clauses             : 0
% 7.05/7.23  #    Propositional clauses after purity: 0
% 7.05/7.23  #    Propositional unsat core size     : 0
% 7.05/7.23  #    Propositional preprocessing time  : 0.000
% 7.05/7.23  #    Propositional encoding time       : 0.000
% 7.05/7.23  #    Propositional solver time         : 0.000
% 7.05/7.23  #    Success case prop preproc time    : 0.000
% 7.05/7.23  #    Success case prop encoding time   : 0.000
% 7.05/7.23  #    Success case prop solver time     : 0.000
% 7.05/7.23  # Current number of processed clauses  : 886
% 7.05/7.23  #    Positive orientable unit clauses  : 141
% 7.05/7.23  #    Positive unorientable unit clauses: 745
% 7.05/7.23  #    Negative unit clauses             : 0
% 7.05/7.23  #    Non-unit-clauses                  : 0
% 7.05/7.23  # Current number of unprocessed clauses: 1446558
% 7.05/7.23  # ...number of literals in the above   : 1446558
% 7.05/7.23  # Current number of archived formulas  : 0
% 7.05/7.23  # Current number of archived clauses   : 217
% 7.05/7.23  # Clause-clause subsumption calls (NU) : 0
% 7.05/7.23  # Rec. Clause-clause subsumption calls : 0
% 7.05/7.23  # Non-unit clause-clause subsumptions  : 0
% 7.05/7.23  # Unit Clause-clause subsumption calls : 254344
% 7.05/7.23  # Rewrite failures with RHS unbound    : 0
% 7.05/7.23  # BW rewrite match attempts            : 392136
% 7.05/7.23  # BW rewrite match successes           : 81258
% 7.05/7.23  # Condensation attempts                : 0
% 7.05/7.23  # Condensation successes               : 0
% 7.05/7.23  # Termbank termtop insertions          : 9697689
% 7.11/7.27  
% 7.11/7.27  # -------------------------------------------------
% 7.11/7.27  # User time                : 6.506 s
% 7.11/7.27  # System time              : 0.418 s
% 7.11/7.27  # Total time               : 6.925 s
% 7.11/7.27  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
