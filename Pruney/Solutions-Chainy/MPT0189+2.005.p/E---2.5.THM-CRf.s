%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:17 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   72 (1200 expanded)
%              Number of clauses        :   41 ( 441 expanded)
%              Number of leaves         :   15 ( 379 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 (1200 expanded)
%              Number of equality atoms :   71 (1199 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t108_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X1,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t66_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(t64_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

fof(t103_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X1,X3,X4) ),
    inference(assume_negation,[status(cth)],[t108_enumset1])).

fof(c_0_16,plain,(
    ! [X24,X25,X26,X27,X28] : k3_enumset1(X24,X25,X26,X27,X28) = k2_xboole_0(k2_enumset1(X24,X25,X26,X27),k1_tarski(X28)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_17,plain,(
    ! [X45] : k2_tarski(X45,X45) = k1_tarski(X45) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X46,X47] : k1_enumset1(X46,X46,X47) = k2_tarski(X46,X47) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X48,X49,X50] : k2_enumset1(X48,X48,X49,X50) = k1_enumset1(X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X51,X52,X53,X54] : k3_enumset1(X51,X51,X52,X53,X54) = k2_enumset1(X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X55,X56,X57,X58,X59] : k4_enumset1(X55,X55,X56,X57,X58,X59) = k3_enumset1(X55,X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X60,X61,X62,X63,X64,X65] : k5_enumset1(X60,X60,X61,X62,X63,X64,X65) = k4_enumset1(X60,X61,X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X66,X67,X68,X69,X70,X71,X72] : k6_enumset1(X66,X66,X67,X68,X69,X70,X71,X72) = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_24,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43,X44] : k6_enumset1(X37,X38,X39,X40,X41,X42,X43,X44) = k2_xboole_0(k3_enumset1(X37,X38,X39,X40,X41),k1_enumset1(X42,X43,X44)) ),
    inference(variable_rename,[status(thm)],[t66_enumset1])).

fof(c_0_25,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk2_0,esk1_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X15,X16,X17,X18] : k2_enumset1(X15,X16,X17,X18) = k2_enumset1(X15,X17,X18,X16) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

fof(c_0_36,plain,(
    ! [X19,X20,X21,X22,X23] : k3_enumset1(X19,X20,X21,X22,X23) = k2_xboole_0(k1_tarski(X19),k2_enumset1(X20,X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_37,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X29,X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k1_enumset1(X29,X30,X31),k3_enumset1(X32,X33,X34,X35,X36)) ),
    inference(variable_rename,[status(thm)],[t64_enumset1])).

fof(c_0_38,plain,(
    ! [X11,X12,X13,X14] : k2_enumset1(X11,X12,X13,X14) = k2_enumset1(X11,X12,X14,X13) ),
    inference(variable_rename,[status(thm)],[t103_enumset1])).

cnf(c_0_39,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk2_0,esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_29]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X9,X10] : k2_tarski(X9,X10) = k2_tarski(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X5,X5) = k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_29]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X4,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk4_0,esk4_0) != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X1,X4,X2,X3,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_49]),c_0_41])).

cnf(c_0_56,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X1,X1,X2,X2,X3,X4,X5) = k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X3,X2,X4) ),
    inference(spm,[status(thm)],[c_0_49,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk1_0,esk4_0,esk4_0,esk4_0) != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X2,X2,X1,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_56]),c_0_52])).

cnf(c_0_61,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X5,X5) = k6_enumset1(X1,X1,X1,X2,X2,X3,X4,X5) ),
    inference(spm,[status(thm)],[c_0_48,c_0_57])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X4,X4,X4,X5,X5,X6,X7,X8)) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_63,plain,
    ( k6_enumset1(X1,X2,X3,X4,X4,X5,X6,X7) = k6_enumset1(X1,X2,X3,X4,X4,X7,X5,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_49]),c_0_52])).

cnf(c_0_64,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X8,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_53]),c_0_41])).

cnf(c_0_65,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X1,X3,X2,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_58]),c_0_41])).

cnf(c_0_66,plain,
    ( k6_enumset1(X1,X2,X3,X4,X4,X4,X5,X6) = k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) ),
    inference(spm,[status(thm)],[c_0_41,c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0,esk1_0,esk4_0) != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_57])).

cnf(c_0_68,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X7,X8,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_62])).

cnf(c_0_69,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X1,X3,X2,X4,X5,X7,X6) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,plain,
    ( k6_enumset1(X1,X2,X3,X4,X4,X5,X6,X7) = k6_enumset1(X1,X2,X3,X4,X5,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_66]),c_0_52])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.92/1.14  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.92/1.14  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.92/1.14  #
% 0.92/1.14  # Preprocessing time       : 0.026 s
% 0.92/1.14  # Presaturation interreduction done
% 0.92/1.14  
% 0.92/1.14  # Proof found!
% 0.92/1.14  # SZS status Theorem
% 0.92/1.14  # SZS output start CNFRefutation
% 0.92/1.14  fof(t108_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X1,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 0.92/1.14  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 0.92/1.14  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.92/1.14  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.92/1.14  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.92/1.14  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.92/1.14  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.92/1.14  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.92/1.14  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.92/1.14  fof(t66_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 0.92/1.14  fof(t105_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 0.92/1.14  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.92/1.14  fof(t64_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_enumset1)).
% 0.92/1.14  fof(t103_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X2,X4,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 0.92/1.14  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.92/1.14  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X1,X3,X4)), inference(assume_negation,[status(cth)],[t108_enumset1])).
% 0.92/1.14  fof(c_0_16, plain, ![X24, X25, X26, X27, X28]:k3_enumset1(X24,X25,X26,X27,X28)=k2_xboole_0(k2_enumset1(X24,X25,X26,X27),k1_tarski(X28)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.92/1.14  fof(c_0_17, plain, ![X45]:k2_tarski(X45,X45)=k1_tarski(X45), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.92/1.14  fof(c_0_18, plain, ![X46, X47]:k1_enumset1(X46,X46,X47)=k2_tarski(X46,X47), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.92/1.14  fof(c_0_19, plain, ![X48, X49, X50]:k2_enumset1(X48,X48,X49,X50)=k1_enumset1(X48,X49,X50), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.92/1.14  fof(c_0_20, plain, ![X51, X52, X53, X54]:k3_enumset1(X51,X51,X52,X53,X54)=k2_enumset1(X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.92/1.14  fof(c_0_21, plain, ![X55, X56, X57, X58, X59]:k4_enumset1(X55,X55,X56,X57,X58,X59)=k3_enumset1(X55,X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.92/1.14  fof(c_0_22, plain, ![X60, X61, X62, X63, X64, X65]:k5_enumset1(X60,X60,X61,X62,X63,X64,X65)=k4_enumset1(X60,X61,X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.92/1.14  fof(c_0_23, plain, ![X66, X67, X68, X69, X70, X71, X72]:k6_enumset1(X66,X66,X67,X68,X69,X70,X71,X72)=k5_enumset1(X66,X67,X68,X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.92/1.14  fof(c_0_24, plain, ![X37, X38, X39, X40, X41, X42, X43, X44]:k6_enumset1(X37,X38,X39,X40,X41,X42,X43,X44)=k2_xboole_0(k3_enumset1(X37,X38,X39,X40,X41),k1_enumset1(X42,X43,X44)), inference(variable_rename,[status(thm)],[t66_enumset1])).
% 0.92/1.14  fof(c_0_25, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk2_0,esk1_0,esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.92/1.14  cnf(c_0_26, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.92/1.14  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.92/1.14  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.92/1.14  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.92/1.14  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.92/1.14  cnf(c_0_31, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.92/1.14  cnf(c_0_32, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.92/1.14  cnf(c_0_33, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.92/1.14  cnf(c_0_34, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.92/1.14  fof(c_0_35, plain, ![X15, X16, X17, X18]:k2_enumset1(X15,X16,X17,X18)=k2_enumset1(X15,X17,X18,X16), inference(variable_rename,[status(thm)],[t105_enumset1])).
% 0.92/1.14  fof(c_0_36, plain, ![X19, X20, X21, X22, X23]:k3_enumset1(X19,X20,X21,X22,X23)=k2_xboole_0(k1_tarski(X19),k2_enumset1(X20,X21,X22,X23)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.92/1.14  fof(c_0_37, plain, ![X29, X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X29,X30,X31,X32,X33,X34,X35,X36)=k2_xboole_0(k1_enumset1(X29,X30,X31),k3_enumset1(X32,X33,X34,X35,X36)), inference(variable_rename,[status(thm)],[t64_enumset1])).
% 0.92/1.14  fof(c_0_38, plain, ![X11, X12, X13, X14]:k2_enumset1(X11,X12,X13,X14)=k2_enumset1(X11,X12,X14,X13), inference(variable_rename,[status(thm)],[t103_enumset1])).
% 0.92/1.14  cnf(c_0_39, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk2_0,esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.92/1.14  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33])).
% 0.92/1.14  cnf(c_0_41, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_29]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.92/1.14  cnf(c_0_42, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.92/1.14  fof(c_0_43, plain, ![X9, X10]:k2_tarski(X9,X10)=k2_tarski(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.92/1.14  cnf(c_0_44, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.92/1.14  cnf(c_0_45, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.92/1.14  cnf(c_0_46, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X2,X4,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.92/1.14  cnf(c_0_47, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.92/1.14  cnf(c_0_48, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X5,X5)=k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.92/1.14  cnf(c_0_49, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.92/1.14  cnf(c_0_50, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.92/1.14  cnf(c_0_51, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33])).
% 0.92/1.14  cnf(c_0_52, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_29]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.92/1.14  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X4,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.92/1.14  cnf(c_0_54, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk4_0,esk4_0)!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.92/1.14  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k6_enumset1(X1,X1,X4,X2,X3,X5,X6,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_49]), c_0_41])).
% 0.92/1.14  cnf(c_0_56, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.92/1.14  cnf(c_0_57, plain, (k6_enumset1(X1,X1,X1,X2,X2,X3,X4,X5)=k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.92/1.14  cnf(c_0_58, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X3,X2,X4)), inference(spm,[status(thm)],[c_0_49, c_0_53])).
% 0.92/1.14  cnf(c_0_59, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk1_0,esk4_0,esk4_0,esk4_0)!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.92/1.14  cnf(c_0_60, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k6_enumset1(X2,X2,X1,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_56]), c_0_52])).
% 0.92/1.14  cnf(c_0_61, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X5,X5)=k6_enumset1(X1,X1,X1,X2,X2,X3,X4,X5)), inference(spm,[status(thm)],[c_0_48, c_0_57])).
% 0.92/1.14  cnf(c_0_62, plain, (k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X4,X4,X4,X5,X5,X6,X7,X8))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_52, c_0_57])).
% 0.92/1.14  cnf(c_0_63, plain, (k6_enumset1(X1,X2,X3,X4,X4,X5,X6,X7)=k6_enumset1(X1,X2,X3,X4,X4,X7,X5,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_49]), c_0_52])).
% 0.92/1.14  cnf(c_0_64, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X8,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_53]), c_0_41])).
% 0.92/1.14  cnf(c_0_65, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k6_enumset1(X1,X1,X3,X2,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_58]), c_0_41])).
% 0.92/1.14  cnf(c_0_66, plain, (k6_enumset1(X1,X2,X3,X4,X4,X4,X5,X6)=k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)), inference(spm,[status(thm)],[c_0_41, c_0_52])).
% 0.92/1.14  cnf(c_0_67, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0,esk1_0,esk4_0)!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_57])).
% 0.92/1.14  cnf(c_0_68, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X7,X8,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_62])).
% 0.92/1.14  cnf(c_0_69, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k6_enumset1(X1,X1,X3,X2,X4,X5,X7,X6)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.92/1.14  cnf(c_0_70, plain, (k6_enumset1(X1,X2,X3,X4,X4,X5,X6,X7)=k6_enumset1(X1,X2,X3,X4,X5,X5,X6,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_66]), c_0_52])).
% 0.92/1.14  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70])]), ['proof']).
% 0.92/1.14  # SZS output end CNFRefutation
% 0.92/1.14  # Proof object total steps             : 72
% 0.92/1.14  # Proof object clause steps            : 41
% 0.92/1.14  # Proof object formula steps           : 31
% 0.92/1.14  # Proof object conjectures             : 9
% 0.92/1.14  # Proof object clause conjectures      : 6
% 0.92/1.14  # Proof object formula conjectures     : 3
% 0.92/1.14  # Proof object initial clauses used    : 15
% 0.92/1.14  # Proof object initial formulas used   : 15
% 0.92/1.14  # Proof object generating inferences   : 12
% 0.92/1.14  # Proof object simplifying inferences  : 98
% 0.92/1.14  # Training examples: 0 positive, 0 negative
% 0.92/1.14  # Parsed axioms                        : 15
% 0.92/1.14  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.14  # Initial clauses                      : 15
% 0.92/1.14  # Removed in clause preprocessing      : 7
% 0.92/1.14  # Initial clauses in saturation        : 8
% 0.92/1.14  # Processed clauses                    : 1365
% 0.92/1.14  # ...of these trivial                  : 13
% 0.92/1.14  # ...subsumed                          : 1010
% 0.92/1.14  # ...remaining for further processing  : 342
% 0.92/1.14  # Other redundant clauses eliminated   : 0
% 0.92/1.14  # Clauses deleted for lack of memory   : 0
% 0.92/1.14  # Backward-subsumed                    : 30
% 0.92/1.14  # Backward-rewritten                   : 13
% 0.92/1.14  # Generated clauses                    : 164748
% 0.92/1.14  # ...of the previous two non-trivial   : 146498
% 0.92/1.14  # Contextual simplify-reflections      : 0
% 0.92/1.14  # Paramodulations                      : 164748
% 0.92/1.14  # Factorizations                       : 0
% 0.92/1.14  # Equation resolutions                 : 0
% 0.92/1.14  # Propositional unsat checks           : 0
% 0.92/1.14  #    Propositional check models        : 0
% 0.92/1.14  #    Propositional check unsatisfiable : 0
% 0.92/1.14  #    Propositional clauses             : 0
% 0.92/1.14  #    Propositional clauses after purity: 0
% 0.92/1.14  #    Propositional unsat core size     : 0
% 0.92/1.14  #    Propositional preprocessing time  : 0.000
% 0.92/1.14  #    Propositional encoding time       : 0.000
% 0.92/1.14  #    Propositional solver time         : 0.000
% 0.92/1.14  #    Success case prop preproc time    : 0.000
% 0.92/1.14  #    Success case prop encoding time   : 0.000
% 0.92/1.14  #    Success case prop solver time     : 0.000
% 0.92/1.14  # Current number of processed clauses  : 291
% 0.92/1.14  #    Positive orientable unit clauses  : 45
% 0.92/1.14  #    Positive unorientable unit clauses: 246
% 0.92/1.14  #    Negative unit clauses             : 0
% 0.92/1.14  #    Non-unit-clauses                  : 0
% 0.92/1.14  # Current number of unprocessed clauses: 144514
% 0.92/1.14  # ...number of literals in the above   : 144514
% 0.92/1.14  # Current number of archived formulas  : 0
% 0.92/1.14  # Current number of archived clauses   : 58
% 0.92/1.14  # Clause-clause subsumption calls (NU) : 0
% 0.92/1.14  # Rec. Clause-clause subsumption calls : 0
% 0.92/1.14  # Non-unit clause-clause subsumptions  : 0
% 0.92/1.14  # Unit Clause-clause subsumption calls : 40353
% 0.92/1.14  # Rewrite failures with RHS unbound    : 0
% 0.92/1.14  # BW rewrite match attempts            : 74791
% 0.92/1.14  # BW rewrite match successes           : 17463
% 0.92/1.14  # Condensation attempts                : 0
% 0.92/1.14  # Condensation successes               : 0
% 0.92/1.14  # Termbank termtop insertions          : 497086
% 0.92/1.14  
% 0.92/1.14  # -------------------------------------------------
% 0.92/1.14  # User time                : 0.745 s
% 0.92/1.14  # System time              : 0.054 s
% 0.92/1.14  # Total time               : 0.799 s
% 0.92/1.14  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
