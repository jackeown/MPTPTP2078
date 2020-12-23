%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 (1469 expanded)
%              Number of clauses        :   33 ( 528 expanded)
%              Number of leaves         :   16 ( 470 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 (1469 expanded)
%              Number of equality atoms :   65 (1468 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t99_enumset1,conjecture,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

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

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(t64_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(c_0_16,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_17,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X1,X3) ),
    inference(assume_negation,[status(cth)],[t99_enumset1])).

fof(c_0_19,plain,(
    ! [X33,X34,X35,X36,X37] : k3_enumset1(X33,X34,X35,X36,X37) = k2_xboole_0(k2_enumset1(X33,X34,X35,X36),k1_tarski(X37)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_20,plain,(
    ! [X46] : k2_tarski(X46,X46) = k1_tarski(X46) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X47,X48] : k1_enumset1(X47,X47,X48) = k2_tarski(X47,X48) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X49,X50,X51] : k2_enumset1(X49,X49,X50,X51) = k1_enumset1(X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X52,X53,X54,X55] : k3_enumset1(X52,X52,X53,X54,X55) = k2_enumset1(X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X56,X57,X58,X59,X60] : k4_enumset1(X56,X56,X57,X58,X59,X60) = k3_enumset1(X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X61,X62,X63,X64,X65,X66] : k5_enumset1(X61,X61,X62,X63,X64,X65,X66) = k4_enumset1(X61,X62,X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X67,X68,X69,X70,X71,X72,X73] : k6_enumset1(X67,X67,X68,X69,X70,X71,X72,X73) = k5_enumset1(X67,X68,X69,X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_29,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] : k6_enumset1(X21,X22,X23,X24,X25,X26,X27,X28) = k2_xboole_0(k2_enumset1(X21,X22,X23,X24),k2_enumset1(X25,X26,X27,X28)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_30,plain,(
    ! [X15,X16,X17,X18,X19,X20] : k4_enumset1(X15,X16,X17,X18,X19,X20) = k2_xboole_0(k1_enumset1(X15,X16,X17),k1_enumset1(X18,X19,X20)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

fof(c_0_31,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44,X45] : k6_enumset1(X38,X39,X40,X41,X42,X43,X44,X45) = k2_xboole_0(k1_enumset1(X38,X39,X40),k3_enumset1(X41,X42,X43,X44,X45)) ),
    inference(variable_rename,[status(thm)],[t64_enumset1])).

fof(c_0_32,plain,(
    ! [X13,X14] : k2_tarski(X13,X14) = k2_tarski(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_33,plain,(
    ! [X29,X30,X31,X32] : k2_enumset1(X29,X30,X31,X32) = k2_xboole_0(k1_enumset1(X29,X30,X31),k1_tarski(X32)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_34,negated_conjecture,(
    k1_enumset1(esk1_0,esk2_0,esk3_0) != k1_enumset1(esk2_0,esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( k1_enumset1(esk1_0,esk2_0,esk3_0) != k1_enumset1(esk2_0,esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_38]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_54,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_37]),c_0_37]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X5,X5,X5) = k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( k6_enumset1(X1,X2,X3,X4,X4,X4,X5,X6) = k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k6_enumset1(X2,X2,X2,X1,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_54]),c_0_51])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X2,X3,X4,X4,X4,X4,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_55,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_62,plain,
    ( k6_enumset1(X1,X2,X3,X4,X4,X4,X5,X6) = k6_enumset1(X2,X2,X2,X1,X3,X4,X5,X6) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X4) = k6_enumset1(X1,X1,X1,X2,X3,X4,X4,X4) ),
    inference(spm,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_64,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X4) ),
    inference(spm,[status(thm)],[c_0_57,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:21:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.039 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.39  fof(t99_enumset1, conjecture, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X1,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 0.19/0.39  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.39  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 0.19/0.39  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 0.19/0.39  fof(t64_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 0.19/0.39  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.39  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.19/0.39  fof(c_0_16, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(X11,k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.39  fof(c_0_17, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.39  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X1,X3)), inference(assume_negation,[status(cth)],[t99_enumset1])).
% 0.19/0.39  fof(c_0_19, plain, ![X33, X34, X35, X36, X37]:k3_enumset1(X33,X34,X35,X36,X37)=k2_xboole_0(k2_enumset1(X33,X34,X35,X36),k1_tarski(X37)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.19/0.39  fof(c_0_20, plain, ![X46]:k2_tarski(X46,X46)=k1_tarski(X46), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_21, plain, ![X47, X48]:k1_enumset1(X47,X47,X48)=k2_tarski(X47,X48), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.39  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  fof(c_0_24, plain, ![X49, X50, X51]:k2_enumset1(X49,X49,X50,X51)=k1_enumset1(X49,X50,X51), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.39  fof(c_0_25, plain, ![X52, X53, X54, X55]:k3_enumset1(X52,X52,X53,X54,X55)=k2_enumset1(X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.39  fof(c_0_26, plain, ![X56, X57, X58, X59, X60]:k4_enumset1(X56,X56,X57,X58,X59,X60)=k3_enumset1(X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.39  fof(c_0_27, plain, ![X61, X62, X63, X64, X65, X66]:k5_enumset1(X61,X61,X62,X63,X64,X65,X66)=k4_enumset1(X61,X62,X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.39  fof(c_0_28, plain, ![X67, X68, X69, X70, X71, X72, X73]:k6_enumset1(X67,X67,X68,X69,X70,X71,X72,X73)=k5_enumset1(X67,X68,X69,X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.39  fof(c_0_29, plain, ![X21, X22, X23, X24, X25, X26, X27, X28]:k6_enumset1(X21,X22,X23,X24,X25,X26,X27,X28)=k2_xboole_0(k2_enumset1(X21,X22,X23,X24),k2_enumset1(X25,X26,X27,X28)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.19/0.39  fof(c_0_30, plain, ![X15, X16, X17, X18, X19, X20]:k4_enumset1(X15,X16,X17,X18,X19,X20)=k2_xboole_0(k1_enumset1(X15,X16,X17),k1_enumset1(X18,X19,X20)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 0.19/0.39  fof(c_0_31, plain, ![X38, X39, X40, X41, X42, X43, X44, X45]:k6_enumset1(X38,X39,X40,X41,X42,X43,X44,X45)=k2_xboole_0(k1_enumset1(X38,X39,X40),k3_enumset1(X41,X42,X43,X44,X45)), inference(variable_rename,[status(thm)],[t64_enumset1])).
% 0.19/0.39  fof(c_0_32, plain, ![X13, X14]:k2_tarski(X13,X14)=k2_tarski(X14,X13), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.39  fof(c_0_33, plain, ![X29, X30, X31, X32]:k2_enumset1(X29,X30,X31,X32)=k2_xboole_0(k1_enumset1(X29,X30,X31),k1_tarski(X32)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.19/0.39  fof(c_0_34, negated_conjecture, k1_enumset1(esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk2_0,esk1_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.39  cnf(c_0_35, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.39  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  cnf(c_0_43, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_44, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_45, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_46, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.39  cnf(c_0_47, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_48, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (k1_enumset1(esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk2_0,esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.19/0.39  cnf(c_0_51, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_38]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.19/0.39  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.19/0.39  cnf(c_0_53, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.19/0.39  cnf(c_0_54, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_37]), c_0_37]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.19/0.39  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0)!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.19/0.39  cnf(c_0_57, plain, (k6_enumset1(X1,X2,X3,X4,X5,X5,X5,X5)=k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.39  cnf(c_0_58, plain, (k6_enumset1(X1,X2,X3,X4,X4,X4,X5,X6)=k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.39  cnf(c_0_59, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k6_enumset1(X2,X2,X2,X1,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_54]), c_0_51])).
% 0.19/0.39  cnf(c_0_60, plain, (k6_enumset1(X1,X2,X3,X4,X4,X4,X4,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_55, c_0_53])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.19/0.39  cnf(c_0_62, plain, (k6_enumset1(X1,X2,X3,X4,X4,X4,X5,X6)=k6_enumset1(X2,X2,X2,X1,X3,X4,X5,X6)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.39  cnf(c_0_63, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X4)=k6_enumset1(X1,X1,X1,X2,X3,X4,X4,X4)), inference(spm,[status(thm)],[c_0_58, c_0_57])).
% 0.19/0.39  cnf(c_0_64, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X4)), inference(spm,[status(thm)],[c_0_57, c_0_60])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64]), c_0_64])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 66
% 0.19/0.39  # Proof object clause steps            : 33
% 0.19/0.39  # Proof object formula steps           : 33
% 0.19/0.39  # Proof object conjectures             : 7
% 0.19/0.39  # Proof object clause conjectures      : 4
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 16
% 0.19/0.39  # Proof object initial formulas used   : 16
% 0.19/0.39  # Proof object generating inferences   : 4
% 0.19/0.39  # Proof object simplifying inferences  : 142
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 16
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 16
% 0.19/0.39  # Removed in clause preprocessing      : 9
% 0.19/0.39  # Initial clauses in saturation        : 7
% 0.19/0.39  # Processed clauses                    : 73
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 37
% 0.19/0.39  # ...remaining for further processing  : 36
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 2
% 0.19/0.39  # Generated clauses                    : 1437
% 0.19/0.39  # ...of the previous two non-trivial   : 1121
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 1437
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 27
% 0.19/0.39  #    Positive orientable unit clauses  : 6
% 0.19/0.39  #    Positive unorientable unit clauses: 21
% 0.19/0.39  #    Negative unit clauses             : 0
% 0.19/0.39  #    Non-unit-clauses                  : 0
% 0.19/0.39  # Current number of unprocessed clauses: 1062
% 0.19/0.39  # ...number of literals in the above   : 1062
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 18
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.39  # Unit Clause-clause subsumption calls : 287
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 1018
% 0.19/0.39  # BW rewrite match successes           : 239
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 8530
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.055 s
% 0.19/0.39  # System time              : 0.002 s
% 0.19/0.39  # Total time               : 0.057 s
% 0.19/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
