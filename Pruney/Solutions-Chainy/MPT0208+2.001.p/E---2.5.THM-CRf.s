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
% DateTime   : Thu Dec  3 10:36:40 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   76 (5747 expanded)
%              Number of clauses        :   39 (2040 expanded)
%              Number of leaves         :   18 (1853 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 (5747 expanded)
%              Number of equality atoms :   75 (5746 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

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

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(t131_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t134_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t128_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_enumset1)).

fof(t127_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(c_0_18,plain,(
    ! [X55,X56,X57,X58,X59,X60,X61,X62] : k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) = k2_xboole_0(k5_enumset1(X55,X56,X57,X58,X59,X60,X61),k1_tarski(X62)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_19,plain,(
    ! [X63] : k2_tarski(X63,X63) = k1_tarski(X63) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X64,X65] : k1_enumset1(X64,X64,X65) = k2_tarski(X64,X65) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_22,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X66,X67,X68] : k2_enumset1(X66,X66,X67,X68) = k1_enumset1(X66,X67,X68) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X69,X70,X71,X72] : k3_enumset1(X69,X69,X70,X71,X72) = k2_enumset1(X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X73,X74,X75,X76,X77] : k4_enumset1(X73,X73,X74,X75,X76,X77) = k3_enumset1(X73,X74,X75,X76,X77) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X78,X79,X80,X81,X82,X83] : k5_enumset1(X78,X78,X79,X80,X81,X82,X83) = k4_enumset1(X78,X79,X80,X81,X82,X83) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X84,X85,X86,X87,X88,X89,X90] : k6_enumset1(X84,X84,X85,X86,X87,X88,X89,X90) = k5_enumset1(X84,X85,X86,X87,X88,X89,X90) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,plain,(
    ! [X18,X19] : k2_tarski(X18,X19) = k2_tarski(X19,X18) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_29,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] : k6_enumset1(X20,X21,X22,X23,X24,X25,X26,X27) = k2_xboole_0(k2_enumset1(X20,X21,X22,X23),k2_enumset1(X24,X25,X26,X27)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_30,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52,X53,X54] : k7_enumset1(X46,X47,X48,X49,X50,X51,X52,X53,X54) = k2_xboole_0(k3_enumset1(X46,X47,X48,X49,X50),k2_enumset1(X51,X52,X53,X54)) ),
    inference(variable_rename,[status(thm)],[t131_enumset1])).

fof(c_0_31,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(assume_negation,[status(cth)],[t134_enumset1])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_47,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_48,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43,X44,X45] : k7_enumset1(X37,X38,X39,X40,X41,X42,X43,X44,X45) = k2_xboole_0(k2_tarski(X37,X38),k5_enumset1(X39,X40,X41,X42,X43,X44,X45)) ),
    inference(variable_rename,[status(thm)],[t128_enumset1])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_34]),c_0_34]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_35]),c_0_36]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_52,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_35]),c_0_36]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

fof(c_0_53,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36] : k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k1_tarski(X28),k6_enumset1(X29,X30,X31,X32,X33,X34,X35,X36)) ),
    inference(variable_rename,[status(thm)],[t127_enumset1])).

fof(c_0_54,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_35]),c_0_35]),c_0_36]),c_0_36])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_49])).

cnf(c_0_59,plain,
    ( k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X4,X5,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X3,X3,X4,X5,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_64,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X4,X4,X4) = k6_enumset1(X2,X2,X2,X2,X2,X1,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_58]),c_0_52]),c_0_59])).

cnf(c_0_65,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_66,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k5_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k5_xboole_0(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k3_xboole_0(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8)))) = k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_49])).

cnf(c_0_68,plain,
    ( k7_enumset1(X1,X2,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k5_xboole_0(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k3_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)))) != k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_56])).

cnf(c_0_70,plain,
    ( k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9)))) = k7_enumset1(X9,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_62,c_0_65])).

cnf(c_0_71,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k7_enumset1(X2,X1,X3,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_50]),c_0_63])).

cnf(c_0_72,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_56]),c_0_65]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k7_enumset1(esk1_0,esk9_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_74,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k7_enumset1(X1,X3,X4,X5,X6,X7,X8,X9,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_72]),c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_74]),c_0_74]),c_0_74]),c_0_74]),c_0_74]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.65  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.47/0.65  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.47/0.65  #
% 0.47/0.65  # Preprocessing time       : 0.027 s
% 0.47/0.65  # Presaturation interreduction done
% 0.47/0.65  
% 0.47/0.65  # Proof found!
% 0.47/0.65  # SZS status Theorem
% 0.47/0.65  # SZS output start CNFRefutation
% 0.47/0.65  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 0.47/0.65  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.47/0.65  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.65  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.47/0.65  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.47/0.65  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.47/0.65  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.47/0.65  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.47/0.65  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.47/0.65  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.47/0.65  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.47/0.65  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 0.47/0.65  fof(t131_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 0.47/0.65  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.47/0.65  fof(t134_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 0.47/0.65  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.47/0.65  fof(t128_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_tarski(X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_enumset1)).
% 0.47/0.65  fof(t127_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 0.47/0.65  fof(c_0_18, plain, ![X55, X56, X57, X58, X59, X60, X61, X62]:k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)=k2_xboole_0(k5_enumset1(X55,X56,X57,X58,X59,X60,X61),k1_tarski(X62)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 0.47/0.65  fof(c_0_19, plain, ![X63]:k2_tarski(X63,X63)=k1_tarski(X63), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.47/0.65  fof(c_0_20, plain, ![X64, X65]:k1_enumset1(X64,X64,X65)=k2_tarski(X64,X65), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.65  fof(c_0_21, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.47/0.65  fof(c_0_22, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.47/0.65  fof(c_0_23, plain, ![X66, X67, X68]:k2_enumset1(X66,X66,X67,X68)=k1_enumset1(X66,X67,X68), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.47/0.65  fof(c_0_24, plain, ![X69, X70, X71, X72]:k3_enumset1(X69,X69,X70,X71,X72)=k2_enumset1(X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.47/0.65  fof(c_0_25, plain, ![X73, X74, X75, X76, X77]:k4_enumset1(X73,X73,X74,X75,X76,X77)=k3_enumset1(X73,X74,X75,X76,X77), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.47/0.65  fof(c_0_26, plain, ![X78, X79, X80, X81, X82, X83]:k5_enumset1(X78,X78,X79,X80,X81,X82,X83)=k4_enumset1(X78,X79,X80,X81,X82,X83), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.47/0.65  fof(c_0_27, plain, ![X84, X85, X86, X87, X88, X89, X90]:k6_enumset1(X84,X84,X85,X86,X87,X88,X89,X90)=k5_enumset1(X84,X85,X86,X87,X88,X89,X90), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.47/0.65  fof(c_0_28, plain, ![X18, X19]:k2_tarski(X18,X19)=k2_tarski(X19,X18), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.47/0.65  fof(c_0_29, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:k6_enumset1(X20,X21,X22,X23,X24,X25,X26,X27)=k2_xboole_0(k2_enumset1(X20,X21,X22,X23),k2_enumset1(X24,X25,X26,X27)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.47/0.65  fof(c_0_30, plain, ![X46, X47, X48, X49, X50, X51, X52, X53, X54]:k7_enumset1(X46,X47,X48,X49,X50,X51,X52,X53,X54)=k2_xboole_0(k3_enumset1(X46,X47,X48,X49,X50),k2_enumset1(X51,X52,X53,X54)), inference(variable_rename,[status(thm)],[t131_enumset1])).
% 0.47/0.65  fof(c_0_31, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k2_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.47/0.65  cnf(c_0_32, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.65  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.65  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.65  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.65  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.65  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.65  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.65  cnf(c_0_40, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.65  cnf(c_0_41, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.47/0.65  cnf(c_0_42, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.65  cnf(c_0_43, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.65  cnf(c_0_44, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.47/0.65  fof(c_0_45, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(assume_negation,[status(cth)],[t134_enumset1])).
% 0.47/0.65  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.65  fof(c_0_47, plain, ![X12, X13]:k3_xboole_0(X12,X13)=k3_xboole_0(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.47/0.65  fof(c_0_48, plain, ![X37, X38, X39, X40, X41, X42, X43, X44, X45]:k7_enumset1(X37,X38,X39,X40,X41,X42,X43,X44,X45)=k2_xboole_0(k2_tarski(X37,X38),k5_enumset1(X39,X40,X41,X42,X43,X44,X45)), inference(variable_rename,[status(thm)],[t128_enumset1])).
% 0.47/0.65  cnf(c_0_49, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.47/0.65  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_34]), c_0_34]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.47/0.65  cnf(c_0_51, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_35]), c_0_36]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.47/0.65  cnf(c_0_52, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_35]), c_0_36]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.47/0.65  fof(c_0_53, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36]:k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)=k2_xboole_0(k1_tarski(X28),k6_enumset1(X29,X30,X31,X32,X33,X34,X35,X36)), inference(variable_rename,[status(thm)],[t127_enumset1])).
% 0.47/0.65  fof(c_0_54, negated_conjecture, k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 0.47/0.65  cnf(c_0_55, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_35]), c_0_35]), c_0_36]), c_0_36])).
% 0.47/0.65  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.47/0.65  cnf(c_0_57, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_tarski(X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.47/0.65  cnf(c_0_58, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_49])).
% 0.47/0.65  cnf(c_0_59, plain, (k7_enumset1(X1,X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.47/0.65  cnf(c_0_60, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.65  cnf(c_0_61, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.47/0.65  cnf(c_0_62, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.47/0.65  cnf(c_0_63, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X4,X5,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X3,X3,X4,X5,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.47/0.65  cnf(c_0_64, plain, (k6_enumset1(X1,X1,X2,X3,X4,X4,X4,X4)=k6_enumset1(X2,X2,X2,X2,X2,X1,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_58]), c_0_52]), c_0_59])).
% 0.47/0.65  cnf(c_0_65, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k3_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.47/0.65  cnf(c_0_66, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k5_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k5_xboole_0(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k3_xboole_0(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.47/0.65  cnf(c_0_67, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8))))=k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)), inference(spm,[status(thm)],[c_0_62, c_0_49])).
% 0.47/0.65  cnf(c_0_68, plain, (k7_enumset1(X1,X2,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_59])).
% 0.47/0.65  cnf(c_0_69, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k5_xboole_0(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k3_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))))!=k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)), inference(rw,[status(thm)],[c_0_66, c_0_56])).
% 0.47/0.65  cnf(c_0_70, plain, (k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))))=k7_enumset1(X9,X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_62, c_0_65])).
% 0.47/0.65  cnf(c_0_71, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k7_enumset1(X2,X1,X3,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_50]), c_0_63])).
% 0.47/0.65  cnf(c_0_72, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_56]), c_0_65]), c_0_68])).
% 0.47/0.65  cnf(c_0_73, negated_conjecture, (k7_enumset1(esk1_0,esk9_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.47/0.65  cnf(c_0_74, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k7_enumset1(X1,X3,X4,X5,X6,X7,X8,X9,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_72]), c_0_65])).
% 0.47/0.65  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_74]), c_0_74]), c_0_74]), c_0_74]), c_0_74]), c_0_74])]), ['proof']).
% 0.47/0.65  # SZS output end CNFRefutation
% 0.47/0.65  # Proof object total steps             : 76
% 0.47/0.65  # Proof object clause steps            : 39
% 0.47/0.65  # Proof object formula steps           : 37
% 0.47/0.65  # Proof object conjectures             : 8
% 0.47/0.65  # Proof object clause conjectures      : 5
% 0.47/0.65  # Proof object formula conjectures     : 3
% 0.47/0.65  # Proof object initial clauses used    : 18
% 0.47/0.65  # Proof object initial formulas used   : 18
% 0.47/0.65  # Proof object generating inferences   : 9
% 0.47/0.65  # Proof object simplifying inferences  : 130
% 0.47/0.65  # Training examples: 0 positive, 0 negative
% 0.47/0.65  # Parsed axioms                        : 18
% 0.47/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.65  # Initial clauses                      : 18
% 0.47/0.65  # Removed in clause preprocessing      : 9
% 0.47/0.65  # Initial clauses in saturation        : 9
% 0.47/0.65  # Processed clauses                    : 820
% 0.47/0.65  # ...of these trivial                  : 82
% 0.47/0.65  # ...subsumed                          : 511
% 0.47/0.65  # ...remaining for further processing  : 227
% 0.47/0.65  # Other redundant clauses eliminated   : 0
% 0.47/0.65  # Clauses deleted for lack of memory   : 0
% 0.47/0.65  # Backward-subsumed                    : 9
% 0.47/0.65  # Backward-rewritten                   : 16
% 0.47/0.65  # Generated clauses                    : 45080
% 0.47/0.65  # ...of the previous two non-trivial   : 40383
% 0.47/0.65  # Contextual simplify-reflections      : 0
% 0.47/0.65  # Paramodulations                      : 45080
% 0.47/0.65  # Factorizations                       : 0
% 0.47/0.65  # Equation resolutions                 : 0
% 0.47/0.65  # Propositional unsat checks           : 0
% 0.47/0.65  #    Propositional check models        : 0
% 0.47/0.65  #    Propositional check unsatisfiable : 0
% 0.47/0.65  #    Propositional clauses             : 0
% 0.47/0.65  #    Propositional clauses after purity: 0
% 0.47/0.65  #    Propositional unsat core size     : 0
% 0.47/0.65  #    Propositional preprocessing time  : 0.000
% 0.47/0.65  #    Propositional encoding time       : 0.000
% 0.47/0.65  #    Propositional solver time         : 0.000
% 0.47/0.65  #    Success case prop preproc time    : 0.000
% 0.47/0.65  #    Success case prop encoding time   : 0.000
% 0.47/0.65  #    Success case prop solver time     : 0.000
% 0.47/0.65  # Current number of processed clauses  : 193
% 0.47/0.65  #    Positive orientable unit clauses  : 35
% 0.47/0.65  #    Positive unorientable unit clauses: 158
% 0.47/0.65  #    Negative unit clauses             : 0
% 0.47/0.65  #    Non-unit-clauses                  : 0
% 0.47/0.65  # Current number of unprocessed clauses: 39484
% 0.47/0.65  # ...number of literals in the above   : 39484
% 0.47/0.65  # Current number of archived formulas  : 0
% 0.47/0.65  # Current number of archived clauses   : 43
% 0.47/0.65  # Clause-clause subsumption calls (NU) : 0
% 0.47/0.65  # Rec. Clause-clause subsumption calls : 0
% 0.47/0.65  # Non-unit clause-clause subsumptions  : 0
% 0.47/0.65  # Unit Clause-clause subsumption calls : 13957
% 0.47/0.65  # Rewrite failures with RHS unbound    : 0
% 0.47/0.65  # BW rewrite match attempts            : 33303
% 0.47/0.65  # BW rewrite match successes           : 4594
% 0.47/0.65  # Condensation attempts                : 0
% 0.47/0.65  # Condensation successes               : 0
% 0.47/0.65  # Termbank termtop insertions          : 211735
% 0.47/0.65  
% 0.47/0.65  # -------------------------------------------------
% 0.47/0.65  # User time                : 0.288 s
% 0.47/0.65  # System time              : 0.028 s
% 0.47/0.65  # Total time               : 0.316 s
% 0.47/0.65  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
