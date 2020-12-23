%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:11 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   80 (1088 expanded)
%              Number of clauses        :   39 ( 395 expanded)
%              Number of leaves         :   20 ( 346 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 (1088 expanded)
%              Number of equality atoms :   79 (1087 expanded)
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

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

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

fof(t66_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t58_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(t98_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(c_0_20,plain,(
    ! [X34,X35] : k2_xboole_0(X34,X35) = k5_xboole_0(X34,k4_xboole_0(X35,X34)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_21,plain,(
    ! [X23,X24] : k4_xboole_0(X23,X24) = k5_xboole_0(X23,k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X1,X3) ),
    inference(assume_negation,[status(cth)],[t99_enumset1])).

fof(c_0_23,plain,(
    ! [X57,X58,X59,X60,X61,X62,X63] : k5_enumset1(X57,X58,X59,X60,X61,X62,X63) = k2_xboole_0(k3_enumset1(X57,X58,X59,X60,X61),k2_tarski(X62,X63)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

fof(c_0_24,plain,(
    ! [X81,X82] : k1_enumset1(X81,X81,X82) = k2_tarski(X81,X82) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X83,X84,X85] : k2_enumset1(X83,X83,X84,X85) = k1_enumset1(X83,X84,X85) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X86,X87,X88,X89] : k3_enumset1(X86,X86,X87,X88,X89) = k2_enumset1(X86,X87,X88,X89) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X90,X91,X92,X93,X94] : k4_enumset1(X90,X90,X91,X92,X93,X94) = k3_enumset1(X90,X91,X92,X93,X94) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X95,X96,X97,X98,X99,X100] : k5_enumset1(X95,X95,X96,X97,X98,X99,X100) = k4_enumset1(X95,X96,X97,X98,X99,X100) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X101,X102,X103,X104,X105,X106,X107] : k6_enumset1(X101,X101,X102,X103,X104,X105,X106,X107) = k5_enumset1(X101,X102,X103,X104,X105,X106,X107) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_32,plain,(
    ! [X64,X65,X66,X67,X68,X69,X70,X71] : k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) = k2_xboole_0(k3_enumset1(X64,X65,X66,X67,X68),k1_enumset1(X69,X70,X71)) ),
    inference(variable_rename,[status(thm)],[t66_enumset1])).

fof(c_0_33,negated_conjecture,(
    k1_enumset1(esk2_0,esk3_0,esk4_0) != k1_enumset1(esk3_0,esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_43,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49] : k5_enumset1(X43,X44,X45,X46,X47,X48,X49) = k2_xboole_0(k2_tarski(X43,X44),k3_enumset1(X45,X46,X47,X48,X49)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

fof(c_0_44,plain,(
    ! [X11,X12] : k5_xboole_0(X11,X12) = k5_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_45,plain,(
    ! [X31,X32,X33] : k5_xboole_0(k5_xboole_0(X31,X32),X33) = k5_xboole_0(X31,k5_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_46,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_47,plain,(
    ! [X72,X73,X74,X75,X76,X77,X78,X79] : k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) = k2_xboole_0(k5_enumset1(X72,X73,X74,X75,X76,X77,X78),k1_tarski(X79)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

fof(c_0_48,plain,(
    ! [X80] : k2_tarski(X80,X80) = k1_tarski(X80) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_49,plain,(
    ! [X50,X51,X52,X53,X54,X55,X56] : k5_enumset1(X50,X51,X52,X53,X54,X55,X56) = k2_xboole_0(k1_enumset1(X50,X51,X52),k2_enumset1(X53,X54,X55,X56)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

cnf(c_0_50,negated_conjecture,
    ( k1_enumset1(esk2_0,esk3_0,esk4_0) != k1_enumset1(esk3_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_53,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_60,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] : k5_enumset1(X36,X37,X38,X39,X40,X41,X42) = k2_xboole_0(k1_tarski(X36),k4_enumset1(X37,X38,X39,X40,X41,X42)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

cnf(c_0_61,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0,esk4_0) != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_62,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_35]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_52,c_0_56])).

cnf(c_0_66,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_35]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_67,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_68,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_69,plain,(
    ! [X108,X109,X110] : k1_enumset1(X108,X109,X110) = k1_enumset1(X108,X110,X109) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

cnf(c_0_70,negated_conjecture,
    ( k6_enumset1(esk2_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_62]),c_0_62]),c_0_62]),c_0_62])).

cnf(c_0_71,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X7) = k6_enumset1(X6,X6,X7,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_54]),c_0_65])).

cnf(c_0_72,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X4,X4,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_58]),c_0_35]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_66,c_0_56])).

cnf(c_0_75,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk2_0,esk3_0) != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_77,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X7,X7,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_73]),c_0_54]),c_0_74])).

cnf(c_0_78,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.56/0.77  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.56/0.77  # and selection function GSelectMinInfpos.
% 0.56/0.77  #
% 0.56/0.77  # Preprocessing time       : 0.028 s
% 0.56/0.77  # Presaturation interreduction done
% 0.56/0.77  
% 0.56/0.77  # Proof found!
% 0.56/0.77  # SZS status Theorem
% 0.56/0.77  # SZS output start CNFRefutation
% 0.56/0.77  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.56/0.77  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.56/0.77  fof(t99_enumset1, conjecture, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X1,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 0.56/0.77  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 0.56/0.77  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.56/0.77  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.56/0.77  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.56/0.77  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.56/0.77  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.56/0.77  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.56/0.77  fof(t66_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 0.56/0.77  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 0.56/0.77  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.56/0.77  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.56/0.77  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.56/0.77  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 0.56/0.77  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.56/0.77  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 0.56/0.77  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 0.56/0.77  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 0.56/0.77  fof(c_0_20, plain, ![X34, X35]:k2_xboole_0(X34,X35)=k5_xboole_0(X34,k4_xboole_0(X35,X34)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.56/0.77  fof(c_0_21, plain, ![X23, X24]:k4_xboole_0(X23,X24)=k5_xboole_0(X23,k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.56/0.77  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X1,X3)), inference(assume_negation,[status(cth)],[t99_enumset1])).
% 0.56/0.77  fof(c_0_23, plain, ![X57, X58, X59, X60, X61, X62, X63]:k5_enumset1(X57,X58,X59,X60,X61,X62,X63)=k2_xboole_0(k3_enumset1(X57,X58,X59,X60,X61),k2_tarski(X62,X63)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 0.56/0.77  fof(c_0_24, plain, ![X81, X82]:k1_enumset1(X81,X81,X82)=k2_tarski(X81,X82), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.56/0.77  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.56/0.77  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.56/0.77  fof(c_0_27, plain, ![X83, X84, X85]:k2_enumset1(X83,X83,X84,X85)=k1_enumset1(X83,X84,X85), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.56/0.77  fof(c_0_28, plain, ![X86, X87, X88, X89]:k3_enumset1(X86,X86,X87,X88,X89)=k2_enumset1(X86,X87,X88,X89), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.56/0.77  fof(c_0_29, plain, ![X90, X91, X92, X93, X94]:k4_enumset1(X90,X90,X91,X92,X93,X94)=k3_enumset1(X90,X91,X92,X93,X94), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.56/0.77  fof(c_0_30, plain, ![X95, X96, X97, X98, X99, X100]:k5_enumset1(X95,X95,X96,X97,X98,X99,X100)=k4_enumset1(X95,X96,X97,X98,X99,X100), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.56/0.77  fof(c_0_31, plain, ![X101, X102, X103, X104, X105, X106, X107]:k6_enumset1(X101,X101,X102,X103,X104,X105,X106,X107)=k5_enumset1(X101,X102,X103,X104,X105,X106,X107), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.56/0.77  fof(c_0_32, plain, ![X64, X65, X66, X67, X68, X69, X70, X71]:k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)=k2_xboole_0(k3_enumset1(X64,X65,X66,X67,X68),k1_enumset1(X69,X70,X71)), inference(variable_rename,[status(thm)],[t66_enumset1])).
% 0.56/0.77  fof(c_0_33, negated_conjecture, k1_enumset1(esk2_0,esk3_0,esk4_0)!=k1_enumset1(esk3_0,esk2_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.56/0.77  cnf(c_0_34, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.56/0.77  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.56/0.77  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.56/0.77  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.56/0.77  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.56/0.77  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.56/0.77  cnf(c_0_40, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.56/0.77  cnf(c_0_41, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.56/0.77  cnf(c_0_42, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.56/0.77  fof(c_0_43, plain, ![X43, X44, X45, X46, X47, X48, X49]:k5_enumset1(X43,X44,X45,X46,X47,X48,X49)=k2_xboole_0(k2_tarski(X43,X44),k3_enumset1(X45,X46,X47,X48,X49)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 0.56/0.77  fof(c_0_44, plain, ![X11, X12]:k5_xboole_0(X11,X12)=k5_xboole_0(X12,X11), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.56/0.77  fof(c_0_45, plain, ![X31, X32, X33]:k5_xboole_0(k5_xboole_0(X31,X32),X33)=k5_xboole_0(X31,k5_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.56/0.77  fof(c_0_46, plain, ![X9, X10]:k3_xboole_0(X9,X10)=k3_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.56/0.77  fof(c_0_47, plain, ![X72, X73, X74, X75, X76, X77, X78, X79]:k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)=k2_xboole_0(k5_enumset1(X72,X73,X74,X75,X76,X77,X78),k1_tarski(X79)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 0.56/0.77  fof(c_0_48, plain, ![X80]:k2_tarski(X80,X80)=k1_tarski(X80), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.56/0.77  fof(c_0_49, plain, ![X50, X51, X52, X53, X54, X55, X56]:k5_enumset1(X50,X51,X52,X53,X54,X55,X56)=k2_xboole_0(k1_enumset1(X50,X51,X52),k2_enumset1(X53,X54,X55,X56)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 0.56/0.77  cnf(c_0_50, negated_conjecture, (k1_enumset1(esk2_0,esk3_0,esk4_0)!=k1_enumset1(esk3_0,esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.56/0.77  cnf(c_0_51, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.56/0.77  cnf(c_0_52, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.56/0.77  cnf(c_0_53, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.56/0.77  cnf(c_0_54, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.56/0.77  cnf(c_0_55, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.56/0.77  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.56/0.77  cnf(c_0_57, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.56/0.77  cnf(c_0_58, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.56/0.77  cnf(c_0_59, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.56/0.77  fof(c_0_60, plain, ![X36, X37, X38, X39, X40, X41, X42]:k5_enumset1(X36,X37,X38,X39,X40,X41,X42)=k2_xboole_0(k1_tarski(X36),k4_enumset1(X37,X38,X39,X40,X41,X42)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 0.56/0.77  cnf(c_0_61, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0,esk4_0)!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.56/0.77  cnf(c_0_62, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.56/0.77  cnf(c_0_63, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_35]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.56/0.77  cnf(c_0_64, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.56/0.77  cnf(c_0_65, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_52, c_0_56])).
% 0.56/0.77  cnf(c_0_66, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_35]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.56/0.77  cnf(c_0_67, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.56/0.77  cnf(c_0_68, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.56/0.77  fof(c_0_69, plain, ![X108, X109, X110]:k1_enumset1(X108,X109,X110)=k1_enumset1(X108,X110,X109), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 0.56/0.77  cnf(c_0_70, negated_conjecture, (k6_enumset1(esk2_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_62]), c_0_62]), c_0_62]), c_0_62])).
% 0.56/0.77  cnf(c_0_71, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X7)=k6_enumset1(X6,X6,X7,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_54]), c_0_65])).
% 0.56/0.77  cnf(c_0_72, plain, (k6_enumset1(X1,X1,X2,X3,X4,X4,X4,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.56/0.77  cnf(c_0_73, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_58]), c_0_35]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.56/0.77  cnf(c_0_74, plain, (k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_66, c_0_56])).
% 0.56/0.77  cnf(c_0_75, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.56/0.77  cnf(c_0_76, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk2_0,esk3_0)!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.56/0.77  cnf(c_0_77, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k6_enumset1(X7,X7,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_73]), c_0_54]), c_0_74])).
% 0.56/0.77  cnf(c_0_78, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.56/0.77  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_78])]), ['proof']).
% 0.56/0.77  # SZS output end CNFRefutation
% 0.56/0.77  # Proof object total steps             : 80
% 0.56/0.77  # Proof object clause steps            : 39
% 0.56/0.77  # Proof object formula steps           : 41
% 0.56/0.77  # Proof object conjectures             : 8
% 0.56/0.77  # Proof object clause conjectures      : 5
% 0.56/0.77  # Proof object formula conjectures     : 3
% 0.56/0.77  # Proof object initial clauses used    : 20
% 0.56/0.77  # Proof object initial formulas used   : 20
% 0.56/0.77  # Proof object generating inferences   : 6
% 0.56/0.77  # Proof object simplifying inferences  : 144
% 0.56/0.77  # Training examples: 0 positive, 0 negative
% 0.56/0.77  # Parsed axioms                        : 27
% 0.56/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.56/0.77  # Initial clauses                      : 32
% 0.56/0.77  # Removed in clause preprocessing      : 9
% 0.56/0.77  # Initial clauses in saturation        : 23
% 0.56/0.77  # Processed clauses                    : 1403
% 0.56/0.77  # ...of these trivial                  : 105
% 0.56/0.77  # ...subsumed                          : 1066
% 0.56/0.77  # ...remaining for further processing  : 232
% 0.56/0.77  # Other redundant clauses eliminated   : 0
% 0.56/0.77  # Clauses deleted for lack of memory   : 0
% 0.56/0.77  # Backward-subsumed                    : 0
% 0.56/0.77  # Backward-rewritten                   : 17
% 0.56/0.77  # Generated clauses                    : 19494
% 0.56/0.77  # ...of the previous two non-trivial   : 16565
% 0.56/0.77  # Contextual simplify-reflections      : 2
% 0.56/0.77  # Paramodulations                      : 19492
% 0.56/0.77  # Factorizations                       : 2
% 0.56/0.77  # Equation resolutions                 : 0
% 0.56/0.77  # Propositional unsat checks           : 0
% 0.56/0.77  #    Propositional check models        : 0
% 0.56/0.77  #    Propositional check unsatisfiable : 0
% 0.56/0.77  #    Propositional clauses             : 0
% 0.56/0.77  #    Propositional clauses after purity: 0
% 0.56/0.77  #    Propositional unsat core size     : 0
% 0.56/0.77  #    Propositional preprocessing time  : 0.000
% 0.56/0.77  #    Propositional encoding time       : 0.000
% 0.56/0.77  #    Propositional solver time         : 0.000
% 0.56/0.77  #    Success case prop preproc time    : 0.000
% 0.56/0.77  #    Success case prop encoding time   : 0.000
% 0.56/0.77  #    Success case prop solver time     : 0.000
% 0.56/0.77  # Current number of processed clauses  : 192
% 0.56/0.77  #    Positive orientable unit clauses  : 56
% 0.56/0.77  #    Positive unorientable unit clauses: 33
% 0.56/0.77  #    Negative unit clauses             : 0
% 0.56/0.77  #    Non-unit-clauses                  : 103
% 0.56/0.77  # Current number of unprocessed clauses: 15169
% 0.56/0.77  # ...number of literals in the above   : 27335
% 0.56/0.77  # Current number of archived formulas  : 0
% 0.56/0.77  # Current number of archived clauses   : 49
% 0.56/0.77  # Clause-clause subsumption calls (NU) : 7362
% 0.56/0.77  # Rec. Clause-clause subsumption calls : 7232
% 0.56/0.77  # Non-unit clause-clause subsumptions  : 900
% 0.56/0.77  # Unit Clause-clause subsumption calls : 810
% 0.56/0.77  # Rewrite failures with RHS unbound    : 0
% 0.56/0.77  # BW rewrite match attempts            : 1984
% 0.56/0.77  # BW rewrite match successes           : 684
% 0.56/0.77  # Condensation attempts                : 0
% 0.56/0.77  # Condensation successes               : 0
% 0.56/0.77  # Termbank termtop insertions          : 264094
% 0.56/0.77  
% 0.56/0.77  # -------------------------------------------------
% 0.56/0.77  # User time                : 0.412 s
% 0.56/0.77  # System time              : 0.017 s
% 0.56/0.77  # Total time               : 0.429 s
% 0.56/0.77  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
