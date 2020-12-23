%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:39 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 242 expanded)
%              Number of clauses        :   31 (  99 expanded)
%              Number of leaves         :   14 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 242 expanded)
%              Number of equality atoms :   59 ( 241 expanded)
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

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t127_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t131_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(t132_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(c_0_14,plain,(
    ! [X10,X11,X12] : k2_xboole_0(k2_xboole_0(X10,X11),X12) = k2_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_15,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54] : k5_enumset1(X48,X49,X50,X51,X52,X53,X54) = k2_xboole_0(k1_tarski(X48),k4_enumset1(X49,X50,X51,X52,X53,X54)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

fof(c_0_17,plain,(
    ! [X75,X76,X77,X78,X79,X80,X81] : k6_enumset1(X75,X75,X76,X77,X78,X79,X80,X81) = k5_enumset1(X75,X76,X77,X78,X79,X80,X81) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_18,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31,X32] : k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) = k2_xboole_0(k1_tarski(X24),k6_enumset1(X25,X26,X27,X28,X29,X30,X31,X32)) ),
    inference(variable_rename,[status(thm)],[t127_enumset1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X13,X14,X15] : k5_xboole_0(k5_xboole_0(X13,X14),X15) = k5_xboole_0(X13,k5_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_22,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X42,X43,X44,X45,X46,X47] : k4_enumset1(X42,X43,X44,X45,X46,X47) = k2_xboole_0(k1_tarski(X42),k3_enumset1(X43,X44,X45,X46,X47)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_25,plain,(
    ! [X70,X71,X72,X73,X74] : k4_enumset1(X70,X70,X71,X72,X73,X74) = k3_enumset1(X70,X71,X72,X73,X74) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X18,X19,X20,X21,X22,X23] : k4_enumset1(X18,X19,X20,X21,X22,X23) = k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

fof(c_0_27,plain,(
    ! [X63,X64,X65] : k2_enumset1(X63,X63,X64,X65) = k1_enumset1(X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X66,X67,X68,X69] : k3_enumset1(X66,X66,X67,X68,X69) = k2_enumset1(X66,X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40,X41] : k7_enumset1(X33,X34,X35,X36,X37,X38,X39,X40,X41) = k2_xboole_0(k3_enumset1(X33,X34,X35,X36,X37),k2_enumset1(X38,X39,X40,X41)) ),
    inference(variable_rename,[status(thm)],[t131_enumset1])).

cnf(c_0_30,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_31,plain,(
    ! [X55,X56,X57,X58,X59,X60,X61,X62] : k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) = k2_xboole_0(k1_tarski(X55),k5_enumset1(X56,X57,X58,X59,X60,X61,X62)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_20]),c_0_23])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(assume_negation,[status(cth)],[t132_enumset1])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)),X8)) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),X8) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X2,X3,X4,X5,X6),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_20]),c_0_36])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k4_xboole_0(k4_enumset1(X4,X4,X4,X4,X5,X6),k4_enumset1(X1,X1,X1,X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_20]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) = k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_xboole_0(k4_enumset1(X6,X6,X6,X7,X8,X9),k4_enumset1(X1,X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_20]),c_0_39]),c_0_36]),c_0_36]),c_0_36]),c_0_41])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_20]),c_0_23])).

fof(c_0_50,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(X8,k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k4_xboole_0(X8,k4_enumset1(X2,X3,X4,X5,X6,X7))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_34]),c_0_45])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X1,X2,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_46,c_0_34])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_xboole_0(k4_enumset1(X7,X7,X7,X8,X9,X10),k4_enumset1(X1,X2,X3,X4,X5,X6))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_52]),c_0_52])).

cnf(c_0_56,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X2,X3,X4,X5,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_53]),c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_tarski(esk1_0))) != k5_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k4_xboole_0(k4_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk8_0,esk9_0),k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_20]),c_0_38]),c_0_39]),c_0_36]),c_0_41])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_xboole_0(k4_enumset1(X7,X7,X7,X7,X8,X9),k4_enumset1(X1,X2,X3,X4,X5,X6))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.58  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.58  #
% 0.21/0.58  # Preprocessing time       : 0.044 s
% 0.21/0.58  # Presaturation interreduction done
% 0.21/0.58  
% 0.21/0.58  # Proof found!
% 0.21/0.58  # SZS status Theorem
% 0.21/0.58  # SZS output start CNFRefutation
% 0.21/0.58  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.21/0.58  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.58  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 0.21/0.58  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.58  fof(t127_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 0.21/0.58  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.21/0.58  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.21/0.58  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.58  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 0.21/0.58  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.58  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.58  fof(t131_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 0.21/0.58  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 0.21/0.58  fof(t132_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_enumset1)).
% 0.21/0.58  fof(c_0_14, plain, ![X10, X11, X12]:k2_xboole_0(k2_xboole_0(X10,X11),X12)=k2_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.21/0.58  fof(c_0_15, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.58  fof(c_0_16, plain, ![X48, X49, X50, X51, X52, X53, X54]:k5_enumset1(X48,X49,X50,X51,X52,X53,X54)=k2_xboole_0(k1_tarski(X48),k4_enumset1(X49,X50,X51,X52,X53,X54)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 0.21/0.58  fof(c_0_17, plain, ![X75, X76, X77, X78, X79, X80, X81]:k6_enumset1(X75,X75,X76,X77,X78,X79,X80,X81)=k5_enumset1(X75,X76,X77,X78,X79,X80,X81), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.58  fof(c_0_18, plain, ![X24, X25, X26, X27, X28, X29, X30, X31, X32]:k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)=k2_xboole_0(k1_tarski(X24),k6_enumset1(X25,X26,X27,X28,X29,X30,X31,X32)), inference(variable_rename,[status(thm)],[t127_enumset1])).
% 0.21/0.58  cnf(c_0_19, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.58  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.58  fof(c_0_21, plain, ![X13, X14, X15]:k5_xboole_0(k5_xboole_0(X13,X14),X15)=k5_xboole_0(X13,k5_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.21/0.58  cnf(c_0_22, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.58  cnf(c_0_23, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.58  fof(c_0_24, plain, ![X42, X43, X44, X45, X46, X47]:k4_enumset1(X42,X43,X44,X45,X46,X47)=k2_xboole_0(k1_tarski(X42),k3_enumset1(X43,X44,X45,X46,X47)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.21/0.58  fof(c_0_25, plain, ![X70, X71, X72, X73, X74]:k4_enumset1(X70,X70,X71,X72,X73,X74)=k3_enumset1(X70,X71,X72,X73,X74), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.58  fof(c_0_26, plain, ![X18, X19, X20, X21, X22, X23]:k4_enumset1(X18,X19,X20,X21,X22,X23)=k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X21,X22,X23)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 0.21/0.58  fof(c_0_27, plain, ![X63, X64, X65]:k2_enumset1(X63,X63,X64,X65)=k1_enumset1(X63,X64,X65), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.58  fof(c_0_28, plain, ![X66, X67, X68, X69]:k3_enumset1(X66,X66,X67,X68,X69)=k2_enumset1(X66,X67,X68,X69), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.58  fof(c_0_29, plain, ![X33, X34, X35, X36, X37, X38, X39, X40, X41]:k7_enumset1(X33,X34,X35,X36,X37,X38,X39,X40,X41)=k2_xboole_0(k3_enumset1(X33,X34,X35,X36,X37),k2_enumset1(X38,X39,X40,X41)), inference(variable_rename,[status(thm)],[t131_enumset1])).
% 0.21/0.58  cnf(c_0_30, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.58  fof(c_0_31, plain, ![X55, X56, X57, X58, X59, X60, X61, X62]:k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)=k2_xboole_0(k1_tarski(X55),k5_enumset1(X56,X57,X58,X59,X60,X61,X62)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.21/0.58  cnf(c_0_32, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20]), c_0_20]), c_0_20])).
% 0.21/0.58  cnf(c_0_33, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.58  cnf(c_0_34, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_20]), c_0_23])).
% 0.21/0.58  cnf(c_0_35, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.58  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.58  cnf(c_0_37, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.58  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.58  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.58  cnf(c_0_40, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.58  cnf(c_0_41, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_30, c_0_20])).
% 0.21/0.58  cnf(c_0_42, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.58  fof(c_0_43, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9))), inference(assume_negation,[status(cth)],[t132_enumset1])).
% 0.21/0.58  cnf(c_0_44, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.58  cnf(c_0_45, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)),X8))=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),X8)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.58  cnf(c_0_46, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X2,X3,X4,X5,X6),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_20]), c_0_36])).
% 0.21/0.58  cnf(c_0_47, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k4_xboole_0(k4_enumset1(X4,X4,X4,X4,X5,X6),k4_enumset1(X1,X1,X1,X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_20]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_36]), c_0_36]), c_0_36])).
% 0.21/0.58  cnf(c_0_48, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))=k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_xboole_0(k4_enumset1(X6,X6,X6,X7,X8,X9),k4_enumset1(X1,X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_20]), c_0_39]), c_0_36]), c_0_36]), c_0_36]), c_0_41])).
% 0.21/0.58  cnf(c_0_49, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_20]), c_0_23])).
% 0.21/0.58  fof(c_0_50, negated_conjecture, k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 0.21/0.58  cnf(c_0_51, plain, (k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(X8,k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k4_xboole_0(X8,k4_enumset1(X2,X3,X4,X5,X6,X7))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_34]), c_0_45])).
% 0.21/0.58  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X2,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_46, c_0_34])).
% 0.21/0.58  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X2,X3,X4,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.21/0.58  cnf(c_0_54, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.58  cnf(c_0_55, plain, (k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_xboole_0(k4_enumset1(X7,X7,X7,X8,X9,X10),k4_enumset1(X1,X2,X3,X4,X5,X6)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_48]), c_0_52]), c_0_52])).
% 0.21/0.58  cnf(c_0_56, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k6_enumset1(X1,X2,X3,X4,X5,X5,X6,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_53]), c_0_34])).
% 0.21/0.58  cnf(c_0_57, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_tarski(esk1_0)))!=k5_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k4_xboole_0(k4_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk8_0,esk9_0),k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_20]), c_0_38]), c_0_39]), c_0_36]), c_0_41])).
% 0.21/0.58  cnf(c_0_58, plain, (k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_xboole_0(k4_enumset1(X7,X7,X7,X7,X8,X9),k4_enumset1(X1,X2,X3,X4,X5,X6)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_49])).
% 0.21/0.58  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])]), ['proof']).
% 0.21/0.58  # SZS output end CNFRefutation
% 0.21/0.58  # Proof object total steps             : 60
% 0.21/0.58  # Proof object clause steps            : 31
% 0.21/0.58  # Proof object formula steps           : 29
% 0.21/0.58  # Proof object conjectures             : 6
% 0.21/0.58  # Proof object clause conjectures      : 3
% 0.21/0.58  # Proof object formula conjectures     : 3
% 0.21/0.58  # Proof object initial clauses used    : 14
% 0.21/0.58  # Proof object initial formulas used   : 14
% 0.21/0.58  # Proof object generating inferences   : 5
% 0.21/0.58  # Proof object simplifying inferences  : 43
% 0.21/0.58  # Training examples: 0 positive, 0 negative
% 0.21/0.58  # Parsed axioms                        : 14
% 0.21/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.58  # Initial clauses                      : 14
% 0.21/0.58  # Removed in clause preprocessing      : 6
% 0.21/0.58  # Initial clauses in saturation        : 8
% 0.21/0.58  # Processed clauses                    : 995
% 0.21/0.58  # ...of these trivial                  : 214
% 0.21/0.58  # ...subsumed                          : 640
% 0.21/0.58  # ...remaining for further processing  : 141
% 0.21/0.58  # Other redundant clauses eliminated   : 0
% 0.21/0.58  # Clauses deleted for lack of memory   : 0
% 0.21/0.58  # Backward-subsumed                    : 0
% 0.21/0.58  # Backward-rewritten                   : 20
% 0.21/0.58  # Generated clauses                    : 8048
% 0.21/0.58  # ...of the previous two non-trivial   : 4821
% 0.21/0.58  # Contextual simplify-reflections      : 0
% 0.21/0.58  # Paramodulations                      : 8048
% 0.21/0.58  # Factorizations                       : 0
% 0.21/0.58  # Equation resolutions                 : 0
% 0.21/0.58  # Propositional unsat checks           : 0
% 0.21/0.58  #    Propositional check models        : 0
% 0.21/0.58  #    Propositional check unsatisfiable : 0
% 0.21/0.58  #    Propositional clauses             : 0
% 0.21/0.58  #    Propositional clauses after purity: 0
% 0.21/0.58  #    Propositional unsat core size     : 0
% 0.21/0.58  #    Propositional preprocessing time  : 0.000
% 0.21/0.58  #    Propositional encoding time       : 0.000
% 0.21/0.58  #    Propositional solver time         : 0.000
% 0.21/0.58  #    Success case prop preproc time    : 0.000
% 0.21/0.58  #    Success case prop encoding time   : 0.000
% 0.21/0.58  #    Success case prop solver time     : 0.000
% 0.21/0.58  # Current number of processed clauses  : 113
% 0.21/0.58  #    Positive orientable unit clauses  : 89
% 0.21/0.58  #    Positive unorientable unit clauses: 24
% 0.21/0.58  #    Negative unit clauses             : 0
% 0.21/0.58  #    Non-unit-clauses                  : 0
% 0.21/0.58  # Current number of unprocessed clauses: 3826
% 0.21/0.58  # ...number of literals in the above   : 3826
% 0.21/0.58  # Current number of archived formulas  : 0
% 0.21/0.58  # Current number of archived clauses   : 34
% 0.21/0.58  # Clause-clause subsumption calls (NU) : 0
% 0.21/0.58  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.58  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.58  # Unit Clause-clause subsumption calls : 218
% 0.21/0.58  # Rewrite failures with RHS unbound    : 0
% 0.21/0.58  # BW rewrite match attempts            : 1428
% 0.21/0.58  # BW rewrite match successes           : 201
% 0.21/0.58  # Condensation attempts                : 0
% 0.21/0.58  # Condensation successes               : 0
% 0.21/0.58  # Termbank termtop insertions          : 245284
% 0.21/0.58  
% 0.21/0.58  # -------------------------------------------------
% 0.21/0.58  # User time                : 0.228 s
% 0.21/0.58  # System time              : 0.011 s
% 0.21/0.58  # Total time               : 0.239 s
% 0.21/0.58  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
