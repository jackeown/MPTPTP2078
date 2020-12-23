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
% DateTime   : Thu Dec  3 10:36:39 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 939 expanded)
%              Number of clauses        :   34 ( 366 expanded)
%              Number of leaves         :   13 ( 286 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 939 expanded)
%              Number of equality atoms :   60 ( 938 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t127_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(t84_enumset1,axiom,(
    ! [X1,X2,X3] : k4_enumset1(X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t131_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(t79_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t132_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

fof(c_0_13,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40,X41] : k7_enumset1(X33,X34,X35,X36,X37,X38,X39,X40,X41) = k2_xboole_0(k1_tarski(X33),k6_enumset1(X34,X35,X36,X37,X38,X39,X40,X41)) ),
    inference(variable_rename,[status(thm)],[t127_enumset1])).

fof(c_0_14,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k4_enumset1(X27,X28,X29,X30,X31,X32) = k2_xboole_0(k1_enumset1(X27,X28,X29),k1_enumset1(X30,X31,X32)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

fof(c_0_16,plain,(
    ! [X72,X73,X74] : k4_enumset1(X72,X72,X72,X72,X73,X74) = k1_enumset1(X72,X73,X74) ),
    inference(variable_rename,[status(thm)],[t84_enumset1])).

fof(c_0_17,plain,(
    ! [X62,X63,X64,X65,X66,X67] : k5_enumset1(X62,X62,X63,X64,X65,X66,X67) = k4_enumset1(X62,X63,X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_18,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48,X49,X50] : k7_enumset1(X42,X43,X44,X45,X46,X47,X48,X49,X50) = k2_xboole_0(k3_enumset1(X42,X43,X44,X45,X46),k2_enumset1(X47,X48,X49,X50)) ),
    inference(variable_rename,[status(thm)],[t131_enumset1])).

fof(c_0_19,plain,(
    ! [X68,X69,X70,X71] : k4_enumset1(X68,X68,X68,X69,X70,X71) = k2_enumset1(X68,X69,X70,X71) ),
    inference(variable_rename,[status(thm)],[t79_enumset1])).

fof(c_0_20,plain,(
    ! [X57,X58,X59,X60,X61] : k4_enumset1(X57,X57,X58,X59,X60,X61) = k3_enumset1(X57,X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_21,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25,X26] : k7_enumset1(X18,X19,X20,X21,X22,X23,X24,X25,X26) = k2_xboole_0(k2_enumset1(X18,X19,X20,X21),k3_enumset1(X22,X23,X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

fof(c_0_24,plain,(
    ! [X10,X11,X12] : k2_xboole_0(k2_xboole_0(X10,X11),X12) = k2_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_25,plain,(
    ! [X51,X52,X53,X54,X55,X56] : k4_enumset1(X51,X52,X53,X54,X55,X56) = k2_xboole_0(k1_tarski(X51),k3_enumset1(X52,X53,X54,X55,X56)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k4_enumset1(X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_33,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X13,X14,X15] : k5_xboole_0(k5_xboole_0(X13,X14),X15) = k5_xboole_0(X13,k5_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X1,X1,X1,X1,X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_22]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) = k5_xboole_0(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_22]),c_0_30]),c_0_31]),c_0_31]),c_0_28]),c_0_28]),c_0_28]),c_0_32])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_22]),c_0_30]),c_0_30]),c_0_31]),c_0_28]),c_0_28]),c_0_28]),c_0_32])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_22]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_22]),c_0_31]),c_0_28]),c_0_28])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X4,X5,X6),k1_tarski(X1))) = k5_enumset1(X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X5,X6,X7,X8),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k1_tarski(X1)),X7)) = k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),X7) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k5_enumset1(X1,X1,X2,X3,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_43])).

fof(c_0_48,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(assume_negation,[status(cth)],[t132_enumset1])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(X7,k5_enumset1(X1,X1,X2,X3,X4,X5,X6))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k4_xboole_0(X7,k5_enumset1(X2,X2,X2,X3,X4,X5,X6))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_46])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X3,X4,X5))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_47])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X5,X6,X7,X8),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X6,X7,X8),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_47]),c_0_39])).

fof(c_0_52,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_50])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X6,X7,X8),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k6_enumset1(X3,X4,X5,X6,X7,X7,X8,X9),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X8,X9,X10),k5_enumset1(X1,X1,X2,X3,X4,X5,X6))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_38])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_tarski(esk1_0))) != k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k4_xboole_0(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk8_0,esk9_0),k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_22]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_32])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X4,X5,X6))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 2.75/2.93  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.75/2.93  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.75/2.93  #
% 2.75/2.93  # Preprocessing time       : 0.026 s
% 2.75/2.93  # Presaturation interreduction done
% 2.75/2.93  
% 2.75/2.93  # Proof found!
% 2.75/2.93  # SZS status Theorem
% 2.75/2.93  # SZS output start CNFRefutation
% 2.75/2.93  fof(t127_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_enumset1)).
% 2.75/2.93  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.75/2.93  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.75/2.93  fof(t84_enumset1, axiom, ![X1, X2, X3]:k4_enumset1(X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 2.75/2.93  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.75/2.93  fof(t131_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_enumset1)).
% 2.75/2.93  fof(t79_enumset1, axiom, ![X1, X2, X3, X4]:k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 2.75/2.93  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.75/2.93  fof(l142_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l142_enumset1)).
% 2.75/2.93  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.75/2.93  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.75/2.93  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.75/2.93  fof(t132_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_enumset1)).
% 2.75/2.93  fof(c_0_13, plain, ![X33, X34, X35, X36, X37, X38, X39, X40, X41]:k7_enumset1(X33,X34,X35,X36,X37,X38,X39,X40,X41)=k2_xboole_0(k1_tarski(X33),k6_enumset1(X34,X35,X36,X37,X38,X39,X40,X41)), inference(variable_rename,[status(thm)],[t127_enumset1])).
% 2.75/2.93  fof(c_0_14, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 2.75/2.93  fof(c_0_15, plain, ![X27, X28, X29, X30, X31, X32]:k4_enumset1(X27,X28,X29,X30,X31,X32)=k2_xboole_0(k1_enumset1(X27,X28,X29),k1_enumset1(X30,X31,X32)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 2.75/2.93  fof(c_0_16, plain, ![X72, X73, X74]:k4_enumset1(X72,X72,X72,X72,X73,X74)=k1_enumset1(X72,X73,X74), inference(variable_rename,[status(thm)],[t84_enumset1])).
% 2.75/2.93  fof(c_0_17, plain, ![X62, X63, X64, X65, X66, X67]:k5_enumset1(X62,X62,X63,X64,X65,X66,X67)=k4_enumset1(X62,X63,X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 2.75/2.93  fof(c_0_18, plain, ![X42, X43, X44, X45, X46, X47, X48, X49, X50]:k7_enumset1(X42,X43,X44,X45,X46,X47,X48,X49,X50)=k2_xboole_0(k3_enumset1(X42,X43,X44,X45,X46),k2_enumset1(X47,X48,X49,X50)), inference(variable_rename,[status(thm)],[t131_enumset1])).
% 2.75/2.93  fof(c_0_19, plain, ![X68, X69, X70, X71]:k4_enumset1(X68,X68,X68,X69,X70,X71)=k2_enumset1(X68,X69,X70,X71), inference(variable_rename,[status(thm)],[t79_enumset1])).
% 2.75/2.93  fof(c_0_20, plain, ![X57, X58, X59, X60, X61]:k4_enumset1(X57,X57,X58,X59,X60,X61)=k3_enumset1(X57,X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 2.75/2.93  cnf(c_0_21, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.75/2.93  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.75/2.93  fof(c_0_23, plain, ![X18, X19, X20, X21, X22, X23, X24, X25, X26]:k7_enumset1(X18,X19,X20,X21,X22,X23,X24,X25,X26)=k2_xboole_0(k2_enumset1(X18,X19,X20,X21),k3_enumset1(X22,X23,X24,X25,X26)), inference(variable_rename,[status(thm)],[l142_enumset1])).
% 2.75/2.93  fof(c_0_24, plain, ![X10, X11, X12]:k2_xboole_0(k2_xboole_0(X10,X11),X12)=k2_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 2.75/2.93  fof(c_0_25, plain, ![X51, X52, X53, X54, X55, X56]:k4_enumset1(X51,X52,X53,X54,X55,X56)=k2_xboole_0(k1_tarski(X51),k3_enumset1(X52,X53,X54,X55,X56)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 2.75/2.93  cnf(c_0_26, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.75/2.93  cnf(c_0_27, plain, (k4_enumset1(X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.75/2.93  cnf(c_0_28, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.75/2.93  cnf(c_0_29, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.75/2.93  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.75/2.93  cnf(c_0_31, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.75/2.93  cnf(c_0_32, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 2.75/2.93  cnf(c_0_33, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.75/2.93  cnf(c_0_34, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.75/2.93  fof(c_0_35, plain, ![X13, X14, X15]:k5_xboole_0(k5_xboole_0(X13,X14),X15)=k5_xboole_0(X13,k5_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 2.75/2.93  cnf(c_0_36, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.75/2.93  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X1,X1,X1,X1,X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_22]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 2.75/2.93  cnf(c_0_38, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))=k5_xboole_0(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_22]), c_0_30]), c_0_31]), c_0_31]), c_0_28]), c_0_28]), c_0_28]), c_0_32])).
% 2.75/2.93  cnf(c_0_39, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))=k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X6,X7,X8,X9),k5_enumset1(X1,X1,X1,X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_22]), c_0_30]), c_0_30]), c_0_31]), c_0_28]), c_0_28]), c_0_28]), c_0_32])).
% 2.75/2.93  cnf(c_0_40, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_22]), c_0_22]), c_0_22]), c_0_22])).
% 2.75/2.93  cnf(c_0_41, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.75/2.93  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_22]), c_0_31]), c_0_28]), c_0_28])).
% 2.75/2.93  cnf(c_0_43, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X4,X5,X6),k1_tarski(X1)))=k5_enumset1(X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 2.75/2.93  cnf(c_0_44, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X5,X6,X7,X8),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 2.75/2.93  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 2.75/2.93  cnf(c_0_46, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k1_tarski(X1)),X7))=k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),X7)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 2.75/2.93  cnf(c_0_47, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k5_enumset1(X1,X1,X2,X3,X3,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_43])).
% 2.75/2.93  fof(c_0_48, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9))), inference(assume_negation,[status(cth)],[t132_enumset1])).
% 2.75/2.93  cnf(c_0_49, plain, (k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(X7,k5_enumset1(X1,X1,X2,X3,X4,X5,X6)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k5_enumset1(X2,X2,X2,X3,X4,X5,X6),k4_xboole_0(X7,k5_enumset1(X2,X2,X2,X3,X4,X5,X6))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_42]), c_0_46])).
% 2.75/2.93  cnf(c_0_50, plain, (k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X3,X4,X5)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_38, c_0_47])).
% 2.75/2.93  cnf(c_0_51, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X5,X6,X7,X8),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X6,X7,X8),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_47]), c_0_39])).
% 2.75/2.93  fof(c_0_52, negated_conjecture, k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).
% 2.75/2.93  cnf(c_0_53, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_50])).
% 2.75/2.93  cnf(c_0_54, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X6,X7,X8),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_44, c_0_51])).
% 2.75/2.93  cnf(c_0_55, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 2.75/2.93  cnf(c_0_56, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k6_enumset1(X3,X4,X5,X6,X7,X7,X8,X9),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 2.75/2.93  cnf(c_0_57, plain, (k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X8,X9,X10),k5_enumset1(X1,X1,X2,X3,X4,X5,X6)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10),k1_tarski(X2))),k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_49, c_0_38])).
% 2.75/2.93  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_tarski(esk1_0)))!=k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k4_xboole_0(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk8_0,esk9_0),k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_22]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_32])).
% 2.75/2.93  cnf(c_0_59, plain, (k5_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X8,X9),k5_enumset1(X1,X1,X2,X3,X4,X5,X6)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 2.75/2.93  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])]), ['proof']).
% 2.75/2.93  # SZS output end CNFRefutation
% 2.75/2.93  # Proof object total steps             : 61
% 2.75/2.93  # Proof object clause steps            : 34
% 2.75/2.93  # Proof object formula steps           : 27
% 2.75/2.93  # Proof object conjectures             : 6
% 2.75/2.93  # Proof object clause conjectures      : 3
% 2.75/2.93  # Proof object formula conjectures     : 3
% 2.75/2.93  # Proof object initial clauses used    : 13
% 2.75/2.93  # Proof object initial formulas used   : 13
% 2.75/2.93  # Proof object generating inferences   : 11
% 2.75/2.93  # Proof object simplifying inferences  : 47
% 2.75/2.93  # Training examples: 0 positive, 0 negative
% 2.75/2.93  # Parsed axioms                        : 13
% 2.75/2.93  # Removed by relevancy pruning/SinE    : 0
% 2.75/2.93  # Initial clauses                      : 13
% 2.75/2.93  # Removed in clause preprocessing      : 6
% 2.75/2.93  # Initial clauses in saturation        : 7
% 2.75/2.93  # Processed clauses                    : 4485
% 2.75/2.93  # ...of these trivial                  : 247
% 2.75/2.93  # ...subsumed                          : 3839
% 2.75/2.93  # ...remaining for further processing  : 399
% 2.75/2.93  # Other redundant clauses eliminated   : 0
% 2.75/2.93  # Clauses deleted for lack of memory   : 0
% 2.75/2.93  # Backward-subsumed                    : 8
% 2.75/2.93  # Backward-rewritten                   : 50
% 2.75/2.93  # Generated clauses                    : 98351
% 2.75/2.93  # ...of the previous two non-trivial   : 81860
% 2.75/2.93  # Contextual simplify-reflections      : 0
% 2.75/2.93  # Paramodulations                      : 98351
% 2.75/2.93  # Factorizations                       : 0
% 2.75/2.93  # Equation resolutions                 : 0
% 2.75/2.93  # Propositional unsat checks           : 0
% 2.75/2.93  #    Propositional check models        : 0
% 2.75/2.93  #    Propositional check unsatisfiable : 0
% 2.75/2.93  #    Propositional clauses             : 0
% 2.75/2.93  #    Propositional clauses after purity: 0
% 2.75/2.93  #    Propositional unsat core size     : 0
% 2.75/2.93  #    Propositional preprocessing time  : 0.000
% 2.75/2.93  #    Propositional encoding time       : 0.000
% 2.75/2.93  #    Propositional solver time         : 0.000
% 2.75/2.93  #    Success case prop preproc time    : 0.000
% 2.75/2.93  #    Success case prop encoding time   : 0.000
% 2.75/2.93  #    Success case prop solver time     : 0.000
% 2.75/2.93  # Current number of processed clauses  : 334
% 2.75/2.93  #    Positive orientable unit clauses  : 230
% 2.75/2.93  #    Positive unorientable unit clauses: 104
% 2.75/2.93  #    Negative unit clauses             : 0
% 2.75/2.93  #    Non-unit-clauses                  : 0
% 2.75/2.93  # Current number of unprocessed clauses: 77191
% 2.75/2.93  # ...number of literals in the above   : 77191
% 2.75/2.93  # Current number of archived formulas  : 0
% 2.75/2.93  # Current number of archived clauses   : 71
% 2.75/2.93  # Clause-clause subsumption calls (NU) : 0
% 2.75/2.93  # Rec. Clause-clause subsumption calls : 0
% 2.75/2.93  # Non-unit clause-clause subsumptions  : 0
% 2.75/2.93  # Unit Clause-clause subsumption calls : 3671
% 2.75/2.93  # Rewrite failures with RHS unbound    : 0
% 2.75/2.93  # BW rewrite match attempts            : 20022
% 2.75/2.93  # BW rewrite match successes           : 1197
% 2.75/2.93  # Condensation attempts                : 0
% 2.75/2.93  # Condensation successes               : 0
% 2.75/2.93  # Termbank termtop insertions          : 9666813
% 2.75/2.94  
% 2.75/2.94  # -------------------------------------------------
% 2.75/2.94  # User time                : 2.505 s
% 2.75/2.94  # System time              : 0.100 s
% 2.75/2.94  # Total time               : 2.605 s
% 2.75/2.94  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
