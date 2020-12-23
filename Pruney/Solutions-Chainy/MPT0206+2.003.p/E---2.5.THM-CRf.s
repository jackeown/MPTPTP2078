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

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 513 expanded)
%              Number of clauses        :   30 ( 190 expanded)
%              Number of leaves         :   14 ( 161 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 513 expanded)
%              Number of equality atoms :   58 ( 512 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t127_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

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

fof(t131_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t132_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(c_0_14,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31,X32] : k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) = k2_xboole_0(k1_tarski(X24),k6_enumset1(X25,X26,X27,X28,X29,X30,X31,X32)) ),
    inference(variable_rename,[status(thm)],[t127_enumset1])).

fof(c_0_15,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X21,X22,X23] : k4_enumset1(X18,X19,X20,X21,X22,X23) = k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

fof(c_0_17,plain,(
    ! [X54,X55,X56] : k2_enumset1(X54,X54,X55,X56) = k1_enumset1(X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X57,X58,X59,X60] : k3_enumset1(X57,X57,X58,X59,X60) = k2_enumset1(X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X61,X62,X63,X64,X65] : k4_enumset1(X61,X61,X62,X63,X64,X65) = k3_enumset1(X61,X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_20,plain,(
    ! [X66,X67,X68,X69,X70,X71] : k5_enumset1(X66,X66,X67,X68,X69,X70,X71) = k4_enumset1(X66,X67,X68,X69,X70,X71) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_21,plain,(
    ! [X72,X73,X74,X75,X76,X77,X78] : k6_enumset1(X72,X72,X73,X74,X75,X76,X77,X78) = k5_enumset1(X72,X73,X74,X75,X76,X77,X78) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_22,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40,X41] : k7_enumset1(X33,X34,X35,X36,X37,X38,X39,X40,X41) = k2_xboole_0(k3_enumset1(X33,X34,X35,X36,X37),k2_enumset1(X38,X39,X40,X41)) ),
    inference(variable_rename,[status(thm)],[t131_enumset1])).

cnf(c_0_23,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X10,X11,X12] : k2_xboole_0(k2_xboole_0(X10,X11),X12) = k2_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_26,plain,(
    ! [X48,X49,X50,X51,X52,X53] : k4_enumset1(X48,X49,X50,X51,X52,X53) = k2_xboole_0(k3_enumset1(X48,X49,X50,X51,X52),k1_tarski(X53)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_27,plain,(
    ! [X42,X43,X44,X45,X46,X47] : k4_enumset1(X42,X43,X44,X45,X46,X47) = k2_xboole_0(k1_tarski(X42),k3_enumset1(X43,X44,X45,X46,X47)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X13,X14,X15] : k5_xboole_0(k5_xboole_0(X13,X14),X15) = k5_xboole_0(X13,k5_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k4_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1))) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_24]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_35])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(assume_negation,[status(cth)],[t132_enumset1])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k1_tarski(X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_24]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X3,X4,X5,X6),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_24]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X4,X5,X6),k1_tarski(X1))) = k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_48,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k4_xboole_0(k1_tarski(X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)),X7)) = k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),X7) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(X7,k1_tarski(X6))),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))) = k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(X7,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_45]),c_0_50])).

cnf(c_0_54,plain,
    ( k6_enumset1(X1,X1,X1,X2,X2,X3,X4,X5) = k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_51]),c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_tarski(esk1_0))) != k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k4_xboole_0(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk8_0,esk9_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_24]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_35])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X7,X8,X9,X10,X11),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))) = k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X8,X9,X10,X11),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X1,X1,X2,X2,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_51,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:20:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.50  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.013 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(t127_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 0.19/0.50  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.50  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 0.19/0.50  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.50  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.50  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.50  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.50  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.50  fof(t131_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 0.19/0.50  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.19/0.50  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.19/0.50  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.19/0.50  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.50  fof(t132_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_enumset1)).
% 0.19/0.50  fof(c_0_14, plain, ![X24, X25, X26, X27, X28, X29, X30, X31, X32]:k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32)=k2_xboole_0(k1_tarski(X24),k6_enumset1(X25,X26,X27,X28,X29,X30,X31,X32)), inference(variable_rename,[status(thm)],[t127_enumset1])).
% 0.19/0.50  fof(c_0_15, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.50  fof(c_0_16, plain, ![X18, X19, X20, X21, X22, X23]:k4_enumset1(X18,X19,X20,X21,X22,X23)=k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X21,X22,X23)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 0.19/0.50  fof(c_0_17, plain, ![X54, X55, X56]:k2_enumset1(X54,X54,X55,X56)=k1_enumset1(X54,X55,X56), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.50  fof(c_0_18, plain, ![X57, X58, X59, X60]:k3_enumset1(X57,X57,X58,X59,X60)=k2_enumset1(X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.50  fof(c_0_19, plain, ![X61, X62, X63, X64, X65]:k4_enumset1(X61,X61,X62,X63,X64,X65)=k3_enumset1(X61,X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.50  fof(c_0_20, plain, ![X66, X67, X68, X69, X70, X71]:k5_enumset1(X66,X66,X67,X68,X69,X70,X71)=k4_enumset1(X66,X67,X68,X69,X70,X71), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.50  fof(c_0_21, plain, ![X72, X73, X74, X75, X76, X77, X78]:k6_enumset1(X72,X72,X73,X74,X75,X76,X77,X78)=k5_enumset1(X72,X73,X74,X75,X76,X77,X78), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.50  fof(c_0_22, plain, ![X33, X34, X35, X36, X37, X38, X39, X40, X41]:k7_enumset1(X33,X34,X35,X36,X37,X38,X39,X40,X41)=k2_xboole_0(k3_enumset1(X33,X34,X35,X36,X37),k2_enumset1(X38,X39,X40,X41)), inference(variable_rename,[status(thm)],[t131_enumset1])).
% 0.19/0.50  cnf(c_0_23, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.50  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.50  fof(c_0_25, plain, ![X10, X11, X12]:k2_xboole_0(k2_xboole_0(X10,X11),X12)=k2_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.19/0.50  fof(c_0_26, plain, ![X48, X49, X50, X51, X52, X53]:k4_enumset1(X48,X49,X50,X51,X52,X53)=k2_xboole_0(k3_enumset1(X48,X49,X50,X51,X52),k1_tarski(X53)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.19/0.50  fof(c_0_27, plain, ![X42, X43, X44, X45, X46, X47]:k4_enumset1(X42,X43,X44,X45,X46,X47)=k2_xboole_0(k1_tarski(X42),k3_enumset1(X43,X44,X45,X46,X47)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.19/0.50  cnf(c_0_28, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.50  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.50  cnf(c_0_31, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.50  cnf(c_0_32, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.50  cnf(c_0_33, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.50  cnf(c_0_34, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.50  cnf(c_0_35, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.50  cnf(c_0_36, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.50  fof(c_0_37, plain, ![X13, X14, X15]:k5_xboole_0(k5_xboole_0(X13,X14),X15)=k5_xboole_0(X13,k5_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.50  cnf(c_0_38, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.50  cnf(c_0_39, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.50  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k4_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.19/0.50  cnf(c_0_41, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_tarski(X1)))=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_24]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_35])).
% 0.19/0.50  fof(c_0_42, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9))), inference(assume_negation,[status(cth)],[t132_enumset1])).
% 0.19/0.50  cnf(c_0_43, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.19/0.50  cnf(c_0_44, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.50  cnf(c_0_45, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k1_tarski(X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_24]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33])).
% 0.19/0.50  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X3,X4,X5,X6),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_24]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.50  cnf(c_0_47, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X4,X5,X6),k1_tarski(X1)))=k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.50  fof(c_0_48, negated_conjecture, k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.19/0.50  cnf(c_0_49, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.50  cnf(c_0_50, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k5_xboole_0(k4_xboole_0(k1_tarski(X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)),X7))=k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),X7)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.50  cnf(c_0_51, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.50  cnf(c_0_52, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.50  cnf(c_0_53, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(X7,k1_tarski(X6))),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))=k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(X7,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_45]), c_0_50])).
% 0.19/0.50  cnf(c_0_54, plain, (k6_enumset1(X1,X1,X1,X2,X2,X3,X4,X5)=k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_51]), c_0_45])).
% 0.19/0.50  cnf(c_0_55, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_tarski(esk1_0)))!=k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k4_xboole_0(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk8_0,esk9_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_24]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_35])).
% 0.19/0.50  cnf(c_0_56, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X7,X8,X9,X10,X11),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))=k5_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X8,X9,X10,X11),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)))), inference(spm,[status(thm)],[c_0_53, c_0_46])).
% 0.19/0.50  cnf(c_0_57, plain, (k6_enumset1(X1,X1,X1,X2,X2,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_51, c_0_54])).
% 0.19/0.50  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_41])]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 59
% 0.19/0.50  # Proof object clause steps            : 30
% 0.19/0.50  # Proof object formula steps           : 29
% 0.19/0.50  # Proof object conjectures             : 6
% 0.19/0.50  # Proof object clause conjectures      : 3
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 14
% 0.19/0.50  # Proof object initial formulas used   : 14
% 0.19/0.50  # Proof object generating inferences   : 6
% 0.19/0.50  # Proof object simplifying inferences  : 69
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 14
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 14
% 0.19/0.50  # Removed in clause preprocessing      : 7
% 0.19/0.50  # Initial clauses in saturation        : 7
% 0.19/0.50  # Processed clauses                    : 941
% 0.19/0.50  # ...of these trivial                  : 99
% 0.19/0.50  # ...subsumed                          : 719
% 0.19/0.50  # ...remaining for further processing  : 123
% 0.19/0.50  # Other redundant clauses eliminated   : 0
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 3
% 0.19/0.50  # Backward-rewritten                   : 8
% 0.19/0.50  # Generated clauses                    : 8388
% 0.19/0.50  # ...of the previous two non-trivial   : 6835
% 0.19/0.50  # Contextual simplify-reflections      : 0
% 0.19/0.50  # Paramodulations                      : 8388
% 0.19/0.50  # Factorizations                       : 0
% 0.19/0.50  # Equation resolutions                 : 0
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 105
% 0.19/0.50  #    Positive orientable unit clauses  : 73
% 0.19/0.50  #    Positive unorientable unit clauses: 32
% 0.19/0.50  #    Negative unit clauses             : 0
% 0.19/0.50  #    Non-unit-clauses                  : 0
% 0.19/0.50  # Current number of unprocessed clauses: 5848
% 0.19/0.50  # ...number of literals in the above   : 5848
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 25
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.50  # Unit Clause-clause subsumption calls : 750
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 1633
% 0.19/0.50  # BW rewrite match successes           : 342
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 279003
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.155 s
% 0.19/0.50  # System time              : 0.008 s
% 0.19/0.50  # Total time               : 0.163 s
% 0.19/0.50  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
