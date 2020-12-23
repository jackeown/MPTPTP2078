%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:27 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 482 expanded)
%              Number of clauses        :   28 ( 203 expanded)
%              Number of leaves         :   11 ( 139 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 ( 482 expanded)
%              Number of equality atoms :   50 ( 481 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t67_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(c_0_11,plain,(
    ! [X17,X18] : k2_tarski(X17,X18) = k2_xboole_0(k1_tarski(X17),k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_12,plain,(
    ! [X15,X16] : k2_xboole_0(X15,X16) = k5_xboole_0(X15,k4_xboole_0(X16,X15)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_13,plain,(
    ! [X26,X27,X28,X29,X30] : k3_enumset1(X26,X27,X28,X29,X30) = k2_xboole_0(k1_tarski(X26),k2_enumset1(X27,X28,X29,X30)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_14,plain,(
    ! [X19,X20,X21] : k1_enumset1(X19,X20,X21) = k2_xboole_0(k1_tarski(X19),k2_tarski(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(assume_negation,[status(cth)],[t67_enumset1])).

fof(c_0_18,plain,(
    ! [X31,X32,X33,X34,X35,X36] : k4_enumset1(X31,X32,X33,X34,X35,X36) = k2_xboole_0(k1_tarski(X31),k3_enumset1(X32,X33,X34,X35,X36)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_19,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50,X51] : k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51) = k2_xboole_0(k1_tarski(X44),k5_enumset1(X45,X46,X47,X48,X49,X50,X51)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

fof(c_0_21,plain,(
    ! [X9,X10,X11] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_22,plain,(
    ! [X22,X23,X24,X25] : k2_enumset1(X22,X23,X24,X25) = k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_25,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_28,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X12,X13,X14] : k5_xboole_0(k5_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_16]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_16]),c_0_27])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_16]),c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_16]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))) != k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_16]),c_0_24]),c_0_34]),c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)),X5)) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),X5) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43] : k5_enumset1(X37,X38,X39,X40,X41,X42,X43) = k2_xboole_0(k1_tarski(X37),k4_enumset1(X38,X39,X40,X41,X42,X43)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

cnf(c_0_43,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0)),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0)))))) != k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_38]),c_0_37]),c_0_40]),c_0_37]),c_0_40])).

cnf(c_0_45,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k5_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))),k1_tarski(esk2_0))),k1_tarski(esk1_0))) != k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_40]),c_0_37]),c_0_40])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(X6,k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X3,X4,X5),k4_xboole_0(X6,k2_enumset1(X2,X3,X4,X5))),k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_44])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_49,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_16]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:00:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.14/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.026 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.14/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.14/0.38  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.14/0.38  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.14/0.38  fof(t67_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 0.14/0.38  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 0.14/0.38  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 0.14/0.38  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.14/0.38  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.14/0.38  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.14/0.38  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 0.14/0.38  fof(c_0_11, plain, ![X17, X18]:k2_tarski(X17,X18)=k2_xboole_0(k1_tarski(X17),k1_tarski(X18)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.14/0.38  fof(c_0_12, plain, ![X15, X16]:k2_xboole_0(X15,X16)=k5_xboole_0(X15,k4_xboole_0(X16,X15)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.14/0.38  fof(c_0_13, plain, ![X26, X27, X28, X29, X30]:k3_enumset1(X26,X27,X28,X29,X30)=k2_xboole_0(k1_tarski(X26),k2_enumset1(X27,X28,X29,X30)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.14/0.38  fof(c_0_14, plain, ![X19, X20, X21]:k1_enumset1(X19,X20,X21)=k2_xboole_0(k1_tarski(X19),k2_tarski(X20,X21)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.14/0.38  cnf(c_0_15, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(assume_negation,[status(cth)],[t67_enumset1])).
% 0.14/0.38  fof(c_0_18, plain, ![X31, X32, X33, X34, X35, X36]:k4_enumset1(X31,X32,X33,X34,X35,X36)=k2_xboole_0(k1_tarski(X31),k3_enumset1(X32,X33,X34,X35,X36)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.14/0.38  cnf(c_0_19, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_20, plain, ![X44, X45, X46, X47, X48, X49, X50, X51]:k6_enumset1(X44,X45,X46,X47,X48,X49,X50,X51)=k2_xboole_0(k1_tarski(X44),k5_enumset1(X45,X46,X47,X48,X49,X50,X51)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.14/0.38  fof(c_0_21, plain, ![X9, X10, X11]:k2_xboole_0(k2_xboole_0(X9,X10),X11)=k2_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.14/0.38  fof(c_0_22, plain, ![X22, X23, X24, X25]:k2_enumset1(X22,X23,X24,X25)=k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.14/0.38  cnf(c_0_23, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_24, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.38  fof(c_0_25, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.14/0.38  cnf(c_0_26, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_27, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_19, c_0_16])).
% 0.14/0.38  cnf(c_0_28, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_29, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  fof(c_0_30, plain, ![X12, X13, X14]:k5_xboole_0(k5_xboole_0(X12,X13),X14)=k5_xboole_0(X12,k5_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.14/0.38  cnf(c_0_31, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_32, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_16]), c_0_24])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_34, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_16]), c_0_27])).
% 0.14/0.38  cnf(c_0_35, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_28, c_0_16])).
% 0.14/0.38  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_16]), c_0_16]), c_0_16]), c_0_16])).
% 0.14/0.38  cnf(c_0_37, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_38, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_16]), c_0_32])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))!=k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_16]), c_0_24]), c_0_34]), c_0_34]), c_0_35])).
% 0.14/0.38  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.38  cnf(c_0_41, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)),X5))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.38  fof(c_0_42, plain, ![X37, X38, X39, X40, X41, X42, X43]:k5_enumset1(X37,X38,X39,X40,X41,X42,X43)=k2_xboole_0(k1_tarski(X37),k4_enumset1(X38,X39,X40,X41,X42,X43)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0)),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))))))!=k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))), inference(rw,[status(thm)],[c_0_39, c_0_37])).
% 0.14/0.38  cnf(c_0_44, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_38]), c_0_37]), c_0_40]), c_0_37]), c_0_40])).
% 0.14/0.38  cnf(c_0_45, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k5_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))),k1_tarski(esk2_0))),k1_tarski(esk1_0)))!=k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_40]), c_0_37]), c_0_40])).
% 0.14/0.38  cnf(c_0_47, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(X6,k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X3,X4,X5),k4_xboole_0(X6,k2_enumset1(X2,X3,X4,X5))),k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_44, c_0_44])).
% 0.14/0.38  cnf(c_0_48, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 0.14/0.38  cnf(c_0_49, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_16]), c_0_34])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 51
% 0.14/0.38  # Proof object clause steps            : 28
% 0.14/0.38  # Proof object formula steps           : 23
% 0.14/0.38  # Proof object conjectures             : 8
% 0.14/0.38  # Proof object clause conjectures      : 5
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 11
% 0.14/0.38  # Proof object initial formulas used   : 11
% 0.14/0.38  # Proof object generating inferences   : 4
% 0.14/0.38  # Proof object simplifying inferences  : 34
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 11
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 11
% 0.14/0.38  # Removed in clause preprocessing      : 6
% 0.14/0.38  # Initial clauses in saturation        : 5
% 0.14/0.38  # Processed clauses                    : 22
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 21
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 2
% 0.14/0.38  # Generated clauses                    : 106
% 0.14/0.38  # ...of the previous two non-trivial   : 70
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 106
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 14
% 0.14/0.38  #    Positive orientable unit clauses  : 14
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 0
% 0.14/0.38  # Current number of unprocessed clauses: 58
% 0.14/0.38  # ...number of literals in the above   : 58
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 13
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 23
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 5952
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.031 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
