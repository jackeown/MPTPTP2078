%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:22 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 324 expanded)
%              Number of clauses        :   30 ( 139 expanded)
%              Number of leaves         :   12 (  92 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 ( 324 expanded)
%              Number of equality atoms :   54 ( 323 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t63_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t113_xboole_1,axiom,(
    ! [X1,X2,X3,X4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(c_0_12,plain,(
    ! [X38,X39,X40,X41,X42] : k3_enumset1(X38,X39,X40,X41,X42) = k2_xboole_0(k1_tarski(X38),k2_enumset1(X39,X40,X41,X42)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_13,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X20) = k5_xboole_0(X19,k4_xboole_0(X20,X19)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_14,plain,(
    ! [X29,X30] : k2_tarski(X29,X30) = k2_xboole_0(k1_tarski(X29),k1_tarski(X30)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(assume_negation,[status(cth)],[t63_enumset1])).

fof(c_0_16,plain,(
    ! [X43,X44,X45,X46,X47,X48] : k4_enumset1(X43,X44,X45,X46,X47,X48) = k2_xboole_0(k1_tarski(X43),k3_enumset1(X44,X45,X46,X47,X48)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_17,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X49,X50,X51,X52,X53,X54,X55,X56] : k6_enumset1(X49,X50,X51,X52,X53,X54,X55,X56) = k2_xboole_0(k1_tarski(X49),k5_enumset1(X50,X51,X52,X53,X54,X55,X56)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

fof(c_0_20,plain,(
    ! [X16,X17,X18] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_21,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_22,plain,(
    ! [X31,X32,X33] : k1_enumset1(X31,X32,X33) = k2_xboole_0(k1_tarski(X31),k2_tarski(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k4_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X9,X10,X11,X12] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X9,X10),X11),X12) = k2_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) ),
    inference(variable_rename,[status(thm)],[t113_xboole_1])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X34,X35,X36,X37] : k2_enumset1(X34,X35,X36,X37) = k2_xboole_0(k1_tarski(X34),k1_enumset1(X35,X36,X37)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k4_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_18]),c_0_26])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_18]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_18])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_18]),c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))) != k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0))),k4_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk4_0))),k1_tarski(esk3_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_18]),c_0_33]),c_0_33]),c_0_35]),c_0_36])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))),k4_xboole_0(X4,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X4,k5_xboole_0(X2,k4_xboole_0(X3,X2)))),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_18]),c_0_18]),c_0_18]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X3,X1),X2)) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_18]),c_0_41])).

fof(c_0_46,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] : k6_enumset1(X21,X22,X23,X24,X25,X26,X27,X28) = k2_xboole_0(k2_enumset1(X21,X22,X23,X24),k2_enumset1(X25,X26,X27,X28)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk4_0))),k1_tarski(esk3_0))),k1_tarski(esk1_0)),k1_tarski(esk2_0))) != k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X1),X2),X3)) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_39]),c_0_44]),c_0_39]),c_0_44]),c_0_39]),c_0_39]),c_0_39]),c_0_44])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)) = k4_xboole_0(X1,k2_enumset1(X2,X3,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_45]),c_0_39]),c_0_39])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk4_0))),k1_tarski(esk3_0))),k1_tarski(esk2_0))),k1_tarski(esk1_0))) != k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_44])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_45]),c_0_39]),c_0_49]),c_0_39]),c_0_44])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_18]),c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.13/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.13/0.38  fof(t63_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 0.13/0.38  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 0.13/0.38  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 0.13/0.38  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.13/0.38  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.13/0.38  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.13/0.38  fof(t113_xboole_1, axiom, ![X1, X2, X3, X4]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_xboole_1)).
% 0.13/0.38  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.13/0.38  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 0.13/0.38  fof(c_0_12, plain, ![X38, X39, X40, X41, X42]:k3_enumset1(X38,X39,X40,X41,X42)=k2_xboole_0(k1_tarski(X38),k2_enumset1(X39,X40,X41,X42)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.13/0.38  fof(c_0_13, plain, ![X19, X20]:k2_xboole_0(X19,X20)=k5_xboole_0(X19,k4_xboole_0(X20,X19)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X29, X30]:k2_tarski(X29,X30)=k2_xboole_0(k1_tarski(X29),k1_tarski(X30)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(assume_negation,[status(cth)],[t63_enumset1])).
% 0.13/0.38  fof(c_0_16, plain, ![X43, X44, X45, X46, X47, X48]:k4_enumset1(X43,X44,X45,X46,X47,X48)=k2_xboole_0(k1_tarski(X43),k3_enumset1(X44,X45,X46,X47,X48)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.13/0.38  cnf(c_0_17, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_19, plain, ![X49, X50, X51, X52, X53, X54, X55, X56]:k6_enumset1(X49,X50,X51,X52,X53,X54,X55,X56)=k2_xboole_0(k1_tarski(X49),k5_enumset1(X50,X51,X52,X53,X54,X55,X56)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.13/0.38  fof(c_0_20, plain, ![X16, X17, X18]:k2_xboole_0(k2_xboole_0(X16,X17),X18)=k2_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.13/0.38  fof(c_0_21, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.13/0.38  fof(c_0_22, plain, ![X31, X32, X33]:k1_enumset1(X31,X32,X33)=k2_xboole_0(k1_tarski(X31),k2_tarski(X32,X33)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.13/0.38  cnf(c_0_23, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_24, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k4_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.13/0.38  cnf(c_0_25, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_27, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_28, plain, ![X9, X10, X11, X12]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X9,X10),X11),X12)=k2_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)), inference(variable_rename,[status(thm)],[t113_xboole_1])).
% 0.13/0.38  cnf(c_0_29, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_31, plain, ![X34, X35, X36, X37]:k2_enumset1(X34,X35,X36,X37)=k2_xboole_0(k1_tarski(X34),k1_enumset1(X35,X36,X37)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.13/0.38  cnf(c_0_32, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_33, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_23, c_0_18])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k4_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_35, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_18]), c_0_26])).
% 0.13/0.38  cnf(c_0_36, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_27, c_0_18])).
% 0.13/0.38  cnf(c_0_37, plain, (k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_38, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 0.13/0.38  cnf(c_0_39, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_30, c_0_18])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_41, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_18]), c_0_33])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))!=k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0))),k4_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk4_0))),k1_tarski(esk3_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_18]), c_0_33]), c_0_33]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_43, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))),k4_xboole_0(X4,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X4,k5_xboole_0(X2,k4_xboole_0(X3,X2)))),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_18]), c_0_18]), c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 0.13/0.38  cnf(c_0_44, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X3,X1),X2))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_45, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_18]), c_0_41])).
% 0.13/0.38  fof(c_0_46, plain, ![X21, X22, X23, X24, X25, X26, X27, X28]:k6_enumset1(X21,X22,X23,X24,X25,X26,X27,X28)=k2_xboole_0(k2_enumset1(X21,X22,X23,X24),k2_enumset1(X25,X26,X27,X28)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk4_0))),k1_tarski(esk3_0))),k1_tarski(esk1_0)),k1_tarski(esk2_0)))!=k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))), inference(rw,[status(thm)],[c_0_42, c_0_39])).
% 0.13/0.38  cnf(c_0_48, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X1),X2),X3))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_39]), c_0_44]), c_0_39]), c_0_44]), c_0_39]), c_0_39]), c_0_39]), c_0_44])).
% 0.13/0.38  cnf(c_0_49, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5))=k4_xboole_0(X1,k2_enumset1(X2,X3,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_45]), c_0_39]), c_0_39])).
% 0.13/0.38  cnf(c_0_50, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk4_0))),k1_tarski(esk3_0))),k1_tarski(esk2_0))),k1_tarski(esk1_0)))!=k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))), inference(rw,[status(thm)],[c_0_47, c_0_44])).
% 0.13/0.38  cnf(c_0_52, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_45]), c_0_39]), c_0_49]), c_0_39]), c_0_44])).
% 0.13/0.38  cnf(c_0_53, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_18]), c_0_36])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 55
% 0.13/0.38  # Proof object clause steps            : 30
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 8
% 0.13/0.38  # Proof object clause conjectures      : 5
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 2
% 0.13/0.38  # Proof object simplifying inferences  : 47
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 12
% 0.13/0.38  # Removed in clause preprocessing      : 6
% 0.13/0.38  # Initial clauses in saturation        : 6
% 0.13/0.38  # Processed clauses                    : 24
% 0.13/0.38  # ...of these trivial                  : 5
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 19
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 93
% 0.13/0.38  # ...of the previous two non-trivial   : 76
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 93
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 11
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 0
% 0.13/0.38  # Current number of unprocessed clauses: 64
% 0.13/0.38  # ...number of literals in the above   : 64
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 14
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 13
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4088
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
