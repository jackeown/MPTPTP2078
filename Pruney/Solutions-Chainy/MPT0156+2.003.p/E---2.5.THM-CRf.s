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
% DateTime   : Thu Dec  3 10:35:41 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 641 expanded)
%              Number of clauses        :   30 ( 252 expanded)
%              Number of leaves         :   13 ( 194 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 641 expanded)
%              Number of equality atoms :   56 ( 640 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

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

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(t72_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(c_0_13,plain,(
    ! [X31,X32,X33,X34,X35] : k3_enumset1(X31,X32,X33,X34,X35) = k2_xboole_0(k1_tarski(X31),k2_enumset1(X32,X33,X34,X35)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_14,plain,(
    ! [X57] : k2_tarski(X57,X57) = k1_tarski(X57) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X58,X59] : k1_enumset1(X58,X58,X59) = k2_tarski(X58,X59) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k5_xboole_0(X12,k4_xboole_0(X13,X12)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_17,plain,(
    ! [X60,X61,X62] : k2_enumset1(X60,X60,X61,X62) = k1_enumset1(X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48] : k5_enumset1(X42,X43,X44,X45,X46,X47,X48) = k2_xboole_0(k1_enumset1(X42,X43,X44),k2_enumset1(X45,X46,X47,X48)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

fof(c_0_19,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30] : k6_enumset1(X23,X24,X25,X26,X27,X28,X29,X30) = k2_xboole_0(k2_enumset1(X23,X24,X25,X26),k2_enumset1(X27,X28,X29,X30)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_20,plain,(
    ! [X36,X37,X38,X39,X40,X41] : k4_enumset1(X36,X37,X38,X39,X40,X41) = k2_xboole_0(k3_enumset1(X36,X37,X38,X39,X40),k1_tarski(X41)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X9,X10,X11] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_27,plain,(
    ! [X49,X50,X51,X52,X53,X54,X55,X56] : k6_enumset1(X49,X50,X51,X52,X53,X54,X55,X56) = k2_xboole_0(k5_enumset1(X49,X50,X51,X52,X53,X54,X55),k1_tarski(X56)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

cnf(c_0_28,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X1,X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_24])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(assume_negation,[status(cth)],[t72_enumset1])).

fof(c_0_37,plain,(
    ! [X18,X19,X20,X21,X22] : k3_enumset1(X18,X19,X20,X21,X22) = k2_xboole_0(k1_enumset1(X18,X19,X20),k2_tarski(X21,X22)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1))),k4_xboole_0(k2_enumset1(X6,X6,X6,X6),k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_31]),c_0_31])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X1,X1,X2,X3))),k4_xboole_0(k2_enumset1(X8,X8,X8,X8),k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X1,X1,X2,X3))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_34]),c_0_34]),c_0_35])).

fof(c_0_41,plain,(
    ! [X14,X15,X16,X17] : k2_enumset1(X14,X15,X16,X17) = k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_42,negated_conjecture,(
    k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X3,X4,X5),k4_xboole_0(k2_enumset1(X6,X6,X6,X6),k2_enumset1(X2,X3,X4,X5))),k2_enumset1(X1,X1,X1,X1))) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k5_xboole_0(k2_enumset1(X4,X5,X6,X7),k4_xboole_0(k2_enumset1(X8,X8,X8,X8),k2_enumset1(X4,X5,X6,X7))),k2_enumset1(X1,X1,X2,X3))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1))) = k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X4,X5),k2_enumset1(X1,X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_23]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_31])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_enumset1(X1,X1,X1,X2))) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_23]),c_0_23]),c_0_24]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_31])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X4,X5),k2_enumset1(X1,X1,X2,X3))) = k4_enumset1(X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( k4_enumset1(X1,X2,X3,X3,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_49])).

cnf(c_0_55,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_52]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 0.13/0.37  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 0.13/0.37  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.13/0.37  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.13/0.37  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 0.13/0.37  fof(t72_enumset1, conjecture, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 0.13/0.37  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.13/0.37  fof(c_0_13, plain, ![X31, X32, X33, X34, X35]:k3_enumset1(X31,X32,X33,X34,X35)=k2_xboole_0(k1_tarski(X31),k2_enumset1(X32,X33,X34,X35)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.13/0.37  fof(c_0_14, plain, ![X57]:k2_tarski(X57,X57)=k1_tarski(X57), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  fof(c_0_15, plain, ![X58, X59]:k1_enumset1(X58,X58,X59)=k2_tarski(X58,X59), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_16, plain, ![X12, X13]:k2_xboole_0(X12,X13)=k5_xboole_0(X12,k4_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.37  fof(c_0_17, plain, ![X60, X61, X62]:k2_enumset1(X60,X60,X61,X62)=k1_enumset1(X60,X61,X62), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_18, plain, ![X42, X43, X44, X45, X46, X47, X48]:k5_enumset1(X42,X43,X44,X45,X46,X47,X48)=k2_xboole_0(k1_enumset1(X42,X43,X44),k2_enumset1(X45,X46,X47,X48)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 0.13/0.37  fof(c_0_19, plain, ![X23, X24, X25, X26, X27, X28, X29, X30]:k6_enumset1(X23,X24,X25,X26,X27,X28,X29,X30)=k2_xboole_0(k2_enumset1(X23,X24,X25,X26),k2_enumset1(X27,X28,X29,X30)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.13/0.37  fof(c_0_20, plain, ![X36, X37, X38, X39, X40, X41]:k4_enumset1(X36,X37,X38,X39,X40,X41)=k2_xboole_0(k3_enumset1(X36,X37,X38,X39,X40),k1_tarski(X41)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.13/0.37  cnf(c_0_21, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  fof(c_0_26, plain, ![X9, X10, X11]:k2_xboole_0(k2_xboole_0(X9,X10),X11)=k2_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.13/0.37  fof(c_0_27, plain, ![X49, X50, X51, X52, X53, X54, X55, X56]:k6_enumset1(X49,X50,X51,X52,X53,X54,X55,X56)=k2_xboole_0(k5_enumset1(X49,X50,X51,X52,X53,X54,X55),k1_tarski(X56)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 0.13/0.37  cnf(c_0_28, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_29, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_30, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_31, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_25])).
% 0.13/0.37  cnf(c_0_32, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_33, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_34, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X1,X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_25]), c_0_25])).
% 0.13/0.37  cnf(c_0_35, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[c_0_29, c_0_24])).
% 0.13/0.37  fof(c_0_36, negated_conjecture, ~(![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(assume_negation,[status(cth)],[t72_enumset1])).
% 0.13/0.37  fof(c_0_37, plain, ![X18, X19, X20, X21, X22]:k3_enumset1(X18,X19,X20,X21,X22)=k2_xboole_0(k1_enumset1(X18,X19,X20),k2_tarski(X21,X22)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.13/0.37  cnf(c_0_38, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1))),k4_xboole_0(k2_enumset1(X6,X6,X6,X6),k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_31]), c_0_31])).
% 0.13/0.37  cnf(c_0_39, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.13/0.37  cnf(c_0_40, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X1,X1,X2,X3))),k4_xboole_0(k2_enumset1(X8,X8,X8,X8),k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X1,X1,X2,X3)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_34]), c_0_34]), c_0_35])).
% 0.13/0.37  fof(c_0_41, plain, ![X14, X15, X16, X17]:k2_enumset1(X14,X15,X16,X17)=k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.13/0.37  fof(c_0_42, negated_conjecture, k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.13/0.37  cnf(c_0_43, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_44, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X3,X4,X5),k4_xboole_0(k2_enumset1(X6,X6,X6,X6),k2_enumset1(X2,X3,X4,X5))),k2_enumset1(X1,X1,X1,X1)))=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.37  cnf(c_0_45, plain, (k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k5_xboole_0(k2_enumset1(X4,X5,X6,X7),k4_xboole_0(k2_enumset1(X8,X8,X8,X8),k2_enumset1(X4,X5,X6,X7))),k2_enumset1(X1,X1,X2,X3)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[c_0_40, c_0_39])).
% 0.13/0.37  cnf(c_0_46, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.37  cnf(c_0_48, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X1,X1,X1,X1)))=k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X4,X5),k2_enumset1(X1,X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_23]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_31])).
% 0.13/0.37  cnf(c_0_49, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_enumset1(X1,X1,X1,X2)))=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.37  cnf(c_0_50, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_23]), c_0_23]), c_0_24]), c_0_25]), c_0_25]), c_0_25])).
% 0.13/0.37  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_47, c_0_31])).
% 0.13/0.37  cnf(c_0_52, plain, (k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X4,X5),k2_enumset1(X1,X1,X2,X3)))=k4_enumset1(X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.37  cnf(c_0_53, plain, (k4_enumset1(X1,X2,X3,X3,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_50, c_0_49])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_51, c_0_49])).
% 0.13/0.37  cnf(c_0_55, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_52]), c_0_53])).
% 0.13/0.37  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 57
% 0.13/0.37  # Proof object clause steps            : 30
% 0.13/0.37  # Proof object formula steps           : 27
% 0.13/0.37  # Proof object conjectures             : 7
% 0.13/0.37  # Proof object clause conjectures      : 4
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 13
% 0.13/0.37  # Proof object generating inferences   : 1
% 0.13/0.37  # Proof object simplifying inferences  : 48
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 13
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 13
% 0.13/0.37  # Removed in clause preprocessing      : 7
% 0.13/0.37  # Initial clauses in saturation        : 6
% 0.13/0.37  # Processed clauses                    : 16
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 16
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 5
% 0.13/0.37  # Generated clauses                    : 4
% 0.13/0.37  # ...of the previous two non-trivial   : 7
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 4
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 5
% 0.13/0.37  #    Positive orientable unit clauses  : 5
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 0
% 0.13/0.37  # Current number of unprocessed clauses: 3
% 0.13/0.37  # ...number of literals in the above   : 3
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 18
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 23
% 0.13/0.37  # BW rewrite match successes           : 7
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1099
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.030 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
