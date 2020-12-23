%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:14 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 299 expanded)
%              Number of clauses        :   29 ( 130 expanded)
%              Number of leaves         :   11 (  84 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 299 expanded)
%              Number of equality atoms :   51 ( 298 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t58_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(c_0_11,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_xboole_0(k1_tarski(X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_12,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(assume_negation,[status(cth)],[t58_enumset1])).

fof(c_0_14,plain,(
    ! [X27,X28,X29] : k1_enumset1(X27,X28,X29) = k2_xboole_0(k1_tarski(X27),k2_tarski(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k5_enumset1(X35,X36,X37,X38,X39,X40,X41) = k2_xboole_0(k1_tarski(X35),k4_enumset1(X36,X37,X38,X39,X40,X41)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

fof(c_0_18,plain,(
    ! [X13,X14,X15] : k2_xboole_0(k2_xboole_0(X13,X14),X15) = k2_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_19,plain,(
    ! [X10,X11,X12] : k4_xboole_0(k4_xboole_0(X10,X11),X12) = k4_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_20,plain,(
    ! [X30,X31,X32,X33,X34] : k3_enumset1(X30,X31,X32,X33,X34) = k2_xboole_0(k1_tarski(X30),k2_enumset1(X31,X32,X33,X34)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_21,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_26,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24] : k5_enumset1(X18,X19,X20,X21,X22,X23,X24) = k2_xboole_0(k2_enumset1(X18,X19,X20,X21),k1_enumset1(X22,X23,X24)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48] : k5_enumset1(X42,X43,X44,X45,X46,X47,X48) = k2_xboole_0(k2_tarski(X42,X43),k3_enumset1(X44,X45,X46,X47,X48)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_16]),c_0_23])).

cnf(c_0_33,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_16])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_16]),c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0))) != k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))),k4_xboole_0(k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_16]),c_0_32]),c_0_32]),c_0_33])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_16]),c_0_16])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_16]),c_0_32]),c_0_33])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X3,X1),X2)) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_16]),c_0_23]),c_0_23]),c_0_39]),c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0))) != k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)),k1_tarski(X6)),k1_tarski(X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_37]),c_0_37])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X1),X2),X3)) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_37]),c_0_37]),c_0_43]),c_0_37]),c_0_43])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_37]),c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k4_enumset1(esk5_0,esk6_0,esk7_0,esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0))) != k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X5),k4_xboole_0(k4_enumset1(X6,X7,X1,X2,X3,X4),k1_tarski(X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:21:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.47  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.47  #
% 0.21/0.47  # Preprocessing time       : 0.026 s
% 0.21/0.47  # Presaturation interreduction done
% 0.21/0.47  
% 0.21/0.47  # Proof found!
% 0.21/0.47  # SZS status Theorem
% 0.21/0.47  # SZS output start CNFRefutation
% 0.21/0.47  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.21/0.47  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.47  fof(t58_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 0.21/0.47  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.21/0.47  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 0.21/0.47  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.21/0.47  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.21/0.47  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.21/0.47  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.21/0.47  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 0.21/0.47  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 0.21/0.47  fof(c_0_11, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_xboole_0(k1_tarski(X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.21/0.47  fof(c_0_12, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.47  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(assume_negation,[status(cth)],[t58_enumset1])).
% 0.21/0.47  fof(c_0_14, plain, ![X27, X28, X29]:k1_enumset1(X27,X28,X29)=k2_xboole_0(k1_tarski(X27),k2_tarski(X28,X29)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.21/0.47  cnf(c_0_15, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.47  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.47  fof(c_0_17, plain, ![X35, X36, X37, X38, X39, X40, X41]:k5_enumset1(X35,X36,X37,X38,X39,X40,X41)=k2_xboole_0(k1_tarski(X35),k4_enumset1(X36,X37,X38,X39,X40,X41)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 0.21/0.47  fof(c_0_18, plain, ![X13, X14, X15]:k2_xboole_0(k2_xboole_0(X13,X14),X15)=k2_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.21/0.47  fof(c_0_19, plain, ![X10, X11, X12]:k4_xboole_0(k4_xboole_0(X10,X11),X12)=k4_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.21/0.47  fof(c_0_20, plain, ![X30, X31, X32, X33, X34]:k3_enumset1(X30,X31,X32,X33,X34)=k2_xboole_0(k1_tarski(X30),k2_enumset1(X31,X32,X33,X34)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.21/0.47  fof(c_0_21, negated_conjecture, k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.21/0.47  cnf(c_0_22, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.47  cnf(c_0_23, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.47  cnf(c_0_24, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.47  fof(c_0_25, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k2_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.21/0.47  fof(c_0_26, plain, ![X18, X19, X20, X21, X22, X23, X24]:k5_enumset1(X18,X19,X20,X21,X22,X23,X24)=k2_xboole_0(k2_enumset1(X18,X19,X20,X21),k1_enumset1(X22,X23,X24)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.21/0.47  cnf(c_0_27, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.47  cnf(c_0_28, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.47  fof(c_0_29, plain, ![X42, X43, X44, X45, X46, X47, X48]:k5_enumset1(X42,X43,X44,X45,X46,X47,X48)=k2_xboole_0(k2_tarski(X42,X43),k3_enumset1(X44,X45,X46,X47,X48)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 0.21/0.47  cnf(c_0_30, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.47  cnf(c_0_31, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.47  cnf(c_0_32, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_16]), c_0_23])).
% 0.21/0.47  cnf(c_0_33, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_24, c_0_16])).
% 0.21/0.47  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.47  cnf(c_0_35, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.47  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_16]), c_0_16]), c_0_16]), c_0_16])).
% 0.21/0.47  cnf(c_0_37, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_16])).
% 0.21/0.47  cnf(c_0_38, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.47  cnf(c_0_39, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_30, c_0_16])).
% 0.21/0.47  cnf(c_0_40, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0)))!=k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))),k4_xboole_0(k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk2_0))),k1_tarski(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_16]), c_0_32]), c_0_32]), c_0_33])).
% 0.21/0.47  cnf(c_0_41, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_16]), c_0_16])).
% 0.21/0.47  cnf(c_0_42, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_16]), c_0_32]), c_0_33])).
% 0.21/0.47  cnf(c_0_43, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X3,X1),X2))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.47  cnf(c_0_44, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_16]), c_0_23]), c_0_23]), c_0_39]), c_0_33])).
% 0.21/0.47  cnf(c_0_45, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)))!=k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0)))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.47  cnf(c_0_46, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))=k5_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)),k1_tarski(X6)),k1_tarski(X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_37]), c_0_37])).
% 0.21/0.47  cnf(c_0_47, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X1),X2),X3))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_37]), c_0_37]), c_0_43]), c_0_37]), c_0_43])).
% 0.21/0.47  cnf(c_0_48, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_37]), c_0_43])).
% 0.21/0.47  cnf(c_0_49, negated_conjecture, (k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k4_enumset1(esk5_0,esk6_0,esk7_0,esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0)))!=k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0)))), inference(rw,[status(thm)],[c_0_45, c_0_42])).
% 0.21/0.47  cnf(c_0_50, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X5),k4_xboole_0(k4_enumset1(X6,X7,X1,X2,X3,X4),k1_tarski(X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.21/0.47  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])]), ['proof']).
% 0.21/0.47  # SZS output end CNFRefutation
% 0.21/0.47  # Proof object total steps             : 52
% 0.21/0.47  # Proof object clause steps            : 29
% 0.21/0.47  # Proof object formula steps           : 23
% 0.21/0.47  # Proof object conjectures             : 8
% 0.21/0.47  # Proof object clause conjectures      : 5
% 0.21/0.47  # Proof object formula conjectures     : 3
% 0.21/0.47  # Proof object initial clauses used    : 11
% 0.21/0.47  # Proof object initial formulas used   : 11
% 0.21/0.47  # Proof object generating inferences   : 2
% 0.21/0.47  # Proof object simplifying inferences  : 39
% 0.21/0.47  # Training examples: 0 positive, 0 negative
% 0.21/0.47  # Parsed axioms                        : 11
% 0.21/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.47  # Initial clauses                      : 11
% 0.21/0.47  # Removed in clause preprocessing      : 5
% 0.21/0.47  # Initial clauses in saturation        : 6
% 0.21/0.47  # Processed clauses                    : 457
% 0.21/0.47  # ...of these trivial                  : 8
% 0.21/0.47  # ...subsumed                          : 397
% 0.21/0.47  # ...remaining for further processing  : 52
% 0.21/0.47  # Other redundant clauses eliminated   : 0
% 0.21/0.47  # Clauses deleted for lack of memory   : 0
% 0.21/0.47  # Backward-subsumed                    : 0
% 0.21/0.47  # Backward-rewritten                   : 4
% 0.21/0.47  # Generated clauses                    : 8545
% 0.21/0.47  # ...of the previous two non-trivial   : 8442
% 0.21/0.47  # Contextual simplify-reflections      : 0
% 0.21/0.47  # Paramodulations                      : 8545
% 0.21/0.47  # Factorizations                       : 0
% 0.21/0.47  # Equation resolutions                 : 0
% 0.21/0.47  # Propositional unsat checks           : 0
% 0.21/0.47  #    Propositional check models        : 0
% 0.21/0.47  #    Propositional check unsatisfiable : 0
% 0.21/0.47  #    Propositional clauses             : 0
% 0.21/0.47  #    Propositional clauses after purity: 0
% 0.21/0.47  #    Propositional unsat core size     : 0
% 0.21/0.47  #    Propositional preprocessing time  : 0.000
% 0.21/0.47  #    Propositional encoding time       : 0.000
% 0.21/0.47  #    Propositional solver time         : 0.000
% 0.21/0.47  #    Success case prop preproc time    : 0.000
% 0.21/0.47  #    Success case prop encoding time   : 0.000
% 0.21/0.47  #    Success case prop solver time     : 0.000
% 0.21/0.47  # Current number of processed clauses  : 42
% 0.21/0.47  #    Positive orientable unit clauses  : 15
% 0.21/0.47  #    Positive unorientable unit clauses: 27
% 0.21/0.47  #    Negative unit clauses             : 0
% 0.21/0.47  #    Non-unit-clauses                  : 0
% 0.21/0.47  # Current number of unprocessed clauses: 7997
% 0.21/0.47  # ...number of literals in the above   : 7997
% 0.21/0.47  # Current number of archived formulas  : 0
% 0.21/0.47  # Current number of archived clauses   : 15
% 0.21/0.47  # Clause-clause subsumption calls (NU) : 0
% 0.21/0.47  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.47  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.47  # Unit Clause-clause subsumption calls : 94
% 0.21/0.47  # Rewrite failures with RHS unbound    : 0
% 0.21/0.47  # BW rewrite match attempts            : 717
% 0.21/0.47  # BW rewrite match successes           : 189
% 0.21/0.47  # Condensation attempts                : 0
% 0.21/0.47  # Condensation successes               : 0
% 0.21/0.47  # Termbank termtop insertions          : 138619
% 0.21/0.47  
% 0.21/0.47  # -------------------------------------------------
% 0.21/0.47  # User time                : 0.118 s
% 0.21/0.47  # System time              : 0.013 s
% 0.21/0.47  # Total time               : 0.131 s
% 0.21/0.47  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
