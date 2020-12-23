%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0867+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:55 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   28 ( 106 expanded)
%              Number of clauses        :   11 (  37 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 ( 106 expanded)
%              Number of equality atoms :   27 ( 105 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_mcart_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t146_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(assume_negation,[status(cth)],[t25_mcart_1])).

fof(c_0_9,negated_conjecture,(
    k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X839,X840] : k1_enumset1(X839,X839,X840) = k2_tarski(X839,X840) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X191,X192,X193] : k2_enumset1(X191,X191,X192,X193) = k1_enumset1(X191,X192,X193) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_12,plain,(
    ! [X194,X195,X196,X197] : k3_enumset1(X194,X194,X195,X196,X197) = k2_enumset1(X194,X195,X196,X197) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_13,plain,(
    ! [X1232,X1233,X1234,X1235,X1236] : k4_enumset1(X1232,X1232,X1233,X1234,X1235,X1236) = k3_enumset1(X1232,X1233,X1234,X1235,X1236) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_14,plain,(
    ! [X1446,X1447,X1448,X1449,X1450,X1451] : k5_enumset1(X1446,X1446,X1447,X1448,X1449,X1450,X1451) = k4_enumset1(X1446,X1447,X1448,X1449,X1450,X1451) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_15,plain,(
    ! [X1452,X1453,X1454,X1455,X1456,X1457,X1458] : k6_enumset1(X1452,X1452,X1453,X1454,X1455,X1456,X1457,X1458) = k5_enumset1(X1452,X1453,X1454,X1455,X1456,X1457,X1458) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_16,plain,(
    ! [X213,X214,X215,X216] : k2_zfmisc_1(k2_tarski(X213,X214),k2_tarski(X215,X216)) = k2_enumset1(k4_tarski(X213,X215),k4_tarski(X213,X216),k4_tarski(X214,X215),k4_tarski(X214,X216)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

cnf(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) != k6_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)) = k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
