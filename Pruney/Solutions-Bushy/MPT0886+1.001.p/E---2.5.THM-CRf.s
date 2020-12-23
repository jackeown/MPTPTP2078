%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0886+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:21 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   31 (  88 expanded)
%              Number of clauses        :   14 (  35 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  90 expanded)
%              Number of equality atoms :   32 (  89 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k2_tarski(X5,X6)) = k6_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X1,X3,X6),k3_mcart_1(X1,X4,X6),k3_mcart_1(X2,X3,X5),k3_mcart_1(X2,X4,X5),k3_mcart_1(X2,X3,X6),k3_mcart_1(X2,X4,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_mcart_1)).

fof(t65_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_enumset1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t104_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

fof(t25_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_mcart_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k2_tarski(X5,X6)) = k6_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X1,X3,X6),k3_mcart_1(X1,X4,X6),k3_mcart_1(X2,X3,X5),k3_mcart_1(X2,X4,X5),k3_mcart_1(X2,X3,X6),k3_mcart_1(X2,X4,X6)) ),
    inference(assume_negation,[status(cth)],[t46_mcart_1])).

fof(c_0_9,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] : k6_enumset1(X30,X31,X32,X33,X34,X35,X36,X37) = k2_xboole_0(k2_enumset1(X30,X31,X32,X33),k2_enumset1(X34,X35,X36,X37)) ),
    inference(variable_rename,[status(thm)],[t65_enumset1])).

fof(c_0_10,plain,(
    ! [X26,X27,X28,X29] : k2_enumset1(X26,X27,X28,X29) = k2_xboole_0(k2_tarski(X26,X27),k2_tarski(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_11,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)) != k6_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk6_0),k3_mcart_1(esk1_0,esk4_0,esk6_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk6_0),k3_mcart_1(esk2_0,esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_12,plain,(
    ! [X9,X10,X11] : k3_mcart_1(X9,X10,X11) = k4_tarski(k4_tarski(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] : k3_zfmisc_1(X12,X13,X14) = k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_14,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18] : k2_enumset1(X15,X16,X17,X18) = k2_enumset1(X15,X17,X16,X18) ),
    inference(variable_rename,[status(thm)],[t104_enumset1])).

cnf(c_0_17,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)) != k6_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk6_0),k3_mcart_1(esk1_0,esk4_0,esk6_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk6_0),k3_mcart_1(esk2_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X22,X23,X24,X25] : k2_zfmisc_1(k2_tarski(X22,X23),k2_tarski(X24,X25)) = k2_enumset1(k4_tarski(X22,X24),k4_tarski(X22,X25),k4_tarski(X23,X24),k4_tarski(X23,X25)) ),
    inference(variable_rename,[status(thm)],[t25_mcart_1])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)),k2_tarski(esk5_0,esk6_0)) != k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0)),k2_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk6_0),k4_tarski(k4_tarski(esk1_0,esk4_0),esk6_0))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0)),k2_tarski(k4_tarski(k4_tarski(esk2_0,esk3_0),esk6_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_18]),c_0_18]),c_0_18]),c_0_18]),c_0_18]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_15]),c_0_15])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X19,X20,X21] :
      ( k2_zfmisc_1(k2_xboole_0(X19,X20),X21) = k2_xboole_0(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X21))
      & k2_zfmisc_1(X21,k2_xboole_0(X19,X20)) = k2_xboole_0(k2_zfmisc_1(X21,X19),k2_zfmisc_1(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk6_0)),k2_tarski(k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk4_0),esk6_0))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk6_0)),k2_tarski(k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk6_0)))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)),k2_tarski(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(k4_tarski(X1,X3),k4_tarski(X1,X4)),k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X4))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28]),c_0_29]),c_0_28])]),
    [proof]).

%------------------------------------------------------------------------------
