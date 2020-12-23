%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0905+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:23 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   26 (  44 expanded)
%              Number of clauses        :   13 (  19 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  44 expanded)
%              Number of equality atoms :   25 (  43 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3),k1_tarski(X4)) = k1_tarski(k4_mcart_1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t39_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

fof(t54_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k4_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3),k1_tarski(X4)) = k1_tarski(k4_mcart_1(X1,X2,X3,X4)) ),
    inference(assume_negation,[status(cth)],[t65_mcart_1])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11] : k4_mcart_1(X8,X9,X10,X11) = k4_tarski(k3_mcart_1(X8,X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_8,plain,(
    ! [X5,X6,X7] : k3_mcart_1(X5,X6,X7) = k4_tarski(k4_tarski(X5,X6),X7) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] : k3_zfmisc_1(k1_tarski(X14),k1_tarski(X15),k1_tarski(X16)) = k1_tarski(k3_mcart_1(X14,X15,X16)) ),
    inference(variable_rename,[status(thm)],[t39_mcart_1])).

fof(c_0_10,negated_conjecture,(
    k4_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X17,X18,X19,X20] : k3_zfmisc_1(k2_zfmisc_1(X17,X18),X19,X20) = k4_zfmisc_1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t54_mcart_1])).

cnf(c_0_14,plain,
    ( k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k3_mcart_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X12,X13] : k2_zfmisc_1(k1_tarski(X12),k1_tarski(X13)) = k1_tarski(k4_tarski(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

cnf(c_0_16,negated_conjecture,
    ( k4_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k3_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_22,plain,
    ( k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( k3_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_tarski(esk3_0)),k1_tarski(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_24,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3),k1_tarski(X4)) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])]),
    [proof]).

%------------------------------------------------------------------------------
