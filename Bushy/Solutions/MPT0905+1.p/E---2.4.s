%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t65_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:12 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  27 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  27 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3),k1_tarski(X4)) = k1_tarski(k4_mcart_1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',t65_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',d3_mcart_1)).

fof(t54_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',t54_mcart_1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',t35_zfmisc_1)).

fof(t39_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',t39_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k4_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3),k1_tarski(X4)) = k1_tarski(k4_mcart_1(X1,X2,X3,X4)) ),
    inference(assume_negation,[status(cth)],[t65_mcart_1])).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17] : k4_mcart_1(X14,X15,X16,X17) = k4_tarski(k3_mcart_1(X14,X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13] : k3_mcart_1(X11,X12,X13) = k4_tarski(k4_tarski(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,negated_conjecture,(
    k4_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X29,X30,X31,X32] : k3_zfmisc_1(k2_zfmisc_1(X29,X30),X31,X32) = k4_zfmisc_1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t54_mcart_1])).

cnf(c_0_13,negated_conjecture,
    ( k4_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X24,X25] : k2_zfmisc_1(k1_tarski(X24),k1_tarski(X25)) = k1_tarski(k4_tarski(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X26,X27,X28] : k3_zfmisc_1(k1_tarski(X26),k1_tarski(X27),k1_tarski(X28)) = k1_tarski(k3_mcart_1(X26,X27,X28)) ),
    inference(variable_rename,[status(thm)],[t39_mcart_1])).

cnf(c_0_18,negated_conjecture,
    ( k3_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k3_mcart_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k3_zfmisc_1(k1_tarski(k4_tarski(esk1_0,esk2_0)),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
