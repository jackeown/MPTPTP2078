%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t40_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:07 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   15 (  21 expanded)
%              Number of clauses        :    6 (   8 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  25 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k1_tarski(X4)) = k2_tarski(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t40_mcart_1.p',t40_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t40_mcart_1.p',d3_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t40_mcart_1.p',d3_mcart_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t40_mcart_1.p',t36_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k1_tarski(X4)) = k2_tarski(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4)) ),
    inference(assume_negation,[status(cth)],[t40_mcart_1])).

fof(c_0_5,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k2_tarski(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X16,X17,X18] : k3_zfmisc_1(X16,X17,X18) = k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X13,X14,X15] : k3_mcart_1(X13,X14,X15) = k4_tarski(k4_tarski(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_8,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k2_tarski(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X25,X26,X27] :
      ( k2_zfmisc_1(k1_tarski(X25),k2_tarski(X26,X27)) = k2_tarski(k4_tarski(X25,X26),k4_tarski(X25,X27))
      & k2_zfmisc_1(k2_tarski(X25,X26),k1_tarski(X27)) = k2_tarski(k4_tarski(X25,X27),k4_tarski(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_12,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)),k1_tarski(esk4_0)) != k2_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_10])).

cnf(c_0_13,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
