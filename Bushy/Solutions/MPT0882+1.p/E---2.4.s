%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t42_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:07 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  21 expanded)
%              Number of clauses        :    7 (   8 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  23 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t42_mcart_1.p',t42_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t42_mcart_1.p',d3_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t42_mcart_1.p',d3_mcart_1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t42_mcart_1.p',t35_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t42_mcart_1.p',t36_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X1,X2,X4)) ),
    inference(assume_negation,[status(cth)],[t42_mcart_1])).

fof(c_0_6,negated_conjecture,(
    k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X16,X17,X18] : k3_zfmisc_1(X16,X17,X18) = k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X13,X14,X15] : k3_mcart_1(X13,X14,X15) = k4_tarski(k4_tarski(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_9,negated_conjecture,
    ( k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X25,X26] : k2_zfmisc_1(k1_tarski(X25),k1_tarski(X26)) = k1_tarski(k4_tarski(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X27,X28,X29] :
      ( k2_zfmisc_1(k1_tarski(X27),k2_tarski(X28,X29)) = k2_tarski(k4_tarski(X27,X28),k4_tarski(X27,X29))
      & k2_zfmisc_1(k2_tarski(X27,X28),k1_tarski(X29)) = k2_tarski(k4_tarski(X27,X29),k4_tarski(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_14,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_tarski(esk3_0,esk4_0)) != k2_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_11])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
