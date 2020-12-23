%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t44_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:08 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   23 (  32 expanded)
%              Number of clauses        :   10 (  13 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  34 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t44_mcart_1.p',t44_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t44_mcart_1.p',d3_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t44_mcart_1.p',d3_mcart_1)).

fof(t104_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t44_mcart_1.p',t104_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t44_mcart_1.p',t36_zfmisc_1)).

fof(t25_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t44_mcart_1.p',t25_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t44_mcart_1])).

fof(c_0_7,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X18,X19,X20] : k3_zfmisc_1(X18,X19,X20) = k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X15,X16,X17] : k3_mcart_1(X15,X16,X17) = k4_tarski(k4_tarski(X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_10,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X23,X24,X25,X26] : k2_enumset1(X23,X24,X25,X26) = k2_enumset1(X23,X25,X24,X26) ),
    inference(variable_rename,[status(thm)],[t104_enumset1])).

cnf(c_0_14,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X35,X36,X37] :
      ( k2_zfmisc_1(k1_tarski(X35),k2_tarski(X36,X37)) = k2_tarski(k4_tarski(X35,X36),k4_tarski(X35,X37))
      & k2_zfmisc_1(k2_tarski(X35,X36),k1_tarski(X37)) = k2_tarski(k4_tarski(X35,X37),k4_tarski(X36,X37)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_17,negated_conjecture,
    ( k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)),k2_tarski(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X29,X30,X31,X32] : k2_zfmisc_1(k2_tarski(X29,X30),k2_tarski(X31,X32)) = k2_enumset1(k4_tarski(X29,X31),k4_tarski(X29,X32),k4_tarski(X30,X31),k4_tarski(X30,X32)) ),
    inference(variable_rename,[status(thm)],[t25_mcart_1])).

cnf(c_0_20,negated_conjecture,
    ( k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) != k2_zfmisc_1(k2_tarski(k4_tarski(esk1_0,esk3_0),k4_tarski(esk2_0,esk3_0)),k2_tarski(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
