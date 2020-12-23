%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0913+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:24 EST 2020

% Result     : Theorem 0.07s
% Output     : CNFRefutation 0.07s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 114 expanded)
%              Number of clauses        :   23 (  48 expanded)
%              Number of leaves         :    4 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 335 expanded)
%              Number of equality atoms :    6 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
    <=> ( r2_hidden(X1,X4)
        & r2_hidden(X2,X5)
        & r2_hidden(X3,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
      <=> ( r2_hidden(X1,X4)
          & r2_hidden(X2,X5)
          & r2_hidden(X3,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t73_mcart_1])).

fof(c_0_5,negated_conjecture,
    ( ( ~ r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      | ~ r2_hidden(esk1_0,esk4_0)
      | ~ r2_hidden(esk2_0,esk5_0)
      | ~ r2_hidden(esk3_0,esk6_0) )
    & ( r2_hidden(esk1_0,esk4_0)
      | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) )
    & ( r2_hidden(esk2_0,esk5_0)
      | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) )
    & ( r2_hidden(esk3_0,esk6_0)
      | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9] : k3_mcart_1(X7,X8,X9) = k4_tarski(k4_tarski(X7,X8),X9) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_7,plain,(
    ! [X10,X11,X12] : k3_zfmisc_1(X10,X11,X12) = k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r2_hidden(X13,X15)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( r2_hidden(X14,X16)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X14,X16)
        | r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk2_0,esk5_0)
    | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    | ~ r2_hidden(esk1_0,esk4_0)
    | ~ r2_hidden(esk2_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_0,esk4_0)
    | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk3_0,esk6_0)
    | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_0,esk5_0)
    | r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk4_0)
    | ~ r2_hidden(esk2_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk6_0)
    | ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_10]),c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_0,esk4_0)
    | r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_10]),c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk3_0,esk6_0)
    | r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_10]),c_0_11])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | ~ r2_hidden(esk1_0,esk4_0)
    | ~ r2_hidden(esk2_0,esk5_0) ),
    inference(csr,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_19]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,esk6_0) ),
    inference(csr,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_0),k2_zfmisc_1(X2,esk5_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | ~ r2_hidden(esk2_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk3_0),k2_zfmisc_1(X2,esk6_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_22])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),
    [proof]).

%------------------------------------------------------------------------------
