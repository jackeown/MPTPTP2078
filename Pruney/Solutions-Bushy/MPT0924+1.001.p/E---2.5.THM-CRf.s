%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0924+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:25 EST 2020

% Result     : Theorem 0.07s
% Output     : CNFRefutation 0.07s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 209 expanded)
%              Number of clauses        :   33 (  91 expanded)
%              Number of leaves         :    6 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 569 expanded)
%              Number of equality atoms :   10 ( 107 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
    <=> ( r2_hidden(X1,X5)
        & r2_hidden(X2,X6)
        & r2_hidden(X3,X7)
        & r2_hidden(X4,X8) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t54_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).

fof(t73_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
    <=> ( r2_hidden(X1,X4)
        & r2_hidden(X2,X5)
        & r2_hidden(X3,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
      <=> ( r2_hidden(X1,X5)
          & r2_hidden(X2,X6)
          & r2_hidden(X3,X7)
          & r2_hidden(X4,X8) ) ) ),
    inference(assume_negation,[status(cth)],[t84_mcart_1])).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X15] : k4_mcart_1(X12,X13,X14,X15) = k4_tarski(k3_mcart_1(X12,X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_8,plain,(
    ! [X9,X10,X11] : k3_mcart_1(X9,X10,X11) = k4_tarski(k4_tarski(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,negated_conjecture,
    ( ( ~ r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      | ~ r2_hidden(esk1_0,esk5_0)
      | ~ r2_hidden(esk2_0,esk6_0)
      | ~ r2_hidden(esk3_0,esk7_0)
      | ~ r2_hidden(esk4_0,esk8_0) )
    & ( r2_hidden(esk1_0,esk5_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) )
    & ( r2_hidden(esk2_0,esk6_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) )
    & ( r2_hidden(esk3_0,esk7_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) )
    & ( r2_hidden(esk4_0,esk8_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_10,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X20,X21,X22,X23] : k3_zfmisc_1(k2_zfmisc_1(X20,X21),X22,X23) = k4_zfmisc_1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t54_mcart_1])).

fof(c_0_13,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( r2_hidden(X24,X27)
        | ~ r2_hidden(k3_mcart_1(X24,X25,X26),k3_zfmisc_1(X27,X28,X29)) )
      & ( r2_hidden(X25,X28)
        | ~ r2_hidden(k3_mcart_1(X24,X25,X26),k3_zfmisc_1(X27,X28,X29)) )
      & ( r2_hidden(X26,X29)
        | ~ r2_hidden(k3_mcart_1(X24,X25,X26),k3_zfmisc_1(X27,X28,X29)) )
      & ( ~ r2_hidden(X24,X27)
        | ~ r2_hidden(X25,X28)
        | ~ r2_hidden(X26,X29)
        | r2_hidden(k3_mcart_1(X24,X25,X26),k3_zfmisc_1(X27,X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_mcart_1])])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_0,esk8_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k3_mcart_1(X3,X4,X1),k3_zfmisc_1(X5,X6,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    | ~ r2_hidden(esk1_0,esk5_0)
    | ~ r2_hidden(esk2_0,esk6_0)
    | ~ r2_hidden(esk3_0,esk7_0)
    | ~ r2_hidden(esk4_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk4_0,esk8_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(k4_tarski(X3,X4),X1),k3_zfmisc_1(X5,X6,X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_11])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k3_mcart_1(X3,X1,X4),k3_zfmisc_1(X5,X2,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k3_mcart_1(X1,X3,X4),k3_zfmisc_1(X2,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk1_0,esk5_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_24,plain,(
    ! [X16,X17,X18,X19] :
      ( ( r2_hidden(X16,X18)
        | ~ r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,X19)) )
      & ( r2_hidden(X17,X19)
        | ~ r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,X19)) )
      & ( ~ r2_hidden(X16,X18)
        | ~ r2_hidden(X17,X19)
        | r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk2_0,esk6_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk5_0)
    | ~ r2_hidden(esk2_0,esk6_0)
    | ~ r2_hidden(esk3_0,esk7_0)
    | ~ r2_hidden(esk4_0,esk8_0)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_15]),c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_0,esk8_0) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(k4_tarski(X3,X1),X4),k3_zfmisc_1(X5,X2,X6)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_11])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(k4_tarski(X1,X3),X4),k3_zfmisc_1(X2,X5,X6)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_0,esk5_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_15]),c_0_16])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_0,esk6_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_15]),c_0_16])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,esk7_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0))
    | ~ r2_hidden(esk1_0,esk5_0)
    | ~ r2_hidden(esk2_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])]),c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_32]),c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(k3_mcart_1(X1,X3,X5),k3_zfmisc_1(X2,X4,X6))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,esk7_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_15]),c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),c_0_37])])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(k4_tarski(X1,X3),X5),k3_zfmisc_1(X2,X4,X6))
    | ~ r2_hidden(X5,X6)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,esk7_0) ),
    inference(csr,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_27]),c_0_42])])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_37]),c_0_36])]),
    [proof]).

%------------------------------------------------------------------------------
