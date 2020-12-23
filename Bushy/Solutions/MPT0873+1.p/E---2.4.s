%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t33_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:06 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 293 expanded)
%              Number of clauses        :   25 ( 141 expanded)
%              Number of leaves         :    4 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :   75 ( 666 expanded)
%              Number of equality atoms :   74 ( 665 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
     => ( X1 = X5
        & X2 = X6
        & X3 = X7
        & X4 = X8 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t33_mcart_1.p',t33_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t33_mcart_1.p',d4_mcart_1)).

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t33_mcart_1.p',t33_zfmisc_1)).

fof(t28_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_mcart_1(X1,X2,X3) = k3_mcart_1(X4,X5,X6)
     => ( X1 = X4
        & X2 = X5
        & X3 = X6 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t33_mcart_1.p',t28_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
       => ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ),
    inference(assume_negation,[status(cth)],[t33_mcart_1])).

fof(c_0_5,negated_conjecture,
    ( k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20] : k4_mcart_1(X17,X18,X19,X20) = k4_tarski(k3_mcart_1(X17,X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_7,plain,(
    ! [X27,X28,X29,X30] :
      ( ( X27 = X29
        | k4_tarski(X27,X28) != k4_tarski(X29,X30) )
      & ( X28 = X30
        | k4_tarski(X27,X28) != k4_tarski(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).

cnf(c_0_8,negated_conjecture,
    ( k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X2
    | k4_tarski(X3,X1) != k4_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k4_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0),esk8_0) = k4_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk8_0 = X1
    | k4_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),esk4_0) != k4_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,negated_conjecture,
    ( esk4_0 = esk8_0 ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_14,plain,
    ( X1 = X2
    | k4_tarski(X1,X3) != k4_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( k4_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0),esk8_0) = k4_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_13])).

fof(c_0_16,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( X21 = X24
        | k3_mcart_1(X21,X22,X23) != k3_mcart_1(X24,X25,X26) )
      & ( X22 = X25
        | k3_mcart_1(X21,X22,X23) != k3_mcart_1(X24,X25,X26) )
      & ( X23 = X26
        | k3_mcart_1(X21,X22,X23) != k3_mcart_1(X24,X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).

cnf(c_0_17,negated_conjecture,
    ( k3_mcart_1(esk5_0,esk6_0,esk7_0) = X1
    | k4_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),esk8_0) != k4_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( X1 = X2
    | k3_mcart_1(X3,X4,X1) != k3_mcart_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k3_mcart_1(esk5_0,esk6_0,esk7_0) = k3_mcart_1(esk1_0,esk2_0,esk3_0) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( X1 = esk7_0
    | k3_mcart_1(X2,X3,X1) != k3_mcart_1(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( esk3_0 = esk7_0 ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_22,plain,
    ( X1 = X2
    | k3_mcart_1(X3,X1,X4) != k3_mcart_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k3_mcart_1(esk5_0,esk6_0,esk7_0) = k3_mcart_1(esk1_0,esk2_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( esk6_0 = X1
    | k3_mcart_1(esk1_0,esk2_0,esk7_0) != k3_mcart_1(X2,X1,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 = esk6_0 ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_13])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | k3_mcart_1(X1,X3,X4) != k3_mcart_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( k3_mcart_1(esk5_0,esk6_0,esk7_0) = k3_mcart_1(esk1_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk2_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_21])])).

cnf(c_0_31,negated_conjecture,
    ( esk5_0 = X1
    | k3_mcart_1(esk1_0,esk6_0,esk7_0) != k3_mcart_1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
