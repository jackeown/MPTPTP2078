%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0873+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:19 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(t28_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_mcart_1(X1,X2,X3) = k3_mcart_1(X4,X5,X6)
     => ( X1 = X4
        & X2 = X5
        & X3 = X6 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

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
    ! [X9,X10,X11,X12] : k4_mcart_1(X9,X10,X11,X12) = k4_tarski(k3_mcart_1(X9,X10,X11),X12) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_7,plain,(
    ! [X19,X20,X21,X22] :
      ( ( X19 = X21
        | k4_tarski(X19,X20) != k4_tarski(X21,X22) )
      & ( X20 = X22
        | k4_tarski(X19,X20) != k4_tarski(X21,X22) ) ) ),
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
    ( esk4_0 = X1
    | k4_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0),esk8_0) != k4_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,negated_conjecture,
    ( esk4_0 = esk8_0 ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_14,plain,
    ( X1 = X2
    | k4_tarski(X1,X3) != k4_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( k4_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),esk8_0) = k4_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_13])).

fof(c_0_16,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( X13 = X16
        | k3_mcart_1(X13,X14,X15) != k3_mcart_1(X16,X17,X18) )
      & ( X14 = X17
        | k3_mcart_1(X13,X14,X15) != k3_mcart_1(X16,X17,X18) )
      & ( X15 = X18
        | k3_mcart_1(X13,X14,X15) != k3_mcart_1(X16,X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).

cnf(c_0_17,negated_conjecture,
    ( k3_mcart_1(esk1_0,esk2_0,esk3_0) = X1
    | k4_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0),esk8_0) != k4_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( X1 = X2
    | k3_mcart_1(X3,X4,X1) != k3_mcart_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k3_mcart_1(esk1_0,esk2_0,esk3_0) = k3_mcart_1(esk5_0,esk6_0,esk7_0) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 = X1
    | k3_mcart_1(esk5_0,esk6_0,esk7_0) != k3_mcart_1(X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( esk3_0 = esk7_0 ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_22,plain,
    ( X1 = X2
    | k3_mcart_1(X3,X1,X4) != k3_mcart_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k3_mcart_1(esk1_0,esk2_0,esk7_0) = k3_mcart_1(esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 = X1
    | k3_mcart_1(esk5_0,esk6_0,esk7_0) != k3_mcart_1(X2,X1,X3) ),
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
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_13])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | k3_mcart_1(X1,X3,X4) != k3_mcart_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( k3_mcart_1(esk1_0,esk6_0,esk7_0) = k3_mcart_1(esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_21])])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 = X1
    | k3_mcart_1(esk5_0,esk6_0,esk7_0) != k3_mcart_1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_32]),
    [proof]).

%------------------------------------------------------------------------------
