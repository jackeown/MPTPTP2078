%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0869+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:19 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   25 ( 137 expanded)
%              Number of clauses        :   18 (  65 expanded)
%              Number of leaves         :    3 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :   48 ( 282 expanded)
%              Number of equality atoms :   47 ( 281 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_mcart_1(X1,X2,X3) = k3_mcart_1(X4,X5,X6)
     => ( X1 = X4
        & X2 = X5
        & X3 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k3_mcart_1(X1,X2,X3) = k3_mcart_1(X4,X5,X6)
       => ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ),
    inference(assume_negation,[status(cth)],[t28_mcart_1])).

fof(c_0_4,negated_conjecture,
    ( k3_mcart_1(esk1_0,esk2_0,esk3_0) = k3_mcart_1(esk4_0,esk5_0,esk6_0)
    & ( esk1_0 != esk4_0
      | esk2_0 != esk5_0
      | esk3_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X7,X8,X9] : k3_mcart_1(X7,X8,X9) = k4_tarski(k4_tarski(X7,X8),X9) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13] :
      ( ( X10 = X12
        | k4_tarski(X10,X11) != k4_tarski(X12,X13) )
      & ( X11 = X13
        | k4_tarski(X10,X11) != k4_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).

cnf(c_0_7,negated_conjecture,
    ( k3_mcart_1(esk1_0,esk2_0,esk3_0) = k3_mcart_1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = X2
    | k4_tarski(X3,X1) != k4_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0) = k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( X1 = esk3_0
    | k4_tarski(X2,X1) != k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,negated_conjecture,
    ( esk3_0 = esk6_0 ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_13,plain,
    ( X1 = X2
    | k4_tarski(X1,X3) != k4_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_0,esk2_0),esk6_0) = k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_10,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( k4_tarski(esk1_0,esk2_0) = X1
    | k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0) != k4_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( k4_tarski(esk1_0,esk2_0) = k4_tarski(esk4_0,esk5_0) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 = X1
    | k4_tarski(esk4_0,esk5_0) != k4_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_16])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 = esk5_0 ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( k4_tarski(esk1_0,esk5_0) = k4_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_12])])).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 = X1
    | k4_tarski(esk4_0,esk5_0) != k4_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23]),
    [proof]).

%------------------------------------------------------------------------------
