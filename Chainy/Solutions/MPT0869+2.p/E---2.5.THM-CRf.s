%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0869+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:55 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   21 ( 119 expanded)
%              Number of clauses        :   14 (  49 expanded)
%              Number of leaves         :    3 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   35 ( 208 expanded)
%              Number of equality atoms :   34 ( 207 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    4 (   1 average)
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

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

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
    ! [X19,X20,X21] : k3_mcart_1(X19,X20,X21) = k4_tarski(k4_tarski(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_6,plain,(
    ! [X404,X405] :
      ( k1_mcart_1(k4_tarski(X404,X405)) = X404
      & k2_mcart_1(k4_tarski(X404,X405)) = X405 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_7,negated_conjecture,
    ( k3_mcart_1(esk1_0,esk2_0,esk3_0) = k3_mcart_1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0) = k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( k4_tarski(esk1_0,esk2_0) = k4_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk1_0 = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_11]),c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( k4_tarski(esk4_0,esk2_0) = k4_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k4_tarski(k4_tarski(esk4_0,esk5_0),esk3_0) = k4_tarski(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( esk3_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_18]),c_0_14]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
