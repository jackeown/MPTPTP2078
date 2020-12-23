%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0873+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:55 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 478 expanded)
%              Number of clauses        :   20 ( 210 expanded)
%              Number of leaves         :    4 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :   49 ( 776 expanded)
%              Number of equality atoms :   48 ( 775 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
     => ( X1 = X5
        & X2 = X6
        & X3 = X7
        & X4 = X8 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
       => ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ),
    inference(assume_negation,[status(cth)],[t33_mcart_1])).

fof(c_0_5,plain,(
    ! [X21,X22,X23,X24] : k4_mcart_1(X21,X22,X23,X24) = k4_tarski(k3_mcart_1(X21,X22,X23),X24) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_6,plain,(
    ! [X424,X425,X426] : k3_mcart_1(X424,X425,X426) = k4_tarski(k4_tarski(X424,X425),X426) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_7,negated_conjecture,
    ( k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X415,X416] :
      ( k1_mcart_1(k4_tarski(X415,X416)) = X415
      & k2_mcart_1(k4_tarski(X415,X416)) = X416 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_11,negated_conjecture,
    ( k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) = k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk4_0 = esk8_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_13])).

cnf(c_0_16,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk8_0) = k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0) = k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk3_0 = esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_18]),c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_0,esk2_0),esk7_0) = k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( k4_tarski(esk1_0,esk2_0) = k4_tarski(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_20]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_15])])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_22]),c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19])])).

cnf(c_0_26,negated_conjecture,
    ( k4_tarski(esk5_0,esk2_0) = k4_tarski(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk2_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_26]),c_0_13]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
