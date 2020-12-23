%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0273+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:20 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   22 (  95 expanded)
%              Number of clauses        :   17 (  40 expanded)
%              Number of leaves         :    2 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 452 expanded)
%              Number of equality atoms :   37 ( 236 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
      <=> ( ~ r2_hidden(X1,X3)
          & ( r2_hidden(X2,X3)
            | X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_zfmisc_1])).

fof(c_0_3,plain,(
    ! [X4,X5,X6] :
      ( ( ~ r2_hidden(X4,X6)
        | k4_xboole_0(k2_tarski(X4,X5),X6) != k1_tarski(X4) )
      & ( r2_hidden(X5,X6)
        | X4 = X5
        | k4_xboole_0(k2_tarski(X4,X5),X6) != k1_tarski(X4) )
      & ( ~ r2_hidden(X5,X6)
        | r2_hidden(X4,X6)
        | k4_xboole_0(k2_tarski(X4,X5),X6) = k1_tarski(X4) )
      & ( X4 != X5
        | r2_hidden(X4,X6)
        | k4_xboole_0(k2_tarski(X4,X5),X6) = k1_tarski(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

fof(c_0_4,negated_conjecture,
    ( ( ~ r2_hidden(esk2_0,esk3_0)
      | r2_hidden(esk1_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) )
    & ( esk1_0 != esk2_0
      | r2_hidden(esk1_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) )
    & ( ~ r2_hidden(esk1_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_tarski(esk1_0) )
    & ( r2_hidden(esk2_0,esk3_0)
      | esk1_0 = esk2_0
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_tarski(esk1_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])).

cnf(c_0_5,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) != k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_tarski(esk1_0)
    | ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | ~ r2_hidden(esk2_0,esk3_0)
    | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | X3 = X1
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | esk1_0 = esk2_0
    | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | esk1_0 != esk2_0
    | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0)
    | esk2_0 != esk1_0 ),
    inference(sr,[status(thm)],[c_0_13,c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 = esk1_0 ),
    inference(sr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk3_0) != k1_tarski(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k1_tarski(X1)
    | r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_8]),
    [proof]).

%------------------------------------------------------------------------------
