%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0111+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:03 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   28 ( 162 expanded)
%              Number of clauses        :   19 (  64 expanded)
%              Number of leaves         :    4 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 622 expanded)
%              Number of equality atoms :   11 ( 108 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_xboole_1,conjecture,(
    ! [X1,X2] :
      ( ~ ( ~ r2_xboole_0(X1,X2)
          & X1 != X2
          & ~ r2_xboole_0(X2,X1) )
    <=> r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_xboole_1)).

fof(reflexivity_r3_xboole_0,axiom,(
    ! [X1,X2] : r3_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ ( ~ r2_xboole_0(X1,X2)
            & X1 != X2
            & ~ r2_xboole_0(X2,X1) )
      <=> r3_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t104_xboole_1])).

fof(c_0_5,negated_conjecture,
    ( ( ~ r2_xboole_0(esk1_0,esk2_0)
      | ~ r3_xboole_0(esk1_0,esk2_0) )
    & ( esk1_0 != esk2_0
      | ~ r3_xboole_0(esk1_0,esk2_0) )
    & ( ~ r2_xboole_0(esk2_0,esk1_0)
      | ~ r3_xboole_0(esk1_0,esk2_0) )
    & ( r2_xboole_0(esk1_0,esk2_0)
      | esk1_0 = esk2_0
      | r2_xboole_0(esk2_0,esk1_0)
      | r3_xboole_0(esk1_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

fof(c_0_6,plain,(
    ! [X7] : r3_xboole_0(X7,X7) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_xboole_0])])).

fof(c_0_7,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | ~ r2_xboole_0(X3,X4) )
      & ( X3 != X4
        | ~ r2_xboole_0(X3,X4) )
      & ( ~ r1_tarski(X3,X4)
        | X3 = X4
        | r2_xboole_0(X3,X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_8,negated_conjecture,
    ( esk1_0 != esk2_0
    | ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_xboole_0(esk1_0,esk2_0)
    | esk1_0 = esk2_0
    | r2_xboole_0(esk2_0,esk1_0)
    | r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r3_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ( ~ r3_xboole_0(X5,X6)
        | r1_tarski(X5,X6)
        | r1_tarski(X6,X5) )
      & ( ~ r1_tarski(X5,X6)
        | r3_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X6,X5)
        | r3_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( r3_xboole_0(esk1_0,esk2_0)
    | r2_xboole_0(esk2_0,esk1_0)
    | r2_xboole_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r3_xboole_0(esk1_0,esk2_0)
    | r2_xboole_0(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_16,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | r1_tarski(X2,X1)
    | ~ r3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r3_xboole_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_15]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_xboole_0(esk1_0,esk2_0)
    | ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    | r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_xboole_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_xboole_0(esk2_0,esk1_0)
    | ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_xboole_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_18])])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_25]),c_0_22]),c_0_26]),
    [proof]).

%------------------------------------------------------------------------------
