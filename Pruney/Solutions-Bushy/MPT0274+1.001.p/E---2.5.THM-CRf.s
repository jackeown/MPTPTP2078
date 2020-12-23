%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0274+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:20 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  75 expanded)
%              Number of clauses        :   16 (  32 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 214 expanded)
%              Number of equality atoms :   18 (  70 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t57_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
      <=> ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t72_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k4_xboole_0(X12,X13) = X12 )
      & ( k4_xboole_0(X12,X13) != X12
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_7,plain,(
    ! [X9,X10,X11] :
      ( r2_hidden(X9,X10)
      | r2_hidden(X11,X10)
      | r1_xboole_0(k2_tarski(X9,X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).

fof(c_0_8,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0)
      | r2_hidden(esk1_0,esk3_0)
      | r2_hidden(esk2_0,esk3_0) )
    & ( ~ r2_hidden(esk1_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0) )
    & ( ~ r2_hidden(esk2_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

cnf(c_0_9,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0)
    | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    | r2_hidden(X2,X3)
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0)
    | ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_xboole_0(k2_tarski(X6,X7),X8)
      | ~ r2_hidden(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

fof(c_0_17,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_tarski(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_14,c_0_24]),c_0_25]),
    [proof]).

%------------------------------------------------------------------------------
