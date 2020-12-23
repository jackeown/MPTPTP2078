%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0044+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:56 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   12 (  25 expanded)
%              Number of clauses        :    7 (  10 expanded)
%              Number of leaves         :    2 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  58 expanded)
%              Number of equality atoms :   12 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_xboole_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = k1_xboole_0
      <=> r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t37_xboole_1])).

fof(c_0_3,plain,(
    ! [X3,X4] :
      ( ( k4_xboole_0(X3,X4) != k1_xboole_0
        | r1_tarski(X3,X4) )
      & ( ~ r1_tarski(X3,X4)
        | k4_xboole_0(X3,X4) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_4,negated_conjecture,
    ( ( k4_xboole_0(esk1_0,esk2_0) != k1_xboole_0
      | ~ r1_tarski(esk1_0,esk2_0) )
    & ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0
      | r1_tarski(esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0
    | r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) != k1_xboole_0
    | ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8])])).

cnf(c_0_11,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_8]),c_0_10]),
    [proof]).

%------------------------------------------------------------------------------
