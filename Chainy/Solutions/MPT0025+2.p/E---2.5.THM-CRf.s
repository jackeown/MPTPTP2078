%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0025+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:32 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   17 (  20 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  33 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k3_xboole_0(X2,X3))
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t18_xboole_1])).

fof(c_0_5,plain,(
    ! [X108,X109] :
      ( ~ r1_tarski(X108,X109)
      | k2_xboole_0(X108,X109) = X109 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_6,negated_conjecture,
    ( r1_tarski(esk15_0,k3_xboole_0(esk16_0,esk17_0))
    & ~ r1_tarski(esk15_0,esk16_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X105,X106,X107] :
      ( ~ r1_tarski(k2_xboole_0(X105,X106),X107)
      | r1_tarski(X105,X107) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_8,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk15_0,k3_xboole_0(esk16_0,esk17_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k2_xboole_0(esk15_0,k3_xboole_0(esk16_0,esk17_0)) = k3_xboole_0(esk16_0,esk17_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_12,plain,(
    ! [X123,X124] : r1_tarski(k3_xboole_0(X123,X124),X123) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk15_0,X1)
    | ~ r1_tarski(k3_xboole_0(esk16_0,esk17_0),X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_tarski(esk15_0,esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
