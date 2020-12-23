%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0073+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   15 (  45 expanded)
%              Number of clauses        :    8 (  17 expanded)
%              Number of leaves         :    3 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 ( 121 expanded)
%              Number of equality atoms :   19 (  67 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_xboole_1,conjecture,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ~ ( ~ r1_xboole_0(X1,X1)
            & X1 = k1_xboole_0 )
        & ~ ( X1 != k1_xboole_0
            & r1_xboole_0(X1,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t66_xboole_1])).

fof(c_0_4,plain,(
    ! [X3,X4] :
      ( ( ~ r1_xboole_0(X3,X4)
        | k3_xboole_0(X3,X4) = k1_xboole_0 )
      & ( k3_xboole_0(X3,X4) != k1_xboole_0
        | r1_xboole_0(X3,X4) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_5,negated_conjecture,
    ( ( esk1_0 != k1_xboole_0
      | ~ r1_xboole_0(esk1_0,esk1_0) )
    & ( r1_xboole_0(esk1_0,esk1_0)
      | ~ r1_xboole_0(esk1_0,esk1_0) )
    & ( esk1_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( r1_xboole_0(esk1_0,esk1_0)
      | esk1_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])).

fof(c_0_6,plain,(
    ! [X5] : k3_xboole_0(X5,X5) = X5 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_7,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk1_0)
    | esk1_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ r1_xboole_0(esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11]),c_0_11])])).

cnf(c_0_14,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_9])]),c_0_13]),
    [proof]).

%------------------------------------------------------------------------------
