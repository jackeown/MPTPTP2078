%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0097+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   16 (  19 expanded)
%              Number of clauses        :    7 (   8 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  19 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t90_xboole_1,conjecture,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(assume_negation,[status(cth)],[t90_xboole_1])).

fof(c_0_5,negated_conjecture,(
    ~ r1_xboole_0(k4_xboole_0(esk16_0,k3_xboole_0(esk16_0,esk17_0)),esk17_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X222,X223] : k4_xboole_0(X222,k4_xboole_0(X222,X223)) = k3_xboole_0(X222,X223) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_7,plain,(
    ! [X220,X221] : k4_xboole_0(X220,k3_xboole_0(X220,X221)) = k4_xboole_0(X220,X221) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(esk16_0,k3_xboole_0(esk16_0,esk17_0)),esk17_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X312,X313] : r1_xboole_0(k4_xboole_0(X312,X313),X313) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0))),esk17_0) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_14,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
