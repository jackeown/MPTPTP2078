%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0172+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:39 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_enumset1,conjecture,(
    ! [X1,X2] : k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] : k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t88_enumset1])).

fof(c_0_6,negated_conjecture,(
    k4_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0) != k2_tarski(esk19_0,esk20_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X665,X666] : k1_enumset1(X665,X665,X666) = k2_tarski(X665,X666) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_8,plain,(
    ! [X667,X668,X669] : k2_enumset1(X667,X667,X668,X669) = k1_enumset1(X667,X668,X669) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_9,plain,(
    ! [X670,X671,X672,X673] : k3_enumset1(X670,X670,X671,X672,X673) = k2_enumset1(X670,X671,X672,X673) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_10,plain,(
    ! [X674,X675,X676,X677,X678] : k4_enumset1(X674,X674,X675,X676,X677,X678) = k3_enumset1(X674,X675,X676,X677,X678) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_11,negated_conjecture,
    ( k4_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0) != k2_tarski(esk19_0,esk20_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
