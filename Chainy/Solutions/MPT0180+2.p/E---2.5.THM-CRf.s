%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0180+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:39 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    4
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t96_enumset1,conjecture,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t96_enumset1])).

fof(c_0_9,negated_conjecture,(
    k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk19_0) != k1_tarski(esk19_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X664] : k2_tarski(X664,X664) = k1_tarski(X664) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X665,X666] : k1_enumset1(X665,X665,X666) = k2_tarski(X665,X666) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X667,X668,X669] : k2_enumset1(X667,X667,X668,X669) = k1_enumset1(X667,X668,X669) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X670,X671,X672,X673] : k3_enumset1(X670,X670,X671,X672,X673) = k2_enumset1(X670,X671,X672,X673) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_14,plain,(
    ! [X674,X675,X676,X677,X678] : k4_enumset1(X674,X674,X675,X676,X677,X678) = k3_enumset1(X674,X675,X676,X677,X678) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_15,plain,(
    ! [X679,X680,X681,X682,X683,X684] : k5_enumset1(X679,X679,X680,X681,X682,X683,X684) = k4_enumset1(X679,X680,X681,X682,X683,X684) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_16,plain,(
    ! [X685,X686,X687,X688,X689,X690,X691] : k6_enumset1(X685,X685,X686,X687,X688,X689,X690,X691) = k5_enumset1(X685,X686,X687,X688,X689,X690,X691) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_17,negated_conjecture,
    ( k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk19_0) != k1_tarski(esk19_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
