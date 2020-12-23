%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0851+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:54 EST 2020

% Result     : Theorem 1.25s
% Output     : CNFRefutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  52 expanded)
%              Number of equality atoms :   51 (  51 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

fof(t7_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

fof(c_0_3,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21] :
      ( ( X18 != k2_mcart_1(X15)
        | X15 != k4_tarski(X19,X20)
        | X18 = X20
        | X15 != k4_tarski(X16,X17) )
      & ( X15 = k4_tarski(esk3_2(X15,X21),esk4_2(X15,X21))
        | X21 = k2_mcart_1(X15)
        | X15 != k4_tarski(X16,X17) )
      & ( X21 != esk4_2(X15,X21)
        | X21 = k2_mcart_1(X15)
        | X15 != k4_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k1_mcart_1(k4_tarski(X1,X2)) = X1
        & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    inference(assume_negation,[status(cth)],[t7_mcart_1])).

cnf(c_0_5,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,plain,(
    ! [X386,X387,X388,X389,X390,X391,X392] :
      ( ( X389 != k1_mcart_1(X386)
        | X386 != k4_tarski(X390,X391)
        | X389 = X390
        | X386 != k4_tarski(X387,X388) )
      & ( X386 = k4_tarski(esk84_2(X386,X392),esk85_2(X386,X392))
        | X392 = k1_mcart_1(X386)
        | X386 != k4_tarski(X387,X388) )
      & ( X392 != esk84_2(X386,X392)
        | X392 = k1_mcart_1(X386)
        | X386 != k4_tarski(X387,X388) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( k1_mcart_1(k4_tarski(esk1_0,esk2_0)) != esk1_0
    | k2_mcart_1(k4_tarski(esk1_0,esk2_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_5])])).

cnf(c_0_9,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k1_mcart_1(k4_tarski(esk1_0,esk2_0)) != esk1_0
    | k2_mcart_1(k4_tarski(esk1_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).

cnf(c_0_13,negated_conjecture,
    ( k1_mcart_1(k4_tarski(esk1_0,esk2_0)) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11])])).

cnf(c_0_14,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
