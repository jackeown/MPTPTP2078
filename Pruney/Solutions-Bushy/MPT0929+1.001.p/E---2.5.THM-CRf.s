%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0929+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:25 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   28 (  58 expanded)
%              Number of clauses        :   13 (  31 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   75 ( 201 expanded)
%              Number of equality atoms :   74 ( 200 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t89_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k17_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X1
      & k18_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X2
      & k19_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X4
      & k20_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X5 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_mcart_1)).

fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_mcart_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(d14_mcart_1,axiom,(
    ! [X1] : k17_mcart_1(X1) = k1_mcart_1(k1_mcart_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_mcart_1)).

fof(d15_mcart_1,axiom,(
    ! [X1] : k18_mcart_1(X1) = k2_mcart_1(k1_mcart_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_mcart_1)).

fof(d16_mcart_1,axiom,(
    ! [X1] : k19_mcart_1(X1) = k1_mcart_1(k2_mcart_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_mcart_1)).

fof(d17_mcart_1,axiom,(
    ! [X1] : k20_mcart_1(X1) = k2_mcart_1(k2_mcart_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_mcart_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k17_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X1
        & k18_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X2
        & k19_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X4
        & k20_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X5 ) ),
    inference(assume_negation,[status(cth)],[t89_mcart_1])).

fof(c_0_8,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26] :
      ( ( X23 != k2_mcart_1(X20)
        | X20 != k4_tarski(X24,X25)
        | X23 = X25
        | X20 != k4_tarski(X21,X22) )
      & ( X20 = k4_tarski(esk3_2(X20,X26),esk4_2(X20,X26))
        | X26 = k2_mcart_1(X20)
        | X20 != k4_tarski(X21,X22) )
      & ( X26 != esk4_2(X20,X26)
        | X26 = k2_mcart_1(X20)
        | X20 != k4_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( X14 != k1_mcart_1(X11)
        | X11 != k4_tarski(X15,X16)
        | X14 = X15
        | X11 != k4_tarski(X12,X13) )
      & ( X11 = k4_tarski(esk1_2(X11,X17),esk2_2(X11,X17))
        | X17 = k1_mcart_1(X11)
        | X11 != k4_tarski(X12,X13) )
      & ( X17 != esk1_2(X11,X17)
        | X17 = k1_mcart_1(X11)
        | X11 != k4_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

fof(c_0_10,negated_conjecture,
    ( k17_mcart_1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)) != esk5_0
    | k18_mcart_1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)) != esk6_0
    | k19_mcart_1(k4_tarski(esk10_0,k4_tarski(esk8_0,esk9_0))) != esk8_0
    | k20_mcart_1(k4_tarski(esk10_0,k4_tarski(esk8_0,esk9_0))) != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X7] : k17_mcart_1(X7) = k1_mcart_1(k1_mcart_1(X7)) ),
    inference(variable_rename,[status(thm)],[d14_mcart_1])).

fof(c_0_12,plain,(
    ! [X8] : k18_mcart_1(X8) = k2_mcart_1(k1_mcart_1(X8)) ),
    inference(variable_rename,[status(thm)],[d15_mcart_1])).

fof(c_0_13,plain,(
    ! [X9] : k19_mcart_1(X9) = k1_mcart_1(k2_mcart_1(X9)) ),
    inference(variable_rename,[status(thm)],[d16_mcart_1])).

fof(c_0_14,plain,(
    ! [X10] : k20_mcart_1(X10) = k2_mcart_1(k2_mcart_1(X10)) ),
    inference(variable_rename,[status(thm)],[d17_mcart_1])).

cnf(c_0_15,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( k17_mcart_1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)) != esk5_0
    | k18_mcart_1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)) != esk6_0
    | k19_mcart_1(k4_tarski(esk10_0,k4_tarski(esk8_0,esk9_0))) != esk8_0
    | k20_mcart_1(k4_tarski(esk10_0,k4_tarski(esk8_0,esk9_0))) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k17_mcart_1(X1) = k1_mcart_1(k1_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k18_mcart_1(X1) = k2_mcart_1(k1_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k19_mcart_1(X1) = k1_mcart_1(k2_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k20_mcart_1(X1) = k2_mcart_1(k2_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])])).

cnf(c_0_23,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

cnf(c_0_24,negated_conjecture,
    ( k1_mcart_1(k2_mcart_1(k4_tarski(esk10_0,k4_tarski(esk8_0,esk9_0)))) != esk8_0
    | k2_mcart_1(k2_mcart_1(k4_tarski(esk10_0,k4_tarski(esk8_0,esk9_0)))) != esk9_0
    | k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))) != esk5_0
    | k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))) != esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_25])]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_25])]),
    [proof]).

%------------------------------------------------------------------------------
