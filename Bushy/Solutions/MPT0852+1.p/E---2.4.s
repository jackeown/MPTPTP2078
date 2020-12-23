%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t8_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:15 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   19 (  38 expanded)
%              Number of clauses        :   12 (  16 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  90 expanded)
%              Number of equality atoms :   55 (  89 expanded)
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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t8_mcart_1.p',d2_mcart_1)).

fof(t8_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t8_mcart_1.p',t8_mcart_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t8_mcart_1.p',d1_mcart_1)).

fof(c_0_3,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23] :
      ( ( X20 != k2_mcart_1(X17)
        | X17 != k4_tarski(X21,X22)
        | X20 = X22
        | X17 != k4_tarski(X18,X19) )
      & ( X17 = k4_tarski(esk6_2(X17,X23),esk7_2(X17,X23))
        | X23 = k2_mcart_1(X17)
        | X17 != k4_tarski(X18,X19) )
      & ( X23 != esk7_2(X17,X23)
        | X23 = k2_mcart_1(X17)
        | X17 != k4_tarski(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1 ) ),
    inference(assume_negation,[status(cth)],[t8_mcart_1])).

cnf(c_0_5,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,
    ( esk1_0 = k4_tarski(esk2_0,esk3_0)
    & k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14] :
      ( ( X11 != k1_mcart_1(X8)
        | X8 != k4_tarski(X12,X13)
        | X11 = X12
        | X8 != k4_tarski(X9,X10) )
      & ( X8 = k4_tarski(esk4_2(X8,X14),esk5_2(X8,X14))
        | X14 = k1_mcart_1(X8)
        | X8 != k4_tarski(X9,X10) )
      & ( X14 != esk4_2(X8,X14)
        | X14 = k1_mcart_1(X8)
        | X8 != k4_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

cnf(c_0_8,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_5])])).

cnf(c_0_9,negated_conjecture,
    ( esk1_0 = k4_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k2_mcart_1(esk1_0) = X1
    | k4_tarski(X2,X1) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).

cnf(c_0_13,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k2_mcart_1(esk1_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( k1_mcart_1(esk1_0) = X1
    | k4_tarski(X1,X2) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk1_0),esk3_0) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( k1_mcart_1(esk1_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_9])]),
    [proof]).
%------------------------------------------------------------------------------
