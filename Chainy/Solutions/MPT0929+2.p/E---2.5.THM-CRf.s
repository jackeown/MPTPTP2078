%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0929+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:58 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   23 (  43 expanded)
%              Number of clauses        :   10 (  16 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  76 expanded)
%              Number of equality atoms :   41 (  75 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    4 (   2 average)
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

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k17_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X1
        & k18_mcart_1(k4_tarski(k4_tarski(X1,X2),X3)) = X2
        & k19_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X4
        & k20_mcart_1(k4_tarski(X6,k4_tarski(X4,X5))) = X5 ) ),
    inference(assume_negation,[status(cth)],[t89_mcart_1])).

fof(c_0_7,negated_conjecture,
    ( k17_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk1_0
    | k18_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk2_0
    | k19_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk4_0
    | k20_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X428] : k17_mcart_1(X428) = k1_mcart_1(k1_mcart_1(X428)) ),
    inference(variable_rename,[status(thm)],[d14_mcart_1])).

fof(c_0_9,plain,(
    ! [X427] : k18_mcart_1(X427) = k2_mcart_1(k1_mcart_1(X427)) ),
    inference(variable_rename,[status(thm)],[d15_mcart_1])).

fof(c_0_10,plain,(
    ! [X426] : k19_mcart_1(X426) = k1_mcart_1(k2_mcart_1(X426)) ),
    inference(variable_rename,[status(thm)],[d16_mcart_1])).

fof(c_0_11,plain,(
    ! [X19] : k20_mcart_1(X19) = k2_mcart_1(k2_mcart_1(X19)) ),
    inference(variable_rename,[status(thm)],[d17_mcart_1])).

cnf(c_0_12,negated_conjecture,
    ( k17_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk1_0
    | k18_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) != esk2_0
    | k19_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk4_0
    | k20_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0))) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k17_mcart_1(X1) = k1_mcart_1(k1_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k18_mcart_1(X1) = k2_mcart_1(k1_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k19_mcart_1(X1) = k1_mcart_1(k2_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k20_mcart_1(X1) = k2_mcart_1(k2_mcart_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X417,X418] :
      ( k1_mcart_1(k4_tarski(X417,X418)) = X417
      & k2_mcart_1(k4_tarski(X417,X418)) = X418 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_18,negated_conjecture,
    ( k1_mcart_1(k2_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))) != esk4_0
    | k2_mcart_1(k2_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))) != esk5_0
    | k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))) != esk1_0
    | k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_19,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( k1_mcart_1(k2_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))) != esk4_0
    | k2_mcart_1(k2_mcart_1(k4_tarski(esk6_0,k4_tarski(esk4_0,esk5_0)))) != esk5_0
    | k2_mcart_1(k4_tarski(esk1_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19]),c_0_19])])).

cnf(c_0_21,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_19]),c_0_21]),c_0_21]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
