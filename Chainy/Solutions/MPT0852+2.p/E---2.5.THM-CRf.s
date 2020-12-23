%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0852+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:54 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   13 (  26 expanded)
%              Number of clauses        :    8 (  10 expanded)
%              Number of leaves         :    2 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  42 expanded)
%              Number of equality atoms :   17 (  41 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1 ) ),
    inference(assume_negation,[status(cth)],[t8_mcart_1])).

fof(c_0_3,plain,(
    ! [X387,X388] :
      ( k1_mcart_1(k4_tarski(X387,X388)) = X387
      & k2_mcart_1(k4_tarski(X387,X388)) = X388 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_4,negated_conjecture,
    ( esk1_0 = k4_tarski(esk2_0,esk3_0)
    & k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( esk1_0 = k4_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( k1_mcart_1(esk1_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_9,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,negated_conjecture,
    ( k4_tarski(esk2_0,k2_mcart_1(esk1_0)) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( k2_mcart_1(esk1_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_6])]),
    [proof]).
%------------------------------------------------------------------------------
