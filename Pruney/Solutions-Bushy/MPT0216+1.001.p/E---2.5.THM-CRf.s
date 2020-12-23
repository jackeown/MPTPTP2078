%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0216+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   17 (  27 expanded)
%              Number of clauses        :   10 (  12 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   26 (  45 expanded)
%              Number of equality atoms :   25 (  44 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k1_tarski(X1) = k2_tarski(X2,X3)
     => X2 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(t8_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k1_tarski(X1) = k2_tarski(X2,X3)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k1_tarski(X1) = k2_tarski(X2,X3)
       => X2 = X3 ) ),
    inference(assume_negation,[status(cth)],[t9_zfmisc_1])).

fof(c_0_4,plain,(
    ! [X6,X7,X8] :
      ( k1_tarski(X6) != k2_tarski(X7,X8)
      | X6 = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_zfmisc_1])])).

fof(c_0_5,negated_conjecture,
    ( k1_tarski(esk1_0) = k2_tarski(esk2_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | k1_tarski(X1) != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k1_tarski(esk1_0) = k2_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_9,negated_conjecture,
    ( esk1_0 = X1
    | k2_tarski(esk2_0,esk3_0) != k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk1_0 = esk2_0 ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( X1 = X2
    | k1_tarski(X1) != k2_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_tarski(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_7,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( esk2_0 = X1
    | k2_tarski(esk2_0,esk3_0) != k2_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15]),
    [proof]).

%------------------------------------------------------------------------------
