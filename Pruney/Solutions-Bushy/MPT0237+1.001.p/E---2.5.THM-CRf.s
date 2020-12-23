%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0237+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:16 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    4
%              Number of atoms          :   12 (  12 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_zfmisc_1,conjecture,(
    ! [X1,X2] : k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2))) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] : k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2))) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t32_zfmisc_1])).

fof(c_0_4,plain,(
    ! [X5,X6] : k2_tarski(X5,X6) = k2_xboole_0(k1_tarski(X5),k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_5,plain,(
    ! [X3,X4] : k3_tarski(k2_tarski(X3,X4)) = k2_xboole_0(X3,X4) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_6,negated_conjecture,(
    k3_tarski(k2_tarski(k1_tarski(esk1_0),k1_tarski(esk2_0))) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k3_tarski(k2_tarski(k1_tarski(esk1_0),k1_tarski(esk2_0))) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X2) = k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10])]),
    [proof]).

%------------------------------------------------------------------------------
