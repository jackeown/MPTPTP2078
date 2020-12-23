%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0120+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:04 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :    8 (  17 expanded)
%              Number of clauses        :    3 (   6 expanded)
%              Number of leaves         :    2 (   5 expanded)
%              Depth                    :    4
%              Number of atoms          :    8 (  17 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(assume_negation,[status(cth)],[t113_xboole_1])).

fof(c_0_3,negated_conjecture,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0) != k2_xboole_0(esk1_0,k2_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

fof(c_0_4,plain,(
    ! [X5,X6,X7] : k2_xboole_0(k2_xboole_0(X5,X6),X7) = k2_xboole_0(X5,k2_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_5,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0) != k2_xboole_0(esk1_0,k2_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_5,c_0_6]),c_0_6]),c_0_6]),c_0_6])]),
    [proof]).

%------------------------------------------------------------------------------
