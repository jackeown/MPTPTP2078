%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0106+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:03 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   17 (  20 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  20 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t99_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(assume_negation,[status(cth)],[t99_xboole_1])).

fof(c_0_5,plain,(
    ! [X9,X10,X11] : k4_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(k4_xboole_0(X9,X11),k4_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

fof(c_0_6,plain,(
    ! [X6,X7,X8] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_7,negated_conjecture,(
    k4_xboole_0(k5_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_8,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_9,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X4,X2))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X3,X4)),X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,k2_xboole_0(X5,X3))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X4,X5)),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15])]),
    [proof]).

%------------------------------------------------------------------------------
