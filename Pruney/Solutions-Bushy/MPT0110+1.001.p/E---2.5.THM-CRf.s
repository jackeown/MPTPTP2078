%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0110+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of clauses        :    3 (   3 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    4
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t103_xboole_1,conjecture,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_xboole_1)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t103_xboole_1])).

fof(c_0_3,negated_conjecture,(
    ~ r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

fof(c_0_4,plain,(
    ! [X3,X4] : r1_xboole_0(k3_xboole_0(X3,X4),k5_xboole_0(X3,X4)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

cnf(c_0_5,negated_conjecture,
    ( ~ r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_5,c_0_6])]),
    [proof]).

%------------------------------------------------------------------------------
