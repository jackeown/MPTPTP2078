%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : enumset1__t123_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:57 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  28 expanded)
%              Number of clauses        :    9 (  13 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  28 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t123_enumset1.p',t123_enumset1)).

fof(t119_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t123_enumset1.p',t119_enumset1)).

fof(l123_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t123_enumset1.p',l123_enumset1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    inference(assume_negation,[status(cth)],[t123_enumset1])).

fof(c_0_4,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16] : k2_enumset1(X13,X14,X15,X16) = k2_enumset1(X15,X16,X14,X13) ),
    inference(variable_rename,[status(thm)],[t119_enumset1])).

fof(c_0_6,plain,(
    ! [X9,X10,X11,X12] : k2_enumset1(X9,X10,X11,X12) = k2_enumset1(X10,X11,X9,X12) ),
    inference(variable_rename,[status(thm)],[l123_enumset1])).

cnf(c_0_7,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k2_enumset1(esk4_0,esk3_0,esk1_0,esk2_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( k2_enumset1(esk4_0,esk2_0,esk1_0,esk3_0) != k2_enumset1(esk4_0,esk2_0,esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
