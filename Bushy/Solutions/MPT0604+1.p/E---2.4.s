%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t208_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:59 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   13 (  19 expanded)
%              Number of clauses        :    6 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  19 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    3 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t208_relat_1,conjecture,(
    ! [X1] : k3_relat_1(k1_tarski(k4_tarski(X1,X1))) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t208_relat_1.p',t208_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t208_relat_1.p',t69_enumset1)).

fof(t32_relat_1,axiom,(
    ! [X1,X2] : k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t208_relat_1.p',t32_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] : k3_relat_1(k1_tarski(k4_tarski(X1,X1))) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t208_relat_1])).

fof(c_0_4,negated_conjecture,(
    k3_relat_1(k1_tarski(k4_tarski(esk1_0,esk1_0))) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_6,plain,(
    ! [X19,X20] : k3_relat_1(k1_tarski(k4_tarski(X19,X20))) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t32_relat_1])).

cnf(c_0_7,negated_conjecture,
    ( k3_relat_1(k1_tarski(k4_tarski(esk1_0,esk1_0))) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k3_relat_1(k2_tarski(k4_tarski(esk1_0,esk1_0),k4_tarski(esk1_0,esk1_0))) != k2_tarski(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_8])).

cnf(c_0_11,plain,
    ( k3_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_9,c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
