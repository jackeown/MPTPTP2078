%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0769+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:10 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   13 (  20 expanded)
%              Number of clauses        :    6 (   7 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  35 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k8_relat_1(X1,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(t17_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k7_relat_1(k8_relat_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(t140_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(X2,X1) = k8_relat_1(X1,k7_relat_1(X2,X1)) ) ),
    inference(assume_negation,[status(cth)],[t18_wellord1])).

fof(c_0_4,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k2_wellord1(esk2_0,esk1_0) != k8_relat_1(esk1_0,k7_relat_1(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | k2_wellord1(X8,X7) = k7_relat_1(k8_relat_1(X7,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).

cnf(c_0_6,negated_conjecture,
    ( k2_wellord1(esk2_0,esk1_0) != k8_relat_1(esk1_0,k7_relat_1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k2_wellord1(X1,X2) = k7_relat_1(k8_relat_1(X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_9,plain,(
    ! [X4,X5,X6] :
      ( ~ v1_relat_1(X6)
      | k7_relat_1(k8_relat_1(X4,X6),X5) = k8_relat_1(X4,k7_relat_1(X6,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).

cnf(c_0_10,negated_conjecture,
    ( k7_relat_1(k8_relat_1(esk1_0,esk2_0),esk1_0) != k8_relat_1(esk1_0,k7_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_11,plain,
    ( k7_relat_1(k8_relat_1(X2,X1),X3) = k8_relat_1(X2,k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_8])]),
    [proof]).

%------------------------------------------------------------------------------
