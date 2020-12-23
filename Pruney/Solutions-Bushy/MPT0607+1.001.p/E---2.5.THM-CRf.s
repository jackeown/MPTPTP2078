%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0607+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:54 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   15 (  25 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  58 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t211_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(k1_relat_1(X3),X1)
       => k6_subset_1(X3,k7_relat_1(X3,X2)) = k7_relat_1(X3,k6_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t109_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(k1_relat_1(X3),X1)
         => k6_subset_1(X3,k7_relat_1(X3,X2)) = k7_relat_1(X3,k6_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t211_relat_1])).

fof(c_0_4,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(k1_relat_1(X8),X7)
      | k7_relat_1(X8,X7) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(k1_relat_1(esk3_0),esk1_0)
    & k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)) != k7_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X4,X5,X6] :
      ( ~ v1_relat_1(X6)
      | k7_relat_1(X6,k6_subset_1(X4,X5)) = k6_subset_1(k7_relat_1(X6,X4),k7_relat_1(X6,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).

cnf(c_0_7,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k7_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( k7_relat_1(esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_12,negated_conjecture,
    ( k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)) != k7_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( k7_relat_1(esk3_0,k6_subset_1(esk1_0,X1)) = k6_subset_1(esk3_0,k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_9])])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13])]),
    [proof]).

%------------------------------------------------------------------------------
