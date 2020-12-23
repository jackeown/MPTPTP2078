%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0566+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:49 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   13 (  16 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  29 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t170_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2))) ) ),
    inference(assume_negation,[status(cth)],[t170_relat_1])).

fof(c_0_4,plain,(
    ! [X3,X4] :
      ( ~ v1_relat_1(X4)
      | r1_tarski(k10_relat_1(X4,X3),k1_relat_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_5,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k10_relat_1(X5,k2_relat_1(X5)) = k1_relat_1(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ~ r1_tarski(k10_relat_1(esk2_0,esk1_0),k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk2_0,esk1_0),k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])]),
    [proof]).

%------------------------------------------------------------------------------
