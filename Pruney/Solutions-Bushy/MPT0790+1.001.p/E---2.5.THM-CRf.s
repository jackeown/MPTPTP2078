%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0790+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:11 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   14 (  20 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    4
%              Number of atoms          :   34 (  52 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1))) = k1_wellord1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

fof(t39_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ( v2_wellord1(X2)
          & r1_tarski(X1,k3_relat_1(X2)) )
       => k3_relat_1(k2_wellord1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_wellord1)).

fof(t13_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1))) = k1_wellord1(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t40_wellord1])).

fof(c_0_4,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | ~ v2_wellord1(X6)
      | ~ r1_tarski(X5,k3_relat_1(X6))
      | k3_relat_1(k2_wellord1(X6,X5)) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_wellord1])])).

fof(c_0_5,plain,(
    ! [X3,X4] :
      ( ~ v1_relat_1(X4)
      | r1_tarski(k1_wellord1(X4,X3),k3_relat_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v2_wellord1(esk2_0)
    & k3_relat_1(k2_wellord1(esk2_0,k1_wellord1(esk2_0,esk1_0))) != k1_wellord1(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( k3_relat_1(k2_wellord1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r1_tarski(X2,k3_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k3_relat_1(k2_wellord1(esk2_0,k1_wellord1(esk2_0,esk1_0))) != k1_wellord1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2))) = k1_wellord1(X1,X2)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),
    [proof]).

%------------------------------------------------------------------------------
