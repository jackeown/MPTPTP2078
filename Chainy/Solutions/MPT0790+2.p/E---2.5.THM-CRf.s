%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0790+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  25 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  61 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

fof(t13_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(t39_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ( v2_wellord1(X2)
          & r1_tarski(X1,k3_relat_1(X2)) )
       => k3_relat_1(k2_wellord1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_wellord1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1))) = k1_wellord1(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t40_wellord1])).

fof(c_0_4,plain,(
    ! [X3413,X3414] :
      ( ~ v1_relat_1(X3414)
      | r1_tarski(k1_wellord1(X3414,X3413),k3_relat_1(X3414)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk279_0)
    & v2_wellord1(esk279_0)
    & k3_relat_1(k2_wellord1(esk279_0,k1_wellord1(esk279_0,esk278_0))) != k1_wellord1(esk279_0,esk278_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X3473,X3474] :
      ( ~ v1_relat_1(X3474)
      | ~ v2_wellord1(X3474)
      | ~ r1_tarski(X3473,k3_relat_1(X3474))
      | k3_relat_1(k2_wellord1(X3474,X3473)) = X3473 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_wellord1])])).

cnf(c_0_7,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk279_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_relat_1(k2_wellord1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r1_tarski(X2,k3_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk279_0,X1),k3_relat_1(esk279_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v2_wellord1(esk279_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( k3_relat_1(k2_wellord1(esk279_0,k1_wellord1(esk279_0,esk278_0))) != k1_wellord1(esk279_0,esk278_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( k3_relat_1(k2_wellord1(esk279_0,k1_wellord1(esk279_0,X1))) = k1_wellord1(esk279_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_8])])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
