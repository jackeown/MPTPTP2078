%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0586+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:52 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   10 (  16 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    2 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   26 (  44 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t190_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( ~ v3_relat_1(k7_relat_1(X2,X1))
          & v3_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_relat_1)).

fof(fc19_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v3_relat_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v3_relat_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc19_relat_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( ~ v3_relat_1(k7_relat_1(X2,X1))
            & v3_relat_1(X2) ) ) ),
    inference(assume_negation,[status(cth)],[t190_relat_1])).

fof(c_0_3,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ~ v3_relat_1(k7_relat_1(esk2_0,esk1_0))
    & v3_relat_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).

fof(c_0_4,plain,(
    ! [X3,X4] :
      ( ( v1_relat_1(k7_relat_1(X3,X4))
        | ~ v1_relat_1(X3)
        | ~ v3_relat_1(X3) )
      & ( v3_relat_1(k7_relat_1(X3,X4))
        | ~ v1_relat_1(X3)
        | ~ v3_relat_1(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc19_relat_1])])])).

cnf(c_0_5,negated_conjecture,
    ( ~ v3_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( v3_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v3_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v3_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8])]),
    [proof]).

%------------------------------------------------------------------------------
