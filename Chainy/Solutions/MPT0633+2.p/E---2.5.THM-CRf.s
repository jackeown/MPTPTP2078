%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0633+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:49 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   16 (  19 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    4
%              Number of atoms          :   49 (  55 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',dt_k6_relat_1)).

fof(t35_funct_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(c_0_4,plain,(
    ! [X2808,X2809,X2810] :
      ( ( k1_relat_1(X2809) = X2808
        | X2809 != k6_relat_1(X2808)
        | ~ v1_relat_1(X2809)
        | ~ v1_funct_1(X2809) )
      & ( ~ r2_hidden(X2810,X2808)
        | k1_funct_1(X2809,X2810) = X2810
        | X2809 != k6_relat_1(X2808)
        | ~ v1_relat_1(X2809)
        | ~ v1_funct_1(X2809) )
      & ( r2_hidden(esk181_2(X2808,X2809),X2808)
        | k1_relat_1(X2809) != X2808
        | X2809 = k6_relat_1(X2808)
        | ~ v1_relat_1(X2809)
        | ~ v1_funct_1(X2809) )
      & ( k1_funct_1(X2809,esk181_2(X2808,X2809)) != esk181_2(X2808,X2809)
        | k1_relat_1(X2809) != X2808
        | X2809 = k6_relat_1(X2808)
        | ~ v1_relat_1(X2809)
        | ~ v1_funct_1(X2809) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_5,plain,(
    ! [X2737] :
      ( v1_relat_1(k6_relat_1(X2737))
      & v1_funct_1(k6_relat_1(X2737)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_6,plain,(
    ! [X2226] : v1_relat_1(k6_relat_1(X2226)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    inference(assume_negation,[status(cth)],[t35_funct_1])).

cnf(c_0_8,plain,
    ( k1_funct_1(X3,X1) = X1
    | ~ r2_hidden(X1,X2)
    | X3 != k6_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,
    ( r2_hidden(esk182_0,esk183_0)
    & k1_funct_1(k6_relat_1(esk183_0),esk182_0) != esk182_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( k1_funct_1(k6_relat_1(X1),X2) = X2
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk182_0,esk183_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( k1_funct_1(k6_relat_1(esk183_0),esk182_0) != esk182_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
