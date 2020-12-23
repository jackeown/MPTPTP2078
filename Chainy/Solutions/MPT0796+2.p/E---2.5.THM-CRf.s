%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0796+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   19 (  26 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   54 (  67 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r4_wellord1(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_wellord1)).

fof(t47_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_wellord1)).

fof(d8_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
          <=> ? [X3] :
                ( v1_relat_1(X3)
                & v1_funct_1(X3)
                & r3_wellord1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',fc3_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',dt_k6_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => r4_wellord1(X1,X1) ) ),
    inference(assume_negation,[status(cth)],[t48_wellord1])).

fof(c_0_6,plain,(
    ! [X3520] :
      ( ~ v1_relat_1(X3520)
      | r3_wellord1(X3520,X3520,k6_relat_1(k3_relat_1(X3520))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_wellord1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk288_0)
    & ~ r4_wellord1(esk288_0,esk288_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X3378,X3379,X3381] :
      ( ( v1_relat_1(esk265_2(X3378,X3379))
        | ~ r4_wellord1(X3378,X3379)
        | ~ v1_relat_1(X3379)
        | ~ v1_relat_1(X3378) )
      & ( v1_funct_1(esk265_2(X3378,X3379))
        | ~ r4_wellord1(X3378,X3379)
        | ~ v1_relat_1(X3379)
        | ~ v1_relat_1(X3378) )
      & ( r3_wellord1(X3378,X3379,esk265_2(X3378,X3379))
        | ~ r4_wellord1(X3378,X3379)
        | ~ v1_relat_1(X3379)
        | ~ v1_relat_1(X3378) )
      & ( ~ v1_relat_1(X3381)
        | ~ v1_funct_1(X3381)
        | ~ r3_wellord1(X3378,X3379,X3381)
        | r4_wellord1(X3378,X3379)
        | ~ v1_relat_1(X3379)
        | ~ v1_relat_1(X3378) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).

cnf(c_0_9,plain,
    ( r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk288_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X2797] :
      ( v1_relat_1(k6_relat_1(X2797))
      & v1_funct_1(k6_relat_1(X2797)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_12,plain,(
    ! [X2226] : v1_relat_1(k6_relat_1(X2226)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_13,plain,
    ( r4_wellord1(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r3_wellord1(esk288_0,esk288_0,k6_relat_1(k3_relat_1(esk288_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ r4_wellord1(esk288_0,esk288_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_10]),c_0_16])]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
