%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0796+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:12 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   17 (  26 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   52 (  69 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r4_wellord1(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_wellord1)).

fof(t47_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_wellord1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_wellord1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => r4_wellord1(X1,X1) ) ),
    inference(assume_negation,[status(cth)],[t48_wellord1])).

fof(c_0_5,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | r3_wellord1(X9,X9,k6_relat_1(k3_relat_1(X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_wellord1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ~ r4_wellord1(esk2_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X4,X5,X7] :
      ( ( v1_relat_1(esk1_2(X4,X5))
        | ~ r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) )
      & ( v1_funct_1(esk1_2(X4,X5))
        | ~ r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) )
      & ( r3_wellord1(X4,X5,esk1_2(X4,X5))
        | ~ r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) )
      & ( ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ r3_wellord1(X4,X5,X7)
        | r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).

cnf(c_0_8,plain,
    ( r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X8] :
      ( v1_relat_1(k6_relat_1(X8))
      & v1_funct_1(k6_relat_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_11,plain,
    ( r4_wellord1(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r3_wellord1(esk2_0,esk2_0,k6_relat_1(k3_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ r4_wellord1(esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_9]),c_0_14])]),c_0_15]),
    [proof]).

%------------------------------------------------------------------------------
