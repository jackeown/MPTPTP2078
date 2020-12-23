%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0755+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:08 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   27 (  58 expanded)
%              Number of clauses        :   16 (  20 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  107 ( 354 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_ordinal1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v5_ordinal1(X2) )
     => ! [X3] :
          ( v3_ordinal1(X3)
         => ( v1_relat_1(k7_relat_1(X2,X3))
            & v5_relat_1(k7_relat_1(X2,X3),X1)
            & v1_funct_1(k7_relat_1(X2,X3))
            & v5_ordinal1(k7_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_ordinal1)).

fof(fc5_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v5_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v5_relat_1(k7_relat_1(X1,X2),k2_relat_1(X1))
        & v5_ordinal1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_ordinal1)).

fof(fc22_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v5_relat_1(X3,X2) )
     => ( v1_relat_1(k7_relat_1(X3,X1))
        & v5_relat_1(k7_relat_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v5_relat_1(X2,X1)
          & v1_funct_1(X2)
          & v5_ordinal1(X2) )
       => ! [X3] :
            ( v3_ordinal1(X3)
           => ( v1_relat_1(k7_relat_1(X2,X3))
              & v5_relat_1(k7_relat_1(X2,X3),X1)
              & v1_funct_1(k7_relat_1(X2,X3))
              & v5_ordinal1(k7_relat_1(X2,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_ordinal1])).

fof(c_0_6,plain,(
    ! [X9,X10] :
      ( ( v1_relat_1(k7_relat_1(X9,X10))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v5_ordinal1(X9)
        | ~ v3_ordinal1(X10) )
      & ( v5_relat_1(k7_relat_1(X9,X10),k2_relat_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v5_ordinal1(X9)
        | ~ v3_ordinal1(X10) )
      & ( v5_ordinal1(k7_relat_1(X9,X10))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v5_ordinal1(X9)
        | ~ v3_ordinal1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_ordinal1])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v5_relat_1(esk2_0,esk1_0)
    & v1_funct_1(esk2_0)
    & v5_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & ( ~ v1_relat_1(k7_relat_1(esk2_0,esk3_0))
      | ~ v5_relat_1(k7_relat_1(esk2_0,esk3_0),esk1_0)
      | ~ v1_funct_1(k7_relat_1(esk2_0,esk3_0))
      | ~ v5_ordinal1(k7_relat_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ( v1_relat_1(k7_relat_1(X8,X6))
        | ~ v1_relat_1(X8)
        | ~ v5_relat_1(X8,X7) )
      & ( v5_relat_1(k7_relat_1(X8,X6),X7)
        | ~ v1_relat_1(X8)
        | ~ v5_relat_1(X8,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc22_relat_1])])])).

cnf(c_0_9,plain,
    ( v5_ordinal1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v5_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk2_0,esk3_0))
    | ~ v5_relat_1(k7_relat_1(esk2_0,esk3_0),esk1_0)
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk3_0))
    | ~ v5_ordinal1(k7_relat_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v5_relat_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v5_ordinal1(k7_relat_1(X1,esk3_0))
    | ~ v5_ordinal1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v5_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( ~ v5_ordinal1(k7_relat_1(esk2_0,esk3_0))
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk3_0))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_19,negated_conjecture,
    ( v5_ordinal1(k7_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_14])])).

fof(c_0_20,plain,(
    ! [X11,X12] :
      ( ( v1_relat_1(k7_relat_1(X11,X12))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( v1_funct_1(k7_relat_1(X11,X12))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk2_0,esk3_0))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_22,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | v1_relat_1(k7_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17]),c_0_14])])).

cnf(c_0_25,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_14])]),
    [proof]).

%------------------------------------------------------------------------------
