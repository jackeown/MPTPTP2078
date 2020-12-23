%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0802+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:12 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 227 expanded)
%              Number of clauses        :   31 (  69 expanded)
%              Number of leaves         :    4 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  181 (1451 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => ( ( v1_relat_2(X1)
                   => v1_relat_2(X2) )
                  & ( v8_relat_2(X1)
                   => v8_relat_2(X2) )
                  & ( v6_relat_2(X1)
                   => v6_relat_2(X2) )
                  & ( v4_relat_2(X1)
                   => v4_relat_2(X2) )
                  & ( v1_wellord1(X1)
                   => v1_wellord1(X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).

fof(t54_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( ( v2_wellord1(X1)
                  & r3_wellord1(X1,X2,X3) )
               => v2_wellord1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(c_0_3,plain,(
    ! [X1,X2] :
      ( epred1_2(X2,X1)
    <=> ( ( v1_relat_2(X1)
         => v1_relat_2(X2) )
        & ( v8_relat_2(X1)
         => v8_relat_2(X2) )
        & ( v6_relat_2(X1)
         => v6_relat_2(X2) )
        & ( v4_relat_2(X1)
         => v4_relat_2(X2) )
        & ( v1_wellord1(X1)
         => v1_wellord1(X2) ) ) ) ),
    introduced(definition)).

fof(c_0_4,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => epred1_2(X2,X1) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t53_wellord1,c_0_3])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( ( v2_wellord1(X1)
                    & r3_wellord1(X1,X2,X3) )
                 => v2_wellord1(X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t54_wellord1])).

fof(c_0_6,plain,(
    ! [X1,X2] :
      ( epred1_2(X2,X1)
     => ( ( v1_relat_2(X1)
         => v1_relat_2(X2) )
        & ( v8_relat_2(X1)
         => v8_relat_2(X2) )
        & ( v6_relat_2(X1)
         => v6_relat_2(X2) )
        & ( v4_relat_2(X1)
         => v4_relat_2(X2) )
        & ( v1_wellord1(X1)
         => v1_wellord1(X2) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_3])).

fof(c_0_7,plain,(
    ! [X5,X6,X7] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | ~ r3_wellord1(X5,X6,X7)
      | epred1_2(X6,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v2_wellord1(esk1_0)
    & r3_wellord1(esk1_0,esk2_0,esk3_0)
    & ~ v2_wellord1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X11,X12] :
      ( ( ~ v1_relat_2(X11)
        | v1_relat_2(X12)
        | ~ epred1_2(X12,X11) )
      & ( ~ v8_relat_2(X11)
        | v8_relat_2(X12)
        | ~ epred1_2(X12,X11) )
      & ( ~ v6_relat_2(X11)
        | v6_relat_2(X12)
        | ~ epred1_2(X12,X11) )
      & ( ~ v4_relat_2(X11)
        | v4_relat_2(X12)
        | ~ epred1_2(X12,X11) )
      & ( ~ v1_wellord1(X11)
        | v1_wellord1(X12)
        | ~ epred1_2(X12,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( epred1_2(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r3_wellord1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r3_wellord1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v1_wellord1(X2)
    | ~ v1_wellord1(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( epred1_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

fof(c_0_18,plain,(
    ! [X4] :
      ( ( v1_relat_2(X4)
        | ~ v2_wellord1(X4)
        | ~ v1_relat_1(X4) )
      & ( v8_relat_2(X4)
        | ~ v2_wellord1(X4)
        | ~ v1_relat_1(X4) )
      & ( v4_relat_2(X4)
        | ~ v2_wellord1(X4)
        | ~ v1_relat_1(X4) )
      & ( v6_relat_2(X4)
        | ~ v2_wellord1(X4)
        | ~ v1_relat_1(X4) )
      & ( v1_wellord1(X4)
        | ~ v2_wellord1(X4)
        | ~ v1_relat_1(X4) )
      & ( ~ v1_relat_2(X4)
        | ~ v8_relat_2(X4)
        | ~ v4_relat_2(X4)
        | ~ v6_relat_2(X4)
        | ~ v1_wellord1(X4)
        | v2_wellord1(X4)
        | ~ v1_relat_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

cnf(c_0_19,plain,
    ( v6_relat_2(X2)
    | ~ v6_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( v4_relat_2(X2)
    | ~ v4_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( v8_relat_2(X2)
    | ~ v8_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( v1_relat_2(X2)
    | ~ v1_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( v1_wellord1(esk2_0)
    | ~ v1_wellord1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v2_wellord1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( v6_relat_2(esk2_0)
    | ~ v6_relat_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_27,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( v4_relat_2(esk2_0)
    | ~ v4_relat_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_29,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( v8_relat_2(esk2_0)
    | ~ v8_relat_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_31,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( v1_relat_2(esk2_0)
    | ~ v1_relat_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_33,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
    ( v1_wellord1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_15])])).

cnf(c_0_36,plain,
    ( v6_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_25]),c_0_15])])).

cnf(c_0_37,plain,
    ( v4_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25]),c_0_15])])).

cnf(c_0_38,plain,
    ( v8_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_25]),c_0_15])])).

cnf(c_0_39,plain,
    ( v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_15])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_41,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_14])]),c_0_40]),
    [proof]).

%------------------------------------------------------------------------------
