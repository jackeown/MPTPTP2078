%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:59 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 355 expanded)
%              Number of clauses        :   55 ( 117 expanded)
%              Number of leaves         :   10 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  278 (2006 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t8_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,k3_relat_1(X1))
      <=> v2_wellord1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).

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

fof(d5_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_wellord1(X1,X2)
        <=> ( r1_relat_2(X1,X2)
            & r8_relat_2(X1,X2)
            & r4_relat_2(X1,X2)
            & r6_relat_2(X1,X2)
            & r1_wellord1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).

fof(t5_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
      <=> r1_wellord1(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).

fof(d9_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> r1_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).

fof(d16_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> r8_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).

fof(d14_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> r6_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).

fof(d12_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> r4_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
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

fof(c_0_11,plain,(
    ! [X14] :
      ( ( ~ r2_wellord1(X14,k3_relat_1(X14))
        | v2_wellord1(X14)
        | ~ v1_relat_1(X14) )
      & ( ~ v2_wellord1(X14)
        | r2_wellord1(X14,k3_relat_1(X14))
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord1])])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v2_wellord1(esk1_0)
    & r3_wellord1(esk1_0,esk2_0,esk3_0)
    & ~ v2_wellord1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => epred1_2(X2,X1) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t53_wellord1,c_0_10])).

fof(c_0_14,plain,(
    ! [X7,X8] :
      ( ( r1_relat_2(X7,X8)
        | ~ r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r8_relat_2(X7,X8)
        | ~ r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r4_relat_2(X7,X8)
        | ~ r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r6_relat_2(X7,X8)
        | ~ r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r1_wellord1(X7,X8)
        | ~ r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r1_relat_2(X7,X8)
        | ~ r8_relat_2(X7,X8)
        | ~ r4_relat_2(X7,X8)
        | ~ r6_relat_2(X7,X8)
        | ~ r1_wellord1(X7,X8)
        | r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_wellord1])])])])).

cnf(c_0_15,plain,
    ( r2_wellord1(X1,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v2_wellord1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ r3_wellord1(X10,X11,X12)
      | epred1_2(X11,X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_20,plain,(
    ! [X13] :
      ( ( ~ v1_wellord1(X13)
        | r1_wellord1(X13,k3_relat_1(X13))
        | ~ v1_relat_1(X13) )
      & ( ~ r1_wellord1(X13,k3_relat_1(X13))
        | v1_wellord1(X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_wellord1])])])).

cnf(c_0_21,plain,
    ( r1_wellord1(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_wellord1(esk1_0,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_23,plain,(
    ! [X9] :
      ( ( ~ v1_relat_2(X9)
        | r1_relat_2(X9,k3_relat_1(X9))
        | ~ v1_relat_1(X9) )
      & ( ~ r1_relat_2(X9,k3_relat_1(X9))
        | v1_relat_2(X9)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_relat_2])])])).

cnf(c_0_24,plain,
    ( r1_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X6] :
      ( ( ~ v8_relat_2(X6)
        | r8_relat_2(X6,k3_relat_1(X6))
        | ~ v1_relat_1(X6) )
      & ( ~ r8_relat_2(X6,k3_relat_1(X6))
        | v8_relat_2(X6)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_2])])])).

cnf(c_0_26,plain,
    ( r8_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_27,plain,(
    ! [X5] :
      ( ( ~ v6_relat_2(X5)
        | r6_relat_2(X5,k3_relat_1(X5))
        | ~ v1_relat_1(X5) )
      & ( ~ r6_relat_2(X5,k3_relat_1(X5))
        | v6_relat_2(X5)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_2])])])).

cnf(c_0_28,plain,
    ( r6_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_29,plain,(
    ! [X4] :
      ( ( ~ v4_relat_2(X4)
        | r4_relat_2(X4,k3_relat_1(X4))
        | ~ v1_relat_1(X4) )
      & ( ~ r4_relat_2(X4,k3_relat_1(X4))
        | v4_relat_2(X4)
        | ~ v1_relat_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_2])])])).

cnf(c_0_30,plain,
    ( r4_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_31,plain,(
    ! [X18,X19] :
      ( ( ~ v1_relat_2(X18)
        | v1_relat_2(X19)
        | ~ epred1_2(X19,X18) )
      & ( ~ v8_relat_2(X18)
        | v8_relat_2(X19)
        | ~ epred1_2(X19,X18) )
      & ( ~ v6_relat_2(X18)
        | v6_relat_2(X19)
        | ~ epred1_2(X19,X18) )
      & ( ~ v4_relat_2(X18)
        | v4_relat_2(X19)
        | ~ epred1_2(X19,X18) )
      & ( ~ v1_wellord1(X18)
        | v1_wellord1(X19)
        | ~ epred1_2(X19,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_32,plain,
    ( epred1_2(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r3_wellord1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( r3_wellord1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,plain,
    ( v1_wellord1(X1)
    | ~ r1_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( r1_wellord1(esk1_0,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])])).

cnf(c_0_39,plain,
    ( v1_relat_2(X1)
    | ~ r1_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( r1_relat_2(esk1_0,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_17])])).

cnf(c_0_41,plain,
    ( v8_relat_2(X1)
    | ~ r8_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( r8_relat_2(esk1_0,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_22]),c_0_17])])).

cnf(c_0_43,plain,
    ( v6_relat_2(X1)
    | ~ r6_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( r6_relat_2(esk1_0,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_17])])).

cnf(c_0_45,plain,
    ( v4_relat_2(X1)
    | ~ r4_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( r4_relat_2(esk1_0,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_17])])).

cnf(c_0_47,plain,
    ( v1_wellord1(X2)
    | ~ v1_wellord1(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( epred1_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_17])])).

cnf(c_0_49,negated_conjecture,
    ( v1_wellord1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_17])])).

cnf(c_0_50,plain,
    ( v1_relat_2(X2)
    | ~ v1_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_17])])).

cnf(c_0_52,plain,
    ( v8_relat_2(X2)
    | ~ v8_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( v8_relat_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_17])])).

cnf(c_0_54,plain,
    ( v6_relat_2(X2)
    | ~ v6_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( v6_relat_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_17])])).

cnf(c_0_56,plain,
    ( v4_relat_2(X2)
    | ~ v4_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( v4_relat_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_17])])).

cnf(c_0_58,plain,
    ( r1_wellord1(X1,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_59,plain,
    ( v1_wellord1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_60,plain,
    ( r1_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_61,plain,
    ( v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_48]),c_0_51])])).

cnf(c_0_62,plain,
    ( r8_relat_2(X1,k3_relat_1(X1))
    | ~ v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_63,plain,
    ( v8_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_53])])).

cnf(c_0_64,plain,
    ( r6_relat_2(X1,k3_relat_1(X1))
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_65,plain,
    ( v6_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_48]),c_0_55])])).

cnf(c_0_66,plain,
    ( r4_relat_2(X1,k3_relat_1(X1))
    | ~ v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_67,plain,
    ( v4_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_48]),c_0_57])])).

cnf(c_0_68,plain,
    ( r2_wellord1(X1,X2)
    | ~ r1_relat_2(X1,X2)
    | ~ r8_relat_2(X1,X2)
    | ~ r4_relat_2(X1,X2)
    | ~ r6_relat_2(X1,X2)
    | ~ r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_69,plain,
    ( r1_wellord1(esk2_0,k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_36])])).

cnf(c_0_70,plain,
    ( r1_relat_2(esk2_0,k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_36])])).

cnf(c_0_71,plain,
    ( r8_relat_2(esk2_0,k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_36])])).

cnf(c_0_72,plain,
    ( r6_relat_2(esk2_0,k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_36])])).

cnf(c_0_73,plain,
    ( r4_relat_2(esk2_0,k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_36])])).

cnf(c_0_74,plain,
    ( v2_wellord1(X1)
    | ~ r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_75,plain,
    ( r2_wellord1(esk2_0,k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71]),c_0_72]),c_0_73]),c_0_36])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_77,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_36])]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:15:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S048A
% 0.14/0.37  # and selection function SelectComplexPreferEQ.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.028 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t54_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((v2_wellord1(X1)&r3_wellord1(X1,X2,X3))=>v2_wellord1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_wellord1)).
% 0.14/0.37  fof(t8_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(r2_wellord1(X1,k3_relat_1(X1))<=>v2_wellord1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord1)).
% 0.14/0.37  fof(t53_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)=>(((((v1_relat_2(X1)=>v1_relat_2(X2))&(v8_relat_2(X1)=>v8_relat_2(X2)))&(v6_relat_2(X1)=>v6_relat_2(X2)))&(v4_relat_2(X1)=>v4_relat_2(X2)))&(v1_wellord1(X1)=>v1_wellord1(X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_wellord1)).
% 0.14/0.37  fof(d5_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r2_wellord1(X1,X2)<=>((((r1_relat_2(X1,X2)&r8_relat_2(X1,X2))&r4_relat_2(X1,X2))&r6_relat_2(X1,X2))&r1_wellord1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_wellord1)).
% 0.14/0.37  fof(t5_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_wellord1(X1)<=>r1_wellord1(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_wellord1)).
% 0.14/0.37  fof(d9_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>r1_relat_2(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_relat_2)).
% 0.14/0.37  fof(d16_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>r8_relat_2(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_2)).
% 0.14/0.37  fof(d14_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>r6_relat_2(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_2)).
% 0.14/0.37  fof(d12_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>(v4_relat_2(X1)<=>r4_relat_2(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_2)).
% 0.14/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((v2_wellord1(X1)&r3_wellord1(X1,X2,X3))=>v2_wellord1(X2)))))), inference(assume_negation,[status(cth)],[t54_wellord1])).
% 0.14/0.37  fof(c_0_10, plain, ![X1, X2]:(epred1_2(X2,X1)<=>(((((v1_relat_2(X1)=>v1_relat_2(X2))&(v8_relat_2(X1)=>v8_relat_2(X2)))&(v6_relat_2(X1)=>v6_relat_2(X2)))&(v4_relat_2(X1)=>v4_relat_2(X2)))&(v1_wellord1(X1)=>v1_wellord1(X2)))), introduced(definition)).
% 0.14/0.37  fof(c_0_11, plain, ![X14]:((~r2_wellord1(X14,k3_relat_1(X14))|v2_wellord1(X14)|~v1_relat_1(X14))&(~v2_wellord1(X14)|r2_wellord1(X14,k3_relat_1(X14))|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord1])])])).
% 0.14/0.37  fof(c_0_12, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v2_wellord1(esk1_0)&r3_wellord1(esk1_0,esk2_0,esk3_0))&~v2_wellord1(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.37  fof(c_0_13, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)=>epred1_2(X2,X1))))), inference(apply_def,[status(thm)],[t53_wellord1, c_0_10])).
% 0.14/0.37  fof(c_0_14, plain, ![X7, X8]:((((((r1_relat_2(X7,X8)|~r2_wellord1(X7,X8)|~v1_relat_1(X7))&(r8_relat_2(X7,X8)|~r2_wellord1(X7,X8)|~v1_relat_1(X7)))&(r4_relat_2(X7,X8)|~r2_wellord1(X7,X8)|~v1_relat_1(X7)))&(r6_relat_2(X7,X8)|~r2_wellord1(X7,X8)|~v1_relat_1(X7)))&(r1_wellord1(X7,X8)|~r2_wellord1(X7,X8)|~v1_relat_1(X7)))&(~r1_relat_2(X7,X8)|~r8_relat_2(X7,X8)|~r4_relat_2(X7,X8)|~r6_relat_2(X7,X8)|~r1_wellord1(X7,X8)|r2_wellord1(X7,X8)|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_wellord1])])])])).
% 0.14/0.37  cnf(c_0_15, plain, (r2_wellord1(X1,k3_relat_1(X1))|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (v2_wellord1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  fof(c_0_18, plain, ![X1, X2]:(epred1_2(X2,X1)=>(((((v1_relat_2(X1)=>v1_relat_2(X2))&(v8_relat_2(X1)=>v8_relat_2(X2)))&(v6_relat_2(X1)=>v6_relat_2(X2)))&(v4_relat_2(X1)=>v4_relat_2(X2)))&(v1_wellord1(X1)=>v1_wellord1(X2)))), inference(split_equiv,[status(thm)],[c_0_10])).
% 0.14/0.37  fof(c_0_19, plain, ![X10, X11, X12]:(~v1_relat_1(X10)|(~v1_relat_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12)|(~r3_wellord1(X10,X11,X12)|epred1_2(X11,X10))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.14/0.37  fof(c_0_20, plain, ![X13]:((~v1_wellord1(X13)|r1_wellord1(X13,k3_relat_1(X13))|~v1_relat_1(X13))&(~r1_wellord1(X13,k3_relat_1(X13))|v1_wellord1(X13)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_wellord1])])])).
% 0.14/0.37  cnf(c_0_21, plain, (r1_wellord1(X1,X2)|~r2_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (r2_wellord1(esk1_0,k3_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.14/0.37  fof(c_0_23, plain, ![X9]:((~v1_relat_2(X9)|r1_relat_2(X9,k3_relat_1(X9))|~v1_relat_1(X9))&(~r1_relat_2(X9,k3_relat_1(X9))|v1_relat_2(X9)|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_relat_2])])])).
% 0.14/0.37  cnf(c_0_24, plain, (r1_relat_2(X1,X2)|~r2_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  fof(c_0_25, plain, ![X6]:((~v8_relat_2(X6)|r8_relat_2(X6,k3_relat_1(X6))|~v1_relat_1(X6))&(~r8_relat_2(X6,k3_relat_1(X6))|v8_relat_2(X6)|~v1_relat_1(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_2])])])).
% 0.14/0.37  cnf(c_0_26, plain, (r8_relat_2(X1,X2)|~r2_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  fof(c_0_27, plain, ![X5]:((~v6_relat_2(X5)|r6_relat_2(X5,k3_relat_1(X5))|~v1_relat_1(X5))&(~r6_relat_2(X5,k3_relat_1(X5))|v6_relat_2(X5)|~v1_relat_1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_2])])])).
% 0.14/0.37  cnf(c_0_28, plain, (r6_relat_2(X1,X2)|~r2_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  fof(c_0_29, plain, ![X4]:((~v4_relat_2(X4)|r4_relat_2(X4,k3_relat_1(X4))|~v1_relat_1(X4))&(~r4_relat_2(X4,k3_relat_1(X4))|v4_relat_2(X4)|~v1_relat_1(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_2])])])).
% 0.14/0.37  cnf(c_0_30, plain, (r4_relat_2(X1,X2)|~r2_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  fof(c_0_31, plain, ![X18, X19]:(((((~v1_relat_2(X18)|v1_relat_2(X19)|~epred1_2(X19,X18))&(~v8_relat_2(X18)|v8_relat_2(X19)|~epred1_2(X19,X18)))&(~v6_relat_2(X18)|v6_relat_2(X19)|~epred1_2(X19,X18)))&(~v4_relat_2(X18)|v4_relat_2(X19)|~epred1_2(X19,X18)))&(~v1_wellord1(X18)|v1_wellord1(X19)|~epred1_2(X19,X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.14/0.37  cnf(c_0_32, plain, (epred1_2(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)|~r3_wellord1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (r3_wellord1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_37, plain, (v1_wellord1(X1)|~r1_wellord1(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_38, negated_conjecture, (r1_wellord1(esk1_0,k3_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_17])])).
% 0.14/0.37  cnf(c_0_39, plain, (v1_relat_2(X1)|~r1_relat_2(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_40, negated_conjecture, (r1_relat_2(esk1_0,k3_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_17])])).
% 0.14/0.37  cnf(c_0_41, plain, (v8_relat_2(X1)|~r8_relat_2(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (r8_relat_2(esk1_0,k3_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_22]), c_0_17])])).
% 0.14/0.37  cnf(c_0_43, plain, (v6_relat_2(X1)|~r6_relat_2(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (r6_relat_2(esk1_0,k3_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_22]), c_0_17])])).
% 0.14/0.37  cnf(c_0_45, plain, (v4_relat_2(X1)|~r4_relat_2(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.37  cnf(c_0_46, negated_conjecture, (r4_relat_2(esk1_0,k3_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_22]), c_0_17])])).
% 0.14/0.37  cnf(c_0_47, plain, (v1_wellord1(X2)|~v1_wellord1(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_48, negated_conjecture, (epred1_2(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_17])])).
% 0.14/0.37  cnf(c_0_49, negated_conjecture, (v1_wellord1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_17])])).
% 0.14/0.37  cnf(c_0_50, plain, (v1_relat_2(X2)|~v1_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_51, negated_conjecture, (v1_relat_2(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_17])])).
% 0.14/0.37  cnf(c_0_52, plain, (v8_relat_2(X2)|~v8_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_53, negated_conjecture, (v8_relat_2(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_17])])).
% 0.14/0.37  cnf(c_0_54, plain, (v6_relat_2(X2)|~v6_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_55, negated_conjecture, (v6_relat_2(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_17])])).
% 0.14/0.37  cnf(c_0_56, plain, (v4_relat_2(X2)|~v4_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_57, negated_conjecture, (v4_relat_2(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_17])])).
% 0.14/0.37  cnf(c_0_58, plain, (r1_wellord1(X1,k3_relat_1(X1))|~v1_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_59, plain, (v1_wellord1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.14/0.37  cnf(c_0_60, plain, (r1_relat_2(X1,k3_relat_1(X1))|~v1_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_61, plain, (v1_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_48]), c_0_51])])).
% 0.14/0.37  cnf(c_0_62, plain, (r8_relat_2(X1,k3_relat_1(X1))|~v8_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_63, plain, (v8_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_48]), c_0_53])])).
% 0.14/0.37  cnf(c_0_64, plain, (r6_relat_2(X1,k3_relat_1(X1))|~v6_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.37  cnf(c_0_65, plain, (v6_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_48]), c_0_55])])).
% 0.14/0.37  cnf(c_0_66, plain, (r4_relat_2(X1,k3_relat_1(X1))|~v4_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.37  cnf(c_0_67, plain, (v4_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_48]), c_0_57])])).
% 0.14/0.37  cnf(c_0_68, plain, (r2_wellord1(X1,X2)|~r1_relat_2(X1,X2)|~r8_relat_2(X1,X2)|~r4_relat_2(X1,X2)|~r6_relat_2(X1,X2)|~r1_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_69, plain, (r1_wellord1(esk2_0,k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_36])])).
% 0.14/0.37  cnf(c_0_70, plain, (r1_relat_2(esk2_0,k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_36])])).
% 0.14/0.37  cnf(c_0_71, plain, (r8_relat_2(esk2_0,k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_36])])).
% 0.14/0.37  cnf(c_0_72, plain, (r6_relat_2(esk2_0,k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_36])])).
% 0.14/0.37  cnf(c_0_73, plain, (r4_relat_2(esk2_0,k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_36])])).
% 0.14/0.37  cnf(c_0_74, plain, (v2_wellord1(X1)|~r2_wellord1(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_75, plain, (r2_wellord1(esk2_0,k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71]), c_0_72]), c_0_73]), c_0_36])])).
% 0.14/0.37  cnf(c_0_76, negated_conjecture, (~v2_wellord1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_77, plain, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_36])]), c_0_76]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 78
% 0.14/0.37  # Proof object clause steps            : 55
% 0.14/0.37  # Proof object formula steps           : 23
% 0.14/0.37  # Proof object conjectures             : 22
% 0.14/0.37  # Proof object clause conjectures      : 19
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 31
% 0.14/0.37  # Proof object initial formulas used   : 9
% 0.14/0.37  # Proof object generating inferences   : 24
% 0.14/0.37  # Proof object simplifying inferences  : 56
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 9
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 31
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 31
% 0.14/0.37  # Processed clauses                    : 85
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 85
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 41
% 0.14/0.37  # ...of the previous two non-trivial   : 23
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 41
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 54
% 0.14/0.37  #    Positive orientable unit clauses  : 29
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 24
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 31
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 56
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 56
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 4
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 2639
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.030 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.034 s
% 0.14/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
