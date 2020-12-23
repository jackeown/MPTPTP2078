%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1217+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:55 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   97 (1185 expanded)
%              Number of clauses        :   66 ( 390 expanded)
%              Number of leaves         :   15 ( 291 expanded)
%              Depth                    :   11
%              Number of atoms          :  446 (7475 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_lattices(X1,X2,X3)
               => r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(reflexivity_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_lattices(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(cc5_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v17_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(t52_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k4_lattices(X1,X2,X3) = k5_lattices(X1)
              <=> r3_lattices(X1,X2,k7_lattices(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).

fof(cc4_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v15_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v13_lattices(X1)
          & v14_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(redefinition_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,X3)
      <=> r1_lattices(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(t41_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r3_lattices(X1,k5_lattices(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattices)).

fof(t27_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattices(X1,X2,X3)
                   => r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).

fof(t26_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattices(X1,X2,X3)
                  & r1_lattices(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v17_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r3_lattices(X1,X2,X3)
                 => r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_lattices])).

fof(c_0_16,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v4_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v5_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v6_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v8_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v9_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & v17_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & r3_lattices(esk2_0,esk3_0,esk4_0)
    & ~ r3_lattices(esk2_0,k7_lattices(esk2_0,esk4_0),k7_lattices(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X28,X29,X30] :
      ( v2_struct_0(X28)
      | ~ v6_lattices(X28)
      | ~ v8_lattices(X28)
      | ~ v9_lattices(X28)
      | ~ l3_lattices(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | r3_lattices(X28,X29,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

cnf(c_0_19,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ l3_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | m1_subset_1(k7_lattices(X17,X18),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

fof(c_0_26,plain,(
    ! [X19] :
      ( ( l1_lattices(X19)
        | ~ l3_lattices(X19) )
      & ( l2_lattices(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v9_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v8_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( v6_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v6_lattices(X14)
      | ~ l1_lattices(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k4_lattices(X14,X15,X16),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_34,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X7] :
      ( ( ~ v2_struct_0(X7)
        | v2_struct_0(X7)
        | ~ v17_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v11_lattices(X7)
        | v2_struct_0(X7)
        | ~ v17_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v15_lattices(X7)
        | v2_struct_0(X7)
        | ~ v17_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v16_lattices(X7)
        | v2_struct_0(X7)
        | ~ v17_lattices(X7)
        | ~ l3_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).

fof(c_0_36,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v6_lattices(X8)
      | ~ l1_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | k4_lattices(X8,X9,X10) = k4_lattices(X8,X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

fof(c_0_37,plain,(
    ! [X40,X41,X42] :
      ( ( k4_lattices(X40,X41,X42) != k5_lattices(X40)
        | r3_lattices(X40,X41,k7_lattices(X40,X42))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v17_lattices(X40)
        | ~ l3_lattices(X40) )
      & ( ~ r3_lattices(X40,X41,k7_lattices(X40,X42))
        | k4_lattices(X40,X41,X42) = k5_lattices(X40)
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v17_lattices(X40)
        | ~ l3_lattices(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_lattices])])])])])).

cnf(c_0_38,negated_conjecture,
    ( r3_lattices(esk2_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_21])]),c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk2_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_21])]),c_0_22])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( l1_lattices(esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

fof(c_0_42,plain,(
    ! [X6] :
      ( ( ~ v2_struct_0(X6)
        | v2_struct_0(X6)
        | ~ v15_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v13_lattices(X6)
        | v2_struct_0(X6)
        | ~ v15_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v14_lattices(X6)
        | v2_struct_0(X6)
        | ~ v15_lattices(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_lattices])])])])).

cnf(c_0_43,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v17_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_45,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ v6_lattices(X22)
      | ~ l1_lattices(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | k4_lattices(X22,X23,X24) = k2_lattices(X22,X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k4_lattices(X1,X2,X3) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,k7_lattices(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r3_lattices(esk2_0,k7_lattices(esk2_0,esk4_0),k7_lattices(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk2_0,X1,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_41]),c_0_31])]),c_0_22])).

fof(c_0_50,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r3_lattices(X25,X26,X27)
        | r1_lattices(X25,X26,X27)
        | v2_struct_0(X25)
        | ~ v6_lattices(X25)
        | ~ v8_lattices(X25)
        | ~ v9_lattices(X25)
        | ~ l3_lattices(X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X25)) )
      & ( ~ r1_lattices(X25,X26,X27)
        | r3_lattices(X25,X26,X27)
        | v2_struct_0(X25)
        | ~ v6_lattices(X25)
        | ~ v8_lattices(X25)
        | ~ v9_lattices(X25)
        | ~ l3_lattices(X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk2_0,X1,k7_lattices(esk2_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_41]),c_0_31])]),c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_53,plain,(
    ! [X38,X39] :
      ( v2_struct_0(X38)
      | ~ v10_lattices(X38)
      | ~ v13_lattices(X38)
      | ~ l3_lattices(X38)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | r3_lattices(X38,k5_lattices(X38),X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattices])])])])).

cnf(c_0_54,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( v15_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_21])]),c_0_22])).

cnf(c_0_56,plain,
    ( r3_lattices(X1,X2,k7_lattices(X1,X3))
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_57,plain,(
    ! [X34,X35,X36,X37] :
      ( v2_struct_0(X34)
      | ~ v7_lattices(X34)
      | ~ v8_lattices(X34)
      | ~ v9_lattices(X34)
      | ~ l3_lattices(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ m1_subset_1(X36,u1_struct_0(X34))
      | ~ m1_subset_1(X37,u1_struct_0(X34))
      | ~ r1_lattices(X34,X35,X36)
      | r1_lattices(X34,k2_lattices(X34,X35,X37),k2_lattices(X34,X36,X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_lattices])])])])).

cnf(c_0_58,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( k4_lattices(esk2_0,X1,esk4_0) = k4_lattices(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_28]),c_0_41]),c_0_31])]),c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( k4_lattices(esk2_0,k7_lattices(esk2_0,esk4_0),esk4_0) = k5_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_28]),c_0_39]),c_0_44]),c_0_20]),c_0_21])]),c_0_22])).

fof(c_0_62,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v4_lattices(X31)
      | ~ l2_lattices(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | ~ r1_lattices(X31,X32,X33)
      | ~ r1_lattices(X31,X33,X32)
      | X32 = X33 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk2_0,k7_lattices(esk2_0,esk4_0),esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_39])).

cnf(c_0_64,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_65,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk2_0,esk3_0,k7_lattices(esk2_0,esk4_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,k5_lattices(X1),X2)
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( v13_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_21])]),c_0_22])).

cnf(c_0_70,negated_conjecture,
    ( r3_lattices(esk2_0,X1,k7_lattices(esk2_0,esk3_0))
    | k4_lattices(esk2_0,X1,esk3_0) != k5_lattices(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_52]),c_0_44]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_71,negated_conjecture,
    ( ~ r3_lattices(esk2_0,k7_lattices(esk2_0,esk4_0),k7_lattices(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_72,negated_conjecture,
    ( k4_lattices(esk2_0,X1,esk3_0) = k4_lattices(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_52]),c_0_41]),c_0_31])]),c_0_22])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))
    | ~ v7_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_74,negated_conjecture,
    ( v7_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_75,negated_conjecture,
    ( k2_lattices(esk2_0,X1,k7_lattices(esk2_0,esk4_0)) = k4_lattices(esk2_0,X1,k7_lattices(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_39]),c_0_41]),c_0_31])]),c_0_22])).

cnf(c_0_76,negated_conjecture,
    ( k4_lattices(esk2_0,esk4_0,k7_lattices(esk2_0,esk4_0)) = k5_lattices(esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_39]),c_0_61])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk2_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_61])).

cnf(c_0_79,negated_conjecture,
    ( l2_lattices(esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_21])).

cnf(c_0_80,negated_conjecture,
    ( v4_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_81,negated_conjecture,
    ( r1_lattices(esk2_0,X1,k4_lattices(esk2_0,esk3_0,k7_lattices(esk2_0,esk4_0)))
    | ~ r3_lattices(esk2_0,X1,k4_lattices(esk2_0,esk3_0,k7_lattices(esk2_0,esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_29]),c_0_30]),c_0_31]),c_0_21])]),c_0_22])).

cnf(c_0_82,negated_conjecture,
    ( r3_lattices(esk2_0,k5_lattices(esk2_0),k4_lattices(esk2_0,esk3_0,k7_lattices(esk2_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_67]),c_0_69]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( k4_lattices(esk2_0,k7_lattices(esk2_0,esk4_0),esk3_0) != k5_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_39]),c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( k4_lattices(esk2_0,k7_lattices(esk2_0,esk4_0),esk3_0) = k4_lattices(esk2_0,esk3_0,k7_lattices(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_39])).

cnf(c_0_85,negated_conjecture,
    ( r1_lattices(esk2_0,k2_lattices(esk2_0,X1,k7_lattices(esk2_0,esk4_0)),k2_lattices(esk2_0,X2,k7_lattices(esk2_0,esk4_0)))
    | ~ r1_lattices(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_39]),c_0_29]),c_0_30]),c_0_74]),c_0_21])]),c_0_22])).

cnf(c_0_86,negated_conjecture,
    ( k2_lattices(esk2_0,esk4_0,k7_lattices(esk2_0,esk4_0)) = k5_lattices(esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_28]),c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( r1_lattices(esk2_0,X1,esk4_0)
    | ~ r3_lattices(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_21])]),c_0_22])).

cnf(c_0_88,negated_conjecture,
    ( r3_lattices(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_89,negated_conjecture,
    ( X1 = k5_lattices(esk2_0)
    | ~ r1_lattices(esk2_0,k5_lattices(esk2_0),X1)
    | ~ r1_lattices(esk2_0,X1,k5_lattices(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80])]),c_0_22])).

cnf(c_0_90,negated_conjecture,
    ( r1_lattices(esk2_0,k5_lattices(esk2_0),k4_lattices(esk2_0,esk3_0,k7_lattices(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_78])])).

cnf(c_0_91,negated_conjecture,
    ( k4_lattices(esk2_0,esk3_0,k7_lattices(esk2_0,esk4_0)) != k5_lattices(esk2_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( r1_lattices(esk2_0,k2_lattices(esk2_0,X1,k7_lattices(esk2_0,esk4_0)),k5_lattices(esk2_0))
    | ~ r1_lattices(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_28]),c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( r1_lattices(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_52])])).

cnf(c_0_94,negated_conjecture,
    ( k2_lattices(esk2_0,esk3_0,k7_lattices(esk2_0,esk4_0)) = k4_lattices(esk2_0,esk3_0,k7_lattices(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_52])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_lattices(esk2_0,k4_lattices(esk2_0,esk3_0,k7_lattices(esk2_0,esk4_0)),k5_lattices(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_67])]),c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_52])]),c_0_95]),
    [proof]).

%------------------------------------------------------------------------------
