%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1217+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:55 EST 2020

% Result     : Theorem 8.55s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 682 expanded)
%              Number of clauses        :   64 ( 223 expanded)
%              Number of leaves         :   16 ( 171 expanded)
%              Depth                    :   11
%              Number of atoms          :  480 (4333 expanded)
%              Number of equality atoms :   30 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)
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

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(dt_k2_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(t47_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k7_lattices(X1,X2),X2) = k5_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattices)).

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

fof(cc4_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v15_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v13_lattices(X1)
          & v14_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).

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

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X29,X30,X31,X32] :
      ( v2_struct_0(X29)
      | ~ v7_lattices(X29)
      | ~ v8_lattices(X29)
      | ~ v9_lattices(X29)
      | ~ l3_lattices(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | ~ m1_subset_1(X32,u1_struct_0(X29))
      | ~ r1_lattices(X29,X30,X31)
      | r1_lattices(X29,k2_lattices(X29,X30,X32),k2_lattices(X29,X31,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_lattices])])])])).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ l3_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | m1_subset_1(k7_lattices(X17,X18),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

fof(c_0_19,plain,(
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

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v17_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & r3_lattices(esk1_0,esk2_0,esk3_0)
    & ~ r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_21,plain,(
    ! [X19] :
      ( ( l1_lattices(X19)
        | ~ l3_lattices(X19) )
      & ( l2_lattices(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X23,X24,X25] :
      ( ( ~ r3_lattices(X23,X24,X25)
        | r1_lattices(X23,X24,X25)
        | v2_struct_0(X23)
        | ~ v6_lattices(X23)
        | ~ v8_lattices(X23)
        | ~ v9_lattices(X23)
        | ~ l3_lattices(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23)) )
      & ( ~ r1_lattices(X23,X24,X25)
        | r3_lattices(X23,X24,X25)
        | v2_struct_0(X23)
        | ~ v6_lattices(X23)
        | ~ v8_lattices(X23)
        | ~ v9_lattices(X23)
        | ~ l3_lattices(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_31,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_32,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ v6_lattices(X20)
      | ~ l1_lattices(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | k4_lattices(X20,X21,X22) = k2_lattices(X20,X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

fof(c_0_33,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v6_lattices(X8)
      | ~ l1_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | k4_lattices(X8,X9,X10) = k4_lattices(X8,X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_34,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( r1_lattices(X1,k2_lattices(X1,X2,k7_lattices(X1,X3)),k2_lattices(X1,X4,k7_lattices(X1,X3)))
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v7_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( v7_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_40,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( l1_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

fof(c_0_47,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v6_lattices(X14)
      | ~ l1_lattices(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k4_lattices(X14,X15,X16),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

fof(c_0_48,plain,(
    ! [X11,X12,X13] :
      ( v2_struct_0(X11)
      | ~ l1_lattices(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | m1_subset_1(k2_lattices(X11,X12,X13),u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).

cnf(c_0_49,negated_conjecture,
    ( r1_lattices(esk1_0,k2_lattices(esk1_0,X1,k7_lattices(esk1_0,X2)),k2_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X2)))
    | ~ r1_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_26])]),c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_36]),c_0_42]),c_0_26])]),c_0_27]),c_0_37]),c_0_38]),c_0_43])])).

cnf(c_0_51,plain,
    ( k2_lattices(X1,X2,k7_lattices(X1,X3)) = k4_lattices(X1,X2,k7_lattices(X1,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_23]),c_0_34])).

fof(c_0_52,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v10_lattices(X35)
      | ~ v17_lattices(X35)
      | ~ l3_lattices(X35)
      | ~ m1_subset_1(X36,u1_struct_0(X35))
      | k4_lattices(X35,k7_lattices(X35,X36),X36) = k5_lattices(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattices])])])])).

cnf(c_0_53,negated_conjecture,
    ( k4_lattices(esk1_0,X1,esk3_0) = k4_lattices(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_36]),c_0_27]),c_0_46]),c_0_43])])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_55,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ v10_lattices(X33)
      | ~ v13_lattices(X33)
      | ~ l3_lattices(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | r3_lattices(X33,k5_lattices(X33),X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattices])])])])).

fof(c_0_56,plain,(
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

fof(c_0_57,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v4_lattices(X26)
      | ~ l2_lattices(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | ~ r1_lattices(X26,X27,X28)
      | ~ r1_lattices(X26,X28,X27)
      | X27 = X28 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattices(esk1_0,k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1)),k2_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_42]),c_0_50])])).

cnf(c_0_60,negated_conjecture,
    ( k2_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1)) = k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_36]),c_0_43]),c_0_26])]),c_0_27])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),X2) = k5_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0) = k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_23]),c_0_26])]),c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,X1,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_36]),c_0_27]),c_0_46]),c_0_43])])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,k5_lattices(X1),X2)
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_66,plain,(
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

cnf(c_0_67,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_68,plain,(
    ! [X37,X38,X39] :
      ( ( k4_lattices(X37,X38,X39) != k5_lattices(X37)
        | r3_lattices(X37,X38,k7_lattices(X37,X39))
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v17_lattices(X37)
        | ~ l3_lattices(X37) )
      & ( ~ r3_lattices(X37,X38,k7_lattices(X37,X39))
        | k4_lattices(X37,X38,X39) = k5_lattices(X37)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v17_lattices(X37)
        | ~ l3_lattices(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_lattices])])])])])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( m1_subset_1(k2_lattices(X1,X2,k7_lattices(X1,X3)),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_23]),c_0_34])).

cnf(c_0_71,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattices(esk1_0,k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1)),k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk3_0)) = k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_36]),c_0_63]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_61]),c_0_36]),c_0_63]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_75,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_76,plain,
    ( r1_lattices(X1,k5_lattices(X1),X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_65]),c_0_31]),c_0_28]),c_0_24])).

cnf(c_0_77,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( v15_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_63]),c_0_26])]),c_0_27])).

cnf(c_0_79,negated_conjecture,
    ( ~ r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_80,plain,
    ( r3_lattices(X1,X2,k7_lattices(X1,X3))
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_81,plain,
    ( X1 = k2_lattices(X2,X3,k7_lattices(X2,X4))
    | v2_struct_0(X2)
    | ~ r1_lattices(X2,k2_lattices(X2,X3,k7_lattices(X2,X4)),X1)
    | ~ r1_lattices(X2,X1,k2_lattices(X2,X3,k7_lattices(X2,X4)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v4_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( r1_lattices(esk1_0,k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k5_lattices(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_36])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_23]),c_0_36]),c_0_26])]),c_0_27])).

cnf(c_0_84,negated_conjecture,
    ( v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_85,plain,
    ( r1_lattices(X1,k5_lattices(X1),k2_lattices(X1,X2,k7_lattices(X1,X3)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( v13_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_26]),c_0_27]),c_0_78])])).

cnf(c_0_87,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) != k5_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_42]),c_0_63]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_88,negated_conjecture,
    ( k4_lattices(esk1_0,X1,esk2_0) = k4_lattices(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_27]),c_0_46]),c_0_43])])).

cnf(c_0_89,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) = k5_lattices(esk1_0)
    | ~ r1_lattices(esk1_0,k5_lattices(esk1_0),k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_42]),c_0_36]),c_0_84]),c_0_26])]),c_0_27])).

cnf(c_0_90,negated_conjecture,
    ( r1_lattices(esk1_0,k5_lattices(esk1_0),k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_42]),c_0_83]),c_0_86]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_91,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) != k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_23]),c_0_36]),c_0_26])]),c_0_27])).

cnf(c_0_92,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0) = k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_23]),c_0_26])]),c_0_27])).

cnf(c_0_93,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1)) = k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_42]),c_0_43]),c_0_26])]),c_0_27])).

cnf(c_0_94,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) = k5_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_36])])).

cnf(c_0_95,negated_conjecture,
    ( k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) != k5_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_36])])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_36])]),c_0_95]),
    [proof]).

%------------------------------------------------------------------------------
