%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:29 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 270 expanded)
%              Number of clauses        :   33 (  86 expanded)
%              Number of leaves         :    8 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  229 (1621 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(t51_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_lattices(X1,k3_lattices(X1,X2,X3)) = k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(t49_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k7_lattices(X1,k7_lattices(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_lattices)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X10] :
      ( ( l1_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( l2_lattices(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v17_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & r3_lattices(esk1_0,esk2_0,esk3_0)
    & ~ r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v4_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v5_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v6_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v7_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v8_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v9_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_12,plain,(
    ! [X5,X6,X7] :
      ( v2_struct_0(X5)
      | ~ v4_lattices(X5)
      | ~ l2_lattices(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | k3_lattices(X5,X6,X7) = k3_lattices(X5,X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_13,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X13,X14,X15] :
      ( v2_struct_0(X13)
      | ~ v10_lattices(X13)
      | ~ v17_lattices(X13)
      | ~ l3_lattices(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | k7_lattices(X13,k3_lattices(X13,X14,X15)) = k4_lattices(X13,k7_lattices(X13,X14),k7_lattices(X13,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_lattices])])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( l2_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_14])]),c_0_17])).

fof(c_0_23,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | m1_subset_1(k7_lattices(X8,X9),u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k3_lattices(X1,X2,X3)) = k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk3_0) = k3_lattices(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17]),c_0_21]),c_0_22])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ v10_lattices(X11)
      | ~ v17_lattices(X11)
      | ~ l3_lattices(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | k7_lattices(X11,k7_lattices(X11,X12)) = X12 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).

cnf(c_0_29,negated_conjecture,
    ( k7_lattices(esk1_0,k3_lattices(esk1_0,X1,X2)) = k4_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_16]),c_0_14])]),c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0) = k3_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_14])]),c_0_17])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k7_lattices(X1,X2)) = X2
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k7_lattices(esk1_0,k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0)) = k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,k7_lattices(esk1_0,X1)))
    | ~ m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_20])])).

cnf(c_0_33,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,X1)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_25]),c_0_16]),c_0_14])]),c_0_17])).

fof(c_0_34,plain,(
    ! [X16,X17,X18] :
      ( ( k4_lattices(X16,X17,X18) != k5_lattices(X16)
        | r3_lattices(X16,X17,k7_lattices(X16,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v17_lattices(X16)
        | ~ l3_lattices(X16) )
      & ( ~ r3_lattices(X16,X17,k7_lattices(X16,X18))
        | k4_lattices(X16,X17,X18) = k5_lattices(X16)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v17_lattices(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_lattices])])])])])).

cnf(c_0_35,negated_conjecture,
    ( k7_lattices(esk1_0,k3_lattices(esk1_0,X1,esk3_0)) = k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,X1))
    | ~ m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,plain,
    ( k4_lattices(X1,X2,X3) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,k7_lattices(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,X1)) = k4_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk3_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_35]),c_0_20])])).

cnf(c_0_38,negated_conjecture,
    ( k4_lattices(esk1_0,X1,k7_lattices(esk1_0,X2)) = k5_lattices(esk1_0)
    | ~ r3_lattices(esk1_0,X1,X2)
    | ~ m1_subset_1(k7_lattices(esk1_0,X2),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_25]),c_0_16]),c_0_14])]),c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( ~ r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,plain,
    ( r3_lattices(X1,X2,k7_lattices(X1,X3))
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),X1) = k4_lattices(esk1_0,X1,k7_lattices(esk1_0,esk3_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) = k5_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_20])])).

cnf(c_0_45,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) != k5_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_25]),c_0_40]),c_0_16]),c_0_14])]),c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),X1) = k4_lattices(esk1_0,X1,k7_lattices(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_27]),c_0_14])]),c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) = k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_20]),c_0_14])]),c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) != k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_27]),c_0_20]),c_0_14])]),c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_47]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:43:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.18/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.028 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t53_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)=>r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_lattices)).
% 0.18/0.36  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.18/0.36  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.18/0.36  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 0.18/0.36  fof(t51_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k7_lattices(X1,k3_lattices(X1,X2,X3))=k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_lattices)).
% 0.18/0.36  fof(dt_k7_lattices, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 0.18/0.36  fof(t49_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k7_lattices(X1,k7_lattices(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_lattices)).
% 0.18/0.36  fof(t52_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k4_lattices(X1,X2,X3)=k5_lattices(X1)<=>r3_lattices(X1,X2,k7_lattices(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_lattices)).
% 0.18/0.36  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)=>r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2))))))), inference(assume_negation,[status(cth)],[t53_lattices])).
% 0.18/0.36  fof(c_0_9, plain, ![X10]:((l1_lattices(X10)|~l3_lattices(X10))&(l2_lattices(X10)|~l3_lattices(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.18/0.36  fof(c_0_10, negated_conjecture, ((((~v2_struct_0(esk1_0)&v10_lattices(esk1_0))&v17_lattices(esk1_0))&l3_lattices(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(r3_lattices(esk1_0,esk2_0,esk3_0)&~r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.18/0.36  fof(c_0_11, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.18/0.36  fof(c_0_12, plain, ![X5, X6, X7]:(v2_struct_0(X5)|~v4_lattices(X5)|~l2_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))|k3_lattices(X5,X6,X7)=k3_lattices(X5,X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 0.18/0.36  cnf(c_0_13, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_14, negated_conjecture, (l3_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_15, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.36  cnf(c_0_16, negated_conjecture, (v10_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  fof(c_0_18, plain, ![X13, X14, X15]:(v2_struct_0(X13)|~v10_lattices(X13)|~v17_lattices(X13)|~l3_lattices(X13)|(~m1_subset_1(X14,u1_struct_0(X13))|(~m1_subset_1(X15,u1_struct_0(X13))|k7_lattices(X13,k3_lattices(X13,X14,X15))=k4_lattices(X13,k7_lattices(X13,X14),k7_lattices(X13,X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_lattices])])])])).
% 0.18/0.36  cnf(c_0_19, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_21, negated_conjecture, (l2_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (v4_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_14])]), c_0_17])).
% 0.18/0.36  fof(c_0_23, plain, ![X8, X9]:(v2_struct_0(X8)|~l3_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|m1_subset_1(k7_lattices(X8,X9),u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).
% 0.18/0.36  cnf(c_0_24, plain, (v2_struct_0(X1)|k7_lattices(X1,k3_lattices(X1,X2,X3))=k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.36  cnf(c_0_25, negated_conjecture, (v17_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_26, negated_conjecture, (k3_lattices(esk1_0,X1,esk3_0)=k3_lattices(esk1_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_17]), c_0_21]), c_0_22])])).
% 0.18/0.36  cnf(c_0_27, plain, (v2_struct_0(X1)|m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.36  fof(c_0_28, plain, ![X11, X12]:(v2_struct_0(X11)|~v10_lattices(X11)|~v17_lattices(X11)|~l3_lattices(X11)|(~m1_subset_1(X12,u1_struct_0(X11))|k7_lattices(X11,k7_lattices(X11,X12))=X12)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, (k7_lattices(esk1_0,k3_lattices(esk1_0,X1,X2))=k4_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,X2))|~m1_subset_1(X2,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_16]), c_0_14])]), c_0_17])).
% 0.18/0.36  cnf(c_0_30, negated_conjecture, (k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0)=k3_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_14])]), c_0_17])).
% 0.18/0.36  cnf(c_0_31, plain, (v2_struct_0(X1)|k7_lattices(X1,k7_lattices(X1,X2))=X2|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.36  cnf(c_0_32, negated_conjecture, (k7_lattices(esk1_0,k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0))=k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,k7_lattices(esk1_0,X1)))|~m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_20])])).
% 0.18/0.36  cnf(c_0_33, negated_conjecture, (k7_lattices(esk1_0,k7_lattices(esk1_0,X1))=X1|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_25]), c_0_16]), c_0_14])]), c_0_17])).
% 0.18/0.36  fof(c_0_34, plain, ![X16, X17, X18]:((k4_lattices(X16,X17,X18)!=k5_lattices(X16)|r3_lattices(X16,X17,k7_lattices(X16,X18))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v10_lattices(X16)|~v17_lattices(X16)|~l3_lattices(X16)))&(~r3_lattices(X16,X17,k7_lattices(X16,X18))|k4_lattices(X16,X17,X18)=k5_lattices(X16)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v10_lattices(X16)|~v17_lattices(X16)|~l3_lattices(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_lattices])])])])])).
% 0.18/0.36  cnf(c_0_35, negated_conjecture, (k7_lattices(esk1_0,k3_lattices(esk1_0,X1,esk3_0))=k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,X1))|~m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.18/0.36  cnf(c_0_36, plain, (k4_lattices(X1,X2,X3)=k5_lattices(X1)|v2_struct_0(X1)|~r3_lattices(X1,X2,k7_lattices(X1,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.36  cnf(c_0_37, negated_conjecture, (k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,X1))=k4_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk3_0))|~m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_35]), c_0_20])])).
% 0.18/0.36  cnf(c_0_38, negated_conjecture, (k4_lattices(esk1_0,X1,k7_lattices(esk1_0,X2))=k5_lattices(esk1_0)|~r3_lattices(esk1_0,X1,X2)|~m1_subset_1(k7_lattices(esk1_0,X2),u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X2,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_33]), c_0_25]), c_0_16]), c_0_14])]), c_0_17])).
% 0.18/0.36  cnf(c_0_39, negated_conjecture, (r3_lattices(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_41, negated_conjecture, (~r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_42, plain, (r3_lattices(X1,X2,k7_lattices(X1,X3))|v2_struct_0(X1)|k4_lattices(X1,X2,X3)!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.36  cnf(c_0_43, negated_conjecture, (k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),X1)=k4_lattices(esk1_0,X1,k7_lattices(esk1_0,esk3_0))|~m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_37, c_0_33])).
% 0.18/0.36  cnf(c_0_44, negated_conjecture, (k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))=k5_lattices(esk1_0)|~m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_20])])).
% 0.18/0.36  cnf(c_0_45, negated_conjecture, (k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0)!=k5_lattices(esk1_0)|~m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_25]), c_0_40]), c_0_16]), c_0_14])]), c_0_17])).
% 0.18/0.36  cnf(c_0_46, negated_conjecture, (k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),X1)=k4_lattices(esk1_0,X1,k7_lattices(esk1_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_27]), c_0_14])]), c_0_17])).
% 0.18/0.36  cnf(c_0_47, negated_conjecture, (k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))=k5_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_20]), c_0_14])]), c_0_17])).
% 0.18/0.36  cnf(c_0_48, negated_conjecture, (k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0)!=k5_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_27]), c_0_20]), c_0_14])]), c_0_17])).
% 0.18/0.36  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_47]), c_0_48]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 50
% 0.18/0.36  # Proof object clause steps            : 33
% 0.18/0.36  # Proof object formula steps           : 17
% 0.18/0.36  # Proof object conjectures             : 28
% 0.18/0.36  # Proof object clause conjectures      : 25
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 16
% 0.18/0.36  # Proof object initial formulas used   : 8
% 0.18/0.36  # Proof object generating inferences   : 17
% 0.18/0.36  # Proof object simplifying inferences  : 49
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 8
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 23
% 0.18/0.36  # Removed in clause preprocessing      : 1
% 0.18/0.36  # Initial clauses in saturation        : 22
% 0.18/0.36  # Processed clauses                    : 85
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 7
% 0.18/0.36  # ...remaining for further processing  : 78
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 2
% 0.18/0.36  # Backward-rewritten                   : 2
% 0.18/0.36  # Generated clauses                    : 143
% 0.18/0.36  # ...of the previous two non-trivial   : 133
% 0.18/0.36  # Contextual simplify-reflections      : 1
% 0.18/0.36  # Paramodulations                      : 143
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 0
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 52
% 0.18/0.36  #    Positive orientable unit clauses  : 18
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 3
% 0.18/0.36  #    Non-unit-clauses                  : 31
% 0.18/0.36  # Current number of unprocessed clauses: 89
% 0.18/0.36  # ...number of literals in the above   : 415
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 26
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 535
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 126
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 10
% 0.18/0.36  # Unit Clause-clause subsumption calls : 3
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 4
% 0.18/0.36  # BW rewrite match successes           : 2
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 7099
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.033 s
% 0.18/0.36  # System time              : 0.005 s
% 0.18/0.36  # Total time               : 0.038 s
% 0.18/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
