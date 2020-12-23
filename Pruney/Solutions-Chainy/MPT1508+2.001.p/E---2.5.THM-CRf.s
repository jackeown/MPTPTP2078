%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:02 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 404 expanded)
%              Number of clauses        :   48 ( 135 expanded)
%              Number of leaves         :   10 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  355 (2556 expanded)
%              Number of equality atoms :   35 ( 246 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r3_lattice3(X1,X2,X3) )
             => k16_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(d3_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k1_lattices(X1,X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

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

fof(t38_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r2_hidden(X2,X3)
             => ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
                & r3_lattices(X1,k16_lattice3(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

fof(t34_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k16_lattice3(X1,X3)
            <=> ( r3_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r3_lattice3(X1,X4,X3)
                     => r3_lattices(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( ( r2_hidden(X2,X3)
                  & r3_lattice3(X1,X2,X3) )
               => k16_lattice3(X1,X3) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_lattice3])).

fof(c_0_11,plain,(
    ! [X12] :
      ( ( l1_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( l2_lattices(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & v4_lattice3(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & r2_hidden(esk3_0,esk4_0)
    & r3_lattice3(esk2_0,esk3_0,esk4_0)
    & k16_lattice3(esk2_0,esk4_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
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

fof(c_0_14,plain,(
    ! [X13,X14,X15] :
      ( v2_struct_0(X13)
      | ~ v4_lattices(X13)
      | ~ l2_lattices(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | k3_lattices(X13,X14,X15) = k1_lattices(X13,X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_15,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ v4_lattices(X6)
      | ~ l2_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k3_lattices(X6,X7,X8) = k3_lattices(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( l2_lattices(esk2_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v4_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_16])]),c_0_19])).

fof(c_0_25,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ l3_lattices(X19)
      | m1_subset_1(k16_lattice3(X19,X20),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_26,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r1_lattices(X9,X10,X11)
        | k1_lattices(X9,X10,X11) = X11
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l2_lattices(X9) )
      & ( k1_lattices(X9,X10,X11) != X11
        | r1_lattices(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l2_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k3_lattices(esk2_0,X1,esk3_0) = k1_lattices(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19]),c_0_23]),c_0_24])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k3_lattices(esk2_0,X1,esk3_0) = k3_lattices(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_19]),c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( k3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) = k1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16])]),c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( k1_lattices(esk2_0,X1,esk3_0) = esk3_0
    | ~ r1_lattices(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_19]),c_0_23])])).

cnf(c_0_34,plain,
    ( k3_lattices(X1,X2,k16_lattice3(X1,X3)) = k1_lattices(X1,X2,k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_29]),c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) = k1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_32]),c_0_16])]),c_0_19])).

fof(c_0_36,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r3_lattices(X16,X17,X18)
        | r1_lattices(X16,X17,X18)
        | v2_struct_0(X16)
        | ~ v6_lattices(X16)
        | ~ v8_lattices(X16)
        | ~ v9_lattices(X16)
        | ~ l3_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16)) )
      & ( ~ r1_lattices(X16,X17,X18)
        | r3_lattices(X16,X17,X18)
        | v2_struct_0(X16)
        | ~ v6_lattices(X16)
        | ~ v8_lattices(X16)
        | ~ v9_lattices(X16)
        | ~ l3_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_37,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( k1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) = esk3_0
    | ~ r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_16])]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( k1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) = k1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_22]),c_0_35]),c_0_24]),c_0_16])]),c_0_19])).

cnf(c_0_42,plain,
    ( k1_lattices(X1,X2,k16_lattice3(X1,X3)) = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,k16_lattice3(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_15])).

cnf(c_0_43,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v9_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_16])]),c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( v8_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_18]),c_0_16])]),c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( v6_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_18]),c_0_16])]),c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( k1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) = esk3_0
    | ~ r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) = k16_lattice3(esk2_0,X1)
    | ~ r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_22]),c_0_16])]),c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( r1_lattices(esk2_0,X1,esk3_0)
    | ~ r3_lattices(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_22]),c_0_16])]),c_0_19]),c_0_44]),c_0_45]),c_0_46])])).

fof(c_0_50,plain,(
    ! [X27,X28,X29] :
      ( ( r3_lattices(X27,X28,k15_lattice3(X27,X29))
        | ~ r2_hidden(X28,X29)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27) )
      & ( r3_lattices(X27,k16_lattice3(X27,X29),X28)
        | ~ r2_hidden(X28,X29)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_51,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( r3_lattice3(X21,X22,X23)
        | X22 != k16_lattice3(X21,X23)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r3_lattice3(X21,X24,X23)
        | r3_lattices(X21,X24,X22)
        | X22 != k16_lattice3(X21,X23)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) )
      & ( m1_subset_1(esk1_3(X21,X22,X25),u1_struct_0(X21))
        | ~ r3_lattice3(X21,X22,X25)
        | X22 = k16_lattice3(X21,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) )
      & ( r3_lattice3(X21,esk1_3(X21,X22,X25),X25)
        | ~ r3_lattice3(X21,X22,X25)
        | X22 = k16_lattice3(X21,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) )
      & ( ~ r3_lattices(X21,esk1_3(X21,X22,X25),X22)
        | ~ r3_lattice3(X21,X22,X25)
        | X22 = k16_lattice3(X21,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_52,negated_conjecture,
    ( k16_lattice3(esk2_0,X1) = esk3_0
    | ~ r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_16])]),c_0_19])).

cnf(c_0_54,plain,
    ( r1_lattices(X1,X2,k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_29])).

cnf(c_0_55,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v4_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_57,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k16_lattice3(esk2_0,X1) = esk3_0
    | ~ r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))
    | ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_44]),c_0_45]),c_0_46]),c_0_16])]),c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_56]),c_0_18]),c_0_16])]),c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_62,plain,
    ( r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_57]),c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_64,negated_conjecture,
    ( k16_lattice3(esk2_0,X1) = esk3_0
    | ~ r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r3_lattices(esk2_0,k16_lattice3(esk2_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_56]),c_0_22]),c_0_18]),c_0_16])]),c_0_19])).

cnf(c_0_67,negated_conjecture,
    ( k16_lattice3(esk2_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:08:19 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.029 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t42_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 0.19/0.37  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.37  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.37  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.19/0.37  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 0.19/0.37  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.19/0.37  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.19/0.37  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.19/0.37  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 0.19/0.37  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2)))), inference(assume_negation,[status(cth)],[t42_lattice3])).
% 0.19/0.37  fof(c_0_11, plain, ![X12]:((l1_lattices(X12)|~l3_lattices(X12))&(l2_lattices(X12)|~l3_lattices(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.37  fof(c_0_12, negated_conjecture, ((((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&v4_lattice3(esk2_0))&l3_lattices(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((r2_hidden(esk3_0,esk4_0)&r3_lattice3(esk2_0,esk3_0,esk4_0))&k16_lattice3(esk2_0,esk4_0)!=esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.37  fof(c_0_13, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X13, X14, X15]:(v2_struct_0(X13)|~v4_lattices(X13)|~l2_lattices(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))|k3_lattices(X13,X14,X15)=k1_lattices(X13,X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.19/0.37  cnf(c_0_15, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_17, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  fof(c_0_20, plain, ![X6, X7, X8]:(v2_struct_0(X6)|~v4_lattices(X6)|~l2_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))|k3_lattices(X6,X7,X8)=k3_lattices(X6,X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 0.19/0.37  cnf(c_0_21, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (l2_lattices(esk2_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (v4_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_16])]), c_0_19])).
% 0.19/0.37  fof(c_0_25, plain, ![X19, X20]:(v2_struct_0(X19)|~l3_lattices(X19)|m1_subset_1(k16_lattice3(X19,X20),u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.19/0.37  fof(c_0_26, plain, ![X9, X10, X11]:((~r1_lattices(X9,X10,X11)|k1_lattices(X9,X10,X11)=X11|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l2_lattices(X9)))&(k1_lattices(X9,X10,X11)!=X11|r1_lattices(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l2_lattices(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.19/0.37  cnf(c_0_27, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (k3_lattices(esk2_0,X1,esk3_0)=k1_lattices(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_19]), c_0_23]), c_0_24])])).
% 0.19/0.37  cnf(c_0_29, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_30, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (k3_lattices(esk2_0,X1,esk3_0)=k3_lattices(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_22]), c_0_19]), c_0_23]), c_0_24])])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (k3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)=k1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (k1_lattices(esk2_0,X1,esk3_0)=esk3_0|~r1_lattices(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_22]), c_0_19]), c_0_23])])).
% 0.19/0.37  cnf(c_0_34, plain, (k3_lattices(X1,X2,k16_lattice3(X1,X3))=k1_lattices(X1,X2,k16_lattice3(X1,X3))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v4_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_29]), c_0_15])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (k3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))=k1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_32]), c_0_16])]), c_0_19])).
% 0.19/0.37  fof(c_0_36, plain, ![X16, X17, X18]:((~r3_lattices(X16,X17,X18)|r1_lattices(X16,X17,X18)|(v2_struct_0(X16)|~v6_lattices(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))))&(~r1_lattices(X16,X17,X18)|r3_lattices(X16,X17,X18)|(v2_struct_0(X16)|~v6_lattices(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.19/0.37  cnf(c_0_37, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_38, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_39, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (k1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)=esk3_0|~r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (k1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)=k1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_22]), c_0_35]), c_0_24]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_42, plain, (k1_lattices(X1,X2,k16_lattice3(X1,X3))=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,k16_lattice3(X1,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_15])).
% 0.19/0.37  cnf(c_0_43, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (v9_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (v8_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_18]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (v6_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_18]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (k1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))=esk3_0|~r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (k1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))=k16_lattice3(esk2_0,X1)|~r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_22]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (r1_lattices(esk2_0,X1,esk3_0)|~r3_lattices(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_22]), c_0_16])]), c_0_19]), c_0_44]), c_0_45]), c_0_46])])).
% 0.19/0.37  fof(c_0_50, plain, ![X27, X28, X29]:((r3_lattices(X27,X28,k15_lattice3(X27,X29))|~r2_hidden(X28,X29)|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27)))&(r3_lattices(X27,k16_lattice3(X27,X29),X28)|~r2_hidden(X28,X29)|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.19/0.37  fof(c_0_51, plain, ![X21, X22, X23, X24, X25]:(((r3_lattice3(X21,X22,X23)|X22!=k16_lattice3(X21,X23)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21)))&(~m1_subset_1(X24,u1_struct_0(X21))|(~r3_lattice3(X21,X24,X23)|r3_lattices(X21,X24,X22))|X22!=k16_lattice3(X21,X23)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21))))&((m1_subset_1(esk1_3(X21,X22,X25),u1_struct_0(X21))|~r3_lattice3(X21,X22,X25)|X22=k16_lattice3(X21,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21)))&((r3_lattice3(X21,esk1_3(X21,X22,X25),X25)|~r3_lattice3(X21,X22,X25)|X22=k16_lattice3(X21,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21)))&(~r3_lattices(X21,esk1_3(X21,X22,X25),X22)|~r3_lattice3(X21,X22,X25)|X22=k16_lattice3(X21,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (k16_lattice3(esk2_0,X1)=esk3_0|~r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_29]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_54, plain, (r1_lattices(X1,X2,k16_lattice3(X1,X3))|v2_struct_0(X1)|~r3_lattices(X1,X2,k16_lattice3(X1,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~v6_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_43, c_0_29])).
% 0.19/0.37  cnf(c_0_55, plain, (r3_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.37  cnf(c_0_56, negated_conjecture, (v4_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_57, plain, (r3_lattices(X2,X1,X4)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattice3(X2,X1,X3)|X4!=k16_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (k16_lattice3(esk2_0,X1)=esk3_0|~r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))|~r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_22]), c_0_44]), c_0_45]), c_0_46]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r2_hidden(esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_22]), c_0_56]), c_0_18]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_61, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_62, plain, (r3_lattices(X1,X2,k16_lattice3(X1,X3))|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_57]), c_0_29])).
% 0.19/0.37  cnf(c_0_63, negated_conjecture, (r3_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_64, negated_conjecture, (k16_lattice3(esk2_0,X1)=esk3_0|~r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.37  cnf(c_0_65, negated_conjecture, (r3_lattices(esk2_0,k16_lattice3(esk2_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.37  cnf(c_0_66, negated_conjecture, (r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_56]), c_0_22]), c_0_18]), c_0_16])]), c_0_19])).
% 0.19/0.37  cnf(c_0_67, negated_conjecture, (k16_lattice3(esk2_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])]), c_0_67]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 69
% 0.19/0.37  # Proof object clause steps            : 48
% 0.19/0.37  # Proof object formula steps           : 21
% 0.19/0.37  # Proof object conjectures             : 35
% 0.19/0.37  # Proof object clause conjectures      : 32
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 20
% 0.19/0.37  # Proof object initial formulas used   : 10
% 0.19/0.37  # Proof object generating inferences   : 27
% 0.19/0.37  # Proof object simplifying inferences  : 75
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 10
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 31
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 30
% 0.19/0.37  # Processed clauses                    : 127
% 0.19/0.37  # ...of these trivial                  : 5
% 0.19/0.37  # ...subsumed                          : 6
% 0.19/0.37  # ...remaining for further processing  : 116
% 0.19/0.37  # Other redundant clauses eliminated   : 2
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 94
% 0.19/0.37  # ...of the previous two non-trivial   : 81
% 0.19/0.37  # Contextual simplify-reflections      : 7
% 0.19/0.37  # Paramodulations                      : 92
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 2
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 84
% 0.19/0.38  #    Positive orientable unit clauses  : 20
% 0.19/0.38  #    Positive unorientable unit clauses: 1
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 61
% 0.19/0.38  # Current number of unprocessed clauses: 14
% 0.19/0.38  # ...number of literals in the above   : 137
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 30
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1322
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 213
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.19/0.38  # Unit Clause-clause subsumption calls : 12
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 6
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 6039
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.035 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
