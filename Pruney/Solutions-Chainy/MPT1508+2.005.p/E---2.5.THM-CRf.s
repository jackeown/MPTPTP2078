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
% DateTime   : Thu Dec  3 11:15:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 250 expanded)
%              Number of clauses        :   34 (  81 expanded)
%              Number of leaves         :    8 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  296 (1695 expanded)
%              Number of equality atoms :   17 ( 149 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    2 (   1 average)

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

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
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

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & v4_lattice3(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & r2_hidden(esk3_0,esk4_0)
    & r3_lattice3(esk2_0,esk3_0,esk4_0)
    & k16_lattice3(esk2_0,esk4_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r3_lattices(X7,X8,X9)
        | r1_lattices(X7,X8,X9)
        | v2_struct_0(X7)
        | ~ v6_lattices(X7)
        | ~ v8_lattices(X7)
        | ~ v9_lattices(X7)
        | ~ l3_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7)) )
      & ( ~ r1_lattices(X7,X8,X9)
        | r3_lattices(X7,X8,X9)
        | v2_struct_0(X7)
        | ~ v6_lattices(X7)
        | ~ v8_lattices(X7)
        | ~ v9_lattices(X7)
        | ~ l3_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_12,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,plain,(
    ! [X10,X11,X12] :
      ( v2_struct_0(X10)
      | ~ v4_lattices(X10)
      | ~ l2_lattices(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ r1_lattices(X10,X11,X12)
      | ~ r1_lattices(X10,X12,X11)
      | X11 = X12 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

fof(c_0_19,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ l3_lattices(X13)
      | m1_subset_1(k16_lattice3(X13,X14),u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_20,plain,(
    ! [X6] :
      ( ( l1_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( l2_lattices(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_21,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( v9_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v8_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v6_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r1_lattices(esk2_0,X1,esk3_0)
    | ~ r3_lattices(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_14])]),c_0_15]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_30,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_31,plain,(
    ! [X21,X22,X23] :
      ( ( r3_lattices(X21,X22,k15_lattice3(X21,X23))
        | ~ r2_hidden(X22,X23)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) )
      & ( r3_lattices(X21,k16_lattice3(X21,X23),X22)
        | ~ r2_hidden(X22,X23)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_32,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( r3_lattice3(X15,X16,X17)
        | X16 != k16_lattice3(X15,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v4_lattice3(X15)
        | ~ l3_lattices(X15) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r3_lattice3(X15,X18,X17)
        | r3_lattices(X15,X18,X16)
        | X16 != k16_lattice3(X15,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v4_lattice3(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk1_3(X15,X16,X19),u1_struct_0(X15))
        | ~ r3_lattice3(X15,X16,X19)
        | X16 = k16_lattice3(X15,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v4_lattice3(X15)
        | ~ l3_lattices(X15) )
      & ( r3_lattice3(X15,esk1_3(X15,X16,X19),X19)
        | ~ r3_lattice3(X15,X16,X19)
        | X16 = k16_lattice3(X15,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v4_lattice3(X15)
        | ~ l3_lattices(X15) )
      & ( ~ r3_lattices(X15,esk1_3(X15,X16,X19),X16)
        | ~ r3_lattice3(X15,X16,X19)
        | X16 = k16_lattice3(X15,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v4_lattice3(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_33,plain,
    ( X1 = k16_lattice3(X2,X3)
    | v2_struct_0(X2)
    | ~ r1_lattices(X2,k16_lattice3(X2,X3),X1)
    | ~ r1_lattices(X2,X1,k16_lattice3(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_14])]),c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( v4_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_36,plain,
    ( r1_lattices(X1,X2,k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_37,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v4_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 = k16_lattice3(esk2_0,X1)
    | ~ r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))
    | ~ r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_22]),c_0_35]),c_0_14])]),c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))
    | ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_14])]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_22]),c_0_38]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,plain,
    ( r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 = k16_lattice3(esk2_0,X1)
    | ~ r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r3_lattices(esk2_0,k16_lattice3(esk2_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_38]),c_0_22]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( k16_lattice3(esk2_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:48:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t42_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 0.13/0.37  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.13/0.37  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.13/0.37  fof(t26_lattices, axiom, ![X1]:(((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 0.13/0.37  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.13/0.37  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.13/0.37  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 0.13/0.37  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2)))), inference(assume_negation,[status(cth)],[t42_lattice3])).
% 0.13/0.37  fof(c_0_9, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.13/0.37  fof(c_0_10, negated_conjecture, ((((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&v4_lattice3(esk2_0))&l3_lattices(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((r2_hidden(esk3_0,esk4_0)&r3_lattice3(esk2_0,esk3_0,esk4_0))&k16_lattice3(esk2_0,esk4_0)!=esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.13/0.37  fof(c_0_11, plain, ![X7, X8, X9]:((~r3_lattices(X7,X8,X9)|r1_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))&(~r1_lattices(X7,X8,X9)|r3_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.13/0.37  cnf(c_0_12, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_16, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_17, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  fof(c_0_18, plain, ![X10, X11, X12]:(v2_struct_0(X10)|~v4_lattices(X10)|~l2_lattices(X10)|(~m1_subset_1(X11,u1_struct_0(X10))|(~m1_subset_1(X12,u1_struct_0(X10))|(~r1_lattices(X10,X11,X12)|~r1_lattices(X10,X12,X11)|X11=X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).
% 0.13/0.37  fof(c_0_19, plain, ![X13, X14]:(v2_struct_0(X13)|~l3_lattices(X13)|m1_subset_1(k16_lattice3(X13,X14),u1_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.13/0.37  fof(c_0_20, plain, ![X6]:((l1_lattices(X6)|~l3_lattices(X6))&(l2_lattices(X6)|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.13/0.37  cnf(c_0_21, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (v9_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), c_0_15])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (v8_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_13]), c_0_14])]), c_0_15])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (v6_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_14])]), c_0_15])).
% 0.13/0.37  cnf(c_0_26, plain, (v2_struct_0(X1)|X2=X3|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)|~r1_lattices(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_27, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_28, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (r1_lattices(esk2_0,X1,esk3_0)|~r3_lattices(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_14])]), c_0_15]), c_0_23]), c_0_24]), c_0_25])])).
% 0.13/0.37  cnf(c_0_30, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  fof(c_0_31, plain, ![X21, X22, X23]:((r3_lattices(X21,X22,k15_lattice3(X21,X23))|~r2_hidden(X22,X23)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21)))&(r3_lattices(X21,k16_lattice3(X21,X23),X22)|~r2_hidden(X22,X23)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.13/0.37  fof(c_0_32, plain, ![X15, X16, X17, X18, X19]:(((r3_lattice3(X15,X16,X17)|X16!=k16_lattice3(X15,X17)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v10_lattices(X15)|~v4_lattice3(X15)|~l3_lattices(X15)))&(~m1_subset_1(X18,u1_struct_0(X15))|(~r3_lattice3(X15,X18,X17)|r3_lattices(X15,X18,X16))|X16!=k16_lattice3(X15,X17)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v10_lattices(X15)|~v4_lattice3(X15)|~l3_lattices(X15))))&((m1_subset_1(esk1_3(X15,X16,X19),u1_struct_0(X15))|~r3_lattice3(X15,X16,X19)|X16=k16_lattice3(X15,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v10_lattices(X15)|~v4_lattice3(X15)|~l3_lattices(X15)))&((r3_lattice3(X15,esk1_3(X15,X16,X19),X19)|~r3_lattice3(X15,X16,X19)|X16=k16_lattice3(X15,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v10_lattices(X15)|~v4_lattice3(X15)|~l3_lattices(X15)))&(~r3_lattices(X15,esk1_3(X15,X16,X19),X16)|~r3_lattice3(X15,X16,X19)|X16=k16_lattice3(X15,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v10_lattices(X15)|~v4_lattice3(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.13/0.37  cnf(c_0_33, plain, (X1=k16_lattice3(X2,X3)|v2_struct_0(X2)|~r1_lattices(X2,k16_lattice3(X2,X3),X1)|~r1_lattices(X2,X1,k16_lattice3(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v4_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_27]), c_0_14])]), c_0_15])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (v4_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_13]), c_0_14])]), c_0_15])).
% 0.13/0.37  cnf(c_0_36, plain, (r1_lattices(X1,X2,k16_lattice3(X1,X3))|v2_struct_0(X1)|~r3_lattices(X1,X2,k16_lattice3(X1,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~v6_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_21, c_0_27])).
% 0.13/0.37  cnf(c_0_37, plain, (r3_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (v4_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_39, plain, (r3_lattices(X2,X1,X4)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattice3(X2,X1,X3)|X4!=k16_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (esk3_0=k16_lattice3(esk2_0,X1)|~r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))|~r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_22]), c_0_35]), c_0_14])]), c_0_15])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))|~r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_14])]), c_0_15])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r2_hidden(esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_22]), c_0_38]), c_0_13]), c_0_14])]), c_0_15])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_44, plain, (r3_lattices(X1,X2,k16_lattice3(X1,X3))|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_27])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (r3_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (esk3_0=k16_lattice3(esk2_0,X1)|~r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (r3_lattices(esk2_0,k16_lattice3(esk2_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_38]), c_0_22]), c_0_13]), c_0_14])]), c_0_15])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (k16_lattice3(esk2_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])]), c_0_49]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 51
% 0.13/0.37  # Proof object clause steps            : 34
% 0.13/0.37  # Proof object formula steps           : 17
% 0.13/0.37  # Proof object conjectures             : 24
% 0.13/0.37  # Proof object clause conjectures      : 21
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 18
% 0.13/0.37  # Proof object initial formulas used   : 8
% 0.13/0.37  # Proof object generating inferences   : 15
% 0.13/0.37  # Proof object simplifying inferences  : 50
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 8
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 28
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 27
% 0.13/0.37  # Processed clauses                    : 88
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 88
% 0.13/0.37  # Other redundant clauses eliminated   : 2
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 46
% 0.13/0.37  # ...of the previous two non-trivial   : 41
% 0.13/0.37  # Contextual simplify-reflections      : 5
% 0.13/0.37  # Paramodulations                      : 44
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 2
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 58
% 0.13/0.37  #    Positive orientable unit clauses  : 17
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 39
% 0.13/0.37  # Current number of unprocessed clauses: 7
% 0.13/0.37  # ...number of literals in the above   : 68
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 28
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 1083
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 120
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.37  # Unit Clause-clause subsumption calls : 8
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 4218
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.032 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.037 s
% 0.13/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
