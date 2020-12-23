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
% DateTime   : Thu Dec  3 11:15:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 189 expanded)
%              Number of clauses        :   32 (  64 expanded)
%              Number of leaves         :    5 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  301 (1424 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d21_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ( X3 = k15_lattice3(X1,X2)
            <=> ( r4_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r4_lattice3(X1,X4,X2)
                     => r1_lattices(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(d18_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v4_lattice3(X1)
      <=> ! [X2] :
          ? [X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
            & r4_lattice3(X1,X3,X2)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r4_lattice3(X1,X4,X2)
                 => r1_lattices(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).

fof(t40_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
             => r3_lattices(X1,X2,k16_lattice3(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

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

fof(d22_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] : k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

fof(c_0_5,plain,(
    ! [X12,X13,X14,X15] :
      ( ( r4_lattice3(X12,X14,X13)
        | X14 != k15_lattice3(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ v4_lattice3(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r4_lattice3(X12,X15,X13)
        | r1_lattices(X12,X14,X15)
        | X14 != k15_lattice3(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ v4_lattice3(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk4_3(X12,X13,X14),u1_struct_0(X12))
        | ~ r4_lattice3(X12,X14,X13)
        | X14 = k15_lattice3(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ v4_lattice3(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( r4_lattice3(X12,esk4_3(X12,X13,X14),X13)
        | ~ r4_lattice3(X12,X14,X13)
        | X14 = k15_lattice3(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ v4_lattice3(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( ~ r1_lattices(X12,X14,esk4_3(X12,X13,X14))
        | ~ r4_lattice3(X12,X14,X13)
        | X14 = k15_lattice3(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ v4_lattice3(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_6,plain,
    ( r4_lattice3(X1,esk4_3(X1,X2,X3),X2)
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_7,plain,(
    ! [X5,X6,X8,X10] :
      ( ( m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))
        | ~ v4_lattice3(X5)
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( r4_lattice3(X5,esk1_2(X5,X6),X6)
        | ~ v4_lattice3(X5)
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r4_lattice3(X5,X8,X6)
        | r1_lattices(X5,esk1_2(X5,X6),X8)
        | ~ v4_lattice3(X5)
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( m1_subset_1(esk3_2(X5,X10),u1_struct_0(X5))
        | ~ m1_subset_1(X10,u1_struct_0(X5))
        | ~ r4_lattice3(X5,X10,esk2_1(X5))
        | v4_lattice3(X5)
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( r4_lattice3(X5,esk3_2(X5,X10),esk2_1(X5))
        | ~ m1_subset_1(X10,u1_struct_0(X5))
        | ~ r4_lattice3(X5,X10,esk2_1(X5))
        | v4_lattice3(X5)
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( ~ r1_lattices(X5,X10,esk3_2(X5,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X5))
        | ~ r4_lattice3(X5,X10,esk2_1(X5))
        | v4_lattice3(X5)
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattice3])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( r3_lattice3(X1,X2,X3)
               => r3_lattices(X1,X2,k16_lattice3(X1,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_lattice3])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk4_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r4_lattice3(X1,esk1_2(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v10_lattices(esk6_0)
    & v4_lattice3(esk6_0)
    & l3_lattices(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & r3_lattice3(esk6_0,esk7_0,esk8_0)
    & ~ r3_lattices(esk6_0,esk7_0,k16_lattice3(esk6_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_14,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( esk1_2(X1,X2) = k15_lattice3(X1,X2)
    | r4_lattice3(X1,esk4_3(X1,X2,esk1_2(X1,X2)),X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v4_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( esk1_2(X1,X2) = k15_lattice3(X1,X2)
    | m1_subset_1(esk4_3(X1,X2,esk1_2(X1,X2)),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_11]),c_0_12])).

cnf(c_0_21,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk4_3(X1,X3,X2))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,plain,
    ( r1_lattices(X2,esk1_2(X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( esk1_2(esk6_0,X1) = k15_lattice3(esk6_0,X1)
    | r4_lattice3(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,X1)),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( esk1_2(esk6_0,X1) = k15_lattice3(esk6_0,X1)
    | m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,X1)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_25,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk4_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( esk1_2(esk6_0,X1) = k15_lattice3(esk6_0,X1)
    | r1_lattices(esk6_0,esk1_2(esk6_0,X1),esk4_3(esk6_0,X1,esk1_2(esk6_0,X1))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_17]),c_0_18])]),c_0_19]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk1_2(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_17]),c_0_18])]),c_0_19])).

fof(c_0_28,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( r3_lattice3(X19,X20,X21)
        | X20 != k16_lattice3(X19,X21)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r3_lattice3(X19,X22,X21)
        | r3_lattices(X19,X22,X20)
        | X20 != k16_lattice3(X19,X21)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) )
      & ( m1_subset_1(esk5_3(X19,X20,X23),u1_struct_0(X19))
        | ~ r3_lattice3(X19,X20,X23)
        | X20 = k16_lattice3(X19,X23)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) )
      & ( r3_lattice3(X19,esk5_3(X19,X20,X23),X23)
        | ~ r3_lattice3(X19,X20,X23)
        | X20 = k16_lattice3(X19,X23)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) )
      & ( ~ r3_lattices(X19,esk5_3(X19,X20,X23),X20)
        | ~ r3_lattice3(X19,X20,X23)
        | X20 = k16_lattice3(X19,X23)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_29,negated_conjecture,
    ( esk1_2(esk6_0,X1) = k15_lattice3(esk6_0,X1)
    | ~ r4_lattice3(esk6_0,esk1_2(esk6_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_16]),c_0_27]),c_0_17]),c_0_18])]),c_0_19])).

fof(c_0_30,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ l3_lattices(X17)
      | k16_lattice3(X17,X18) = k15_lattice3(X17,a_2_1_lattice3(X17,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattice3])])])])).

cnf(c_0_31,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( esk1_2(esk6_0,X1) = k15_lattice3(esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_11]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(k16_lattice3(X1,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r3_lattice3(esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( ~ r3_lattices(esk6_0,esk7_0,k16_lattice3(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_1_lattice3(esk6_0,X1)) = k16_lattice3(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_33]),c_0_18])])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(k16_lattice3(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_16]),c_0_36]),c_0_17]),c_0_18])]),c_0_37]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k16_lattice3(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.13/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 0.13/0.38  fof(d18_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v4_lattice3(X1)<=>![X2]:?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r4_lattice3(X1,X3,X2))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_lattice3)).
% 0.13/0.38  fof(t40_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)=>r3_lattices(X1,X2,k16_lattice3(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattice3)).
% 0.13/0.38  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.13/0.38  fof(d22_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:k16_lattice3(X1,X2)=k15_lattice3(X1,a_2_1_lattice3(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d22_lattice3)).
% 0.13/0.38  fof(c_0_5, plain, ![X12, X13, X14, X15]:(((r4_lattice3(X12,X14,X13)|X14!=k15_lattice3(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~v4_lattice3(X12)|~l3_lattices(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&(~m1_subset_1(X15,u1_struct_0(X12))|(~r4_lattice3(X12,X15,X13)|r1_lattices(X12,X14,X15))|X14!=k15_lattice3(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~v4_lattice3(X12)|~l3_lattices(X12))|(v2_struct_0(X12)|~l3_lattices(X12))))&((m1_subset_1(esk4_3(X12,X13,X14),u1_struct_0(X12))|~r4_lattice3(X12,X14,X13)|X14=k15_lattice3(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~v4_lattice3(X12)|~l3_lattices(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&((r4_lattice3(X12,esk4_3(X12,X13,X14),X13)|~r4_lattice3(X12,X14,X13)|X14=k15_lattice3(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~v4_lattice3(X12)|~l3_lattices(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&(~r1_lattices(X12,X14,esk4_3(X12,X13,X14))|~r4_lattice3(X12,X14,X13)|X14=k15_lattice3(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~v4_lattice3(X12)|~l3_lattices(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.13/0.38  cnf(c_0_6, plain, (r4_lattice3(X1,esk4_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  fof(c_0_7, plain, ![X5, X6, X8, X10]:((((m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))|~v4_lattice3(X5)|(v2_struct_0(X5)|~l3_lattices(X5)))&(r4_lattice3(X5,esk1_2(X5,X6),X6)|~v4_lattice3(X5)|(v2_struct_0(X5)|~l3_lattices(X5))))&(~m1_subset_1(X8,u1_struct_0(X5))|(~r4_lattice3(X5,X8,X6)|r1_lattices(X5,esk1_2(X5,X6),X8))|~v4_lattice3(X5)|(v2_struct_0(X5)|~l3_lattices(X5))))&((m1_subset_1(esk3_2(X5,X10),u1_struct_0(X5))|(~m1_subset_1(X10,u1_struct_0(X5))|~r4_lattice3(X5,X10,esk2_1(X5)))|v4_lattice3(X5)|(v2_struct_0(X5)|~l3_lattices(X5)))&((r4_lattice3(X5,esk3_2(X5,X10),esk2_1(X5))|(~m1_subset_1(X10,u1_struct_0(X5))|~r4_lattice3(X5,X10,esk2_1(X5)))|v4_lattice3(X5)|(v2_struct_0(X5)|~l3_lattices(X5)))&(~r1_lattices(X5,X10,esk3_2(X5,X10))|(~m1_subset_1(X10,u1_struct_0(X5))|~r4_lattice3(X5,X10,esk2_1(X5)))|v4_lattice3(X5)|(v2_struct_0(X5)|~l3_lattices(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattice3])])])])])])).
% 0.13/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)=>r3_lattices(X1,X2,k16_lattice3(X1,X3)))))), inference(assume_negation,[status(cth)],[t40_lattice3])).
% 0.13/0.38  cnf(c_0_9, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_10, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk4_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_11, plain, (r4_lattice3(X1,esk1_2(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_12, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v4_lattice3(esk6_0))&l3_lattices(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&(r3_lattice3(esk6_0,esk7_0,esk8_0)&~r3_lattices(esk6_0,esk7_0,k16_lattice3(esk6_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.13/0.38  cnf(c_0_14, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_15, plain, (esk1_2(X1,X2)=k15_lattice3(X1,X2)|r4_lattice3(X1,esk4_3(X1,X2,esk1_2(X1,X2)),X2)|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (v4_lattice3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (esk1_2(X1,X2)=k15_lattice3(X1,X2)|m1_subset_1(esk4_3(X1,X2,esk1_2(X1,X2)),u1_struct_0(X1))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_11]), c_0_12])).
% 0.13/0.38  cnf(c_0_21, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk4_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_22, plain, (r1_lattices(X2,esk1_2(X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (esk1_2(esk6_0,X1)=k15_lattice3(esk6_0,X1)|r4_lattice3(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk6_0,X1)),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (esk1_2(esk6_0,X1)=k15_lattice3(esk6_0,X1)|m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk6_0,X1)),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.38  cnf(c_0_25, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk4_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (esk1_2(esk6_0,X1)=k15_lattice3(esk6_0,X1)|r1_lattices(esk6_0,esk1_2(esk6_0,X1),esk4_3(esk6_0,X1,esk1_2(esk6_0,X1)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_17]), c_0_18])]), c_0_19]), c_0_24])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk1_2(esk6_0,X1),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.38  fof(c_0_28, plain, ![X19, X20, X21, X22, X23]:(((r3_lattice3(X19,X20,X21)|X20!=k16_lattice3(X19,X21)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19)))&(~m1_subset_1(X22,u1_struct_0(X19))|(~r3_lattice3(X19,X22,X21)|r3_lattices(X19,X22,X20))|X20!=k16_lattice3(X19,X21)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19))))&((m1_subset_1(esk5_3(X19,X20,X23),u1_struct_0(X19))|~r3_lattice3(X19,X20,X23)|X20=k16_lattice3(X19,X23)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19)))&((r3_lattice3(X19,esk5_3(X19,X20,X23),X23)|~r3_lattice3(X19,X20,X23)|X20=k16_lattice3(X19,X23)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19)))&(~r3_lattices(X19,esk5_3(X19,X20,X23),X20)|~r3_lattice3(X19,X20,X23)|X20=k16_lattice3(X19,X23)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (esk1_2(esk6_0,X1)=k15_lattice3(esk6_0,X1)|~r4_lattice3(esk6_0,esk1_2(esk6_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_16]), c_0_27]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.38  fof(c_0_30, plain, ![X17, X18]:(v2_struct_0(X17)|~l3_lattices(X17)|k16_lattice3(X17,X18)=k15_lattice3(X17,a_2_1_lattice3(X17,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattice3])])])])).
% 0.13/0.38  cnf(c_0_31, plain, (r3_lattices(X2,X1,X4)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattice3(X2,X1,X3)|X4!=k16_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (esk1_2(esk6_0,X1)=k15_lattice3(esk6_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_11]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.38  cnf(c_0_33, plain, (v2_struct_0(X1)|k16_lattice3(X1,X2)=k15_lattice3(X1,a_2_1_lattice3(X1,X2))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_34, plain, (r3_lattices(X1,X2,k16_lattice3(X1,X3))|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~v10_lattices(X1)|~m1_subset_1(k16_lattice3(X1,X3),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v4_lattice3(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r3_lattice3(esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (~r3_lattices(esk6_0,esk7_0,k16_lattice3(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(k15_lattice3(esk6_0,X1),u1_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_27, c_0_32])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (k15_lattice3(esk6_0,a_2_1_lattice3(esk6_0,X1))=k16_lattice3(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_33]), c_0_18])])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (~m1_subset_1(k16_lattice3(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_16]), c_0_36]), c_0_17]), c_0_18])]), c_0_37]), c_0_19])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (m1_subset_1(k16_lattice3(esk6_0,X1),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 43
% 0.13/0.38  # Proof object clause steps            : 32
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 21
% 0.13/0.38  # Proof object clause conjectures      : 18
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 15
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 11
% 0.13/0.38  # Proof object simplifying inferences  : 44
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 24
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 24
% 0.13/0.38  # Processed clauses                    : 71
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 71
% 0.13/0.38  # Other redundant clauses eliminated   : 4
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 8
% 0.13/0.38  # Generated clauses                    : 42
% 0.13/0.38  # ...of the previous two non-trivial   : 36
% 0.13/0.38  # Contextual simplify-reflections      : 6
% 0.13/0.38  # Paramodulations                      : 38
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 4
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 35
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 24
% 0.13/0.38  # Current number of unprocessed clauses: 12
% 0.13/0.38  # ...number of literals in the above   : 55
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 32
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 303
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 8
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.38  # Unit Clause-clause subsumption calls : 9
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 4
% 0.13/0.38  # BW rewrite match successes           : 4
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4168
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
