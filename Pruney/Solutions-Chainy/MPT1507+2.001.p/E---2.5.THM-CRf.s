%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 333 expanded)
%              Number of clauses        :   45 ( 113 expanded)
%              Number of leaves         :   10 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  396 (2138 expanded)
%              Number of equality atoms :   36 ( 215 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r4_lattice3(X1,X2,X3) )
             => k15_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

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

fof(d9_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v9_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(d6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v6_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

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
                  & r4_lattice3(X1,X2,X3) )
               => k15_lattice3(X1,X3) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_lattice3])).

fof(c_0_11,plain,(
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

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v10_lattices(esk6_0)
    & v4_lattice3(esk6_0)
    & l3_lattices(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & r2_hidden(esk7_0,esk8_0)
    & r4_lattice3(esk6_0,esk7_0,esk8_0)
    & k15_lattice3(esk6_0,esk8_0) != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v9_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | k2_lattices(X9,X10,k1_lattices(X9,X10,X11)) = X10
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk1_1(X9),u1_struct_0(X9))
        | v9_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk2_1(X9),u1_struct_0(X9))
        | v9_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( k2_lattices(X9,esk1_1(X9),k1_lattices(X9,esk1_1(X9),esk2_1(X9))) != esk1_1(X9)
        | v9_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_14,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r1_lattices(X6,X7,X8)
        | k1_lattices(X6,X7,X8) = X8
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l2_lattices(X6) )
      & ( k1_lattices(X6,X7,X8) != X8
        | r1_lattices(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l2_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

fof(c_0_19,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r4_lattice3(X18,X20,X19)
        | X20 != k15_lattice3(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v4_lattice3(X18)
        | ~ l3_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ r4_lattice3(X18,X21,X19)
        | r1_lattices(X18,X20,X21)
        | X20 != k15_lattice3(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v4_lattice3(X18)
        | ~ l3_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( m1_subset_1(esk3_3(X18,X19,X20),u1_struct_0(X18))
        | ~ r4_lattice3(X18,X20,X19)
        | X20 = k15_lattice3(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v4_lattice3(X18)
        | ~ l3_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( r4_lattice3(X18,esk3_3(X18,X19,X20),X19)
        | ~ r4_lattice3(X18,X20,X19)
        | X20 = k15_lattice3(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v4_lattice3(X18)
        | ~ l3_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( ~ r1_lattices(X18,X20,esk3_3(X18,X19,X20))
        | ~ r4_lattice3(X18,X20,X19)
        | X20 = k15_lattice3(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v4_lattice3(X18)
        | ~ l3_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_20,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v9_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_23,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_lattices(X2,X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | X4 != k15_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ l3_lattices(X28)
      | m1_subset_1(k15_lattice3(X28,X29),u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_26,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X1,esk7_0)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_16])]),c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( k1_lattices(esk6_0,X1,esk7_0) = esk7_0
    | ~ r1_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_21]),c_0_17])).

fof(c_0_28,plain,(
    ! [X14] :
      ( ( l1_lattices(X14)
        | ~ l3_lattices(X14) )
      & ( l2_lattices(X14)
        | ~ l3_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r3_lattices(X15,X16,X17)
        | r1_lattices(X15,X16,X17)
        | v2_struct_0(X15)
        | ~ v6_lattices(X15)
        | ~ v8_lattices(X15)
        | ~ v9_lattices(X15)
        | ~ l3_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15)) )
      & ( ~ r1_lattices(X15,X16,X17)
        | r3_lattices(X15,X16,X17)
        | v2_struct_0(X15)
        | ~ v6_lattices(X15)
        | ~ v8_lattices(X15)
        | ~ v9_lattices(X15)
        | ~ l3_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_32,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_34,plain,(
    ! [X30,X31,X32] :
      ( ( r3_lattices(X30,X31,k15_lattice3(X30,X32))
        | ~ r2_hidden(X31,X32)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30) )
      & ( r3_lattices(X30,k16_lattice3(X30,X32),X31)
        | ~ r2_hidden(X31,X32)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

cnf(c_0_35,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk7_0) = X1
    | ~ r1_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v4_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_39,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v6_lattices(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | k2_lattices(X23,X24,X25) = k2_lattices(X23,X25,X24)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) )
      & ( m1_subset_1(esk4_1(X23),u1_struct_0(X23))
        | v6_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) )
      & ( m1_subset_1(esk5_1(X23),u1_struct_0(X23))
        | v6_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) )
      & ( k2_lattices(X23,esk4_1(X23),esk5_1(X23)) != k2_lattices(X23,esk5_1(X23),esk4_1(X23))
        | v6_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_16]),c_0_17])).

cnf(c_0_41,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( v8_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( v6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_44,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk7_0) = X1
    | ~ r1_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_16])])).

cnf(c_0_46,negated_conjecture,
    ( r1_lattices(esk6_0,k15_lattice3(esk6_0,X1),esk7_0)
    | ~ r4_lattice3(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_38]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_47,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_40]),c_0_22]),c_0_16])]),c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( k1_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2)) = k15_lattice3(esk6_0,X2)
    | ~ r1_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_40]),c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))
    | ~ r3_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_22]),c_0_42]),c_0_43]),c_0_16])]),c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( r3_lattices(esk6_0,esk7_0,k15_lattice3(esk6_0,X1))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_21]),c_0_38]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),esk7_0) = k15_lattice3(esk6_0,X1)
    | ~ r4_lattice3(esk6_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_40])])).

cnf(c_0_53,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk7_0) = k2_lattices(esk6_0,esk7_0,X1)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_21]),c_0_43])]),c_0_17])).

cnf(c_0_54,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2)) = X1
    | ~ r1_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_lattices(esk6_0,esk7_0,k15_lattice3(esk6_0,X1))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_21])])).

cnf(c_0_56,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k15_lattice3(esk6_0,X1)) = k15_lattice3(esk6_0,X1)
    | ~ r4_lattice3(esk6_0,esk7_0,X1)
    | ~ l1_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_40])])).

cnf(c_0_57,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k15_lattice3(esk6_0,X1)) = esk7_0
    | ~ r2_hidden(esk7_0,X1)
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_21])])).

cnf(c_0_58,negated_conjecture,
    ( k15_lattice3(esk6_0,X1) = esk7_0
    | ~ r2_hidden(esk7_0,X1)
    | ~ r4_lattice3(esk6_0,esk7_0,X1)
    | ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_60,negated_conjecture,
    ( r4_lattice3(esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_61,negated_conjecture,
    ( k15_lattice3(esk6_0,esk8_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_62,negated_conjecture,
    ( ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( ~ l1_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_36]),c_0_16])])).

cnf(c_0_64,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t41_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r4_lattice3(X1,X2,X3))=>k15_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattice3)).
% 0.13/0.39  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.13/0.39  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 0.13/0.39  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 0.13/0.39  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.13/0.39  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.13/0.39  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.13/0.39  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.13/0.39  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 0.13/0.39  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 0.13/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r4_lattice3(X1,X2,X3))=>k15_lattice3(X1,X3)=X2)))), inference(assume_negation,[status(cth)],[t41_lattice3])).
% 0.13/0.39  fof(c_0_11, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.13/0.39  fof(c_0_12, negated_conjecture, ((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v4_lattice3(esk6_0))&l3_lattices(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&((r2_hidden(esk7_0,esk8_0)&r4_lattice3(esk6_0,esk7_0,esk8_0))&k15_lattice3(esk6_0,esk8_0)!=esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.13/0.39  fof(c_0_13, plain, ![X9, X10, X11]:((~v9_lattices(X9)|(~m1_subset_1(X10,u1_struct_0(X9))|(~m1_subset_1(X11,u1_struct_0(X9))|k2_lattices(X9,X10,k1_lattices(X9,X10,X11))=X10))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk1_1(X9),u1_struct_0(X9))|v9_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk2_1(X9),u1_struct_0(X9))|v9_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&(k2_lattices(X9,esk1_1(X9),k1_lattices(X9,esk1_1(X9),esk2_1(X9)))!=esk1_1(X9)|v9_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.13/0.39  cnf(c_0_14, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_15, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  fof(c_0_18, plain, ![X6, X7, X8]:((~r1_lattices(X6,X7,X8)|k1_lattices(X6,X7,X8)=X8|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l2_lattices(X6)))&(k1_lattices(X6,X7,X8)!=X8|r1_lattices(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l2_lattices(X6)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.13/0.39  fof(c_0_19, plain, ![X18, X19, X20, X21]:(((r4_lattice3(X18,X20,X19)|X20!=k15_lattice3(X18,X19)|~m1_subset_1(X20,u1_struct_0(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~v4_lattice3(X18)|~l3_lattices(X18))|(v2_struct_0(X18)|~l3_lattices(X18)))&(~m1_subset_1(X21,u1_struct_0(X18))|(~r4_lattice3(X18,X21,X19)|r1_lattices(X18,X20,X21))|X20!=k15_lattice3(X18,X19)|~m1_subset_1(X20,u1_struct_0(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~v4_lattice3(X18)|~l3_lattices(X18))|(v2_struct_0(X18)|~l3_lattices(X18))))&((m1_subset_1(esk3_3(X18,X19,X20),u1_struct_0(X18))|~r4_lattice3(X18,X20,X19)|X20=k15_lattice3(X18,X19)|~m1_subset_1(X20,u1_struct_0(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~v4_lattice3(X18)|~l3_lattices(X18))|(v2_struct_0(X18)|~l3_lattices(X18)))&((r4_lattice3(X18,esk3_3(X18,X19,X20),X19)|~r4_lattice3(X18,X20,X19)|X20=k15_lattice3(X18,X19)|~m1_subset_1(X20,u1_struct_0(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~v4_lattice3(X18)|~l3_lattices(X18))|(v2_struct_0(X18)|~l3_lattices(X18)))&(~r1_lattices(X18,X20,esk3_3(X18,X19,X20))|~r4_lattice3(X18,X20,X19)|X20=k15_lattice3(X18,X19)|~m1_subset_1(X20,u1_struct_0(X18))|(v2_struct_0(X18)|~v10_lattices(X18)|~v4_lattice3(X18)|~l3_lattices(X18))|(v2_struct_0(X18)|~l3_lattices(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.13/0.39  cnf(c_0_20, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (v9_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])]), c_0_17])).
% 0.13/0.39  cnf(c_0_23, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_24, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  fof(c_0_25, plain, ![X28, X29]:(v2_struct_0(X28)|~l3_lattices(X28)|m1_subset_1(k15_lattice3(X28,X29),u1_struct_0(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X1,esk7_0))=X1|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_16])]), c_0_17])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (k1_lattices(esk6_0,X1,esk7_0)=esk7_0|~r1_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_21]), c_0_17])).
% 0.13/0.39  fof(c_0_28, plain, ![X14]:((l1_lattices(X14)|~l3_lattices(X14))&(l2_lattices(X14)|~l3_lattices(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.13/0.39  cnf(c_0_29, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_30, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  fof(c_0_31, plain, ![X15, X16, X17]:((~r3_lattices(X15,X16,X17)|r1_lattices(X15,X16,X17)|(v2_struct_0(X15)|~v6_lattices(X15)|~v8_lattices(X15)|~v9_lattices(X15)|~l3_lattices(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))))&(~r1_lattices(X15,X16,X17)|r3_lattices(X15,X16,X17)|(v2_struct_0(X15)|~v6_lattices(X15)|~v8_lattices(X15)|~v9_lattices(X15)|~l3_lattices(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.13/0.39  cnf(c_0_32, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_33, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  fof(c_0_34, plain, ![X30, X31, X32]:((r3_lattices(X30,X31,k15_lattice3(X30,X32))|~r2_hidden(X31,X32)|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30)))&(r3_lattices(X30,k16_lattice3(X30,X32),X31)|~r2_hidden(X31,X32)|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (k2_lattices(esk6_0,X1,esk7_0)=X1|~r1_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.39  cnf(c_0_36, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_37, plain, (r1_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~v4_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_30])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (v4_lattice3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  fof(c_0_39, plain, ![X23, X24, X25]:((~v6_lattices(X23)|(~m1_subset_1(X24,u1_struct_0(X23))|(~m1_subset_1(X25,u1_struct_0(X23))|k2_lattices(X23,X24,X25)=k2_lattices(X23,X25,X24)))|(v2_struct_0(X23)|~l1_lattices(X23)))&((m1_subset_1(esk4_1(X23),u1_struct_0(X23))|v6_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23)))&((m1_subset_1(esk5_1(X23),u1_struct_0(X23))|v6_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23)))&(k2_lattices(X23,esk4_1(X23),esk5_1(X23))!=k2_lattices(X23,esk5_1(X23),esk4_1(X23))|v6_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (m1_subset_1(k15_lattice3(esk6_0,X1),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_16]), c_0_17])).
% 0.13/0.39  cnf(c_0_41, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (v8_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_15]), c_0_16])]), c_0_17])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (v6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_15]), c_0_16])]), c_0_17])).
% 0.13/0.39  cnf(c_0_44, plain, (r3_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (k2_lattices(esk6_0,X1,esk7_0)=X1|~r1_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_16])])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (r1_lattices(esk6_0,k15_lattice3(esk6_0,X1),esk7_0)|~r4_lattice3(esk6_0,esk7_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_38]), c_0_15]), c_0_16])]), c_0_17])).
% 0.13/0.39  cnf(c_0_47, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2)))=X1|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_40]), c_0_22]), c_0_16])]), c_0_17])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (k1_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))=k15_lattice3(esk6_0,X2)|~r1_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_40]), c_0_17])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (r1_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))|~r3_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_22]), c_0_42]), c_0_43]), c_0_16])]), c_0_17])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (r3_lattices(esk6_0,esk7_0,k15_lattice3(esk6_0,X1))|~r2_hidden(esk7_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_21]), c_0_38]), c_0_15]), c_0_16])]), c_0_17])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),esk7_0)=k15_lattice3(esk6_0,X1)|~r4_lattice3(esk6_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_40])])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (k2_lattices(esk6_0,X1,esk7_0)=k2_lattices(esk6_0,esk7_0,X1)|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_21]), c_0_43])]), c_0_17])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (k2_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))=X1|~r1_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (r1_lattices(esk6_0,esk7_0,k15_lattice3(esk6_0,X1))|~r2_hidden(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_21])])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k15_lattice3(esk6_0,X1))=k15_lattice3(esk6_0,X1)|~r4_lattice3(esk6_0,esk7_0,X1)|~l1_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_40])])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k15_lattice3(esk6_0,X1))=esk7_0|~r2_hidden(esk7_0,X1)|~l2_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_21])])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (k15_lattice3(esk6_0,X1)=esk7_0|~r2_hidden(esk7_0,X1)|~r4_lattice3(esk6_0,esk7_0,X1)|~l1_lattices(esk6_0)|~l2_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (r2_hidden(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (r4_lattice3(esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (k15_lattice3(esk6_0,esk8_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (~l1_lattices(esk6_0)|~l2_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])]), c_0_61])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (~l1_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_36]), c_0_16])])).
% 0.13/0.39  cnf(c_0_64, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_16])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 66
% 0.13/0.39  # Proof object clause steps            : 45
% 0.13/0.39  # Proof object formula steps           : 21
% 0.13/0.39  # Proof object conjectures             : 34
% 0.13/0.39  # Proof object clause conjectures      : 31
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 20
% 0.13/0.39  # Proof object initial formulas used   : 10
% 0.13/0.39  # Proof object generating inferences   : 23
% 0.13/0.39  # Proof object simplifying inferences  : 59
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 10
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 37
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 36
% 0.13/0.39  # Processed clauses                    : 113
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 113
% 0.13/0.39  # Other redundant clauses eliminated   : 2
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 2
% 0.13/0.39  # Backward-rewritten                   : 0
% 0.13/0.39  # Generated clauses                    : 58
% 0.13/0.39  # ...of the previous two non-trivial   : 48
% 0.13/0.39  # Contextual simplify-reflections      : 2
% 0.13/0.39  # Paramodulations                      : 56
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 2
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 73
% 0.13/0.39  #    Positive orientable unit clauses  : 14
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 3
% 0.13/0.39  #    Non-unit-clauses                  : 56
% 0.13/0.39  # Current number of unprocessed clauses: 7
% 0.13/0.39  # ...number of literals in the above   : 32
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 38
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1168
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 227
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.39  # Unit Clause-clause subsumption calls : 36
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 0
% 0.13/0.39  # BW rewrite match successes           : 0
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 5575
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.034 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.039 s
% 0.13/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
