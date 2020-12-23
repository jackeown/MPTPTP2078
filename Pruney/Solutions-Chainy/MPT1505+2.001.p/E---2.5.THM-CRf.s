%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:00 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 205 expanded)
%              Number of clauses        :   43 (  74 expanded)
%              Number of leaves         :    9 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  526 (1875 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal clause size      :   50 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(t38_lattice3,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattice3)).

fof(d17_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r4_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(d16_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(c_0_9,plain,(
    ! [X28,X29,X30,X31] :
      ( ( r4_lattice3(X28,X30,X29)
        | X30 != k15_lattice3(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28)
        | v2_struct_0(X28)
        | ~ l3_lattices(X28) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X28))
        | ~ r4_lattice3(X28,X31,X29)
        | r1_lattices(X28,X30,X31)
        | X30 != k15_lattice3(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28)
        | v2_struct_0(X28)
        | ~ l3_lattices(X28) )
      & ( m1_subset_1(esk6_3(X28,X29,X30),u1_struct_0(X28))
        | ~ r4_lattice3(X28,X30,X29)
        | X30 = k15_lattice3(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28)
        | v2_struct_0(X28)
        | ~ l3_lattices(X28) )
      & ( r4_lattice3(X28,esk6_3(X28,X29,X30),X29)
        | ~ r4_lattice3(X28,X30,X29)
        | X30 = k15_lattice3(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28)
        | v2_struct_0(X28)
        | ~ l3_lattices(X28) )
      & ( ~ r1_lattices(X28,X30,esk6_3(X28,X29,X30))
        | ~ r4_lattice3(X28,X30,X29)
        | X30 = k15_lattice3(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28)
        | v2_struct_0(X28)
        | ~ l3_lattices(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t38_lattice3])).

fof(c_0_11,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r3_lattices(X6,X7,X8)
        | r1_lattices(X6,X7,X8)
        | v2_struct_0(X6)
        | ~ v6_lattices(X6)
        | ~ v8_lattices(X6)
        | ~ v9_lattices(X6)
        | ~ l3_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6)) )
      & ( ~ r1_lattices(X6,X7,X8)
        | r3_lattices(X6,X7,X8)
        | v2_struct_0(X6)
        | ~ v6_lattices(X6)
        | ~ v8_lattices(X6)
        | ~ v9_lattices(X6)
        | ~ l3_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_12,plain,(
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

cnf(c_0_13,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk6_3(X1,X3,X2))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X21,X22,X24,X26] :
      ( ( m1_subset_1(esk3_2(X21,X22),u1_struct_0(X21))
        | ~ v4_lattice3(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( r4_lattice3(X21,esk3_2(X21,X22),X22)
        | ~ v4_lattice3(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r4_lattice3(X21,X24,X22)
        | r1_lattices(X21,esk3_2(X21,X22),X24)
        | ~ v4_lattice3(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( m1_subset_1(esk5_2(X21,X26),u1_struct_0(X21))
        | ~ m1_subset_1(X26,u1_struct_0(X21))
        | ~ r4_lattice3(X21,X26,esk4_1(X21))
        | v4_lattice3(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( r4_lattice3(X21,esk5_2(X21,X26),esk4_1(X21))
        | ~ m1_subset_1(X26,u1_struct_0(X21))
        | ~ r4_lattice3(X21,X26,esk4_1(X21))
        | v4_lattice3(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( ~ r1_lattices(X21,X26,esk5_2(X21,X26))
        | ~ m1_subset_1(X26,u1_struct_0(X21))
        | ~ r4_lattice3(X21,X26,esk4_1(X21))
        | v4_lattice3(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattice3])])])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v10_lattices(esk8_0)
    & v4_lattice3(esk8_0)
    & l3_lattices(esk8_0)
    & m1_subset_1(esk9_0,u1_struct_0(esk8_0))
    & r2_hidden(esk9_0,esk10_0)
    & ( ~ r3_lattices(esk8_0,esk9_0,k15_lattice3(esk8_0,esk10_0))
      | ~ r3_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_17,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r4_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,X17)
        | r1_lattices(X15,X18,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))
        | r4_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( r2_hidden(esk2_3(X15,X16,X19),X19)
        | r4_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( ~ r1_lattices(X15,esk2_3(X15,X16,X19),X16)
        | r4_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk6_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r1_lattices(X2,esk3_2(X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( r4_lattice3(X1,esk6_3(X1,X2,X3),X2)
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( ~ r3_lattices(esk8_0,esk9_0,k15_lattice3(esk8_0,esk10_0))
    | ~ r3_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v10_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( l3_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( esk3_2(X1,X2) = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,esk6_3(X1,X3,esk3_2(X1,X2)),X2)
    | ~ r4_lattice3(X1,esk3_2(X1,X2),X3)
    | ~ m1_subset_1(esk6_3(X1,X3,esk3_2(X1,X2)),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_36,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk6_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r4_lattice3(X1,esk3_2(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_39,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( ( r3_lattice3(X35,X36,X37)
        | X36 != k16_lattice3(X35,X37)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( ~ m1_subset_1(X38,u1_struct_0(X35))
        | ~ r3_lattice3(X35,X38,X37)
        | r3_lattices(X35,X38,X36)
        | X36 != k16_lattice3(X35,X37)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( m1_subset_1(esk7_3(X35,X36,X39),u1_struct_0(X35))
        | ~ r3_lattice3(X35,X36,X39)
        | X36 = k16_lattice3(X35,X39)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( r3_lattice3(X35,esk7_3(X35,X36,X39),X39)
        | ~ r3_lattice3(X35,X36,X39)
        | X36 = k16_lattice3(X35,X39)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( ~ r3_lattices(X35,esk7_3(X35,X36,X39),X36)
        | ~ r3_lattice3(X35,X36,X39)
        | X36 = k16_lattice3(X35,X39)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

fof(c_0_40,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ l3_lattices(X33)
      | m1_subset_1(k16_lattice3(X33,X34),u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0)
    | ~ r3_lattices(esk8_0,esk9_0,k15_lattice3(esk8_0,esk10_0))
    | ~ m1_subset_1(k16_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_42,plain,
    ( r1_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(k15_lattice3(X1,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,plain,
    ( esk3_2(X1,X2) = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk6_3(X1,X2,esk3_2(X1,X2)),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_25]),c_0_37])).

cnf(c_0_45,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r3_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X12,X11)
        | r1_lattices(X9,X10,X12)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X13),u1_struct_0(X9))
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( r2_hidden(esk1_3(X9,X10,X13),X13)
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( ~ r1_lattices(X9,X10,esk1_3(X9,X10,X13))
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_47,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0)
    | ~ r1_lattices(esk8_0,esk9_0,k15_lattice3(esk8_0,esk10_0))
    | ~ m1_subset_1(k16_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0))
    | ~ m1_subset_1(k15_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattices(X1,esk9_0,k15_lattice3(X1,esk10_0))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(k15_lattice3(X1,esk10_0),u1_struct_0(X1))
    | ~ m1_subset_1(esk9_0,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v4_lattice3(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_52,plain,
    ( esk3_2(X1,X2) = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_25]),c_0_37])).

cnf(c_0_53,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0)
    | ~ m1_subset_1(k16_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0))
    | ~ m1_subset_1(k15_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_56,plain,
    ( m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_52])).

cnf(c_0_57,plain,
    ( r1_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0)
    | ~ m1_subset_1(k16_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_51]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattices(X1,k16_lattice3(X1,esk10_0),esk9_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk9_0,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(k16_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_51]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_48]),c_0_31])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.32  % Computer   : n016.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 18:51:49 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.33  # Version: 2.5pre002
% 0.10/0.33  # No SInE strategy applied
% 0.10/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.18/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.031 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.18/0.37  fof(t38_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 0.18/0.37  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.18/0.37  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.18/0.37  fof(d18_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v4_lattice3(X1)<=>![X2]:?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r4_lattice3(X1,X3,X2))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_lattice3)).
% 0.18/0.37  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.18/0.37  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.18/0.37  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.18/0.37  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.18/0.37  fof(c_0_9, plain, ![X28, X29, X30, X31]:(((r4_lattice3(X28,X30,X29)|X30!=k15_lattice3(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))|(v2_struct_0(X28)|~l3_lattices(X28)))&(~m1_subset_1(X31,u1_struct_0(X28))|(~r4_lattice3(X28,X31,X29)|r1_lattices(X28,X30,X31))|X30!=k15_lattice3(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))|(v2_struct_0(X28)|~l3_lattices(X28))))&((m1_subset_1(esk6_3(X28,X29,X30),u1_struct_0(X28))|~r4_lattice3(X28,X30,X29)|X30=k15_lattice3(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))|(v2_struct_0(X28)|~l3_lattices(X28)))&((r4_lattice3(X28,esk6_3(X28,X29,X30),X29)|~r4_lattice3(X28,X30,X29)|X30=k15_lattice3(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))|(v2_struct_0(X28)|~l3_lattices(X28)))&(~r1_lattices(X28,X30,esk6_3(X28,X29,X30))|~r4_lattice3(X28,X30,X29)|X30=k15_lattice3(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))|(v2_struct_0(X28)|~l3_lattices(X28)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.18/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2)))))), inference(assume_negation,[status(cth)],[t38_lattice3])).
% 0.18/0.37  fof(c_0_11, plain, ![X6, X7, X8]:((~r3_lattices(X6,X7,X8)|r1_lattices(X6,X7,X8)|(v2_struct_0(X6)|~v6_lattices(X6)|~v8_lattices(X6)|~v9_lattices(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))&(~r1_lattices(X6,X7,X8)|r3_lattices(X6,X7,X8)|(v2_struct_0(X6)|~v6_lattices(X6)|~v8_lattices(X6)|~v9_lattices(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.18/0.37  fof(c_0_12, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.18/0.37  cnf(c_0_13, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_14, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk6_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  fof(c_0_15, plain, ![X21, X22, X24, X26]:((((m1_subset_1(esk3_2(X21,X22),u1_struct_0(X21))|~v4_lattice3(X21)|(v2_struct_0(X21)|~l3_lattices(X21)))&(r4_lattice3(X21,esk3_2(X21,X22),X22)|~v4_lattice3(X21)|(v2_struct_0(X21)|~l3_lattices(X21))))&(~m1_subset_1(X24,u1_struct_0(X21))|(~r4_lattice3(X21,X24,X22)|r1_lattices(X21,esk3_2(X21,X22),X24))|~v4_lattice3(X21)|(v2_struct_0(X21)|~l3_lattices(X21))))&((m1_subset_1(esk5_2(X21,X26),u1_struct_0(X21))|(~m1_subset_1(X26,u1_struct_0(X21))|~r4_lattice3(X21,X26,esk4_1(X21)))|v4_lattice3(X21)|(v2_struct_0(X21)|~l3_lattices(X21)))&((r4_lattice3(X21,esk5_2(X21,X26),esk4_1(X21))|(~m1_subset_1(X26,u1_struct_0(X21))|~r4_lattice3(X21,X26,esk4_1(X21)))|v4_lattice3(X21)|(v2_struct_0(X21)|~l3_lattices(X21)))&(~r1_lattices(X21,X26,esk5_2(X21,X26))|(~m1_subset_1(X26,u1_struct_0(X21))|~r4_lattice3(X21,X26,esk4_1(X21)))|v4_lattice3(X21)|(v2_struct_0(X21)|~l3_lattices(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattice3])])])])])])).
% 0.18/0.37  fof(c_0_16, negated_conjecture, ((((~v2_struct_0(esk8_0)&v10_lattices(esk8_0))&v4_lattice3(esk8_0))&l3_lattices(esk8_0))&(m1_subset_1(esk9_0,u1_struct_0(esk8_0))&(r2_hidden(esk9_0,esk10_0)&(~r3_lattices(esk8_0,esk9_0,k15_lattice3(esk8_0,esk10_0))|~r3_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.18/0.37  cnf(c_0_17, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_18, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_19, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_20, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  fof(c_0_21, plain, ![X15, X16, X17, X18, X19]:((~r4_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X17)|r1_lattices(X15,X18,X16)))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))|r4_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((r2_hidden(esk2_3(X15,X16,X19),X19)|r4_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&(~r1_lattices(X15,esk2_3(X15,X16,X19),X16)|r4_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.18/0.37  cnf(c_0_22, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_13])).
% 0.18/0.37  cnf(c_0_23, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk6_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_24, plain, (r1_lattices(X2,esk3_2(X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_25, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_26, plain, (r4_lattice3(X1,esk6_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_27, negated_conjecture, (~r3_lattices(esk8_0,esk9_0,k15_lattice3(esk8_0,esk10_0))|~r3_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  cnf(c_0_28, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])).
% 0.18/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (v10_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  cnf(c_0_31, negated_conjecture, (l3_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  cnf(c_0_33, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_34, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_22])).
% 0.18/0.37  cnf(c_0_35, plain, (esk3_2(X1,X2)=k15_lattice3(X1,X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,esk6_3(X1,X3,esk3_2(X1,X2)),X2)|~r4_lattice3(X1,esk3_2(X1,X2),X3)|~m1_subset_1(esk6_3(X1,X3,esk3_2(X1,X2)),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.18/0.37  cnf(c_0_36, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk6_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_26])).
% 0.18/0.37  cnf(c_0_37, plain, (r4_lattice3(X1,esk3_2(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_38, plain, (m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  fof(c_0_39, plain, ![X35, X36, X37, X38, X39]:(((r3_lattice3(X35,X36,X37)|X36!=k16_lattice3(X35,X37)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))&(~m1_subset_1(X38,u1_struct_0(X35))|(~r3_lattice3(X35,X38,X37)|r3_lattices(X35,X38,X36))|X36!=k16_lattice3(X35,X37)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35))))&((m1_subset_1(esk7_3(X35,X36,X39),u1_struct_0(X35))|~r3_lattice3(X35,X36,X39)|X36=k16_lattice3(X35,X39)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))&((r3_lattice3(X35,esk7_3(X35,X36,X39),X39)|~r3_lattice3(X35,X36,X39)|X36=k16_lattice3(X35,X39)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))&(~r3_lattices(X35,esk7_3(X35,X36,X39),X36)|~r3_lattice3(X35,X36,X39)|X36=k16_lattice3(X35,X39)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.18/0.37  fof(c_0_40, plain, ![X33, X34]:(v2_struct_0(X33)|~l3_lattices(X33)|m1_subset_1(k16_lattice3(X33,X34),u1_struct_0(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.18/0.37  cnf(c_0_41, negated_conjecture, (~r1_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0)|~r3_lattices(esk8_0,esk9_0,k15_lattice3(esk8_0,esk10_0))|~m1_subset_1(k16_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.18/0.37  cnf(c_0_42, plain, (r1_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X2,X3)|~m1_subset_1(k15_lattice3(X1,X3),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  cnf(c_0_44, plain, (esk3_2(X1,X2)=k15_lattice3(X1,X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk6_3(X1,X2,esk3_2(X1,X2)),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_25]), c_0_37])).
% 0.18/0.37  cnf(c_0_45, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_38])).
% 0.18/0.37  fof(c_0_46, plain, ![X9, X10, X11, X12, X13]:((~r3_lattice3(X9,X10,X11)|(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X11)|r1_lattices(X9,X10,X12)))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk1_3(X9,X10,X13),u1_struct_0(X9))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((r2_hidden(esk1_3(X9,X10,X13),X13)|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&(~r1_lattices(X9,X10,esk1_3(X9,X10,X13))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.18/0.37  cnf(c_0_47, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.37  cnf(c_0_48, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.37  cnf(c_0_49, negated_conjecture, (~r1_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0)|~r1_lattices(esk8_0,esk9_0,k15_lattice3(esk8_0,esk10_0))|~m1_subset_1(k16_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0))|~m1_subset_1(k15_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.18/0.37  cnf(c_0_50, negated_conjecture, (r1_lattices(X1,esk9_0,k15_lattice3(X1,esk10_0))|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(k15_lattice3(X1,esk10_0),u1_struct_0(X1))|~m1_subset_1(esk9_0,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.37  cnf(c_0_51, negated_conjecture, (v4_lattice3(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  cnf(c_0_52, plain, (esk3_2(X1,X2)=k15_lattice3(X1,X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_25]), c_0_37])).
% 0.18/0.37  cnf(c_0_53, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.37  cnf(c_0_54, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_48])).
% 0.18/0.37  cnf(c_0_55, negated_conjecture, (~r1_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0)|~m1_subset_1(k16_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0))|~m1_subset_1(k15_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.18/0.37  cnf(c_0_56, plain, (m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_25, c_0_52])).
% 0.18/0.37  cnf(c_0_57, plain, (r1_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_48])).
% 0.18/0.37  cnf(c_0_58, negated_conjecture, (~r1_lattices(esk8_0,k16_lattice3(esk8_0,esk10_0),esk9_0)|~m1_subset_1(k16_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_51]), c_0_30]), c_0_31])]), c_0_32])).
% 0.18/0.37  cnf(c_0_59, negated_conjecture, (r1_lattices(X1,k16_lattice3(X1,esk10_0),esk9_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk9_0,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_57, c_0_43])).
% 0.18/0.37  cnf(c_0_60, negated_conjecture, (~m1_subset_1(k16_lattice3(esk8_0,esk10_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_51]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.18/0.37  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_48]), c_0_31])]), c_0_32]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 62
% 0.18/0.37  # Proof object clause steps            : 43
% 0.18/0.37  # Proof object formula steps           : 19
% 0.18/0.37  # Proof object conjectures             : 18
% 0.18/0.37  # Proof object clause conjectures      : 15
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 22
% 0.18/0.37  # Proof object initial formulas used   : 9
% 0.18/0.37  # Proof object generating inferences   : 17
% 0.18/0.37  # Proof object simplifying inferences  : 43
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 9
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 41
% 0.18/0.37  # Removed in clause preprocessing      : 1
% 0.18/0.37  # Initial clauses in saturation        : 40
% 0.18/0.37  # Processed clauses                    : 112
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 0
% 0.18/0.37  # ...remaining for further processing  : 112
% 0.18/0.37  # Other redundant clauses eliminated   : 0
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 6
% 0.18/0.37  # Backward-rewritten                   : 0
% 0.18/0.37  # Generated clauses                    : 60
% 0.18/0.37  # ...of the previous two non-trivial   : 55
% 0.18/0.37  # Contextual simplify-reflections      : 22
% 0.18/0.37  # Paramodulations                      : 58
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 2
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 66
% 0.18/0.37  #    Positive orientable unit clauses  : 5
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 3
% 0.18/0.37  #    Non-unit-clauses                  : 58
% 0.18/0.37  # Current number of unprocessed clauses: 23
% 0.18/0.37  # ...number of literals in the above   : 203
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 46
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 1980
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 107
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 28
% 0.18/0.37  # Unit Clause-clause subsumption calls : 12
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 0
% 0.18/0.37  # BW rewrite match successes           : 0
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 6942
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.041 s
% 0.18/0.37  # System time              : 0.003 s
% 0.18/0.37  # Total time               : 0.044 s
% 0.18/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
