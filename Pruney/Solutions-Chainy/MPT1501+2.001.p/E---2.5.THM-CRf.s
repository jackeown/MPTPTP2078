%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 694 expanded)
%              Number of clauses        :   74 ( 242 expanded)
%              Number of leaves         :    8 ( 170 expanded)
%              Depth                    :   21
%              Number of atoms          :  668 (7329 expanded)
%              Number of equality atoms :   54 ( 987 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_lattice3,conjecture,(
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

fof(fraenkel_a_2_1_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r3_lattice3(X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(d22_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] : k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

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

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t34_lattice3])).

fof(c_0_9,negated_conjecture,(
    ! [X38] :
      ( ~ v2_struct_0(esk5_0)
      & v10_lattices(esk5_0)
      & v4_lattice3(esk5_0)
      & l3_lattices(esk5_0)
      & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
      & ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
        | ~ r3_lattice3(esk5_0,esk6_0,esk7_0)
        | esk6_0 != k16_lattice3(esk5_0,esk7_0) )
      & ( r3_lattice3(esk5_0,esk8_0,esk7_0)
        | ~ r3_lattice3(esk5_0,esk6_0,esk7_0)
        | esk6_0 != k16_lattice3(esk5_0,esk7_0) )
      & ( ~ r3_lattices(esk5_0,esk8_0,esk6_0)
        | ~ r3_lattice3(esk5_0,esk6_0,esk7_0)
        | esk6_0 != k16_lattice3(esk5_0,esk7_0) )
      & ( r3_lattice3(esk5_0,esk6_0,esk7_0)
        | esk6_0 = k16_lattice3(esk5_0,esk7_0) )
      & ( ~ m1_subset_1(X38,u1_struct_0(esk5_0))
        | ~ r3_lattice3(esk5_0,X38,esk7_0)
        | r3_lattices(esk5_0,X38,esk6_0)
        | esk6_0 = k16_lattice3(esk5_0,esk7_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

fof(c_0_10,plain,(
    ! [X28,X29,X30,X32,X33] :
      ( ( m1_subset_1(esk4_3(X28,X29,X30),u1_struct_0(X29))
        | ~ r2_hidden(X28,a_2_1_lattice3(X29,X30))
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) )
      & ( X28 = esk4_3(X28,X29,X30)
        | ~ r2_hidden(X28,a_2_1_lattice3(X29,X30))
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) )
      & ( r3_lattice3(X29,esk4_3(X28,X29,X30),X30)
        | ~ r2_hidden(X28,a_2_1_lattice3(X29,X30))
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X29))
        | X28 != X33
        | ~ r3_lattice3(X29,X33,X32)
        | r2_hidden(X28,a_2_1_lattice3(X29,X32))
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).

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

cnf(c_0_12,negated_conjecture,
    ( r3_lattices(esk5_0,X1,esk6_0)
    | esk6_0 = k16_lattice3(esk5_0,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r3_lattice3(esk5_0,X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r3_lattice3(X1,esk4_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
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

cnf(c_0_17,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) = esk6_0
    | r3_lattices(esk5_0,esk4_3(X1,esk5_0,esk7_0),esk6_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0))
    | ~ m1_subset_1(esk4_3(X1,esk5_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,plain,(
    ! [X21,X22,X23,X24] :
      ( ( r4_lattice3(X21,X23,X22)
        | X23 != k15_lattice3(X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r4_lattice3(X21,X24,X22)
        | r1_lattices(X21,X23,X24)
        | X23 != k15_lattice3(X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( m1_subset_1(esk3_3(X21,X22,X23),u1_struct_0(X21))
        | ~ r4_lattice3(X21,X23,X22)
        | X23 = k15_lattice3(X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( r4_lattice3(X21,esk3_3(X21,X22,X23),X22)
        | ~ r4_lattice3(X21,X23,X22)
        | X23 = k15_lattice3(X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( ~ r1_lattices(X21,X23,esk3_3(X21,X22,X23))
        | ~ r4_lattice3(X21,X23,X22)
        | X23 = k15_lattice3(X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) = esk6_0
    | r1_lattices(esk5_0,esk4_3(X1,esk5_0,esk7_0),esk6_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0))
    | ~ m1_subset_1(esk4_3(X1,esk5_0,esk7_0),u1_struct_0(esk5_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_14])]),c_0_15])).

cnf(c_0_21,plain,
    ( X1 = esk4_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_22,plain,(
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

fof(c_0_23,plain,(
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

cnf(c_0_24,plain,
    ( r4_lattice3(X1,esk3_3(X1,X2,X3),X2)
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) = esk6_0
    | r1_lattices(esk5_0,X1,esk6_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14])]),c_0_15])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk3_3(X1,X3,X2))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk3_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) = esk6_0
    | r4_lattice3(X1,X2,a_2_1_lattice3(esk5_0,esk7_0))
    | r1_lattices(esk5_0,esk2_3(X1,X2,a_2_1_lattice3(esk5_0,esk7_0)),esk6_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk2_3(X1,X2,a_2_1_lattice3(esk5_0,esk7_0)),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( r1_lattices(X1,esk4_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_13]),c_0_29])).

cnf(c_0_37,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk3_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( X1 = k15_lattice3(X2,X3)
    | r1_lattices(X2,X4,esk3_3(X2,X3,X1))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) = esk6_0
    | r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0))
    | ~ m1_subset_1(esk2_3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0)),u1_struct_0(esk5_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_14])]),c_0_15])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X4))
    | ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_21])).

cnf(c_0_42,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_43,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ l3_lattices(X26)
      | k16_lattice3(X26,X27) = k15_lattice3(X26,a_2_1_lattice3(X26,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattice3])])])])).

cnf(c_0_44,plain,
    ( X1 = k15_lattice3(X2,X3)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) = esk6_0
    | r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_18]),c_0_14])]),c_0_15])).

cnf(c_0_46,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_47,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,plain,
    ( r4_lattice3(X1,X2,a_2_1_lattice3(X3,X4))
    | r1_lattices(X3,esk2_3(X1,X2,a_2_1_lattice3(X3,X4)),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_1_lattice3(esk5_0,esk7_0)) = esk6_0
    | k16_lattice3(esk5_0,esk7_0) = esk6_0
    | ~ r2_hidden(esk6_0,a_2_1_lattice3(esk5_0,esk7_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_18]),c_0_47]),c_0_14])]),c_0_15])).

cnf(c_0_52,plain,
    ( r2_hidden(X3,a_2_1_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattice3(X2,X1,X4)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,plain,
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

cnf(c_0_54,plain,
    ( r4_lattice3(X1,X2,a_2_1_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_48])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_56,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) = esk6_0
    | ~ r2_hidden(esk6_0,a_2_1_lattice3(esk5_0,esk7_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_14])]),c_0_15])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r3_lattice3(esk5_0,esk6_0,esk7_0)
    | esk6_0 = k16_lattice3(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_60,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( r4_lattice3(X1,esk1_3(X2,X3,X4),a_2_1_lattice3(X1,X4))
    | r3_lattice3(X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk1_3(X2,X3,X4),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( r4_lattice3(X1,k16_lattice3(X1,X2),a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) = esk6_0
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_18]),c_0_14])]),c_0_15]),c_0_59])).

cnf(c_0_64,plain,
    ( r3_lattice3(X1,X2,X3)
    | r1_lattices(X4,X5,esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | X5 != k15_lattice3(X4,a_2_1_lattice3(X4,X3))
    | ~ v4_lattice3(X4)
    | ~ m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X4)
    | ~ l3_lattices(X4)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_65,plain,(
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

cnf(c_0_66,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_46]),c_0_18]),c_0_47]),c_0_14])]),c_0_15])).

cnf(c_0_67,plain,
    ( r3_lattice3(X1,X2,X3)
    | r1_lattices(X4,X5,esk1_3(X1,X2,X3))
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | X5 != k16_lattice3(X4,X3)
    | ~ v4_lattice3(X4)
    | ~ m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X4)
    | ~ l3_lattices(X4)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_50])).

cnf(c_0_68,plain,
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

cnf(c_0_69,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk6_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_66]),c_0_18]),c_0_14])]),c_0_15])).

cnf(c_0_73,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( r3_lattice3(esk5_0,esk6_0,esk7_0)
    | r3_lattice3(X1,X2,esk7_0)
    | r1_lattices(esk5_0,X3,esk1_3(X1,X2,esk7_0))
    | v2_struct_0(X1)
    | X3 != esk6_0
    | ~ m1_subset_1(esk1_3(X1,X2,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_59]),c_0_46]),c_0_47]),c_0_14])]),c_0_15])).

cnf(c_0_75,negated_conjecture,
    ( ~ r3_lattices(esk5_0,esk8_0,esk6_0)
    | ~ r3_lattice3(esk5_0,esk6_0,esk7_0)
    | esk6_0 != k16_lattice3(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_76,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    | ~ r3_lattice3(esk5_0,esk6_0,esk7_0)
    | esk6_0 != k16_lattice3(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_78,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk6_0)
    | ~ r3_lattice3(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_58]),c_0_14])]),c_0_15])).

cnf(c_0_79,negated_conjecture,
    ( r3_lattice3(esk5_0,esk8_0,esk7_0)
    | ~ r3_lattice3(esk5_0,esk6_0,esk7_0)
    | esk6_0 != k16_lattice3(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_80,negated_conjecture,
    ( r3_lattice3(esk5_0,esk6_0,esk7_0)
    | r3_lattice3(esk5_0,X1,esk7_0)
    | X1 != esk6_0
    | ~ m1_subset_1(esk1_3(esk5_0,X1,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_14])]),c_0_15])).

cnf(c_0_81,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_82,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) != esk6_0
    | ~ r3_lattice3(esk5_0,esk6_0,esk7_0)
    | ~ r1_lattices(esk5_0,esk8_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_18]),c_0_47]),c_0_14])]),c_0_15]),c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( r1_lattices(esk5_0,esk8_0,esk6_0)
    | ~ r3_lattice3(esk5_0,esk6_0,esk7_0)
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_77]),c_0_63])).

cnf(c_0_84,negated_conjecture,
    ( r3_lattice3(esk5_0,esk6_0,esk7_0)
    | r3_lattice3(esk5_0,X1,esk7_0)
    | X1 != esk6_0
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_14])]),c_0_15])).

cnf(c_0_85,negated_conjecture,
    ( ~ r3_lattice3(esk5_0,esk6_0,esk7_0)
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_63])).

cnf(c_0_86,negated_conjecture,
    ( r3_lattice3(esk5_0,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_18])).

cnf(c_0_87,negated_conjecture,
    ( ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_88,negated_conjecture,
    ( ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_69]),c_0_47]),c_0_14])]),c_0_15])).

cnf(c_0_89,negated_conjecture,
    ( ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_71]),c_0_47]),c_0_14])]),c_0_15])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_70]),c_0_47]),c_0_14])]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:35:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.030 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t34_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.20/0.43  fof(fraenkel_a_2_1_lattice3, axiom, ![X1, X2, X3]:((~(v2_struct_0(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_1_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 0.20/0.43  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.20/0.43  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 0.20/0.43  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 0.20/0.43  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 0.20/0.43  fof(d22_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:k16_lattice3(X1,X2)=k15_lattice3(X1,a_2_1_lattice3(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d22_lattice3)).
% 0.20/0.43  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.43  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2)))))))), inference(assume_negation,[status(cth)],[t34_lattice3])).
% 0.20/0.43  fof(c_0_9, negated_conjecture, ![X38]:((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v4_lattice3(esk5_0))&l3_lattices(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(((m1_subset_1(esk8_0,u1_struct_0(esk5_0))|~r3_lattice3(esk5_0,esk6_0,esk7_0)|esk6_0!=k16_lattice3(esk5_0,esk7_0))&((r3_lattice3(esk5_0,esk8_0,esk7_0)|~r3_lattice3(esk5_0,esk6_0,esk7_0)|esk6_0!=k16_lattice3(esk5_0,esk7_0))&(~r3_lattices(esk5_0,esk8_0,esk6_0)|~r3_lattice3(esk5_0,esk6_0,esk7_0)|esk6_0!=k16_lattice3(esk5_0,esk7_0))))&((r3_lattice3(esk5_0,esk6_0,esk7_0)|esk6_0=k16_lattice3(esk5_0,esk7_0))&(~m1_subset_1(X38,u1_struct_0(esk5_0))|(~r3_lattice3(esk5_0,X38,esk7_0)|r3_lattices(esk5_0,X38,esk6_0))|esk6_0=k16_lattice3(esk5_0,esk7_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).
% 0.20/0.43  fof(c_0_10, plain, ![X28, X29, X30, X32, X33]:((((m1_subset_1(esk4_3(X28,X29,X30),u1_struct_0(X29))|~r2_hidden(X28,a_2_1_lattice3(X29,X30))|(v2_struct_0(X29)|~l3_lattices(X29)))&(X28=esk4_3(X28,X29,X30)|~r2_hidden(X28,a_2_1_lattice3(X29,X30))|(v2_struct_0(X29)|~l3_lattices(X29))))&(r3_lattice3(X29,esk4_3(X28,X29,X30),X30)|~r2_hidden(X28,a_2_1_lattice3(X29,X30))|(v2_struct_0(X29)|~l3_lattices(X29))))&(~m1_subset_1(X33,u1_struct_0(X29))|X28!=X33|~r3_lattice3(X29,X33,X32)|r2_hidden(X28,a_2_1_lattice3(X29,X32))|(v2_struct_0(X29)|~l3_lattices(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).
% 0.20/0.43  fof(c_0_11, plain, ![X6, X7, X8]:((~r3_lattices(X6,X7,X8)|r1_lattices(X6,X7,X8)|(v2_struct_0(X6)|~v6_lattices(X6)|~v8_lattices(X6)|~v9_lattices(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))&(~r1_lattices(X6,X7,X8)|r3_lattices(X6,X7,X8)|(v2_struct_0(X6)|~v6_lattices(X6)|~v8_lattices(X6)|~v9_lattices(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.20/0.43  cnf(c_0_12, negated_conjecture, (r3_lattices(esk5_0,X1,esk6_0)|esk6_0=k16_lattice3(esk5_0,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r3_lattice3(esk5_0,X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_13, plain, (r3_lattice3(X1,esk4_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_14, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_16, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_17, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)=esk6_0|r3_lattices(esk5_0,esk4_3(X1,esk5_0,esk7_0),esk6_0)|~r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0))|~m1_subset_1(esk4_3(X1,esk5_0,esk7_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  fof(c_0_19, plain, ![X21, X22, X23, X24]:(((r4_lattice3(X21,X23,X22)|X23!=k15_lattice3(X21,X22)|~m1_subset_1(X23,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&(~m1_subset_1(X24,u1_struct_0(X21))|(~r4_lattice3(X21,X24,X22)|r1_lattices(X21,X23,X24))|X23!=k15_lattice3(X21,X22)|~m1_subset_1(X23,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21))|(v2_struct_0(X21)|~l3_lattices(X21))))&((m1_subset_1(esk3_3(X21,X22,X23),u1_struct_0(X21))|~r4_lattice3(X21,X23,X22)|X23=k15_lattice3(X21,X22)|~m1_subset_1(X23,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((r4_lattice3(X21,esk3_3(X21,X22,X23),X22)|~r4_lattice3(X21,X23,X22)|X23=k15_lattice3(X21,X22)|~m1_subset_1(X23,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&(~r1_lattices(X21,X23,esk3_3(X21,X22,X23))|~r4_lattice3(X21,X23,X22)|X23=k15_lattice3(X21,X22)|~m1_subset_1(X23,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.20/0.43  cnf(c_0_20, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)=esk6_0|r1_lattices(esk5_0,esk4_3(X1,esk5_0,esk7_0),esk6_0)|~r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0))|~m1_subset_1(esk4_3(X1,esk5_0,esk7_0),u1_struct_0(esk5_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_21, plain, (X1=esk4_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  fof(c_0_22, plain, ![X15, X16, X17, X18, X19]:((~r4_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X17)|r1_lattices(X15,X18,X16)))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))|r4_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((r2_hidden(esk2_3(X15,X16,X19),X19)|r4_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&(~r1_lattices(X15,esk2_3(X15,X16,X19),X16)|r4_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.20/0.43  fof(c_0_23, plain, ![X9, X10, X11, X12, X13]:((~r3_lattice3(X9,X10,X11)|(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X11)|r1_lattices(X9,X10,X12)))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk1_3(X9,X10,X13),u1_struct_0(X9))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((r2_hidden(esk1_3(X9,X10,X13),X13)|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&(~r1_lattices(X9,X10,esk1_3(X9,X10,X13))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.20/0.43  cnf(c_0_24, plain, (r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_25, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_26, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)=esk6_0|r1_lattices(esk5_0,X1,esk6_0)|~r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_27, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_28, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_29, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_30, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_31, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_32, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_33, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_34, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk2_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)=esk6_0|r4_lattice3(X1,X2,a_2_1_lattice3(esk5_0,esk7_0))|r1_lattices(esk5_0,esk2_3(X1,X2,a_2_1_lattice3(esk5_0,esk7_0)),esk6_0)|v2_struct_0(X1)|~m1_subset_1(esk2_3(X1,X2,a_2_1_lattice3(esk5_0,esk7_0)),u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.43  cnf(c_0_36, plain, (r1_lattices(X1,esk4_3(X2,X1,X3),X4)|v2_struct_0(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_13]), c_0_29])).
% 0.20/0.43  cnf(c_0_37, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_30])).
% 0.20/0.43  cnf(c_0_38, plain, (X1=k15_lattice3(X2,X3)|r1_lattices(X2,X4,esk3_3(X2,X3,X1))|v2_struct_0(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)=esk6_0|r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0))|~m1_subset_1(esk2_3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0)),u1_struct_0(esk5_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_18]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_40, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_41, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,X4))|~r2_hidden(X3,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_36, c_0_21])).
% 0.20/0.43  cnf(c_0_42, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  fof(c_0_43, plain, ![X26, X27]:(v2_struct_0(X26)|~l3_lattices(X26)|k16_lattice3(X26,X27)=k15_lattice3(X26,a_2_1_lattice3(X26,X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattice3])])])])).
% 0.20/0.43  cnf(c_0_44, plain, (X1=k15_lattice3(X2,X3)|v2_struct_0(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~r2_hidden(X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)=esk6_0|r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_18]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (v4_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_47, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_48, plain, (r4_lattice3(X1,X2,a_2_1_lattice3(X3,X4))|r1_lattices(X3,esk2_3(X1,X2,a_2_1_lattice3(X3,X4)),X5)|v2_struct_0(X1)|v2_struct_0(X3)|~r2_hidden(X5,X4)|~m1_subset_1(X5,u1_struct_0(X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X3)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.20/0.43  cnf(c_0_49, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_42])).
% 0.20/0.43  cnf(c_0_50, plain, (v2_struct_0(X1)|k16_lattice3(X1,X2)=k15_lattice3(X1,a_2_1_lattice3(X1,X2))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (k15_lattice3(esk5_0,a_2_1_lattice3(esk5_0,esk7_0))=esk6_0|k16_lattice3(esk5_0,esk7_0)=esk6_0|~r2_hidden(esk6_0,a_2_1_lattice3(esk5_0,esk7_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_18]), c_0_47]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_52, plain, (r2_hidden(X3,a_2_1_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattice3(X2,X1,X4)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_53, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_54, plain, (r4_lattice3(X1,X2,a_2_1_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_34, c_0_48])).
% 0.20/0.43  cnf(c_0_55, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_56, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_49])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)=esk6_0|~r2_hidden(esk6_0,a_2_1_lattice3(esk5_0,esk7_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_58, plain, (r2_hidden(X1,a_2_1_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_52])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (r3_lattice3(esk5_0,esk6_0,esk7_0)|esk6_0=k16_lattice3(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_60, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_53])).
% 0.20/0.43  cnf(c_0_61, plain, (r4_lattice3(X1,esk1_3(X2,X3,X4),a_2_1_lattice3(X1,X4))|r3_lattice3(X2,X3,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(esk1_3(X2,X3,X4),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X2))|~l3_lattices(X1)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.43  cnf(c_0_62, plain, (r4_lattice3(X1,k16_lattice3(X1,X2),a_2_1_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_56, c_0_50])).
% 0.20/0.43  cnf(c_0_63, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)=esk6_0|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_18]), c_0_14])]), c_0_15]), c_0_59])).
% 0.20/0.43  cnf(c_0_64, plain, (r3_lattice3(X1,X2,X3)|r1_lattices(X4,X5,esk1_3(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X4)|X5!=k15_lattice3(X4,a_2_1_lattice3(X4,X3))|~v4_lattice3(X4)|~m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X4)|~l3_lattices(X4)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.43  fof(c_0_65, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_46]), c_0_18]), c_0_47]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_67, plain, (r3_lattice3(X1,X2,X3)|r1_lattices(X4,X5,esk1_3(X1,X2,X3))|v2_struct_0(X4)|v2_struct_0(X1)|X5!=k16_lattice3(X4,X3)|~v4_lattice3(X4)|~m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X4)|~l3_lattices(X4)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_64, c_0_50])).
% 0.20/0.43  cnf(c_0_68, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_69, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.43  cnf(c_0_70, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.43  cnf(c_0_71, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.43  cnf(c_0_72, negated_conjecture, (r1_lattices(esk5_0,X1,esk6_0)|~r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_66]), c_0_18]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_73, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_74, negated_conjecture, (r3_lattice3(esk5_0,esk6_0,esk7_0)|r3_lattice3(X1,X2,esk7_0)|r1_lattices(esk5_0,X3,esk1_3(X1,X2,esk7_0))|v2_struct_0(X1)|X3!=esk6_0|~m1_subset_1(esk1_3(X1,X2,esk7_0),u1_struct_0(esk5_0))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_59]), c_0_46]), c_0_47]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_75, negated_conjecture, (~r3_lattices(esk5_0,esk8_0,esk6_0)|~r3_lattice3(esk5_0,esk6_0,esk7_0)|esk6_0!=k16_lattice3(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_76, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71])).
% 0.20/0.43  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))|~r3_lattice3(esk5_0,esk6_0,esk7_0)|esk6_0!=k16_lattice3(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_78, negated_conjecture, (r1_lattices(esk5_0,X1,esk6_0)|~r3_lattice3(esk5_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_58]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_79, negated_conjecture, (r3_lattice3(esk5_0,esk8_0,esk7_0)|~r3_lattice3(esk5_0,esk6_0,esk7_0)|esk6_0!=k16_lattice3(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_80, negated_conjecture, (r3_lattice3(esk5_0,esk6_0,esk7_0)|r3_lattice3(esk5_0,X1,esk7_0)|X1!=esk6_0|~m1_subset_1(esk1_3(esk5_0,X1,esk7_0),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_81, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_82, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)!=esk6_0|~r3_lattice3(esk5_0,esk6_0,esk7_0)|~r1_lattices(esk5_0,esk8_0,esk6_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_18]), c_0_47]), c_0_14])]), c_0_15]), c_0_77])).
% 0.20/0.43  cnf(c_0_83, negated_conjecture, (r1_lattices(esk5_0,esk8_0,esk6_0)|~r3_lattice3(esk5_0,esk6_0,esk7_0)|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_77]), c_0_63])).
% 0.20/0.43  cnf(c_0_84, negated_conjecture, (r3_lattice3(esk5_0,esk6_0,esk7_0)|r3_lattice3(esk5_0,X1,esk7_0)|X1!=esk6_0|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_85, negated_conjecture, (~r3_lattice3(esk5_0,esk6_0,esk7_0)|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_63])).
% 0.20/0.43  cnf(c_0_86, negated_conjecture, (r3_lattice3(esk5_0,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_84, c_0_18])).
% 0.20/0.43  cnf(c_0_87, negated_conjecture, (~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 0.20/0.43  cnf(c_0_88, negated_conjecture, (~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_69]), c_0_47]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_89, negated_conjecture, (~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_71]), c_0_47]), c_0_14])]), c_0_15])).
% 0.20/0.43  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_70]), c_0_47]), c_0_14])]), c_0_15]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 91
% 0.20/0.43  # Proof object clause steps            : 74
% 0.20/0.43  # Proof object formula steps           : 17
% 0.20/0.43  # Proof object conjectures             : 36
% 0.20/0.43  # Proof object clause conjectures      : 33
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 33
% 0.20/0.43  # Proof object initial formulas used   : 8
% 0.20/0.43  # Proof object generating inferences   : 34
% 0.20/0.43  # Proof object simplifying inferences  : 89
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 8
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 37
% 0.20/0.43  # Removed in clause preprocessing      : 1
% 0.20/0.43  # Initial clauses in saturation        : 36
% 0.20/0.43  # Processed clauses                    : 432
% 0.20/0.43  # ...of these trivial                  : 1
% 0.20/0.43  # ...subsumed                          : 129
% 0.20/0.43  # ...remaining for further processing  : 302
% 0.20/0.43  # Other redundant clauses eliminated   : 1
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 97
% 0.20/0.43  # Backward-rewritten                   : 44
% 0.20/0.43  # Generated clauses                    : 491
% 0.20/0.43  # ...of the previous two non-trivial   : 472
% 0.20/0.43  # Contextual simplify-reflections      : 45
% 0.20/0.43  # Paramodulations                      : 474
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 17
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 124
% 0.20/0.43  #    Positive orientable unit clauses  : 6
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 3
% 0.20/0.43  #    Non-unit-clauses                  : 115
% 0.20/0.43  # Current number of unprocessed clauses: 69
% 0.20/0.43  # ...number of literals in the above   : 682
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 177
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 15750
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 796
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 269
% 0.20/0.43  # Unit Clause-clause subsumption calls : 60
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 3
% 0.20/0.43  # BW rewrite match successes           : 2
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 22117
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.080 s
% 0.20/0.43  # System time              : 0.007 s
% 0.20/0.43  # Total time               : 0.087 s
% 0.20/0.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
