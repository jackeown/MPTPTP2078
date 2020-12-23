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
% DateTime   : Thu Dec  3 11:15:05 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   74 (2160 expanded)
%              Number of clauses        :   57 ( 699 expanded)
%              Number of leaves         :    8 ( 534 expanded)
%              Depth                    :   23
%              Number of atoms          :  462 (17967 expanded)
%              Number of equality atoms :   20 ( 306 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   50 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ~ ( r2_hidden(X4,X2)
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ~ ( r3_lattices(X1,X4,X5)
                          & r2_hidden(X5,X3) ) ) ) )
         => r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).

fof(t47_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
          & k16_lattice3(X1,X2) = k16_lattice3(X1,a_2_6_lattice3(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

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

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

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

fof(fraenkel_a_2_5_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_5_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ? [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
                & r3_lattices(X2,X4,X5)
                & r2_hidden(X5,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ~ ( r2_hidden(X4,X2)
                    & ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ~ ( r3_lattices(X1,X4,X5)
                            & r2_hidden(X5,X3) ) ) ) )
           => r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t48_lattice3])).

fof(c_0_9,plain,(
    ! [X31,X32] :
      ( ( k15_lattice3(X31,X32) = k15_lattice3(X31,a_2_5_lattice3(X31,X32))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ v4_lattice3(X31)
        | ~ l3_lattices(X31) )
      & ( k16_lattice3(X31,X32) = k16_lattice3(X31,a_2_6_lattice3(X31,X32))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ v4_lattice3(X31)
        | ~ l3_lattices(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X36] :
      ( ~ v2_struct_0(esk5_0)
      & v10_lattices(esk5_0)
      & v4_lattice3(esk5_0)
      & l3_lattices(esk5_0)
      & ( m1_subset_1(esk8_1(X36),u1_struct_0(esk5_0))
        | ~ r2_hidden(X36,esk6_0)
        | ~ m1_subset_1(X36,u1_struct_0(esk5_0)) )
      & ( r3_lattices(esk5_0,X36,esk8_1(X36))
        | ~ r2_hidden(X36,esk6_0)
        | ~ m1_subset_1(X36,u1_struct_0(esk5_0)) )
      & ( r2_hidden(esk8_1(X36),esk7_0)
        | ~ r2_hidden(X36,esk6_0)
        | ~ m1_subset_1(X36,u1_struct_0(esk5_0)) )
      & ~ r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0)) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

fof(c_0_11,plain,(
    ! [X16,X17,X18,X19] :
      ( ( r4_lattice3(X16,X18,X17)
        | X18 != k15_lattice3(X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v4_lattice3(X16)
        | ~ l3_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r4_lattice3(X16,X19,X17)
        | r1_lattices(X16,X18,X19)
        | X18 != k15_lattice3(X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v4_lattice3(X16)
        | ~ l3_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( m1_subset_1(esk2_3(X16,X17,X18),u1_struct_0(X16))
        | ~ r4_lattice3(X16,X18,X17)
        | X18 = k15_lattice3(X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v4_lattice3(X16)
        | ~ l3_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( r4_lattice3(X16,esk2_3(X16,X17,X18),X17)
        | ~ r4_lattice3(X16,X18,X17)
        | X18 = k15_lattice3(X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v4_lattice3(X16)
        | ~ l3_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( ~ r1_lattices(X16,X18,esk2_3(X16,X17,X18))
        | ~ r4_lattice3(X16,X18,X17)
        | X18 = k15_lattice3(X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v10_lattices(X16)
        | ~ v4_lattice3(X16)
        | ~ l3_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_12,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ l3_lattices(X21)
      | m1_subset_1(k15_lattice3(X21,X22),u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_13,plain,
    ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r4_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X12)
        | r1_lattices(X10,X13,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X14),u1_struct_0(X10))
        | r4_lattice3(X10,X11,X14)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( r2_hidden(esk1_3(X10,X11,X14),X14)
        | r4_lattice3(X10,X11,X14)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( ~ r1_lattices(X10,esk1_3(X10,X11,X14),X11)
        | r4_lattice3(X10,X11,X14)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_5_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_22,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk5_0,X1),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16])]),c_0_17])).

fof(c_0_25,plain,(
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

cnf(c_0_26,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r4_lattice3(esk5_0,k15_lattice3(esk5_0,X1),X2)
    | m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_16])]),c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))
    | m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_14]),c_0_24]),c_0_15]),c_0_16])]),c_0_17])).

fof(c_0_31,plain,(
    ! [X6] :
      ( ( ~ v2_struct_0(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v4_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v5_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v6_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v7_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v8_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v9_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)
    | r4_lattice3(esk5_0,k15_lattice3(esk5_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_16])]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( r3_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))
    | m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24]),c_0_24]),c_0_16])]),c_0_17])).

cnf(c_0_34,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)
    | r1_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_32]),c_0_14]),c_0_24]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( r3_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))
    | m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_37,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)
    | r3_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_35]),c_0_24]),c_0_24]),c_0_16])]),c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))
    | m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0))
    | ~ v9_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_40,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)
    | r3_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( ~ r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( r3_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))
    | m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)
    | r3_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))
    | ~ v9_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_45,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_46,plain,(
    ! [X23,X24,X25,X28,X29,X30] :
      ( ( m1_subset_1(esk3_3(X23,X24,X25),u1_struct_0(X24))
        | ~ r2_hidden(X23,a_2_5_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24) )
      & ( X23 = esk3_3(X23,X24,X25)
        | ~ r2_hidden(X23,a_2_5_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24) )
      & ( m1_subset_1(esk4_3(X23,X24,X25),u1_struct_0(X24))
        | ~ r2_hidden(X23,a_2_5_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24) )
      & ( r3_lattices(X24,esk3_3(X23,X24,X25),esk4_3(X23,X24,X25))
        | ~ r2_hidden(X23,a_2_5_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24) )
      & ( r2_hidden(esk4_3(X23,X24,X25),X25)
        | ~ r2_hidden(X23,a_2_5_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24) )
      & ( ~ m1_subset_1(X29,u1_struct_0(X24))
        | X23 != X29
        | ~ m1_subset_1(X30,u1_struct_0(X24))
        | ~ r3_lattices(X24,X29,X30)
        | ~ r2_hidden(X30,X28)
        | r2_hidden(X23,a_2_5_lattice3(X24,X28))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( r3_lattices(esk5_0,X1,esk8_1(X1))
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)
    | r3_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk8_1(X1),u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( r2_hidden(X3,a_2_5_lattice3(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_lattices(X2,X1,X4)
    | ~ r2_hidden(X4,X5)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)))
    | ~ r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),u1_struct_0(esk5_0))
    | ~ r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_56,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_20])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X4,X3)
    | ~ r3_lattices(X2,X1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_54])])).

cnf(c_0_61,plain,
    ( r1_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),a_2_5_lattice3(esk5_0,X1))
    | ~ r2_hidden(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_14]),c_0_48]),c_0_15]),c_0_16])]),c_0_17]),c_0_60])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk8_1(X1),esk7_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_64,negated_conjecture,
    ( r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,X1))
    | ~ r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_48]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),a_2_5_lattice3(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_54]),c_0_48])])).

cnf(c_0_66,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk1_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( r4_lattice3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_24]),c_0_16])]),c_0_17])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_68]),c_0_14]),c_0_24]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_70,negated_conjecture,
    ( ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_69]),c_0_24]),c_0_24]),c_0_16])]),c_0_42]),c_0_17])).

cnf(c_0_71,negated_conjecture,
    ( ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_34]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_72,negated_conjecture,
    ( ~ v9_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_37]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_40]),c_0_15]),c_0_16])]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:43:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.12/0.39  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.029 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t48_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_lattice3)).
% 0.12/0.39  fof(t47_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))&k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_lattice3)).
% 0.12/0.39  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 0.12/0.39  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.12/0.39  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 0.12/0.39  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.12/0.39  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.12/0.39  fof(fraenkel_a_2_5_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_5_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r3_lattices(X2,X4,X5))&r2_hidden(X5,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 0.12/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))))), inference(assume_negation,[status(cth)],[t48_lattice3])).
% 0.12/0.39  fof(c_0_9, plain, ![X31, X32]:((k15_lattice3(X31,X32)=k15_lattice3(X31,a_2_5_lattice3(X31,X32))|(v2_struct_0(X31)|~v10_lattices(X31)|~v4_lattice3(X31)|~l3_lattices(X31)))&(k16_lattice3(X31,X32)=k16_lattice3(X31,a_2_6_lattice3(X31,X32))|(v2_struct_0(X31)|~v10_lattices(X31)|~v4_lattice3(X31)|~l3_lattices(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).
% 0.12/0.39  fof(c_0_10, negated_conjecture, ![X36]:((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v4_lattice3(esk5_0))&l3_lattices(esk5_0))&(((m1_subset_1(esk8_1(X36),u1_struct_0(esk5_0))|~r2_hidden(X36,esk6_0)|~m1_subset_1(X36,u1_struct_0(esk5_0)))&((r3_lattices(esk5_0,X36,esk8_1(X36))|~r2_hidden(X36,esk6_0)|~m1_subset_1(X36,u1_struct_0(esk5_0)))&(r2_hidden(esk8_1(X36),esk7_0)|~r2_hidden(X36,esk6_0)|~m1_subset_1(X36,u1_struct_0(esk5_0)))))&~r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).
% 0.12/0.39  fof(c_0_11, plain, ![X16, X17, X18, X19]:(((r4_lattice3(X16,X18,X17)|X18!=k15_lattice3(X16,X17)|~m1_subset_1(X18,u1_struct_0(X16))|(v2_struct_0(X16)|~v10_lattices(X16)|~v4_lattice3(X16)|~l3_lattices(X16))|(v2_struct_0(X16)|~l3_lattices(X16)))&(~m1_subset_1(X19,u1_struct_0(X16))|(~r4_lattice3(X16,X19,X17)|r1_lattices(X16,X18,X19))|X18!=k15_lattice3(X16,X17)|~m1_subset_1(X18,u1_struct_0(X16))|(v2_struct_0(X16)|~v10_lattices(X16)|~v4_lattice3(X16)|~l3_lattices(X16))|(v2_struct_0(X16)|~l3_lattices(X16))))&((m1_subset_1(esk2_3(X16,X17,X18),u1_struct_0(X16))|~r4_lattice3(X16,X18,X17)|X18=k15_lattice3(X16,X17)|~m1_subset_1(X18,u1_struct_0(X16))|(v2_struct_0(X16)|~v10_lattices(X16)|~v4_lattice3(X16)|~l3_lattices(X16))|(v2_struct_0(X16)|~l3_lattices(X16)))&((r4_lattice3(X16,esk2_3(X16,X17,X18),X17)|~r4_lattice3(X16,X18,X17)|X18=k15_lattice3(X16,X17)|~m1_subset_1(X18,u1_struct_0(X16))|(v2_struct_0(X16)|~v10_lattices(X16)|~v4_lattice3(X16)|~l3_lattices(X16))|(v2_struct_0(X16)|~l3_lattices(X16)))&(~r1_lattices(X16,X18,esk2_3(X16,X17,X18))|~r4_lattice3(X16,X18,X17)|X18=k15_lattice3(X16,X17)|~m1_subset_1(X18,u1_struct_0(X16))|(v2_struct_0(X16)|~v10_lattices(X16)|~v4_lattice3(X16)|~l3_lattices(X16))|(v2_struct_0(X16)|~l3_lattices(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.12/0.39  fof(c_0_12, plain, ![X21, X22]:(v2_struct_0(X21)|~l3_lattices(X21)|m1_subset_1(k15_lattice3(X21,X22),u1_struct_0(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.12/0.39  cnf(c_0_13, plain, (k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_14, negated_conjecture, (v4_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_15, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_16, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_18, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  fof(c_0_19, plain, ![X10, X11, X12, X13, X14]:((~r4_lattice3(X10,X11,X12)|(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_hidden(X13,X12)|r1_lattices(X10,X13,X11)))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))&((m1_subset_1(esk1_3(X10,X11,X14),u1_struct_0(X10))|r4_lattice3(X10,X11,X14)|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))&((r2_hidden(esk1_3(X10,X11,X14),X14)|r4_lattice3(X10,X11,X14)|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))&(~r1_lattices(X10,esk1_3(X10,X11,X14),X11)|r4_lattice3(X10,X11,X14)|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.12/0.39  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_21, negated_conjecture, (k15_lattice3(esk5_0,a_2_5_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_22, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_23, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(k15_lattice3(esk5_0,X1),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_16])]), c_0_17])).
% 0.12/0.39  fof(c_0_25, plain, ![X7, X8, X9]:((~r3_lattices(X7,X8,X9)|r1_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))&(~r1_lattices(X7,X8,X9)|r3_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.12/0.39  cnf(c_0_26, plain, (r1_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_20])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (r4_lattice3(esk5_0,k15_lattice3(esk5_0,X1),X2)|m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_28, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_29, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.39  cnf(c_0_30, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))|m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_14]), c_0_24]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  fof(c_0_31, plain, ![X6]:(((((((~v2_struct_0(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))&(v4_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v5_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v6_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v7_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v8_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v9_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.12/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)|r4_lattice3(esk5_0,k15_lattice3(esk5_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (r3_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))|m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_24]), c_0_24]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_34, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)|r1_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_32]), c_0_14]), c_0_24]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, (r3_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))|m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_37, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)|r3_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_35]), c_0_24]), c_0_24]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (r3_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))|m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0))|~v9_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_40, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)|r3_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (~r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_43, negated_conjecture, (r3_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))|m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),X1),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)|r3_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))|~v9_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_37]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_45, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  fof(c_0_46, plain, ![X23, X24, X25, X28, X29, X30]:((((m1_subset_1(esk3_3(X23,X24,X25),u1_struct_0(X24))|~r2_hidden(X23,a_2_5_lattice3(X24,X25))|(v2_struct_0(X24)|~v10_lattices(X24)|~v4_lattice3(X24)|~l3_lattices(X24)))&(X23=esk3_3(X23,X24,X25)|~r2_hidden(X23,a_2_5_lattice3(X24,X25))|(v2_struct_0(X24)|~v10_lattices(X24)|~v4_lattice3(X24)|~l3_lattices(X24))))&(((m1_subset_1(esk4_3(X23,X24,X25),u1_struct_0(X24))|~r2_hidden(X23,a_2_5_lattice3(X24,X25))|(v2_struct_0(X24)|~v10_lattices(X24)|~v4_lattice3(X24)|~l3_lattices(X24)))&(r3_lattices(X24,esk3_3(X23,X24,X25),esk4_3(X23,X24,X25))|~r2_hidden(X23,a_2_5_lattice3(X24,X25))|(v2_struct_0(X24)|~v10_lattices(X24)|~v4_lattice3(X24)|~l3_lattices(X24))))&(r2_hidden(esk4_3(X23,X24,X25),X25)|~r2_hidden(X23,a_2_5_lattice3(X24,X25))|(v2_struct_0(X24)|~v10_lattices(X24)|~v4_lattice3(X24)|~l3_lattices(X24)))))&(~m1_subset_1(X29,u1_struct_0(X24))|X23!=X29|(~m1_subset_1(X30,u1_struct_0(X24))|~r3_lattices(X24,X29,X30)|~r2_hidden(X30,X28))|r2_hidden(X23,a_2_5_lattice3(X24,X28))|(v2_struct_0(X24)|~v10_lattices(X24)|~v4_lattice3(X24)|~l3_lattices(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (r3_lattices(esk5_0,X1,esk8_1(X1))|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.39  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)|r3_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk8_1(X1),u1_struct_0(esk5_0))|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_51, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_45])).
% 0.12/0.39  cnf(c_0_52, plain, (r2_hidden(X3,a_2_5_lattice3(X2,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~m1_subset_1(X4,u1_struct_0(X2))|~r3_lattices(X2,X1,X4)|~r2_hidden(X4,X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.39  cnf(c_0_53, negated_conjecture, (r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)))|~r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.39  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.12/0.39  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),u1_struct_0(esk5_0))|~r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 0.12/0.39  cnf(c_0_56, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_57, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]), c_0_20])).
% 0.12/0.39  cnf(c_0_58, plain, (r2_hidden(X1,a_2_5_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X4,X3)|~r3_lattices(X2,X1,X4)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_52])).
% 0.12/0.39  cnf(c_0_59, negated_conjecture, (r3_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 0.12/0.39  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_54])])).
% 0.12/0.39  cnf(c_0_61, plain, (r1_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_20])).
% 0.12/0.39  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),a_2_5_lattice3(esk5_0,X1))|~r2_hidden(esk8_1(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_14]), c_0_48]), c_0_15]), c_0_16])]), c_0_17]), c_0_60])])).
% 0.12/0.39  cnf(c_0_63, negated_conjecture, (r2_hidden(esk8_1(X1),esk7_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_64, negated_conjecture, (r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,X1))|~r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_48]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),a_2_5_lattice3(esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_54]), c_0_48])])).
% 0.12/0.39  cnf(c_0_66, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk1_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_67, negated_conjecture, (r1_lattices(esk5_0,esk1_3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0),k15_lattice3(esk5_0,esk7_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_21])).
% 0.12/0.39  cnf(c_0_68, negated_conjecture, (r4_lattice3(esk5_0,k15_lattice3(esk5_0,esk7_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_24]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_69, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_68]), c_0_14]), c_0_24]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_70, negated_conjecture, (~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_69]), c_0_24]), c_0_24]), c_0_16])]), c_0_42]), c_0_17])).
% 0.12/0.39  cnf(c_0_71, negated_conjecture, (~v9_lattices(esk5_0)|~v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_34]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_72, negated_conjecture, (~v9_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_37]), c_0_15]), c_0_16])]), c_0_17])).
% 0.12/0.39  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_40]), c_0_15]), c_0_16])]), c_0_17]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 74
% 0.12/0.39  # Proof object clause steps            : 57
% 0.12/0.39  # Proof object formula steps           : 17
% 0.12/0.39  # Proof object conjectures             : 41
% 0.12/0.39  # Proof object clause conjectures      : 38
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 21
% 0.12/0.39  # Proof object initial formulas used   : 8
% 0.12/0.39  # Proof object generating inferences   : 29
% 0.12/0.39  # Proof object simplifying inferences  : 116
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 8
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 35
% 0.12/0.39  # Removed in clause preprocessing      : 1
% 0.12/0.39  # Initial clauses in saturation        : 34
% 0.12/0.39  # Processed clauses                    : 246
% 0.12/0.39  # ...of these trivial                  : 4
% 0.12/0.39  # ...subsumed                          : 53
% 0.12/0.39  # ...remaining for further processing  : 189
% 0.12/0.39  # Other redundant clauses eliminated   : 3
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 13
% 0.12/0.39  # Backward-rewritten                   : 5
% 0.12/0.39  # Generated clauses                    : 305
% 0.12/0.39  # ...of the previous two non-trivial   : 290
% 0.12/0.39  # Contextual simplify-reflections      : 3
% 0.12/0.39  # Paramodulations                      : 302
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 3
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 134
% 0.12/0.39  #    Positive orientable unit clauses  : 26
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 3
% 0.12/0.39  #    Non-unit-clauses                  : 105
% 0.12/0.39  # Current number of unprocessed clauses: 112
% 0.12/0.39  # ...number of literals in the above   : 486
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 52
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 2314
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 867
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 69
% 0.12/0.39  # Unit Clause-clause subsumption calls : 176
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 41
% 0.12/0.39  # BW rewrite match successes           : 4
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 13519
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.045 s
% 0.12/0.39  # System time              : 0.005 s
% 0.12/0.39  # Total time               : 0.050 s
% 0.12/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
