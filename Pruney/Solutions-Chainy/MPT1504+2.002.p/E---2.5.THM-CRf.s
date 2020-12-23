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
% Statistics : Number of formulae       :   78 (3917 expanded)
%              Number of clauses        :   61 (1520 expanded)
%              Number of leaves         :    8 ( 956 expanded)
%              Depth                    :   28
%              Number of atoms          :  551 (27270 expanded)
%              Number of equality atoms :   65 (3042 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(fraenkel_a_2_2_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r4_lattice3(X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(t37_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

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

fof(c_0_8,plain,(
    ! [X15,X16,X17,X18] :
      ( ( r4_lattice3(X15,X17,X16)
        | X17 != k15_lattice3(X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v4_lattice3(X15)
        | ~ l3_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r4_lattice3(X15,X18,X16)
        | r1_lattices(X15,X17,X18)
        | X17 != k15_lattice3(X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v4_lattice3(X15)
        | ~ l3_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))
        | ~ r4_lattice3(X15,X17,X16)
        | X17 = k15_lattice3(X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v4_lattice3(X15)
        | ~ l3_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( r4_lattice3(X15,esk2_3(X15,X16,X17),X16)
        | ~ r4_lattice3(X15,X17,X16)
        | X17 = k15_lattice3(X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v4_lattice3(X15)
        | ~ l3_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( ~ r1_lattices(X15,X17,esk2_3(X15,X16,X17))
        | ~ r4_lattice3(X15,X17,X16)
        | X17 = k15_lattice3(X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ v4_lattice3(X15)
        | ~ l3_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_9,plain,(
    ! [X22,X23,X24,X26,X27] :
      ( ( m1_subset_1(esk3_3(X22,X23,X24),u1_struct_0(X23))
        | ~ r2_hidden(X22,a_2_2_lattice3(X23,X24))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) )
      & ( X22 = esk3_3(X22,X23,X24)
        | ~ r2_hidden(X22,a_2_2_lattice3(X23,X24))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) )
      & ( r4_lattice3(X23,esk3_3(X22,X23,X24),X24)
        | ~ r2_hidden(X22,a_2_2_lattice3(X23,X24))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X23))
        | X22 != X27
        | ~ r4_lattice3(X23,X27,X26)
        | r2_hidden(X22,a_2_2_lattice3(X23,X26))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

cnf(c_0_10,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ l3_lattices(X20)
      | m1_subset_1(k15_lattice3(X20,X21),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t37_lattice3])).

cnf(c_0_18,plain,
    ( X1 = esk3_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(k15_lattice3(X1,X2),a_2_2_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_14])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v4_lattice3(esk5_0)
    & l3_lattices(esk5_0)
    & k15_lattice3(esk5_0,esk6_0) != k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( esk3_3(k15_lattice3(X1,X2),X1,X2) = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( m1_subset_1(esk3_3(k15_lattice3(X1,X2),X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( esk3_3(k15_lattice3(esk5_0,X1),esk5_0,X1) = k15_lattice3(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_30,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( ( r3_lattice3(X28,X29,X30)
        | X29 != k16_lattice3(X28,X30)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X28))
        | ~ r3_lattice3(X28,X31,X30)
        | r3_lattices(X28,X31,X29)
        | X29 != k16_lattice3(X28,X30)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) )
      & ( m1_subset_1(esk4_3(X28,X29,X32),u1_struct_0(X28))
        | ~ r3_lattice3(X28,X29,X32)
        | X29 = k16_lattice3(X28,X32)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) )
      & ( r3_lattice3(X28,esk4_3(X28,X29,X32),X32)
        | ~ r3_lattice3(X28,X29,X32)
        | X29 = k16_lattice3(X28,X32)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) )
      & ( ~ r3_lattices(X28,esk4_3(X28,X29,X32),X29)
        | ~ r3_lattice3(X28,X29,X32)
        | X29 = k16_lattice3(X28,X32)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk5_0,X1),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_29]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_33,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r3_lattice3(X1,esk4_3(X1,X2,X3),X3)
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)
    | r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25])]),c_0_26])).

cnf(c_0_37,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r1_lattices(X2,esk4_3(X2,X1,X3),X4)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X4,X3)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))
    | r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))
    | k15_lattice3(esk5_0,X1) = k16_lattice3(esk5_0,a_2_2_lattice3(X2,X3))
    | r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X4)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X4,a_2_2_lattice3(X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(esk5_0))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_23]),c_0_32]),c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_40,plain,(
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

cnf(c_0_41,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))
    | k15_lattice3(esk5_0,X1) = k16_lattice3(esk5_0,a_2_2_lattice3(X2,X3))
    | r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),k15_lattice3(esk5_0,X4))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(k15_lattice3(esk5_0,X4),a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))
    | k15_lattice3(esk5_0,X1) = k16_lattice3(esk5_0,a_2_2_lattice3(X2,X3))
    | m1_subset_1(esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),u1_struct_0(esk5_0))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_38]),c_0_23]),c_0_32]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_43,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))
    | k15_lattice3(esk5_0,X1) = k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))
    | r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_19]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))
    | k15_lattice3(esk5_0,X1) = k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))
    | m1_subset_1(esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_46,plain,(
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

cnf(c_0_47,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))
    | k15_lattice3(esk5_0,X1) = k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))
    | r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X2))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_32]),c_0_25])]),c_0_26]),c_0_45])).

cnf(c_0_48,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_49,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_50,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))
    | k15_lattice3(esk5_0,X1) = k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))
    | r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X2))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_51,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_49])).

cnf(c_0_53,plain,
    ( r4_lattice3(X1,esk3_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_54,plain,
    ( X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk4_3(X1,X2,X3),X2)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))
    | k15_lattice3(esk5_0,X1) = k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))
    | r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X2))
    | ~ v9_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_56,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( r4_lattice3(X1,esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),a_2_2_lattice3(X1,X3)),X1,X3),X3)
    | r3_lattice3(esk5_0,k15_lattice3(esk5_0,X2),a_2_2_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))
    | m1_subset_1(esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))
    | k15_lattice3(esk5_0,X1) = k16_lattice3(esk5_0,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),k15_lattice3(esk5_0,X1))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_38]),c_0_23]),c_0_32]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))
    | k15_lattice3(esk5_0,X1) = k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))
    | r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_62,negated_conjecture,
    ( r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))
    | r1_lattices(X2,k15_lattice3(X2,X3),esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),esk5_0,X1) = esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1))
    | k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_64,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1)
    | r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1))
    | r1_lattices(esk5_0,k15_lattice3(esk5_0,X1),esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_66,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1)
    | r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_32]),c_0_25])]),c_0_26])).

cnf(c_0_67,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1)
    | r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),X2)
    | ~ r2_hidden(X2,a_2_2_lattice3(esk5_0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_66]),c_0_23]),c_0_32]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_68,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1)
    | r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),k15_lattice3(esk5_0,X2))
    | ~ r2_hidden(k15_lattice3(esk5_0,X2),a_2_2_lattice3(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_32])).

cnf(c_0_69,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1)
    | r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),k15_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_19]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1)
    | m1_subset_1(esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_66]),c_0_23]),c_0_32]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_71,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1)
    | ~ r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),k15_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_66]),c_0_23]),c_0_32]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1)
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_69]),c_0_32]),c_0_25])]),c_0_26]),c_0_70]),c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1)
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_48]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_74,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1)
    | ~ v9_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_51]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_75,negated_conjecture,
    ( k15_lattice3(esk5_0,esk6_0) != k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_76,negated_conjecture,
    ( k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:07:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.44  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.030 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.20/0.44  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.20/0.44  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.20/0.44  fof(t37_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 0.20/0.44  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.20/0.44  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.20/0.44  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.20/0.44  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.44  fof(c_0_8, plain, ![X15, X16, X17, X18]:(((r4_lattice3(X15,X17,X16)|X17!=k15_lattice3(X15,X16)|~m1_subset_1(X17,u1_struct_0(X15))|(v2_struct_0(X15)|~v10_lattices(X15)|~v4_lattice3(X15)|~l3_lattices(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&(~m1_subset_1(X18,u1_struct_0(X15))|(~r4_lattice3(X15,X18,X16)|r1_lattices(X15,X17,X18))|X17!=k15_lattice3(X15,X16)|~m1_subset_1(X17,u1_struct_0(X15))|(v2_struct_0(X15)|~v10_lattices(X15)|~v4_lattice3(X15)|~l3_lattices(X15))|(v2_struct_0(X15)|~l3_lattices(X15))))&((m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))|~r4_lattice3(X15,X17,X16)|X17=k15_lattice3(X15,X16)|~m1_subset_1(X17,u1_struct_0(X15))|(v2_struct_0(X15)|~v10_lattices(X15)|~v4_lattice3(X15)|~l3_lattices(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((r4_lattice3(X15,esk2_3(X15,X16,X17),X16)|~r4_lattice3(X15,X17,X16)|X17=k15_lattice3(X15,X16)|~m1_subset_1(X17,u1_struct_0(X15))|(v2_struct_0(X15)|~v10_lattices(X15)|~v4_lattice3(X15)|~l3_lattices(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&(~r1_lattices(X15,X17,esk2_3(X15,X16,X17))|~r4_lattice3(X15,X17,X16)|X17=k15_lattice3(X15,X16)|~m1_subset_1(X17,u1_struct_0(X15))|(v2_struct_0(X15)|~v10_lattices(X15)|~v4_lattice3(X15)|~l3_lattices(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.20/0.44  fof(c_0_9, plain, ![X22, X23, X24, X26, X27]:((((m1_subset_1(esk3_3(X22,X23,X24),u1_struct_0(X23))|~r2_hidden(X22,a_2_2_lattice3(X23,X24))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23)))&(X22=esk3_3(X22,X23,X24)|~r2_hidden(X22,a_2_2_lattice3(X23,X24))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23))))&(r4_lattice3(X23,esk3_3(X22,X23,X24),X24)|~r2_hidden(X22,a_2_2_lattice3(X23,X24))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23))))&(~m1_subset_1(X27,u1_struct_0(X23))|X22!=X27|~r4_lattice3(X23,X27,X26)|r2_hidden(X22,a_2_2_lattice3(X23,X26))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.20/0.44  cnf(c_0_10, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  fof(c_0_11, plain, ![X20, X21]:(v2_struct_0(X20)|~l3_lattices(X20)|m1_subset_1(k15_lattice3(X20,X21),u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.20/0.44  cnf(c_0_12, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.44  cnf(c_0_13, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_10])).
% 0.20/0.44  cnf(c_0_14, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.44  cnf(c_0_15, plain, (r2_hidden(X1,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~r4_lattice3(X2,X1,X3)|~v4_lattice3(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.44  cnf(c_0_16, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_14])).
% 0.20/0.44  fof(c_0_17, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2)))), inference(assume_negation,[status(cth)],[t37_lattice3])).
% 0.20/0.44  cnf(c_0_18, plain, (X1=esk3_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.44  cnf(c_0_19, plain, (r2_hidden(k15_lattice3(X1,X2),a_2_2_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_14])).
% 0.20/0.44  fof(c_0_20, negated_conjecture, ((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v4_lattice3(esk5_0))&l3_lattices(esk5_0))&k15_lattice3(esk5_0,esk6_0)!=k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.20/0.44  cnf(c_0_21, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.44  cnf(c_0_22, plain, (esk3_3(k15_lattice3(X1,X2),X1,X2)=k15_lattice3(X1,X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.44  cnf(c_0_23, negated_conjecture, (v4_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.44  cnf(c_0_24, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.44  cnf(c_0_25, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.44  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.44  fof(c_0_27, plain, ![X9, X10, X11, X12, X13]:((~r3_lattice3(X9,X10,X11)|(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X11)|r1_lattices(X9,X10,X12)))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk1_3(X9,X10,X13),u1_struct_0(X9))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((r2_hidden(esk1_3(X9,X10,X13),X13)|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&(~r1_lattices(X9,X10,esk1_3(X9,X10,X13))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.20/0.44  cnf(c_0_28, plain, (m1_subset_1(esk3_3(k15_lattice3(X1,X2),X1,X2),u1_struct_0(X1))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.20/0.44  cnf(c_0_29, negated_conjecture, (esk3_3(k15_lattice3(esk5_0,X1),esk5_0,X1)=k15_lattice3(esk5_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  fof(c_0_30, plain, ![X28, X29, X30, X31, X32]:(((r3_lattice3(X28,X29,X30)|X29!=k16_lattice3(X28,X30)|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28)))&(~m1_subset_1(X31,u1_struct_0(X28))|(~r3_lattice3(X28,X31,X30)|r3_lattices(X28,X31,X29))|X29!=k16_lattice3(X28,X30)|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))))&((m1_subset_1(esk4_3(X28,X29,X32),u1_struct_0(X28))|~r3_lattice3(X28,X29,X32)|X29=k16_lattice3(X28,X32)|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28)))&((r3_lattice3(X28,esk4_3(X28,X29,X32),X32)|~r3_lattice3(X28,X29,X32)|X29=k16_lattice3(X28,X32)|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28)))&(~r3_lattices(X28,esk4_3(X28,X29,X32),X29)|~r3_lattice3(X28,X29,X32)|X29=k16_lattice3(X28,X32)|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.20/0.44  cnf(c_0_31, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.44  cnf(c_0_32, negated_conjecture, (m1_subset_1(k15_lattice3(esk5_0,X1),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_29]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_33, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.44  cnf(c_0_34, plain, (r3_lattice3(X1,esk4_3(X1,X2,X3),X3)|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.44  cnf(c_0_35, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.44  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),X2),X2)|r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_37, plain, (X1=k16_lattice3(X2,X3)|r1_lattices(X2,esk4_3(X2,X1,X3),X4)|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X4,X3)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.20/0.44  cnf(c_0_38, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))|r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_18, c_0_36])).
% 0.20/0.44  cnf(c_0_39, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))|k15_lattice3(esk5_0,X1)=k16_lattice3(esk5_0,a_2_2_lattice3(X2,X3))|r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X4)|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X4,a_2_2_lattice3(X2,X3))|~m1_subset_1(X4,u1_struct_0(esk5_0))|~v10_lattices(X2)|~l3_lattices(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_23]), c_0_32]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  fof(c_0_40, plain, ![X6, X7, X8]:((~r3_lattices(X6,X7,X8)|r1_lattices(X6,X7,X8)|(v2_struct_0(X6)|~v6_lattices(X6)|~v8_lattices(X6)|~v9_lattices(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))&(~r1_lattices(X6,X7,X8)|r3_lattices(X6,X7,X8)|(v2_struct_0(X6)|~v6_lattices(X6)|~v8_lattices(X6)|~v9_lattices(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.20/0.44  cnf(c_0_41, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))|k15_lattice3(esk5_0,X1)=k16_lattice3(esk5_0,a_2_2_lattice3(X2,X3))|r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),k15_lattice3(esk5_0,X4))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(k15_lattice3(esk5_0,X4),a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_39, c_0_32])).
% 0.20/0.44  cnf(c_0_42, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))|k15_lattice3(esk5_0,X1)=k16_lattice3(esk5_0,a_2_2_lattice3(X2,X3))|m1_subset_1(esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),u1_struct_0(esk5_0))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_38]), c_0_23]), c_0_32]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_43, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.44  cnf(c_0_44, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))|k15_lattice3(esk5_0,X1)=k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))|r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_19]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_45, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))|k15_lattice3(esk5_0,X1)=k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))|m1_subset_1(esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  fof(c_0_46, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.44  cnf(c_0_47, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))|k15_lattice3(esk5_0,X1)=k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))|r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X2))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_32]), c_0_25])]), c_0_26]), c_0_45])).
% 0.20/0.44  cnf(c_0_48, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.44  cnf(c_0_49, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_50, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))|k15_lattice3(esk5_0,X1)=k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))|r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X2))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_51, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.44  cnf(c_0_52, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_49])).
% 0.20/0.44  cnf(c_0_53, plain, (r4_lattice3(X1,esk3_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,X3))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.44  cnf(c_0_54, plain, (X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattices(X1,esk4_3(X1,X2,X3),X2)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.44  cnf(c_0_55, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))|k15_lattice3(esk5_0,X1)=k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))|r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X2))|~v9_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_56, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.44  cnf(c_0_57, plain, (r1_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~v4_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_14])).
% 0.20/0.44  cnf(c_0_58, negated_conjecture, (r4_lattice3(X1,esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X2),a_2_2_lattice3(X1,X3)),X1,X3),X3)|r3_lattice3(esk5_0,k15_lattice3(esk5_0,X2),a_2_2_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_53, c_0_36])).
% 0.20/0.44  cnf(c_0_59, negated_conjecture, (r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))|m1_subset_1(esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_21, c_0_36])).
% 0.20/0.44  cnf(c_0_60, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))|k15_lattice3(esk5_0,X1)=k16_lattice3(esk5_0,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),k15_lattice3(esk5_0,X1))|~v10_lattices(X2)|~l3_lattices(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_38]), c_0_23]), c_0_32]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_61, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),esk5_0,X2)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2))|k15_lattice3(esk5_0,X1)=k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X2))|r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_62, negated_conjecture, (r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3))|r1_lattices(X2,k15_lattice3(X2,X3),esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(X2,X3)),X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.20/0.44  cnf(c_0_63, negated_conjecture, (esk3_3(esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),esk5_0,X1)=esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1))|k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_64, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.44  cnf(c_0_65, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)|r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1))|r1_lattices(esk5_0,k15_lattice3(esk5_0,X1),esk1_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_66, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)|r3_lattice3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_32]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_67, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)|r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),X2)|~r2_hidden(X2,a_2_2_lattice3(esk5_0,X1))|~m1_subset_1(X2,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_66]), c_0_23]), c_0_32]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_68, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)|r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),k15_lattice3(esk5_0,X2))|~r2_hidden(k15_lattice3(esk5_0,X2),a_2_2_lattice3(esk5_0,X1))), inference(spm,[status(thm)],[c_0_67, c_0_32])).
% 0.20/0.44  cnf(c_0_69, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)|r1_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),k15_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_19]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_70, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)|m1_subset_1(esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_66]), c_0_23]), c_0_32]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_71, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)|~r3_lattices(esk5_0,esk4_3(esk5_0,k15_lattice3(esk5_0,X1),a_2_2_lattice3(esk5_0,X1)),k15_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_66]), c_0_23]), c_0_32]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_72, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_69]), c_0_32]), c_0_25])]), c_0_26]), c_0_70]), c_0_71])).
% 0.20/0.44  cnf(c_0_73, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_48]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_74, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)|~v9_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_51]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_75, negated_conjecture, (k15_lattice3(esk5_0,esk6_0)!=k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.44  cnf(c_0_76, negated_conjecture, (k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.44  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 78
% 0.20/0.44  # Proof object clause steps            : 61
% 0.20/0.44  # Proof object formula steps           : 17
% 0.20/0.44  # Proof object conjectures             : 38
% 0.20/0.44  # Proof object clause conjectures      : 35
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 22
% 0.20/0.44  # Proof object initial formulas used   : 8
% 0.20/0.44  # Proof object generating inferences   : 33
% 0.20/0.44  # Proof object simplifying inferences  : 123
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 8
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 33
% 0.20/0.44  # Removed in clause preprocessing      : 1
% 0.20/0.44  # Initial clauses in saturation        : 32
% 0.20/0.44  # Processed clauses                    : 386
% 0.20/0.44  # ...of these trivial                  : 0
% 0.20/0.44  # ...subsumed                          : 78
% 0.20/0.44  # ...remaining for further processing  : 308
% 0.20/0.44  # Other redundant clauses eliminated   : 5
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 52
% 0.20/0.44  # Backward-rewritten                   : 43
% 0.20/0.44  # Generated clauses                    : 763
% 0.20/0.44  # ...of the previous two non-trivial   : 748
% 0.20/0.44  # Contextual simplify-reflections      : 59
% 0.20/0.44  # Paramodulations                      : 758
% 0.20/0.44  # Factorizations                       : 0
% 0.20/0.44  # Equation resolutions                 : 5
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 176
% 0.20/0.44  #    Positive orientable unit clauses  : 10
% 0.20/0.44  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 1
% 0.20/0.44  #    Non-unit-clauses                  : 165
% 0.20/0.44  # Current number of unprocessed clauses: 412
% 0.20/0.44  # ...number of literals in the above   : 3155
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 127
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 27476
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 1429
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 189
% 0.20/0.44  # Unit Clause-clause subsumption calls : 209
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 8
% 0.20/0.44  # BW rewrite match successes           : 4
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 45757
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.085 s
% 0.20/0.44  # System time              : 0.005 s
% 0.20/0.44  # Total time               : 0.090 s
% 0.20/0.44  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
