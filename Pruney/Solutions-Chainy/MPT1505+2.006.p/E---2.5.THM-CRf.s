%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:00 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 161 expanded)
%              Number of clauses        :   37 (  56 expanded)
%              Number of leaves         :    9 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  422 (1245 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

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

fof(t37_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

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

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X23,X24,X25,X27,X28] :
      ( ( m1_subset_1(esk3_3(X23,X24,X25),u1_struct_0(X24))
        | ~ r2_hidden(X23,a_2_2_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24) )
      & ( X23 = esk3_3(X23,X24,X25)
        | ~ r2_hidden(X23,a_2_2_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24) )
      & ( r4_lattice3(X24,esk3_3(X23,X24,X25),X25)
        | ~ r2_hidden(X23,a_2_2_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X24))
        | X23 != X28
        | ~ r4_lattice3(X24,X28,X27)
        | r2_hidden(X23,a_2_2_lattice3(X24,X27))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

cnf(c_0_11,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r4_lattice3(X1,esk3_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_lattices(X1,X2,esk3_3(X3,X1,X4))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X3,a_2_2_lattice3(X1,X4))
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_15,plain,
    ( X1 = esk3_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
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

cnf(c_0_17,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X3,a_2_2_lattice3(X1,X4))
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,negated_conjecture,(
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

cnf(c_0_20,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r3_lattice3(X1,X2,a_2_2_lattice3(X3,X4))
    | r1_lattices(X3,X5,esk1_3(X1,X2,a_2_2_lattice3(X3,X4)))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v4_lattice3(X3)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v4_lattice3(esk5_0)
    & l3_lattices(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & r2_hidden(esk6_0,esk7_0)
    & ( ~ r3_lattices(esk5_0,esk6_0,k15_lattice3(esk5_0,esk7_0))
      | ~ r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_23,plain,(
    ! [X29,X30,X31,X32,X33] :
      ( ( r3_lattice3(X29,X30,X31)
        | X30 != k16_lattice3(X29,X31)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ r3_lattice3(X29,X32,X31)
        | r3_lattices(X29,X32,X30)
        | X30 != k16_lattice3(X29,X31)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( m1_subset_1(esk4_3(X29,X30,X33),u1_struct_0(X29))
        | ~ r3_lattice3(X29,X30,X33)
        | X30 = k16_lattice3(X29,X33)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( r3_lattice3(X29,esk4_3(X29,X30,X33),X33)
        | ~ r3_lattice3(X29,X30,X33)
        | X30 = k16_lattice3(X29,X33)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( ~ r3_lattices(X29,esk4_3(X29,X30,X33),X30)
        | ~ r3_lattice3(X29,X30,X33)
        | X30 = k16_lattice3(X29,X33)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_24,plain,
    ( r3_lattice3(X1,X2,a_2_2_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v10_lattices(X35)
      | ~ v4_lattice3(X35)
      | ~ l3_lattices(X35)
      | k15_lattice3(X35,X36) = k16_lattice3(X35,a_2_2_lattice3(X35,X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_27,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r3_lattice3(X1,esk6_0,a_2_2_lattice3(X1,esk7_0))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ l3_lattices(X21)
      | m1_subset_1(k16_lattice3(X21,X22),u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

cnf(c_0_30,negated_conjecture,
    ( ~ r3_lattices(esk5_0,esk6_0,k15_lattice3(esk5_0,esk7_0))
    | ~ r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( r3_lattices(X1,esk6_0,X2)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,a_2_2_lattice3(X1,esk7_0))
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
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

fof(c_0_39,plain,(
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

cnf(c_0_40,negated_conjecture,
    ( ~ r3_lattices(esk5_0,esk6_0,k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,esk7_0)))
    | ~ r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r3_lattices(X1,esk6_0,k16_lattice3(X1,a_2_2_lattice3(X1,esk7_0)))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

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
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( ~ r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32]),c_0_42]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_49,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_50,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),esk6_0)
    | ~ m1_subset_1(k16_lattice3(esk5_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_42]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_53,plain,
    ( r1_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_subset_1(k16_lattice3(esk5_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_32]),c_0_25]),c_0_42]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_37]),c_0_34])]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:29:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.12/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.030 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 0.12/0.38  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.12/0.38  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 0.12/0.38  fof(t38_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 0.12/0.38  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.12/0.38  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_lattice3)).
% 0.12/0.38  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.12/0.38  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.12/0.38  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.12/0.38  fof(c_0_9, plain, ![X15, X16, X17, X18, X19]:((~r4_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X17)|r1_lattices(X15,X18,X16)))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))|r4_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((r2_hidden(esk2_3(X15,X16,X19),X19)|r4_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&(~r1_lattices(X15,esk2_3(X15,X16,X19),X16)|r4_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.12/0.38  fof(c_0_10, plain, ![X23, X24, X25, X27, X28]:((((m1_subset_1(esk3_3(X23,X24,X25),u1_struct_0(X24))|~r2_hidden(X23,a_2_2_lattice3(X24,X25))|(v2_struct_0(X24)|~v10_lattices(X24)|~v4_lattice3(X24)|~l3_lattices(X24)))&(X23=esk3_3(X23,X24,X25)|~r2_hidden(X23,a_2_2_lattice3(X24,X25))|(v2_struct_0(X24)|~v10_lattices(X24)|~v4_lattice3(X24)|~l3_lattices(X24))))&(r4_lattice3(X24,esk3_3(X23,X24,X25),X25)|~r2_hidden(X23,a_2_2_lattice3(X24,X25))|(v2_struct_0(X24)|~v10_lattices(X24)|~v4_lattice3(X24)|~l3_lattices(X24))))&(~m1_subset_1(X28,u1_struct_0(X24))|X23!=X28|~r4_lattice3(X24,X28,X27)|r2_hidden(X23,a_2_2_lattice3(X24,X27))|(v2_struct_0(X24)|~v10_lattices(X24)|~v4_lattice3(X24)|~l3_lattices(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.12/0.38  cnf(c_0_11, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_12, plain, (r4_lattice3(X1,esk3_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,X3))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_13, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_14, plain, (r1_lattices(X1,X2,esk3_3(X3,X1,X4))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X3,a_2_2_lattice3(X1,X4))|~r2_hidden(X2,X4)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.12/0.38  cnf(c_0_15, plain, (X1=esk3_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  fof(c_0_16, plain, ![X9, X10, X11, X12, X13]:((~r3_lattice3(X9,X10,X11)|(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X11)|r1_lattices(X9,X10,X12)))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk1_3(X9,X10,X13),u1_struct_0(X9))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((r2_hidden(esk1_3(X9,X10,X13),X13)|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&(~r1_lattices(X9,X10,esk1_3(X9,X10,X13))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.12/0.38  cnf(c_0_17, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X3,a_2_2_lattice3(X1,X4))|~r2_hidden(X2,X4)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.38  cnf(c_0_18, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  fof(c_0_19, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2)))))), inference(assume_negation,[status(cth)],[t38_lattice3])).
% 0.12/0.38  cnf(c_0_20, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_21, plain, (r3_lattice3(X1,X2,a_2_2_lattice3(X3,X4))|r1_lattices(X3,X5,esk1_3(X1,X2,a_2_2_lattice3(X3,X4)))|v2_struct_0(X1)|v2_struct_0(X3)|~v4_lattice3(X3)|~r2_hidden(X5,X4)|~m1_subset_1(X5,u1_struct_0(X3))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X3)|~l3_lattices(X3)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.38  fof(c_0_22, negated_conjecture, ((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v4_lattice3(esk5_0))&l3_lattices(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(r2_hidden(esk6_0,esk7_0)&(~r3_lattices(esk5_0,esk6_0,k15_lattice3(esk5_0,esk7_0))|~r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.12/0.38  fof(c_0_23, plain, ![X29, X30, X31, X32, X33]:(((r3_lattice3(X29,X30,X31)|X30!=k16_lattice3(X29,X31)|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29)))&(~m1_subset_1(X32,u1_struct_0(X29))|(~r3_lattice3(X29,X32,X31)|r3_lattices(X29,X32,X30))|X30!=k16_lattice3(X29,X31)|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29))))&((m1_subset_1(esk4_3(X29,X30,X33),u1_struct_0(X29))|~r3_lattice3(X29,X30,X33)|X30=k16_lattice3(X29,X33)|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29)))&((r3_lattice3(X29,esk4_3(X29,X30,X33),X33)|~r3_lattice3(X29,X30,X33)|X30=k16_lattice3(X29,X33)|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29)))&(~r3_lattices(X29,esk4_3(X29,X30,X33),X30)|~r3_lattice3(X29,X30,X33)|X30=k16_lattice3(X29,X33)|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.12/0.38  cnf(c_0_24, plain, (r3_lattice3(X1,X2,a_2_2_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  fof(c_0_26, plain, ![X35, X36]:(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)|k15_lattice3(X35,X36)=k16_lattice3(X35,a_2_2_lattice3(X35,X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 0.12/0.38  cnf(c_0_27, plain, (r3_lattices(X2,X1,X4)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattice3(X2,X1,X3)|X4!=k16_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (r3_lattice3(X1,esk6_0,a_2_2_lattice3(X1,esk7_0))|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk6_0,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.38  fof(c_0_29, plain, ![X21, X22]:(v2_struct_0(X21)|~l3_lattices(X21)|m1_subset_1(k16_lattice3(X21,X22),u1_struct_0(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (~r3_lattices(esk5_0,esk6_0,k15_lattice3(esk5_0,esk7_0))|~r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_31, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (v4_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (r3_lattices(X1,esk6_0,X2)|v2_struct_0(X1)|X2!=k16_lattice3(X1,a_2_2_lattice3(X1,esk7_0))|~v4_lattice3(X1)|~m1_subset_1(esk6_0,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.38  cnf(c_0_37, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  fof(c_0_38, plain, ![X6, X7, X8]:((~r3_lattices(X6,X7,X8)|r1_lattices(X6,X7,X8)|(v2_struct_0(X6)|~v6_lattices(X6)|~v8_lattices(X6)|~v9_lattices(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))&(~r1_lattices(X6,X7,X8)|r3_lattices(X6,X7,X8)|(v2_struct_0(X6)|~v6_lattices(X6)|~v8_lattices(X6)|~v9_lattices(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.12/0.38  fof(c_0_39, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (~r3_lattices(esk5_0,esk6_0,k16_lattice3(esk5_0,a_2_2_lattice3(esk5_0,esk7_0)))|~r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (r3_lattices(X1,esk6_0,k16_lattice3(X1,a_2_2_lattice3(X1,esk7_0)))|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk6_0,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_37])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_43, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.38  cnf(c_0_44, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_45, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_46, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_47, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (~r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_32]), c_0_42]), c_0_33]), c_0_34])]), c_0_35])).
% 0.12/0.38  cnf(c_0_49, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])).
% 0.12/0.38  cnf(c_0_50, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_51, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_37])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (~r1_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),esk6_0)|~m1_subset_1(k16_lattice3(esk5_0,esk7_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_42]), c_0_33]), c_0_34])]), c_0_35])).
% 0.12/0.38  cnf(c_0_53, plain, (r1_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_37])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (~m1_subset_1(k16_lattice3(esk5_0,esk7_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_32]), c_0_25]), c_0_42]), c_0_33]), c_0_34])]), c_0_35])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_37]), c_0_34])]), c_0_35]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 56
% 0.12/0.38  # Proof object clause steps            : 37
% 0.12/0.38  # Proof object formula steps           : 19
% 0.12/0.38  # Proof object conjectures             : 18
% 0.12/0.38  # Proof object clause conjectures      : 15
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 22
% 0.12/0.38  # Proof object initial formulas used   : 9
% 0.12/0.38  # Proof object generating inferences   : 15
% 0.12/0.38  # Proof object simplifying inferences  : 32
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 9
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 35
% 0.12/0.38  # Removed in clause preprocessing      : 1
% 0.12/0.38  # Initial clauses in saturation        : 34
% 0.12/0.38  # Processed clauses                    : 130
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 10
% 0.12/0.38  # ...remaining for further processing  : 120
% 0.12/0.38  # Other redundant clauses eliminated   : 1
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 0
% 0.12/0.38  # Generated clauses                    : 86
% 0.12/0.38  # ...of the previous two non-trivial   : 81
% 0.12/0.38  # Contextual simplify-reflections      : 29
% 0.12/0.38  # Paramodulations                      : 83
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 3
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 84
% 0.12/0.38  #    Positive orientable unit clauses  : 5
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 4
% 0.12/0.38  #    Non-unit-clauses                  : 75
% 0.12/0.38  # Current number of unprocessed clauses: 19
% 0.12/0.38  # ...number of literals in the above   : 196
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 35
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 4619
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 156
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 40
% 0.12/0.38  # Unit Clause-clause subsumption calls : 18
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 0
% 0.12/0.38  # BW rewrite match successes           : 0
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 7387
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.043 s
% 0.12/0.38  # System time              : 0.002 s
% 0.12/0.38  # Total time               : 0.045 s
% 0.12/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
