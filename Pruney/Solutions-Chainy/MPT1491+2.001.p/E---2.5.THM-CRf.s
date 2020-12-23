%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:58 EST 2020

% Result     : Theorem 9.17s
% Output     : CNFRefutation 9.17s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 753 expanded)
%              Number of clauses        :   49 ( 238 expanded)
%              Number of leaves         :    6 ( 186 expanded)
%              Depth                    :   16
%              Number of atoms          :  316 (4949 expanded)
%              Number of equality atoms :   13 (  94 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_lattice3,conjecture,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v17_lattices(X2)
        & l3_lattices(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(X2))
         => ( r3_lattice3(X2,X3,X1)
          <=> r4_lattice3(X2,k7_lattices(X2,X3),a_2_0_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_lattice3)).

fof(t23_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v17_lattices(X2)
        & l3_lattices(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(X2))
         => ( r4_lattice3(X2,X3,X1)
          <=> r3_lattice3(X2,k7_lattices(X2,X3),a_2_0_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattice3)).

fof(t49_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k7_lattices(X1,k7_lattices(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(fraenkel_a_2_0_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X3)
        & v10_lattices(X3)
        & v17_lattices(X3)
        & l3_lattices(X3) )
     => ( r2_hidden(X1,a_2_0_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X3))
            & X1 = k7_lattices(X3,X4)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_lattice3)).

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

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( ~ v2_struct_0(X2)
          & v10_lattices(X2)
          & v17_lattices(X2)
          & l3_lattices(X2) )
       => ! [X3] :
            ( m1_subset_1(X3,u1_struct_0(X2))
           => ( r3_lattice3(X2,X3,X1)
            <=> r4_lattice3(X2,k7_lattices(X2,X3),a_2_0_lattice3(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_lattice3])).

fof(c_0_7,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r4_lattice3(X21,X22,X20)
        | r3_lattice3(X21,k7_lattices(X21,X22),a_2_0_lattice3(X20,X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v17_lattices(X21)
        | ~ l3_lattices(X21) )
      & ( ~ r3_lattice3(X21,k7_lattices(X21,X22),a_2_0_lattice3(X20,X21))
        | r4_lattice3(X21,X22,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v17_lattices(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattice3])])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v10_lattices(esk4_0)
    & v17_lattices(esk4_0)
    & l3_lattices(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ( ~ r3_lattice3(esk4_0,esk5_0,esk3_0)
      | ~ r4_lattice3(esk4_0,k7_lattices(esk4_0,esk5_0),a_2_0_lattice3(esk3_0,esk4_0)) )
    & ( r3_lattice3(esk4_0,esk5_0,esk3_0)
      | r4_lattice3(esk4_0,k7_lattices(esk4_0,esk5_0),a_2_0_lattice3(esk3_0,esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( v2_struct_0(X7)
      | ~ v10_lattices(X7)
      | ~ v17_lattices(X7)
      | ~ l3_lattices(X7)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | k7_lattices(X7,k7_lattices(X7,X8)) = X8 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).

cnf(c_0_10,plain,
    ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X3,X1))
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,esk3_0)
    | r4_lattice3(esk4_0,k7_lattices(esk4_0,esk5_0),a_2_0_lattice3(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v17_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v10_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( l3_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k7_lattices(X1,X2)) = X2
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X15,X16,X17,X19] :
      ( ( m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X17))
        | ~ r2_hidden(X15,a_2_0_lattice3(X16,X17))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v17_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( X15 = k7_lattices(X17,esk2_3(X15,X16,X17))
        | ~ r2_hidden(X15,a_2_0_lattice3(X16,X17))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v17_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X16)
        | ~ r2_hidden(X15,a_2_0_lattice3(X16,X17))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v17_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X17))
        | X15 != k7_lattices(X17,X19)
        | ~ r2_hidden(X19,X16)
        | r2_hidden(X15,a_2_0_lattice3(X16,X17))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v17_lattices(X17)
        | ~ l3_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_lattice3])])])])])])).

fof(c_0_18,plain,(
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

cnf(c_0_19,negated_conjecture,
    ( r3_lattice3(esk4_0,k7_lattices(esk4_0,k7_lattices(esk4_0,esk5_0)),a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))
    | r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k7_lattices(esk4_0,k7_lattices(esk4_0,X1)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,a_2_0_lattice3(X4,X2))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != k7_lattices(X2,X1)
    | ~ r2_hidden(X1,X4)
    | ~ v10_lattices(X2)
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))
    | r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(X2,esk4_0))
    | ~ r2_hidden(k7_lattices(esk4_0,X1),X2)
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])])).

cnf(c_0_26,plain,
    ( r2_hidden(k7_lattices(X1,X2),a_2_0_lattice3(X3,X1))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ v17_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_lattices(esk4_0,esk5_0,X1)
    | r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21]),c_0_14])]),c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk4_0),esk4_0))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_29,plain,
    ( X1 = k7_lattices(X2,esk2_3(X1,X3,X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(X3,X2))
    | ~ v10_lattices(X2)
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( r1_lattices(esk4_0,esk5_0,X1)
    | r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( esk2_3(X1,X2,esk4_0) = k7_lattices(esk4_0,X1)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk4_0))
    | ~ m1_subset_1(esk2_3(X1,X2,esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_29]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X3))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,X3))
    | ~ v10_lattices(X3)
    | ~ v17_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattices(esk4_0,esk5_0,esk1_3(X1,X2,esk3_0))
    | r3_lattice3(esk4_0,esk5_0,esk3_0)
    | r3_lattice3(X1,X2,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k7_lattices(esk4_0,esk1_3(X1,X2,esk3_0)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk1_3(X1,X2,esk3_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_36,plain,(
    ! [X5,X6] :
      ( v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | m1_subset_1(k7_lattices(X5,X6),u1_struct_0(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,X3))
    | ~ v10_lattices(X3)
    | ~ v17_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( esk2_3(X1,X2,esk4_0) = k7_lattices(esk4_0,X1)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ m1_subset_1(k7_lattices(esk4_0,esk1_3(esk4_0,esk5_0,esk3_0)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk1_3(esk4_0,esk5_0,esk3_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_21]),c_0_14])]),c_0_15])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k7_lattices(esk4_0,X1),X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ m1_subset_1(esk1_3(esk4_0,esk5_0,esk3_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_14])]),c_0_15])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X3,esk4_0),a_2_0_lattice3(X2,esk4_0))
    | ~ r2_hidden(X1,a_2_0_lattice3(X3,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( k7_lattices(esk4_0,k7_lattices(esk4_0,X1)) = X1
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_38]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,a_2_0_lattice3(X2,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_38]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_21]),c_0_14])]),c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk4_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_37]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( k7_lattices(esk4_0,k7_lattices(esk4_0,esk1_3(X1,X2,a_2_0_lattice3(X3,esk4_0)))) = esk1_3(X1,X2,a_2_0_lattice3(X3,esk4_0))
    | r3_lattice3(X1,X2,a_2_0_lattice3(X3,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( r3_lattice3(X1,X2,a_2_0_lattice3(X3,esk4_0))
    | m1_subset_1(k7_lattices(esk4_0,esk1_3(X1,X2,a_2_0_lattice3(X3,esk4_0))),u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( ~ r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ r4_lattice3(esk4_0,k7_lattices(esk4_0,esk5_0),a_2_0_lattice3(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_52,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X3,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattices(esk4_0,esk5_0,X1)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_47]),c_0_21]),c_0_14])]),c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,a_2_0_lattice3(a_2_0_lattice3(X3,esk4_0),esk4_0)),X3)
    | r3_lattice3(X1,X2,a_2_0_lattice3(a_2_0_lattice3(X3,esk4_0),esk4_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( r3_lattice3(X1,X2,a_2_0_lattice3(X3,esk4_0))
    | m1_subset_1(esk1_3(X1,X2,a_2_0_lattice3(X3,esk4_0)),u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_49]),c_0_14])]),c_0_15]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ r3_lattice3(esk4_0,k7_lattices(esk4_0,k7_lattices(esk4_0,esk5_0)),a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))
    | ~ r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( r1_lattices(esk4_0,esk5_0,esk1_3(X1,X2,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0)))
    | r3_lattice3(X1,X2,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( ~ r3_lattice3(esk4_0,esk5_0,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))
    | ~ r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_20]),c_0_21])])).

cnf(c_0_59,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))
    | ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_57]),c_0_21]),c_0_14])]),c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_40]),c_0_21]),c_0_14])]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n020.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 11:19:22 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.32  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 9.17/9.33  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 9.17/9.33  # and selection function SelectMaxLComplexAvoidPosPred.
% 9.17/9.33  #
% 9.17/9.33  # Preprocessing time       : 0.028 s
% 9.17/9.33  # Presaturation interreduction done
% 9.17/9.33  
% 9.17/9.33  # Proof found!
% 9.17/9.33  # SZS status Theorem
% 9.17/9.33  # SZS output start CNFRefutation
% 9.17/9.33  fof(t24_lattice3, conjecture, ![X1, X2]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v17_lattices(X2))&l3_lattices(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>(r3_lattice3(X2,X3,X1)<=>r4_lattice3(X2,k7_lattices(X2,X3),a_2_0_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_lattice3)).
% 9.17/9.33  fof(t23_lattice3, axiom, ![X1, X2]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v17_lattices(X2))&l3_lattices(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>(r4_lattice3(X2,X3,X1)<=>r3_lattice3(X2,k7_lattices(X2,X3),a_2_0_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_lattice3)).
% 9.17/9.33  fof(t49_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k7_lattices(X1,k7_lattices(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_lattices)).
% 9.17/9.33  fof(fraenkel_a_2_0_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X3))&v10_lattices(X3))&v17_lattices(X3))&l3_lattices(X3))=>(r2_hidden(X1,a_2_0_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X3))&X1=k7_lattices(X3,X4))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_lattice3)).
% 9.17/9.33  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 9.17/9.33  fof(dt_k7_lattices, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattices)).
% 9.17/9.33  fof(c_0_6, negated_conjecture, ~(![X1, X2]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v17_lattices(X2))&l3_lattices(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>(r3_lattice3(X2,X3,X1)<=>r4_lattice3(X2,k7_lattices(X2,X3),a_2_0_lattice3(X1,X2)))))), inference(assume_negation,[status(cth)],[t24_lattice3])).
% 9.17/9.33  fof(c_0_7, plain, ![X20, X21, X22]:((~r4_lattice3(X21,X22,X20)|r3_lattice3(X21,k7_lattices(X21,X22),a_2_0_lattice3(X20,X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v17_lattices(X21)|~l3_lattices(X21)))&(~r3_lattice3(X21,k7_lattices(X21,X22),a_2_0_lattice3(X20,X21))|r4_lattice3(X21,X22,X20)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v10_lattices(X21)|~v17_lattices(X21)|~l3_lattices(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattice3])])])])])).
% 9.17/9.33  fof(c_0_8, negated_conjecture, ((((~v2_struct_0(esk4_0)&v10_lattices(esk4_0))&v17_lattices(esk4_0))&l3_lattices(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&((~r3_lattice3(esk4_0,esk5_0,esk3_0)|~r4_lattice3(esk4_0,k7_lattices(esk4_0,esk5_0),a_2_0_lattice3(esk3_0,esk4_0)))&(r3_lattice3(esk4_0,esk5_0,esk3_0)|r4_lattice3(esk4_0,k7_lattices(esk4_0,esk5_0),a_2_0_lattice3(esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 9.17/9.33  fof(c_0_9, plain, ![X7, X8]:(v2_struct_0(X7)|~v10_lattices(X7)|~v17_lattices(X7)|~l3_lattices(X7)|(~m1_subset_1(X8,u1_struct_0(X7))|k7_lattices(X7,k7_lattices(X7,X8))=X8)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).
% 9.17/9.33  cnf(c_0_10, plain, (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X3,X1))|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.17/9.33  cnf(c_0_11, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,esk3_0)|r4_lattice3(esk4_0,k7_lattices(esk4_0,esk5_0),a_2_0_lattice3(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 9.17/9.33  cnf(c_0_12, negated_conjecture, (v17_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 9.17/9.33  cnf(c_0_13, negated_conjecture, (v10_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 9.17/9.33  cnf(c_0_14, negated_conjecture, (l3_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 9.17/9.33  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 9.17/9.33  cnf(c_0_16, plain, (v2_struct_0(X1)|k7_lattices(X1,k7_lattices(X1,X2))=X2|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 9.17/9.33  fof(c_0_17, plain, ![X15, X16, X17, X19]:((((m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X17))|~r2_hidden(X15,a_2_0_lattice3(X16,X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v17_lattices(X17)|~l3_lattices(X17)))&(X15=k7_lattices(X17,esk2_3(X15,X16,X17))|~r2_hidden(X15,a_2_0_lattice3(X16,X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v17_lattices(X17)|~l3_lattices(X17))))&(r2_hidden(esk2_3(X15,X16,X17),X16)|~r2_hidden(X15,a_2_0_lattice3(X16,X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v17_lattices(X17)|~l3_lattices(X17))))&(~m1_subset_1(X19,u1_struct_0(X17))|X15!=k7_lattices(X17,X19)|~r2_hidden(X19,X16)|r2_hidden(X15,a_2_0_lattice3(X16,X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v17_lattices(X17)|~l3_lattices(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_lattice3])])])])])])).
% 9.17/9.33  fof(c_0_18, plain, ![X9, X10, X11, X12, X13]:((~r3_lattice3(X9,X10,X11)|(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X11)|r1_lattices(X9,X10,X12)))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk1_3(X9,X10,X13),u1_struct_0(X9))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((r2_hidden(esk1_3(X9,X10,X13),X13)|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&(~r1_lattices(X9,X10,esk1_3(X9,X10,X13))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 9.17/9.33  cnf(c_0_19, negated_conjecture, (r3_lattice3(esk4_0,k7_lattices(esk4_0,k7_lattices(esk4_0,esk5_0)),a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))|r3_lattice3(esk4_0,esk5_0,esk3_0)|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_20, negated_conjecture, (k7_lattices(esk4_0,k7_lattices(esk4_0,X1))=X1|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 9.17/9.33  cnf(c_0_22, plain, (r2_hidden(X3,a_2_0_lattice3(X4,X2))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=k7_lattices(X2,X1)|~r2_hidden(X1,X4)|~v10_lattices(X2)|~v17_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.17/9.33  cnf(c_0_23, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 9.17/9.33  cnf(c_0_24, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))|r3_lattice3(esk4_0,esk5_0,esk3_0)|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 9.17/9.33  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(X2,esk4_0))|~r2_hidden(k7_lattices(esk4_0,X1),X2)|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])])).
% 9.17/9.33  cnf(c_0_26, plain, (r2_hidden(k7_lattices(X1,X2),a_2_0_lattice3(X3,X1))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~v17_lattices(X1)|~v10_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_22])).
% 9.17/9.33  cnf(c_0_27, negated_conjecture, (r1_lattices(esk4_0,esk5_0,X1)|r3_lattice3(esk4_0,esk5_0,esk3_0)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk4_0),esk4_0))|~r2_hidden(X1,X2)|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_29, plain, (X1=k7_lattices(X2,esk2_3(X1,X3,X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_lattice3(X3,X2))|~v10_lattices(X2)|~v17_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.17/9.33  cnf(c_0_30, negated_conjecture, (r1_lattices(esk4_0,esk5_0,X1)|r3_lattice3(esk4_0,esk5_0,esk3_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 9.17/9.33  cnf(c_0_31, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 9.17/9.33  cnf(c_0_32, negated_conjecture, (esk2_3(X1,X2,esk4_0)=k7_lattices(esk4_0,X1)|~r2_hidden(X1,a_2_0_lattice3(X2,esk4_0))|~m1_subset_1(esk2_3(X1,X2,esk4_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_29]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_33, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X3))|v2_struct_0(X3)|~r2_hidden(X1,a_2_0_lattice3(X2,X3))|~v10_lattices(X3)|~v17_lattices(X3)|~l3_lattices(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.17/9.33  cnf(c_0_34, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 9.17/9.33  cnf(c_0_35, negated_conjecture, (r1_lattices(esk4_0,esk5_0,esk1_3(X1,X2,esk3_0))|r3_lattice3(esk4_0,esk5_0,esk3_0)|r3_lattice3(X1,X2,esk3_0)|v2_struct_0(X1)|~m1_subset_1(k7_lattices(esk4_0,esk1_3(X1,X2,esk3_0)),u1_struct_0(esk4_0))|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(esk1_3(X1,X2,esk3_0),u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 9.17/9.33  fof(c_0_36, plain, ![X5, X6]:(v2_struct_0(X5)|~l3_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|m1_subset_1(k7_lattices(X5,X6),u1_struct_0(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).
% 9.17/9.33  cnf(c_0_37, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|v2_struct_0(X3)|~r2_hidden(X1,a_2_0_lattice3(X2,X3))|~v10_lattices(X3)|~v17_lattices(X3)|~l3_lattices(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 9.17/9.33  cnf(c_0_38, negated_conjecture, (esk2_3(X1,X2,esk4_0)=k7_lattices(esk4_0,X1)|~r2_hidden(X1,a_2_0_lattice3(X2,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_39, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,esk3_0)|~m1_subset_1(k7_lattices(esk4_0,esk1_3(esk4_0,esk5_0,esk3_0)),u1_struct_0(esk4_0))|~m1_subset_1(esk1_3(esk4_0,esk5_0,esk3_0),u1_struct_0(esk4_0))|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_21]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_40, plain, (v2_struct_0(X1)|m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 9.17/9.33  cnf(c_0_41, negated_conjecture, (r2_hidden(k7_lattices(esk4_0,X1),X2)|~r2_hidden(X1,a_2_0_lattice3(X2,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_42, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,esk3_0)|~m1_subset_1(esk1_3(esk4_0,esk5_0,esk3_0),u1_struct_0(esk4_0))|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_43, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 9.17/9.33  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(esk2_3(X1,X3,esk4_0),a_2_0_lattice3(X2,esk4_0))|~r2_hidden(X1,a_2_0_lattice3(X3,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_45, negated_conjecture, (k7_lattices(esk4_0,k7_lattices(esk4_0,X1))=X1|~r2_hidden(X1,a_2_0_lattice3(X2,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_38]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_46, negated_conjecture, (m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~r2_hidden(X1,a_2_0_lattice3(X2,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_38]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_47, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,esk3_0)|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_21]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,a_2_0_lattice3(a_2_0_lattice3(X2,esk4_0),esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_37]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_49, negated_conjecture, (k7_lattices(esk4_0,k7_lattices(esk4_0,esk1_3(X1,X2,a_2_0_lattice3(X3,esk4_0))))=esk1_3(X1,X2,a_2_0_lattice3(X3,esk4_0))|r3_lattice3(X1,X2,a_2_0_lattice3(X3,esk4_0))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_45, c_0_31])).
% 9.17/9.33  cnf(c_0_50, negated_conjecture, (r3_lattice3(X1,X2,a_2_0_lattice3(X3,esk4_0))|m1_subset_1(k7_lattices(esk4_0,esk1_3(X1,X2,a_2_0_lattice3(X3,esk4_0))),u1_struct_0(esk4_0))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 9.17/9.33  cnf(c_0_51, negated_conjecture, (~r3_lattice3(esk4_0,esk5_0,esk3_0)|~r4_lattice3(esk4_0,k7_lattices(esk4_0,esk5_0),a_2_0_lattice3(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 9.17/9.33  cnf(c_0_52, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X3,X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.17/9.33  cnf(c_0_53, negated_conjecture, (r1_lattices(esk4_0,esk5_0,X1)|~r2_hidden(X1,esk3_0)|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_47]), c_0_21]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_3(X1,X2,a_2_0_lattice3(a_2_0_lattice3(X3,esk4_0),esk4_0)),X3)|r3_lattice3(X1,X2,a_2_0_lattice3(a_2_0_lattice3(X3,esk4_0),esk4_0))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 9.17/9.33  cnf(c_0_55, negated_conjecture, (r3_lattice3(X1,X2,a_2_0_lattice3(X3,esk4_0))|m1_subset_1(esk1_3(X1,X2,a_2_0_lattice3(X3,esk4_0)),u1_struct_0(esk4_0))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_49]), c_0_14])]), c_0_15]), c_0_50])).
% 9.17/9.33  cnf(c_0_56, negated_conjecture, (~r3_lattice3(esk4_0,k7_lattices(esk4_0,k7_lattices(esk4_0,esk5_0)),a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))|~r3_lattice3(esk4_0,esk5_0,esk3_0)|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_57, negated_conjecture, (r1_lattices(esk4_0,esk5_0,esk1_3(X1,X2,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0)))|r3_lattice3(X1,X2,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))|v2_struct_0(X1)|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 9.17/9.33  cnf(c_0_58, negated_conjecture, (~r3_lattice3(esk4_0,esk5_0,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))|~r3_lattice3(esk4_0,esk5_0,esk3_0)|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_20]), c_0_21])])).
% 9.17/9.33  cnf(c_0_59, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,a_2_0_lattice3(a_2_0_lattice3(esk3_0,esk4_0),esk4_0))|~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_57]), c_0_21]), c_0_14])]), c_0_15])).
% 9.17/9.33  cnf(c_0_60, negated_conjecture, (~m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_47])).
% 9.17/9.33  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_40]), c_0_21]), c_0_14])]), c_0_15]), ['proof']).
% 9.17/9.33  # SZS output end CNFRefutation
% 9.17/9.33  # Proof object total steps             : 62
% 9.17/9.33  # Proof object clause steps            : 49
% 9.17/9.33  # Proof object formula steps           : 13
% 9.17/9.33  # Proof object conjectures             : 39
% 9.17/9.33  # Proof object clause conjectures      : 36
% 9.17/9.33  # Proof object formula conjectures     : 3
% 9.17/9.33  # Proof object initial clauses used    : 19
% 9.17/9.33  # Proof object initial formulas used   : 6
% 9.17/9.33  # Proof object generating inferences   : 30
% 9.17/9.33  # Proof object simplifying inferences  : 97
% 9.17/9.33  # Training examples: 0 positive, 0 negative
% 9.17/9.33  # Parsed axioms                        : 6
% 9.17/9.33  # Removed by relevancy pruning/SinE    : 0
% 9.17/9.33  # Initial clauses                      : 19
% 9.17/9.33  # Removed in clause preprocessing      : 0
% 9.17/9.33  # Initial clauses in saturation        : 19
% 9.17/9.33  # Processed clauses                    : 43865
% 9.17/9.33  # ...of these trivial                  : 144
% 9.17/9.33  # ...subsumed                          : 40500
% 9.17/9.33  # ...remaining for further processing  : 3221
% 9.17/9.33  # Other redundant clauses eliminated   : 235
% 9.17/9.33  # Clauses deleted for lack of memory   : 0
% 9.17/9.33  # Backward-subsumed                    : 838
% 9.17/9.33  # Backward-rewritten                   : 0
% 9.17/9.33  # Generated clauses                    : 486004
% 9.17/9.33  # ...of the previous two non-trivial   : 484532
% 9.17/9.33  # Contextual simplify-reflections      : 440
% 9.17/9.33  # Paramodulations                      : 485435
% 9.17/9.33  # Factorizations                       : 0
% 9.17/9.33  # Equation resolutions                 : 569
% 9.17/9.33  # Propositional unsat checks           : 0
% 9.17/9.33  #    Propositional check models        : 0
% 9.17/9.33  #    Propositional check unsatisfiable : 0
% 9.17/9.33  #    Propositional clauses             : 0
% 9.17/9.33  #    Propositional clauses after purity: 0
% 9.17/9.33  #    Propositional unsat core size     : 0
% 9.17/9.33  #    Propositional preprocessing time  : 0.000
% 9.17/9.33  #    Propositional encoding time       : 0.000
% 9.17/9.33  #    Propositional solver time         : 0.000
% 9.17/9.33  #    Success case prop preproc time    : 0.000
% 9.17/9.33  #    Success case prop encoding time   : 0.000
% 9.17/9.33  #    Success case prop solver time     : 0.000
% 9.17/9.33  # Current number of processed clauses  : 2364
% 9.17/9.33  #    Positive orientable unit clauses  : 4
% 9.17/9.33  #    Positive unorientable unit clauses: 0
% 9.17/9.33  #    Negative unit clauses             : 2
% 9.17/9.33  #    Non-unit-clauses                  : 2358
% 9.17/9.33  # Current number of unprocessed clauses: 416742
% 9.17/9.33  # ...number of literals in the above   : 2748078
% 9.17/9.33  # Current number of archived formulas  : 0
% 9.17/9.33  # Current number of archived clauses   : 857
% 9.17/9.33  # Clause-clause subsumption calls (NU) : 9572925
% 9.17/9.33  # Rec. Clause-clause subsumption calls : 3599042
% 9.17/9.33  # Non-unit clause-clause subsumptions  : 41778
% 9.17/9.33  # Unit Clause-clause subsumption calls : 227
% 9.17/9.33  # Rewrite failures with RHS unbound    : 0
% 9.17/9.33  # BW rewrite match attempts            : 0
% 9.17/9.33  # BW rewrite match successes           : 0
% 9.17/9.33  # Condensation attempts                : 0
% 9.17/9.33  # Condensation successes               : 0
% 9.17/9.33  # Termbank termtop insertions          : 26309016
% 9.17/9.35  
% 9.17/9.35  # -------------------------------------------------
% 9.17/9.35  # User time                : 8.840 s
% 9.17/9.35  # System time              : 0.195 s
% 9.17/9.35  # Total time               : 9.035 s
% 9.17/9.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
