%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 332 expanded)
%              Number of clauses        :   40 ( 111 expanded)
%              Number of leaves         :    9 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  276 (2082 expanded)
%              Number of equality atoms :   18 ( 196 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   2 average)
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

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(t40_lattice3,axiom,(
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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(d4_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ( v4_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k1_lattices(X1,X2,X3) = k1_lattices(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattices)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v4_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v5_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v6_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v7_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v8_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v9_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v10_lattices(esk3_0)
    & v4_lattice3(esk3_0)
    & l3_lattices(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & r2_hidden(esk4_0,esk5_0)
    & r3_lattice3(esk3_0,esk4_0,esk5_0)
    & k16_lattice3(esk3_0,esk5_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X19,X20,X21] :
      ( ( r3_lattices(X19,X20,k15_lattice3(X19,X21))
        | ~ r2_hidden(X20,X21)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) )
      & ( r3_lattices(X19,k16_lattice3(X19,X21),X20)
        | ~ r2_hidden(X20,X21)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ l3_lattices(X17)
      | m1_subset_1(k16_lattice3(X17,X18),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_14,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ v10_lattices(X22)
      | ~ v4_lattice3(X22)
      | ~ l3_lattices(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ r3_lattice3(X22,X23,X24)
      | r3_lattices(X22,X23,k16_lattice3(X22,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattice3])])])])).

fof(c_0_15,plain,(
    ! [X8] :
      ( ( l1_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( l2_lattices(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_16,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r3_lattices(X9,X10,X11)
        | r1_lattices(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v6_lattices(X9)
        | ~ v8_lattices(X9)
        | ~ v9_lattices(X9)
        | ~ l3_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) )
      & ( ~ r1_lattices(X9,X10,X11)
        | r3_lattices(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v6_lattices(X9)
        | ~ v8_lattices(X9)
        | ~ v9_lattices(X9)
        | ~ l3_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_17,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v10_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( l3_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( v4_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_28,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r1_lattices(X5,X6,X7)
        | k1_lattices(X5,X6,X7) = X7
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l2_lattices(X5) )
      & ( k1_lattices(X5,X6,X7) != X7
        | r1_lattices(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l2_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_29,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v9_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v8_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( v6_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( r3_lattices(esk3_0,k16_lattice3(esk3_0,X1),esk4_0)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_36,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v4_lattices(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | k1_lattices(X12,X13,X14) = k1_lattices(X12,X14,X13)
        | v2_struct_0(X12)
        | ~ l2_lattices(X12) )
      & ( m1_subset_1(esk1_1(X12),u1_struct_0(X12))
        | v4_lattices(X12)
        | v2_struct_0(X12)
        | ~ l2_lattices(X12) )
      & ( m1_subset_1(esk2_1(X12),u1_struct_0(X12))
        | v4_lattices(X12)
        | v2_struct_0(X12)
        | ~ l2_lattices(X12) )
      & ( k1_lattices(X12,esk1_1(X12),esk2_1(X12)) != k1_lattices(X12,esk2_1(X12),esk1_1(X12))
        | v4_lattices(X12)
        | v2_struct_0(X12)
        | ~ l2_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_lattices])])])])])])).

cnf(c_0_37,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k16_lattice3(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattices(esk3_0,esk4_0,k16_lattice3(esk3_0,X1))
    | ~ r3_lattice3(esk3_0,esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_25]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( r3_lattice3(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( l2_lattices(esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( r1_lattices(esk3_0,X1,esk4_0)
    | ~ r3_lattices(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_31]),c_0_32]),c_0_33]),c_0_19])]),c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( r3_lattices(esk3_0,k16_lattice3(esk3_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_45,plain,
    ( k1_lattices(X1,X2,X3) = k1_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v4_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v4_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattices(esk3_0,X1,k16_lattice3(esk3_0,X2))
    | ~ r3_lattices(esk3_0,X1,k16_lattice3(esk3_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_38]),c_0_31]),c_0_32]),c_0_33]),c_0_19])]),c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( r3_lattices(esk3_0,esk4_0,k16_lattice3(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k1_lattices(esk3_0,X1,esk4_0) = esk4_0
    | ~ r1_lattices(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_42])]),c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattices(esk3_0,k16_lattice3(esk3_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_38])])).

cnf(c_0_51,negated_conjecture,
    ( k1_lattices(esk3_0,X1,esk4_0) = k1_lattices(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_42]),c_0_46])]),c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( k1_lattices(esk3_0,X1,k16_lattice3(esk3_0,X2)) = k16_lattice3(esk3_0,X2)
    | ~ r1_lattices(esk3_0,X1,k16_lattice3(esk3_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_38]),c_0_42])]),c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattices(esk3_0,esk4_0,k16_lattice3(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_24])])).

cnf(c_0_54,negated_conjecture,
    ( k1_lattices(esk3_0,k16_lattice3(esk3_0,esk5_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_38])])).

cnf(c_0_55,negated_conjecture,
    ( k1_lattices(esk3_0,k16_lattice3(esk3_0,X1),esk4_0) = k1_lattices(esk3_0,esk4_0,k16_lattice3(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( k1_lattices(esk3_0,esk4_0,k16_lattice3(esk3_0,esk5_0)) = k16_lattice3(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_24])])).

cnf(c_0_57,negated_conjecture,
    ( k16_lattice3(esk3_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.20/0.38  # and selection function SelectComplexG.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t42_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 0.20/0.38  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.38  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 0.20/0.38  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.20/0.38  fof(t40_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)=>r3_lattices(X1,X2,k16_lattice3(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattice3)).
% 0.20/0.38  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.20/0.38  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.20/0.38  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.20/0.38  fof(d4_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>(v4_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,X2,X3)=k1_lattices(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_lattices)).
% 0.20/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2)))), inference(assume_negation,[status(cth)],[t42_lattice3])).
% 0.20/0.38  fof(c_0_10, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.38  fof(c_0_11, negated_conjecture, ((((~v2_struct_0(esk3_0)&v10_lattices(esk3_0))&v4_lattice3(esk3_0))&l3_lattices(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&((r2_hidden(esk4_0,esk5_0)&r3_lattice3(esk3_0,esk4_0,esk5_0))&k16_lattice3(esk3_0,esk5_0)!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.20/0.38  fof(c_0_12, plain, ![X19, X20, X21]:((r3_lattices(X19,X20,k15_lattice3(X19,X21))|~r2_hidden(X20,X21)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19)))&(r3_lattices(X19,k16_lattice3(X19,X21),X20)|~r2_hidden(X20,X21)|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v10_lattices(X19)|~v4_lattice3(X19)|~l3_lattices(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.20/0.38  fof(c_0_13, plain, ![X17, X18]:(v2_struct_0(X17)|~l3_lattices(X17)|m1_subset_1(k16_lattice3(X17,X18),u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X22, X23, X24]:(v2_struct_0(X22)|~v10_lattices(X22)|~v4_lattice3(X22)|~l3_lattices(X22)|(~m1_subset_1(X23,u1_struct_0(X22))|(~r3_lattice3(X22,X23,X24)|r3_lattices(X22,X23,k16_lattice3(X22,X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattice3])])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X8]:((l1_lattices(X8)|~l3_lattices(X8))&(l2_lattices(X8)|~l3_lattices(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.20/0.38  fof(c_0_16, plain, ![X9, X10, X11]:((~r3_lattices(X9,X10,X11)|r1_lattices(X9,X10,X11)|(v2_struct_0(X9)|~v6_lattices(X9)|~v8_lattices(X9)|~v9_lattices(X9)|~l3_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))&(~r1_lattices(X9,X10,X11)|r3_lattices(X9,X10,X11)|(v2_struct_0(X9)|~v6_lattices(X9)|~v8_lattices(X9)|~v9_lattices(X9)|~l3_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.20/0.38  cnf(c_0_17, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (v10_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (l3_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_21, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_22, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_23, plain, (r3_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (v4_lattice3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_26, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_27, plain, (v2_struct_0(X1)|r3_lattices(X1,X2,k16_lattice3(X1,X3))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r3_lattice3(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_28, plain, ![X5, X6, X7]:((~r1_lattices(X5,X6,X7)|k1_lattices(X5,X6,X7)=X7|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l2_lattices(X5)))&(k1_lattices(X5,X6,X7)!=X7|r1_lattices(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l2_lattices(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.20/0.38  cnf(c_0_29, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_30, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (v9_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (v8_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (v6_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r3_lattices(esk3_0,k16_lattice3(esk3_0,X1),esk4_0)|~r2_hidden(esk4_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  fof(c_0_36, plain, ![X12, X13, X14]:((~v4_lattices(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~m1_subset_1(X14,u1_struct_0(X12))|k1_lattices(X12,X13,X14)=k1_lattices(X12,X14,X13)))|(v2_struct_0(X12)|~l2_lattices(X12)))&((m1_subset_1(esk1_1(X12),u1_struct_0(X12))|v4_lattices(X12)|(v2_struct_0(X12)|~l2_lattices(X12)))&((m1_subset_1(esk2_1(X12),u1_struct_0(X12))|v4_lattices(X12)|(v2_struct_0(X12)|~l2_lattices(X12)))&(k1_lattices(X12,esk1_1(X12),esk2_1(X12))!=k1_lattices(X12,esk2_1(X12),esk1_1(X12))|v4_lattices(X12)|(v2_struct_0(X12)|~l2_lattices(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_lattices])])])])])])).
% 0.20/0.38  cnf(c_0_37, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(k16_lattice3(esk3_0,X1),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_19]), c_0_20])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (r3_lattices(esk3_0,esk4_0,k16_lattice3(esk3_0,X1))|~r3_lattice3(esk3_0,esk4_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_25]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (r3_lattice3(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_41, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (l2_lattices(esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_19])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (r1_lattices(esk3_0,X1,esk4_0)|~r3_lattices(esk3_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_24]), c_0_31]), c_0_32]), c_0_33]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (r3_lattices(esk3_0,k16_lattice3(esk3_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.38  cnf(c_0_45, plain, (k1_lattices(X1,X2,X3)=k1_lattices(X1,X3,X2)|v2_struct_0(X1)|~v4_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (v4_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (r1_lattices(esk3_0,X1,k16_lattice3(esk3_0,X2))|~r3_lattices(esk3_0,X1,k16_lattice3(esk3_0,X2))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_38]), c_0_31]), c_0_32]), c_0_33]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (r3_lattices(esk3_0,esk4_0,k16_lattice3(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (k1_lattices(esk3_0,X1,esk4_0)=esk4_0|~r1_lattices(esk3_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_24]), c_0_42])]), c_0_20])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (r1_lattices(esk3_0,k16_lattice3(esk3_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_38])])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (k1_lattices(esk3_0,X1,esk4_0)=k1_lattices(esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_42]), c_0_46])]), c_0_20])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (k1_lattices(esk3_0,X1,k16_lattice3(esk3_0,X2))=k16_lattice3(esk3_0,X2)|~r1_lattices(esk3_0,X1,k16_lattice3(esk3_0,X2))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_38]), c_0_42])]), c_0_20])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (r1_lattices(esk3_0,esk4_0,k16_lattice3(esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_24])])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (k1_lattices(esk3_0,k16_lattice3(esk3_0,esk5_0),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_38])])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (k1_lattices(esk3_0,k16_lattice3(esk3_0,X1),esk4_0)=k1_lattices(esk3_0,esk4_0,k16_lattice3(esk3_0,X1))), inference(spm,[status(thm)],[c_0_51, c_0_38])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (k1_lattices(esk3_0,esk4_0,k16_lattice3(esk3_0,esk5_0))=k16_lattice3(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_24])])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (k16_lattice3(esk3_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 59
% 0.20/0.38  # Proof object clause steps            : 40
% 0.20/0.38  # Proof object formula steps           : 19
% 0.20/0.38  # Proof object conjectures             : 32
% 0.20/0.38  # Proof object clause conjectures      : 29
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 19
% 0.20/0.38  # Proof object initial formulas used   : 9
% 0.20/0.38  # Proof object generating inferences   : 20
% 0.20/0.38  # Proof object simplifying inferences  : 56
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 9
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 29
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 28
% 0.20/0.38  # Processed clauses                    : 88
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 88
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 1
% 0.20/0.38  # Generated clauses                    : 41
% 0.20/0.38  # ...of the previous two non-trivial   : 33
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 41
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 59
% 0.20/0.38  #    Positive orientable unit clauses  : 22
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 35
% 0.20/0.38  # Current number of unprocessed clauses: 1
% 0.20/0.38  # ...number of literals in the above   : 2
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 29
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 456
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 88
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 15
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 5
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3878
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
