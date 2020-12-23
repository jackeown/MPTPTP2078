%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t48_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:55 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 (2483 expanded)
%              Number of clauses        :   65 ( 832 expanded)
%              Number of leaves         :    9 ( 610 expanded)
%              Depth                    :   29
%              Number of atoms          :  445 (20885 expanded)
%              Number of equality atoms :    8 ( 120 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',t48_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',d21_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',dt_k15_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',d17_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',redefinition_r3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',cc1_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',t38_lattice3)).

fof(t25_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattices(X1,X2,X3)
                      & r1_lattices(X1,X3,X4) )
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',t25_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',dt_l3_lattices)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r4_lattice3(X19,X21,X20)
        | X21 != k15_lattice3(X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r4_lattice3(X19,X22,X20)
        | r1_lattices(X19,X21,X22)
        | X21 != k15_lattice3(X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( m1_subset_1(esk6_3(X19,X20,X21),u1_struct_0(X19))
        | ~ r4_lattice3(X19,X21,X20)
        | X21 = k15_lattice3(X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( r4_lattice3(X19,esk6_3(X19,X20,X21),X20)
        | ~ r4_lattice3(X19,X21,X20)
        | X21 = k15_lattice3(X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( ~ r1_lattices(X19,X21,esk6_3(X19,X20,X21))
        | ~ r4_lattice3(X19,X21,X20)
        | X21 = k15_lattice3(X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X9] :
      ( ~ v2_struct_0(esk1_0)
      & v10_lattices(esk1_0)
      & v4_lattice3(esk1_0)
      & l3_lattices(esk1_0)
      & ( m1_subset_1(esk4_1(X9),u1_struct_0(esk1_0))
        | ~ r2_hidden(X9,esk2_0)
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0)) )
      & ( r3_lattices(esk1_0,X9,esk4_1(X9))
        | ~ r2_hidden(X9,esk2_0)
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0)) )
      & ( r2_hidden(esk4_1(X9),esk3_0)
        | ~ r2_hidden(X9,esk2_0)
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0)) )
      & ~ r3_lattices(esk1_0,k15_lattice3(esk1_0,esk2_0),k15_lattice3(esk1_0,esk3_0)) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_12,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ l3_lattices(X24)
      | m1_subset_1(k15_lattice3(X24,X25),u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_13,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r4_lattice3(X13,X14,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r2_hidden(X16,X15)
        | r1_lattices(X13,X16,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) )
      & ( m1_subset_1(esk5_3(X13,X14,X17),u1_struct_0(X13))
        | r4_lattice3(X13,X14,X17)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) )
      & ( r2_hidden(esk5_3(X13,X14,X17),X17)
        | r4_lattice3(X13,X14,X17)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) )
      & ( ~ r1_lattices(X13,esk5_3(X13,X14,X17),X14)
        | r4_lattice3(X13,X14,X17)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk1_0,X1),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_21,plain,(
    ! [X43,X44,X45] :
      ( ( ~ r3_lattices(X43,X44,X45)
        | r1_lattices(X43,X44,X45)
        | v2_struct_0(X43)
        | ~ v6_lattices(X43)
        | ~ v8_lattices(X43)
        | ~ v9_lattices(X43)
        | ~ l3_lattices(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X43)) )
      & ( ~ r1_lattices(X43,X44,X45)
        | r3_lattices(X43,X44,X45)
        | v2_struct_0(X43)
        | ~ v6_lattices(X43)
        | ~ v8_lattices(X43)
        | ~ v9_lattices(X43)
        | ~ l3_lattices(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_22,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r4_lattice3(esk1_0,k15_lattice3(esk1_0,X1),X2)
    | m1_subset_1(esk5_3(esk1_0,k15_lattice3(esk1_0,X1),X2),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17])]),c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v4_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_lattices(esk1_0,k15_lattice3(esk1_0,X1),k15_lattice3(esk1_0,X2))
    | m1_subset_1(esk5_3(esk1_0,k15_lattice3(esk1_0,X2),X1),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_20]),c_0_17]),c_0_24]),c_0_25])]),c_0_15])).

fof(c_0_29,plain,(
    ! [X68] :
      ( ( ~ v2_struct_0(X68)
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ l3_lattices(X68) )
      & ( v4_lattices(X68)
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ l3_lattices(X68) )
      & ( v5_lattices(X68)
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ l3_lattices(X68) )
      & ( v6_lattices(X68)
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ l3_lattices(X68) )
      & ( v7_lattices(X68)
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ l3_lattices(X68) )
      & ( v8_lattices(X68)
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ l3_lattices(X68) )
      & ( v9_lattices(X68)
        | v2_struct_0(X68)
        | ~ v10_lattices(X68)
        | ~ l3_lattices(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_30,negated_conjecture,
    ( r4_lattice3(esk1_0,k15_lattice3(esk1_0,X1),X2)
    | r2_hidden(esk5_3(esk1_0,k15_lattice3(esk1_0,X1),X2),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_17])]),c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r3_lattices(esk1_0,k15_lattice3(esk1_0,X1),k15_lattice3(esk1_0,X2))
    | m1_subset_1(esk5_3(esk1_0,k15_lattice3(esk1_0,X2),X1),u1_struct_0(esk1_0))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_20]),c_0_20]),c_0_17])]),c_0_15])).

cnf(c_0_32,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r1_lattices(esk1_0,k15_lattice3(esk1_0,X1),k15_lattice3(esk1_0,X2))
    | r2_hidden(esk5_3(esk1_0,k15_lattice3(esk1_0,X2),X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_30]),c_0_20]),c_0_17]),c_0_24]),c_0_25])]),c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( r3_lattices(esk1_0,k15_lattice3(esk1_0,X1),k15_lattice3(esk1_0,X2))
    | m1_subset_1(esk5_3(esk1_0,k15_lattice3(esk1_0,X2),X1),u1_struct_0(esk1_0))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_35,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r3_lattices(esk1_0,k15_lattice3(esk1_0,X1),k15_lattice3(esk1_0,X2))
    | r2_hidden(esk5_3(esk1_0,k15_lattice3(esk1_0,X2),X1),X1)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_33]),c_0_20]),c_0_20]),c_0_17])]),c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( r3_lattices(esk1_0,k15_lattice3(esk1_0,X1),k15_lattice3(esk1_0,X2))
    | m1_subset_1(esk5_3(esk1_0,k15_lattice3(esk1_0,X2),X1),u1_struct_0(esk1_0))
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_38,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattices(esk1_0,k15_lattice3(esk1_0,X1),k15_lattice3(esk1_0,X2))
    | r2_hidden(esk5_3(esk1_0,k15_lattice3(esk1_0,X2),X1),X1)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( ~ r3_lattices(esk1_0,k15_lattice3(esk1_0,esk2_0),k15_lattice3(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( r3_lattices(esk1_0,k15_lattice3(esk1_0,X1),k15_lattice3(esk1_0,X2))
    | m1_subset_1(esk5_3(esk1_0,k15_lattice3(esk1_0,X2),X1),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( r3_lattices(esk1_0,k15_lattice3(esk1_0,X1),k15_lattice3(esk1_0,X2))
    | r2_hidden(esk5_3(esk1_0,k15_lattice3(esk1_0,X2),X1),X1)
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_1(X1),u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r3_lattices(esk1_0,k15_lattice3(esk1_0,X1),k15_lattice3(esk1_0,X2))
    | r2_hidden(esk5_3(esk1_0,k15_lattice3(esk1_0,X2),X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_38]),c_0_17]),c_0_25])]),c_0_15])).

fof(c_0_46,plain,(
    ! [X60,X61,X62] :
      ( ( r3_lattices(X60,X61,k15_lattice3(X60,X62))
        | ~ r2_hidden(X61,X62)
        | ~ m1_subset_1(X61,u1_struct_0(X60))
        | v2_struct_0(X60)
        | ~ v10_lattices(X60)
        | ~ v4_lattice3(X60)
        | ~ l3_lattices(X60) )
      & ( r3_lattices(X60,k16_lattice3(X60,X62),X61)
        | ~ r2_hidden(X61,X62)
        | ~ m1_subset_1(X61,u1_struct_0(X60))
        | v2_struct_0(X60)
        | ~ v10_lattices(X60)
        | ~ v4_lattice3(X60)
        | ~ l3_lattices(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),u1_struct_0(esk1_0))
    | ~ r2_hidden(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_1(X1),esk3_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),esk3_0)
    | ~ r2_hidden(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r3_lattices(esk1_0,esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),k15_lattice3(esk1_0,X1))
    | ~ r2_hidden(esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_17]),c_0_24]),c_0_25])]),c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_48])])).

cnf(c_0_55,negated_conjecture,
    ( r3_lattices(esk1_0,X1,esk4_1(X1))
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( r3_lattices(esk1_0,esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),k15_lattice3(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r3_lattices(esk1_0,esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)))
    | ~ r2_hidden(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattices(esk1_0,esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),k15_lattice3(esk1_0,esk3_0))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_20]),c_0_51]),c_0_17])]),c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( r3_lattices(esk1_0,esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_48])])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattices(esk1_0,esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),k15_lattice3(esk1_0,esk3_0))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_32]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( r1_lattices(esk1_0,esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_60]),c_0_44]),c_0_17])]),c_0_15]),c_0_51])])).

fof(c_0_63,plain,(
    ! [X51,X52,X53,X54] :
      ( v2_struct_0(X51)
      | ~ v5_lattices(X51)
      | ~ l2_lattices(X51)
      | ~ m1_subset_1(X52,u1_struct_0(X51))
      | ~ m1_subset_1(X53,u1_struct_0(X51))
      | ~ m1_subset_1(X54,u1_struct_0(X51))
      | ~ r1_lattices(X51,X52,X53)
      | ~ r1_lattices(X51,X53,X54)
      | r1_lattices(X51,X52,X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_lattices])])])])).

cnf(c_0_64,negated_conjecture,
    ( r1_lattices(esk1_0,esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),k15_lattice3(esk1_0,esk3_0))
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_35]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattices(esk1_0,esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_32]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,X2,X4)
    | ~ v5_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattices(esk1_0,esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)),k15_lattice3(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_38]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_68,negated_conjecture,
    ( r1_lattices(esk1_0,esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)))
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_35]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattices(esk1_0,X1,k15_lattice3(esk1_0,esk3_0))
    | ~ v5_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ r1_lattices(esk1_0,X1,esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_20]),c_0_51])]),c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattices(esk1_0,esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),esk4_1(esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_38]),c_0_17]),c_0_25])]),c_0_15])).

fof(c_0_71,plain,(
    ! [X30] :
      ( ( l1_lattices(X30)
        | ~ l3_lattices(X30) )
      & ( l2_lattices(X30)
        | ~ l3_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattices(esk1_0,esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),k15_lattice3(esk1_0,esk3_0))
    | ~ v5_lattices(esk1_0)
    | ~ l2_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_44])])).

cnf(c_0_73,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r1_lattices(esk1_0,esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),k15_lattice3(esk1_0,esk3_0))
    | ~ v5_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_17])])).

cnf(c_0_75,plain,
    ( v5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_76,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk5_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_77,negated_conjecture,
    ( r1_lattices(esk1_0,esk5_3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0),k15_lattice3(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_78,negated_conjecture,
    ( r4_lattice3(esk1_0,k15_lattice3(esk1_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_20]),c_0_17])]),c_0_15])).

cnf(c_0_79,negated_conjecture,
    ( r1_lattices(esk1_0,k15_lattice3(esk1_0,esk2_0),k15_lattice3(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_78]),c_0_20]),c_0_17]),c_0_24]),c_0_25])]),c_0_15])).

cnf(c_0_80,negated_conjecture,
    ( ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_79]),c_0_20]),c_0_20]),c_0_17])]),c_0_40]),c_0_15])).

cnf(c_0_81,negated_conjecture,
    ( ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_32]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_82,negated_conjecture,
    ( ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_35]),c_0_17]),c_0_25])]),c_0_15])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_38]),c_0_17]),c_0_25])]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
