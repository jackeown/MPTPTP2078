%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:41 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   68 (1229 expanded)
%              Number of clauses        :   43 ( 474 expanded)
%              Number of leaves         :   12 ( 354 expanded)
%              Depth                    :   12
%              Number of atoms          :  271 (3318 expanded)
%              Number of equality atoms :   13 ( 253 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_yellow_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
         => ( r3_orders_2(k3_yellow_1(X1),X2,X3)
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(d4_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => k5_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattice3)).

fof(fc2_lattice3,axiom,(
    ! [X1] :
      ( v3_lattices(k1_lattice3(X1))
      & v10_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).

fof(dt_k1_lattice3,axiom,(
    ! [X1] :
      ( v3_lattices(k1_lattice3(X1))
      & l3_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(fc1_lattice3,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k1_lattice3(X1))
      & v3_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

fof(dt_k5_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
     => m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattice3)).

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

fof(d3_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

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

fof(t7_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_lattices(X1,X2,X3)
              <=> r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).

fof(t2_lattice3,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))
         => ( r1_lattices(k1_lattice3(X1),X2,X3)
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_lattice3)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
           => ( r3_orders_2(k3_yellow_1(X1),X2,X3)
            <=> r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t2_yellow_1])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0)))
    & ( ~ r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk3_0) )
    & ( r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)
      | r1_tarski(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X23] : k3_yellow_1(X23) = k3_lattice3(k1_lattice3(X23)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( v2_struct_0(X10)
      | ~ v10_lattices(X10)
      | ~ l3_lattices(X10)
      | ~ m1_subset_1(X11,u1_struct_0(k3_lattice3(X10)))
      | k5_lattice3(X10,X11) = X11 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_lattice3])])])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X16] :
      ( v3_lattices(k1_lattice3(X16))
      & v10_lattices(k1_lattice3(X16)) ) ),
    inference(variable_rename,[status(thm)],[fc2_lattice3])).

fof(c_0_19,plain,(
    ! [X12] :
      ( v3_lattices(k1_lattice3(X12))
      & l3_lattices(k1_lattice3(X12)) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_lattice3])).

fof(c_0_20,plain,(
    ! [X15] :
      ( ~ v2_struct_0(k1_lattice3(X15))
      & v3_lattices(k1_lattice3(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_lattice3])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v10_lattices(X13)
      | ~ l3_lattices(X13)
      | ~ m1_subset_1(X14,u1_struct_0(k3_lattice3(X13)))
      | m1_subset_1(k5_lattice3(X13,X14),u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattice3])])])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | k5_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( v10_lattices(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( l3_lattices(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( ~ v2_struct_0(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_17])).

fof(c_0_29,plain,(
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

fof(c_0_30,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v10_lattices(X8)
      | ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | k4_lattice3(X8,X9) = X9 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k5_lattice3(k1_lattice3(esk1_0),esk2_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k5_lattice3(k1_lattice3(esk1_0),esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_28]),c_0_25]),c_0_26])]),c_0_27])).

fof(c_0_34,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r3_lattices(X5,X6,X7)
        | r1_lattices(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v6_lattices(X5)
        | ~ v8_lattices(X5)
        | ~ v9_lattices(X5)
        | ~ l3_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) )
      & ( ~ r1_lattices(X5,X6,X7)
        | r3_lattices(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v6_lattices(X5)
        | ~ v8_lattices(X5)
        | ~ v9_lattices(X5)
        | ~ l3_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_35,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r3_lattices(X20,X21,X22)
        | r3_orders_2(k3_lattice3(X20),k4_lattice3(X20,X21),k4_lattice3(X20,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( ~ r3_orders_2(k3_lattice3(X20),k4_lattice3(X20,X21),k4_lattice3(X20,X22))
        | r3_lattices(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_lattice3])])])])])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | k4_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_32]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_33]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_42,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( v9_lattices(k1_lattice3(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_44,plain,
    ( v8_lattices(k1_lattice3(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_45,plain,
    ( v6_lattices(k1_lattice3(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_46,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( k4_lattice3(k1_lattice3(esk1_0),esk2_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_48,plain,
    ( r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k4_lattice3(k1_lattice3(esk1_0),esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_41]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_50,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_51,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r1_lattices(k1_lattice3(X17),X18,X19)
        | r1_tarski(X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(k1_lattice3(X17)))
        | ~ m1_subset_1(X18,u1_struct_0(k1_lattice3(X17))) )
      & ( ~ r1_tarski(X18,X19)
        | r1_lattices(k1_lattice3(X17),X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(k1_lattice3(X17)))
        | ~ m1_subset_1(X18,u1_struct_0(k1_lattice3(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_lattice3])])])])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_43]),c_0_44]),c_0_45]),c_0_26])]),c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( r3_lattices(k1_lattice3(esk1_0),esk2_0,X1)
    | ~ r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,k4_lattice3(k1_lattice3(esk1_0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_40]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)
    | r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),k4_lattice3(k1_lattice3(esk1_0),X1),esk3_0)
    | ~ r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_41]),c_0_49]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_41]),c_0_43]),c_0_44]),c_0_45]),c_0_26])]),c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( ~ r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,plain,
    ( r1_tarski(X2,X3)
    | ~ r1_lattices(k1_lattice3(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)
    | ~ r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_40]),c_0_49]),c_0_41])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),k4_lattice3(k1_lattice3(esk1_0),X1),esk3_0)
    | ~ r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( r1_lattices(k1_lattice3(X3),X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0)
    | ~ r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_17])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_41]),c_0_40])]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),k4_lattice3(k1_lattice3(esk1_0),X1),esk3_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_41])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_47]),c_0_64]),c_0_40])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.024 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t2_yellow_1, conjecture, ![X1, X2]:(m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))=>(r3_orders_2(k3_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow_1)).
% 0.13/0.38  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.13/0.38  fof(d4_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))=>k5_lattice3(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_lattice3)).
% 0.13/0.38  fof(fc2_lattice3, axiom, ![X1]:(v3_lattices(k1_lattice3(X1))&v10_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_lattice3)).
% 0.13/0.38  fof(dt_k1_lattice3, axiom, ![X1]:(v3_lattices(k1_lattice3(X1))&l3_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 0.13/0.38  fof(fc1_lattice3, axiom, ![X1]:(~(v2_struct_0(k1_lattice3(X1)))&v3_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_lattice3)).
% 0.13/0.38  fof(dt_k5_lattice3, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))))=>m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattice3)).
% 0.13/0.38  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.13/0.38  fof(d3_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattice3(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattice3)).
% 0.13/0.38  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.13/0.38  fof(t7_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)<=>r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_lattice3)).
% 0.13/0.38  fof(t2_lattice3, axiom, ![X1, X2]:(m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))=>(r1_lattices(k1_lattice3(X1),X2,X3)<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_lattice3)).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))=>(r3_orders_2(k3_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t2_yellow_1])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))&(m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0)))&((~r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)|~r1_tarski(esk2_0,esk3_0))&(r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)|r1_tarski(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X23]:k3_yellow_1(X23)=k3_lattice3(k1_lattice3(X23)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.13/0.38  fof(c_0_15, plain, ![X10, X11]:(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10)|(~m1_subset_1(X11,u1_struct_0(k3_lattice3(X10)))|k5_lattice3(X10,X11)=X11)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_lattice3])])])])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_18, plain, ![X16]:(v3_lattices(k1_lattice3(X16))&v10_lattices(k1_lattice3(X16))), inference(variable_rename,[status(thm)],[fc2_lattice3])).
% 0.13/0.38  fof(c_0_19, plain, ![X12]:(v3_lattices(k1_lattice3(X12))&l3_lattices(k1_lattice3(X12))), inference(variable_rename,[status(thm)],[dt_k1_lattice3])).
% 0.13/0.38  fof(c_0_20, plain, ![X15]:(~v2_struct_0(k1_lattice3(X15))&v3_lattices(k1_lattice3(X15))), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_lattice3])])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_22, plain, ![X13, X14]:(v2_struct_0(X13)|~v10_lattices(X13)|~l3_lattices(X13)|~m1_subset_1(X14,u1_struct_0(k3_lattice3(X13)))|m1_subset_1(k5_lattice3(X13,X14),u1_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattice3])])])).
% 0.13/0.38  cnf(c_0_23, plain, (v2_struct_0(X1)|k5_lattice3(X1,X2)=X2|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0))))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.38  cnf(c_0_25, plain, (v10_lattices(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_26, plain, (l3_lattices(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_27, plain, (~v2_struct_0(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0))))), inference(rw,[status(thm)],[c_0_21, c_0_17])).
% 0.13/0.38  fof(c_0_29, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.13/0.38  fof(c_0_30, plain, ![X8, X9]:(v2_struct_0(X8)|~v10_lattices(X8)|~l3_lattices(X8)|(~m1_subset_1(X9,u1_struct_0(X8))|k4_lattice3(X8,X9)=X9)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).
% 0.13/0.38  cnf(c_0_31, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (k5_lattice3(k1_lattice3(esk1_0),esk2_0)=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (k5_lattice3(k1_lattice3(esk1_0),esk3_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_28]), c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  fof(c_0_34, plain, ![X5, X6, X7]:((~r3_lattices(X5,X6,X7)|r1_lattices(X5,X6,X7)|(v2_struct_0(X5)|~v6_lattices(X5)|~v8_lattices(X5)|~v9_lattices(X5)|~l3_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))&(~r1_lattices(X5,X6,X7)|r3_lattices(X5,X6,X7)|(v2_struct_0(X5)|~v6_lattices(X5)|~v8_lattices(X5)|~v9_lattices(X5)|~l3_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.13/0.38  cnf(c_0_35, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_36, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_37, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  fof(c_0_38, plain, ![X20, X21, X22]:((~r3_lattices(X20,X21,X22)|r3_orders_2(k3_lattice3(X20),k4_lattice3(X20,X21),k4_lattice3(X20,X22))|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v10_lattices(X20)|~l3_lattices(X20)))&(~r3_orders_2(k3_lattice3(X20),k4_lattice3(X20,X21),k4_lattice3(X20,X22))|r3_lattices(X20,X21,X22)|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v10_lattices(X20)|~l3_lattices(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_lattice3])])])])])).
% 0.13/0.38  cnf(c_0_39, plain, (v2_struct_0(X1)|k4_lattice3(X1,X2)=X2|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_32]), c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_33]), c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_42, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_43, plain, (v9_lattices(k1_lattice3(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_44, plain, (v8_lattices(k1_lattice3(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_45, plain, (v6_lattices(k1_lattice3(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_46, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (k4_lattice3(k1_lattice3(esk1_0),esk2_0)=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_48, plain, (r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k4_lattice3(k1_lattice3(esk1_0),esk3_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_41]), c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_50, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  fof(c_0_51, plain, ![X17, X18, X19]:((~r1_lattices(k1_lattice3(X17),X18,X19)|r1_tarski(X18,X19)|~m1_subset_1(X19,u1_struct_0(k1_lattice3(X17)))|~m1_subset_1(X18,u1_struct_0(k1_lattice3(X17))))&(~r1_tarski(X18,X19)|r1_lattices(k1_lattice3(X17),X18,X19)|~m1_subset_1(X19,u1_struct_0(k1_lattice3(X17)))|~m1_subset_1(X18,u1_struct_0(k1_lattice3(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_lattice3])])])])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_43]), c_0_44]), c_0_45]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (r3_lattices(k1_lattice3(esk1_0),esk2_0,X1)|~r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,k4_lattice3(k1_lattice3(esk1_0),X1))|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_40]), c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)|r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),k4_lattice3(k1_lattice3(esk1_0),X1),esk3_0)|~r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_41]), c_0_49]), c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_41]), c_0_43]), c_0_44]), c_0_45]), c_0_26])]), c_0_27])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (~r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)|~r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_58, plain, (r1_tarski(X2,X3)|~r1_lattices(k1_lattice3(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))|~m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)|~r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_40]), c_0_49]), c_0_41])])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r1_tarski(esk2_0,esk3_0)|r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_54, c_0_17])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),k4_lattice3(k1_lattice3(esk1_0),X1),esk3_0)|~r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.38  cnf(c_0_62, plain, (r1_lattices(k1_lattice3(X3),X1,X2)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k1_lattice3(X3)))|~m1_subset_1(X1,u1_struct_0(k1_lattice3(X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)|~r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_57, c_0_17])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_41]), c_0_40])]), c_0_60])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),k4_lattice3(k1_lattice3(esk1_0),X1),esk3_0)|~r1_tarski(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_41])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (~r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_47]), c_0_64]), c_0_40])]), c_0_66]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 68
% 0.13/0.38  # Proof object clause steps            : 43
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 27
% 0.13/0.38  # Proof object clause conjectures      : 24
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 20
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 18
% 0.13/0.38  # Proof object simplifying inferences  : 77
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 27
% 0.13/0.38  # Removed in clause preprocessing      : 2
% 0.13/0.38  # Initial clauses in saturation        : 25
% 0.13/0.38  # Processed clauses                    : 90
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 3
% 0.13/0.38  # ...remaining for further processing  : 85
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 65
% 0.13/0.38  # ...of the previous two non-trivial   : 50
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 65
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
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
% 0.13/0.38  # Current number of processed clauses  : 60
% 0.13/0.38  #    Positive orientable unit clauses  : 18
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 40
% 0.13/0.38  # Current number of unprocessed clauses: 7
% 0.13/0.38  # ...number of literals in the above   : 47
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 26
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 243
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 85
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 19
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4545
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.028 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.032 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
