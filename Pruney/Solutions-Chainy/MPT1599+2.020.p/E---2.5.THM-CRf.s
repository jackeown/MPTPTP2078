%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 757 expanded)
%              Number of clauses        :   40 ( 300 expanded)
%              Number of leaves         :   11 ( 200 expanded)
%              Depth                    :   13
%              Number of atoms          :  282 (2300 expanded)
%              Number of equality atoms :   23 ( 488 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   67 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v2_lattice3(k2_yellow_1(X1))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(dt_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(t23_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k12_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(t3_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v2_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_1])).

fof(c_0_12,plain,(
    ! [X15,X16,X17] :
      ( ~ v5_orders_2(X15)
      | ~ v2_lattice3(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | k12_lattice3(X15,X16,X17) = k11_lattice3(X15,X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_13,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v2_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X28] :
      ( v1_orders_2(k2_yellow_1(X28))
      & v3_orders_2(k2_yellow_1(X28))
      & v4_orders_2(k2_yellow_1(X28))
      & v5_orders_2(k2_yellow_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_15,plain,(
    ! [X30] :
      ( u1_struct_0(k2_yellow_1(X30)) = X30
      & u1_orders_2(k2_yellow_1(X30)) = k1_yellow_1(X30) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_16,plain,(
    ! [X27] :
      ( v1_orders_2(k2_yellow_1(X27))
      & l1_orders_2(k2_yellow_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_17,plain,(
    ! [X12,X13,X14] :
      ( ~ v5_orders_2(X12)
      | ~ v2_lattice3(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | m1_subset_1(k12_lattice3(X12,X13,X14),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).

cnf(c_0_18,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),X1,X2) = k11_lattice3(k2_yellow_1(esk2_0),X1,X2)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_21]),c_0_22])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k12_lattice3(k2_yellow_1(esk2_0),X1,X2),esk2_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_21]),c_0_20]),c_0_21]),c_0_21]),c_0_22])])).

fof(c_0_29,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( r1_orders_2(X21,X24,X22)
        | X24 != k12_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,X24,X23)
        | X24 != k12_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X21))
        | ~ r1_orders_2(X21,X25,X22)
        | ~ r1_orders_2(X21,X25,X23)
        | r1_orders_2(X21,X25,X24)
        | X24 != k12_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk1_4(X21,X22,X23,X24),u1_struct_0(X21))
        | ~ r1_orders_2(X21,X24,X22)
        | ~ r1_orders_2(X21,X24,X23)
        | X24 = k12_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,esk1_4(X21,X22,X23,X24),X22)
        | ~ r1_orders_2(X21,X24,X22)
        | ~ r1_orders_2(X21,X24,X23)
        | X24 = k12_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,esk1_4(X21,X22,X23,X24),X23)
        | ~ r1_orders_2(X21,X24,X22)
        | ~ r1_orders_2(X21,X24,X23)
        | X24 = k12_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ r1_orders_2(X21,esk1_4(X21,X22,X23,X24),X24)
        | ~ r1_orders_2(X21,X24,X22)
        | ~ r1_orders_2(X21,X24,X23)
        | X24 = k12_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_yellow_0])])])])])).

cnf(c_0_30,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),esk3_0,X1) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k12_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

fof(c_0_33,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r3_orders_2(X9,X10,X11)
        | r1_orders_2(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ l1_orders_2(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) )
      & ( ~ r1_orders_2(X9,X10,X11)
        | r3_orders_2(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ l1_orders_2(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k12_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k12_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) = k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k12_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_37,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),X1,esk4_0)
    | X1 != k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19]),c_0_20]),c_0_21]),c_0_26]),c_0_21]),c_0_31]),c_0_21]),c_0_22])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_41,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k12_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_42,plain,(
    ! [X31,X32,X33] :
      ( ( ~ r3_orders_2(k2_yellow_1(X31),X32,X33)
        | r1_tarski(X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))
        | v1_xboole_0(X31) )
      & ( ~ r1_tarski(X32,X33)
        | r3_orders_2(k2_yellow_1(X31),X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))
        | v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

fof(c_0_43,plain,(
    ! [X29] :
      ( ( ~ v2_struct_0(k2_yellow_1(X29))
        | v1_xboole_0(X29) )
      & ( v1_orders_2(k2_yellow_1(X29))
        | v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_44,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_22]),c_0_21]),c_0_21]),c_0_38])])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),X1,esk3_0)
    | X1 != k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_19]),c_0_20]),c_0_21]),c_0_31]),c_0_21]),c_0_26]),c_0_21]),c_0_22])])).

cnf(c_0_47,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_31]),c_0_40])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_40])])).

fof(c_0_52,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X8)
      | r1_tarski(X6,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_21]),c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_51]),c_0_26]),c_0_40])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_31]),c_0_40])]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_55]),c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(X1,esk4_0))
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_58]),c_0_26]),c_0_40])]),c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.19/0.39  # and selection function SelectNegativeLiterals.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 0.19/0.39  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.19/0.39  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.19/0.39  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.19/0.39  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.19/0.39  fof(dt_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 0.19/0.39  fof(t23_yellow_0, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k12_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_0)).
% 0.19/0.39  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.19/0.39  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.19/0.39  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.19/0.39  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.19/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 0.19/0.39  fof(c_0_12, plain, ![X15, X16, X17]:(~v5_orders_2(X15)|~v2_lattice3(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|k12_lattice3(X15,X16,X17)=k11_lattice3(X15,X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.19/0.39  fof(c_0_13, negated_conjecture, (~v1_xboole_0(esk2_0)&(v2_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.19/0.39  fof(c_0_14, plain, ![X28]:(((v1_orders_2(k2_yellow_1(X28))&v3_orders_2(k2_yellow_1(X28)))&v4_orders_2(k2_yellow_1(X28)))&v5_orders_2(k2_yellow_1(X28))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.19/0.39  fof(c_0_15, plain, ![X30]:(u1_struct_0(k2_yellow_1(X30))=X30&u1_orders_2(k2_yellow_1(X30))=k1_yellow_1(X30)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.19/0.39  fof(c_0_16, plain, ![X27]:(v1_orders_2(k2_yellow_1(X27))&l1_orders_2(k2_yellow_1(X27))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.19/0.39  fof(c_0_17, plain, ![X12, X13, X14]:(~v5_orders_2(X12)|~v2_lattice3(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))|m1_subset_1(k12_lattice3(X12,X13,X14),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).
% 0.19/0.39  cnf(c_0_18, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (v2_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_20, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_21, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_22, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_24, plain, (m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),X1,X2)=k11_lattice3(k2_yellow_1(esk2_0),X1,X2)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_21]), c_0_22])])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_23, c_0_21])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (m1_subset_1(k12_lattice3(k2_yellow_1(esk2_0),X1,X2),esk2_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_21]), c_0_20]), c_0_21]), c_0_21]), c_0_22])])).
% 0.19/0.39  fof(c_0_29, plain, ![X21, X22, X23, X24, X25]:((((r1_orders_2(X21,X24,X22)|X24!=k12_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21)))&(r1_orders_2(X21,X24,X23)|X24!=k12_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21))))&(~m1_subset_1(X25,u1_struct_0(X21))|(~r1_orders_2(X21,X25,X22)|~r1_orders_2(X21,X25,X23)|r1_orders_2(X21,X25,X24))|X24!=k12_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21))))&((m1_subset_1(esk1_4(X21,X22,X23,X24),u1_struct_0(X21))|(~r1_orders_2(X21,X24,X22)|~r1_orders_2(X21,X24,X23))|X24=k12_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21)))&(((r1_orders_2(X21,esk1_4(X21,X22,X23,X24),X22)|(~r1_orders_2(X21,X24,X22)|~r1_orders_2(X21,X24,X23))|X24=k12_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21)))&(r1_orders_2(X21,esk1_4(X21,X22,X23,X24),X23)|(~r1_orders_2(X21,X24,X22)|~r1_orders_2(X21,X24,X23))|X24=k12_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21))))&(~r1_orders_2(X21,esk1_4(X21,X22,X23,X24),X24)|(~r1_orders_2(X21,X24,X22)|~r1_orders_2(X21,X24,X23))|X24=k12_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_yellow_0])])])])])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_27, c_0_21])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (m1_subset_1(k12_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),esk2_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_26])).
% 0.19/0.39  fof(c_0_33, plain, ![X9, X10, X11]:((~r3_orders_2(X9,X10,X11)|r1_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))&(~r1_orders_2(X9,X10,X11)|r3_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.19/0.39  cnf(c_0_34, plain, (r1_orders_2(X1,X2,X3)|X2!=k12_lattice3(X1,X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (k12_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (m1_subset_1(k12_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.19/0.39  cnf(c_0_37, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_38, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),X1,esk4_0)|X1!=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_19]), c_0_20]), c_0_21]), c_0_26]), c_0_21]), c_0_31]), c_0_21]), c_0_22])])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0)), inference(rw,[status(thm)],[c_0_36, c_0_35])).
% 0.19/0.39  cnf(c_0_41, plain, (r1_orders_2(X1,X2,X3)|X2!=k12_lattice3(X1,X3,X4)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  fof(c_0_42, plain, ![X31, X32, X33]:((~r3_orders_2(k2_yellow_1(X31),X32,X33)|r1_tarski(X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))&(~r1_tarski(X32,X33)|r3_orders_2(k2_yellow_1(X31),X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.19/0.39  fof(c_0_43, plain, ![X29]:((~v2_struct_0(k2_yellow_1(X29))|v1_xboole_0(X29))&(v1_orders_2(k2_yellow_1(X29))|v1_xboole_0(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.19/0.39  cnf(c_0_44, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_22]), c_0_21]), c_0_21]), c_0_38])])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_40])])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),X1,esk3_0)|X1!=k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_19]), c_0_20]), c_0_21]), c_0_31]), c_0_21]), c_0_26]), c_0_21]), c_0_22])])).
% 0.19/0.39  cnf(c_0_47, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_48, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)|v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_31]), c_0_40])])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_46]), c_0_40])])).
% 0.19/0.39  fof(c_0_52, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X6,X8)|r1_tarski(X6,k3_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.19/0.39  cnf(c_0_53, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_21]), c_0_21])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)|v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_51]), c_0_26]), c_0_40])])).
% 0.19/0.39  cnf(c_0_56, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_31]), c_0_40])]), c_0_50])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_55]), c_0_50])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(X1,esk4_0))|~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_58]), c_0_26]), c_0_40])]), c_0_50])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 63
% 0.19/0.39  # Proof object clause steps            : 40
% 0.19/0.39  # Proof object formula steps           : 23
% 0.19/0.39  # Proof object conjectures             : 29
% 0.19/0.39  # Proof object clause conjectures      : 26
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 17
% 0.19/0.39  # Proof object initial formulas used   : 11
% 0.19/0.39  # Proof object generating inferences   : 19
% 0.19/0.39  # Proof object simplifying inferences  : 59
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 12
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 30
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 29
% 0.19/0.39  # Processed clauses                    : 188
% 0.19/0.39  # ...of these trivial                  : 13
% 0.19/0.39  # ...subsumed                          : 3
% 0.19/0.39  # ...remaining for further processing  : 172
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 10
% 0.19/0.39  # Generated clauses                    : 794
% 0.19/0.39  # ...of the previous two non-trivial   : 780
% 0.19/0.39  # Contextual simplify-reflections      : 3
% 0.19/0.39  # Paramodulations                      : 787
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 7
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 135
% 0.19/0.39  #    Positive orientable unit clauses  : 76
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 2
% 0.19/0.39  #    Non-unit-clauses                  : 57
% 0.19/0.39  # Current number of unprocessed clauses: 599
% 0.19/0.39  # ...number of literals in the above   : 974
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 38
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 643
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 170
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.19/0.39  # Unit Clause-clause subsumption calls : 81
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 184
% 0.19/0.39  # BW rewrite match successes           : 9
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 22956
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.044 s
% 0.19/0.39  # System time              : 0.005 s
% 0.19/0.39  # Total time               : 0.049 s
% 0.19/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
