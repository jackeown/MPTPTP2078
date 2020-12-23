%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:42 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 562 expanded)
%              Number of clauses        :   44 ( 220 expanded)
%              Number of leaves         :   12 ( 150 expanded)
%              Depth                    :   13
%              Number of atoms          :  306 (1755 expanded)
%              Number of equality atoms :   29 ( 358 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   67 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_lattice3(k2_yellow_1(X1))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
               => r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).

fof(commutativity_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k13_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k13_lattice3)).

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

fof(dt_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k13_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_lattice3)).

fof(t22_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k13_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).

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

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

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

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v1_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_yellow_1])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( ~ v5_orders_2(X12)
      | ~ v1_lattice3(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | k13_lattice3(X12,X13,X14) = k13_lattice3(X12,X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k13_lattice3])])).

fof(c_0_14,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v1_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X28] :
      ( v1_orders_2(k2_yellow_1(X28))
      & v3_orders_2(k2_yellow_1(X28))
      & v4_orders_2(k2_yellow_1(X28))
      & v5_orders_2(k2_yellow_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_16,plain,(
    ! [X30] :
      ( u1_struct_0(k2_yellow_1(X30)) = X30
      & u1_orders_2(k2_yellow_1(X30)) = k1_yellow_1(X30) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_17,plain,(
    ! [X27] :
      ( v1_orders_2(k2_yellow_1(X27))
      & l1_orders_2(k2_yellow_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

cnf(c_0_18,plain,
    ( k13_lattice3(X1,X2,X3) = k13_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X15,X16,X17] :
      ( ~ v5_orders_2(X15)
      | ~ v1_lattice3(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | m1_subset_1(k13_lattice3(X15,X16,X17),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k13_lattice3])])).

cnf(c_0_25,negated_conjecture,
    ( k13_lattice3(k2_yellow_1(esk2_0),X1,X2) = k13_lattice3(k2_yellow_1(esk2_0),X2,X1)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_21]),c_0_22])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( m1_subset_1(k13_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( r1_orders_2(X21,X22,X24)
        | X24 != k13_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,X23,X24)
        | X24 != k13_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X21))
        | ~ r1_orders_2(X21,X22,X25)
        | ~ r1_orders_2(X21,X23,X25)
        | r1_orders_2(X21,X24,X25)
        | X24 != k13_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk1_4(X21,X22,X23,X24),u1_struct_0(X21))
        | ~ r1_orders_2(X21,X22,X24)
        | ~ r1_orders_2(X21,X23,X24)
        | X24 = k13_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,X22,esk1_4(X21,X22,X23,X24))
        | ~ r1_orders_2(X21,X22,X24)
        | ~ r1_orders_2(X21,X23,X24)
        | X24 = k13_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,X23,esk1_4(X21,X22,X23,X24))
        | ~ r1_orders_2(X21,X22,X24)
        | ~ r1_orders_2(X21,X23,X24)
        | X24 = k13_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ r1_orders_2(X21,X24,esk1_4(X21,X22,X23,X24))
        | ~ r1_orders_2(X21,X22,X24)
        | ~ r1_orders_2(X21,X23,X24)
        | X24 = k13_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_yellow_0])])])])])).

cnf(c_0_30,negated_conjecture,
    ( k13_lattice3(k2_yellow_1(esk2_0),esk4_0,X1) = k13_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),X1,X2),esk2_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_21]),c_0_20]),c_0_21]),c_0_21]),c_0_22])])).

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
    | X3 != k13_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k13_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0) = k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),esk3_0,X1)
    | X1 != k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19]),c_0_20]),c_0_21]),c_0_26]),c_0_21]),c_0_21]),c_0_31]),c_0_22])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_41,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k13_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_42,plain,(
    ! [X18,X19,X20] :
      ( ~ v5_orders_2(X18)
      | ~ v1_lattice3(X18)
      | ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | k13_lattice3(X18,X19,X20) = k10_lattice3(X18,X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

fof(c_0_43,plain,(
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

fof(c_0_44,plain,(
    ! [X29] :
      ( ( ~ v2_struct_0(k2_yellow_1(X29))
        | v1_xboole_0(X29) )
      & ( v1_orders_2(k2_yellow_1(X29))
        | v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_45,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_22]),c_0_21]),c_0_21]),c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),esk4_0,X1)
    | X1 != k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_19]),c_0_20]),c_0_21]),c_0_31]),c_0_21]),c_0_21]),c_0_26]),c_0_22])])).

cnf(c_0_48,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_40]),c_0_31])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_40])])).

cnf(c_0_54,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(esk2_0),X1,X2) = k13_lattice3(k2_yellow_1(esk2_0),X1,X2)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_19]),c_0_20]),c_0_21]),c_0_21]),c_0_22])])).

fof(c_0_55,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X8,X7)
      | r1_tarski(k2_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_21]),c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_53]),c_0_40]),c_0_26])])).

cnf(c_0_59,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(esk2_0),esk3_0,X1) = k13_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_31])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_40]),c_0_31])]),c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_58]),c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) = k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_26])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,X1),k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | ~ r1_tarski(X1,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_62]),c_0_40]),c_0_26])]),c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.19/0.38  # and selection function SelectNegativeLiterals.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t6_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v1_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_1)).
% 0.19/0.38  fof(commutativity_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k13_lattice3(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k13_lattice3)).
% 0.19/0.38  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.19/0.38  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.19/0.38  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.19/0.38  fof(dt_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k13_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 0.19/0.38  fof(t22_yellow_0, axiom, ![X1]:(((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k13_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_yellow_0)).
% 0.19/0.38  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.19/0.38  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.19/0.38  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.19/0.38  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.19/0.38  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.19/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v1_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3))))))), inference(assume_negation,[status(cth)],[t6_yellow_1])).
% 0.19/0.38  fof(c_0_13, plain, ![X12, X13, X14]:(~v5_orders_2(X12)|~v1_lattice3(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))|k13_lattice3(X12,X13,X14)=k13_lattice3(X12,X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k13_lattice3])])).
% 0.19/0.38  fof(c_0_14, negated_conjecture, (~v1_xboole_0(esk2_0)&(v1_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.19/0.38  fof(c_0_15, plain, ![X28]:(((v1_orders_2(k2_yellow_1(X28))&v3_orders_2(k2_yellow_1(X28)))&v4_orders_2(k2_yellow_1(X28)))&v5_orders_2(k2_yellow_1(X28))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.19/0.38  fof(c_0_16, plain, ![X30]:(u1_struct_0(k2_yellow_1(X30))=X30&u1_orders_2(k2_yellow_1(X30))=k1_yellow_1(X30)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.19/0.38  fof(c_0_17, plain, ![X27]:(v1_orders_2(k2_yellow_1(X27))&l1_orders_2(k2_yellow_1(X27))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.19/0.38  cnf(c_0_18, plain, (k13_lattice3(X1,X2,X3)=k13_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (v1_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_20, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_21, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_22, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  fof(c_0_24, plain, ![X15, X16, X17]:(~v5_orders_2(X15)|~v1_lattice3(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|m1_subset_1(k13_lattice3(X15,X16,X17),u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k13_lattice3])])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (k13_lattice3(k2_yellow_1(esk2_0),X1,X2)=k13_lattice3(k2_yellow_1(esk2_0),X2,X1)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_21]), c_0_22])])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_23, c_0_21])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_28, plain, (m1_subset_1(k13_lattice3(X1,X2,X3),u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  fof(c_0_29, plain, ![X21, X22, X23, X24, X25]:((((r1_orders_2(X21,X22,X24)|X24!=k13_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v1_lattice3(X21)|~l1_orders_2(X21)))&(r1_orders_2(X21,X23,X24)|X24!=k13_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v1_lattice3(X21)|~l1_orders_2(X21))))&(~m1_subset_1(X25,u1_struct_0(X21))|(~r1_orders_2(X21,X22,X25)|~r1_orders_2(X21,X23,X25)|r1_orders_2(X21,X24,X25))|X24!=k13_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v1_lattice3(X21)|~l1_orders_2(X21))))&((m1_subset_1(esk1_4(X21,X22,X23,X24),u1_struct_0(X21))|(~r1_orders_2(X21,X22,X24)|~r1_orders_2(X21,X23,X24))|X24=k13_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v1_lattice3(X21)|~l1_orders_2(X21)))&(((r1_orders_2(X21,X22,esk1_4(X21,X22,X23,X24))|(~r1_orders_2(X21,X22,X24)|~r1_orders_2(X21,X23,X24))|X24=k13_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v1_lattice3(X21)|~l1_orders_2(X21)))&(r1_orders_2(X21,X23,esk1_4(X21,X22,X23,X24))|(~r1_orders_2(X21,X22,X24)|~r1_orders_2(X21,X23,X24))|X24=k13_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v1_lattice3(X21)|~l1_orders_2(X21))))&(~r1_orders_2(X21,X24,esk1_4(X21,X22,X23,X24))|(~r1_orders_2(X21,X22,X24)|~r1_orders_2(X21,X23,X24))|X24=k13_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~v1_lattice3(X21)|~l1_orders_2(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_yellow_0])])])])])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (k13_lattice3(k2_yellow_1(esk2_0),esk4_0,X1)=k13_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_27, c_0_21])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),X1,X2),esk2_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_19]), c_0_21]), c_0_20]), c_0_21]), c_0_21]), c_0_22])])).
% 0.19/0.38  fof(c_0_33, plain, ![X9, X10, X11]:((~r3_orders_2(X9,X10,X11)|r1_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))&(~r1_orders_2(X9,X10,X11)|r3_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.19/0.38  cnf(c_0_34, plain, (r1_orders_2(X1,X2,X3)|X3!=k13_lattice3(X1,X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (k13_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0)=k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),esk2_0)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.19/0.38  cnf(c_0_37, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_38, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),esk3_0,X1)|X1!=k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_19]), c_0_20]), c_0_21]), c_0_26]), c_0_21]), c_0_21]), c_0_31]), c_0_22])])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 0.19/0.38  cnf(c_0_41, plain, (r1_orders_2(X1,X2,X3)|X3!=k13_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  fof(c_0_42, plain, ![X18, X19, X20]:(~v5_orders_2(X18)|~v1_lattice3(X18)|~l1_orders_2(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|k13_lattice3(X18,X19,X20)=k10_lattice3(X18,X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.19/0.38  fof(c_0_43, plain, ![X31, X32, X33]:((~r3_orders_2(k2_yellow_1(X31),X32,X33)|r1_tarski(X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))&(~r1_tarski(X32,X33)|r3_orders_2(k2_yellow_1(X31),X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.19/0.38  fof(c_0_44, plain, ![X29]:((~v2_struct_0(k2_yellow_1(X29))|v1_xboole_0(X29))&(v1_orders_2(k2_yellow_1(X29))|v1_xboole_0(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.19/0.38  cnf(c_0_45, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_22]), c_0_21]), c_0_21]), c_0_38])])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_40])])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),esk4_0,X1)|X1!=k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_19]), c_0_20]), c_0_21]), c_0_31]), c_0_21]), c_0_21]), c_0_26]), c_0_22])])).
% 0.19/0.38  cnf(c_0_48, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_49, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_50, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_40]), c_0_31])])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_40])])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (k10_lattice3(k2_yellow_1(esk2_0),X1,X2)=k13_lattice3(k2_yellow_1(esk2_0),X1,X2)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_19]), c_0_20]), c_0_21]), c_0_21]), c_0_22])])).
% 0.19/0.38  fof(c_0_55, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X8,X7)|r1_tarski(k2_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.19/0.38  cnf(c_0_56, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_21]), c_0_21])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_53]), c_0_40]), c_0_26])])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (k10_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)=k13_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_54, c_0_31])).
% 0.19/0.38  cnf(c_0_60, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (r1_tarski(esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_40]), c_0_31])]), c_0_52])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_58]), c_0_52])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)=k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_26])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,X1),k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|~r1_tarski(X1,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (r1_tarski(esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_62]), c_0_40]), c_0_26])]), c_0_52])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 69
% 0.19/0.38  # Proof object clause steps            : 44
% 0.19/0.38  # Proof object formula steps           : 25
% 0.19/0.38  # Proof object conjectures             : 32
% 0.19/0.38  # Proof object clause conjectures      : 29
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 18
% 0.19/0.38  # Proof object initial formulas used   : 12
% 0.19/0.38  # Proof object generating inferences   : 22
% 0.19/0.38  # Proof object simplifying inferences  : 64
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 12
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 30
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 29
% 0.19/0.38  # Processed clauses                    : 138
% 0.19/0.38  # ...of these trivial                  : 13
% 0.19/0.38  # ...subsumed                          : 2
% 0.19/0.38  # ...remaining for further processing  : 123
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 5
% 0.19/0.38  # Generated clauses                    : 467
% 0.19/0.38  # ...of the previous two non-trivial   : 447
% 0.19/0.38  # Contextual simplify-reflections      : 3
% 0.19/0.38  # Paramodulations                      : 462
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 5
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 91
% 0.19/0.38  #    Positive orientable unit clauses  : 43
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 46
% 0.19/0.38  # Current number of unprocessed clauses: 359
% 0.19/0.38  # ...number of literals in the above   : 543
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 33
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 599
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 176
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.19/0.38  # Unit Clause-clause subsumption calls : 74
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 90
% 0.19/0.38  # BW rewrite match successes           : 5
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 14466
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.037 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
