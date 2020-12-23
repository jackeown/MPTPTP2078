%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 200 expanded)
%              Number of clauses        :   32 (  78 expanded)
%              Number of leaves         :   13 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  270 ( 669 expanded)
%              Number of equality atoms :   25 ( 118 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

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

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(t15_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).

fof(t13_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(c_0_13,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r3_orders_2(k2_yellow_1(X30),X31,X32)
        | r1_tarski(X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))
        | v1_xboole_0(X30) )
      & ( ~ r1_tarski(X31,X32)
        | r3_orders_2(k2_yellow_1(X30),X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))
        | v1_xboole_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

fof(c_0_14,plain,(
    ! [X29] :
      ( u1_struct_0(k2_yellow_1(X29)) = X29
      & u1_orders_2(k2_yellow_1(X29)) = k1_yellow_1(X29) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_15,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r3_orders_2(X8,X9,X10)
        | r1_orders_2(X8,X9,X10)
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ l1_orders_2(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8)) )
      & ( ~ r1_orders_2(X8,X9,X10)
        | r3_orders_2(X8,X9,X10)
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ l1_orders_2(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_16,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X26] :
      ( v1_orders_2(k2_yellow_1(X26))
      & l1_orders_2(k2_yellow_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_19,plain,(
    ! [X27] :
      ( v1_orders_2(k2_yellow_1(X27))
      & v3_orders_2(k2_yellow_1(X27))
      & v4_orders_2(k2_yellow_1(X27))
      & v5_orders_2(k2_yellow_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_20,plain,(
    ! [X28] :
      ( ( ~ v2_struct_0(k2_yellow_1(X28))
        | v1_xboole_0(X28) )
      & ( v1_orders_2(k2_yellow_1(X28))
        | v1_xboole_0(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

fof(c_0_21,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( m1_subset_1(esk2_2(X17,X18),u1_struct_0(X17))
        | ~ r1_yellow_0(X17,X18)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r2_lattice3(X17,X18,esk2_2(X17,X18))
        | ~ r1_yellow_0(X17,X18)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_lattice3(X17,X18,X20)
        | r1_orders_2(X17,esk2_2(X17,X18),X20)
        | ~ r1_yellow_0(X17,X18)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk3_3(X17,X21,X22),u1_struct_0(X17))
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r2_lattice3(X17,X21,X22)
        | r1_yellow_0(X17,X21)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r2_lattice3(X17,X21,esk3_3(X17,X21,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r2_lattice3(X17,X21,X22)
        | r1_yellow_0(X17,X21)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X22,esk3_3(X17,X21,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r2_lattice3(X17,X21,X22)
        | r1_yellow_0(X17,X21)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( r2_hidden(k1_xboole_0,X1)
         => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_1])).

fof(c_0_23,plain,(
    ! [X12,X13,X14,X15] :
      ( ( r2_lattice3(X12,X13,X14)
        | X14 != k1_yellow_0(X12,X13)
        | ~ r1_yellow_0(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_lattice3(X12,X13,X15)
        | r1_orders_2(X12,X14,X15)
        | X14 != k1_yellow_0(X12,X13)
        | ~ r1_yellow_0(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk1_3(X12,X13,X14),u1_struct_0(X12))
        | ~ r2_lattice3(X12,X13,X14)
        | X14 = k1_yellow_0(X12,X13)
        | ~ r1_yellow_0(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( r2_lattice3(X12,X13,esk1_3(X12,X13,X14))
        | ~ r2_lattice3(X12,X13,X14)
        | X14 = k1_yellow_0(X12,X13)
        | ~ r1_yellow_0(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,X14,esk1_3(X12,X13,X14))
        | ~ r2_lattice3(X12,X13,X14)
        | X14 = k1_yellow_0(X12,X13)
        | ~ r1_yellow_0(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_26,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_31,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | m1_subset_1(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & r2_hidden(k1_xboole_0,esk4_0)
    & k3_yellow_0(k2_yellow_1(esk4_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_17]),c_0_17])]),c_0_28])).

cnf(c_0_35,plain,
    ( r1_yellow_0(k2_yellow_1(X1),X2)
    | m1_subset_1(esk3_3(k2_yellow_1(X1),X2,X3),X1)
    | ~ r2_lattice3(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_30]),c_0_26])])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_39,plain,
    ( X1 = k1_yellow_0(k2_yellow_1(X2),X3)
    | m1_subset_1(esk1_3(k2_yellow_1(X2),X3,X1),X2)
    | ~ r2_lattice3(k2_yellow_1(X2),X3,X1)
    | ~ r1_yellow_0(k2_yellow_1(X2),X3)
    | ~ m1_subset_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_26])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | r1_yellow_0(k2_yellow_1(X1),X2)
    | r1_orders_2(k2_yellow_1(X1),X3,esk3_3(k2_yellow_1(X1),X2,X4))
    | ~ r2_lattice3(k2_yellow_1(X1),X2,X4)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X1)
    | ~ r1_tarski(X3,esk3_3(k2_yellow_1(X1),X2,X4)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | k3_yellow_0(X11) = k1_yellow_0(X11,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_45,plain,
    ( X1 = k1_yellow_0(k2_yellow_1(X2),X3)
    | v1_xboole_0(X2)
    | r1_orders_2(k2_yellow_1(X2),X4,esk1_3(k2_yellow_1(X2),X3,X1))
    | ~ r2_lattice3(k2_yellow_1(X2),X3,X1)
    | ~ r1_yellow_0(k2_yellow_1(X2),X3)
    | ~ m1_subset_1(X4,X2)
    | ~ m1_subset_1(X1,X2)
    | ~ r1_tarski(X4,esk1_3(k2_yellow_1(X2),X3,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_39])).

cnf(c_0_46,plain,
    ( r1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk3_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( r1_yellow_0(k2_yellow_1(esk4_0),X1)
    | r1_orders_2(k2_yellow_1(esk4_0),k1_xboole_0,esk3_3(k2_yellow_1(esk4_0),X1,X2))
    | ~ r2_lattice3(k2_yellow_1(esk4_0),X1,X2)
    | ~ m1_subset_1(X2,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( X1 = k1_yellow_0(k2_yellow_1(esk4_0),X2)
    | r1_orders_2(k2_yellow_1(esk4_0),k1_xboole_0,esk1_3(k2_yellow_1(esk4_0),X2,X1))
    | ~ r2_lattice3(k2_yellow_1(esk4_0),X2,X1)
    | ~ r1_yellow_0(k2_yellow_1(esk4_0),X2)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r1_yellow_0(k2_yellow_1(esk4_0),X1)
    | ~ r2_lattice3(k2_yellow_1(esk4_0),X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_30]),c_0_26]),c_0_17]),c_0_41]),c_0_41])])).

cnf(c_0_53,negated_conjecture,
    ( k1_yellow_0(k2_yellow_1(esk4_0),k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_26])])).

cnf(c_0_54,negated_conjecture,
    ( k1_yellow_0(k2_yellow_1(esk4_0),X1) = k1_xboole_0
    | ~ r2_lattice3(k2_yellow_1(esk4_0),X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_26]),c_0_17]),c_0_41]),c_0_41])]),c_0_52])).

fof(c_0_55,plain,(
    ! [X24,X25] :
      ( ( r2_lattice3(X24,k1_xboole_0,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( r1_lattice3(X24,k1_xboole_0,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_26]),c_0_17]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:57 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.20/0.41  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.042 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.20/0.41  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.20/0.41  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.41  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.20/0.41  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.20/0.41  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.20/0.41  fof(t15_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(r1_yellow_0(X1,X2)<=>?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r2_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow_0)).
% 0.20/0.41  fof(t13_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.20/0.41  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.20/0.41  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.41  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.20/0.41  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.20/0.41  fof(c_0_13, plain, ![X30, X31, X32]:((~r3_orders_2(k2_yellow_1(X30),X31,X32)|r1_tarski(X31,X32)|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))|~m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))|v1_xboole_0(X30))&(~r1_tarski(X31,X32)|r3_orders_2(k2_yellow_1(X30),X31,X32)|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))|~m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))|v1_xboole_0(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.20/0.41  fof(c_0_14, plain, ![X29]:(u1_struct_0(k2_yellow_1(X29))=X29&u1_orders_2(k2_yellow_1(X29))=k1_yellow_1(X29)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.20/0.41  fof(c_0_15, plain, ![X8, X9, X10]:((~r3_orders_2(X8,X9,X10)|r1_orders_2(X8,X9,X10)|(v2_struct_0(X8)|~v3_orders_2(X8)|~l1_orders_2(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))))&(~r1_orders_2(X8,X9,X10)|r3_orders_2(X8,X9,X10)|(v2_struct_0(X8)|~v3_orders_2(X8)|~l1_orders_2(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.41  cnf(c_0_16, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_17, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_18, plain, ![X26]:(v1_orders_2(k2_yellow_1(X26))&l1_orders_2(k2_yellow_1(X26))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.41  fof(c_0_19, plain, ![X27]:(((v1_orders_2(k2_yellow_1(X27))&v3_orders_2(k2_yellow_1(X27)))&v4_orders_2(k2_yellow_1(X27)))&v5_orders_2(k2_yellow_1(X27))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.20/0.41  fof(c_0_20, plain, ![X28]:((~v2_struct_0(k2_yellow_1(X28))|v1_xboole_0(X28))&(v1_orders_2(k2_yellow_1(X28))|v1_xboole_0(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.20/0.41  fof(c_0_21, plain, ![X17, X18, X20, X21, X22]:((((m1_subset_1(esk2_2(X17,X18),u1_struct_0(X17))|~r1_yellow_0(X17,X18)|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(r2_lattice3(X17,X18,esk2_2(X17,X18))|~r1_yellow_0(X17,X18)|(~v5_orders_2(X17)|~l1_orders_2(X17))))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_lattice3(X17,X18,X20)|r1_orders_2(X17,esk2_2(X17,X18),X20))|~r1_yellow_0(X17,X18)|(~v5_orders_2(X17)|~l1_orders_2(X17))))&((m1_subset_1(esk3_3(X17,X21,X22),u1_struct_0(X17))|(~m1_subset_1(X22,u1_struct_0(X17))|~r2_lattice3(X17,X21,X22))|r1_yellow_0(X17,X21)|(~v5_orders_2(X17)|~l1_orders_2(X17)))&((r2_lattice3(X17,X21,esk3_3(X17,X21,X22))|(~m1_subset_1(X22,u1_struct_0(X17))|~r2_lattice3(X17,X21,X22))|r1_yellow_0(X17,X21)|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(~r1_orders_2(X17,X22,esk3_3(X17,X21,X22))|(~m1_subset_1(X22,u1_struct_0(X17))|~r2_lattice3(X17,X21,X22))|r1_yellow_0(X17,X21)|(~v5_orders_2(X17)|~l1_orders_2(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).
% 0.20/0.41  fof(c_0_22, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0))), inference(assume_negation,[status(cth)],[t13_yellow_1])).
% 0.20/0.41  fof(c_0_23, plain, ![X12, X13, X14, X15]:(((r2_lattice3(X12,X13,X14)|X14!=k1_yellow_0(X12,X13)|~r1_yellow_0(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_lattice3(X12,X13,X15)|r1_orders_2(X12,X14,X15))|X14!=k1_yellow_0(X12,X13)|~r1_yellow_0(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12)))&((m1_subset_1(esk1_3(X12,X13,X14),u1_struct_0(X12))|~r2_lattice3(X12,X13,X14)|X14=k1_yellow_0(X12,X13)|~r1_yellow_0(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&((r2_lattice3(X12,X13,esk1_3(X12,X13,X14))|~r2_lattice3(X12,X13,X14)|X14=k1_yellow_0(X12,X13)|~r1_yellow_0(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&(~r1_orders_2(X12,X14,esk1_3(X12,X13,X14))|~r2_lattice3(X12,X13,X14)|X14=k1_yellow_0(X12,X13)|~r1_yellow_0(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.20/0.41  cnf(c_0_24, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_25, plain, (v1_xboole_0(X1)|r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.20/0.41  cnf(c_0_26, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_27, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_28, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_29, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_30, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  fof(c_0_31, plain, ![X6, X7]:(~r2_hidden(X6,X7)|m1_subset_1(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.41  fof(c_0_32, negated_conjecture, (~v1_xboole_0(esk4_0)&(r2_hidden(k1_xboole_0,esk4_0)&k3_yellow_0(k2_yellow_1(esk4_0))!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.20/0.41  cnf(c_0_33, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_34, plain, (v1_xboole_0(X1)|r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_17]), c_0_17])]), c_0_28])).
% 0.20/0.41  cnf(c_0_35, plain, (r1_yellow_0(k2_yellow_1(X1),X2)|m1_subset_1(esk3_3(k2_yellow_1(X1),X2,X3),X1)|~r2_lattice3(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_17]), c_0_30]), c_0_26])])).
% 0.20/0.41  cnf(c_0_36, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (r2_hidden(k1_xboole_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.41  fof(c_0_38, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.41  cnf(c_0_39, plain, (X1=k1_yellow_0(k2_yellow_1(X2),X3)|m1_subset_1(esk1_3(k2_yellow_1(X2),X3,X1),X2)|~r2_lattice3(k2_yellow_1(X2),X3,X1)|~r1_yellow_0(k2_yellow_1(X2),X3)|~m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_17]), c_0_26])])).
% 0.20/0.41  cnf(c_0_40, plain, (v1_xboole_0(X1)|r1_yellow_0(k2_yellow_1(X1),X2)|r1_orders_2(k2_yellow_1(X1),X3,esk3_3(k2_yellow_1(X1),X2,X4))|~r2_lattice3(k2_yellow_1(X1),X2,X4)|~m1_subset_1(X3,X1)|~m1_subset_1(X4,X1)|~r1_tarski(X3,esk3_3(k2_yellow_1(X1),X2,X4))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (m1_subset_1(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.41  cnf(c_0_42, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.41  fof(c_0_44, plain, ![X11]:(~l1_orders_2(X11)|k3_yellow_0(X11)=k1_yellow_0(X11,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.20/0.41  cnf(c_0_45, plain, (X1=k1_yellow_0(k2_yellow_1(X2),X3)|v1_xboole_0(X2)|r1_orders_2(k2_yellow_1(X2),X4,esk1_3(k2_yellow_1(X2),X3,X1))|~r2_lattice3(k2_yellow_1(X2),X3,X1)|~r1_yellow_0(k2_yellow_1(X2),X3)|~m1_subset_1(X4,X2)|~m1_subset_1(X1,X2)|~r1_tarski(X4,esk1_3(k2_yellow_1(X2),X3,X1))), inference(spm,[status(thm)],[c_0_34, c_0_39])).
% 0.20/0.41  cnf(c_0_46, plain, (r1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk3_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (r1_yellow_0(k2_yellow_1(esk4_0),X1)|r1_orders_2(k2_yellow_1(esk4_0),k1_xboole_0,esk3_3(k2_yellow_1(esk4_0),X1,X2))|~r2_lattice3(k2_yellow_1(esk4_0),X1,X2)|~m1_subset_1(X2,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), c_0_43])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (k3_yellow_0(k2_yellow_1(esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.41  cnf(c_0_49, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.41  cnf(c_0_50, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (X1=k1_yellow_0(k2_yellow_1(esk4_0),X2)|r1_orders_2(k2_yellow_1(esk4_0),k1_xboole_0,esk1_3(k2_yellow_1(esk4_0),X2,X1))|~r2_lattice3(k2_yellow_1(esk4_0),X2,X1)|~r1_yellow_0(k2_yellow_1(esk4_0),X2)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_41]), c_0_42])]), c_0_43])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (r1_yellow_0(k2_yellow_1(esk4_0),X1)|~r2_lattice3(k2_yellow_1(esk4_0),X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_30]), c_0_26]), c_0_17]), c_0_41]), c_0_41])])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (k1_yellow_0(k2_yellow_1(esk4_0),k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_26])])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (k1_yellow_0(k2_yellow_1(esk4_0),X1)=k1_xboole_0|~r2_lattice3(k2_yellow_1(esk4_0),X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_26]), c_0_17]), c_0_41]), c_0_41])]), c_0_52])).
% 0.20/0.41  fof(c_0_55, plain, ![X24, X25]:((r2_lattice3(X24,k1_xboole_0,X25)|~m1_subset_1(X25,u1_struct_0(X24))|~l1_orders_2(X24))&(r1_lattice3(X24,k1_xboole_0,X25)|~m1_subset_1(X25,u1_struct_0(X24))|~l1_orders_2(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (~r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.41  cnf(c_0_57, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_26]), c_0_17]), c_0_41])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 59
% 0.20/0.41  # Proof object clause steps            : 32
% 0.20/0.41  # Proof object formula steps           : 27
% 0.20/0.41  # Proof object conjectures             : 14
% 0.20/0.41  # Proof object clause conjectures      : 11
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 18
% 0.20/0.41  # Proof object initial formulas used   : 13
% 0.20/0.41  # Proof object generating inferences   : 13
% 0.20/0.41  # Proof object simplifying inferences  : 37
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 13
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 33
% 0.20/0.41  # Removed in clause preprocessing      : 1
% 0.20/0.41  # Initial clauses in saturation        : 32
% 0.20/0.41  # Processed clauses                    : 158
% 0.20/0.41  # ...of these trivial                  : 2
% 0.20/0.41  # ...subsumed                          : 25
% 0.20/0.41  # ...remaining for further processing  : 131
% 0.20/0.41  # Other redundant clauses eliminated   : 2
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 4
% 0.20/0.41  # Backward-rewritten                   : 0
% 0.20/0.41  # Generated clauses                    : 220
% 0.20/0.41  # ...of the previous two non-trivial   : 188
% 0.20/0.41  # Contextual simplify-reflections      : 19
% 0.20/0.41  # Paramodulations                      : 218
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 2
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 95
% 0.20/0.41  #    Positive orientable unit clauses  : 10
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 4
% 0.20/0.41  #    Non-unit-clauses                  : 81
% 0.20/0.41  # Current number of unprocessed clauses: 88
% 0.20/0.41  # ...number of literals in the above   : 712
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 35
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1235
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 152
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 48
% 0.20/0.41  # Unit Clause-clause subsumption calls : 22
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 0
% 0.20/0.41  # BW rewrite match successes           : 0
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 10591
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.064 s
% 0.20/0.41  # System time              : 0.006 s
% 0.20/0.41  # Total time               : 0.070 s
% 0.20/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
